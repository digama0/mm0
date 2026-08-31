// The MMB proof stack machine.
//
// Models the machine exactly as `ProofCmd` documents it: convertibility
// obligations (`e1 =?= e2`) live on the stack alongside expressions, proofs and
// convertibility proofs. That deliberately differs from mm0-rs's `mmb::import`,
// which encodes conversions as `CoConv` *continuations* -- a representation
// that suits rebuilding an mm0-rs `Proof`, but does not correspond to the
// machine state a user is trying to debug.
//
// This *runs* the unifier at each `Thm` and `Unfold` rather than treating it as
// a black box. A visualiser can skip that, because the main stream's stack
// effect needs only the arity -- how many `UnifyCmd::Hyp`s the stream contains
// -- which a walk of the stream recovers on its own.
// Running the unifier walks the same stream, so a checked pass costs one walk
// where the black box cost one walk, and there is a single code path rather
// than a replaying one and a verifying one that could disagree.
//
// This still does not verify *types*: sorts are tracked for display, but no
// dependencies, bound-variable conditions or provability are checked.

import { CLASS, PROOF, UNIFY, type Arg, type Decl, type MmbFile } from './mmb.js';
import { Arena } from './arena.js';
import { MAX_BOUND_VARS, bitHi, bitLo, depsBelow, hasBit, sortsCompatible } from './types.js';
import { EL, coconv, conv, expr, kindName, proof, type El } from './el.js';
import { UMODE, Unifier, UnifyError, type UMode } from './unifier.js';
import { argRef, nameRef } from './msg.js';

export { EL, type El } from './el.js';

/**
 * Which declaration's proof stream is running. The two differ in the dependency
 * calculation for `Term`, and in which commands are legal at all: a definition
 * may not use `Thm`, `Hyp` or `Sorry`.
 */
export const PMODE = { DEF: 0, THM: 1 } as const;
export type PMode = (typeof PMODE)[keyof typeof PMODE];

/**
 * How many sorts, terms and theorems have been *declared* at the point a proof
 * runs. Ids are assigned in declaration-stream order, and a proof may only
 * name what already exists: this is what rules out a definition referring to
 * itself or to a later one, and hence what rules out cyclic definitions.
 *
 * `Limits.all` is the permissive version -- everything in the file -- for
 * browsing a declaration in isolation rather than verifying the file in order.
 */
export interface Limits {
  sorts: number;
  terms: number;
  thms: number;
}

export const allLimits = (file: MmbFile): Limits =>
  ({ sorts: file.numSorts, terms: file.numTerms, thms: file.numThms });

/**
 * Which unify site is running, for error messages. Passed as a number with the
 * declaration id rather than as a formatted string or a `() =>` thunk: the
 * label is wanted only when something fails, and a template built at every
 * `Thm` costs a name lookup and a string on 23,828 applications of peano
 * alone. A thunk would skip that work but still allocate a closure per call,
 * and it escapes into `runUnify`, so escape analysis cannot be relied on to
 * remove it. Two numbers already in hand cost nothing.
 */
const SITE = { THM: 0, UNFOLD: 1, DEF_HEADER: 2, THM_HEADER: 3 } as const;
type Site = (typeof SITE)[keyof typeof SITE];

/** One command of a unify stream, with the state *before* it ran. */
export interface UnifyStep {
  /** The command, or null for the terminal state after the last one. */
  cmd: number | null;
  data: number;
  /** Expressions from the target still to be matched. */
  ustack: number[];
  /** The substitution. */
  uheap: number[];
  /** Depth of the caller's main stack; `UHyp` in `THM` mode takes from it. */
  mlen: number;
  /** Depth of the hypothesis stack; `UHyp` in `THM_END` mode takes from it. */
  hlen: number;
  /** Unify-stack elements this command consumes. */
  pops: number;
}

/**
 * How many stack elements a command takes, from the effects `ProofCmd`
 * documents.
 *
 * The machine counts what it actually popped, which is right for a command
 * that ran and useless for one that did not: a command that failed part way
 * reports fewer than it wanted, or none at all, so the step whose consumption
 * is most worth seeing was the one showing least. This is what it *would* have
 * taken, so the view can show that instead.
 *
 * `Ref` is 0 or 1 depending on the heap slot it names, so it answers 0 rather
 * than guess. Nothing here is on a hot path: it is asked only about a step
 * that already failed.
 */
export function stackPops(file: MmbFile, cmd: number, data: number): number {
  switch (cmd) {
    case PROOF.HYP: case PROOF.REFL: case PROOF.SYM:
    case PROOF.CONG: case PROOF.CONV_CUT: case PROOF.CONV_SAVE:
    case PROOF.SORRY:
      return 1;
    case PROOF.CONV: case PROOF.UNFOLD:
      return 2;
    case PROOF.TERM: case PROOF.TERM_SAVE:
      return data < file.numTerms ? file.term(data).numArgs : 0;
    case PROOF.THM: case PROOF.THM_SAVE: {
      // The arguments, the target, and one proof per `UHyp` -- the arity of a
      // `Thm`, which a walk of its unify stream gives without unifying.
      if (data >= file.numThms) return 0;
      const td = file.thm(data);
      let hyps = 0;
      const it = file.unifyAt(td.unifyStart);
      while (it.step()) if (it.cmd === UNIFY.HYP) hyps++;
      return td.numArgs + 1 + hyps;
    }
    default:
      return 0;
  }
}

/** A whole unify run, as invoked by one proof command or a header check. */
export interface UnifyTrace {
  /** The site that invoked it, e.g. `Thm syl`. Phrased for an error message. */
  site: string;
  /** The declaration being applied or unfolded, for the view to phrase itself. */
  name: string;
  mode: UMode;
  steps: UnifyStep[];
  error: string | null;
}

/**
 * One step of the path to a failure, inside a declaration.
 *
 * Structured rather than pre-formatted, because the view does two things with
 * it: writes it out, and *finds* the thing it names. A trail that is already a
 * string can only be read -- the step and the unify command it identifies are
 * exactly the rows that should be marked, and parsing them back out of prose
 * to do that would be inventing a format in order to re-read it.
 */
export type Where =
  /** A command of the proof stream. */
  | { at: 'step'; index: number }
  /** A command of a unify run, and the site that invoked the run. */
  | { at: 'unify'; index: number; site: string }
  /** A binder of the declaration. */
  | { at: 'arg'; index: number }
  /** A byte of the file, for a failure found while reading rather than
   *  checking -- there is no step or argument to name, only a position. */
  | { at: 'byte'; offset: number }
  /** The return type, which is checked as a binder is but names no variable. */
  | { at: 'ret' };

export function whereLabel(w: Where): string {
  switch (w.at) {
    case 'step': return `step ${w.index}`;
    // A run can fail as a whole rather than at a command, in which case there
    // is no index to give.
    case 'unify': return w.index < 0 ? w.site : `${w.site}, unify step ${w.index}`;
    case 'arg': return `arg ${w.index}`;
    case 'byte': return `0x${w.offset.toString(16)}`;
    case 'ret': return 'return type';
  }
}

/** `step 12, unify step 3: expected \`lam\`` -- the path, then what failed. */
export function trailOf(where: readonly Where[], message: string): string {
  return where.length === 0 ? message : `${where.map(whereLabel).join(', ')}: ${message}`;
}

/**
 * A failed check, with the trail of where it failed.
 *
 * A bare message cannot be acted on: `bad sort` on a definition that renders
 * correctly says neither which sort nor which part of the declaration carried
 * it, and leaves the reader comparing a rendering against a spec to find out.
 */
export class MachineError extends Error {
  readonly where: Where[];

  constructor(message: string, where: Where[] = []) {
    super(message);
    this.name = 'MachineError';
    this.where = where;
  }

  get trail(): string { return trailOf(this.where, this.message); }

  /** The same failure, seen from one level further out. */
  under(...outer: Where[]): MachineError {
    return new MachineError(this.message, [...outer, ...this.where]);
  }
}


export class Machine {
  readonly file: MmbFile;
  readonly arena = new Arena();
  stack: El[] = [];
  heap: El[] = [];
  /** Hypothesis expressions, in order of their `Hyp` commands. */
  hyps: number[] = [];

  /**
   * Stack elements consumed by the command currently being applied. Counted by
   * the machine as it pops rather than inferred by a caller, since only the
   * machine knows an arity like `Thm`'s (target + args + one proof per
   * `UnifyCmd::Hyp`). Reset at the top of `apply`.
   */
  popped = 0;

  /** How many unify streams have been run, and how many commands they took.
   *  Counted so a test can tell a passing verification from one that never
   *  invoked the unifier at all. */
  unifyRuns = 0;
  unifySteps = 0;

  /**
   * Set to record every unify run in full. Off by default: tracing copies both
   * unify stacks per command, which is pure waste when verifying a library and
   * exactly what is wanted when stepping through one declaration.
   */
  onUnify: ((t: UnifyTrace) => void) | null = null;

  /** Set if the proof used `Sorry`, which must not verify. */
  usesSorry = false;

  /**
   * Failures the run carried on past.
   *
   * A disjoint-variable violation and a failed unify run are both verdicts
   * about a step rather than damage to the machine: the stack effect either
   * does not depend on them at all, or can be completed without them. Stopping
   * at the first meant a proof with six bad steps was six edit-and-recheck
   * cycles to see.
   *
   * They are still failures -- `verify` reports every one, and a declaration
   * with any is not verified.
   */
  readonly errors: MachineError[] = [];

  /**
   * How many failures to carry on past before giving up on a declaration.
   *
   * A corrupt file can make every step fail, and past the first handful the
   * list stops being a list of things to fix and starts being a symptom that
   * the file is not a proof at all.
   */
  static readonly MAX_ERRORS = 16;

  /** Set when the cap stopped the run, so a report can say it is not the whole
   *  story: the count it carries is a floor, not a total. */
  gaveUp = false;

  /** Record a failure and carry on -- or stop, if there are too many. */
  private carryOn(e: MachineError): void {
    this.errors.push(e);
    if (this.errors.length >= Machine.MAX_ERRORS) {
      this.gaveUp = true;
      throw new MachineError(
        `giving up after ${Machine.MAX_ERRORS} failures in this declaration`);
    }
  }

  readonly decl: Decl;
  readonly mode: PMode;

  /**
   * The index of the next bound variable. Every bound variable owns one bit of
   * every dependency set, and this is the next one to hand out. mm0-c keeps
   * the bit itself (`g_next_bv`, doubled each time); an index is the same
   * thing without needing 56-bit arithmetic to advance it.
   */
  private nextBv = 0;

  /**
   * Scratch: the dependency sets of the bound arguments of the `Term` or `Thm`
   * being applied, in order. Reused across commands rather than reallocated,
   * as mm0-c's `g_deps` is.
   */
  private readonly boundLo: number[] = [];
  private readonly boundHi: number[] = [];
  /** The argument each bound variable came from, for naming it in a failure. */
  private readonly boundArg: number[] = [];


  /**
   * Start the machine for a declaration, loading its binders onto the heap.
   */
  private readonly limits: Limits;

  constructor(file: MmbFile, d: Decl, limits: Limits = allLimits(file)) {
    this.file = file;
    this.decl = d;
    this.limits = limits;
    this.mode = d.cls === CLASS.TERM ? PMODE.DEF : PMODE.THM;
    this.loadArgs(d);
  }

  /**
   * Load a declaration's binders as variables on the heap, checking each is
   * well formed. Port of mm0-c's `load_args`.
   *
   * A bound binder must own exactly the next dependency bit -- binders are
   * numbered in order and may not skip or repeat -- and a regular binder may
   * only depend on bound variables declared before it. Neither is implied by
   * anything else: they are what makes the bit positions in every later
   * dependency set mean what the typing rules assume.
   *
   * For a term or def the *return* type is loaded too, so it is validity
   * checked on the same terms, and then dropped from the heap: it names no
   * variable, it only constrains one.
   */
  private loadArgs(d: Decl): void {
    if (d.cls === CLASS.SORT) return;
    const isTerm = d.cls === CLASS.TERM;
    const args: Arg[] = isTerm ? this.file.term(d.num).args : this.file.thm(d.num).args;
    // A term's return type is checked on the same terms as a binder, but names
    // no variable -- it only constrains one -- so it gets no `newVar`. mm0-c
    // allocates it and then drops it from the heap; we skip it, because
    // `newVar` advances the variable index, and that index is the key into the
    // `VarN` name list. Allocating one here would renumber every `Dummy` after
    // it, and a def's dummy would print as `e5` instead of `y`.
    const all = isTerm ? [...args, this.file.term(d.num).ret] : args;
    for (let i = 0; i < all.length; i++) {
      const a = all[i]!;
      // Which binder failed, and the return type told apart from the arguments
      // -- `bad binder sort` on a declaration with six of them says nothing
      // about where to look.
      const at: Where[] = [i < args.length ? { at: 'arg', index: i } : { at: 'ret' }];
      if (a.sort >= this.limits.sorts) {
        throw new MachineError(
          `sort ${a.sort} is not a declared sort (${this.limits.sorts} so far)`, at);
      }
      if (a.bound) {
        if (this.file.sortIsStrict(a.sort)) {
          throw new MachineError(
            `bound, but ${nameRef('sort', this.file.sortName(a.sort))} is strict`, at);
        }
        if (this.nextBv >= MAX_BOUND_VARS) {
          throw new MachineError(`more than ${MAX_BOUND_VARS} bound variables`, at);
        }
        if (a.depsLo !== bitLo(this.nextBv) || a.depsHi !== bitHi(this.nextBv)) {
          throw new MachineError(`bound, so deps must be bit ${this.nextBv} alone`, at);
        }
        this.nextBv++;
      } else if (!depsBelow(a.depsLo, a.depsHi, this.nextBv)) {
        throw new MachineError(
          `deps reference a bound variable at or past ${this.nextBv}`, at);
      }
      if (i < args.length) {
        this.heap.push(expr(this.arena.newVar(a.sort, a.bound, a.depsLo, a.depsHi)));
      }
    }
  }

  private pop(): El {
    const el = this.stack.pop();
    if (el === undefined) throw new MachineError('stack underflow');
    this.popped++;
    return el;
  }

  private popExpr(): number {
    const el = this.pop();
    if (el.k !== EL.EXPR) {
      throw new MachineError(`expected an expression, found ${kindName(el.k)}`);
    }
    return el.a;
  }

  private popProof(): number {
    const el = this.pop();
    if (el.k !== EL.PROOF) {
      throw new MachineError(`expected a proof, found ${kindName(el.k)}`);
    }
    return el.a;
  }

  private popCoConv(): El {
    const el = this.pop();
    if (el.k !== EL.COCONV) {
      throw new MachineError(
        `expected a convertibility obligation, found ${kindName(el.k)}`);
    }
    return el;
  }

  /**
   * Pop `n` expressions, returning them bottom-to-top -- the order they were
   * pushed, which is argument order.
   */
  private popnExprs(n: number): number[] {
    const mid = this.stack.length - n;
    if (mid < 0) throw new MachineError('stack underflow');
    this.popped += n;
    const out: number[] = new Array(n);
    for (let i = 0; i < n; i++) {
      const el = this.stack[mid + i]!;
      if (el.k !== EL.EXPR) {
        throw new MachineError(`expected an expression, found ${kindName(el.k)}`);
      }
      out[i] = el.a;
    }
    this.stack.length = mid;
    return out;
  }

  /**
   * An argument of the theorem being applied, by position and name.
   *
   * A message giving only indices -- `argument 3 may not depend on bound
   * variable 0` -- names neither the variables the applied theorem declared nor
   * what they stand for here, which is the whole content of the complaint. The
   * name goes in the message; what it was substituted with does not, because
   * it is on the stack at this step and anything replaying the proof has it.
   */
  private arg(tid: number, i: number): string {
    return argRef(i, this.file.thmVarName(tid, i));
  }

  /**
   * The disjoint-variable conditions for a theorem application.
   *
   * This is what makes substitution sound, and it is the part a visualiser has
   * no need of, since it type-checks nothing. Two rules, from mm0-c:
   *
   * * A bound binder must receive something whose dependencies are disjoint
   *   from *every* argument substituted before it -- that is what "distinct
   *   variable" means, and it is checked against all previous arguments, not
   *   only the bound ones.
   * * A regular binder must receive something disjoint from each bound
   *   argument its declared type does *not* mention. Declaring the dependency
   *   is exactly how a theorem opts out of the restriction.
   */
  private checkDisjoint(tid: number, targets: readonly Arg[], args: readonly number[]): void {
    let nbound = 0;
    for (let i = 0; i < targets.length; i++) {
      const n = this.arena.get(args[i]!);
      const target = targets[i]!;
      if (!sortsCompatible(n.bound, n.sort, target.bound, target.sort)) {
        this.carryOn(new MachineError(
          `${nameRef('thm', this.file.thmName(tid))}: type mismatch at argument ${i}`));
      }
      if (target.bound) {
        this.boundLo[nbound] = n.depsLo;
        this.boundHi[nbound] = n.depsHi;
        // Which argument this bound variable is, so a failure can name it: the
        // `j` below counts bound variables, not arguments.
        this.boundArg[nbound] = i;
        nbound++;
        for (let j = 0; j < i; j++) {
          const prev = this.arena.get(args[j]!);
          if ((prev.depsLo & n.depsLo) !== 0 || (prev.depsHi & n.depsHi) !== 0) {
            this.carryOn(new MachineError(`${nameRef('thm', this.file.thmName(tid))}`
              + `: argument ${i} (${this.arg(tid, i)})`
              + ` must be disjoint from argument ${j} (${this.arg(tid, j)})`));
          }
        }
      } else {
        for (let j = 0; j < nbound; j++) {
          if (hasBit(target.depsLo, target.depsHi, j)) continue;
          if ((this.boundLo[j]! & n.depsLo) !== 0 || (this.boundHi[j]! & n.depsHi) !== 0) {
            const at = this.boundArg[j]!;
            this.carryOn(new MachineError(`${nameRef('thm', this.file.thmName(tid))}`
              + `: bound variable ${j} (${this.arg(tid, at)})`
              + ` is referenced in argument ${i} (${this.arg(tid, i)})`));
          }
        }
      }
    }
  }

  private asApp(e: number, what: string) {
    const n = this.arena.asApp(e);
    if (n === null) {
      throw new MachineError(`${what}: expected a term application, found a variable`);
    }
    return n;
  }

  /**
   * Take the hypothesis proofs a stopped unify run had not reached.
   *
   * `UHyp` in `THM` mode pops a proof from the caller's stack, so a run that
   * gave up part way still owes however many of those remain. The rest of the
   * stream is scanned rather than applied -- the substitution is already
   * wrong and nothing counted here depends on it -- which is the same walk
   * that yields a `Thm`'s arity without running the unifier.
   */
  private settleHyps(it: ReturnType<MmbFile['unifyAt']>, mode: UMode): void {
    // Only `THM` takes from the caller's stack: `THM_END` takes from the
    // hypothesis list it was handed, and `DEF` has no `UHyp` at all.
    if (mode !== UMODE.THM) return;
    let owed = 0;
    while (it.step()) if (it.cmd === UNIFY.HYP) owed++;
    for (let k = 0; k < owed && this.stack.length > 0; k++) this.stack.pop();
  }

  /** Format a unify site. Called only on the failure path. */
  private siteLabel(site: Site, id: number): string {
    switch (site) {
      case SITE.THM: return `Thm ${this.file.thmName(id)}`;
      case SITE.UNFOLD: return `Unfold ${this.file.termName(id)}`;
      case SITE.DEF_HEADER: return `def ${this.file.termName(id)} header`;
      case SITE.THM_HEADER: return `${this.file.thmName(id)} header`;
    }
  }

  /**
   * Run a unify stream to completion against a target.
   *
   * `UHyp` in `THM` mode pops hypothesis proofs off this machine's own stack,
   * so the unifier is handed it directly and whatever it takes is added to
   * `popped` -- keeping the reported arity of a `Thm` (target + arguments +
   * one proof per `UHyp`) counted by the machine as it happens, rather than
   * inferred afterwards.
   */
  private runUnify(
    site: Site, id: number, mode: UMode, it: ReturnType<MmbFile['unifyAt']>,
    ustack: number[], uheap: number[], hstack: number[],
  ): void {
    const before = this.stack.length;
    const u = new Unifier(this.file, this.arena, mode, ustack, uheap, hstack, this.stack);
    this.unifyRuns++;
    // Tracing copies both unify stacks per command, so it is off unless a caller asks
    const trace: UnifyTrace | null = this.onUnify === null
      ? null
      : {
        site: this.siteLabel(site, id),
        name: site === SITE.THM || site === SITE.THM_HEADER
          ? this.file.thmName(id) : this.file.termName(id),
        mode, steps: [], error: null,
      };
    // Which command of the run is being applied, so a failure can name it.
    let ustep = -1;
    try {
      while (it.step()) {
        ustep++;
        this.unifySteps++;
        if (trace !== null) {
          trace.steps.push({
            cmd: it.cmd, data: it.data,
            ustack: u.ustack.slice(), uheap: u.uheap.slice(),
            mlen: this.stack.length, hlen: u.hstack.length, pops: 0,
          });
        }
        u.apply(it.cmd, it.data);
        const last = trace?.steps[trace.steps.length - 1];
        if (last !== undefined) last.pops = u.popped;
      }
      if (it.error) throw new UnifyError(it.error.message);
      // Past the commands: `finish` rejects the run as a whole -- the target
      // was left partly matched, or a hypothesis was never taken -- so there is
      // no command to point at, and pointing at the last one that *worked*
      // would blame it for something it did not do.
      ustep = -1;
      u.finish();
      // The end state, so the view can show the stacks after the last command.
      if (trace !== null) {
        trace.steps.push({
          cmd: null, data: 0,
          ustack: u.ustack.slice(), uheap: u.uheap.slice(),
          mlen: this.stack.length, hlen: u.hstack.length, pops: 0,
        });
        this.onUnify?.(trace);
      }
    } catch (e) {
      // Surface one error type from the machine, with the site that failed --
      // a bare "does not match the substitution at heap slot 2" is unusable
      // without knowing which theorem application it came from.
      if (e instanceof UnifyError) {
        // A failed run is still worth showing: the view stops *at* the command
        // that failed, which is the last step in the trace -- its pre-state was
        // pushed before it was applied. No terminal step is added: the run did
        // not reach an end, and a row saying so after the failing command puts
        // the verdict one line below the thing it is about.
        //
        // Unless nothing ran at all, which `finish` can still reject -- an
        // empty trace has no row to carry the error and no state to draw.
        if (trace !== null) {
          trace.error = e.message;
          if (trace.steps.length === 0) {
            trace.steps.push({
              cmd: null, data: 0,
              ustack: u.ustack.slice(), uheap: u.uheap.slice(),
              mlen: this.stack.length, hlen: u.hstack.length, pops: 0,
            });
          }
          this.onUnify?.(trace);
        }
        // The site and the command within it: `Thm syl, unify step 3`. A run
        // has tens of commands and they all look alike.
        const err = new MachineError(e.message,
          [{ at: 'unify', index: ustep, site: this.siteLabel(site, id) }]);
        // A failed run is a verdict about this step, not damage to the machine
        // -- the caller pushes its conclusion either way, and the run's only
        // effect on the main stack is the hypothesis proofs `UHyp` takes. So
        // the debt is settled and the proof carries on, and the step after
        // this one is checked against a stack of the right depth rather than
        // being abandoned along with everything that follows.
        this.settleHyps(it, mode);
        this.carryOn(err);
        this.popped += before - this.stack.length;
        return;
      }
      throw e;
    }
    this.popped += before - this.stack.length;
  }

  /**
   * Check the finished proof against the declaration's own header.
   *
   * This is the fourth unify site, and the one mmb.md does not document: after
   * the stream ends, mm0-c seeds the substitution with the declaration's
   * arguments and unifies the single remaining stack element against the
   * header -- `UThmEnd` for an axiom or theorem, whose hypotheses come off the
   * hypothesis stack, `UDef` for a def. A plain term has no proof to check.
   *
   * Without this a proof could build *anything* and still be accepted: the
   * stream up to here never once consults what the declaration claims.
   */
  endCheck(d: Decl): void {
    if (d.cls === CLASS.SORT || (d.cls === CLASS.TERM && !d.isDef)) return;
    const top = this.stack[this.stack.length - 1];
    if (this.stack.length !== 1 || top === undefined) {
      throw new MachineError(
        `the proof left ${this.stack.length} elements on the stack, expected 1`);
    }
    // An axiom states an expression; a theorem must actually prove one.
    const wantProof = d.cls === CLASS.THM && d.isThm;
    if (top.k !== (wantProof ? EL.PROOF : EL.EXPR)) {
      throw new MachineError(
        `the proof ended with ${kindName(top.k)}, expected ${wantProof ? 'a proof' : 'an expression'}`);
    }
    const val = this.arena.get(top.a);
    if (d.cls === CLASS.TERM) {
      // The value must have the declared return type, and may not depend on
      // anything the return type does not declare -- otherwise the definition
      // would smuggle in a dependency its users never see.
      const ret = this.file.term(d.num).ret;
      if (!sortsCompatible(val.bound, val.sort, ret.bound, ret.sort)) {
        throw new MachineError('def value has the wrong type');
      }
      if ((val.depsLo & ~ret.depsLo) !== 0 || (val.depsHi & ~ret.depsHi) !== 0) {
        throw new MachineError('def value has unaccounted dependencies');
      }
    } else if (!this.file.sortIsProvable(val.sort)) {
      throw new MachineError('conclusion should have provable sort');
    }
    // The substitution is the declaration's own arguments, which are the first
    // entries of the heap and are still exactly as the machine seeded them.
    const nargs = d.cls === CLASS.TERM
      ? this.file.term(d.num).numArgs
      : this.file.thm(d.num).numArgs;
    const uheap: number[] = new Array(nargs);
    for (let i = 0; i < nargs; i++) {
      const el = this.heap[i];
      if (el === undefined || el.k !== EL.EXPR) {
        throw new MachineError(`heap slot ${i} is not an argument variable`);
      }
      uheap[i] = el.a;
    }
    if (d.cls === CLASS.TERM) {
      const td = this.file.term(d.num);
      if (td.unifyStart === null) return;
      this.runUnify(
        SITE.DEF_HEADER, d.num, UMODE.DEF,
        this.file.unifyAt(td.unifyStart), [top.a], uheap, []);
    } else {
      const td = this.file.thm(d.num);
      // `hstack` is consumed from the top, and `UHyp` takes the last-declared
      // hypothesis first, matching the stream's reverse order.
      this.runUnify(
        SITE.THM_HEADER, d.num, UMODE.THM_END,
        this.file.unifyAt(td.unifyStart), [top.a], uheap, this.hyps.slice());
    }
  }

  /**
   * Apply one proof command, given its opcode and immediate as the stream
   * cursor decoded them.
   */
  apply(cmd: number, data: number): void {
    this.popped = 0;
    switch (cmd) {
      // Term t:      H; S, e1, ..., en --> H; S, (t e1 .. en)
      // TermSave t:  as Term, and the result is also saved to the heap.
      case PROOF.TERM:
      case PROOF.TERM_SAVE: {
        if (data >= this.limits.terms) throw new MachineError('term out of range');
        const td = this.file.term(data);
        const args = this.popnExprs(td.numArgs);
        // The result's dependency set. A bound argument contributes nothing
        // directly -- it is *recorded*, because the binders that follow may
        // declare that they depend on it -- while a regular argument
        // contributes its own dependencies.
        let accLo = 0, accHi = 0;
        let nbound = 0;
        for (let i = 0; i < td.numArgs; i++) {
          const n = this.arena.get(args[i]!);
          const target = td.args[i]!;
          if (!sortsCompatible(n.bound, n.sort, target.bound, target.sort)) {
            throw new MachineError(
              `${nameRef('term', this.file.termName(data))}`
              + `: type mismatch at argument ${i}`);
          }
          let dLo = n.depsLo, dHi = n.depsHi;
          if (target.bound) {
            this.boundLo[nbound] = dLo;
            this.boundHi[nbound] = dHi;
            nbound++;
          } else {
            if (this.mode === PMODE.DEF) {
              // In a definition the bound arguments really are bound: a
              // dependency the binder *declares* is discharged by the binding,
              // so it is subtracted rather than propagated. In a theorem
              // nothing binds, so every variable stays visible.
              for (let j = 0; j < nbound; j++) {
                if (hasBit(target.depsLo, target.depsHi, j)) {
                  dLo &= ~this.boundLo[j]!;
                  dHi &= ~this.boundHi[j]!;
                }
              }
            }
            accLo |= dLo;
            accHi |= dHi;
          }
        }
        if (this.mode === PMODE.DEF) {
          // The return type declares which of the bound arguments the result
          // may depend on; those come back in.
          const ret = td.ret;
          for (let j = 0; j < nbound; j++) {
            if (hasBit(ret.depsLo, ret.depsHi, j)) {
              accLo |= this.boundLo[j]!;
              accHi |= this.boundHi[j]!;
            }
          }
        }
        const e = this.arena.app(data, args, td.sort, accLo >>> 0, accHi >>> 0);
        if (cmd === PROOF.TERM_SAVE) this.heap.push(expr(e));
        this.stack.push(expr(e));
        break;
      }

      // Ref i:      H; S --> H; S, Hi
      // ConvRef i:  H; S, e1 =?= e2 --> H; S   (when Hi is e1 = e2)
      //
      // One opcode, two behaviours, decided by what the heap slot holds: a
      // saved convertibility proof *discharges* an obligation instead of
      // pushing. This is why `Ref` is the only fixed-arity command whose
      // `popped` is not constant.
      case PROOF.REF: {
        const el = this.heap[data];
        if (el === undefined) {
          throw new MachineError(
            `heap reference ${data} out of range (heap has ${this.heap.length})`);
        }
        if (el.k === EL.CONV) {
          const ob = this.popCoConv();
          if (ob.a !== el.a || ob.b !== el.b) {
            throw new MachineError(
              'ConvRef: obligation does not match the saved convertibility proof');
          }
        } else {
          this.stack.push(el);
        }
        break;
      }

      // Dummy s: H; S --> H, x; S, x
      case PROOF.DUMMY: {
        if (data >= this.limits.sorts) throw new MachineError('bad dummy sort');
        // A strict sort admits no bound variables at all; a free sort admits
        // them only as binders, never introduced mid-proof.
        if (this.file.sortIsStrict(data) || this.file.sortIsFree(data)) {
          throw new MachineError('dummy variable in strict or free sort');
        }
        if (this.nextBv >= MAX_BOUND_VARS) throw new MachineError('too many bound variables');
        const e = this.arena.newVar(
          data, true, bitLo(this.nextBv), bitHi(this.nextBv), true);
        this.nextBv++;
        this.heap.push(expr(e));
        this.stack.push(expr(e));
        break;
      }

      // Thm T: H; S, e1, ..., en, e --> H; S', |- e
      //
      // The target is on top, the arguments below it -- together the
      // substitution -- and the hypothesis proofs below those, which the
      // unifier takes one at a time as it meets each `UHyp`.
      case PROOF.THM:
      case PROOF.THM_SAVE: {
        if (this.mode === PMODE.DEF) throw new MachineError('Thm is not allowed in a def');
        if (data >= this.limits.thms) throw new MachineError('theorem out of range');
        const td = this.file.thm(data);
        const tgt = this.popExpr();
        const args = this.popnExprs(td.numArgs);
        this.checkDisjoint(data, td.args, args);
        this.runUnify(
          SITE.THM, data, UMODE.THM,
          this.file.unifyAt(td.unifyStart), [tgt], args, []);
        if (cmd === PROOF.THM_SAVE) this.heap.push(proof(tgt));
        this.stack.push(proof(tgt));
        break;
      }

      // Hyp: HS; H; S, e --> HS, e; H, |- e; S
      case PROOF.HYP: {
        if (this.mode === PMODE.DEF) throw new MachineError('Hyp is not allowed in a def');
        const e = this.popExpr();
        if (!this.file.sortIsProvable(this.arena.get(e).sort)) {
          throw new MachineError('hypothesis should have provable sort');
        }
        this.hyps.push(e);
        this.heap.push(proof(e));
        break;
      }

      // Conv: S, e1, |- e2 --> S, |- e1, e1 =?= e2
      case PROOF.CONV: {
        const e2 = this.popProof();
        const e1 = this.popExpr();
        this.stack.push(proof(e1));
        this.stack.push(coconv(e1, e2));
        break;
      }

      // Refl: S, e =?= e --> S
      case PROOF.REFL: {
        const ob = this.popCoConv();
        // An identity test, not a structural one: the spec asks whether the two
        // sides *are* the same expression, so it is the producer's job to have
        // built them as one. Comparing structurally here would accept proofs
        // mm0-c rejects. See the note in arena.ts.
        if (ob.a !== ob.b) throw new MachineError('Refl: the two sides are not equal');
        break;
      }

      // Sym: S, e1 =?= e2 --> S, e2 =?= e1
      case PROOF.SYM: {
        const ob = this.popCoConv();
        this.stack.push(coconv(ob.b, ob.a));
        break;
      }

      // Cong: S, (t e1..en) =?= (t e1'..en') --> S, en =?= en', ..., e1 =?= e1'
      case PROOF.CONG: {
        const ob = this.popCoConv();
        const l = this.asApp(ob.a, 'Cong');
        const r = this.asApp(ob.b, 'Cong');
        if (l.term !== r.term) {
          throw new MachineError('Cong: the two sides apply different terms');
        }
        if (l.args.length !== r.args.length) throw new MachineError('Cong: arity mismatch');
        // Pushed in reverse so that e1 =?= e1' ends up on top and the parts are
        // dealt with in declaration order.
        for (let i = l.args.length - 1; i >= 0; i--) {
          this.stack.push(coconv(l.args[i]!, r.args[i]!));
        }
        break;
      }

      // Unfold: S, (t e1..en) =?= e', e --> S, e =?= e'
      //
      // The def's own arguments are the substitution, and `e` -- the claimed
      // expansion -- is matched against the def's value.
      case PROOF.UNFOLD: {
        const e = this.popExpr();
        const ob = this.popCoConv();
        const head = this.asApp(ob.a, 'Unfold');
        const td = this.file.term(head.term);
        if (td.unifyStart === null) {
          throw new MachineError(
            `Unfold: ${nameRef('term', this.file.termName(head.term))} is not a def`);
        }
        this.runUnify(
          SITE.UNFOLD, head.term, UMODE.DEF,
          this.file.unifyAt(td.unifyStart), [e], head.args.slice(), []);
        this.stack.push(coconv(e, ob.b));
        break;
      }

      // ConvCut: S, e1 =?= e2 --> S, e1 = e2, e1 =?= e2
      case PROOF.CONV_CUT: {
        const ob = this.popCoConv();
        this.stack.push(conv(ob.a, ob.b));
        this.stack.push(coconv(ob.a, ob.b));
        break;
      }

      // ConvSave: H; S, e1 = e2 --> H, e1 = e2; S
      case PROOF.CONV_SAVE: {
        const el = this.pop();
        if (el.k !== EL.CONV) {
          throw new MachineError(
            `expected a convertibility proof, found ${kindName(el.k)}`);
        }
        this.heap.push(conv(el.a, el.b));
        break;
      }

      // Save: H; S, s --> H, s; S, s   (peeks; the stack is unchanged)
      case PROOF.SAVE: {
        const el = this.stack[this.stack.length - 1];
        if (el === undefined) throw new MachineError('stack underflow');
        if (el.k === EL.COCONV) {
          throw new MachineError("Save: can't save a convertibility obligation");
        }
        this.heap.push(el);
        break;
      }

      // Sorry:     S, e -> S, |- e
      // ConvSorry: S, e1 =?= e2 -> S
      case PROOF.SORRY: {
        if (this.mode === PMODE.DEF) throw new MachineError('Sorry is not allowed in a def');
        this.usesSorry = true;
        const el = this.pop();
        if (el.k === EL.EXPR) this.stack.push(proof(el.a));
        else if (el.k !== EL.COCONV) {
          throw new MachineError(
            `Sorry: expected an expression or obligation, found ${kindName(el.k)}`);
        }
        break;
      }

      default:
        throw new MachineError(`unknown proof command 0x${cmd.toString(16)}`);
    }
  }
}
