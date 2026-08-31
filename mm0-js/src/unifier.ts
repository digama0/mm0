// The unify stack machine, run as the matcher it is.
//
// This is the sub-machine that `Thm` and `Unfold` invoke, and the counterpart
// to printer.ts's `UnifyReader`: the reader treats a unify stream as a
// construction, to recover a statement; this destructures a concrete target
// against it.
//
// State, as documented on `UnifyCmd`:
//
//   * `ustack` -- expressions from the target, being taken apart;
//   * `uheap`  -- the substitution: what the caller supplies for the
//                 declaration's variables, extended by `save` and dummies;
//   * the caller's main stack, which only `UHyp` touches, to pop hypothesis
//     proofs.
//
// It allocates nothing: `UDummy` *moves* a variable already on the ustack into
// the uheap, so the arena is read-only here and every id it reports is one the
// caller already has.
//
// Note mm0-c runs a unify stream at *four* sites, not the two mmb.md describes:
// applying a `Thm` (UThm), an `Unfold` (UDef), and -- undocumented -- at the
// end of every declaration, checking what the proof built against the
// declaration's own header (UThmEnd for an axiom or theorem, UDef for a def).

import { UNIFY, type MmbFile } from './mmb.js';
import { NODE, type Arena } from './arena.js';
import { EL, kindName, type El } from './el.js';
import { nameRef } from './msg.js';

/**
 * Which unify context we are in, mirroring mm0-c's `unify_mode`. The three
 * share a stream format but differ on `UDummy` and `UHyp`.
 */
export const UMODE = {
  /** A definition's header, or an `Unfold`. `UDummy` is legal only here, and
   *  `UHyp` is legal everywhere but here. */
  DEF: 0,
  /** Applying a theorem: `UHyp` takes hypothesis proofs off the main stack. */
  THM: 1,
  /** Checking a theorem's header: `UHyp` takes from the hypothesis stack that
   *  `ProofCmd::Hyp` built, and the stream must consume all of it. */
  THM_END: 2,
} as const;
export type UMode = (typeof UMODE)[keyof typeof UMODE];

/**
 * How many unify-stack elements a command takes, from the stack effects above.
 *
 * The machine counts what it actually popped, which is right for a command
 * that ran and useless for one that did not: a command that failed reports
 * zero, so the view had nothing to mark on the one step worth looking at.
 * This is what the command *would* have taken, so the view can show it anyway.
 */
export function ustackPops(cmd: number | null): number {
  switch (cmd) {
    // `S, (t e1..en) --> S, en..e1`, `S, e --> S` and `H; S, x --> H, x; S`
    // all take the top of the stack.
    case UNIFY.TERM: case UNIFY.TERM_SAVE: case UNIFY.REF: case UNIFY.DUMMY: return 1;
    // `UHyp` takes from the caller's stack, not this one, and pushes here.
    default: return 0;
  }
}

export class UnifyError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'UnifyError';
  }
}

export class Unifier {
  private readonly file: MmbFile;
  private readonly arena: Arena;
  readonly mode: UMode;
  /** Expressions from the target, being taken apart. */
  ustack: number[];
  /** The substitution. */
  uheap: number[];
  /**
   * Which `uheap` entries came from a `save` rather than from the caller's
   * substitution. mm0-c flags these with a tag bit in the pointer itself; they
   * are skipped by `UDummy`'s disjointness scan, since a shared subterm is not
   * something a dummy has to be distinct from. `URef` masks the tag off, so a
   * saved slot is still referenceable.
   */
  private readonly uheapSaved: boolean[];
  /** `UThmEnd` only: the declaration's own hypotheses, taken from the top. */
  hstack: number[];
  /**
   * The caller's main stack as it stands *inside* the command -- already shorn
   * of the target and the arguments. `UHyp` pops hypothesis proofs off it.
   */
  private readonly mstack: El[];

  /**
   * Unify-stack elements consumed by the command being applied, counted here
   * rather than inferred. `UHyp` consumes none of these: it takes from the
   * main or hypothesis stack instead.
   */
  popped = 0;

  constructor(
    file: MmbFile, arena: Arena, mode: UMode,
    ustack: number[], uheap: number[], hstack: number[], mstack: El[],
  ) {
    this.file = file;
    this.arena = arena;
    this.mode = mode;
    this.ustack = ustack;
    this.uheap = uheap;
    this.uheapSaved = new Array(uheap.length).fill(false);
    this.hstack = hstack;
    this.mstack = mstack;
  }

  private popU(): number {
    const e = this.ustack.pop();
    if (e === undefined) throw new UnifyError('unify stack underflow');
    this.popped++;
    return e;
  }

  apply(cmd: number, data: number): void {
    this.popped = 0;
    switch (cmd) {
      // UTerm t: S, (t e1 ... en) --> S, en, ..., e1
      // USave:   H; S, e --> H, e; S, e     (UTermSave = USave; UTerm)
      case UNIFY.TERM:
      case UNIFY.TERM_SAVE: {
        const e = this.popU();
        // `save` records the whole term *before* destructuring it.
        if (cmd === UNIFY.TERM_SAVE) {
          this.uheap.push(e);
          this.uheapSaved.push(true);
        }
        const n = this.arena.get(e);
        if (n.k === NODE.VAR) {
          throw new UnifyError(
            `expected ${nameRef('term', this.file.termName(data))}, found a variable`);
        }
        if (n.term !== data) {
          throw new UnifyError(`expected ${nameRef('term', this.file.termName(data))}`
            + `, found ${nameRef('term', this.file.termName(n.term))}`);
        }
        // Pushed in reverse so `e1` ends up on top and the arguments are
        // matched in declaration order.
        for (let i = n.args.length - 1; i >= 0; i--) this.ustack.push(n.args[i]!);
        break;
      }

      // URef i: H; S, Hi --> H; S
      case UNIFY.REF: {
        const e = this.popU();
        const h = this.uheap[data];
        if (h === undefined) {
          throw new UnifyError(`unify heap reference ${data} out of range`);
        }
        // An identity test, like `Refl`: the spec asks whether the target's
        // subexpression *is* the one the substitution supplies, not whether it
        // is structurally equal. See the note in arena.ts.
        if (e !== h) {
          throw new UnifyError(`does not match the substitution at heap slot ${data}`);
        }
        break;
      }

      // UDummy s: H; S, x --> H, x; S   (where x:s)
      case UNIFY.DUMMY: {
        if (this.mode !== UMODE.DEF) {
          throw new UnifyError('UDummy is not allowed in a theorem statement');
        }
        const e = this.popU();
        const n = this.arena.get(e);
        if (n.k !== NODE.VAR) throw new UnifyError('UDummy: expected a variable');
        // The variable must be bound and of exactly the sort the command
        // names. Compared as mm0-c does, over the whole upper byte, so that a
        // `data` with bit 7 set is rejected rather than silently masked down
        // to a legal sort.
        if (!n.bound || (0x80 | data) !== (0x80 | n.sort)) {
          throw new UnifyError('unify failure at dummy');
        }
        // A dummy must be distinct from everything else in the substitution:
        // it is freshly bound by the definition, so it may not collide with
        // anything the caller supplied. Saved subterms are skipped -- they are
        // sharing, not substitution.
        for (let i = 0; i < this.uheap.length; i++) {
          if (this.uheapSaved[i]) continue;
          const h = this.arena.get(this.uheap[i]!);
          if ((h.depsLo & n.depsLo) !== 0 || (h.depsHi & n.depsHi) !== 0) {
            throw new UnifyError('dummy disjoint variable violation');
          }
        }
        this.uheap.push(e);
        this.uheapSaved.push(false);
        break;
      }

      // UHyp (UThm):    MS, |- e; S --> MS; S, e
      // UHyp (UThmEnd): HS, e; S --> HS; S, e
      case UNIFY.HYP: {
        if (this.mode === UMODE.THM) {
          const el = this.mstack.pop();
          if (el === undefined) throw new UnifyError('UHyp: stack underflow');
          if (el.k !== EL.PROOF) {
            throw new UnifyError(
              `UHyp: expected a proof on the stack, found ${kindName(el.k)}`);
          }
          this.ustack.push(el.a);
        } else if (this.mode === UMODE.THM_END) {
          // Each hypothesis must be fully matched before the next one starts,
          // and the conclusion before the first. This requirement is what fixes
          // the layout of the stream.
          if (this.ustack.length !== 0) {
            throw new UnifyError('UHyp: the unify stack must be empty first');
          }
          const e = this.hstack.pop();
          if (e === undefined) throw new UnifyError('UHyp: hypothesis stack underflow');
          this.ustack.push(e);
        } else {
          throw new UnifyError('UHyp is not allowed in a definition');
        }
        break;
      }

      default:
        throw new UnifyError(`unknown unify command 0x${cmd.toString(16)}`);
    }
  }

  /**
   * The end-of-stream conditions. The spec writes the success case as
   * `Unify(T): S; e1..en; e --> S'; H'; .` -- the trailing `.` is an empty
   * unify stack, meaning the target was consumed exactly.
   *
   * Both conditions are enforced, not merely observed. A visualiser can get
   * away with checking the hypotheses alone, since in practice the ustack does
   * always empty; a verifier cannot, or a stream that stopped early would leave
   * part of the target unmatched and pass.
   */
  finish(): void {
    if (this.ustack.length !== 0) {
      throw new UnifyError(
        `unify stack not empty at the end (${this.ustack.length} left unmatched)`);
    }
    if (this.mode === UMODE.THM_END && this.hstack.length !== 0) {
      // An unmatched hypothesis means the proof proves a weaker statement than
      // the one declared.
      throw new UnifyError(`${this.hstack.length} hypotheses never matched`);
    }
  }
}
