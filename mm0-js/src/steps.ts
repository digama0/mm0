// Per-step snapshots of one declaration's proof, for the step view.
//
// There is no wire between producer and consumer here, which removes most of
// what a stepping protocol would have to do: no arena to serialise and no ids
// to keep stable across two requests. The view holds the same `Arena` the
// machine built, and the unify traces reference it directly rather than being
// recomputed by replaying to a step a second time.
//
// The machine is the *verifier*, unchanged. Stepping is a view over a
// verification run, not a second implementation of one -- so a step view can
// never disagree with what the file actually does, and a declaration that
// fails to verify still produces every snapshot up to the failure.

import { PROOF, type Decl, type MmbFile } from './mmb.js';
import { Arena } from './arena.js';
import { EL, type El } from './el.js';
import { Machine, MachineError, type Limits, type UnifyTrace, type Where } from './machine.js';

/** The machine state *before* one command. */
export interface Snapshot {
  /** Step number; `steps[n]` is the state after every earlier command ran. */
  i: number;
  /** The command about to run, or null for the terminal state. */
  cmd: number | null;
  data: number;
  /**
   * How much of the heap exists at this point. The heap is append-only, so a
   * snapshot's heap is `replay.heap.slice(0, heapLen)` -- keeping this a
   * number is what stops a long proof being quadratic in memory.
   */
  heapLen: number;
  /** Likewise for the hypothesis list. */
  hypsLen: number;
  /**
   * How many stack elements this command consumes -- counted by the machine as
   * it pops, since only it knows an arity like `Thm`'s (target + arguments +
   * one proof per `UHyp`). The top `pops` elements are what this step eats.
   */
  pops: number;
  /**
   * What this command leaves on the stack in their place.
   *
   * The stack is not append-only, so it cannot be a length the way the heap
   * is -- but it is only ever changed at the top, so `(pops, pushed)` is the
   * whole delta and copying the stack per step is unnecessary. Storage becomes
   * proportional to the number of commands rather than to the sum of the stack
   * depths, and this is also exactly the diff the view wants to highlight:
   * `pops` elements struck through, `pushed` marked as new.
   */
  pushed: El[];
  /** The unify runs this command invoked, if tracing was on. */
  unify: UnifyTrace[];
  /** Set if this command failed; there are no snapshots after it. */
  err: string | null;
  /**
   * Where inside this step it failed, structured. The view marks the rows this
   * names -- a failing unify command is a row of the sub-step listing, and
   * guessing which one from the fact that the run failed marked the terminal
   * row instead of the one that did not match.
   */
  errAt: Where[];
}

export interface Replay {
  decl: Decl;
  /** Shared with every snapshot; node ids index into it. */
  arena: Arena;
  /** The final heap. A snapshot's heap is its first `heapLen` entries. */
  heap: El[];
  /** The final hypothesis list, likewise. */
  hyps: number[];
  steps: Snapshot[];
  /** The declaration failed to verify; `steps` still covers everything up to it. */
  error: string | null;
  /** The proof used `Sorry`, so it does not count as verified. */
  usesSorry: boolean;
}

export interface ReplayOptions {
  /**
   * Record every unify run. Off by default -- see `Machine.onUnify`. The step
   * view wants it; a listing of declarations does not.
   */
  unify?: boolean;
  /** What the proof may name; defaults to everything in the file. */
  limits?: Limits;
}

/**
 * Replay one declaration, snapshotting the state before each command.
 *
 * Errors are captured rather than thrown: a declaration that fails is exactly
 * the one a user most wants to step through, so the snapshots up to the
 * failure are the point, not a lost cause.
 */
export function replay(file: MmbFile, d: Decl, opts: ReplayOptions = {}): Replay {
  const steps: Snapshot[] = [];
  let error: string | null = null;

  // The machine's constructor checks the declaration's binders, so a
  // declaration whose *arguments* are malformed fails before any of its proof
  // runs. `verify` is total for any input and this has to be too: it threw out
  // of the view instead, leaving a blank pane and an uncaught error, on
  // exactly the declaration the file said to look at.
  let m: Machine;
  try {
    m = opts.limits === undefined
      ? new Machine(file, d)
      : new Machine(file, d, opts.limits);
  } catch (e) {
    if (!(e instanceof MachineError)) throw e;
    return {
      decl: d, steps: [], arena: new Arena(), heap: [], hyps: [],
      error: e.trail, usesSorry: false,
    };
  }

  // The traces of the command currently being applied. `runUnify` may fire
  // more than once for one command -- an end-of-declaration check follows the
  // last one -- so they are collected per step rather than assumed singular.
  let pending: UnifyTrace[] = [];
  if (opts.unify === true) m.onUnify = t => pending.push(t);

  // Cloned, not consumed: `Decl.proof` is a live cursor, so replaying a
  // declaration twice from the same `Decl` would otherwise find it exhausted
  // and report an empty proof. A view that re-renders is exactly that case.
  /** How many of the machine's collected failures have been attributed. */
  let seen = 0;
  const it = d.proof.clone();
  if (!it.isNull) {
    while (it.step()) {
      const before = m.stack.length;
      const snap: Snapshot = {
        i: steps.length, cmd: it.cmd, data: it.data,
        heapLen: m.heap.length, hypsLen: m.hyps.length,
        pops: 0, pushed: [], unify: [], err: null, errAt: [],
      };
      steps.push(snap);
      pending = [];
      let stopped = false;
      try {
        m.apply(it.cmd, it.data);
      } catch (e) {
        if (!(e instanceof MachineError)) throw e;
        snap.err = e.trail;
        snap.errAt = e.where;
        error = e.trail;
        stopped = true;
      }
      // Failures the machine carried on past belong to this step too -- and a
      // step can have several, since each argument of a `Thm` is checked
      // separately. Without this the view showed nothing at all for them: they
      // are not thrown, so nothing here saw them.
      if (m.errors.length > seen) {
        const newly = m.errors.slice(seen);
        seen = m.errors.length;
        // Added to what the step threw, not written over it: a step can carry
        // on past several failures and *then* hit one that stops it, and the
        // one that stopped it was the message being lost. Collected first,
        // since that is the order they happened in.
        const all = [...newly.map((e) => e.trail), ...(snap.err === null ? [] : [snap.err])];
        snap.err = all.join('; ');
        snap.errAt = newly[0]!.where;
        error ??= snap.err;
      }
      snap.pops = m.popped;
      // Whatever sits above the region the command cut back to is what it left.
      snap.pushed = m.stack.slice(before - snap.pops);
      snap.unify = pending;
      // Only a throw ends the replay; a failure it carried on past does not.
      if (stopped) break;
    }
    if (error === null && it.error !== null) error = it.error.message;
  }

  // The terminal state, and with it the declaration's own header check -- the
  // fourth unify site, and the one that ties the proof to what was declared.
  if (error === null) {
    const snap: Snapshot = {
      i: steps.length, cmd: null, data: 0,
      heapLen: m.heap.length, hypsLen: m.hyps.length,
      pops: 0, pushed: [], unify: [], err: null, errAt: [],
    };
    steps.push(snap);
    pending = [];
    try {
      m.endCheck(d);
      if (m.errors.length > seen) {
        const newly = m.errors.slice(seen);
        seen = m.errors.length;
        snap.err = newly.map((e) => e.trail).join('; ');
        snap.errAt = newly[0]!.where;
        error ??= snap.err;
      }
    } catch (e) {
      if (!(e instanceof MachineError)) throw e;
      snap.err = e.trail;
      snap.errAt = e.where;
      error = e.trail;
    }
    snap.unify = pending;
  }

  return {
    decl: d, arena: m.arena, heap: m.heap, hyps: m.hyps,
    steps, error, usesSorry: m.usesSorry,
  };
}

/**
 * The stack as it stands before step `i`, rebuilt from the deltas.
 *
 * O(i) in the number of commands, which is why the view should hold one of
 * these and step it rather than calling this per render: `advance` is O(1).
 */
export function stackAt(r: Replay, i: number): El[] {
  const out: El[] = [];
  for (let n = 0; n < i && n < r.steps.length; n++) {
    const s = r.steps[n]!;
    out.length -= s.pops;
    for (const el of s.pushed) out.push(el);
  }
  return out;
}

/**
 * A stack that walks with the view. Stepping forward applies one delta;
 * stepping back re-runs from the start, since the delta does not record what
 * was removed. Rebuilding is cheap -- a whole 1620-step proof is a few
 * thousand array operations -- and recording the popped elements as well would
 * double the storage to make the rarer direction O(1).
 */
export class StackCursor {
  private readonly r: Replay;
  private stack: El[] = [];
  private at = 0;

  constructor(r: Replay) { this.r = r; }

  get step(): number { return this.at; }
  /** The live stack. Do not mutate it; it is the cursor's own. */
  get value(): readonly El[] { return this.stack; }

  seek(i: number): readonly El[] {
    if (i < this.at) { this.stack = []; this.at = 0; }
    while (this.at < i && this.at < this.r.steps.length) {
      const s = this.r.steps[this.at]!;
      this.stack.length -= s.pops;
      for (const el of s.pushed) this.stack.push(el);
      this.at++;
    }
    return this.stack;
  }
}

/**
 * Whether a step belongs to the proof-level view -- the one that hides
 * expression plumbing and leaves the logical argument.
 *
 * A step qualifies when it puts a *proof* on the stack: `Thm`/`ThmSave`,
 * `Sorry`, and `Ref i` where heap slot `i` holds a proof, since using a
 * hypothesis or an earlier result is an inference rather than plumbing. A
 * `Ref` to an expression stays hidden, as does ConvRef -- proof mode hides
 * convertibility throughout.
 *
 * The heap is append-only, so a slot's contents are the same at every step and
 * this needs no per-step state. Failing steps and the terminal state are never
 * hidden: they are where the user is trying to get to.
 */
export function isProofStep(r: Replay, s: Snapshot): boolean {
  if (s.cmd === null || s.err !== null) return true;
  switch (s.cmd) {
    case PROOF.THM:
    case PROOF.THM_SAVE:
    case PROOF.SORRY:
      return true;
    case PROOF.REF: {
      const el = r.heap[s.data];
      return el !== undefined && el.k === EL.PROOF;
    }
    default:
      return false;
  }
}
