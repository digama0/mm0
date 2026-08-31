// The expression arena: the expressions a proof builds, as the stream directs.
//
// Deliberately *not* hash-consed. `Refl` is specified as an identity test on
// the two sides -- no structural comparison -- so sharing is the producer's
// job: a compiler that wants a `Refl` to succeed must have built both sides as
// the same expression, and one that constructs two equal-but-separate
// expressions and tries to `Refl` them is meant to fail. The machine's only
// job is to construct what it is told to.
//
// So interning here would not "make Refl exact"; it would make this machine
// accept proofs that mm0-c rejects, by silently merging what the producer kept
// apart. Confirmed empirically: with interning removed, all of peano still
// replays with zero errors -- because mm0-rs's exporter already shares every
// repeated subexpression, which is why `Ref` is 62% of all commands.
//
// The DAG is therefore still a DAG, but its sharing is exactly the sharing the
// producer chose, which is also what a debugging view should show.
//
// One arena per declaration, and they stay small -- the largest in peano is 227
// nodes -- so nodes are ordinary objects rather than parallel typed arrays.

/** Node discriminants. Numeric, so a test is a field compare, not a string one. */
export const NODE = { VAR: 0, APP: 1 } as const;

/**
 * A variable: an argument of the declaration, or a `Dummy` introduced by the
 * proof. `idx` indexes the declaration's variable-name list, which runs past
 * the arguments to cover dummies in order of their `Dummy` commands.
 */
export interface VarNode {
  k: typeof NODE.VAR;
  idx: number;
  sort: number;
  /** A bound variable: an argument declared `{x: s}`, or a `Dummy`. */
  bound: boolean;
  /**
   * A `Dummy`: bound, but local to the proof rather than an argument. Recorded
   * by the machine that creates it, since that is the only place the
   * distinction is known -- a reader looking at the node afterwards cannot
   * tell it from a bound argument.
   */
  dummy: boolean;
  /** Bits 0..31 of the dependency set. */
  depsLo: number;
  /** Bits 32..54 of the dependency set. */
  depsHi: number;
}

/** A term applied to arguments: `(t e1 ... en)`. */
export interface AppNode {
  k: typeof NODE.APP;
  term: number;
  args: number[];
  /** The applied term's return sort. */
  sort: number;
  /** Never bound: only a variable can be. Present so a node's type can be
   *  read without discriminating first. */
  bound: false;
  depsLo: number;
  depsHi: number;
}

export type Node = VarNode | AppNode;

export class Arena {
  readonly nodes: Node[] = [];

  /**
   * The sort of each variable by index: the declaration's argument sorts, then
   * the sort each `Dummy` names. Parallel to the `VarN` name list, and its
   * length is the next variable index.
   */
  readonly varSorts: number[] = [];

  get length(): number { return this.nodes.length; }

  /**
   * Allocate a fresh variable. `bound` and the dependency set are the
   * variable's type: a bound variable depends on exactly itself, a regular one
   * on whatever its binder declares.
   *
   * The returned node's `idx` is the number of variables allocated so far, and
   * unlike an arena id it is *observable*: it is the key into the declaration's
   * `VarN` name list, which runs over the binders and then the dummies in order
   * of their `Dummy` commands. So this must be called exactly once per binder
   * and once per `Dummy`, and never for anything else -- an extra call renames
   * every variable after it. (An extra `app` is harmless by contrast: arena ids
   * are only ever compared for equality.)
   */
  newVar(sort: number, bound: boolean, depsLo: number, depsHi: number, dummy = false): number {
    const idx = this.varSorts.length;
    this.varSorts.push(sort);
    const id = this.nodes.length;
    this.nodes.push({ k: NODE.VAR, idx, sort, bound, dummy, depsLo, depsHi });
    return id;
  }

  /** Allocate an application. */
  app(term: number, args: number[], sort: number, depsLo: number, depsHi: number): number {
    const id = this.nodes.length;
    this.nodes.push({ k: NODE.APP, term, args, sort, bound: false, depsLo, depsHi });
    return id;
  }

  get(i: number): Node {
    const n = this.nodes[i];
    if (n === undefined) throw new RangeError(`arena id ${i} out of range`);
    return n;
  }

  /** The application at `i`, or null if it is a variable. */
  asApp(i: number): AppNode | null {
    const n = this.get(i);
    return n.k === NODE.APP ? n : null;
  }

  sortOf(i: number): number { return this.get(i).sort; }
}
