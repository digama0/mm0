// Elements of the proof machine's stack and heap.
//
// Split out from machine.ts because the unifier needs them too -- `UHyp` takes
// hypothesis proofs off the main stack -- and the machine invokes the unifier,
// so sharing them through either module would be a cycle.

/** Stack/heap element discriminants. Numeric, so a test is a field compare. */
export const EL = { EXPR: 0, PROOF: 1, CONV: 2, COCONV: 3 } as const;
export type ElKind = (typeof EL)[keyof typeof EL];

/**
 * An element of the stack or heap: an expression `e`, a proof `|- e`, a
 * convertibility proof `e1 = e2`, or an outstanding convertibility obligation
 * `e1 =?= e2`. `b` is unused for the first two.
 */
export interface El {
  k: ElKind;
  a: number;
  b: number;
}

export const expr = (a: number): El => ({ k: EL.EXPR, a, b: 0 });
export const proof = (a: number): El => ({ k: EL.PROOF, a, b: 0 });
export const conv = (a: number, b: number): El => ({ k: EL.CONV, a, b });
export const coconv = (a: number, b: number): El => ({ k: EL.COCONV, a, b });

/** A human-readable name for an element's kind, for error messages. */
export function kindName(k: ElKind): string {
  switch (k) {
    case EL.EXPR: return 'an expression';
    case EL.PROOF: return 'a proof';
    case EL.CONV: return 'a convertibility proof';
    case EL.COCONV: return 'a convertibility obligation';
  }
}
