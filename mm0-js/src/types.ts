// Expression types: `(bound, sort, deps)`.
//
// Port of the typing rules in mm0-c/verifier.c, which is the only place they
// are written down: a visualiser of the proof stream needs none of this, since
// it checks no types at all.
//
// Every expression the machine builds carries a type: whether it is a bound
// variable, its sort, and the set of bound variables it may depend on. The
// dependency set is what makes the disjoint-variable conditions checkable, and
// those are what make substitution sound.
//
// Dependency sets are 55 bits, so they do not fit in a JS number's 53 bits of
// integer precision. They are carried as two halves -- `lo` holding bits 0..31
// and `hi` bits 32..54 -- rather than as BigInt or an object, because they are
// computed per argument of every `Term` and `Thm` on the hot path, and a pair
// of numbers costs no allocation. This is the same split `Arg` already uses for
// a binder's declared dependencies.

/**
 * Bit 55 of a type is reserved and must be zero, so a declaration may have at
 * most 55 bound variables. mm0-c enforces the same limit by checking that its
 * `next_bv` cursor has not shifted past bit 55.
 */
export const MAX_BOUND_VARS = 55;

/** The low half of the singleton dependency set `{i}`. */
export const bitLo = (i: number): number => (i < 32 ? (1 << i) >>> 0 : 0);
/** The high half of the singleton dependency set `{i}`. */
export const bitHi = (i: number): number => (i >= 32 ? (1 << (i - 32)) >>> 0 : 0);

/** Whether the set `(lo, hi)` contains `i`. */
export const hasBit = (lo: number, hi: number, i: number): boolean =>
  i < 32 ? (lo & (1 << i)) !== 0 : (hi & (1 << (i - 32))) !== 0;

/**
 * Whether every member of `(lo, hi)` is below `n`.
 *
 * The two branches exist because JS shifts count modulo 32, so `1 << 32` is 1
 * rather than 0 and a single expression would silently compute the wrong mask
 * at the boundary.
 */
export function depsBelow(lo: number, hi: number, n: number): boolean {
  if (n >= MAX_BOUND_VARS) return true;
  // At or above bit 32 every low bit is already below `n`, so only `hi` is
  // constrained; below it, `hi` must be empty entirely.
  if (n >= 32) return (hi & ~((1 << (n - 32)) - 1)) === 0;
  return hi === 0 && (lo & ~((1 << n) - 1)) === 0;
}

/**
 * Whether a value of type `from` can be used where `to` is expected.
 *
 * The sorts must be equal, and if `to` is a bound variable then `from` must be
 * one too -- a bound variable may stand in for a regular one, never the
 * reverse. mm0-c writes this as bit arithmetic over the shared upper byte;
 * spelled out, it is exactly these two conditions.
 */
export function sortsCompatible(
  fromBound: boolean, fromSort: number, toBound: boolean, toSort: number,
): boolean {
  if (fromSort !== toSort) return false;
  return fromBound === toBound || fromBound;
}
