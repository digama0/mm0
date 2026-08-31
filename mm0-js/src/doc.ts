// A Wadler pretty-printing document.
//
// Wadler's "A prettier printer", in Lindig's strict formulation ("Strictly
// Pretty"): a document describes *where* it may break and how far to indent if
// it does, and layout picks breaks to fit a width. A `group` is laid out on one
// line if it fits and broken at every one of its own `line`s if it does not --
// all-or-nothing per group, which is what stops a long expression from breaking
// raggedly in the middle.
//
// mm0-rs prints through the same algebra (elab::lisp::pretty over the `pretty`
// crate). Leaves are `Tok`s rather than strings so that layout can stay
// agnostic to whether the output becomes text or one span per token.

/** A rendered token; see printer.ts for the kinds. */
export interface Tok {
  k: number;
  s: string;
  term: number;
  idx: number;
}

export const DOC = {
  /** A leaf token. Must not contain a newline. */
  TOK: 0,
  /** A sequence. */
  CAT: 1,
  /**
   * A break opportunity: `alt` when its group is flat, a newline and the
   * current indent when broken.
   */
  LINE: 2,
  /** Indent by `i` when breaking inside. */
  NEST: 3,
  /** Flatten if it fits, otherwise break every LINE directly inside. */
  GROUP: 4,
} as const;

export type Doc =
  | { k: typeof DOC.TOK; t: Tok }
  | { k: typeof DOC.CAT; ds: Doc[] }
  | { k: typeof DOC.LINE; alt: string }
  | { k: typeof DOC.NEST; i: number; d: Doc }
  | { k: typeof DOC.GROUP; d: Doc };

export const docTok = (t: Tok): Doc => ({ k: DOC.TOK, t });
export const cat = (ds: Doc[]): Doc => (ds.length === 1 ? ds[0]! : { k: DOC.CAT, ds });
/** A break opportunity that is a space when flat. */
export const line = (): Doc => ({ k: DOC.LINE, alt: ' ' });
/** A break opportunity that disappears when flat. */
export const softline = (): Doc => ({ k: DOC.LINE, alt: '' });
export const nest = (i: number, d: Doc): Doc => ({ k: DOC.NEST, i, d });
export const group = (d: Doc): Doc => ({ k: DOC.GROUP, d });

const FLAT = 0, BREAK = 1;

interface Item { i: number; mode: number; d: Doc }

/**
 * Does the flattened front of the work list fit in `w` columns? Scans until the
 * budget is spent or a genuine break is reached -- everything after that break
 * is on a later line and so cannot overflow this one.
 */
function fits(w: number, items: Item[]): boolean {
  // A local stack, walked without mutating the caller's list.
  const stack = items.slice().reverse();
  while (stack.length > 0) {
    if (w < 0) return false;
    const it = stack.pop()!;
    switch (it.d.k) {
      case DOC.TOK:
        w -= it.d.t.s.length;
        break;
      case DOC.CAT:
        for (let i = it.d.ds.length - 1; i >= 0; i--) {
          stack.push({ i: it.i, mode: it.mode, d: it.d.ds[i]! });
        }
        break;
      case DOC.NEST:
        stack.push({ i: it.i + it.d.i, mode: it.mode, d: it.d.d });
        break;
      case DOC.LINE:
        if (it.mode === BREAK) return true;
        w -= it.d.alt.length;
        break;
      case DOC.GROUP:
        // A group nested inside something being measured flat is itself flat.
        stack.push({ i: it.i, mode: FLAT, d: it.d.d });
        break;
    }
  }
  return w >= 0;
}

/**
 * Lay a document out to `width` columns, returning the tokens in order. A
 * break emits a token of kind `newlineKind` whose text is a newline followed
 * by the indent, so a consumer joining `s` gets correct text for free.
 *
 * `width = Infinity` lays everything flat, which is the single-line rendering.
 */
export function layout(d: Doc, width: number, spaceKind: number, newlineKind: number): Tok[] {
  const out: Tok[] = [];
  // Everything starts in BREAK mode: the outermost document is allowed to use
  // as many lines as it needs, and each group decides for itself.
  const stack: Item[] = [{ i: 0, mode: BREAK, d }];
  let col = 0;
  while (stack.length > 0) {
    const it = stack.pop()!;
    switch (it.d.k) {
      case DOC.TOK:
        out.push(it.d.t);
        col += it.d.t.s.length;
        break;
      case DOC.CAT:
        for (let i = it.d.ds.length - 1; i >= 0; i--) {
          stack.push({ i: it.i, mode: it.mode, d: it.d.ds[i]! });
        }
        break;
      case DOC.NEST:
        stack.push({ i: it.i + it.d.i, mode: it.mode, d: it.d.d });
        break;
      case DOC.LINE:
        if (it.mode === FLAT) {
          if (it.d.alt.length > 0) {
            out.push({ k: spaceKind, s: it.d.alt, term: -1, idx: -1 });
            col += it.d.alt.length;
          }
        } else {
          out.push({ k: newlineKind, s: `\n${' '.repeat(it.i)}`, term: -1, idx: -1 });
          col = it.i;
        }
        break;
      case DOC.GROUP: {
        const flat = { i: it.i, mode: FLAT, d: it.d.d };
        if (it.mode === FLAT || fits(width - col, [flat, ...stack.slice().reverse()])) {
          stack.push(flat);
        } else {
          stack.push({ i: it.i, mode: BREAK, d: it.d.d });
        }
        break;
      }
    }
  }
  return out;
}
