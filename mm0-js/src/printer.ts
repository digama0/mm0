// Printing expressions with notation, from the mmb alone.
//
// One renderer over two *sources* -- arena nodes, and unify streams read as
// constructions -- because `app()` takes already-rendered arguments and neither
// source is visible to it. Splitting those into a renderer apiece, one for
// signatures and statements and one over the arena, costs a pair that has to be
// kept in lockstep by hand; with one implementation that class of drift is gone.
//
// Output is a Wadler document (see doc.ts) laid out to a width, rather than a
// string. At infinite width that is exactly the single-line rendering a
// string-building renderer produces; at a finite width it breaks and indents,
// which one cannot. Layout yields tokens, not text, so a caller can join them or
// wrap each in its own element -- the design notes record that recolouring a
// rendered row does not work, since every name already sits in its own span.
//
// The printing rule is the one in mm0-c/mmb.md, "The `Nota` table"; it is the
// precedence logic of mm0-rs's elab::lisp::pretty (`expr_paren`), fed by the
// mmb reader instead of an elaborated Environment -- which is the whole point
// of the table existing.

import {
  APP_PREC, PREC_MAX, UNIFY,
  type Arg, type Delimiters, type MmbFile, type Nota, type StreamIter,
} from './mmb.js';
import { NODE, type Arena } from './arena.js';
import { cat, docTok, group, layout, line, nest, type Doc, type Tok } from './doc.js';

export type { Tok } from './doc.js';

export const TOK = {
  /** A constant token of a notation: `->`, `~`, `[`. Links to its term. */
  CONST: 0,
  /** A term's name, in the s-expression fallback. Links to its term. */
  NAME: 1,
  /** A free variable: an argument declared `(x: s)`. */
  VAR: 2,
  /** A parenthesis added by the printer, not by any notation. */
  PAREN: 3,
  /** Inter-token space. */
  SPACE: 4,
  /** A line break and its indent. */
  NEWLINE: 5,
  /** A placeholder for something that could not be rendered. */
  ERROR: 6,
  /** A sort's name. Links to its declaration. */
  SORT: 7,
  /** The `$` fences around a formula: structure, not content. */
  FENCE: 8,
  /** Punctuation of the surrounding syntax -- `{`, `}`, `(`, `)`, `:`, `>`. */
  PUNCT: 9,
  /**
   * A bound variable: an argument declared `{x: s}`, which a term may quantify
   * over. Told apart from a free one because the distinction is what the
   * dependency conditions are about -- `A. x p` is only well formed when `x`
   * is bound, and reading a proof means knowing which names can be captured.
   */
  BOUND: 10,
  /**
   * A dummy: a bound variable local to a proof or a def's value, introduced by
   * `Dummy` or `UDummy` and written `{.x: s}`. Drawn as a bound variable in
   * italic, because that is what it is -- one that nothing outside can name.
   */
  DUMMY: 11,
} as const;
export type TokKind = (typeof TOK)[keyof typeof TOK];

/**
 * A sort as a token: named where it exists, and marked as an error where it
 * does not.
 *
 * An id past the end of the table names nothing. Drawn as an ordinary sort it
 * reads as one that happens to be called `s48`, which is exactly the reading
 * that hides the defect -- the declaration looks well formed and is not.
 */
function sortTok(file: MmbFile, sort: number): Tok {
  return sort < file.numSorts
    ? tok(TOK.SORT, file.sortName(sort), sort)
    : tok(TOK.ERROR, `s${sort}`);
}

/** Which of the three a variable is, from what the machine recorded about it. */
export const varKind = (bound: boolean, dummy: boolean): TokKind =>
  dummy ? TOK.DUMMY : bound ? TOK.BOUND : TOK.VAR;

/**
 * Which parts of a signature to draw.
 *
 * The list column shows the longest form that fits, giving up the affordable
 * parts first; each form is a document in its own right rather than the full
 * one cut down as text, so it keeps its colouring and its links.
 */
export interface SigOpts { binders?: boolean; hyps?: boolean }

/** How far to indent the continuation lines of a broken application. */
const INDENT = 2;

/**
 * A rendered expression: the document, the precedence it binds at, and the
 * first and last characters of its text.
 *
 * The characters are carried rather than recomputed because the delimiter rule
 * needs them at every join, and they are unaffected by layout -- breaking only
 * ever replaces a space.
 */
export interface Rendered {
  doc: Doc;
  prec: number;
  first: number;
  last: number;
}

const tok = (k: TokKind, s: string, term = -1, idx = -1): Tok => ({ k, s, term, idx });

const leaf = (t: Tok, prec: number): Rendered => ({
  doc: docTok(t),
  prec,
  first: t.s.length > 0 ? t.s.charCodeAt(0) : -1,
  last: t.s.length > 0 ? t.s.charCodeAt(t.s.length - 1) : -1,
});

/** Lay a rendering out to `width` columns; `Infinity` keeps it on one line. */
export function render(r: Rendered, width = Infinity): Tok[] {
  return layout(r.doc, width, TOK.SPACE, TOK.NEWLINE);
}

/** Lay out and flatten to text. */
export function toText(r: Rendered, width = Infinity): string {
  let out = '';
  for (const t of render(r, width)) out += t.s;
  return out;
}

export class Printer {
  readonly file: MmbFile;
  private readonly nota: Map<number, Nota>;
  private readonly delims: Delimiters | null;

  constructor(file: MmbFile) {
    this.file = file;
    this.nota = file.notations();
    this.delims = file.delimiters();
  }

  /**
   * Whether no space falls between two adjacent pieces: the left ends with a
   * left delimiter, or the right begins with a right delimiter -- the two
   * places the tokenizer would split them anyway. With no `Delm` table every
   * join keeps its space, which is also how the Rust behaves.
   */
  private tight(left: number, last: number): boolean {
    const d = this.delims;
    if (d === null) return false;
    return (left >= 0 && d.isLeft(left)) || (last >= 0 && d.isRight(last));
  }

  /**
   * Join pieces with a single space, dropped where the delimiters say tight.
   *
   * How each join breaks follows mm0-rs's own printer (elab::lisp::pretty,
   * `append`/`infixl`), and it is not Wadler's default:
   *
   * * Every join but the last is its own group, so it breaks *independently* —
   *   fill behaviour. Wadler's all-or-nothing would strand an operator on a
   *   line of its own, turning `a -> b` into `a` / `->` / `b`.
   * * The last join is a plain break that participates in the enclosing group,
   *   so when the whole application breaks, it breaks *there* — after the
   *   operator, giving `a ->` / `  b`.
   * * A tight join is not a break at all. A delimiter is glued to what it
   *   delimits, so breaking there strands it: an opening parenthesis ends up
   *   alone on a line above the expression it opens, and a closing one alone
   *   below. It would be a *legal* break -- a delimiter is exactly where the
   *   tokenizer splits regardless -- but legality is not the question.
   *
   * `spaced` forces every join to keep its space, for the s-expression
   * fallback, whose juxtaposition is never delimiter-tight.
   */
  private join(
    pieces: readonly Rendered[], spaced = false,
  ): { doc: Doc; first: number; last: number } {
    const ds: Doc[] = [];
    let first = -1, last = -1;
    for (let i = 0; i < pieces.length; i++) {
      const p = pieces[i]!;
      if (ds.length > 0) {
        const isLast = i === pieces.length - 1;
        // A tight join contributes nothing: no space, and no opportunity.
        if (!spaced && this.tight(last, p.first)) { /* glued */ }
        else ds.push(isLast ? line() : group(line()));
      }
      ds.push(p.doc);
      if (first < 0) first = p.first;
      if (p.last >= 0) last = p.last;
    }
    return { doc: cat(ds), first, last };
  }

  /**
   * Wrap a rendering in parentheses when the context demands a precedence
   * tighter than it offers. This is the rule that makes `a -> b -> c` group
   * while `(a -> b) -> c` keeps its parens. The parens set tight or spaced by
   * the same delimiter rule as any other token.
   */
  private paren(r: Rendered, req: number): Rendered {
    if (req <= r.prec) return r;
    const l = leaf(tok(TOK.PAREN, '('), PREC_MAX);
    const rp = leaf(tok(TOK.PAREN, ')'), PREC_MAX);
    const j = this.join([l, r, rp]);
    return { doc: j.doc, prec: PREC_MAX, first: j.first, last: j.last };
  }

  /**
   * Render an application whose arguments are already rendered, each with the
   * precedence it stands at. Agnostic to where the arguments came from, which
   * is what lets the arena and the unify stream share this.
   */
  app(tid: number, args: readonly Rendered[]): Rendered {
    const n = this.nota.get(tid);
    if (n !== undefined) {
      if (n.isCoercion) {
        // A coercion is invisible: it prints as its one argument, at that
        // argument's own precedence, so the caller parenthesises against the
        // argument rather than against the coercion.
        const a = args[0];
        if (a !== undefined) return a;
      } else {
        const pieces: Rendered[] = [];
        for (const lit of n.lits) {
          if ('const' in lit) {
            // A notation's constant is the drill-down link to its term, which
            // is what replaces the head name the s-expr form would have shown.
            pieces.push(leaf(tok(TOK.CONST, lit.const, tid), PREC_MAX));
          } else {
            const a = args[lit.var];
            pieces.push(a === undefined
              ? leaf(tok(TOK.ERROR, '?'), PREC_MAX)
              : this.paren(a, lit.prec));
          }
        }
        const j = this.join(pieces);
        return { doc: group(nest(INDENT, j.doc)), prec: n.prec, first: j.first, last: j.last };
      }
    }

    // No notation: the s-expression fallback. A nullary term is atomic; an
    // application juxtaposes head and arguments at APP_PREC with each argument
    // at `max`, and the caller wraps the whole where a tighter context needs
    // it -- so `f x` stays bare at the top level and becomes `(f x)` as an
    // argument. This reading is what makes the spec's "wrapping the whole in
    // parentheses if p > 1024" mean anything; the alternative, always
    // parenthesising, would leave the 1024 idle.
    const name = leaf(tid < this.file.numTerms
      ? tok(TOK.NAME, this.file.termName(tid), tid)
      : tok(TOK.ERROR, `t${tid}`), PREC_MAX);
    if (args.length === 0) return name;
    // The juxtaposition is always spaced, as MM1's own printer does it: only
    // each argument's own parens set tight.
    const pieces = [name, ...args.map((a) => this.paren(a, PREC_MAX))];
    const j = this.join(pieces, true);
    return { doc: group(nest(INDENT, j.doc)), prec: APP_PREC, first: j.first, last: j.last };
  }

  /** Render an arena node, in terms of the declaration's variable names. */
  node(arena: Arena, id: number, varName: (i: number) => string): Rendered {
    const n = arena.get(id);
    if (n.k === NODE.VAR) return leaf(tok(varKind(n.bound, n.dummy), varName(n.idx), -1, n.idx), PREC_MAX);
    const args: Rendered[] = new Array(n.args.length);
    for (let i = 0; i < n.args.length; i++) {
      args[i] = this.node(arena, n.args[i]!, varName);
    }
    return this.app(n.term, args);
  }

  /** Render an arena node at a required precedence, parenthesising if needed. */
  nodeAt(arena: Arena, id: number, varName: (i: number) => string, req: number): Rendered {
    return this.paren(this.node(arena, id, varName), req);
  }

  /** Render a bare name as an atom, for a callout's schematic arguments. */
  atom(name: string, idx = -1, k: TokKind = TOK.VAR): Rendered {
    return leaf(tok(k, name, -1, idx), PREC_MAX);
  }
}

/**
 * Reads a unify stream as a *construction*.
 *
 * The stream is a matcher -- when a theorem is applied it destructures the
 * target -- but read forwards it spells out the statement, which is how
 * mm0-rs's `mmb::import::parse_unify` recovers one. Sharing (`save`) simply
 * repeats the rendering here, since this is for display.
 */
class UnifyReader {
  private readonly p: Printer;
  private readonly it: StreamIter;
  private readonly varName: (i: number) => string;
  /** Unify-heap slot -> rendering. Starts as the declaration's binders. */
  private readonly fwd: (Rendered | null)[] = [];
  private nextVar: number;
  /** Dummies introduced by `UDummy`, in stream order. */
  readonly dummies: { name: string; sort: number }[] = [];

  constructor(
    p: Printer, it: StreamIter, args: readonly Arg[], varName: (i: number) => string,
  ) {
    this.p = p;
    this.it = it;
    this.varName = varName;
    this.nextVar = args.length;
    // Seeded from the *binders*, not just their names: a statement rebuilt
    // from the unify stream has to colour its variables the same way the
    // machine's own expressions do, and only the declaration says which of
    // them are bound.
    for (const [i, a] of args.entries()) {
      this.fwd.push(p.atom(varName(i), i, varKind(a.bound, false)));
    }
  }

  /** Read one expression off the stream. */
  go(): Rendered {
    if (!this.it.step()) {
      throw new Error(this.it.error ? this.it.error.message : 'unify stream ended early');
    }
    switch (this.it.cmd) {
      case UNIFY.TERM:
      case UNIFY.TERM_SAVE: {
        const tid = this.it.data;
        const save = this.it.cmd === UNIFY.TERM_SAVE;
        // Reserve the slot *before* reading the arguments, so that nested
        // saves number in stream order.
        const slot = this.fwd.length;
        if (save) this.fwd.push(null);
        const n = this.p.file.term(tid).numArgs;
        const args: Rendered[] = new Array(n);
        for (let i = 0; i < n; i++) args[i] = this.go();
        const out = this.p.app(tid, args);
        if (save) this.fwd[slot] = out;
        return out;
      }
      case UNIFY.REF: {
        const r = this.fwd[this.it.data];
        if (r === undefined || r === null) {
          throw new Error(`unify heap reference ${this.it.data} out of range`);
        }
        return r;
      }
      case UNIFY.DUMMY: {
        // A def's value is the only place these occur -- UDummy is legal only
        // in UDef mode -- and they are not otherwise recoverable, since the
        // term's args do not mention them.
        const idx = this.nextVar++;
        const name = this.varName(idx);
        const r = this.p.atom(name, idx, TOK.DUMMY);
        this.fwd.push(r);
        this.dummies.push({ name, sort: this.it.data });
        return r;
      }
      case UNIFY.HYP:
        throw new Error('unexpected hypothesis marker');
      default:
        throw new Error(`unknown unify command 0x${this.it.cmd.toString(16)}`);
    }
  }

  /** True if the next command is `UHyp`, consuming it only when it is. */
  tryHyp(): boolean {
    const at = this.it.pos;
    if (!this.it.step()) return false;
    if (this.it.cmd === UNIFY.HYP) return true;
    this.it.pos = at;
    return false;
  }
}

/**
 * A def's value, reconstructed from its unify stream over the def's own
 * binders, with the dummies it quantifies over in the order it introduces
 * them. Null for a plain term, which has no value.
 */
export function defValue(
  p: Printer, tid: number,
): { value: Rendered; dummies: { name: string; sort: number }[] } | null {
  const td = p.file.term(tid);
  if (td.unifyStart === null) return null;
  const r = new UnifyReader(
    p, p.file.unifyAt(td.unifyStart), td.args, (i) => p.file.termVarName(tid, i));
  const value = r.go();
  return { value, dummies: r.dummies };
}

/**
 * The grouping key for a binder: two consecutive binders can share a group
 * exactly when they agree on all of this, i.e. when the source could have
 * written them as `(a b: wff)`.
 *
 * Bound variables each carry a distinct bit in their type identifying *which*
 * bound variable they are, so they are keyed on sort alone; regular variables
 * additionally have to agree on their dependencies.
 */
const binderKey = (a: Arg): string =>
  a.bound ? `b${a.sort}` : `r${a.sort}:${a.depsLo},${a.depsHi}`;

/**
 * A declaration's binders in MM0 source syntax, e.g. ` {x: nat} (p q: wff x)`.
 *
 * Each group carries its own leading space, including the first, so a
 * signature composes directly onto the declaration's name with nothing
 * between: `im (a b: wff): wff` and `tru: wff` both fall out. Spacing the
 * *name* instead needs the signature to know whether it has any binders, and
 * gets `tru : wff` when it does not, which is what this used to print.
 *
 * Consecutive binders of the same type are grouped as the source writes them.
 * A regular binder names the bound variables it depends on, bit `i` of its
 * dependency mask referring to the `i`th *bound* variable -- and bound
 * variables always precede the regular ones that depend on them, so the list
 * of names is always populated in time.
 */
export function binders(
  file: MmbFile, args: readonly Arg[], name: (i: number) => string,
  dummies: readonly { name: string; sort: number }[] = [],
): Doc[] {
  const bvs: string[] = [];
  const out: Doc[] = [];
  const punct = (t: string): Doc => docTok(tok(TOK.PUNCT, t));
  const sp = (): Doc => docTok(tok(TOK.SPACE, ' '));
  let i = 0;
  while (i < args.length) {
    const a = args[i]!;
    const key = binderKey(a);
    let j = i + 1;
    while (j < args.length && binderKey(args[j]!) === key) j++;
    out.push(sp(), punct(a.bound ? '{' : '('));
    for (let n = i; n < j; n++) {
      if (n > i) out.push(sp());
      out.push(docTok(tok(a.bound ? TOK.BOUND : TOK.VAR, name(n))));
      if (a.bound) bvs.push(name(n));
    }
    out.push(punct(':'), sp());
    // The sort links to its own declaration, like any other name.
    out.push(docTok(sortTok(file, a.sort)));
    if (!a.bound) {
      for (const [k, bv] of bvs.entries()) {
        if (a.dependsOn(k)) out.push(sp(), docTok(tok(TOK.BOUND, bv)));
      }
    }
    out.push(punct(a.bound ? '}' : ')'));
    i = j;
  }
  // A def's dummies are bound variables local to its value, written `{.x: nat}`.
  // They are not exposed to anything outside: nothing in the arguments or the
  // return type can depend on one, so unlike the bound arguments above they
  // never join `bvs`.
  let k = 0;
  while (k < dummies.length) {
    const sort = dummies[k]!.sort;
    let n = k + 1;
    while (n < dummies.length && dummies[n]!.sort === sort) n++;
    out.push(sp(), punct('{'));
    for (let m = k; m < n; m++) {
      if (m > k) out.push(sp());
      out.push(docTok(tok(TOK.DUMMY, `.${dummies[m]!.name}`)));
    }
    out.push(punct(':'), sp(), docTok(sortTok(file, sort)), punct('}'));
    k = n;
  }
  return out;
}

/**
 * A term or def's signature, as MM0 source writes the declaration:
 * `{x: nat} (p: wff x): wff`, and for a def `(a b: wff): wff = $ ~(a -> ~b) $`.
 *
 * A def's value is part of its declaration rather than a separate fact about
 * it, so it belongs here -- the step view showing how the value gets built is
 * a different question from what the value is.
 */
export function termSignature(p: Printer, tid: number, opts: SigOpts = {}): Rendered {
  const td = p.file.term(tid);
  const def = defValue(p, tid);
  const ds = opts.binders === false ? []
    : binders(p.file, td.args, (i) => p.file.termVarName(tid, i),
      def === null ? [] : def.dummies);
  // The `:` is part of the syntax, not a separator between the binders and the
  // return type: a nullary term is written `term tru: wff`, not `term tru wff`.
  ds.push(docTok(tok(TOK.PUNCT, ':')), docTok(tok(TOK.SPACE, ' ')));
  ds.push(docTok(sortTok(p.file, td.ret.sort)));
  // The return type names the bound variables it may depend on, exactly as a
  // regular binder does. Legal but rare: none of peano, hol or hello_mmc has a
  // term with a dependent return type, so this is written to match mm0-rs's
  // `render_binders` rather than validated against a library.
  const bvs: string[] = [];
  for (const [i, a] of td.args.entries()) if (a.bound) bvs.push(p.file.termVarName(tid, i));
  for (const [k, bv] of bvs.entries()) {
    if (td.ret.dependsOn(k)) {
      ds.push(docTok(tok(TOK.SPACE, ' ')), docTok(tok(TOK.BOUND, bv)));
    }
  }
  if (def !== null) {
    const fence = (t: string): Doc => docTok(tok(TOK.FENCE, t));
    const sp = (): Doc => docTok(tok(TOK.SPACE, ' '));
    ds.push(sp(), docTok(tok(TOK.PUNCT, '=')), line(),
      fence('$'), sp(), def.value.doc, sp(), fence('$'));
  }
  return { doc: group(nest(INDENT, cat(ds))), prec: PREC_MAX, first: -1, last: -1 };
}

/**
 * A theorem's statement as MM0 writes one: `(binders): $ h1 $ > $ h2 $ > $ c $`.
 *
 * Laid out as a document rather than concatenated, so a long statement breaks
 * after each `>` -- which keeps the separator with the hypothesis it follows,
 * the same rule the infix layout uses. mm0-rs's own printer does exactly this
 * in `hyps_and_ret`.
 */
export function statement(p: Printer, tid: number, opts: SigOpts = {}): Rendered {
  const td = p.file.thm(tid);
  const { hyps, concl } = thmStmt(p, tid);
  const ds = opts.binders === false ? []
    : binders(p.file, td.args, (i) => p.file.thmVarName(tid, i));
  const fence = (t: string): Doc => docTok(tok(TOK.FENCE, t));
  const sp = (): Doc => docTok(tok(TOK.SPACE, ' '));
  // A binder-less theorem is written `theorem itru: $ T. $`: the `:` is part
  // of the syntax and not a separator, so it is unconditional.
  ds.push(docTok(tok(TOK.PUNCT, ':')), line());
  if (opts.hyps === false && hyps.length > 0) {
    // The hypotheses stand in for themselves: what the shortest form has to
    // keep is the conclusion, which is what the row is being read for.
    ds.push(docTok(tok(TOK.PUNCT, '…')), sp(), docTok(tok(TOK.PUNCT, '>')), line());
  } else {
    for (const h of hyps) {
      ds.push(fence('$'), sp(), h.doc, sp(), fence('$'), sp(),
        docTok(tok(TOK.PUNCT, '>')), line());
    }
  }
  ds.push(fence('$'), sp(), concl.doc, sp(), fence('$'));
  return { doc: group(nest(INDENT, cat(ds))), prec: PREC_MAX, first: -1, last: -1 };
}

/**
 * A theorem's statement, reconstructed from its unify stream: the hypotheses
 * in declaration order, and the conclusion.
 *
 * The stream holds the conclusion *first*, then the hypotheses in *reverse*
 * declaration order, because it is a matcher: the unify stack starts with the
 * statement to match, so the conclusion is the first thing it must describe,
 * and `UHyp` takes hypotheses off a stack where they sit in declaration order,
 * so the first popped is the last declared.
 */
export function thmStmt(p: Printer, tid: number): { hyps: Rendered[]; concl: Rendered } {
  const td = p.file.thm(tid);
  const r = new UnifyReader(
    p, p.file.unifyAt(td.unifyStart), td.args, (i) => p.file.thmVarName(tid, i));
  const concl = r.go();
  const hyps: Rendered[] = [];
  while (r.tryHyp()) hyps.push(r.go());
  hyps.reverse();
  return { hyps, concl };
}
