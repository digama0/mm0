// Rendering expressions and machine elements to DOM.
//
// The printer emits tokens rather than text precisely so this can wrap each in
// its own element: a term's name becomes a link to its declaration, a
// notation's constant token becomes that same link (clicking `->` opens `im`),
// and a variable gets its own span. The design notes record why text would not
// do -- recolouring a rendered row does nothing when every name already sits
// in its own span, so the consumer has to see the pieces.

import { CLASS, type MmbFile } from '../src/mmb.js';
import { type Arena } from '../src/arena.js';
import { EL, type El } from '../src/el.js';
import { PREC_MAX } from '../src/mmb.js';
import { Printer, TOK, render, type Rendered, type TokKind } from '../src/printer.js';

/** How wide an expression may be before the printer breaks it. */
const WIDTH = 78;

export interface Ctx {
  file: MmbFile;
  printer: Printer;
  /** Names for the variables of the declaration being viewed. */
  varName: (i: number) => string;
  /** Where a term or theorem name should link. */
  href: (cls: number, num: number) => string;
}

const el = (tag: string, cls?: string, text?: string): HTMLElement => {
  const e = document.createElement(tag);
  if (cls !== undefined) e.className = cls;
  if (text !== undefined) e.textContent = text;
  return e;
};

/**
 * A name, as a link where there is somewhere to go and as plain text where
 * there is not.
 *
 * A declaration this file does not have -- an id past the end of a table, or
 * one in a stream that stopped before reaching it -- has no address, and an
 * anchor to `#` is a link that looks live and goes nowhere. It keeps the
 * colouring that says it is a name either way.
 */
function named(cls: string, href: string, text: string): HTMLElement {
  if (href === '#') return el('span', cls, text);
  const a = el('a', cls, text) as HTMLAnchorElement;
  a.href = href;
  return a;
}

/** Lay a rendered expression out and turn its tokens into elements. */
export function expr(ctx: Ctx, r: Rendered, width = WIDTH): DocumentFragment {
  const frag = document.createDocumentFragment();
  for (const t of render(r, width)) {
    switch (t.k) {
      case TOK.CONST:
      case TOK.NAME:
        // Both link to the term. For a notation the constant *is* the handle:
        // there is no head name to click, so `->` has to be it.
        frag.append(named('nm', ctx.href(CLASS.TERM, t.term), t.s));
        break;
      case TOK.SORT:
        // A sort is a declaration like any other, so its name links too.
        frag.append(named('sortname', ctx.href(CLASS.SORT, t.term), t.s));
        break;
      case TOK.VAR:
      case TOK.BOUND:
      case TOK.DUMMY:
        frag.append(varSpan(t.k, t.s));
        break;
      // The `$` fences and the surrounding punctuation are structure rather
      // than content, so they are told apart from the formula they delimit.
      case TOK.FENCE:
        frag.append(el('span', 'fence', t.s));
        break;
      case TOK.PUNCT:
        frag.append(el('span', 'punct', t.s));
        break;
      case TOK.ERROR:
        frag.append(el('span', 'missing', t.s));
        break;
      default:
        // Spaces, newlines and printer parentheses carry no meaning of their
        // own; `white-space: pre-wrap` on the slot keeps them.
        frag.append(document.createTextNode(t.s));
    }
  }
  return frag;
}

/**
 * A variable, in the colour its kind is drawn in.
 *
 * The three are told apart because the difference is what the binding
 * conditions are about: whether a name can be captured, and whether anything
 * outside can refer to it at all. Shared, because the callout names variables
 * too -- schematically, without an expression to render -- and one that looked
 * different there would be saying they were different variables.
 */
export function varSpan(kind: TokKind, text: string): HTMLElement {
  return el('span',
    kind === TOK.DUMMY ? 'bvar dummy' : kind === TOK.BOUND ? 'bvar' : 'var', text);
}

/** Render an arena node. */
export function node(ctx: Ctx, arena: Arena, id: number, width = WIDTH): DocumentFragment {
  return expr(ctx, ctx.printer.node(arena, id, ctx.varName), width);
}

/**
 * An arena node with its sort tag.
 *
 * The unify panes hold bare expressions rather than `El`s, so they cannot go
 * through `element` -- but they are expressions all the same, and were the
 * only place the view showed one untagged.
 */
export function taggedNode(ctx: Ctx, arena: Arena, id: number): DocumentFragment {
  const frag = document.createDocumentFragment();
  frag.append(node(ctx, arena, id), sortTag(ctx, arena.get(id).sort));
  return frag;
}

/**
 * Render one stack or heap element.
 *
 * The four kinds are visually distinct because confusing them is the whole
 * difficulty of reading this machine: `⊢ e` is a proof, a bare `e` an
 * expression tagged with its sort, `e ≟ e'` an outstanding obligation and
 * `e ≡ e'` a discharged one.
 */
export function element(ctx: Ctx, arena: Arena, x: El): DocumentFragment {
  const frag = document.createDocumentFragment();
  switch (x.k) {
    case EL.PROOF:
      frag.append(el('span', 'turnstile', '⊢ '));
      frag.append(node(ctx, arena, x.a));
      break;
    case EL.EXPR: {
      frag.append(node(ctx, arena, x.a));
      // Only expressions get a sort tag: a proof's sort is always the provable
      // one, and a convertibility's two sides share a sort, so there is
      // nowhere unambiguous to hang it.
      frag.append(sortTag(ctx, arena.get(x.a).sort));
      break;
    }
    case EL.COCONV:
    case EL.CONV:
      frag.append(node(ctx, arena, x.a));
      frag.append(el('span', 'conv', x.k === EL.CONV ? ' ≡ ' : ' ≟ '));
      frag.append(node(ctx, arena, x.b));
      break;
  }
  return frag;
}

/**
 * An expression's `: sort` tag. The sort links to its declaration, like every
 * other name the view shows.
 */
export function sortTag(ctx: Ctx, sort: number): HTMLElement {
  const ann = el('span', 'sortann');
  ann.append(document.createTextNode(': '));
  ann.append(sortLink(ctx, sort));
  return ann;
}

/**
 * `pub theorem` -> `k-pubtheorem`, `local def` -> `k-localdef`.
 *
 * Shared, because two spellings of this drifted apart: taking the last word
 * instead of removing the spaces turns `local def` into `k-def`, so the same
 * declaration got a different class depending on which view drew it.
 */
export const kindClass = (kind: string): string => `k-${kind.replace(/ /g, '')}`;

/**
 * A sort's name, linking to its declaration -- or marked as an error where
 * there is no declaration to link to. An id past the end of the table names
 * nothing, and should look the same wherever it is drawn.
 */
export function sortLink(ctx: Ctx, sort: number): HTMLElement {
  if (sort >= ctx.file.numSorts) return el('span', 'missing', `s${sort}`);
  const a = el('a', 'sortname', ctx.file.sortName(sort)) as HTMLAnchorElement;
  a.href = ctx.href(CLASS.SORT, sort);
  return a;
}

/**
 * One numbered row of a stack or heap pane.
 *
 * The marker gutter is always present, so a row never shifts when a marker
 * appears -- the panes are read by comparing them across steps, and content
 * that moves for a cosmetic reason is worse than useless.
 *
 * `why` says in words what the row's colour means. Colour alone requires the
 * legend to be read and remembered, and distinguishes nothing for a reader who
 * cannot tell the two markers apart.
 */
export function slot(
  idx: number, body: Node, classes: string[] = [], why = '',
): HTMLElement {
  const row = el('div', ['slot', ...classes].join(' '));
  if (why !== '') row.title = why;
  row.append(el('span', 'mk', '▸'));
  row.append(el('span', 'idx', String(idx)));
  const val = el('span', 'val');
  val.append(body);
  row.append(val);
  return row;
}

/** A pane that has nothing to show, distinguishing empty from filtered. */
export function empty(text: string): HTMLElement {
  return el('div', 'empty', text);
}

export { el, PREC_MAX };
