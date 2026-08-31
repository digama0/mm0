// The callout: what the active step does, schematically.
//
// The point is that it is *schematic*: the stack pane already shows the
// instantiated elements, with red bars on the ones about to be consumed, so
// repeating them here would add nothing. What the callout adds is the *shape*
// of what the step takes, in the applied declaration's own variables -- so you
// read the role each stack slot plays rather than its value.

import { CLASS, type DeclClass, type MmbFile } from '../src/mmb.js';
import { EL, type El } from '../src/el.js';
import { NODE, type Arena } from '../src/arena.js';
import {
  Printer, TOK, defValue, thmStmt, varKind, type Rendered, type TokKind,
} from '../src/printer.js';
import { UMODE } from '../src/unifier.js';
import { type UnifyStep, type UnifyTrace } from '../src/machine.js';
import { type Replay, type Snapshot } from '../src/steps.js';
import * as R from './render.js';

/** One item of a stack effect. `p` marks a proof, which proof-mode keeps. */
export interface Item { p: boolean; node: Node }
/**
 * A note is text, or a mix of text and rendered expression -- `Save: also
 * pushes ⊢ a -> c to the heap` names the thing it pushes, and naming it means
 * rendering it, with its notation and its links, exactly as everywhere else.
 */
export type Note = string | Node;
export interface Schema { takes: Item[]; makes: Item[]; notes: Note[] }

/** A note built from parts, so text and rendered expressions sit together. */
export function note(...parts: (string | Node)[]): Node {
  const f = document.createDocumentFragment();
  for (const p of parts) f.append(typeof p === 'string' ? document.createTextNode(p) : p);
  return f;
}

/**
 * The notes as one block, the way the original draws them: several notes are
 * one paragraph with line breaks, not several separately indented ones.
 */
export function notesNode(notes: Note[]): HTMLElement | null {
  if (notes.length === 0) return null;
  const box = R.el('div', 'po-note');
  for (const [i, n] of notes.entries()) {
    if (i > 0) box.append(R.el('br'));
    box.append(typeof n === 'string' ? document.createTextNode(n) : n);
  }
  return box;
}

const V = (s: string): Item => ({ p: false, node: schem(s) });
/**
 * A schematic item naming one of the declaration's own variables.
 *
 * The callout names variables without an expression to render -- `consumes x ·
 * p` -- so they have to be coloured from the declaration's binders directly.
 * Left as plain text they were the one place a bound variable looked free.
 */
const Vk = (name: string, kind: TokKind): Item =>
  ({ p: false, node: wrap(R.varSpan(kind, name)) });
const P = (s: string): Item => ({ p: true, node: proofOf(schem(s)) });
/** Like `V`, but from an already-rendered expression (with links). */
const Vr = (n: Node): Item => ({ p: false, node: wrap(n) });
const Pr = (n: Node): Item => ({ p: true, node: proofOf(wrap(n)) });

/**
 * A schematic item from text, with the convertibility symbols coloured to
 * match how the stack panes render them: the obligation `≟` (U+225F) and the
 * convertibility proof `≡` (U+2261).
 *
 * Both are metatheoretic and never object notation, so colouring every
 * occurrence is safe. The `eq` notation's `=` is a term operator and is
 * deliberately left alone.
 */
function schem(s: string): Node {
  const f = document.createDocumentFragment();
  for (const part of s.split(/([≟≡])/)) {
    if (part === '') continue;
    if (part === '≟' || part === '≡') f.append(R.el('span', 'conv', part));
    else f.append(document.createTextNode(part));
  }
  return wrap(f);
}
function wrap(inner: Node): Node {
  const e = R.el('span', 'schem');
  e.append(inner);
  return e;
}
function proofOf(inner: Node): Node {
  const f = document.createDocumentFragment();
  f.append(R.el('span', 'turnstile', '⊢'), document.createTextNode(' '), inner);
  return f;
}

/**
 * Stack effects for the commands that name no declaration, in the notation of
 * the `ProofCmd` docs. `Cong` and `Unfold` are handled separately: they act on
 * a *specific* term, which the stack tells us, so they can be named concretely.
 */
const SCHEMA: Record<number, () => Schema> = {
  0x13: () => ({
    takes: [], makes: [Vk('x', TOK.DUMMY)], notes: ['also pushes x to the heap'],
  }),
  0x16: () => ({ takes: [V('e')], makes: [], notes: ['pushes ⊢ e to the heap and hypotheses'] }),
  0x17: () => ({ takes: [V('e1'), P('e2')], makes: [P('e1'), V('e1 ≟ e2')], notes: [] }),
  0x18: () => ({ takes: [V('e ≟ e')], makes: [], notes: [] }),
  0x19: () => ({ takes: [V('e1 ≟ e2')], makes: [V('e2 ≟ e1')], notes: [] }),
  0x1c: () => ({ takes: [V('e1 ≟ e2')], makes: [V('e1 ≡ e2'), V('e1 ≟ e2')], notes: [] }),
  0x1e: () => ({ takes: [V('e1 ≡ e2')], makes: [], notes: ['saves e1 ≡ e2 to the heap'] }),
  0x1f: () => ({ takes: [], makes: [], notes: ['copies the top of the stack to the heap'] }),

};

/**
 * The argument names to use for an applied term: the names from its own
 * declaration where available (`im` -> `p q`), else positional `e1..en`.
 */
export function termBinders(file: MmbFile, tid: number, nargs: number): string[] {
  const td = file.term(tid);
  if (td.numArgs === nargs) {
    return Array.from({ length: nargs }, (_, i) => file.termVarName(tid, i));
  }
  return Array.from({ length: nargs }, (_, i) => `e${i + 1}`);
}

/**
 * A term applied to argument *names* -- the applied declaration's own variables
 * -- rendered with notation and drill-down links, through the same printer the
 * arena uses. The names are atomic, so none needs parentheses of its own; the
 * notation still sets tight per the delimiters, so `not` applied to `p` reads
 * `~p` rather than `(not p)`.
 */
function appNames(ctx: R.Ctx, tid: number, names: string[]): Node {
  // The term's own binders say which of its arguments are bound, so the
  // schematic reads with the same colouring as the instantiated expression
  // beside it -- `A. x p` with `x` bound in both.
  const td = ctx.file.term(tid);
  const args = names.map((n, i) => {
    const a = td.args[i];
    return ctx.printer.atom(n, -1, varKind(a?.bound ?? false, false));
  });
  return R.expr(ctx, ctx.printer.app(tid, args), Infinity);
}

const rendered = (ctx: R.Ctx, r: Rendered): Node => R.expr(ctx, r, Infinity);

function binderNames(file: MmbFile, cls: DeclClass, num: number): string[] {
  if (cls === CLASS.TERM) {
    const n = file.term(num).numArgs;
    return Array.from({ length: n }, (_, i) => file.termVarName(num, i));
  }
  const n = file.thm(num).numArgs;
  return Array.from({ length: n }, (_, i) => file.thmVarName(num, i));
}

/** Which kind each of a declaration's binders is. Never a dummy: a dummy is
 *  not an argument, so nothing outside the proof names one. */
function binderKinds(file: MmbFile, cls: DeclClass, num: number): TokKind[] {
  const args = cls === CLASS.TERM ? file.term(num).args : file.thm(num).args;
  return args.map((a) => varKind(a.bound, false));
}

/**
 * The active step's stack effect.
 *
 * A `Thm` takes its hypotheses' proofs -- in declaration order, which is the
 * order they sit on the stack bottom to top -- then one expression per binder,
 * then the target it proves.
 */
export function schematic(
  ctx: R.Ctx, r: Replay, s: Snapshot, stack: readonly El[], onlyProof: boolean,
): Schema | null {
  const file = ctx.file;
  if (s.cmd === null) return null;

  // `Sorry` proves whatever it is given, or discharges an obligation without
  // proving it -- the spec writes them as two rules on one opcode, and which
  // ran is decided by what was on the stack. It pushes a proof only in the
  // first case.
  if (s.cmd === 0x20) {
    return s.pushed.length === 0
      ? {
        takes: [V('e1 ≟ e2')], makes: [],
        notes: ['unjustified: the obligation is discharged without being shown'],
      }
      : { takes: [V('e')], makes: [P('e')], notes: ['unjustified'] };
  }

  // `Ref i` normally copies heap slot `i` to the stack -- but if that slot
  // holds a convertibility proof it is a ConvRef, which instead *discharges* a
  // pending obligation. `pops` tells the two apart without re-deriving it.
  if (s.cmd === 0x12) {
    if (s.pops === 1) {
      // Both ends are concrete, as they are for the copying form: the
      // obligation being discharged is on the stack, and the proof that
      // discharges it is in the slot. Left schematic, the reader is told a
      // slot number and two placeholders and has to go and look up both.
      const ob = stack[stack.length - 1];
      const held = r.heap[s.data];
      return {
        takes: [ob === undefined
          ? V('e1 ≟ e2')
          : { p: false, node: wrap(R.element(ctx, r.arena, ob)) }],
        makes: [],
        notes: [held === undefined
          ? `heap slot ${s.data} holds a proof of it, discharging the obligation`
          : note(`heap slot ${s.data} holds `, R.element(ctx, r.arena, held),
            ', discharging the obligation')],
      };
    }
    const slot = r.heap[s.data];
    if (slot === undefined) return { takes: [], makes: [V(`H[${s.data}]`)], notes: [] };
    // Unlike `Term`/`Thm`, a `Ref` names a slot in *this* proof's own heap, so
    // its contents are already in this declaration's variables -- show them
    // rather than a placeholder.
    return {
      takes: [],
      makes: [{ p: slot.k === EL.PROOF, node: wrap(R.element(ctx, r.arena, slot)) }],
      notes: [`copies heap slot ${s.data} to the stack`],
    };
  }

  // `Cong` and `Unfold` apply at a specific term: the head of the obligation
  // they consume, which is sitting on the stack. Name it, and use its own
  // declaration's variable names, rather than the generic `(t e1..en)`.
  if (s.cmd === 0x1a || s.cmd === 0x1b) {
    const ob = stack[stack.length - s.pops];
    const head = ob !== undefined && ob.k === EL.COCONV ? r.arena.get(ob.a) : null;
    if (head !== null && head.k === NODE.APP) {
      const bs = termBinders(file, head.term, head.args.length);
      const name = file.termName(head.term);
      if (s.cmd === 0x1a) {
        return {
          // Pushed in reverse, so the parts are dealt with in declaration order.
          takes: [Vr(pair(appNames(ctx, head.term, bs), '≟',
            appNames(ctx, head.term, bs.map((x) => `${x}'`))))],
          makes: bs.map((x, i) => {
            const k = ctx.file.term(head.term).args[i];
            const kind = varKind(k?.bound ?? false, false);
            return Vr(pair(R.varSpan(kind, x), '≟', R.varSpan(kind, `${x}'`)));
          }).reverse(),
          notes: bs.length === 0 ? [`${name} takes no arguments`] : [],
        };
      }
      // `Unfold`'s `e` is the def's value, available because a def's unify
      // stream *is* its value. Shown over the def's own binders, matching the
      // left-hand side.
      const def = defValue(ctx.printer, head.term);
      const val = def === null ? schem('e') : rendered(ctx, def.value);
      const val2 = def === null ? schem('e') : rendered(ctx, def.value);
      return {
        takes: [Vr(pair(appNames(ctx, head.term, bs), '≟', schem("e'"))), Vr(val)],
        makes: [Vr(pair(val2, '≟', schem("e'")))],
        notes: [`unfolds ${name}`],
      };
    }
    return s.cmd === 0x1a
      ? { takes: [V("(t e1..en) ≟ (t e1'..en')")],
        makes: [V("en ≟ en'"), V('…'), V("e1 ≟ e1'")], notes: [] }
      : { takes: [V("(t e1..en) ≟ e'"), V('e')], makes: [V("e ≟ e'")], notes: [] };
  }

  // Term / TermSave
  if (s.cmd === 0x10 || s.cmd === 0x11) {
    const bs = binderNames(file, CLASS.TERM, s.data);
    const ks = binderKinds(file, CLASS.TERM, s.data);
    const e = (): Node => appNames(ctx, s.data, bs);
    return {
      takes: bs.map((n, i) => Vk(n, ks[i] ?? TOK.VAR)),
      makes: [Vr(e())],
      notes: s.cmd === 0x11
        ? [note('Save: also pushes ', e(), ' to the heap')] : [],
    };
  }

  // Thm / ThmSave
  if (s.cmd === 0x14 || s.cmd === 0x15) {
    const st = thmStmt(ctx.printer, s.data);
    const bs = binderNames(file, CLASS.THM, s.data);
    const hyps = Array.from({ length: st.hyps.length }, (_, i) => file.hypName(s.data, i));
    const notes: Note[] = [];
    if (st.hyps.length > 0) {
      const named = `${st.hyps.length} hypothes${st.hyps.length > 1 ? 'es' : 'is'}`
        + ` (${hyps.join(', ')})`;
      // Proof mode filters the binders and target out of the effect, so naming
      // them would describe slots the callout no longer shows.
      notes.push(onlyProof ? named
        : `${named}, ${bs.length} binder${bs.length === 1 ? '' : 's'}, then the target`);
    }
    if (s.cmd === 0x15) {
      notes.push(note('Save: also pushes ', proofOf(rendered(ctx, st.concl)), ' to the heap'));
    }
    return {
      takes: [
        ...st.hyps.map((h) => Pr(rendered(ctx, h))),
        ...bs.map((n, i) => Vk(n, binderKinds(file, CLASS.THM, s.data)[i] ?? TOK.VAR)),
        Vr(rendered(ctx, st.concl)),
      ],
      makes: [Pr(rendered(ctx, st.concl))],
      notes,
    };
  }

  return SCHEMA[s.cmd]?.() ?? null;
}

/**
 * The callout while inside the unifier: what *this* unify command does.
 *
 * Same idea as the proof-step callout -- schematic, in the applied
 * declaration's own variables -- but for the sub-machine. `URef` is the
 * exception: it names a slot of *this* substitution, so its contents are
 * concrete and worth showing, exactly as `Ref` shows the heap slot it copies.
 */
export function uschematic(ctx: R.Ctx, u: UnifyTrace, us: UnifyStep): Schema | null {
  if (us.cmd === null) return null;

  // UTerm / UTermSave
  if (us.cmd === 0x30 || us.cmd === 0x31) {
    const bs = binderNames(ctx.file, CLASS.TERM, us.data);
    const ks = binderKinds(ctx.file, CLASS.TERM, us.data);
    const notes: Note[] = [];
    if (us.cmd === 0x31) notes.push('USave: also pushes the whole term to the substitution');
    if (bs.length > 1) {
      notes.push('arguments are pushed in reverse, so they match in declaration order');
    }
    return {
      // `UTerm t: S, (t e1..en) --> S, en, ..., e1` -- the head must be `t`,
      // and its arguments go back reversed so `e1` is matched first.
      takes: [Vr(appNames(ctx, us.data, bs))],
      // The same names as the row above, so they are drawn the same way: `x`
      // is bound in `lam x e2 e3` and is still bound when it comes back off.
      makes: bs.map((n, i) => Vk(n, ks[i] ?? TOK.VAR)).reverse(),
      notes,
    };
  }

  // URef
  if (us.cmd === 0x32) {
    return {
      // Not "consumes e": what it takes off the stack has to *be* `H[i]`,
      // which is the whole content of the command.
      takes: [V(`H[${us.data}]`)], makes: [],
      notes: ['the top of the unify stack must be exactly this'],
    };
  }

  // UDummy
  if (us.cmd === 0x33) {
    return {
      takes: [Vk('x', TOK.DUMMY)], makes: [],
      notes: [`x must be a variable of sort ${ctx.file.sortName(us.data)},`
        + ' distinct from the substitution'],
    };
  }

  // UHyp: in THM the proof comes off the main stack, in THM_END off the
  // hypotheses that `Hyp` built.
  if (us.cmd === 0x36) {
    return {
      takes: [], makes: [V('e')],
      notes: [u.mode === UMODE.THM_END
        ? 'takes the next hypothesis, to check against the one declared'
        : 'takes a hypothesis’s proof ⊢ e off the main stack'],
    };
  }
  return null;
}

function pair(a: Node, op: string, b: Node): Node {
  const f = document.createDocumentFragment();
  f.append(a, R.el('span', 'conv', ` ${op} `), b);
  return f;
}

/** One row of the effect: `consumes  a · b · c`. */
function effRow(cls: string, label: string, items: Item[], filter: boolean): Node | null {
  const vis = filter ? items.filter((x) => x.p) : items;
  if (vis.length === 0) return null;
  const row = R.el('div', `eff ${cls}`);
  row.append(R.el('span', 'lbl', label));
  const box = R.el('span', 'items');
  for (const [i, x] of vis.entries()) {
    if (i > 0) box.append(R.el('span', 'sep', ' · '));
    box.append(x.node);
  }
  row.append(box);
  return row;
}

/** The declaration identity line: `T6 theorem mpd (a b c: wff): $ … $`. */
export function declHead(
  file: MmbFile, cls: DeclClass, num: number, kind: string, sig: string, right: Node | null,
): HTMLElement {
  const head = R.el('div', 'po-head');
  const decl = R.el('span', 'po-decl');
  const prefix = cls === CLASS.SORT ? 's' : cls === CLASS.TERM ? 't' : 'T';
  decl.append(R.el('span', 'idtag', `${prefix}${num}`), document.createTextNode(' '));
  decl.append(R.el('span', `kind ${R.kindClass(kind)}`, kind), document.createTextNode(' '));
  // Three classes, not two: the id tag above already distinguishes them, and
  // reading the name from the wrong table gave a sort the name of whichever
  // theorem shared its number -- `s0 sort ax_1` for `wff`.
  const b = R.el('b', undefined,
    cls === CLASS.SORT ? file.sortName(num)
      : cls === CLASS.TERM ? file.termName(num) : file.thmName(num));
  // The signature carries its own leading space when it has binders.
  decl.append(b, R.el('span', 'po-sig', sig));
  head.append(decl);
  if (right !== null) head.append(right);
  return head;
}

export { effRow, R as Render };
export type { Arena, Printer };
