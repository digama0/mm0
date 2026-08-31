// The notation printer, against peano.mmb.
//
// The expected strings are from EXPLORER_DESIGN.md, where they were validated
// against peano.mm1 itself -- `syl`'s statement, `pim`'s and `sb`'s values --
// so matching them here ties this renderer to the source, not merely to the
// Rust one.
//
// The bulk check is stronger than a string comparison: a def's value is built
// by its *proof* stream and independently spelled out by its *unify* stream,
// and this renders both and requires them to agree. That is 158 cross-checks
// between two unrelated paths through the file.

import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { CLASS, MmbFile } from '../src/mmb.js';
import { EL, Machine } from '../src/machine.js';
import {
  Printer, TOK, defValue, statement, termSignature, thmStmt, toText, render,
} from '../src/printer.js';

const here = join(dirname(fileURLToPath(import.meta.url)), '..', '..', 'test');

let failures = 0;
function check(name: string, actual: unknown, expected: unknown): void {
  const a = JSON.stringify(actual), e = JSON.stringify(expected);
  if (a === e) console.log(`  ok   ${name}`);
  else {
    console.log(`  FAIL ${name}\n         got ${a}\n    expected ${e}`);
    failures++;
  }
}

const f = MmbFile.parse(new Uint8Array(readFileSync(join(here, 'peano.mmb'))));
const p = new Printer(f);

const termId = (name: string): number => {
  for (let i = 0; i < f.numTerms; i++) if (f.termName(i) === name) return i;
  throw new Error(`no term ${name}`);
};
const thmId = (name: string): number => {
  for (let i = 0; i < f.numThms; i++) if (f.thmName(i) === name) return i;
  throw new Error(`no theorem ${name}`);
};

console.log('hypotheses and conclusions');
// peano.mm0 declares `axiom ax_mp (a b: wff): $ a -> b $ > $ a $ > $ b $`.
{
  const s = thmStmt(p, thmId('ax_mp'));
  check('ax_mp hypotheses', s.hyps.map((h) => toText(h)), ['a -> b', 'a']);
  check('ax_mp conclusion', toText(s.concl), 'b');
}
{
  const s = thmStmt(p, thmId('syl'));
  check('syl hypotheses', s.hyps.map((h) => toText(h)), ['b -> c', 'a -> b']);
  check('syl conclusion', toText(s.concl), 'a -> c');
}

console.log('statements');
// A theorem's signature *is* its statement, written the way an .mm0 file
// writes one. peano.mm0 literally declares
// `axiom ax_mp (a b: wff): $ a -> b $ > $ a $ > $ b $`.
// The leading space belongs to the binders, so a signature composes straight
// onto the declaration's name with nothing inserted between the two.
check('ax_mp', toText(statement(p, thmId('ax_mp'))),
  ' (a b: wff): $ a -> b $ > $ a $ > $ b $');
check('syl', toText(statement(p, thmId('syl'))),
  ' (a b c: wff): $ b -> c $ > $ a -> b $ > $ a -> c $');
// Bound binders read `{x: nat}`, and a regular binder names the bound
// variables it depends on.
check('ax_gen', toText(statement(p, thmId('ax_gen'))),
  ' {x: nat} (p: wff x): $ p $ > $ A. x p $');
// The `:` belongs to the syntax, not to the binders: `term tru: wff` and
// `theorem itru: $ T. $` are how MM0 writes these, and dropping the colon with
// the binder list produced `tru wff`, which is not MM0 at all. peano has 15
// nullary terms and 47 binder-less theorems, so this was not a corner.
check('a nullary term keeps its colon', toText(termSignature(p, termId('tru'))), ': wff');
check('a binder-less theorem keeps its colon',
  toText(statement(p, thmId('itru'))), ': $ T. $');
// What the two cases above are *for*: the declaration line the UI builds, with
// no space of its own between the name and the signature. Spacing the name
// instead prints `tru : wff`, with the stray space.
{
  const term = (n: string): string => {
    const t = termId(n);
    const kind = f.term(t).unifyStart === null ? 'term' : 'def';
    return `${kind} ${n}${toText(termSignature(p, t))}`;
  };
  const thm = (n: string): string => `theorem ${n}${toText(statement(p, thmId(n)))}`;
  check('a nullary term composes', term('tru'), 'term tru: wff');
  check('a term with binders composes', term('im'), 'term im (p q: wff): wff');
  check('a binder-less theorem composes', thm('itru'), 'theorem itru: $ T. $');
  check('a theorem with binders composes', thm('syl'),
    'theorem syl (a b c: wff): $ b -> c $ > $ a -> b $ > $ a -> c $');
  // A def's value is part of its declaration, and the dummies its value
  // quantifies over are written `{.y: nat}` between the args and the return
  // type -- `sb` has both.
  check('a def carries its value', term('an'), 'def an (a b: wff): wff = $ ~(a -> ~b) $');
  check('and its dummies', term('sb'),
    'def sb (a: nat) {x: nat} (p: wff x) {.y: nat}: wff'
    + ' = $ A. y (y = a -> A. x (x = y -> p)) $');
  check('a plain term has neither', term('im'), 'term im (p q: wff): wff');
}
{
  const missing: string[] = [];
  for (let i = 0; i < f.numTerms; i++) {
    if (!toText(termSignature(p, i)).includes(':')) missing.push(f.termName(i));
  }
  for (let i = 0; i < f.numThms; i++) {
    if (!toText(statement(p, i)).includes(':')) missing.push(f.thmName(i));
  }
  check('every signature has one', missing.slice(0, 5), []);
}
{
  // Laid out as a document, so a long statement breaks after each `>` --
  // keeping the separator with the hypothesis it follows.
  const long = statement(p, thmId('grecaux2eqd'));
  const wide = toText(long), narrow = toText(long, 60);
  check('a long statement is one line when it fits', wide.includes('\n'), false);
  check('and breaks when it does not', narrow.includes('\n'), true);
  check('breaking after the separator, not before',
    narrow.split('\n').filter((l) => l.trim().startsWith('>')).length, 0);
  check('every hypothesis gets its own line',
    narrow.split('\n').filter((l) => l.trim().endsWith('$ >')).length, 6);
}

console.log('anonymous binders');
// MM1's `_` marks a binder with no name. Printed literally, `lam x _ _` has
// two arguments that are neither distinguishable from each other nor usable to
// say which one anything refers to -- so they are positional instead, the same
// `e1..en` the callout falls back to. hol.mmb has 18 of them; peano has none,
// which is why this reads a second file.
{
  const h = MmbFile.parse(new Uint8Array(readFileSync(join(here, 'hol.mmb'))));
  const hp = new Printer(h);
  const hterm = (name: string): string => {
    for (let i = 0; i < h.numTerms; i++) {
      if (h.termName(i) === name) return `term ${name}${toText(termSignature(hp, i))}`;
    }
    throw new Error(`no term ${name}`);
  };
  check('an anonymous binder is named for its position',
    hterm('lam'), 'term lam {x: term} (e2: type) (e3: term x): term');
  check('and consecutive ones still group',
    hterm('im'), 'term im (e1 e2: wff): wff');
  // Nothing is renamed that had a name.
  let named = 0;
  for (let i = 0; i < h.numTerms; i++) {
    for (let j = 0; j < h.term(i).args.length; j++) {
      if (h.termVarName(i, j) === '_') named++;
    }
  }
  check('no underscore survives as a name', named, 0);
}

console.log('def values');
// `an` is `$ ~(a -> ~b) $` -- the parenthesis is the precedence rule working,
// and `~` setting tight against what follows is the Delm rule working.
check('an', toText(defValue(p, termId('an'))!.value), '~(a -> ~b)');
check('pim', toText(defValue(p, termId('pim'))!.value), 'E. x p /\\ A. x (p -> q)');
// `sb` quantifies over a dummy `y`, introduced by the stream, not by the args.
{
  const d = defValue(p, termId('sb'))!;
  check('sb', toText(d.value), 'A. y (y = a -> A. x (x = y -> p))');
  check('sb dummies', d.dummies.map((x) => x.name), ['y']);
}
// Only a def has a value; `im` is a primitive term.
check('a plain term has no value', defValue(p, termId('im')), null);

console.log('coverage');
// Every theorem's statement and every def's value must reconstruct.
{
  const errs: string[] = [];
  let stmts = 0, values = 0;
  for (let i = 0; i < f.numThms; i++) {
    try { thmStmt(p, i); stmts++; } catch (e) { errs.push(`${f.thmName(i)}: ${(e as Error).message}`); }
  }
  for (let i = 0; i < f.numTerms; i++) {
    try { if (defValue(p, i) !== null) values++; } catch (e) {
      errs.push(`${f.termName(i)}: ${(e as Error).message}`);
    }
  }
  check('reconstruction errors', errs.slice(0, 5), []);
  check('statements reconstructed', stmts, 2723);
  check('def values reconstructed', values, 158);
}

console.log('proof stream vs unify stream');
// The real cross-check: replay each def and render the value the *proof*
// stream builds, then compare with what the *unify* stream says it is. The two
// encodings are independent, so agreement pins the machine, the reader and the
// printer against each other at once.
{
  const mismatches: string[] = [];
  let compared = 0;
  for (const d of f.decls()) {
    if (d.cls !== CLASS.TERM || !d.isDef || d.proof.isNull) continue;
    const m = new Machine(f, d);
    const it = d.proof;
    while (it.step()) m.apply(it.cmd, it.data);
    const el = m.stack[0];
    if (el === undefined || el.k !== EL.EXPR) continue;
    const built = toText(p.node(m.arena, el.a, (i) => f.termVarName(d.num, i)));
    const declared = toText(defValue(p, d.num)!.value);
    compared++;
    if (built !== declared) {
      mismatches.push(`${f.termName(d.num)}: built ${built} / declared ${declared}`);
    }
  }
  check('def value mismatches', mismatches.slice(0, 5), []);
  check('defs compared', compared, 158);
}

console.log('layout');
// The content of a layout is its non-whitespace tokens, compared without the
// whitespace rather than with it collapsed: breaking replaces a space with a
// newline and an indent, so the two forms differ in whitespace by design and
// only the tokens are supposed to be invariant.
const content = (r: Parameters<typeof render>[0], w?: number): string =>
  render(r, w).filter((t) => t.k !== TOK.SPACE && t.k !== TOK.NEWLINE)
    .map((t) => t.s).join('');
// The invariant that makes breaking safe: laying out at any width changes the
// whitespace and nothing else.
{
  const s = thmStmt(p, thmId('syl'));
  const flat = render(s.concl);
  check('flat has no newline', flat.some((t) => t.k === TOK.NEWLINE), false);

  const big = defValue(p, termId('sb'))!.value;
  const wide = toText(big);
  const narrow = toText(big, 20);
  check('narrow output breaks', narrow.includes('\n'), true);
  check('wide output does not', wide.includes('\n'), false);
  check('breaking preserves the tokens', content(big, 20), content(big));
  console.log(`\n${narrow}\n`);
}

// Across the whole library: for every def value, every width from 10 to 60
// yields the same non-whitespace content.
{
  const bad: string[] = [];
  let checked = 0;
  for (let i = 0; i < f.numTerms; i++) {
    const d = defValue(p, i);
    if (d === null) continue;
    const want = content(d.value);
    for (let w = 10; w <= 60; w += 10) {
      checked++;
      if (content(d.value, w) !== want) {
        bad.push(`${f.termName(i)} at width ${w}`);
        break;
      }
    }
  }
  check('layout is width-independent in content', bad.slice(0, 5), []);
  check('layouts checked', checked, 158 * 6);
}

console.log('delimiters are never stranded');
// A delimiter is glued to what it delimits, so a break must never fall
// between them: an opening parenthesis alone above the expression it opens, or
// a closing one alone below, is the layout coming apart at exactly the joins
// that are meant to hold. peano's `Delm` set is `left = ([{~`, `right = ),]}`.
{
  const d = f.delimiters()!;
  const stranded: string[] = [];
  let lines = 0;
  const inspect = (name: string, r: ReturnType<typeof defValue>): void => {
    if (r === null) return;
    for (const w of [20, 30, 45, 60, 78]) {
      for (const line of toText(r.value, w).split('\n')) {
        const t = line.trim();
        if (t === '') continue;
        lines++;
        // A left delimiter ending a line means the thing it opens went to the
        // next one; a right delimiter starting one means the same in reverse.
        if (d.isLeft(t.charCodeAt(t.length - 1))) stranded.push(`${name}@${w}: ends "${t}"`);
        if (d.isRight(t.charCodeAt(0))) stranded.push(`${name}@${w}: starts "${t}"`);
      }
    }
  };
  for (let i = 0; i < f.numTerms; i++) inspect(f.termName(i), defValue(p, i));
  check('none end with an opening delimiter', stranded.slice(0, 5), []);
  // Most def values fit on one line even at 20 columns; the check is only
  // meaningful because 157 of the 790 layouts do break.
  check('lines inspected', lines, 1555);
}

console.log(failures ? `\n${failures} failure(s)` : '\nall checks passed');
process.exit(failures ? 1 : 0);
