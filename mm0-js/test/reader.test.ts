// Validates the reader against peano.mmb.
//
// The expected numbers are not invented for this test: they are the counts
// recorded in EXPLORER_DESIGN.md, which were themselves cross-checked against
// `mm0-rs compile`'s own report and against peano.mm0's public interface. So a
// mismatch here means the JS reader disagrees with mm0b_parser, not that a
// fixture drifted.

import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { MmbFile, MmbError, PROOF, CLASS, declKind, declId } from '../src/mmb.js';

// Compiled output lives in dist/test/, so the fixtures are two levels up.
const here = join(dirname(fileURLToPath(import.meta.url)), '..', '..', 'test');

let failures = 0;

/**
 * Plain objects are compared by sorted key, so a histogram built in encounter
 * order matches one written in frequency order.
 */
function canon(v: unknown): string {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return JSON.stringify(v);
  return JSON.stringify(
    Object.entries(v as Record<string, unknown>).sort(([a], [b]) => (a < b ? -1 : 1)));
}

function check(name: string, actual: unknown, expected: unknown): void {
  const a = canon(actual), e = canon(expected);
  if (a === e) {
    console.log(`  ok   ${name}`);
  } else {
    console.log(`  FAIL ${name}\n         got ${a}\n    expected ${e}`);
    failures++;
  }
}

/** The id whose name matches, or undefined. */
function findId(n: number, name: (i: number) => string, want: string): number | undefined {
  for (let i = 0; i < n; i++) if (name(i) === want) return i;
  return undefined;
}

const bytes = new Uint8Array(readFileSync(join(here, 'peano.mmb')));
const f = MmbFile.parse(bytes);

console.log('header');
check('num sorts', f.numSorts, 3);
check('num terms', f.numTerms, 170);
check('num thms', f.numThms, 2723);
check('index present', f.pIndex !== 0, true);
check('no index error', f.indexError, undefined);

console.log('index notes');
// A whole index has nothing to say. The advisory notes exist for what a reader
// finds *missing*, so peano -- which carries every table -- produces none.
check('a complete index has no notes', f.indexNotes(), []);
{
  // hol really is compiled with no notation and no delimiters: that is why it
  // prints in prefix form with spaces, `( ty x A )`. So it is the fixture that
  // proves a present-but-partial index names exactly what it lacks, and no more.
  const hol = MmbFile.parse(new Uint8Array(readFileSync(join(here, 'hol.mmb'))));
  const notes = hol.indexNotes();
  check('a real file missing tables notes each',
    [notes.length, notes.some((n) => n.includes('Nota')), notes.some((n) => n.includes('Delm'))],
    [2, true, true]);
  check('and nothing it does have', notes.some((n) => n.includes('Name') || n.includes('VarN')), false);
}
{
  // The three shapes of a broken index, from the shared counterexample suite.
  const mmb = join(here, '..', '..', 'tests', 'mmb');
  const notesOf = (rel: string): string[] =>
    MmbFile.parse(new Uint8Array(readFileSync(join(mmb, rel)))).indexNotes();
  // No index at all is valid, and says so as one note rather than five.
  check('no index is a single note', notesOf('pass/no_index.mmb'),
    ['this file has no index: declaration names, notation and variable names are unavailable']);
  // An index that cannot be read past its header: the reason, not a per-table
  // list, because nothing was reached to be specific about.
  check('an unreadable index gives the reason', notesOf('fail-index/bad_index_pointer.mmb'),
    ['the index could not be read: index header overruns the file']);
  // A partial index: what was reached, then what is therefore gone.
  const partial = notesOf('fail-index/partial_index.mmb');
  check('a partial index leads with the break',
    partial[0], 'the index is incomplete: VarN table overruns the file');
  check('and then lists what fell after it', partial.length > 1, true);
}

console.log('declaration stream');
const kinds: Record<string, number> = {};
const maxNum: number[] = [];
let total = 0, nullProofs = 0;
let firstThm = '';
for (const d of f.decls()) {
  const k = declKind(d);
  kinds[k] = (kinds[k] ?? 0) + 1;
  if (d.proof.isNull) nullProofs++;
  total++;
  maxNum[d.cls] = Math.max(maxNum[d.cls] ?? -1, d.num);
  if (!firstThm && d.cls === CLASS.THM) firstThm = declId(d);
}
check('total declarations', total, 2896);
check('sort', kinds['sort'], 3);
check('term', kinds['term'], 12);
check('def', kinds['def'], 104);
check('local def', kinds['local def'], 54);
check('axiom', kinds['axiom'], 26);
check('theorem', kinds['theorem'], 2642);
check('pub theorem', kinds['pub theorem'], 55);
// Only sorts and plain terms carry no proof stream; every def and theorem has
// one, including defs (whose stream builds the definition's value).
check('null proof streams', nullProofs, 3 + 12);
check('decls with a proof', total - nullProofs, 2881);

console.log('ids are contiguous per class');
check('max sort id', maxNum[CLASS.SORT], 2);
check('max term id', maxNum[CLASS.TERM], 169);
check('max thm id', maxNum[CLASS.THM], 2722);
// The `s`/`t`/`T` prefixes are how a stripped index names things, so they must
// agree with the class the id is counted in.
check('first thm id renders', firstThm, 'T0');

console.log('names');
// peano has `nat` as both a sort and a term -- the reason URLs must carry the
// class. If this stops holding, the class-qualified routing is untested.
const sortNames = Array.from({ length: f.numSorts }, (_, i) => f.sortName(i));
check('sort names', sortNames.sort(), ['nat', 'set', 'wff']);
const termNames = new Set(Array.from({ length: f.numTerms }, (_, i) => f.termName(i)));
check('`nat` is a term too', termNames.has('nat'), true);
check('names are unique per class', termNames.size, f.numTerms);
const thmNames = new Set(Array.from({ length: f.numThms }, (_, i) => f.thmName(i)));
check('thm names are unique', thmNames.size, f.numThms);

console.log('delimiters');
const d = f.delimiters();
const runOf = (set: Set<number>): string =>
  String.fromCharCode(...Array.from(set).sort((a, b) => a - b));
// Openers (and `~`) glue rightward, closers glue leftward.
check('left delimiters', d && runOf(d.left), '([{~');
check('right delimiters', d && runOf(d.right), '),]}');

console.log('notation');
const nota = f.notations();
check('no nota error', f.notaError, undefined);
check('notation table is populated', nota.size > 0, true);
// `im` is peano's implication, written `a -> b`.
const imId = findId(f.numTerms, (i) => f.termName(i), 'im');
check('found term `im`', imId !== undefined, true);
if (imId !== undefined) {
  const imNota = nota.get(imId);
  check('im has a notation', imNota !== undefined, true);
  check('im literals', imNota?.lits,
    [{ var: 0, prec: 26 }, { const: '->' }, { var: 1, prec: 25 }]);
}

console.log('argument bitfields');
// `ax_mp (a b: wff): $ a -> b $ > $ a $ > $ b $` -- two regular wff binders
// with no dependencies, and anonymous (`_`) hypotheses.
const axMpId = findId(f.numThms, (i) => f.thmName(i), 'ax_mp');
check('found ax_mp', axMpId !== undefined, true);
if (axMpId !== undefined) {
  const axMp = f.thm(axMpId);
  check('ax_mp arity', axMp.numArgs, 2);
  check('ax_mp args unbound', axMp.args.map((a) => a.bound), [false, false]);
  check('ax_mp args have no deps', axMp.args.map((a) => a.deps().length), [0, 0]);
  check('ax_mp hyp names', [0, 1].map((i) => f.hypName(axMpId, i)), ['h0', 'h1']);
}

// `sb` is the substitution def, `(a: nat) {x .y: nat} (p: wff x)` -- it has a
// bound binder, and a regular binder that depends on it. This is the one place
// the 55-bit dependency mask is exercised.
const sbId = findId(f.numTerms, (i) => f.termName(i), 'sb');
check('found sb', sbId !== undefined, true);
if (sbId !== undefined) {
  const sb = f.term(sbId);
  check('sb is a def', sb.isDef, true);
  check('sb bound flags', sb.args.map((a) => a.bound), [false, true, false]);
  check('sb deps', sb.args.map((a) => a.deps()), [[], [0], [0]]);
  check('sb has a unify stream', sb.unifyStart !== null, true);
  // Entries are cached and shared, so a cursor must be minted per use --
  // otherwise two readers of the same def consume each other's stream.
  check('term entries are shared', f.term(sbId) === sb, true);
  const u1 = f.unifyAt(sb.unifyStart!), u2 = f.unifyAt(sb.unifyStart!);
  u1.step();
  check('cursors are independent', u2.pos, sb.unifyStart);
}

console.log('stream iteration terminates');
// The upstream iterators are non-fused and unbounded on a null stream; ours
// must terminate on every declaration, including the ones with no proof.
let steps = 0, errors = 0, withProof = 0;
const hist: Record<string, number> = {};
const PROOF_NAME: Record<number, string> =
  Object.fromEntries(Object.entries(PROOF).map(([k, v]) => [v, k]));
for (const dec of f.decls()) {
  if (dec.proof.isNull) continue;
  withProof++;
  const it = dec.proof;
  while (it.step()) {
    steps++;
    const n = PROOF_NAME[it.cmd] ?? `0x${it.cmd.toString(16)}`;
    hist[n] = (hist[n] ?? 0) + 1;
  }
  if (it.error) errors++;
}
check('no stream errors', errors, 0);
check('total proof commands', steps, 244778);
// EXPLORER_DESIGN.md reports 247,659 "steps rendered", which is this plus one
// terminal "done" state per declaration -- the step model is 0..=n, where the
// state shown at n is after the last command.
check('steps incl. terminal state', steps + withProof, 247659);

// The per-opcode histogram from the design doc's coverage table. Matching all
// fifteen exactly is a far stronger statement than the total: it pins the
// opcode values, the immediate-width decoding and the stream bounds together.
check('opcode histogram', hist, {
  REF: 150926, TERM_SAVE: 34949, TERM: 24774, THM: 23277,
  REFL: 2934, CONG: 1851, UNFOLD: 1442, HYP: 1304,
  DUMMY: 1204, CONV: 1166, THM_SAVE: 551, SYM: 197,
  CONV_CUT: 95, CONV_SAVE: 95, SAVE: 13,
  // SORRY does not occur in peano, which is a complete library.
});

console.log('truncated files fail cleanly');
// One of the two audiences is "I compiled an .mmb, maybe with errors, and want
// to find where it goes wrong", so a malformed file must report where it broke
// rather than throw whatever the DataView happened to raise. Every read is
// bounds-checked *before* it happens; this pins that down across the file.
{
  let clean = 0, reported = 0;
  const leaks: string[] = [];
  for (let cut = 40; cut < bytes.length; cut += 977) {
    try {
      const g = MmbFile.parse(bytes.subarray(0, cut));
      for (const dec of g.decls()) {
        const it = dec.proof;
        if (!it.isNull) while (it.step()) { /* drain */ }
      }
      clean++;
    } catch (e) {
      if (e instanceof MmbError) reported++;
      else leaks.push(`${(e as Error).constructor.name}: ${(e as Error).message}`);
    }
  }
  check('every truncation is an MmbError', leaks, []);
  check('truncations were actually exercised', reported > 100, true);
  check('all cuts accounted for', clean + reported + leaks.length, 899);
}

console.log(failures ? `\n${failures} failure(s)` : '\nall checks passed');
process.exit(failures ? 1 : 0);
