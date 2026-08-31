// The MMB Proof Explorer, client side.
//
// There is no server behind it: the file is parsed, verified and stepped in
// this tab, so what would be requests are function calls, and what a
// server-backed tool cannot do -- open a file it was not started with, say
// whether the whole library verifies -- is the normal case here.

import {
  CLASS, MmbError, MmbFile, declId, declKind, type Decl, type DeclClass,
} from '../src/mmb.js';
import {
  Printer, statement, termSignature, thmStmt, toText,
  type Rendered, type SigOpts,
} from '../src/printer.js';
import {
  replay, isProofStep, stackAt, StackCursor, type Replay, type Snapshot,
} from '../src/steps.js';
import { verify, type Report } from '../src/verify.js';
import { ARG, REF, plainMessage } from '../src/msg.js';
import { UMODE, ustackPops } from '../src/unifier.js';
import {
  stackPops, trailOf, whereLabel, type UnifyStep, type UnifyTrace,
} from '../src/machine.js';
import { EL, type El } from '../src/el.js';
import { type Arena } from '../src/arena.js';
import * as R from './render.js';
import { declHead, effRow, notesNode, schematic, uschematic } from './callout.js';
import * as store from './store.js';

const $ = (id: string): HTMLElement => {
  const e = document.getElementById(id);
  if (e === null) throw new Error(`no #${id}`);
  return e;
};

/** Everything derived from one loaded file. */
interface Loaded {
  name: string;
  file: MmbFile;
  printer: Printer;
  decls: Decl[];
  report: Report;
  /** `(class, id) -> position in the declaration stream`, for drill-down. */
  byId: Map<number, number>;
  /** `class/name -> position`, for routing. */
  byName: Map<string, number>;
  /** `2896 declarations — 3 sort, 12 term, …`, for the list view's crumb. */
  summary: string;
  /** Milliseconds spent verifying, and the file's size in bytes. */
  ms: number;
  size: number;
  /**
   * Advisory notes about the file -- an absent index, no notation table.
   * Nothing wrong and no reason to distrust it, but things a reader is better
   * told than left to infer from names that turned into numbers.
   */
  notes: string[];
  /** Per-declaration caches; see `stepCount`. */
  stepCounts: Map<number, number>;
  sigs: Map<number, string>;
  sigDocs: Map<number, Rendered | null>;
  sigForms: Map<number, string[]>;
}

let LOADED: Loaded | null = null;
/** The signature column's measured width, so a resize can tell if it changed. */
let SIG_CAP = Infinity;
/** The declaration on screen, replayed once and reused while it is shown. */
let CUR: { at: number; r: Replay; cursor: StackCursor } | null = null;

const clsOf = (d: Decl): 'sort' | 'term' | 'thm' =>
  d.cls === CLASS.SORT ? 'sort' : d.cls === CLASS.TERM ? 'term' : 'thm';

const nameOf = (L: Loaded, d: Decl): string =>
  d.cls === CLASS.SORT ? L.file.sortName(d.num)
    : d.cls === CLASS.TERM ? L.file.termName(d.num) : L.file.thmName(d.num);

const key = (cls: DeclClass, num: number): number => cls * 0x1000000 + num;

/** `pub theorem` -> `k-pubtheorem`, `local def` -> `k-localdef`. */
const kindClass = R.kindClass;

/**
 * The declaration's keyword, as MM0 writes it -- with a sort's modifiers,
 * which are part of the keyword the way `pub` and `local` are: `strict
 * provable sort wff`, not `sort wff` with the modifiers dropped.
 *
 * The class still comes from `declKind`, so a sort is coloured as a sort
 * however many modifiers it carries.
 */
function kindText(L: Loaded, d: Decl): string {
  if (d.cls !== CLASS.SORT) return declKind(d);
  const mods = L.file.sortMods(d.num);
  return mods.length === 0 ? 'sort' : `${mods.join(' ')} sort`;
}

/** Columns the statement row gets before it breaks. */
const STMT_WIDTH = 150;

// ---- loading --------------------------------------------------------------

function load(name: string, bytes: Uint8Array): void {
  status('busy', 'verifying…');
  // Yield first, so the browser paints "verifying…" before the main thread is
  // taken. A whole library is tens to hundreds of milliseconds; long enough to
  // be felt, short enough that a worker is not yet worth its complexity.
  setTimeout(() => {
    try {
      const file = MmbFile.parse(bytes);
      // Driven by hand rather than spread, because the walk can fail partway
      // and everything before the break is still readable. Spreading threw all
      // of it away and showed the picker, so a file with one bad length looked
      // exactly like a file that was not an mmb at all. `verify` collects the
      // same error as a failure, and reports it below.
      const decls: Decl[] = [];
      const walk = file.decls();
      for (;;) {
        let step: IteratorResult<Decl, number>;
        try {
          step = walk.next();
        } catch (e) {
          if (!(e instanceof MmbError)) throw e;
          break;
        }
        if (step.done === true) break;
        decls.push(step.value);
      }
      // Nothing at all came out: there is no list to show, so this is the
      // unreadable case after all.
      if (decls.length === 0) throw new MmbError('no declarations could be read');
      // Timed on its own, not around the parse and the walk: the claim being
      // made is about verification.
      const t0 = performance.now();
      const report = verify(file);
      const ms = performance.now() - t0;
      const L: Loaded = {
        name, file, printer: new Printer(file), decls,
        report, byId: new Map(), byName: new Map(),
        summary: '', ms, size: bytes.byteLength, notes: file.indexNotes(),
        stepCounts: new Map(), sigs: new Map(), sigDocs: new Map(), sigForms: new Map(),
      };
      const by = new Map<string, number>();
      for (const d of decls) by.set(declKind(d), (by.get(declKind(d)) ?? 0) + 1);
      L.summary = `${name} — ${fileSize(bytes.byteLength)} — ${decls.length} declarations: `
        + [...by].map(([k, n]) => `${n} ${k}`).join(', ');
      for (const d of decls) {
        L.byId.set(key(d.cls, d.num), d.index);
        L.byName.set(`${clsOf(d)}/${nameOf(L, d)}`, d.index);
      }
      LOADED = L;
      // The title bar and the home link both name the file now, so they are
      // set where the file becomes the one in hand.
      setTitle(L, null);
      ($('home') as HTMLAnchorElement).href = listUrl(L.name);
      $('open').classList.remove('on');
      $('list').classList.remove('off');
      showStatus(L);
      // A fresh file has its own failures, or none; carrying the filter over
      // would open it showing an empty list. The search box goes with it: the
      // two controls compose, so a query left in place would keep hiding rows
      // of the new file while reading as though nothing were filtered.
      ONLY_BAD = false;
      ($('search') as HTMLInputElement).value = '';
      paintBad(L);
      paintFailures(L);
      buildList(L);
      applyFilter();
      // Opening a file is a move from the selector to its declarations, so it
      // gets an entry -- setting the hash makes one and routes in one go. A
      // deep link into *this* file is already at its destination and must not
      // gain a second, so route in place instead. But the address may still
      // name a different file -- a stale hash from before this open -- and that
      // is not a deep link into what was just loaded: routing to it would ask
      // to resolve the other file and abandon the one the user just chose. Only
      // the address that names this file is honoured; anything else yields to
      // the file in hand and lands on its list.
      if (fileInHash() === L.name) route();
      else location.hash = listUrl(L.name);
    } catch (e) {
      // No report to hang a trail on here, so the offset goes in the sentence.
      const msg = e instanceof MmbError
        ? e.message + (e.pos === undefined ? '' : ` (at 0x${e.pos.toString(16)})`)
        : String(e);
      status('bad', 'could not read this file');
      showError(`${name}: ${msg}`);
    }
  }, 0);
}

/**
 * The file's status, which is ambient: it belongs to the whole file, not to
 * the declaration you are reading. On a declaration page it shrinks to a mark,
 * with the wording in the tooltip, so the crumb gets the room -- the header is
 * one line and the crumb is what tells you where you are.
 */
let STATUS = { kind: '', text: '', mark: '' };
/** How long verification took, shown beside the badge. */
let TIMING = '';

function status(kind: string, text: string, mark = ''): void {
  STATUS = { kind, text, mark };
  paintStatus();
}

function paintStatus(): void {
  const s = $('status');
  // The indeterminate bar across the top. Reading a file is fetch + parse +
  // verify, and the parse and verify hold the main thread, so the bar is what
  // shows the page is working rather than wedged.
  $('bar').classList.toggle('on', STATUS.kind === 'busy');
  // The badge on both views. Spelled out, it repeated the declaration count
  // the crumb already gives on the list, and squeezed the name on a
  // declaration page -- and the wording is one hover away either way.
  const compact = STATUS.mark !== '';
  s.className = `meta ${STATUS.kind}${compact ? ' compact' : ''}`;
  // A verified file with notes is still `ok` -- the ✓ stays -- but there is now
  // something behind it to read, so the badge takes a pointer and opens the
  // modal like the failing ones do. On a `bad`/`warn` badge this is redundant
  // with the kind's own affordance and does no harm.
  s.classList.toggle('notes', LOADED !== null && LOADED.notes.length > 0);
  s.textContent = compact ? STATUS.mark : STATUS.text;
  s.title = compact ? STATUS.text : '';
  // The time is a fact about the file, like the status wording, so it shows on
  // the list -- where you land after opening one -- and folds into the tooltip
  // on a declaration page, where the crumb needs the room.
  const t = $('timing');
  t.textContent = CUR === null ? TIMING : '';
  t.title = STATUS.text;
  // Green is the colour of the file being sound. A time in green beside a
  // failed check reads as a second, contradictory verdict.
  t.className = STATUS.kind;
}

/** Bytes as the file manager would say them. */
function fileSize(n: number): string {
  return n >= 1e6 ? `${(n / 1e6).toFixed(1)} MB` : `${Math.round(n / 1e3)} kB`;
}

/** Milliseconds, rounded to something a header can hold. */
const ms = (t: number): string => (t >= 1000 ? `${(t / 1000).toFixed(1)} s` : `${Math.round(t)} ms`);

function showStatus(L: Loaded): void {
  const r = L.report;
  // What was actually done, for the tooltip: the counts are the reason the
  // time is worth quoting.
  const work = `${r.proofSteps.toLocaleString()} proof steps, `
    + `${r.unifySteps.toLocaleString()} unify steps`;
  TIMING = `${ms(L.ms)}`;
  if (r.ok) {
    status('ok', `${L.name} — ${fileSize(L.size)}, ${r.verified.toLocaleString()} declarations verified `
      + `in ${ms(L.ms)} — ${work}`, '✓');
  } else if (r.failures.length === 0) {
    // Every check passed and the file is still not to be trusted. That is a
    // warning, not a verdict: nothing here is *wrong*, and marking it the same
    // as a broken file makes the two indistinguishable at a glance.
    const k = r.sorried.length;
    status('warn', `${L.name} — ${r.verified.toLocaleString()} declarations verified `
      + `in ${ms(L.ms)}, but ${k} used sorry — click for the full list`, '⚠');
  } else {
    const n = r.failures.length;
    status('bad', `${L.name} — ${n} failure${n === 1 ? '' : 's'}, `
      + `${r.verified} of ${L.decls.length} declarations verified in ${ms(L.ms)}`
      + (r.sorried.length > 0 ? `, ${r.sorried.length} used sorry` : '')
      + ' — click for the full list', '✗');
  }
}

/**
 * How much is wrong, in words.
 *
 * `Sorry` is not a failure -- every check passed -- but it is why the file is
 * not to be trusted, so it is counted here too: a heading reading `0 failures`
 * above a list with an entry in it was contradicting the list.
 */
function countText(L: Loaded): string {
  const n = L.report.failures.length, k = L.report.sorried.length, i = L.notes.length;
  const parts: string[] = [];
  // `16+` where a declaration hit the cap: the run stopped looking, so the
  // count is a floor and saying it flat would claim the file was fully read.
  const more = L.report.capped ? '+' : '';
  // The failure part is dropped only when there is genuinely nothing to fail
  // *and* something else to say -- a `sorry` or a note. `0 failures, 2 notes`
  // leads with the thing that did not happen.
  if (n > 0 || (k === 0 && i === 0)) parts.push(`${n}${more} failure${n === 1 ? '' : 's'}`);
  if (k > 0) parts.push(`${k} used sorry`);
  if (i > 0) parts.push(`${i} note${i === 1 ? '' : 's'}`);
  return parts.join(', ');
}

/**
 * The failure count in the header, which opens the full list.
 *
 * It replaces a box across the top of the page that spelled out the first
 * three failures -- the same list the modal holds, in a place that pushed the
 * view down to say it.
 */
function paintFailures(L: Loaded | null): void {
  const b = $('failures');
  const issue = L !== null && (!L.report.ok || L.report.sorried.length > 0);
  const notes = L !== null && L.notes.length > 0;
  b.textContent = L !== null && (issue || notes) ? countText(L) : '';
  // Three tiers, so the colour matches the worst thing being counted: red for
  // a failure (the default), orange when nothing failed but a `sorry` is
  // present, blue when all that is left is a note.
  b.classList.toggle('warn', issue && L!.report.failures.length === 0);
  b.classList.toggle('info', !issue && notes);
}

/**
 * A failure message, with the declarations and arguments it names drawn out.
 *
 * A name becomes a link. An argument becomes `G ↦ an G (ty x A)` -- the binder
 * and what it stands for -- when the caller supplies the step's arguments, and
 * the bare binder name otherwise. The substitution is not carried in the
 * message: it is on the stack at that step, so the replay reconstructs it, and
 * a copy in the message would be state that can go stale.
 */
function messageNode(
  L: Loaded, text: string, from?: { ctx: R.Ctx; arena: Arena; args: number[] },
): DocumentFragment {
  const f = document.createDocumentFragment();
  // One pass over both kinds of reference, so their order in the message holds.
  const both = new RegExp(`${REF.source}|${ARG.source}`, 'g');
  let last = 0;
  for (const m of text.matchAll(both)) {
    if (m.index > last) f.append(document.createTextNode(text.slice(last, m.index)));
    last = m.index + m[0].length;
    if (m[1] !== undefined) { f.append(nameNode(L, m[1], m[2]!)); continue; }
    const [i, name] = [Number(m[3]), m[4]!];
    const node = from?.args[i];
    f.append(R.el('span', 'var', name));
    if (from !== undefined && node !== undefined) {
      f.append(document.createTextNode(' ↦ '), R.node(from.ctx, from.arena, node));
    }
  }
  if (last < text.length) f.append(document.createTextNode(text.slice(last)));
  return f;
}

/** A declaration named in a message: a link where this file has it. */
function nameNode(L: Loaded, kind: string, name: string): HTMLElement {
  const at = L.byName.get(`${kind}/${name}`);
  const d = at === undefined ? undefined : L.decls[at];
  // A name this file does not have is still a name: it keeps the colouring
  // that says so, and simply does not go anywhere.
  if (d === undefined) return R.el('span', 'nm', name);
  const a = R.el('a', 'nm', name) as HTMLAnchorElement;
  a.href = declUrl(L, d);
  return a;
}

/**
 * The arguments a step applied a theorem to, off the stack as it stood then.
 *
 * `Thm T` takes the target on top and the arguments below it, so they are
 * there to be read back -- which is why a message about one of them need only
 * say which.
 */
function stepArgs(L: Loaded, r: Replay, at: number): number[] | null {
  const s = r.steps[at];
  if (s === undefined || s.cmd === null) return null;
  if ((s.cmd & ~1) !== 0x14 || s.data >= L.file.numThms) return null;
  const n = L.file.thm(s.data).numArgs;
  const st = stackAt(r, at);
  const base = st.length - 1 - n;
  if (base < 0) return null;
  return st.slice(base, base + n).map((e) => e.a);
}

function showError(msg: string): void {
  const e = $('error');
  // Plain text: the markers are an encoding, and this box has no links in it.
  e.textContent = plainMessage(msg);
  e.style.display = msg === '' ? 'none' : 'block';
}

// ---- the declaration list -------------------------------------------------

/**
 * The signature column's width in characters, or `Infinity` if it cannot be
 * measured -- in which case every signature renders in full and the CSS
 * ellipsis is the only truncation.
 *
 * Measured off a real row rather than derived from the column widths: the
 * column is a fraction of whatever the window gives us. The font is monospace,
 * so one ruler span is the whole of the arithmetic.
 */
function sigCapacity(): number {
  const tb = $('decls');
  const kept = Array.from(tb.childNodes);
  const n = 100;
  const tr = R.el('tr');
  for (const c of ['num', 'decl', 'steps']) tr.append(R.el('td', c));
  const ruler = R.el('span', undefined, '0'.repeat(n));
  const cell = tr.children[1]!;
  cell.append(ruler);
  tb.replaceChildren(tr);
  const cs = getComputedStyle(cell);
  const inner = cell.clientWidth - parseFloat(cs.paddingLeft) - parseFloat(cs.paddingRight);
  const ch = ruler.getBoundingClientRect().width / n;
  tb.replaceChildren(...kept);
  return ch > 0 && inner > 0 ? Math.floor(inner / ch) : Infinity;
}

/**
 * The binders are a run of `{…}` / `(…)` groups and the rest starts at the
 * first `:` outside them, so dropping them needs no parsing beyond matching
 * brackets.
 */
function sigNoVars(sig: string): string {
  let depth = 0, i = 0;
  for (; i < sig.length; i++) {
    const c = sig[i];
    if (c === '{' || c === '(') depth++;
    else if (c === '}' || c === ')') depth--;
    else if (c === ':' && depth === 0) break;
  }
  return sig.slice(i);
}

/**
 * A signature in progressively shorter forms, longest first.
 *
 * Plain end-truncation is the wrong failure mode: it eats the *conclusion*,
 * which is the thing the column is being read for. So give up the affordable
 * parts first -- the binders, then the hypotheses -- and keep the conclusion
 * whatever happens. The full text stays in the cell's tooltip either way.
 */
function sigForms(L: Loaded, d: Decl): string[] {
  const hit = L.sigForms.get(d.index);
  if (hit !== undefined) return hit;
  const full = signature(L, d);
  const forms = [full];
  const nv = sigNoVars(full);
  if (nv !== full) forms.push(nv);
  if (d.cls === CLASS.THM) {
    try {
      const st = thmStmt(L.printer, d.num);
      if (st.hyps.length > 0) forms.push(`: … > $ ${toText(st.concl)} $`);
    } catch { /* a malformed statement simply offers fewer forms */ }
  }
  L.sigForms.set(d.index, forms);
  return forms;
}

/**
 * What each form drops, in the order `sigForms` lists them. The text is still
 * measured as a string -- cheap, and derived from the one full rendering -- and
 * only the form that wins is built as a document and drawn.
 */
const FORM_OPTS: SigOpts[] = [{}, { binders: false }, { binders: false, hyps: false }];

/** The longest form that fits, as an index into `sigForms`/`FORM_OPTS`. */
function pickSig(L: Loaded, d: Decl, cap: number): number {
  const forms = sigForms(L, d);
  const i = forms.findIndex((f) => f.length <= cap);
  return i < 0 ? forms.length - 1 : i;
}

/**
 * Draw one row's signature, the first time it is scrolled to.
 *
 * Split from `buildList` because it is the expensive half: the document is
 * already built and measured by then, and what this adds is the elements.
 */
function drawSig(L: Loaded, cell: HTMLElement, cap: number): void {
  const d = L.decls[Number(cell.dataset['at'])];
  if (d === undefined) return;
  const kind = declKind(d), name = nameOf(L, d);
  const form = pickSig(L, d, cap - kind.length - name.length - 1);
  // The full form is already in hand from measuring, and it is the one that
  // fits for most rows -- building it again to draw it would run the
  // declaration's unify stream twice.
  const r = form === 0 ? full(L, d) : sigDoc(L, d, FORM_OPTS[form]!);
  if (r !== null) cell.append(R.expr(ctxFor(L, d), r, Infinity));
}

/** Watches the rows on screen; replaced whenever the list is rebuilt. */
let sigWatch: IntersectionObserver | null = null;

function buildList(L: Loaded): void {
  const tbody = $('decls');
  tbody.replaceChildren();
  const cap = sigCapacity();
  SIG_CAP = cap;
  sigWatch?.disconnect();
  // A margin, so a row is drawn shortly before it is looked at rather than as
  // it appears.
  sigWatch = new IntersectionObserver((es) => {
    for (const e of es) {
      if (!e.isIntersecting) continue;
      sigWatch?.unobserve(e.target);
      drawSig(L, e.target as HTMLElement, cap);
    }
  }, { root: $('listbody'), rootMargin: '400px' });
  const frag = document.createDocumentFragment();
  for (const d of L.decls) {
    const kind = declKind(d);
    const name = nameOf(L, d);
    const tr = R.el('tr');
    tr.dataset['name'] = name.toLowerCase();
    tr.dataset['id'] = declId(d);
    // `t12`, not `12`: the number alone is ambiguous across classes, since a
    // term and a theorem can share one.
    tr.append(R.el('td', 'num', declId(d)));
    // Kind, name and signature in one cell, written the way the source writes
    // the declaration and coloured the way the step page colours it -- so the
    // list reads as declarations rather than as a table of fields.
    const cell = R.el('td', 'decl');
    cell.append(R.el('span', `kind ${kindClass(kind)}`, kindText(L, d)),
      document.createTextNode(' '));
    const a = R.el('a', 'declname', name) as HTMLAnchorElement;
    a.href = declUrl(L, d);
    cell.append(a);
    // Whatever form the column shows, the whole declaration is one hover away.
    cell.title = `${kindText(L, d)} ${name}${signature(L, d)}`;
    // The signature itself is drawn when the row is first scrolled to. A
    // coloured signature is twenty-odd elements, and a library is thousands of
    // rows of which a screenful is forty: drawing them all cost more than
    // verifying the file. The text is measured either way -- that is what the
    // tooltip and the form choice need -- so only the drawing is deferred.
    cell.dataset['at'] = String(d.index);
    tr.append(cell);
    tr.append(R.el('td', 'steps', d.proof.isNull ? '' : String(stepCount(L, d))));
    // The whole row is the target, not just the name: the row is what the eye
    // and the pointer both treat as the item, and the name is a small part of
    // a wide one. The anchor stays for middle-click, copy-link and keyboard.
    tr.addEventListener('click', () => { location.hash = a.getAttribute('href')!; });
    // A declaration that failed to verify is the one worth finding.
    if (L.report.failures.some((f) => f.index === d.index)) tr.classList.add('bad');
    frag.append(tr);
  }
  tbody.append(frag);
  for (const c of tbody.querySelectorAll('td.decl')) sigWatch.observe(c);
}

// Both caches hang off `Loaded` rather than the module, because they are keyed
// by declaration index and a second file's indices mean something else
// entirely -- module-level caches would quietly serve the first file's values.

function stepCount(L: Loaded, d: Decl): number {
  const hit = L.stepCounts.get(d.index);
  if (hit !== undefined) return hit;
  const it = d.proof.clone();
  let n = 0;
  while (it.step()) n++;
  L.stepCounts.set(d.index, n);
  return n;
}

/**
 * A declaration's signature as MM0 source writes it: a theorem's statement, a
 * term or def's `(binders): ret`, and for a def its `= $ value $` too.
 *
 * The value is part of the declaration rather than a separate fact about it --
 * how the proof stream *builds* it is the question the step view answers, and
 * a different one from what it is.
 */
function sigDoc(L: Loaded, d: Decl, opts: SigOpts = {}): Rendered | null {
  try {
    if (d.cls === CLASS.THM) return statement(L.printer, d.num, opts);
    if (d.cls === CLASS.TERM) return termSignature(L.printer, d.num, opts);
  } catch {
    // A malformed declaration still deserves a row; it just has no signature.
  }
  return null;
}

/**
 * The full signature as a document, built once per declaration and kept.
 *
 * Both the measuring and the drawing want it, and building it means running
 * the declaration's unify stream -- so doing it per caller doubled the work
 * across the whole library.
 */
function full(L: Loaded, d: Decl): Rendered | null {
  const hit = L.sigDocs.get(d.index);
  if (hit !== undefined) return hit;
  const r = sigDoc(L, d);
  L.sigDocs.set(d.index, r);
  return r;
}

/** The same, flattened, for measuring. */
function signature(L: Loaded, d: Decl): string {
  const hit = L.sigs.get(d.index);
  if (hit !== undefined) return hit;
  const r = full(L, d);
  // Kept whole, leading space and all: a signature composes onto a name, and
  // the callout's identity line does exactly that. The list column, which has
  // no name in front of it, is the one place that trims -- doing it here
  // instead ran the name and the binders together as `al{x: nat}`.
  const s = r === null ? '' : toText(r);
  L.sigs.set(d.index, s);
  return s;
}

/**
 * Show the rows whose name contains the query, plus the one whose id *is* it.
 *
 * The id is matched whole and with its case kept: `T1` and `t1` are different
 * declarations -- theorem 1 and term 1 -- so folding case would conflate them,
 * and matching it as a substring would put every `T1xx` ahead of the row asked
 * for by number. The name match stays loose and case-insensitive, which is
 * what a name search should be.
 */
/** Whether the list is showing only the declarations that failed. */
let ONLY_BAD = false;

/**
 * The failed-only control: how many, and whether it is on.
 *
 * Hidden when nothing failed. A count of zero is not a control, and a filter
 * that can only ever empty the list is worse than absent.
 */
function paintBad(L: Loaded): void {
  const b = $('onlybad') as HTMLButtonElement;
  // Only the failures that mark a row. A broken declaration walk fails with no
  // declaration to blame -- the error line carries that -- and counting it here
  // offered a filter that could only ever empty the list.
  const bad = new Set(L.report.failures.map((f) => f.index));
  const n = L.decls.filter((d) => bad.has(d.index)).length;
  b.textContent = n === 0 ? '' : `${n} failed`;
  b.classList.toggle('on', ONLY_BAD && n > 0);
}

function applyFilter(): void {
  const raw = ($('search') as HTMLInputElement).value.trim();
  const q = raw.toLowerCase();
  for (const tr of $('decls').children) {
    // The row's own name, not the cell's text: the cell now carries the kind
    // and the signature too, and filtering for `wff` would match every row
    // whose statement happened to mention it.
    const el = tr as HTMLElement;
    const hit = (q === ''
      || (el.dataset['name'] ?? '').includes(q)
      || el.dataset['id'] === raw)
      // Narrows what the search found rather than replacing it, so the two
      // controls compose instead of overriding each other.
      && (!ONLY_BAD || el.classList.contains('bad'));
    tr.classList.toggle('hidden', !hit);
  }
}

// ---- routing --------------------------------------------------------------

/**
 * `#/peano.mmb/thm/a1i/9/u1` -- the file, then where in it.
 *
 * The file leads because it is what the rest is relative to: a declaration
 * name means nothing without saying which library it is from, and an address
 * that omitted it resolved against whatever happened to be open. With it
 * there, a link carries its own context and the page can go and get the file.
 *
 * The unify sub-step is part of it for the same reason the step is: without it
 * a link into the unifier reopened the proof step and dropped you at sub-step
 * 0, and a refresh lost the sub-machine entirely.
 */
const ROUTE = /^#\/([^/]+)\/(sort|term|thm)\/([^/]+)(?:\/(\d+)(?:\/u(\d+))?)?$/;
/** `#/peano.mmb` -- the file's declaration list. */
const FILE_ROUTE = /^#\/([^/]+)\/?$/;

/** The file the address names, whichever shape it is in. */
function fileInHash(): string | null {
  const m = ROUTE.exec(location.hash) ?? FILE_ROUTE.exec(location.hash);
  return m === null ? null : decodeURIComponent(m[1]!);
}

/** The address of a file's declaration list. */
const listUrl = (name: string): string => `#/${encodeURIComponent(name)}`;

/** The address of a declaration, which is always relative to its file. */
const declUrl = (L: Loaded, d: Decl): string =>
  `${listUrl(L.name)}/${clsOf(d)}/${encodeURIComponent(nameOf(L, d))}`;

/**
 * The three pages, and what separates them.
 *
 * `#` is the file selector, `#/peano.mmb` its declarations, and
 * `#/peano.mmb/thm/a1i/9` a step. Each is a real place, so moving between them
 * leaves a history entry and Back walks out the way you came in. Moving
 * *within* one does not: a hundred steps of a proof is one place visited, and
 * a Back that walked them in reverse would never get you off the page.
 *
 * The entries come from setting `location.hash`, which the browser pushes for
 * us; every step and sub-step is then written with `replaceState` over the
 * top. So nothing here has to decide between push and replace -- arriving is a
 * hash change, and moving about is not.
 */
function route(): void {
  const L = LOADED;
  const h = location.hash;
  if (h === '' || h === '#') {
    // The selector. The file stays loaded behind it, so Forward comes straight
    // back to its list rather than re-reading it.
    CUR = null;
    UNIFY = null;
    $('open').classList.add('on');
    $('list').classList.add('off');
    $('detail').classList.remove('on');
    $('nav').replaceChildren();
    setTitle(null, null);
    return;
  }
  if (L === null) return;
  // The address may name a file other than the one in hand -- a pasted link,
  // or Back past an `open`. That is a request to go and get it.
  const want = fileInHash();
  if (want !== null && want !== L.name) { resolveFile(want); return; }

  const m = ROUTE.exec(location.hash);
  if (m === null) {
    $('open').classList.remove('on');
    CUR = null;
    $('list').classList.remove('off');
    $('detail').classList.remove('on');
    // On the list, the crumb says what the file holds.
    $('crumb').textContent = L.summary;
    $('nav').replaceChildren();
    setTitle(L, null);
    paintStatus();
    return;
  }
  const idx = L.byName.get(`${m[2]}/${decodeURIComponent(m[3]!)}`);
  if (idx === undefined) { location.hash = listUrl(L.name); return; }
  $('list').classList.add('off');
  $('detail').classList.add('on');
  openDecl(L, idx, m[4] === undefined ? 0 : Number(m[4]),
    m[5] === undefined ? null : Number(m[5]));
  paintStatus();
}

/**
 * The tab's name: where you are, then what you are in.
 *
 * Narrowest first, because a tab strip truncates from the right -- with the
 * tool's name leading, a row of tabs on this page would all read
 * `MMB Proof Ex…` and be impossible to tell apart.
 */
function setTitle(L: Loaded | null, decl: string | null): void {
  document.title = [decl, L?.name, 'MMB Proof Explorer']
    .filter((x) => x !== null && x !== undefined && x !== '').join(' | ');
}

function openDecl(L: Loaded, index: number, step: number, ustep: number | null): void {
  const d = L.decls[index]!;
  if (CUR === null || CUR.at !== index) {
    const r = replay(L.file, d, { unify: true });
    CUR = { at: index, r, cursor: new StackCursor(r) };
  }
  // A `/uN` in the address means the unifier was open at that sub-step, so put
  // it back before rendering rather than leaving the view to be corrected.
  if (ustep === null) UNIFY = null;
  else {
    const t = CUR.r.steps[step]?.unify[0];
    UNIFY = t === undefined ? null : { step, trace: t, at: 0 };
    if (UNIFY !== null) {
      UNIFY.at = Math.max(0, Math.min(ustep, UNIFY.trace.steps.length - 1));
    }
  }
  renderDecl(L, CUR.r, step);
}

// ---- the step view --------------------------------------------------------

function ctxFor(L: Loaded, d: Decl): R.Ctx {
  const varName = d.cls === CLASS.TERM
    ? (i: number) => L.file.termVarName(d.num, i)
    : (i: number) => L.file.thmVarName(d.num, i);
  return {
    file: L.file, printer: L.printer, varName,
    href: (cls, num) => {
      const at = L.byId.get(key(cls as DeclClass, num));
      if (at === undefined) return '#';
      const t = L.decls[at]!;
      return declUrl(L, t);
    },
  };
}

let ONLY_PROOF = localStorage.getItem('mmb-only-proof') === '1';

/** The unifier, while it is open on a step. */
let UNIFY: { step: number; trace: import('../src/machine.js').UnifyTrace; at: number } | null = null;

/**
 * The proof-only button's state and tooltip.
 *
 * Repainted rather than rebuilt, because it lives in the header now: the
 * filter is a setting that holds across the whole session, and rebuilding it
 * with `#nav` made it move on a declaration page and disappear on the list.
 */
function paintProof(): void {
  const b = $('proof');
  b.classList.toggle('on', ONLY_PROOF);
  const r = CUR?.r;
  b.title = !ONLY_PROOF ? 'show only the steps that push a proof (p)'
    : r === undefined ? 'proof steps only (p)'
      : `proof steps only — showing ${r.steps.filter((x) => isProofStep(r, x)).length}`
        + ` of ${r.steps.length} (p)`;
}

function toggleProof(L: Loaded, on: boolean): void {
  ONLY_PROOF = on;
  localStorage.setItem('mmb-only-proof', on ? '1' : '');
  paintProof();
  if (CUR === null) return;
  const r = CUR.r;
  const at = currentStep();
  // Turning the filter on while sitting on a step it hides would leave the
  // panes showing a step the listing no longer offers, with nothing
  // highlighted. Move on to the next visible step instead. Turning it off
  // never moves you.
  if (on && !isProofStep(r, r.steps[at]!)) {
    const next = r.steps.find((s) => s.i >= at && isProofStep(r, s));
    go(L, next?.i ?? at);
  } else {
    renderDecl(L, r, at);
  }
}

/** Enter the unifier on a step, if it has one. */
function enterUnify(L: Loaded, step: number): void {
  if (CUR === null) return;
  const s = CUR.r.steps[step];
  const t = s?.unify[0];
  if (t === undefined) return;
  UNIFY = { step, trace: t, at: 0 };
  if (step !== currentStep()) go(L, step);
  else renderDecl(L, CUR.r, step);
}

function toggleUnify(L: Loaded): void {
  if (CUR === null) return;
  if (UNIFY !== null) {
    UNIFY = null;
    renderDecl(L, CUR.r, currentStep());
  } else {
    enterUnify(L, currentStep());
  }
}

function setUstep(L: Loaded, k: number): void {
  if (UNIFY === null || CUR === null) return;
  UNIFY.at = Math.max(0, Math.min(k, UNIFY.trace.steps.length - 1));
  renderDecl(L, CUR.r, currentStep());
}

/**
 * Move by rows of the listing, which reads as a tree: a step's unify sub-steps
 * are its children, so up and down walk through them and out the other side.
 */
function moveRow(L: Loaded, delta: number): void {
  if (UNIFY === null) { move(L, delta); return; }
  const next = UNIFY.at + delta;
  if (next < 0 || next >= UNIFY.trace.steps.length) {
    // Off the end of the sub-steps: leave the unifier and carry on in the proof.
    UNIFY = null;
    move(L, delta);
    return;
  }
  setUstep(L, next);
}

const helpEl = (): HTMLElement => $('help-modal');
const openHelp = (): void => helpEl().classList.add('open');
const closeHelp = (): void => helpEl().classList.remove('open');
const helpOpen = (): boolean => helpEl().classList.contains('open');

const errEl = (): HTMLElement => $('err-modal');
const closeErrors = (): void => errEl().classList.remove('open');
const errorsOpen = (): boolean => errEl().classList.contains('open');

/**
 * Every failure at once, from the badge that says there were some.
 *
 * The header can only carry a count and the first line or two, and the list
 * only marks the declarations it can name -- so a failure in the declaration
 * stream, which has no declaration to blame, had nowhere to be read in full.
 */
function openErrors(L: Loaded): void {
  const fs = L.report.failures;
  if (fs.length === 0 && L.report.sorried.length === 0 && L.notes.length === 0) return;
  $('err-title').textContent = `${countText(L)} in ${L.name}`;
  // The failure half of the modal has nothing to say for a verified file whose
  // only entries are notes, so its intro and list fold away, leaving the notes
  // section to stand alone.
  const anyFail = fs.length > 0 || L.report.sorried.length > 0;
  $('err-intro').classList.toggle('hidden', !anyFail);
  const list = $('err-list');
  list.classList.toggle('hidden', !anyFail);
  list.replaceChildren();
  const at = new Map(L.decls.map((d) => [d.index, d]));
  for (const f of fs) {
    const dt = R.el('dt');
    const d = at.get(f.index);
    // Every part of the trail that names somewhere is a way to get there: the
    // declaration, the step within it, and the unify command within that. The
    // list is where you decide what to look at, so reading it should be enough
    // to go and look.
    const link = (text: string, href: string): void => {
      const a = R.el('a', undefined, text) as HTMLAnchorElement;
      a.href = href;
      a.addEventListener('click', closeErrors);
      dt.append(a);
    };
    // A failure with no declaration to blame -- the stream, or the file --
    // still has a trail worth showing; it just has nowhere to point.
    if (d === undefined) dt.append(R.el('span', 'kind', f.what));
    else link(f.what, declUrl(L, d));
    // A unify command is addressed within a step, so it can only be linked
    // when the trail says which one. A header check has no step to name.
    const step = f.where.find((w) => w.at === 'step');
    for (const w of f.where) {
      dt.append(document.createTextNode(', '));
      if (d === undefined) dt.append(document.createTextNode(whereLabel(w)));
      else if (w.at === 'step') link(whereLabel(w), `${declUrl(L, d)}/${w.index}`);
      // A run that failed as a whole names no command, so there is no sub-step
      // to address -- `/u-1` is not a place.
      else if (w.at === 'unify' && step !== undefined && w.index >= 0) {
        link(whereLabel(w), `${declUrl(L, d)}/${step.index}/u${w.index}`);
      } else dt.append(document.createTextNode(whereLabel(w)));
    }
    const dd = R.el('dd');
    dd.append(messageNode(L, f.message));
    for (const a of dd.querySelectorAll('a')) a.addEventListener('click', closeErrors);
    list.append(dt, dd);
  }
  for (const w of L.report.sorried) {
    // A declaration like any other, so it is reached like any other.
    const dt = R.el('dt');
    const d = at.get(w.index);
    if (d === undefined) dt.append(R.el('span', 'kind', w.what));
    else {
      const a = R.el('a', undefined, w.what) as HTMLAnchorElement;
      a.href = declUrl(L, d);
      a.addEventListener('click', closeErrors);
      dt.append(a);
    }
    const dd = R.el('dd', 'warn', 'used sorry');
    list.append(dt, dd);
  }
  // The advisory notes, in their own section: an absent index is not something
  // the file got wrong, so it does not belong in a list headed by what the
  // verifier rejected.
  const notes = $('note-list');
  notes.replaceChildren();
  $('note-section').classList.toggle('hidden', L.notes.length === 0);
  for (const n of L.notes) notes.append(R.el('li', undefined, n));
  errEl().classList.add('open');
}

/**
 * `stackPops` for a step whose command may name nothing.
 *
 * Every lookup into the file's tables raises `MmbError` for an id out of range
 * or an entry pointing outside the file, and the step being drawn is often the
 * one that failed for exactly that reason. `null` means "cannot be known",
 * which the caller reads as "use what the step recorded".
 */
function tryPops(L: Loaded, s: Snapshot): number | null {
  if (s.cmd === null) return null;
  try {
    return stackPops(L.file, s.cmd, s.data);
  } catch (e) {
    if (e instanceof MmbError) return null;
    throw e;
  }
}

/**
 * A callout for a step whose declaration cannot be read, in place of the
 * schematic one.
 *
 * The schematic needs the applied declaration's binders and statement, so an id
 * that names nothing leaves it nothing to draw. Rendering the reason keeps the
 * pane meaningful; letting the `MmbError` out would abort the render half way
 * and leave the crumb and step list pointing at panes that were never rebuilt.
 */
function calloutError(e: MmbError): Node {
  const box = R.el('div', 'popout');
  box.append(R.el('div', 'po-err', e.message));
  return box;
}

function renderDecl(L: Loaded, r: Replay, step: number): void {
  const d = r.decl;
  // The unifier belongs to one proof step, so it is dropped the moment the step
  // changes -- otherwise navigating away leaves its panes showing a sub-machine
  // that no longer has anything to do with the highlighted command.
  if (UNIFY !== null && UNIFY.step !== Math.max(0, Math.min(step, r.steps.length - 1))) {
    UNIFY = null;
  }
  const ctx = ctxFor(L, d);
  const name = nameOf(L, d);
  // Which step failed, from the replay if it failed there and from the file's
  // own verdict otherwise. The two can disagree: the verifier runs a
  // declaration against what was declared *before* it, while browsing one runs
  // it against the whole file -- so a proof that names a later theorem fails
  // for the verifier and replays clean here. Taking the report's word for it
  // means the step is still marked.
  const reported = L.report.failures.filter((f) => f.index === d.index);
  // Every step a failure names, not just the first: a run carries on past a
  // disjoint-variable violation or a failed unify, so a proof can have several
  // and marking one of them says the others are fine.
  const failedSteps = new Set<number>();
  for (const x of r.steps) if (x.err !== null) failedSteps.add(x.i);
  for (const f of reported) {
    const w = f.where.find((e) => e.at === 'step');
    if (w?.at === 'step') failedSteps.add(w.index);
  }
  const failAt = failedSteps.size === 0 ? null : Math.min(...failedSteps);
  const visible = r.steps.filter((s) => isProofStep(r, s));
  const steps = ONLY_PROOF ? visible : r.steps;
  const at = Math.max(0, Math.min(step, r.steps.length - 1));
  const snap = r.steps[at];

  // The address is written here rather than by each mover, so every way of
  // changing the view -- stepping, entering the unifier, walking its sub-steps
  // -- keeps the URL current and linkable. `replaceState`, so running through a
  // long proof leaves one history entry rather than one per step: Back should
  // return where you came from, not walk backwards a step at a time. It is the
  // *clamped* step, so an out-of-range deep link corrects itself instead of
  // leaving the nav reading a step that does not exist.
  history.replaceState(null, '', urlFor(L, d, at, UNIFY === null ? null : UNIFY.at));
  setTitle(L, name);

  // The crumb repeats the identity: it stays put while the statement row
  // scrolls, and the header is where you look to see what you are in. The
  // statement row carries the whole declaration as the source writes it --
  // `theorem mpd (a b c: wff): $ … $` -- since the kind and name are part of
  // the signature rather than labels stuck to it.
  const kind = declKind(d);
  $('crumb').replaceChildren(
    R.el('span', 'idtag', declId(d)), document.createTextNode(' '),
    R.el('span', `kind ${kindClass(kind)}`, kindText(L, d)), document.createTextNode(' '),
    R.el('b', undefined, name));
  const bar = R.el('span');
  // No space after the name: the signature brings its own when it starts with
  // a binder, and a nullary one has to read `itru: $ T. $`, not `itru : …`.
  bar.append(R.el('span', `kind ${kindClass(kind)}`, kindText(L, d)),
    document.createTextNode(' '), R.el('b', 'declname', name));
  // Laid out rather than concatenated, so a long statement breaks after each
  // `>` instead of running off the row.
  const sig = sigDoc(L, d);
  if (sig !== null) bar.append(R.expr(ctx, sig, STMT_WIDTH));
  $('stmtbar').replaceChildren(bar);
  // The declaration's own error row carries this now; the file-level box is
  // for the file, and repeating it here said the same thing twice.
  showError('');

  // A declaration whose binders are malformed has no proof to show: the
  // machine rejects it before running a command, so there is no first state
  // and nothing to step. Draw what it is and why it was rejected, and leave
  // the panes empty rather than half-filled with a machine that never started.
  if (snap === undefined) {
    $('errrow').replaceChildren(R.el('div', 'errbox',
      r.error ?? reported[0]?.message ?? 'this declaration could not be run'));
    for (const id of ['b-stack', 'b-heap', 'b-hyps', 'callout', 'nav']) {
      $(id).replaceChildren();
    }
    // The listing says why it is empty, in the place the commands would have
    // been. Marked as a failed row like any other, so the `!` in the margin
    // and the shading mean here what they mean everywhere else -- an empty
    // pane would have read as a declaration with no proof, which is a
    // different and unremarkable thing.
    const norun = R.el('div', 'step err norun');
    // The same shape as a command row -- the index gutter, then the content --
    // so the `!` sits where it sits on every other failed row and the text
    // begins where a command begins, without either being positioned by hand.
    norun.append(R.el('span', 'i'), R.el('span', 'why', 'initialization error'));
    $('steps').replaceChildren(norun);
    for (const [id, t] of [['h-stack', 'Stack'], ['h-heap', 'Heap'],
      ['h-hyps', 'Hypotheses']] as const) $(id).textContent = t;
    $('right').classList.remove('unify');
    paintProof();
    return;
  }

  // Command listing. Real step numbers stay under the filter, so the gaps are
  // evident from the numbering and need no "n steps hidden" markers. The
  // unifier's sub-steps splice in beneath the command that invokes them, which
  // is what they are.
  const list = R.el('div');
  for (const s of steps) {
    const row = R.el('div',
      `step${s.i === at && UNIFY === null ? ' cur' : ''}${failedSteps.has(s.i) ? ' err' : ''}`);
    row.append(R.el('span', 'i', String(s.i)));
    // Wrapped, not appended loose: the row is a flex container with an 8px
    // gap, so a bare fragment makes every piece of the command -- the op, the
    // spaces, the name -- its own flex child and spreads `Term im + Save` out
    // across the row.
    const cmd = R.el('span');
    cmd.append(cmdNode(L, ctx, s));
    row.append(cmd);
    if (s.unify.length > 0) {
      const flag = R.el('span', 'uflag', 'u');
      flag.title = 'step into the unifier (u)';
      flag.addEventListener('click', (e) => { e.stopPropagation(); enterUnify(L, s.i); });
      row.append(flag);
    }
    row.addEventListener('click', () => go(L, s.i));
    list.append(row);
    if (UNIFY !== null && s.i === at) {
      for (const [k, us] of UNIFY.trace.steps.entries()) {
        // The command that failed, named by the error itself. Marking the
        // terminal row instead put the flag one row past the thing that did
        // not match -- and on a run whose failure is not at the end, nowhere
        // near it.
        const bad = UNIFY.trace.error !== null && k === UNIFY.trace.steps.length - 1;
        const sub = R.el('div',
          `step ustep${k === UNIFY.at ? ' cur' : ''}${bad ? ' err' : ''}`);
        sub.append(R.el('span', 'i', String(k)));
        sub.append(ucmdNode(L, ctx, us, UNIFY.trace.error !== null));
        sub.addEventListener('click', () => setUstep(L, k));
        list.append(sub);
      }
    }
  }
  $('steps').replaceChildren(list);

  // In proof mode the panes show only proofs, dropping expressions and
  // convertibility elements, but keep their *real* indices. The reason differs
  // by pane: a heap index is an address, and `Ref i` names it, so renumbering
  // would make the pane disagree with the listing; a stack index is only depth
  // and nothing refers to it, but keeping it real is what makes the gaps
  // visible, which is how the pane admits it is not showing everything.
  const isPf = (x: El): boolean => x.k === EL.PROOF;
  const count = (xs: readonly El[]): number =>
    ONLY_PROOF ? xs.filter(isPf).length : xs.length;
  // `M of N` only while the filter is actually hiding something.
  const of = (shown: number, total: number): string =>
    ONLY_PROOF && shown !== total ? `${shown} of ${total}` : `${total}`;
  // "empty" would be a lie when the filter is what emptied the pane.
  const none = (built: HTMLElement, rows: number, total: number): Node =>
    rows > 0 ? built : R.empty(ONLY_PROOF && total > 0 ? 'no proofs — filtered' : 'empty');

  // The unify sub-step being viewed, if any. While it is open the main panes
  // are shown as the *unifier* sees them.
  const US = UNIFY === null ? null : UNIFY.trace.steps[UNIFY.at]!;
  const uhypHere = US !== null && US.cmd === 0x36;

  // Stack, top first: the top is the active end.
  const stack = CUR!.cursor.seek(at);
  // A step that failed never recorded what it popped -- it threw part way, or
  // before touching the stack at all -- so the step whose consumption is most
  // worth seeing was the one showing none. Fall back to the arity the command
  // would have taken, clamped by what is there, which is also the right answer
  // when the failure *is* that there was not enough.
  // `stackPops` looks the command's declaration up, which throws when the id
  // names nothing -- and the step that failed *because* of that is exactly the
  // one being drawn here. What it was going to take is then unknowable, so fall
  // back to what it recorded.
  const wants = snap.err !== null && snap.cmd !== null
    ? Math.max(snap.pops, tryPops(L, snap) ?? snap.pops)
    : snap.pops;
  const firstDoomed = stack.length - Math.min(wants, stack.length);
  const firstFresh = freshFrom(r, at, ONLY_PROOF);
  // Inside the unifier the target and arguments are already gone by its first
  // command, and every `UHyp` takes one more proof off; `mlen` is that depth,
  // so the pane shrinks as you step. Only `UThm`'s `UHyp` eats from the main
  // stack -- in `UThmEnd` it takes from the hypothesis stack and the main one
  // stands still -- and it eats exactly one proof, so it gets the unifier's
  // marker rather than the main view's bar.
  const mlen = US === null ? stack.length : US.mlen;
  const mstack = stack.slice(0, mlen);
  const mDoomed = US === null ? firstDoomed
    : uhypHere && UNIFY!.trace.mode === UMODE.THM ? mlen - 1 : mlen;
  // Nothing arrives on the main stack mid-unify.
  const mFresh = US === null ? firstFresh : mlen;
  const sb = R.el('div');
  let sRows = 0;
  for (let i = mlen - 1; i >= 0; i--) {
    const x = mstack[i]!;
    if (ONLY_PROOF && !isPf(x)) continue;
    const classes: string[] = [];
    // The topmost row *shown*, not index `mlen - 1`. With the filter on the
    // panes are a proof-level machine in their own right, and its top is the
    // topmost proof -- marking the true top would leave nothing marked
    // whenever an expression sits above it, which is most steps. Unfiltered
    // the two are the same row.
    if (sRows === 0) classes.push('top');
    // What this step is about to consume, and what arrived since the previous
    // *visible* step. Recolouring the text does not work -- every name already
    // sits in its own span, so a colour on the row only repaints the
    // parentheses -- hence a bar and a marker in a reserved gutter.
    if (i >= mFresh) classes.push('fresh');
    if (i >= mDoomed) classes.push(US === null ? 'doomed' : 'u-takes');
    const why = i >= mDoomed ? (US === null ? 'consumed by this step' : 'taken by this UHyp')
      : i >= mFresh ? 'pushed by the previous step' : '';
    sb.append(R.slot(i, R.element(ctx, r.arena, x), classes, why));
    sRows++;
  }
  $('b-stack').replaceChildren(none(sb, sRows, mstack.length));
  // The counts follow the filter: counting the expressions a step shuffles
  // would contradict a pane that is not showing them. Inside the unifier the
  // proof step's own counts would describe a step you are not on, so they give
  // way to what the *unify* step takes from this stack.
  const nDoomed = count(mstack.slice(mDoomed));
  const nFresh = count(mstack.slice(Math.min(mFresh, mstack.length)));
  $('h-stack').replaceChildren(
    document.createTextNode(`Stack (${of(count(mstack), mstack.length)})`),
    US === null ? legend(nDoomed, nFresh) : utakeLegend(nDoomed));

  // Heap, bottom-pinned: it is append-only, so the newest entries are in play.
  const heap = r.heap.slice(0, snap.heapLen);
  const prevHeap = prevVisible(r, at, ONLY_PROOF)?.heapLen ?? snap.heapLen;
  const hb = R.el('div');
  let hRows = 0;
  for (const [i, x] of heap.entries()) {
    if (ONLY_PROOF && !isPf(x)) continue;
    // Only a `Ref` names a heap slot. Every other command's `data` is a term,
    // theorem or sort id, which would outline an unrelated slot that happened
    // to share the number.
    const classes: string[] = [];
    const refd = snap.cmd === 0x12 && snap.data === i;
    if (refd) classes.push('refd');
    if (i >= prevHeap) classes.push('fresh');
    hb.append(R.slot(i, R.element(ctx, r.arena, x), classes,
      refd ? 'referenced by this step' : i >= prevHeap ? 'added by the previous step' : ''));
    hRows++;
  }
  $('b-heap').replaceChildren(none(hb, hRows, heap.length));
  $('h-heap').textContent = `Heap (${of(count(heap), heap.length)})`;

  // Hypotheses are append-only like the heap, so the same "just added" marker
  // applies -- a `Hyp` step is exactly where one appears. They are always
  // proofs, so the filter never touches this pane.
  //
  // `UThmEnd` is the exception: there `UHyp` consumes them top down, checking
  // each against the declared statement, so the list shrinks and the top one
  // is marked as taken. In `UThm` the unifier never touches them.
  const inThmEnd = US !== null && UNIFY!.trace.mode === UMODE.THM_END;
  const hlen = inThmEnd ? US.hlen : snap.hypsLen;
  const hDoomed = inThmEnd && uhypHere ? hlen - 1 : hlen;
  const prevHyps = prevVisible(r, at, ONLY_PROOF)?.hypsLen ?? snap.hypsLen;
  const yb = R.el('div');
  for (let i = 0; i < hlen; i++) {
    const classes: string[] = [];
    const fresh = US === null && i >= prevHyps;
    if (fresh) classes.push('fresh');
    if (i >= hDoomed) classes.push('u-takes');
    yb.append(R.slot(i, R.node(ctx, r.arena, r.hyps[i]!), classes,
      i >= hDoomed ? 'taken by this UHyp' : fresh ? 'added by the previous step' : ''));
  }
  $('b-hyps').replaceChildren(hlen === 0 ? R.empty('none') : yb);
  $('h-hyps').replaceChildren(
    document.createTextNode(`Hypotheses (${hlen})`), utakeLegend(hlen - hDoomed));

  // The *declaration's* verdict, not the current step's. Two things were
  // invisible before: a declaration can fail without any step failing -- a bad
  // sort is checked before the proof is run, so `COND` replayed clean while
  // the file said it was broken -- and a failing step said nothing at all
  // unless you happened to already be standing on it.
  const fail = reported[0] ?? null;
  // The step is written as the prefix below, so it is dropped from the trail
  // here -- otherwise a failure the replay did not reproduce, and whose text
  // therefore comes from the report, reads `step 40: step 40, …`.
  const why = r.error ?? (fail === null ? null
    : trailOf(fail.where.filter((w) => w.at !== 'step'), fail.message));
  if (why === null) {
    $('errrow').replaceChildren();
  } else {
    const box = R.el('div', 'errbox');
    const line = R.el('span', 'why');
    if (failAt !== null) line.append(document.createTextNode(`step ${failAt}: `));
    // The failing step's own arguments, so a message about one of them can say
    // what it stands for. Read from that step rather than the current one:
    // this row is shown from wherever you are standing.
    const args = failAt === null ? null : stepArgs(L, r, failAt);
    line.append(messageNode(L, why,
      args === null ? undefined : { ctx, arena: r.arena, args }));
    box.append(line);
    if (failAt !== null && !failedSteps.has(at)) {
      const n = failedSteps.size;
      const go2 = R.el('button', undefined,
        n === 1 ? '↓ go to the failure' : `↓ go to the first of ${n}`);
      go2.title = `jump to step ${failAt}`;
      go2.addEventListener('click', () => go(L, failAt));
      box.append(go2);
    }
    $('errrow').replaceChildren(box);
  }

  // The unify panes exist only while the unifier is open; `#right.unify` is
  // what splits each row in two.
  // A sort has no proof and so no machine state; the panes would be three
  // empty boxes. What it *is* is its modifiers, which take the space instead.
  const isSort = d.cls === CLASS.SORT;
  $('right').classList.toggle('sort', isSort);
  $('right').classList.toggle('unify', UNIFY !== null);
  if (UNIFY !== null) renderUnify(r, ctx);

  // Inside the unifier the callout describes the unify command, not the proof
  // step that parked to run it.
  const us = UNIFY === null ? undefined : UNIFY.trace.steps[UNIFY.at];
  let head: Node;
  try {
    head = isSort ? sortCallout(L, d, r)
      : UNIFY !== null && us !== undefined
        ? ucallout(L, ctx, r, UNIFY.trace, us)
        : callout(L, ctx, r, snap, stack);
  } catch (e) {
    if (!(e instanceof MmbError)) throw e;
    head = calloutError(e);
  }
  $('callout').replaceChildren(head);
  buildNav(L, r, at, visible);
  paintProof();
  anchor();
}

/**
 * Scroll anchoring, which follows what each pane means.
 *
 * The current step must be in view or stepping is blind. The heap is
 * append-only, so it is pinned to the bottom like a terminal -- the newest
 * entries are the ones in play. A `Ref i` overrides that to bring slot `i` into
 * view: `Ref` is 62% of all commands and heaps run to hundreds of entries, so a
 * reference you cannot see is useless.
 */
function anchor(): void {
  document.querySelector('#steps .step.cur')?.scrollIntoView({ block: 'nearest' });
  const heap = $('b-heap');
  const refd = heap.querySelector('.slot.refd');
  if (refd !== null) refd.scrollIntoView({ block: 'nearest' });
  else heap.scrollTop = heap.scrollHeight;
  if (UNIFY !== null) {
    document.querySelector('#steps .step.ustep.cur')?.scrollIntoView({ block: 'nearest' });
  }
}

/**
 * The header controls. Buttons rather than a bare counter, because the tool is
 * used by moving: a mouse user needs the same reach as the keyboard, and a
 * disabled button is how the view says an edge has been reached.
 */
function buildNav(L: Loaded, r: Replay, at: number, visible: Snapshot[]): void {
  const nav = $('nav');
  nav.replaceChildren();
  // Every button names its key. The `kbd` hint at the end is the first thing
  // dropped when the row is tight, and it never covered the ends anyway, so
  // without this the keyboard equivalents were only in the help modal.
  const btn = (label: string, title: string, on: () => void, disabled = false): HTMLElement => {
    const b = R.el('button', undefined, label) as HTMLButtonElement;
    b.title = title;
    b.disabled = disabled;
    b.addEventListener('click', on);
    return b;
  };
  const meta = (t: string): HTMLElement => R.el('span', 'meta', t);

  if (UNIFY !== null) {
    const n = UNIFY.trace.steps.length - 1;
    // Phrased for a reader, not for an error message: `applying syl`, not
    // `Thm syl`. The mode says which verb, except at the terminal step, where
    // the run is no longer applying anything but reporting on the match.
    const at = UNIFY.trace.steps[UNIFY.at];
    const verb = at?.cmd === undefined || at.cmd === null ? 'checking'
      : UNIFY.trace.mode === UMODE.THM ? 'applying'
        : UNIFY.trace.mode === UMODE.THM_END ? 'checking' : 'unfolding';
    const label = R.el('span', 'meta', `${verb} `);
    label.append(R.el('b', undefined, UNIFY.trace.name));
    nav.append(label);
    // Up and down are never disabled here: they run off the ends of the
    // sub-steps back into the proof, like any tree.
    nav.append(btn('⏮', 'first sub-step (Home, g)', () => setUstep(L, 0), UNIFY.at === 0));
    nav.append(btn('↑', 'back one sub-step (↑, k)', () => moveRow(L, -1)));
    nav.append(meta(`unify step ${UNIFY.at} / ${n}`));
    nav.append(btn('↓', 'forward one sub-step (↓, j)', () => moveRow(L, 1)));
    nav.append(btn('⏭', 'last sub-step (End, G)', () => setUstep(L, n), UNIFY.at >= n));
    nav.append(btn('exit', 'leave the unifier (←, h, Esc)', () => toggleUnify(L)));
    nav.append(R.el('kbd', undefined, '↑/↓ j/k · ←/h exits'));
    return;
  }

  const vis = visible.map((s) => s.i);
  const first = ONLY_PROOF ? (vis[0] ?? 0) : 0;
  const last = ONLY_PROOF ? (vis[vis.length - 1] ?? 0) : r.steps.length - 1;
  const atFirst = at <= first, atLast = at >= last;

  nav.append(btn('⏮', 'first step (Home, g)', () => go(L, first), atFirst));
  nav.append(btn('-10', 'back ten steps (PgUp)', () => move(L, -10), atFirst));
  nav.append(btn('↑', 'back one step (↑, k)', () => move(L, -1), atFirst));
  nav.append(meta(`step ${at} / ${r.steps.length - 1}`));
  nav.append(btn('↓', 'forward one step (↓, j)', () => move(L, 1), atLast));
  nav.append(btn('+10', 'forward ten steps (PgDn)', () => move(L, 10), atLast));
  nav.append(btn('⏭', 'last step (End, G)', () => go(L, last), atLast));
  nav.append(R.el('kbd', undefined, '↑/↓ j/k step · →/l unify · Home/End'));
}

/**
 * The unify stack and heap, beside the main ones.
 *
 * Marked with the same shape as the main panes -- what this command eats, what
 * the last one left -- because the unifier is a machine in its own right and
 * reading it is the same exercise. Its markers differ in colour so the two
 * levels never look like one.
 */
function renderUnify(r: Replay, ctx: R.Ctx): void {
  const u = UNIFY!;
  const us = u.trace.steps[u.at]!;
  const prev = u.at > 0 ? u.trace.steps[u.at - 1]! : null;

  // A command that failed never recorded what it popped, so the step whose
  // consumption is most worth seeing was the one showing none. Fall back to the
  // arity it would have taken, clamped by what is actually there -- which is
  // also the answer when the failure *is* that there was not enough.
  const failedHere = u.trace.error !== null && u.at === u.trace.steps.length - 1;
  const wants = failedHere ? ustackPops(us.cmd) : us.pops;
  const uDoomed = us.ustack.length - Math.min(wants, us.ustack.length);
  const uFresh = prev === null ? us.ustack.length : prev.ustack.length - prev.pops;

  // Drawn top-first like the main stack: the top is the end being destructured.
  const sb = R.el('div');
  for (let i = us.ustack.length - 1; i >= 0; i--) {
    const classes: string[] = [];
    if (i === us.ustack.length - 1) classes.push('top');
    if (i >= uDoomed) classes.push('u-takes');
    if (i >= uFresh) classes.push('u-makes');
    sb.append(R.slot(i, R.taggedNode(ctx, r.arena, us.ustack[i]!), classes,
      i >= uDoomed ? 'consumed by this step'
        : i >= uFresh ? 'pushed by the previous step' : ''));
  }
  // An empty unify stack means the target was consumed -- but only if the run
  // got that far. Saying it matched on a run that failed is the same wrong
  // answer the terminal row used to give.
  $('b-ustack').replaceChildren(us.ustack.length === 0
    ? R.empty(u.trace.error === null ? 'empty — target fully matched' : 'empty')
    : sb);

  const nMade = us.ustack.length - uFresh;
  const head = document.createTextNode(`Unify stack (${us.ustack.length})`);
  // The count, not the reason: the failing step and the callout both carry the
  // message, and a third copy in the pane heading crowded out the one thing
  // only the heading can say -- how much of this stack the step is taking.
  $('h-ustack').replaceChildren(head, ulegend(wants, nMade));

  // The uheap is the substitution, indexed by variable, so it reads in order.
  // `URef i` matches the top of the ustack against slot `i` -- the unify
  // counterpart of `Ref` reading the main heap, so it is boxed the same way.
  // `UTermSave`/`UDummy` extend it, so mark what the last command added.
  const uhFresh = prev === null ? us.uheap.length : prev.uheap.length;
  const hb = R.el('div');
  for (const [i, e] of us.uheap.entries()) {
    const classes: string[] = [];
    const uref = us.cmd === 0x32 && us.data === i;
    if (uref) classes.push('refd');
    if (i >= uhFresh) classes.push('fresh');
    hb.append(R.slot(i, R.taggedNode(ctx, r.arena, e), classes,
      uref ? 'matched against by this step'
        : i >= uhFresh ? 'added by the previous step' : ''));
  }
  $('b-uheap').replaceChildren(us.uheap.length === 0 ? R.empty('empty') : hb);
  $('h-uheap').textContent = `Unify heap — substitution (${us.uheap.length})`;

  $('b-uheap').querySelector('.slot.refd')?.scrollIntoView({ block: 'nearest' });
}

/** The unify panes' legend, in the sub-machine's own colours. */
function ulegend(nTakes: number, nMakes: number): Node {
  if (nTakes === 0 && nMakes === 0) return document.createDocumentFragment();
  const box = R.el('span', 'legend');
  if (nTakes > 0) box.append(R.el('i', 'l-utake', `▸ ${nTakes} consumed`));
  if (nTakes > 0 && nMakes > 0) box.append(document.createTextNode(' · '));
  if (nMakes > 0) box.append(R.el('i', 'l-umake', `${nMakes} just pushed`));
  return box;
}

/** What a `UHyp` takes from a main pane, which is always one proof. */
function utakeLegend(n: number): Node {
  if (n <= 0) return document.createDocumentFragment();
  const box = R.el('span', 'legend');
  box.append(R.el('i', 'l-utake', `▸ ${n} consumed`));
  return box;
}

/** The stack pane's legend: how much this step eats, and what just arrived. */
function legend(nDoomed: number, nFresh: number): Node {
  if (nDoomed === 0 && nFresh === 0) return document.createDocumentFragment();
  const box = R.el('span', 'legend');
  if (nDoomed > 0) box.append(R.el('i', 'l-doom', `${nDoomed} consumed here`));
  if (nDoomed > 0 && nFresh > 0) box.append(document.createTextNode(' · '));
  if (nFresh > 0) box.append(R.el('i', 'l-fresh', `▸ ${nFresh} just pushed`));
  return box;
}

/** The previous step the listing actually shows. */
function prevVisible(r: Replay, at: number, onlyProof: boolean): Snapshot | undefined {
  for (let i = at - 1; i >= 0; i--) {
    const s = r.steps[i]!;
    if (!onlyProof || isProofStep(r, s)) return s;
  }
  return undefined;
}

/**
 * The stack index at or above which everything arrived since the previous
 * *visible* step.
 *
 * With the filter on, the hidden steps in between are one transition of a
 * proof-level machine, so the diff has to be against the previous visible step
 * rather than `at - 1`. Each step cuts the stack to `len - pops` before
 * pushing, so the deepest it was cut back to over the interval is the low-water
 * mark: everything at or above it arrived since, everything below was never
 * popped. For a single step this reduces to `len - pops`.
 */
function freshFrom(r: Replay, at: number, onlyProof: boolean): number {
  let from = at - 1;
  if (onlyProof) {
    while (from >= 0 && !isProofStep(r, r.steps[from]!)) from--;
  }
  if (from < 0) return Infinity;
  const cur = new StackCursor(r);
  let low = Infinity;
  for (let k = from; k < at; k++) {
    low = Math.min(low, cur.seek(k).length - r.steps[k]!.pops);
  }
  return low;
}

/**
 * What the active step does.
 *
 * Schematic rather than concrete: the stack pane already shows the
 * instantiated elements, marked with red bars, so repeating them would be
 * redundant. What this adds is the shape of what the step takes, in the applied
 * declaration's *own* variables.
 */
function callout(
  L: Loaded, ctx: R.Ctx, r: Replay, s: Snapshot, stack: readonly El[],
): Node {
  const box = R.el('div', 'popout');
  const d = r.decl;
  // First, before anything describing what the step was going to do: it did
  // not do it, and that is the answer the reader is after.
  if (s.err !== null) {
    const e = R.el('div', 'po-err');
    const args = stepArgs(L, r, s.i);
    e.append(messageNode(L, s.err,
      args === null ? undefined : { ctx, arena: r.arena, args }));
    box.append(e);
  }

  // A step that runs the unifier offers to step into it.
  const go = R.el('span', 'po-go');
  if (s.unify.length > 0) {
    const b = R.el('button', 'po-u', UNIFY === null ? 'unify ⌄' : 'exit unifier');
    b.addEventListener('click', () => toggleUnify(L));
    go.append(b);
  }

  const tgt = stepTarget(s);
  if (tgt !== null) {
    const at = L.byId.get(key(tgt.cls, tgt.num));
    if (at !== undefined) {
      const t = L.decls[at]!;
      const a = R.el('a', undefined, 'open ↗') as HTMLAnchorElement;
      a.href = declUrl(L, t);
      a.title = `open ${nameOf(L, t)}`;
      go.append(a);
    }
    // A target the walk never reached has no declaration to read a kind or a
    // signature off, so both are left out rather than taken from declaration 0
    // -- which reads as fact and is one about an unrelated declaration. The id
    // tag still says which one is meant.
    box.append(declHead(L.file, tgt.cls, tgt.num,
      at === undefined ? '' : declKind(L.decls[at]!),
      at === undefined ? '' : signature(L, L.decls[at]!), go));
  } else if (s.cmd !== null) {
    const head = R.el('div', 'po-head');
    head.append(cmdNode(L, ctx, s), go);
    box.append(head);
  } else {
    // The end of the proof: the interesting thing is what was just proved, so
    // show this declaration's own statement.
    go.classList.add('po-none');
    go.append(document.createTextNode(
      r.error === null ? `${r.steps.length - 1} steps — proved` : 'failed'));
    box.append(declHead(L.file, d.cls, d.num, declKind(d), signature(L, d), go));
  }

  const sch = schematic(ctx, r, s, stack, ONLY_PROOF);
  if (sch !== null) {
    const eff = R.el('div', 'po-eff');
    const takes = effRow('takes', 'consumes', sch.takes, ONLY_PROOF);
    const makes = effRow('makes', 'produces', sch.makes, ONLY_PROOF);
    if (takes !== null) eff.append(takes);
    if (makes !== null) eff.append(makes);
    const notes = notesNode(sch.notes);
    if (notes !== null) eff.append(notes);
    if (eff.childElementCount > 0) box.append(eff);
  }
  return box;
}

/**
 * The callout while inside the unifier, describing the *unify* command.
 *
 * Without this the pane kept describing the parked proof step, identically for
 * every sub-step -- so the one view whose whole job is the sub-machine said
 * nothing about it.
 */
function ucallout(
  L: Loaded, ctx: R.Ctx, r: Replay, u: UnifyTrace, us: UnifyStep,
): Node {
  const box = R.el('div', 'popout');

  // The failing command is the last step of a failed run, so it carries the
  // reason -- there is no terminal row to carry it.
  if (u.error !== null && us === u.steps[u.steps.length - 1]) {
    const e = R.el('div', 'po-err');
    e.append(messageNode(L, u.error));
    box.append(e);
  }

  if (us.cmd === null) {
    const head = R.el('div', 'po-head');
    head.append(R.el('span', 'po-none', u.error === null
      ? 'target fully matched — the check succeeds' : 'check failed'));
    box.append(head);
    if (u.error !== null) {
      const why = R.el('div', 'po-sig', u.error);
      why.style.color = 'var(--err)';
      box.append(why);
    }
    return box;
  }

  // `UTerm t` names a term, so its declaration heads the callout and can be
  // opened -- the same drill-down the proof-side `Term` offers.
  if (us.cmd === 0x30 || us.cmd === 0x31) {
    const at = L.byId.get(key(CLASS.TERM, us.data));
    if (at !== undefined) {
      const t = L.decls[at]!;
      const go = R.el('span', 'po-go');
      const a = R.el('a', undefined, 'open ↗') as HTMLAnchorElement;
      a.href = declUrl(L, t);
      a.title = `open ${nameOf(L, t)}`;
      go.append(a);
      box.append(declHead(L.file, CLASS.TERM, us.data, declKind(t), signature(L, t), go));
    } else {
      const head = R.el('div', 'po-head');
      head.append(ucmdNode(L, ctx, us, u.error !== null));
      box.append(head);
    }
  } else {
    const head = R.el('div', 'po-head');
    head.append(ucmdNode(L, ctx, us, u.error !== null));
    box.append(head);
    // `URef i` names a slot of *this* substitution, so unlike the schematic
    // commands its contents are concrete and worth spelling out.
    if (us.cmd === 0x32) {
      const slot = us.uheap[us.data];
      if (slot !== undefined) {
        const sig = R.el('div', 'po-sig');
        sig.append(document.createTextNode(`H[${us.data}] = `),
          R.taggedNode(ctx, r.arena, slot));
        box.append(sig);
      }
    }
  }

  // Never filtered: the proof-only filter is about the *proof* stream, and
  // hiding non-proof items here would empty every row the unifier has.
  const sch = uschematic(ctx, u, us);
  if (sch !== null) {
    const eff = R.el('div', 'po-eff');
    const takes = effRow('takes', 'consumes', sch.takes, false);
    const makes = effRow('makes', 'produces', sch.makes, false);
    if (takes !== null) eff.append(takes);
    if (makes !== null) eff.append(makes);
    const notes = notesNode(sch.notes);
    if (notes !== null) eff.append(notes);
    if (eff.childElementCount > 0) box.append(eff);
  }
  return box;
}

/**
 * What a sort is: its four modifiers, and what each one means.
 *
 * The glosses are the rules mm0.md gives ("Sorts", the four bullets under
 * `sort-stmt`), not a summary of the checks this verifier happens to make:
 * `strict` also forbids dummy variables and appearance as a dependency, which
 * are easy to leave out if the checks are all one reads.
 *
 * A modifier the sort lacks is struck through rather than left out: all four
 * apply to every sort, and the ones it does not have say as much as the ones
 * it does.
 */
function sortCallout(L: Loaded, d: Decl, r: Replay): Node {
  const has = new Set(L.file.sortMods(d.num));
  const rows: [string, string, string][] = [
    ['pure', 'has no term formers: no term may target it, so only variables inhabit it',
      'terms may target it'],
    ['strict', 'has no binders: no bound or dummy variable may have it, '
      + 'and it may not appear as a dependency',
      'a bound variable may have it'],
    ['provable', 'formulas in axioms and theorems may have it',
      'no formula in an axiom or theorem may have it'],
    ['free', 'no definition or theorem may use a dummy variable of it',
      'a dummy variable may have it'],
  ];
  const box = R.el('div', 'popout');
  // The identity line every other declaration's callout ends with, kept: it
  // says which declaration this is and that it verified, which is as true of a
  // sort as of anything else. The keyword here is the bare `sort` -- the
  // modifiers are the four lines below it, and saying them twice on top of
  // each other says nothing extra.
  const go = R.el('span', 'po-go po-none');
  go.append(document.createTextNode(
    r.error === null ? `${Math.max(0, r.steps.length - 1)} steps — proved` : 'failed'));
  box.append(declHead(L.file, d.cls, d.num, declKind(d), '', go));
  const dl = R.el('div', 'mods');
  for (const [kw, on, off] of rows) {
    const yes = has.has(kw);
    dl.append(R.el('span', `kw${yes ? '' : ' off'}`, kw),
      R.el('span', `gloss${yes ? '' : ' off'}`, yes ? on : off));
  }
  box.append(dl);
  return box;
}

/** The declaration the active step's command refers to, if any. */
function stepTarget(s: Snapshot): { cls: DeclClass; num: number } | null {
  if (s.cmd === null) return null;
  const base = s.cmd & ~1;
  if (base === 0x10) return { cls: CLASS.TERM, num: s.data };
  if (base === 0x14) return { cls: CLASS.THM, num: s.data };
  return null;
}

const OPS: Record<number, string> = {
  0x10: 'Term', 0x11: 'TermSave', 0x12: 'Ref', 0x13: 'Dummy', 0x14: 'Thm',
  0x15: 'ThmSave', 0x16: 'Hyp', 0x17: 'Conv', 0x18: 'Refl', 0x19: 'Sym',
  0x1a: 'Cong', 0x1b: 'Unfold', 0x1c: 'ConvCut', 0x1e: 'ConvSave',
  0x1f: 'Save', 0x20: 'Sorry',
};

const CONV_OPS = new Set([0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1e]);

/**
 * One command, rendered as the listing shows it.
 *
 * `TermSave t` is `Term t; Save` welded into one opcode, and it is written as
 * the two commands it is: spelled `TermSave`, the `Save` half reads as a
 * suffix on the name and is easy to miss, and it is the half with the effect
 * you are most likely to be looking for thirty steps later, when a `Ref` picks
 * the slot back up.
 */
function cmdNode(L: Loaded, ctx: R.Ctx, s: Snapshot): DocumentFragment {
  const frag = document.createDocumentFragment();
  if (s.cmd === null) {
    const e = R.el('span', 'op', '(end)');
    e.style.color = 'var(--faint)';
    frag.append(e);
    return frag;
  }
  const base = s.cmd & ~1; // TermSave/ThmSave differ from Term/Thm in bit 0
  const saved = (s.cmd === 0x11 || s.cmd === 0x15);
  // The *base* op names the row and colours it, with the save written out as
  // the `+ Save` suffix below. Naming it `TermSave` instead both said `Save`
  // twice and asked for a `.op-TermSave` colour that does not exist, so the
  // row fell back to plain foreground and stopped reading as a `Term`.
  // `Ref` and `Sorry` each have two behaviours, and the opcode is the same for
  // both -- which one ran is decided by what was on the stack. The spec names
  // them separately, and so does the listing: `Ref 3` copying a heap slot and
  // `ConvRef 3` discharging an obligation are different things to read past.
  //
  // `Ref` normally pops nothing; popping one means it discharged. `Sorry`
  // pops one either way, and pushes a proof only in the non-conversion case.
  const conv = (s.cmd === 0x12 && s.pops === 1)
    || (s.cmd === 0x20 && s.pushed.length === 0);
  const name = conv
    ? (s.cmd === 0x12 ? 'ConvRef' : 'ConvSorry')
    : OPS[saved ? base : s.cmd] ?? `0x${s.cmd.toString(16)}`;
  // A `ConvSorry` is still a `Sorry`: it is the same admission, so it keeps the
  // warning colour rather than joining the conversion commands.
  const cls = `op op-${CONV_OPS.has(s.cmd) || (conv && s.cmd === 0x12) ? 'conv'
    : s.cmd === 0x20 ? 'Sorry' : name}`;
  frag.append(R.el('span', cls, name));
  if (base === 0x10 || base === 0x14) {
    // The applied declaration is a link: following it is the drill-down.
    const isTerm = base === 0x10;
    const a = R.el('a', undefined,
      isTerm ? L.file.termName(s.data) : L.file.thmName(s.data)) as HTMLAnchorElement;
    a.href = ctx.href(isTerm ? CLASS.TERM : CLASS.THM, s.data);
    frag.append(document.createTextNode(' '), a);
    if (saved) {
      frag.append(document.createTextNode(' '), R.el('span', 'op-fuse', '+'),
        document.createTextNode(' '), R.el('span', 'op', 'Save'));
    }
  } else if (s.cmd === 0x12) {
    const idx = R.el('span', undefined, String(s.data));
    idx.style.color = 'var(--faint)';
    frag.append(document.createTextNode(' '), idx);
  } else if (s.cmd === 0x13) {
    frag.append(document.createTextNode(' '), R.sortLink(ctx, s.data));
  }
  return frag;
}

const UOPS: Record<number, string> = {
  0x30: 'UTerm', 0x31: 'UTermSave', 0x32: 'URef', 0x33: 'UDummy', 0x36: 'UHyp',
};

/**
 * One unify command, coloured the way the main listing colours its own.
 *
 * Every op used to be `op-conv`, which painted the whole sub-step listing one
 * green: a `URef` is a match against the substitution, not a conversion, and
 * reads like the listing's `Ref`. Only `UTerm` and `UHyp` carry a colour, and
 * they borrow the ones `Term` and `Thm` already have.
 */
function ucmdNode(
  L: Loaded, ctx: R.Ctx, us: { cmd: number | null; data: number }, failed = false,
): HTMLElement {
  const box = R.el('span', 'op');
  if (us.cmd === null) {
    // The terminal row is the run's verdict, so it has to state which one:
    // saying the target matched on a run that failed is not a label, it is a
    // wrong answer. Not `(end)` either -- that is what the proof listing's own
    // terminal row says, and this means something stronger.
    const bad = failed === true;
    box.textContent = bad ? '(check failed)' : '(target matched)';
    box.style.color = bad ? 'var(--err)' : 'var(--faint)';
    return box;
  }
  const op = UOPS[us.cmd] ?? `0x${us.cmd.toString(16)}`;
  if (us.cmd === 0x30 || us.cmd === 0x31) {
    // `UTermSave t` is `USave; UTerm t` -- and note the order is the mirror of
    // the proof stream's `TermSave` = `Term t; Save`: here the save runs
    // *first*, on the whole term, before it is taken apart. Writing it out is
    // what makes that visible; `UTermSave` reads like `TermSave` and hides it.
    if (us.cmd === 0x31) {
      box.append(R.el('span', 'op', 'USave'), document.createTextNode(' '),
        R.el('span', 'op-fuse', '+'), document.createTextNode(' '));
    }
    box.append(R.el('span', 'op op-Term', 'UTerm'));
    const a = R.el('a', undefined, L.file.termName(us.data)) as HTMLAnchorElement;
    a.href = ctx.href(CLASS.TERM, us.data);
    box.append(document.createTextNode(' '), a);
    return box;
  }
  if (us.cmd === 0x36) {
    box.append(R.el('span', 'op op-Thm', op));
    return box;
  }
  box.append(document.createTextNode(op));
  if (us.cmd === 0x32) {
    const idx = R.el('span', undefined, String(us.data));
    idx.style.color = 'var(--faint)';
    box.append(document.createTextNode(' '), idx);
  } else if (us.cmd === 0x33) {
    box.append(document.createTextNode(' '), R.sortLink(ctx, us.data));
  }
  return box;
}

// ---- navigation -----------------------------------------------------------

/** The address of a step, and of a unify sub-step within it. */
function urlFor(L: Loaded, d: Decl, step: number, ustep: number | null): string {
  const base = `${listUrl(L.name)}/${clsOf(d)}/${encodeURIComponent(nameOf(L, d))}/${step}`;
  return ustep === null ? base : `${base}/u${ustep}`;
}

function go(L: Loaded, step: number): void {
  if (CUR === null) return;
  // Setting the hash here would fire a hashchange and route again; `renderDecl`
  // writes the address itself.
  renderDecl(L, CUR.r, step);
}

function currentStep(): number {
  // Group 4: the file leads the address, so everything after it moved along one.
  const m = ROUTE.exec(location.hash);
  return m?.[4] === undefined ? 0 : Number(m[4]);
}

function move(L: Loaded, delta: number): void {
  if (CUR === null) return;
  const r = CUR.r;
  const at = currentStep();
  if (!ONLY_PROOF) {
    go(L, Math.max(0, Math.min(at + delta, r.steps.length - 1)));
    return;
  }
  // In proof mode navigation moves between *visible* steps: offering to go
  // somewhere the listing does not show would be a lie about what happened.
  const vis = r.steps.filter((s) => isProofStep(r, s)).map((s) => s.i);
  if (vis.length === 0) return;
  let k = vis.findIndex((i) => i >= at);
  if (k < 0) k = vis.length - 1;
  go(L, vis[Math.max(0, Math.min(k + delta, vis.length - 1))]!);
}

// ---- wiring ---------------------------------------------------------------

/**
 * Where the open file came from, so a reload can get it back.
 *
 * The hash survives a refresh, so the view knows exactly where you were --
 * dropping you at the picker anyway is the app forgetting something it was
 * told. A file fetched by URL can simply be fetched again; one the user
 * supplied cannot be re-read without them, so it is named and waited for.
 */
type Source = { kind: 'url'; url: string } | { kind: 'file'; name: string };

const SRC_KEY = 'mmb-source';

function remember(src: Source): void {
  try {
    localStorage.setItem(SRC_KEY, JSON.stringify(src));
  } catch {
    // Storage can be unavailable or full; remembering is a convenience.
  }
}

function lastSource(): Source | null {
  try {
    const raw = localStorage.getItem(SRC_KEY);
    if (raw === null) return null;
    const v = JSON.parse(raw) as Source;
    return v.kind === 'url' || v.kind === 'file' ? v : null;
  } catch {
    return null;
  }
}

function openBytes(name: string, buf: ArrayBuffer, src: Source): void {
  showError('');
  remember(src);
  const bytes = new Uint8Array(buf);
  // Kept for next time, so a refresh does not need the file again. Fire and
  // forget: whether it is stored has no bearing on reading it now.
  void store.save(name, bytes);
  load(name, bytes);
}

/**
 * Re-read the open file, for the recompile-and-look loop.
 *
 * A URL can be fetched again, so that case is whole. A file the user picked
 * cannot: the browser hands over the bytes, not a handle to re-read them, and
 * offers no way back to that file without another gesture. So the picker is
 * opened on the same file's behalf rather than pretending to reload -- the
 * address is untouched either way, so it lands back on the same step.
 */
function reread(): void {
  const src = lastSource();
  if (src === null) return;
  if (src.kind === 'url') { openUrl(src.url, true); return; }
  status('busy', `pick ${src.name} again to reload it`);
  ($('file') as HTMLInputElement).click();
}

/** Fetch a `.mmb` by URL and open it. */
function openUrl(url: string, restoring = false): void {
  status('busy', restoring ? 'reopening…' : 'fetching…');
  // The same entry point as a dropped file: both end at a Uint8Array, so
  // nothing downstream knows or cares where the bytes came from.
  void fetch(url)
    .then((res) => {
      if (!res.ok) throw new Error(`${res.status} ${res.statusText}`);
      return res.arrayBuffer();
    })
    .then((buf) => openBytes(url.split('/').pop()!, buf, { kind: 'url', url }))
    .catch((err: unknown) => {
      // Offline, or the file has moved. A kept copy is better than nothing.
      void store.load().then((saved) => {
        if (restoring && saved !== null) {
          openBytes(saved.name, saved.bytes, { kind: 'url', url });
          return;
        }
        status('bad', 'not found');
        $('open').classList.add('on');
        // The sample libraries are build outputs of the examples/ sources, so
        // that is where to build them -- `mm0-rs compile examples/peano.mm1
        // examples/peano.mmb`, which the examples CI job exercises. The copies
        // the buttons load live under test/ and are committed frozen (the tests
        // pin exact counts to them), so build into examples/, not over those.
        showError(`${url}: ${String(err)}`
          + (restoring ? '' : ' — build the libraries from examples/,'
            + ' e.g. `mm0-rs compile examples/peano.mm1 examples/peano.mmb`'));
      });
    });
}

/** Tell the picker which file a refresh is waiting for, and where it was. */
function waitingFor(name: string): void {
  const where = ROUTE.exec(location.hash);
  $('drop').textContent = where === null
    ? `drop ${name} here again`
    : `drop ${name} here again — you were at ${decodeURIComponent(where[3]!)}`;
}

/** The example whose path ends in this name, if the page offers one. */
function exampleFor(name: string): string | null {
  for (const b of document.querySelectorAll<HTMLElement>('[data-example]')) {
    const url = b.dataset['example']!;
    if (url.split('/').pop() === name) return url;
  }
  return null;
}

/**
 * Where the development server publishes a file it was told to serve.
 *
 * Relative to the page, so it works wherever the page is mounted.
 */
const servedUrl = (name: string): string => `open/${encodeURIComponent(name)}`;

/**
 * Whether a server here publishes `/open/`, which it says by opening the page
 * with `?served`.
 *
 * Asked rather than probed. Probing means a request for a file that is not
 * there on every ordinary deep link, and a failed fetch is written to the
 * console whatever the code does with the rejection -- five of them on the
 * front page alone, which the UI suite reads as the page erroring. The marker
 * is in the query, so it survives the hash moving around inside a file and a
 * refresh, both of which have to keep working.
 */
const servedHere = (): boolean => new URLSearchParams(location.search).has('served');

/**
 * Get the file the address names.
 *
 * Four ways in, in order of how much they can be trusted to be *that* file. A
 * development server's copy comes first: `npm start peano.mmb` serves the file
 * the user named, so it is the one they mean, ahead of an example or a kept
 * copy that share its name -- `test/peano.mmb` is a frozen fixture, and opening
 * that instead of the file just compiled is exactly the confusion to avoid.
 * Then a remembered URL, which is re-fetched and so is current; then an example,
 * the same fetch by another name; then the browser's kept copy, which is
 * whatever was last read -- right when the user supplied the file themselves,
 * since there is no other way back to it. Failing all four, say which file is
 * wanted and wait for it.
 *
 * Off the development server there is no first way in at all, and the chain is
 * the three it always was.
 */
function resolveFile(name: string): void {
  if (!servedHere()) { resolveWithoutServer(name); return; }
  status('busy', 'reopening…');
  void fetch(servedUrl(name))
    .then((res) => {
      if (!res.ok) throw new Error(`${res.status} ${res.statusText}`);
      return res.arrayBuffer();
    })
    .then((buf) => {
      // The fetch is asynchronous, so the address can move on while it is in
      // flight; the same withdrawn-question case as the store read below.
      if (fileInHash() !== name) return;
      // Remembered as a URL, which is what it is: `r` after a recompile
      // re-fetches it, so the served file reloads in place.
      openBytes(name, buf, { kind: 'url', url: servedUrl(name) });
    })
    .catch(() => { resolveWithoutServer(name); });
}

/** The rest of the chain, for a file the development server is not serving. */
function resolveWithoutServer(name: string): void {
  const src = lastSource();
  if (src !== null && src.kind === 'url' && src.url.split('/').pop() === name) {
    openUrl(src.url, true);
    return;
  }
  const ex = exampleFor(name);
  if (ex !== null) { openUrl(ex, true); return; }
  status('busy', 'reopening…');
  void store.load().then((saved) => {
    // The store read is asynchronous, so the address can move on while it is in
    // flight -- another file opened, or a declaration within a different one
    // navigated to. Everything below mutates the one global view, so a stale
    // resolution would clobber whatever is now on screen with a file no longer
    // asked for. If the address no longer names this file, this answer is for a
    // question that has been withdrawn.
    if (fileInHash() !== name) return;
    if (saved !== null && saved.name === name) {
      openBytes(saved.name, saved.bytes, { kind: 'file', name });
      return;
    }
    status('', '');
    // A file the user supplied is a different case from one that does not
    // exist: the browser cannot re-read it, but they can hand it over again,
    // and the address is still where they were. Keep both.
    if (src !== null && src.kind === 'file' && src.name === name) {
      $('open').classList.add('on');
      $('list').classList.add('off');
      $('detail').classList.remove('on');
      waitingFor(name);
      return;
    }
    // Otherwise nothing can produce it. Say so and fall back to the selector,
    // rather than leaving an address in the bar naming a file that is not
    // there and cannot be fetched -- picking one is what has to happen next.
    LOADED = null;
    ($('home') as HTMLAnchorElement).href = '#';
    history.replaceState(null, '', location.pathname + location.search);
    route();
    showError(`${name} not found`);
  });
}

/**
 * Put back whatever was open, so a refresh lands where it left off.
 *
 * A URL is re-fetched rather than served from the kept copy, because the file
 * behind it can change -- recompiling an example and reloading should show the
 * new one, not last time's. The kept copy is the fallback for when that fetch
 * fails, and the only route for a file the user supplied, which cannot be
 * re-read without them.
 */
function restore(): void {
  // The address names the file, so it decides -- otherwise a pasted link to
  // one library would open whichever was last read and then fail to find the
  // declaration in it.
  const want = fileInHash();
  if (want !== null) { resolveFile(want); return; }
  const src = lastSource();
  if (src === null) return;
  if (src.kind === 'url') { openUrl(src.url, true); return; }
  status('busy', 'reopening…');
  void store.load().then((saved) => {
    if (saved !== null && saved.name === src.name) {
      openBytes(saved.name, saved.bytes, src);
      return;
    }
    status('', '');
    waitingFor(src.name);
  });
}

addEventListener('hashchange', route);

// The signature column is a fraction of the window, so its capacity changes
// with the window. Rebuild only when the measured width actually crosses into
// a different character count -- a resize drag fires continuously, and
// rebuilding 2896 rows per frame is not affordable.
let resizeTimer = 0;
addEventListener('resize', () => {
  const L = LOADED;
  if (L === null || CUR !== null) return;
  clearTimeout(resizeTimer);
  resizeTimer = setTimeout(() => {
    if (sigCapacity() !== SIG_CAP) { buildList(L); applyFilter(); }
  }, 100) as unknown as number;
});

$('search').addEventListener('input', applyFilter);

$('onlybad').addEventListener('click', () => {
  const L = LOADED;
  if (L === null) return;
  ONLY_BAD = !ONLY_BAD;
  paintBad(L);
  applyFilter();
});

($('file') as HTMLInputElement).addEventListener('change', (e) => {
  const f = (e.target as HTMLInputElement).files?.[0];
  if (f !== undefined) {
    void f.arrayBuffer().then((b) => openBytes(f.name, b, { kind: 'file', name: f.name }));
  }
});

for (const b of document.querySelectorAll<HTMLElement>('[data-example]')) {
  b.addEventListener('click', () => openUrl(b.dataset['example']!));
}

const drop = $('drop');
for (const ev of ['dragenter', 'dragover']) {
  drop.addEventListener(ev, (e) => { e.preventDefault(); drop.classList.add('over'); });
}
for (const ev of ['dragleave', 'drop']) {
  drop.addEventListener(ev, () => drop.classList.remove('over'));
}
drop.addEventListener('drop', (e) => {
  e.preventDefault();
  const f = (e as DragEvent).dataTransfer?.files[0];
  if (f !== undefined) {
    void f.arrayBuffer().then((b) => openBytes(f.name, b, { kind: 'file', name: f.name }));
  }
});

$('reload').addEventListener('click', () => {
  // Forget the kept file too, or the picker would lie about what a refresh
  // brings back.
  void store.clear();
  try { localStorage.removeItem(SRC_KEY); } catch { /* convenience only */ }
  LOADED = null;
  paintFailures(null);
  ($('home') as HTMLAnchorElement).href = '#';
  $('drop').textContent = 'drop a file here';
  // The address named the file being forgotten, so it has to go too. Replaced
  // rather than pushed: this discards state, and an entry pointing back at a
  // file that is no longer there is not somewhere to return to. `route` then
  // draws the selector, which is what `#` now means -- and is why none of the
  // panel switching is repeated here.
  history.replaceState(null, '', location.pathname + location.search);
  route();
});

// ---- theme ----------------------------------------------------------------

type Theme = 'light' | 'dark';
const THEME_KEY = 'mmb-theme';

/**
 * The scheme in force: whatever the toggle pinned, or the system's if it has
 * pinned nothing. The unpinned case is the *absence* of a stamp rather than a
 * stored copy of the system value -- so a machine that switches at sunset
 * follows it, instead of freezing whatever it was on first visit.
 */
function currentTheme(): Theme {
  const t = document.documentElement.dataset['theme'];
  if (t === 'light' || t === 'dark') return t;
  return matchMedia('(prefers-color-scheme: light)').matches ? 'light' : 'dark';
}

function paintTheme(): void {
  // Only the label: the icon is drawn in the markup and is the same in both
  // schemes -- one icon says "appearance", and the state is already being
  // reported by the entire page. Writing the glyph here would replace the
  // markup's `<svg>`, which is how this button lost its icon once already.
  const to = currentTheme() === 'dark' ? 'light' : 'dark';
  $('theme').title = `switch to ${to} (t)`;
}

function setTheme(t: Theme): void {
  document.documentElement.dataset['theme'] = t;
  try { localStorage.setItem(THEME_KEY, t); } catch { /* convenience only */ }
  paintTheme();
}

{
  const saved = (() => {
    try { return localStorage.getItem(THEME_KEY); } catch { return null; }
  })();
  if (saved === 'light' || saved === 'dark') document.documentElement.dataset['theme'] = saved;
  paintTheme();
  // Repaint on a system change, which only shows while nothing is pinned --
  // the glyph would otherwise go on offering the scheme already in force.
  matchMedia('(prefers-color-scheme: light)').addEventListener('change', paintTheme);
}

$('theme').addEventListener('click', () => {
  setTheme(currentTheme() === 'dark' ? 'light' : 'dark');
});

$('proof').addEventListener('click', () => {
  const L = LOADED;
  if (L !== null) toggleProof(L, !ONLY_PROOF);
});

for (const id of ['status', 'failures']) {
  $(id).addEventListener('click', () => {
    const L = LOADED;
    if (L !== null) openErrors(L);
  });
}
errEl().querySelector('.close')?.addEventListener('click', closeErrors);
errEl().addEventListener('click', (e) => { if (e.target === errEl()) closeErrors(); });

$('help').addEventListener('click', openHelp);
helpEl().querySelector('.close')?.addEventListener('click', closeHelp);
helpEl().addEventListener('click', (e) => { if (e.target === helpEl()) closeHelp(); });

/** The first or last *visible* step, so nothing offers to go somewhere unlisted. */
function goEdge(L: Loaded, last: boolean): void {
  if (CUR === null) return;
  if (UNIFY !== null) { setUstep(L, last ? UNIFY.trace.steps.length - 1 : 0); return; }
  const vis = CUR.r.steps.filter((s) => !ONLY_PROOF || isProofStep(CUR!.r, s));
  const edge = last ? vis[vis.length - 1] : vis[0];
  if (edge !== undefined) go(L, edge.i);
}

addEventListener('keydown', (e) => {
  // Never swallow a browser shortcut. Alt+←/→ is Back/Forward, and matching on
  // `ArrowLeft` would both step the proof and suppress the navigation. `Shift`
  // is not excluded: `G` needs it.
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const t = e.target as HTMLElement;
  const typing = t.tagName === 'INPUT' && (t as HTMLInputElement).type !== 'checkbox';
  // Help works everywhere, even on the list, and captures the keyboard while
  // open so the navigation behind it does nothing until dismissed.
  if (helpOpen()) {
    if (e.key === 'Escape' || e.key === '?') { e.preventDefault(); closeHelp(); }
    return;
  }
  // Same rule as the help: while a modal is up it owns the keyboard, so the
  // navigation behind it does nothing until it is dismissed.
  if (errorsOpen()) {
    if (e.key === 'Escape') { e.preventDefault(); closeErrors(); }
    return;
  }
  if (e.key === '?' && !typing) { e.preventDefault(); openHelp(); return; }
  const L = LOADED;
  if (L === null) return;
  // `typing` first: the filter box is an input, and `o` occurs in plenty of
  // declaration names, so an unguarded `o` threw away the open file mid-search.
  // It is not behind `CUR` -- opening another file works from the list too.
  if (e.key === 'o' && !typing) { e.preventDefault(); $('reload').click(); return; }
  if (e.key === 'r' && !typing) { e.preventDefault(); reread(); return; }
  if (e.key === 't' && !typing) {
    e.preventDefault();
    setTheme(currentTheme() === 'dark' ? 'light' : 'dark');
    return;
  }
  if (CUR === null || typing) return;

  let d: number | null = null;
  // The listing is a tree, so the keys read as one: up and down walk it,
  // through a step's unify sub-steps and out the other side; left and right
  // enter and leave.
  switch (e.key) {
    case 'ArrowUp': case 'k': d = -1; break;
    case 'ArrowDown': case 'j': d = 1; break;
    case 'ArrowRight': case 'l':
      e.preventDefault();
      if (UNIFY === null) toggleUnify(L);
      return;
    case 'ArrowLeft': case 'h':
      e.preventDefault();
      if (UNIFY !== null) toggleUnify(L);
      return;
    case 'PageUp': d = -10; break;
    case 'PageDown': d = 10; break;
    case 'Home': case 'g': e.preventDefault(); goEdge(L, false); return;
    case 'End': case 'G': e.preventDefault(); goEdge(L, true); return;
    case 'p': e.preventDefault(); toggleProof(L, !ONLY_PROOF); return;
    case 'u': e.preventDefault(); toggleUnify(L); return;
    // Esc leaves the unifier first, then the declaration.
    case 'Escape':
      e.preventDefault();
      if (UNIFY !== null) toggleUnify(L); else location.hash = listUrl(L.name);
      return;
    default: return;
  }
  e.preventDefault();
  moveRow(L, d);
});

$('list').classList.add('off');
route();
restore();
