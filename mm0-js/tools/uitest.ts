// A smoke test of the explorer page, in a real browser.
//
// The alternative, where no browser is available, is to extract the render
// functions and run them against canned data under a DOM shim. That finds real
// bugs but leaves the actual page unexercised, and the bug that got through
// last time it was done that way was in `renderDecl` -- the one function the
// shim had stopped covering.
//
// Here the page is loaded, driven and inspected as a user would meet it. Any
// console error or unhandled rejection fails the run: an exception thrown
// while rendering leaves a half-built pane rather than a blank page, so it is
// easy to miss by looking.
//
// Usage: node dist/tools/uitest.js [url]

import { existsSync } from 'node:fs';
import { chromium } from 'playwright';

const url = process.argv[2] ?? 'http://localhost:8731/index.html';

let failures = 0;
function check(name: string, actual: unknown, expected: unknown): void {
  const a = JSON.stringify(actual), e = JSON.stringify(expected);
  if (a === e) console.log(`  ok   ${name}`);
  else {
    console.log(`  FAIL ${name}\n         got ${a}\n    expected ${e}`);
    failures++;
  }
}

const browser = await chromium.launch();
const page = await browser.newPage();

/**
 * Navigate the app's hash router, reliably.
 *
 * `page.goto` to a URL that differs from the current one only in the fragment
 * is a same-document navigation, and Chromium may treat it as already-there:
 * no `hashchange` fires, so the app's synchronous `route()` never runs, the
 * view never updates, and the following `waitForSelector` waits out its whole
 * timeout. It is not rare in this suite because the app `replaceState`s the
 * step index onto the hash after rendering, so a `goto` to a declaration at the
 * step it is already showing matches the current URL exactly -- a certain
 * no-op. Setting the hash in-page and dispatching `hashchange` ourselves runs
 * `route()` every time; `route()` is idempotent, so the extra run when the
 * browser also fires its own is harmless.
 */
const nav = async (hash: string): Promise<void> => {
  await page.evaluate((h) => {
    // A changed fragment fires `hashchange` on its own; an unchanged one never
    // will, so force it. Exactly one route() runs either way.
    if (location.hash === h) dispatchEvent(new HashChangeEvent('hashchange'));
    else location.hash = h;
  }, hash);
};

const problems: string[] = [];
page.on('console', (m) => {
  if (m.type() === 'error') problems.push(`console: ${m.text()}`);
});
page.on('pageerror', (e) => problems.push(`pageerror: ${e.message}`));

try {
  console.log('loading');
  await page.goto(url, { waitUntil: 'load' });
  check('the landing state is shown', await page.isVisible('#open'), true);
  check('no declaration list yet', await page.isVisible('#decls tr'), false);

  console.log('opening peano.mmb');
  await page.click('[data-example="test/peano.mmb"]');
  await page.waitForSelector('#decls tr', { timeout: 60000 });
  // The badge on both views; the wording is one hover away. Spelled out it
  // repeated the declaration count the crumb already gives.
  check('the file status is a badge', await page.textContent('#status'), '✓');
  // 2896, not 2881: sorts and plain terms are verified too, they just have no
  // proof stream to run. Reporting the smaller number read as a discrepancy
  // against the crumb's total.
  // The claim is that this is a fast verifier, so the time is stated rather
  // than left in a tooltip -- and the tooltip carries the work it covers,
  // which is what makes the number mean anything.
  check('the time is shown',
    /^\d+ ms$/.test(await page.textContent('#timing') ?? ''), true);
  {
    const title = await page.getAttribute('#status', 'title') ?? '';
    check('the tooltip gives the size', /877 kB/.test(title), true);
    check('the count', /2,896 declarations verified/.test(title), true);
    check('the time', /in \d+ ms/.test(title), true);
    check('and the work it covers',
      /244,778 proof steps, 303,904 unify steps/.test(title), true);
  }
  // The header aligns text on baselines, which puts a label a pixel above the
  // centre line of the 24px controls it sits beside. Everything in the
  // right-hand group shares one centre.
  {
    const mid = await page.evaluate(() =>
      ['status', 'timing', 'proof', 'theme', 'help', 'reload'].map((id) => {
        const r = document.getElementById(id)!.getBoundingClientRect();
        return (r.top + r.bottom) / 2;
      }));
    check('the status, timing and controls share a centre line',
      Math.max(...mid) - Math.min(...mid) < 0.5, true);
  }

  // The size belongs beside the file's name.
  check('the crumb gives the size',
    /^peano\.mmb — 877 kB — 2896 declarations/.test(
      await page.textContent('#crumb') ?? ''), true);
  check('lists every declaration', await page.locator('#decls tr').count(), 2896);
  // On the list the crumb names the file and says what it holds.
  check('the crumb summarises the file',
    /2642 theorem/.test(await page.textContent('#crumb') ?? ''), true);
  // Nothing to step through here, so no step controls.
  check('the list has no navigation', await page.textContent('#nav'), '');

  console.log('filtering');
  await page.fill('#search', 'ax_mp');
  const shown = await page.locator('#decls tr:visible').count();
  check('filter narrows the list', shown < 20 && shown > 0, true);
  await page.fill('#search', '');

  {
    // An id is matched whole and with its case kept: `T1` and `t1` are
    // different declarations, theorem 1 and term 1, so folding case would
    // conflate them and a substring match would bury the row asked for by
    // number under every `T1xx`. Names still match loosely.
    const ids = async (q: string): Promise<string[]> => {
      await page.fill('#search', q);
      await page.waitForTimeout(120);
      return page.evaluate(() => [...document.querySelectorAll('#decls tr')]
        .filter((t) => !t.classList.contains('hidden'))
        .map((t) => (t as HTMLElement).dataset['id'] ?? ''));
    };
    const upper = await ids('T1');
    check('an exact id shows its declaration', upper.includes('T1'), true);
    check('and the term of the same number is not it', upper.includes('t1'), false);
    const lower = await ids('t1');
    check('the other case shows the other one', lower.includes('t1'), true);
    check('and not the theorem', lower.includes('T1'), false);
    // Both still carry the name matches, which is the ordinary behaviour.
    check('names still match loosely', upper.includes('T39'), true);
    check('an id that names nothing shows nothing', await ids('T99999'), []);
    await page.fill('#search', '');
  }

  // Typed with real key events, not `fill`: the shortcut handler is on
  // `keydown`, and `o` used to be dispatched before the guard that ignores
  // keys aimed at an input -- so filtering for anything with an `o` in it
  // threw the file away and returned to the picker mid-search.
  await page.click('#search');
  await page.keyboard.type('not');
  check('typing a name with an o in it keeps the file',
    await page.isVisible('#open'), false);
  check('and keeps filtering', await page.inputValue('#search'), 'not');
  check('against a list that is still there',
    await page.locator('#decls tr:visible').count() > 0, true);
  await page.fill('#search', '');

  console.log('the list is drawn as it is looked at');
  {
    // A coloured signature is twenty-odd elements and a library is thousands
    // of rows, of which a screenful is forty. Drawing them all up front cost
    // more than verifying the file does.
    const drawn = (): Promise<number> => page.evaluate(() =>
      [...document.querySelectorAll('#decls td.decl')]
        .filter((e) => e.querySelector('.fence, .punct, .var, .bvar') !== null).length);
    const first = await drawn();
    check('only the rows on screen are drawn', first > 0 && first < 200, true);
    await page.evaluate(() => { document.getElementById('listbody')!.scrollTop = 20000; });
    await page.waitForFunction(
      (n) => [...document.querySelectorAll('#decls td.decl')]
        .filter((e) => e.querySelector('.fence, .punct, .var, .bvar') !== null).length > n,
      first);
    check('and more as it is scrolled', await drawn() > first, true);
    await page.evaluate(() => { document.getElementById('listbody')!.scrollTop = 0; });
    await page.waitForTimeout(150);
  }

  console.log('the search box stays put');
  {
    // Filtering is how you reach a declaration among thousands, so the control
    // must not scroll away: the rows scroll under it, not with it.
    const at = (): Promise<{ search: number; head: number }> => page.evaluate(() => ({
      search: document.getElementById('search')!.getBoundingClientRect().top,
      head: document.querySelector('#list th')!.getBoundingClientRect().top,
    }));
    const before = await at();
    await page.evaluate(() => { document.getElementById('listbody')!.scrollTop = 6000; });
    await page.waitForFunction(() => document.getElementById('listbody')!.scrollTop > 0);
    check('the rows scrolled',
      await page.evaluate(() => document.getElementById('listbody')!.scrollTop) > 0, true);
    const after = await at();
    check('the search box did not', after.search, before.search);
    // The heading row is sticky, and now measured against the part that
    // actually scrolls rather than the whole panel.
    check('nor the column headings', after.head, before.head);
    await page.evaluate(() => { document.getElementById('listbody')!.scrollTop = 0; });
  }

  console.log('the declaration column gives up its parts in order');
  {
    // Narrow enough that the full form cannot fit, so the disclosure actually
    // engages. End-truncation eats the conclusion, which is what the row is
    // read for; the affordable parts go first and the conclusion survives.
    await page.setViewportSize({ width: 640, height: 800 });
    // Wait for rows to be *drawn*, not for a guess at how long that takes: the
    // resize rebuilds the list and the observer draws on the next frame, which
    // a headless browser produces when it feels like it.
    await page.waitForFunction(() =>
      [...document.querySelectorAll('#decls td.decl')]
        .some((e) => e.querySelector('.fence, .punct') !== null));
    // Only the rows that have been drawn carry a signature at all.
    const rows = await page.evaluate(() =>
      [...document.querySelectorAll('#decls td.decl')]
        .filter((e) => e.querySelector('.fence, .punct') !== null)
        .map((e) => ({ shown: e.textContent ?? '', full: (e as HTMLElement).title })));
    check('rows were drawn', rows.length > 0, true);
    check('every row keeps the whole declaration in its tooltip',
      rows.filter((r) => r.full === '').length, 0);
    const shortened = rows.filter((r) => r.shown !== r.full);
    check('some are shortened', shortened.length > 0, true);
    // What went is the binders: the kept part restarts at the `:`.
    check('and they drop the binders, not the conclusion',
      shortened.filter((r) => !/[:]/.test(r.shown)), []);
    check('the conclusion survives',
      shortened.filter((r) => r.shown.includes('$') && !r.shown.trimEnd().endsWith('$')), []);
    await page.setViewportSize({ width: 1280, height: 800 });
    await page.waitForFunction(() =>
      [...document.querySelectorAll('#decls td.decl')]
        .some((e) => e.querySelector('.fence, .punct') !== null));
  }

  console.log('a sort carries its modifiers');
  {
    // `strict provable sort wff`, as MM0 writes it: the modifiers are part of
    // the keyword the way `pub` and `local` are on the others, so they go
    // before it rather than being dropped.
    await nav(`#/peano.mmb/sort/wff`);
    await page.waitForFunction(() =>
      document.getElementById('detail')!.classList.contains('on'));
    await page.waitForTimeout(150);
    check('the statement bar spells the sort out',
      await page.textContent('#stmtbar'), 'strict provable sort wff');
    // Still coloured as a sort, however many modifiers it carries.
    check('and it is still a sort',
      await page.getAttribute('#stmtbar .kind', 'class'), 'kind k-sort');
    await nav(`#/peano.mmb/sort/nat`);
    await page.waitForTimeout(150);
    check('one with none reads as before',
      await page.textContent('#stmtbar'), 'sort nat');
    await nav(`#/peano.mmb`);
    await page.waitForSelector('#decls tr');
    check('and the list says the same',
      (await page.locator('#decls tr').first().textContent())?.trim(),
      's0strict provable sort wff');

    // A sort has no proof and so no machine state: three empty panes saying
    // nothing. What it *is* is its four modifiers.
    await nav(`#/peano.mmb/sort/wff`);
    await page.waitForFunction(() =>
      document.getElementById('right')!.classList.contains('sort'));
    await page.waitForTimeout(150);
    check('the machine panes are gone', await page.evaluate(() =>
      ['p-stack', 'p-heap', 'p-hyps']
        .filter((i) => document.getElementById(i)!.offsetParent !== null)), []);
    // All four are listed whether the sort has them or not: which it lacks is
    // as much of the declaration as which it has.
    // The identity line every other callout ends with: which declaration this
    // is, and that it verified. `declHead` read the name from the theorem
    // table for anything that was not a term, so a sort took the name of
    // whichever theorem shared its number -- `s0 sort ax_1` for `wff`.
    check('the callout still says which declaration it is',
      await page.textContent('#callout .po-decl'), 's0 sort wff');
    check('and that it verified',
      await page.textContent('#callout .po-go'), '0 steps — proved');
    check('all four modifiers are listed', await page.evaluate(() =>
      [...document.querySelectorAll('#callout .mods .kw')].map((e) => e.textContent)),
    ['pure', 'strict', 'provable', 'free']);
    check('with the ones it lacks struck through', await page.evaluate(() =>
      [...document.querySelectorAll('#callout .mods .kw')]
        .filter((e) => e.classList.contains('off')).map((e) => e.textContent)),
    ['pure', 'free']);
    check('and struck through means struck through', await page.evaluate(() =>
      getComputedStyle(document.querySelector('#callout .mods .kw.off')!).textDecorationLine),
    'line-through');
    // The gloss says what having it means, and what lacking it means.
    check('a modifier it has is glossed as such',
      await page.locator('#callout .mods .gloss').nth(1).textContent(),
      'has no binders: no bound or dummy variable may have it, '
      + 'and it may not appear as a dependency');
    check('and one it lacks the other way round',
      await page.locator('#callout .mods .gloss').nth(0).textContent(),
      'terms may target it');
    // A declaration with a proof keeps its panes.
    await nav(`#/peano.mmb/thm/a1i/9`);
    await page.waitForSelector('#steps .step');
    check('a theorem still has its panes', await page.evaluate(() =>
      ['p-stack', 'p-heap', 'p-hyps']
        .filter((i) => document.getElementById(i)!.offsetParent !== null).length), 3);
    // Back to the list, which is where the next block starts from.
    await nav(`#/peano.mmb`);
    await page.waitForSelector('#decls tr');
  }

  console.log('the id column disambiguates the classes');
  {
    // A term `12` and a theorem `12` both exist, so the bare number named two
    // different declarations.
    const ids = await page.locator('#decls tr .num').allTextContents();
    check('every id carries its class prefix',
      ids.filter((i) => !/^[stT]\d+$/.test(i)).length, 0);
    check('and the classes are all present',
      [...new Set(ids.map((i) => i[0]))].sort(), ['T', 's', 't']);
  }

  console.log('a row is clickable across its width');
  {
    // The steps cell is nowhere near the name link, so reaching a declaration
    // from it means the row itself is the target.
    const want = await page.locator('#decls tr').first().locator('a').getAttribute('href');
    await page.locator('#decls tr').first().locator('.steps').click();
    await page.waitForFunction(() => document.getElementById('detail')!.classList.contains('on'));
    check('clicking the signature cell opens the declaration',
      (await page.evaluate(() => location.hash)).startsWith(`${want}/`), true);
    await nav(`#/peano.mmb`);
    await page.waitForSelector('#decls tr');
  }

  console.log('opening a declaration');
  await nav(`#/peano.mmb/thm/a1i`);
  await page.waitForSelector('#steps .step');
  // The crumb is structured, not a label: an id tag, the kind in its own
  // colour, and the name in bold -- the same identity line the callout uses.
  check('the crumb carries the id tag',
    await page.textContent('#crumb .idtag'), 'T4');
  check('and the kind, coloured by class',
    await page.getAttribute('#crumb .kind', 'class'), 'kind k-theorem');
  check('and the name in bold', await page.textContent('#crumb b'), 'a1i');
  // The statement bar spells the declaration as the source writes it, since
  // the kind and name are part of the signature rather than labels on it.
  check('the statement bar names it too',
    (await page.textContent('#stmtbar'))?.startsWith('theorem a1i'), true);
  // `TermSave` is `Term t; Save` welded into one opcode, and the row is spelled
  // as the two commands it is. Labelling the op itself `TermSave` said `Save`
  // twice and asked for an `.op-TermSave` colour that no rule defines, so the
  // row fell back to plain foreground and stopped reading as a `Term`.
  {
    const ops = await page.locator('#steps .step .op').allTextContents();
    check('no step is labelled TermSave', ops.filter((o) => /Save$/.test(o) && o !== 'Save'), []);
    check('the save is written as a separate op', ops.filter((o) => o === 'Save').length > 0, true);
    // Checked as "no op asks for a colour that does not exist" rather than
    // "some op is blue": a1i has unsaved `Term` steps too, so the latter
    // passes even when every *saved* one has fallen back to plain foreground.
    const classes = await page.locator('#steps .step .op').evaluateAll(
      (es) => es.map((e) => e.className));
    check('no op asks for an undefined colour',
      classes.filter((c) => /op-\w+Save/.test(c)), []);
  }

  console.log('the statement is styled by part');
  // `ax_gen` is `{x: nat} (p: wff x): $ p $ > $ A. x p $` -- a bound binder, a
  // dependent regular binder, two sorts, and the `$` fences.
  await nav(`#/peano.mmb/thm/ax_gen/0`);
  await page.waitForSelector('#stmtbar .fence');
  check('the whole statement', (await page.textContent('#stmtbar')),
    'axiom ax_gen {x: nat} (p: wff x): $ p $ > $ A. x p $');
  // Each part is its own element: the `$` fences are structure and subdued,
  // the syntax around them is not, and a sort is a declaration so it links.
  check('the $ fences are marked',
    await page.locator('#stmtbar .fence').allTextContents(), ['$', '$', '$', '$']);
  check('the syntax punctuation is marked',
    await page.locator('#stmtbar .punct').allTextContents(),
    ['{', ':', '}', '(', ':', ')', ':', '>']);
  // `{x: nat} (p: wff x)`: the bound `x` and the free `p` are drawn apart, in
  // the binders, in the dependency list and in the formulas alike.
  check('the free variables are marked',
    await page.locator('#stmtbar .var').allTextContents(), ['p', 'p', 'p']);
  check('and the bound ones separately',
    await page.locator('#stmtbar .bvar').allTextContents(), ['x', 'x', 'x']);
  check('the sorts are marked',
    await page.locator('#stmtbar a.sortname').allTextContents(), ['nat', 'wff']);
  check('and a sort links to its declaration',
    await page.getAttribute('#stmtbar a.sortname', 'href'), '#/peano.mmb/sort/nat');
  await page.click('#stmtbar a.sortname');
  // The link itself carries no step, but the router normalises the address to
  // the step it is actually showing -- so wait for that, not merely for the
  // hash to change, or the URL gets read in between the two.
  await page.waitForFunction(() => location.hash === '#/peano.mmb/sort/nat/0');
  check('following one opens the sort', new URL(page.url()).hash, '#/peano.mmb/sort/nat/0');
  await nav(`#/peano.mmb/thm/a1i`);
  await page.waitForSelector('#steps .step');
  check('16 steps are listed', await page.locator('#steps .step').count(), 16);
  check('the stack starts empty', (await page.textContent('#b-stack'))?.trim(), 'empty');
  check('the heap starts with the binders',
    await page.locator('#b-heap .slot').count(), 2);

  console.log('stepping');
  // The whole point of the tool: move and watch the machine state change.
  await page.keyboard.press('j');
  await page.waitForFunction(() => location.hash.endsWith('/1'));
  check('stepping advances the hash', /\/1$/.test(new URL(page.url()).hash), true);
  check('and the stack now has an element',
    await page.locator('#b-stack .slot').count(), 1);

  await nav(`#/peano.mmb/thm/a1i/15`);
  await page.waitForSelector('#b-stack .slot');
  check('the final state has one element',
    await page.locator('#b-stack .slot').count(), 1);
  check('and it is a proof',
    (await page.textContent('#b-stack .slot .turnstile'))?.trim(), '⊢');
  const concl = (await page.textContent('#b-stack .slot .val')) ?? '';
  // a1i proves `b -> a -> b` from `b`; notation, not s-exprs.
  check('rendered with notation', /->/.test(concl) && !/\(im /.test(concl), true);

  console.log('sorts are clickable everywhere');
  {
    await nav(`#/peano.mmb/thm/a1i/9`);
    await page.waitForSelector('#b-heap .slot');
    // An expression's `: wff` tag names a declaration, so it links like any
    // other name the view shows.
    check('the sort tag on a heap slot links',
      await page.locator('#b-heap .sortann a.sortname').count(), 3);
    check('and points at the sort',
      await page.getAttribute('#b-heap .sortann a.sortname', 'href'), '#/peano.mmb/sort/wff');
    check('as does one on the stack',
      await page.locator('#b-stack .sortann a.sortname').count() > 0, true);

    // `Dummy s` and `UDummy s` name a sort too -- one that did nothing while
    // every other sort in the view linked would just be the next surprise.
    await nav(`#/peano.mmb/term/sb/0`);
    await page.waitForSelector('#steps .step');
    const dummy = page.locator('#steps .step', { hasText: 'Dummy' }).first();
    check('a Dummy command links its sort',
      await dummy.locator('a.sortname').count(), 1);
    await nav(`#/peano.mmb/thm/a1i/9`);
    await page.waitForSelector('#steps .step');
  }

  console.log('the three kinds of variable are told apart');
  {
    // `sb` has one of each: `(a: nat) {x: nat} (p: wff x) {.y: nat}`. The
    // distinction is what the binding conditions are about, so it has to be
    // visible in the expression, not only in the binder list.
    await nav(`#/peano.mmb/term/sb/6`);
    await page.waitForSelector('#steps .step');
    // No helper function inside `evaluate`: the transpiler adds a `__name`
    // shim for named function expressions, which does not exist in the page.
    const kinds = await page.evaluate(() => ({
      free: [...document.querySelectorAll('#stmtbar .var')].map((e) => e.textContent ?? ''),
      bound: [...document.querySelectorAll('#stmtbar .bvar:not(.dummy)')]
        .map((e) => e.textContent ?? ''),
      dummy: [...document.querySelectorAll('#stmtbar .dummy')].map((e) => e.textContent ?? ''),
    }));
    check('free variables', [...new Set(kinds.free)].sort(), ['a', 'p']);
    check('bound variables', [...new Set(kinds.bound)].sort(), ['x']);
    check('and dummies, named with their dot in the binder',
      [...new Set(kinds.dummy)].sort(), ['.y', 'y']);
    // A dummy is a bound variable that nothing outside can name -- a narrowing
    // of the same idea, so it is the same colour, set in italic.
    const style = await page.evaluate(() => {
      const d = getComputedStyle(document.querySelector('#stmtbar .dummy')!);
      const b = getComputedStyle(document.querySelector('#stmtbar .bvar:not(.dummy)')!);
      const f = getComputedStyle(document.querySelector('#stmtbar .var')!);
      return {
        sameColour: d.color === b.color,
        differsFromFree: b.color !== f.color,
        freeIsColoured: f.color !== getComputedStyle(document.body).color,
        italic: d.fontStyle,
        upright: b.fontStyle,
      };
    });
    check('a dummy is coloured as the bound variable it is', style.sameColour, true);
    check('and bound is not free', style.differsFromFree, true);
    // Each kind is drawn as itself. A free variable had been left in the
    // foreground colour, which made it indistinguishable from ordinary text --
    // the thing the colouring is for.
    check('and free is not ordinary text', style.freeIsColoured, true);
    check('the dummy is italic', style.italic, 'italic');
    check('the bound one is not', style.upright, 'normal');
    // The callout names variables schematically -- `consumes x · p` -- with no
    // expression to render, so they have to be coloured from the declaration's
    // binders directly. This was the one place a bound variable looked free.
    await nav(`#/peano.mmb/thm/alnex/3`);
    await page.waitForSelector('#steps .step');
    const eff = await page.evaluate(() => ({
      bound: [...document.querySelectorAll('#callout .eff .bvar')]
        .map((e) => e.textContent ?? ''),
      free: [...document.querySelectorAll('#callout .eff .var')].map((e) => e.textContent ?? ''),
    }));
    check('the callout colours the bound ones', eff.bound.includes('x'), true);
    check('and leaves the free ones alone', eff.free.includes('p'), true);
    // A signature composes onto a name, so it carries its own leading space --
    // trimming it for the list column ran the two together as `al{x: nat}`.
    check('the identity line separates the name from the signature',
      (await page.textContent('#callout .po-decl'))?.includes('al {x: nat}'), true);

    // Put back the declaration the next block reads from.
    await nav(`#/peano.mmb/thm/a1i/9`);
    await page.waitForSelector('#steps .step');
  }

  console.log('the two-behaviour commands name which one ran');
  {
    // `Ref` and `Sorry` are each one opcode with two rules in the spec, and
    // which ran is decided by what was on the stack -- so the listing says
    // which, rather than leaving `Ref 8` to mean either.
    await nav(`#/peano.mmb/thm/nfex1/31`);
    await page.waitForSelector('#steps .step.cur');
    check('a Ref that discharged is a ConvRef',
      (await page.locator('#steps .step.cur').textContent())?.trim(), '31ConvRef 8');
    check('and is coloured as a conversion',
      await page.evaluate(() => {
        const e = document.querySelector('#steps .step.cur .op')!;
        const probe = document.createElement('div');
        probe.style.color = 'var(--conv)';
        document.body.append(probe);
        const c = getComputedStyle(probe).color;
        probe.remove();
        return getComputedStyle(e).color === c;
      }), true);
    check('and the description follows it',
      /discharging the obligation/.test(await page.textContent('#callout') ?? ''), true);
    // Both ends concrete, as they are for the copying form: the obligation
    // being discharged and the proof that discharges it. Left schematic, the
    // reader is given a slot number and two placeholders to look up.
    check('it names the obligation it discharges',
      (await page.textContent('#callout .eff.takes'))?.includes('≟'), true);
    check('and what the slot actually holds',
      /heap slot 8 holds .*≡/.test(await page.textContent('#callout .po-note') ?? ''), true);
    check('with neither left as a placeholder',
      /e1|e2/.test(await page.textContent('#callout') ?? ''), false);
    await nav(`#/peano.mmb/thm/a1i/9`);
    await page.waitForSelector('#steps .step');
  }

  console.log('drill-down');
  const link = page.locator('#b-stack .slot .val a').first();
  check('term names in expressions are links', await link.count(), 1);
  await link.click();
  await page.waitForSelector('#steps');
  check('following one opens a term',
    /^#\/peano\.mmb\/term\//.test(new URL(page.url()).hash), true);

  console.log('proof-only mode');
  await nav(`#/peano.mmb/thm/a1i/0`);
  await page.waitForSelector('#steps .step');
  await page.keyboard.press('p');
  await page.waitForFunction(() => document.querySelectorAll('#steps .step').length === 4);
  check('collapses to the four inferences',
    await page.locator('#steps .step').count(), 4);
  await page.keyboard.press('p');

  console.log('header controls');
  await nav(`#/peano.mmb/thm/a1i/9`);
  await page.waitForSelector('#steps .step');
  // The nav is buttons, not a bare counter: a mouse user needs the keyboard's
  // reach, and a disabled button is how an edge is announced.
  // ⏮ -10 ↑ ↓ +10 ⏭. The proof-only toggle is not among them: it is a session
  // setting and lives in the corner cluster, which does not get rebuilt.
  check('nav has the full control set',
    await page.locator('#nav button').count(), 6);
  check('and the step counter', /step 9 \/ 15/.test(await page.textContent('#nav') ?? ''), true);
  await nav(`#/peano.mmb/thm/a1i/0`);
  await page.waitForSelector('#steps .step');
  check('at the first step the back buttons are disabled',
    await page.locator('#nav button:disabled').count(), 3);

  // The header is one line, and the crumb is the only item on it that can give
  // way -- so the controls must leave it room for the declaration's name.
  await nav(`#/peano.mmb/thm/grecaux2eqd/9`);
  await page.waitForSelector('#steps .step');
  check('the crumb is not truncated',
    await page.locator('#crumb').evaluate((e) => e.scrollWidth <= e.clientWidth), true);
  // The file's status is ambient, so it shrinks to a mark on a declaration page
  // and keeps its wording in the tooltip.
  check('the status is a mark here', await page.textContent('#status'), '✓');
  // The time is a fact about the file, so it folds into the tooltip here --
  // the crumb needs the room for the declaration's name.
  check('and the time gives way to the crumb', await page.textContent('#timing'), '');
  check('and the nav is back for a declaration',
    await page.locator('#nav button').count() > 0, true);
  check('with the wording kept',
    (await page.getAttribute('#status', 'title'))?.includes('verified'), true);
  // A badge rather than a bare glyph: `✓` in the body's monospace face is
  // sized for a text column, not to be read at a glance.
  check('drawn as a badge',
    (await page.getAttribute('#status', 'class'))?.includes('compact'), true);
  {
    const bb = (await page.locator('#status').boundingBox())!;
    check('square enough to be a circle', Math.round(bb.width) === Math.round(bb.height), true);
    check('and big enough to see', Math.round(bb.width) >= 16, true);
  }

  console.log('leaving a declaration clears the navigation');
  {
    await nav(`#/peano.mmb/thm/a1i/9`);
    await page.waitForSelector('#steps .step');
    check('a declaration has controls', await page.locator('#nav button').count(), 6);
    await nav(`#/peano.mmb`);
    await page.waitForFunction(() => document.getElementById('nav')!.textContent === '');
    // Otherwise the list offers to step through something you have left.
    check('going back to the list clears them', await page.textContent('#nav'), '');
    await nav(`#/peano.mmb/thm/grecaux2eqd/9`);
    await page.waitForSelector('#steps .step');
  }

  console.log('the proof-only toggle');
  {
    const tog = page.locator('#proof');
    check('is a turnstile', await tog.locator('svg path').count(), 1);
    check('and starts off', await tog.getAttribute('class'), 'tog');
    // It is a session setting, so it sits in the corner cluster rather than in
    // `#nav`, which is rebuilt per step and emptied on the list.
    check('it is not part of the step navigation',
      await page.locator('#nav #proof').count(), 0);
    const before = (await tog.boundingBox())!.width;
    await page.mouse.move(0, 300);
    await page.waitForTimeout(60);
    const offPaint = await page.evaluate(() => {
      const c = getComputedStyle(document.getElementById('proof')!);
      return `${c.backgroundColor} ${c.borderTopColor} ${c.color}`;
    });
    // `--thm`, resolved through a probe rather than written out, so the check
    // survives the palette moving and covers both themes.
    const accent = await page.evaluate(() => {
      const d = document.createElement('div');
      d.style.backgroundColor = 'var(--thm)';
      document.body.append(d);
      const c = getComputedStyle(d).backgroundColor;
      d.remove();
      return c;
    });
    await tog.click();
    await page.waitForFunction(() =>
      document.getElementById('proof')!.classList.contains('on'));
    check('turns on when clicked', await tog.getAttribute('class'), 'tog on');
    // The class alone proved nothing: `.tog.on` is two classes and was losing
    // to the `#proof` rules in the corner cluster, so the state flipped in the
    // DOM while the button went on looking exactly the same. Compare what is
    // actually drawn, with the pointer away so `:hover` is not what is seen.
    await page.mouse.move(0, 300);
    await page.waitForTimeout(60);
    const paint = (): Promise<string> => page.evaluate(() => {
      const c = getComputedStyle(document.getElementById('proof')!);
      return `${c.backgroundColor} ${c.borderTopColor} ${c.color}`;
    });
    const onPaint = await paint();
    check('and looks different, not just reads different', onPaint !== offPaint, true);
    // Filled: a thin stroke changing hue is not a state you can read at 24px.
    check('the active state is filled',
      onPaint.startsWith(accent), true);
    check('and says how much it is showing',
      /showing \d+ of \d+/.test(await tog.getAttribute('title') ?? ''), true);
    // Its width must not change with its state, or toggling shifts every
    // control beside it.
    check('without changing width', (await tog.boundingBox())!.width, before);
    await page.keyboard.press('p');
    await page.waitForFunction(() =>
      !document.getElementById('proof')!.classList.contains('on'));
    check('p toggles it too', await tog.getAttribute('class'), 'tog');
    // The list has no `#nav` at all, so a toggle built with it disappeared
    // exactly where you would go to change it before opening anything.
    await nav(`#/peano.mmb`);
    await page.waitForSelector('#decls tr');
    check('and it survives leaving the declaration', await tog.isVisible(), true);
  }

  console.log('the theme toggle');
  {
    const bg = (): Promise<string> =>
      page.evaluate(() => getComputedStyle(document.body).backgroundColor);
    const theme = page.locator('#theme');
    // `light-dark()` is what makes one palette serve both, so a browser that
    // does not support it would leave every colour unresolved.
    check('the palette resolves', await bg() !== '', true);
    const first = await bg();
    const said = await theme.getAttribute('title');
    check('it is the half-filled circle',
      await theme.locator('svg circle').count(), 1);
    await theme.click();
    await page.waitForFunction((b) =>
      getComputedStyle(document.body).backgroundColor !== b, first);
    check('clicking it changes the scheme', await bg() !== first, true);
    // The icon is fixed -- the page itself reports the state -- so the
    // direction of the next click is carried by the label.
    check('and it still reads as one icon',
      await theme.locator('svg circle').count(), 1);
    check('now offering the other scheme',
      await theme.getAttribute('title') !== said, true);
    check('the choice is pinned on the root',
      ['light', 'dark'].includes(
        await page.getAttribute('html', 'data-theme') ?? ''), true);
    // Pinned means kept: the scheme is a preference, not view state.
    const pinned = await page.getAttribute('html', 'data-theme');
    await page.reload();
    await page.waitForSelector('#decls tr', { timeout: 60000 });
    check('and survives a reload', await page.getAttribute('html', 'data-theme'), pinned);
    await page.keyboard.press('t');
    await page.waitForFunction((t) =>
      document.documentElement.dataset['theme'] !== t, pinned);
    check('t toggles it too', await page.getAttribute('html', 'data-theme') !== pinned, true);
  }

  console.log('the address names the file');
  {
    await nav(`#/peano.mmb/thm/a1i/9`);
    await page.waitForSelector('#steps .step');
    check('a declaration address leads with it',
      new URL(page.url()).hash.startsWith('#/peano.mmb/'), true);
    check('and the tab says where you are',
      await page.title(), 'a1i | peano.mmb | MMB Proof Explorer');
    await nav(`#/peano.mmb`);
    await page.waitForSelector('#decls tr');
    check('the list is the file on its own', await page.title(),
      'peano.mmb | MMB Proof Explorer');
    await nav(`#`);
    await page.waitForFunction(() => document.getElementById('open')!.classList.contains('on'));
    check('and bare # is the selector', await page.isVisible('#open'), true);
    check('which is named for the tool alone',
      await page.title(), 'MMB Proof Explorer');
  }

  console.log('history separates the pages, not the steps');
  {
    // Three places, so Back walks out the way you came in -- but a hundred
    // steps of one proof is one place visited.
    await nav(`#`);
    await page.waitForFunction(() => document.getElementById('open')!.classList.contains('on'));
    await page.click('[data-example="test/peano.mmb"]');
    await page.waitForSelector('#decls tr', { timeout: 60000 });
    check('opening a file lands on its list',
      await page.evaluate(() => location.hash), '#/peano.mmb');
    // A theorem, not whichever row is first: a sort has no steps to walk.
    await page.locator('#decls a[href$="/thm/a1i"]').click();
    await page.waitForFunction(() => document.getElementById('detail')!.classList.contains('on'));
    for (const _ of [0, 1, 2]) {
      await page.keyboard.press('j');
      await page.waitForTimeout(80);
    }
    check('stepping moved within the declaration',
      /\/3$/.test(await page.evaluate(() => location.hash)), true);
    await page.goBack();
    await page.waitForFunction(() => !document.getElementById('detail')!.classList.contains('on'));
    check('Back leaves the declaration, not the steps',
      await page.evaluate(() => location.hash), '#/peano.mmb');
    await page.goBack();
    await page.waitForFunction(() => document.getElementById('open')!.classList.contains('on'));
    check('and again reaches the selector',
      await page.evaluate(() => location.hash), '');
  }

  console.log('an unknown file says so');
  {
    await nav(`#/nonexistent.mmb`);
    await page.waitForFunction(() => document.getElementById('open')!.classList.contains('on'));
    check('it falls back to the selector', await page.isVisible('#open'), true);
    check('the address does not keep pointing at it',
      await page.evaluate(() => location.hash), '');
    check('and it says which file',
      await page.textContent('#error'), 'nonexistent.mmb not found');
    // Boxed and centred, so it reads as something that happened rather than
    // as another line of chrome along the top edge.
    {
      const box = (await page.locator('#error').boundingBox())!;
      const vw = page.viewportSize()!.width;
      check('the message is centred',
        Math.abs((box.x + box.width / 2) - vw / 2) <= 1, true);
      check('and boxed rather than bare',
        await page.evaluate(() =>
          getComputedStyle(document.getElementById('error')!).borderTopWidth), '1px');
      // Compared against a probe carrying `--err`, since the computed value is
      // an rgb() triple either way -- it used to be `--axiom`, the colour
      // axioms are drawn in.
      const red = await page.evaluate(() => {
        const d = document.createElement('div');
        d.style.color = 'var(--err)';
        document.body.append(d);
        const c = getComputedStyle(d).color;
        d.remove();
        return c;
      });
      check('in the colour failures are reported in',
        await page.evaluate(() =>
          getComputedStyle(document.getElementById('error')!).color), red);
    }
    // Put the file back for what follows.
    await page.click('[data-example="test/peano.mmb"]');
    await page.waitForSelector('#decls tr', { timeout: 60000 });
  }

  console.log('help');
  check('the modal starts closed', await page.isVisible('#help-modal'), false);
  await page.keyboard.press('?');
  await page.waitForSelector('#help-modal.open');
  check('? opens it', await page.isVisible('#help-modal'), true);
  check('it documents the keys', (await page.textContent('#help-modal'))?.includes('proof steps only'), true);
  await page.keyboard.press('Escape');
  await page.waitForFunction(() => !document.getElementById('help-modal')!.classList.contains('open'));
  check('Escape closes it', await page.isVisible('#help-modal'), false);

  console.log('the unifier');
  // Step 9 is `Thm ax_1`, which invokes the unifier.
  await nav(`#/peano.mmb/thm/a1i/9`);
  await page.waitForSelector('#steps .step');
  check('steps with a unifier are flagged',
    await page.locator('#steps .step .uflag').count() > 0, true);
  check('the unify panes are hidden', await page.isVisible('#p-ustack'), false);
  await page.keyboard.press('u');
  await page.waitForSelector('#right.unify');
  check('u opens them', await page.isVisible('#p-ustack'), true);
  check('the unify stack has content',
    await page.locator('#b-ustack .slot').count() > 0, true);
  check('sub-steps splice into the listing',
    await page.locator('#steps .step.ustep').count() > 0, true);
  // The sub-step listing used to paint every op `op-conv` green. A `URef` is a
  // match against the substitution, not a conversion, and reads like the main
  // listing's `Ref`; only `UTerm` and `UHyp` carry a colour.
  check('unify ops are not uniformly conv-coloured',
    await page.locator('#steps .step.ustep .op-conv').count(), 0);
  check('UTerm borrows the term colour',
    await page.locator('#steps .step.ustep .op-Term').count() > 0, true);
  check('the nav switches to unify controls',
    /unify step 0 \//.test(await page.textContent('#nav') ?? ''), true);
  await page.keyboard.press('j');
  await page.waitForFunction(() => /unify step 1 \//.test(document.getElementById('nav')!.textContent!));
  check('j walks the sub-steps',
    /unify step 1 \//.test(await page.textContent('#nav') ?? ''), true);
  check('the sub-step is in the address', /\/9\/u1$/.test(page.url()), true);
  // Phrased for a reader rather than reusing the error-message label.
  check('the nav says what the unifier is doing',
    /applying\s*ax_1/.test(await page.textContent('#nav') ?? ''), true);

  // The callout has to describe the *unify* command. It used to describe the
  // parked proof step, identically for every sub-step, so the pane whose whole
  // job is the sub-machine said nothing about it.
  {
    const at1 = await page.textContent('#callout');
    await page.keyboard.press('j');
    await page.waitForFunction(() => /unify step 2 \//.test(document.getElementById('nav')!.textContent!));
    const at2 = await page.textContent('#callout');
    check('the callout changes with the sub-step', at1 === at2, false);
    check('and does not describe the parked proof step',
      /consumes.*⊢/.test(at2 ?? ''), false);
    // Walk to the end: the terminal sub-step reports the verdict.
    await page.keyboard.press('G');
    await page.waitForTimeout(150);
    check('the last sub-step reports the match',
      /target fully matched/.test(await page.textContent('#callout') ?? ''), true);
    await nav(`#/peano.mmb/thm/a1i/9/u1`);
    await page.waitForSelector('#right.unify');
  }
  await page.keyboard.press('h');
  await page.waitForFunction(() => !document.getElementById('right')!.classList.contains('unify'));
  check('h leaves the unifier', await page.isVisible('#p-ustack'), false);
  check('and leaves the address', /\/9$/.test(page.url()), true);

  console.log('a unify sub-step is linkable');
  {
    // Straight to a sub-step, with no proof step visited first: the unifier has
    // to be reopened from the address, not left to a later correction.
    await nav(`#/peano.mmb/thm/a1i/9/u2`);
    await page.waitForSelector('#right.unify');
    check('the unifier is open', await page.isVisible('#p-ustack'), true);
    check('at the linked sub-step',
      /unify step 2 \//.test(await page.textContent('#nav') ?? ''), true);
    await page.reload();
    await page.waitForSelector('#right.unify');
    check('and it survives a refresh',
      /unify step 2 \//.test(await page.textContent('#nav') ?? ''), true);
  }

  console.log('an out-of-range step corrects the address');
  {
    await nav(`#/peano.mmb/thm/a1i/99999`);
    await page.waitForSelector('#steps .step');
    const last = (await page.locator('#steps .step:not(.ustep)').count()) - 1;
    check('the address is clamped', page.url().endsWith(`/${last}`), true);
    check('and the nav agrees',
      new RegExp(`step ${last} /`).test(await page.textContent('#nav') ?? ''), true);
  }

  console.log('unify markers');
  {
    await nav(`#/peano.mmb/thm/a1i/14`);
    await page.waitForSelector('#steps .step');
    await page.keyboard.press('u');
    await page.waitForSelector('#right.unify');
    // The unifier is a machine in its own right, so its panes carry the same
    // shape of marker -- what this command eats, what the last one left --
    // in the sub-machine's own colours.
    check('the unify stack marks what it consumes',
      await page.locator('#b-ustack .slot.u-takes').count(), 1);
    check('and says so in the legend',
      /▸ 1 consumed/.test(await page.textContent('#h-ustack') ?? ''), true);
    check('the unify heap is labelled the substitution',
      (await page.textContent('#h-uheap'))?.startsWith('Unify heap — substitution'), true);

    // Step 1 is a `UHyp`, which takes a proof off the *main* stack rather than
    // the unify stack -- so that is where the marker has to appear.
    await page.keyboard.press('j');
    await page.waitForFunction(() => /unify step 1 \//.test(document.getElementById('nav')!.textContent!));
    check('a UHyp marks the main stack instead',
      await page.locator('#b-stack .slot.u-takes').count(), 1);
    check('and the main legend reports it',
      /▸ 1 consumed/.test(await page.textContent('#h-stack') ?? ''), true);
    check('while the unify stack is empty',
      (await page.textContent('#b-ustack'))?.trim(), 'empty — target fully matched');

    await page.keyboard.press('j');
    await page.waitForFunction(() => /unify step 2 \//.test(document.getElementById('nav')!.textContent!));
    check('a UTerm marks what it pushed',
      await page.locator('#b-ustack .slot.u-makes').count(), 1);
    check('and counts both halves',
      /▸ 1 consumed · 1 just pushed/.test(await page.textContent('#h-ustack') ?? ''), true);
    await page.keyboard.press('h');
    await page.waitForFunction(() => !document.getElementById('right')!.classList.contains('unify'));
  }

  console.log('markers');
  await nav(`#/peano.mmb/thm/mpd/14`);
  await page.waitForSelector('#b-stack .slot');
  // What the previous step pushed, and what this one is about to consume.
  check('the previous push is marked',
    await page.locator('#b-stack .slot.fresh').count() > 0, true);
  await nav(`#/peano.mmb/thm/mpd/25`);
  await page.waitForSelector('#b-stack .slot');
  check('the consumed region is barred',
    await page.locator('#b-stack .slot.doomed').count() > 0, true);
  await nav(`#/peano.mmb/thm/mpd/14`);
  await page.waitForSelector('#b-heap .slot');
  // Step 14 is `Ref 3`, so slot 3 is the one it copies.
  check('a Ref outlines its heap slot',
    await page.locator('#b-heap .slot.refd').count(), 1);

  console.log('the callout');
  await nav(`#/peano.mmb/thm/mpd/25`);
  await page.waitForSelector('#callout .po-head');
  const co = (await page.textContent('#callout')) ?? '';
  // Schematic, in the applied theorem's own variables -- the stack pane
  // already shows the instantiated elements.
  check('names the applied declaration', /axiom\s+ax_mp/.test(co), true);
  check('shows what it consumes', /consumes/i.test(co), true);
  check('and what it produces', /produces/i.test(co), true);
  check('and explains the slot order', /2 hypotheses .*2 binders, then the target/.test(co), true);
  check('offers to step into the unifier',
    await page.locator('#callout .po-u').count(), 1);
  check('and to open the declaration',
    await page.locator('#callout .po-go a').count(), 1);

  console.log('proof mode filters the panes');
  {
    // `rlistindd` step 55 is a `Thm` popping six stack elements, only one of
    // which is a proof, with a heap of nineteen entries.
    await nav(`#/peano.mmb/thm/rlistindd/55`);
    await page.waitForSelector('#b-stack .slot');
    check('unfiltered stack shows everything',
      await page.locator('#b-stack .slot').count(), 6);
    check('and the header is a plain count',
      (await page.textContent('#h-stack'))?.startsWith('Stack (6)'), true);
    check('unfiltered heap shows everything',
      await page.locator('#b-heap .slot').count(), 19);

    await page.keyboard.press('p');
    await page.waitForFunction(() =>
      document.getElementById('h-stack')!.textContent!.includes('of'));
    check('filtered stack shows only proofs',
      await page.locator('#b-stack .slot').count(), 1);
    check('filtered heap shows only proofs',
      await page.locator('#b-heap .slot').count(), 6);
    // Real indices, so the gaps show. A heap index is an address that `Ref`
    // names; a stack index is only depth, but the gaps are how each pane
    // admits it is not showing everything.
    check('the heap keeps its real indices',
      await page.locator('#b-heap .slot .idx').allTextContents(),
      ['10', '12', '13', '15', '16', '17']);
    check('the stack header reads M of N',
      (await page.textContent('#h-stack'))?.startsWith('Stack (1 of 6)'), true);
    check('the heap header reads M of N',
      await page.textContent('#h-heap'), 'Heap (6 of 19)');
    // Counting the expressions a step shuffles would contradict a pane that is
    // not showing them.
    check('the legend counts follow the filter',
      /1 consumed here/.test(await page.textContent('#h-stack') ?? ''), true);

    // `eori` step 32 has proofs at stack positions 0 and 2 of 7, so the
    // filtered pane must show `2, 0` and not renumber them to `1, 0`.
    await nav(`#/peano.mmb/thm/eori/32`);
    await page.waitForSelector('#b-stack .slot');
    check('the stack keeps its real indices',
      await page.locator('#b-stack .slot .idx').allTextContents(), ['2', '0']);
    // The filtered panes are a proof-level machine in their own right, and its
    // top is the topmost *proof*. Marking the true top instead would leave
    // nothing marked whenever an expression sits above it -- here, position 6.
    check('the topmost shown row is marked as the top',
      await page.locator('#b-stack .slot.top .idx').allTextContents(), ['2']);
    await page.keyboard.press('p');
    await page.waitForFunction(() =>
      document.querySelectorAll('#b-stack .slot').length === 7);
    check('and unfiltered that is the real top',
      await page.locator('#b-stack .slot.top .idx').allTextContents(), ['6']);
    await page.keyboard.press('p');
    await page.waitForFunction(() =>
      document.querySelectorAll('#b-stack .slot').length === 2);

    // A pane the filter emptied must say so rather than claim to be empty.
    await nav(`#/peano.mmb/thm/a1i/5`);
    await page.waitForSelector('#b-stack');
    check('a pane emptied by the filter says so',
      (await page.textContent('#b-stack'))?.trim(), 'no proofs — filtered');
    await nav(`#/peano.mmb/thm/a1i/0`);
    await page.waitForSelector('#b-stack');
    check('a genuinely empty pane still says empty',
      (await page.textContent('#b-stack'))?.trim(), 'empty');
    await page.keyboard.press('p');
    await page.waitForFunction(() =>
      !document.getElementById('h-stack')!.textContent!.includes('of'));
  }

  console.log('convertibility symbols are coloured');
  {
    // `anl` step 22 is a `Conv`, whose schematic effect mentions `e1 ≟ e2`.
    await nav(`#/peano.mmb/thm/anl/22`);
    await page.waitForSelector('#callout .po-eff');
    const co = (await page.textContent('#callout')) ?? '';
    check('the effect mentions a convertibility', /≟/.test(co), true);
    // Coloured exactly as the stack panes render it, rather than left as plain
    // text in the callout.
    check('and it is wrapped in .conv',
      await page.locator('#callout .conv').count() > 0, true);
  }

  console.log('the unifier is dropped when the step changes');
  // Self-contained: step 25 of `mpd` is a `Thm`, so it has a unifier to open.
  await nav(`#/peano.mmb/thm/mpd/25`);
  await page.waitForSelector('#steps .step');
  await page.keyboard.press('u');
  await page.waitForSelector('#right.unify');
  await nav(`#/peano.mmb/thm/mpd/26`);
  await page.waitForSelector('#steps .step');
  // It belongs to one step; leaving that step must close it, or the panes show
  // a sub-machine unrelated to the highlighted command.
  check('moving off the step closes it', await page.isVisible('#p-ustack'), false);

  console.log('a refresh lands where it left off');
  {
    await nav(`#/peano.mmb/thm/syl/7`);
    await page.waitForSelector('#steps .step');
    await page.reload();
    // The hash survives a refresh, so the view knows where it was; a file it
    // fetched by URL it can simply fetch again.
    await page.waitForSelector('#steps .step', { timeout: 60000 });
    check('the picker is not shown', await page.isVisible('#open'), false);
    check('the hash is kept', new URL(page.url()).hash, '#/peano.mmb/thm/syl/7');
    check('the declaration is reopened', await page.textContent('#crumb b'), 'syl');
    check('at the same step',
      /step 7 \/ 23/.test(await page.textContent('#nav') ?? ''), true);
  }

  console.log('r re-reads the file in place');
  {
    // The recompile-and-look loop: the file is fetched again, and the address
    // is untouched, so it lands back on the step you were reading. This has to
    // run while the source is still the *URL* the examples load from -- a file
    // the user supplied cannot be re-read, so `r` opens the picker instead.
    await nav(`#/peano.mmb/thm/a1i/7`);
    await page.waitForSelector('#steps .step');
    await page.keyboard.press('r');
    await page.waitForFunction(() => document.getElementById('detail')!.classList.contains('on'));
    await page.waitForSelector('#steps .step');
    check('the declaration is still open', await page.isVisible('#open'), false);
    check('at the same step', new URL(page.url()).hash, '#/peano.mmb/thm/a1i/7');
    // The re-fetch and re-verify are asynchronous, so wait for the badge to
    // settle rather than reading it mid-flight.
    await page.waitForFunction(() => document.getElementById('status')!.textContent === '✓');
    check('and it verified again', await page.textContent('#status'), '✓');
  }

  console.log('a supplied file survives a refresh too');
  {
    // It cannot be re-read from the filesystem without the user, so it is kept
    // in the browser's own storage and read back from there.
    await page.goto(url);
    await page.setInputFiles('#file', 'test/peano.mmb');
    await page.waitForSelector('#decls tr', { timeout: 60000 });
    await nav(`#/peano.mmb/thm/syl/7`);
    await page.waitForSelector('#steps .step');
    await page.reload();
    await page.waitForSelector('#steps .step', { timeout: 60000 });
    check('the picker is not shown', await page.isVisible('#open'), false);
    check('the hash is kept', new URL(page.url()).hash, '#/peano.mmb/thm/syl/7');
    check('the declaration is reopened', await page.textContent('#crumb b'), 'syl');
    check('at the same step',
      /step 7 \/ 23/.test(await page.textContent('#nav') ?? ''), true);
  }

  console.log('opening another file forgets the kept one');
  {
    // Otherwise the picker would lie about what a refresh brings back.
    await page.keyboard.press('o');
    check('the picker returns', await page.isVisible('#open'), true);
    check('and its prompt is reset', await page.textContent('#drop'), 'drop a file here');
    await page.goto(url);
    await page.waitForTimeout(300);
    check('a reload now offers the picker', await page.isVisible('#open'), true);
    check('with nothing restored', await page.isVisible('#decls tr'), false);
  }

  console.log('broken files');
  {
    // The checked-in counterexamples, shared with the mm0-c test suite and
    // regenerated by `tests/mmb/mutate.py`. Each is a shape of failure the
    // view treats differently; without one of each in front of it, the error
    // paths are only ever reasoned about.
    //
    // The folder is the *verifier's* verdict, which is not the reader's: the
    // index cases sit in `pass/` because they verify, and are counterexamples
    // here precisely because verifying did not make them legible. So a name
    // is looked up in both rather than spelled with its folder.
    const open = async (n: string): Promise<void> => {
      const file = ['fail', 'fail-index', 'pass']
        .map((d) => `../tests/mmb/${d}/${n}.mmb`)
        .find((p) => existsSync(p));
      if (file === undefined) throw new Error(`no counterexample named ${n}`);
      await page.goto(url);
      await page.evaluate(() => { localStorage.clear(); });
      await page.goto(url);
      await page.setInputFiles('#file', file);
      await page.waitForTimeout(900);
    };

    // A file that verifies has nothing to filter to.
    check('a sound file offers no failed-only filter',
      await page.isVisible('#onlybad'), false);

    await open('bad_magic');
    check('a file that is not an mmb keeps the picker up',
      await page.isVisible('#open'), true);
    check('and says why', /bad magic/.test(await page.textContent('#error') ?? ''), true);

    // The walk stopping partway is not the same as the file being unreadable:
    // everything before the break is still a declaration.
    await open('bad_stream');
    check('a broken walk still lists what was read',
      await page.locator('#decls tr').count() > 0, true);
    // The summary moved from a box across the page into the header, beside the
    // badge: it was the modal's list again, in a place that pushed the view
    // down to say it.
    // One line for the stream stopping, one for what it is therefore short of
    // -- not one per class, which was three views of the same fact. The count
    // is comma-joined and these fixtures (hol mutants) also carry hol's own
    // notes, so the failure clause is the part before the first comma.
    check('and reports how much failed',
      (await page.textContent('#failures') ?? '').split(',')[0], '2 failures');
    await page.click('#failures');
    await page.waitForSelector('#err-modal.open');
    check('and where it stopped',
      /declaration stream/.test(await page.textContent('#err-list') ?? ''), true);
    await page.keyboard.press('Escape');
    await page.waitForFunction(() =>
      !document.getElementById('err-modal')!.classList.contains('open'));

    // A broken *walk* fails with no declaration to blame, so it offers no
    // failed-only filter: one that could only ever empty the list is worse
    // than absent. The error line is what carries that case.
    check('and offers no failed-only filter', await page.isVisible('#onlybad'), false);

    await open('one_bad_decl');
    check('one bad declaration marks one row', await page.locator('#decls tr.bad').count(), 1);
    check('the file is still browsable',
      await page.locator('#decls tr').count() > 100, true);
    check('and the badge says it failed', await page.textContent('#status'), '✗');
    check('the header counts the failures',
      (await page.textContent('#failures') ?? '').split(',')[0], '1 failure');
    // A time in green beside a failed check reads as a second, contradictory
    // verdict.
    {
      const red = await page.evaluate(() => {
        const d = document.createElement('div');
        d.style.color = 'var(--err)';
        document.body.append(d);
        const c = getComputedStyle(d).color;
        d.remove();
        return c;
      });
      check('and the time is not reported as good news',
        await page.evaluate(() => getComputedStyle(document.getElementById('timing')!).color),
        red);
    }
    check('the failed-only filter counts them', await page.textContent('#onlybad'), '1 failed');
    await page.click('#onlybad');
    await page.waitForTimeout(150);
    check('and shows only those',
      await page.evaluate(() => [...document.querySelectorAll('#decls tr')]
        .filter((t) => !t.classList.contains('hidden'))
        .every((t) => t.classList.contains('bad'))), true);
    check('which is one row', await page.locator('#decls tr:visible').count(), 1);
    // The two controls narrow together rather than overriding each other.
    await page.fill('#search', 'zzzz');
    await page.waitForTimeout(150);
    check('and it still composes with the search',
      await page.locator('#decls tr:visible').count(), 0);
    await page.fill('#search', '');
    await page.click('#onlybad');
    await page.waitForTimeout(150);
    check('turning it off restores the list',
      await page.locator('#decls tr:visible').count() > 100, true);

    // The case with its own pane: a unify run that fails has to say so where
    // it failed, not just in the file-level error.
    await open('unify_mismatch');
    await nav(`#/unify_mismatch.mmb/term/F/4/u1`);
    await page.waitForSelector('#right.unify');
    check('the failing step is marked',
      /def F header/.test(await page.textContent('#errrow') ?? ''), true);
    // Every backticked token in a message is a declaration's name, so it is
    // shown as one: printed raw, the quoting was visible and the name was not
    // reachable, which is the wrong way round.
    check('the names in the message are links, not backticks',
      await page.locator('#errrow a').evaluateAll(
        (es) => es.map((e) => `${e.textContent}${(e as HTMLAnchorElement).getAttribute('href')}`)),
      ['lam#/unify_mismatch.mmb/term/lam', 'allc#/unify_mismatch.mmb/term/allc']);
    check('and no backtick survives',
      /`/.test(await page.textContent('#errrow') ?? ''), false);
    // The run stops at the command that failed: no row follows it saying so,
    // and the reason is shown against that command.
    check('the listing ends at the command that failed',
      (await page.locator('#steps .step.ustep').last().textContent())?.includes('UTerm lam'),
      true);
    // The reason is on the failing row and at the head of the callout; the
    // pane heading says the one thing only it can -- how much of this stack
    // the step takes. A command that failed recorded no pops, so that count is
    // the arity it would have taken, clamped by what is there.
    check('the pane heading counts what the step takes',
      /1 consumed/i.test(await page.textContent('#h-ustack') ?? ''), true);
    check('and the element it would have taken is marked',
      await page.locator('#b-ustack .slot.u-takes').count(), 1);
    check('and does not claim the target matched',
      /target (fully )?matched/.test(await page.textContent('#right') ?? ''), false);
    check('the unify pane marks what the failing step takes',
      await page.locator('#b-ustack .slot.u-takes').count(), 1);
    // Marked by the row, not only by the text: a listing is scanned, and a
    // colour difference in one word is not something scanning finds.
    // The command the error names, not the terminal row: marking the end of
    // the run put the flag one row past the thing that did not match.
    check('the failed sub-step row is marked',
      await page.locator('#steps .step.ustep.err').count(), 1);
    check('and it is the command that failed',
      await page.evaluate(() => [...document.querySelectorAll('#steps .step.ustep')]
        .findIndex((e) => e.classList.contains('err'))), 0);

    // A failing step says so from wherever you are standing, and offers to
    // take you there -- it used to say nothing unless you were already on it.
    await nav(`#/unify_mismatch.mmb/term/F/0`);
    await page.waitForSelector('#steps .step');
    check('the verdict shows from another step',
      /def F header/.test(await page.textContent('#errrow') ?? ''), true);
    check('with a way to reach the failure',
      await page.locator('#errrow button').count(), 1);
    await page.click('#errrow button');
    await page.waitForFunction(() => location.hash.endsWith('/4'));
    check('which jumps to it', await page.evaluate(() => location.hash),
      '#/unify_mismatch.mmb/term/F/4');
    check('and the failed step row is marked',
      await page.locator('#steps .step.err').count(), 1);
    check('the offer is gone once taken',
      await page.locator('#errrow button').count(), 0);
    // The callout leads with what went wrong; everything after it describes a
    // step that did not finish.
    // The same names appear on both rows of the effect, so they are drawn the
    // same way: `x` is bound in `lam x e2 e3` and is still bound coming back
    // off. Only the consumed row was being coloured.
    await nav(`#/unify_mismatch.mmb/thm/F_DEF/40/u0`);
    await page.waitForSelector('#right.unify');
    await page.waitForTimeout(200);
    {
      const kinds = async (row: string): Promise<string[]> =>
        page.locator(`#callout .eff.${row}`).evaluateAll(
          (es) => es.flatMap((e) => [...e.querySelectorAll('.var, .bvar')]
            .map((x) => `${x.className}:${x.textContent}`)));
      check('what a unify step consumes is coloured',
        (await kinds('takes')).sort(), ['bvar:x', 'var:e2', 'var:e3']);
      check('and so is what it produces',
        (await kinds('makes')).sort(), ['bvar:x', 'var:e2', 'var:e3']);
    }
    await nav(`#/unify_mismatch.mmb/term/F/4`);
    await page.waitForSelector('#steps .step');

    check('the callout opens with the error',
      (await page.textContent('#callout'))?.startsWith('def F header'), true);
    // A trail, not a bare message: which step, and which command inside it.
    // `expected lam, found allc` alone does not say where to look among forty.
    check('and the error names where it happened',
      /def F header, unify step \d+: /.test(await page.textContent('#callout') ?? ''), true);

    // A declaration can fail without any step failing: `COND`'s sort is
    // checked before its proof runs, so it replayed clean while the file said
    // it was broken, and the step view showed nothing at all.
    await open('one_bad_decl');
    await nav(`#/one_bad_decl.mmb/term/COND`);
    await page.waitForSelector('#steps .step');
    // Named by the field that is wrong and the value it holds. `bad sort` said
    // neither, on a declaration that renders correctly -- the view draws
    // `ret.sort`, and it is `td.sort` that is corrupt.
    check('a declaration-level failure is still shown',
      await page.textContent('#errrow'), 'td.sort 3 is not a declared sort (3 so far)');
    check('with nothing to jump to', await page.locator('#errrow button').count(), 0);

    // A declaration whose *binders* are malformed is rejected before any of
    // its proof runs, so it has no first state and nothing to step. That threw
    // out of the view -- twice: once building the machine, and once assuming
    // there was a step to show -- leaving a blank pane on exactly the
    // declaration the file said to look at.
    await open('bad_arg');
    await nav(`#/bad_arg.mmb/term/eu`);
    await page.waitForFunction(() =>
      document.getElementById('detail')!.classList.contains('on'));
    await page.waitForTimeout(200);
    check('a declaration that cannot be run still says what it is',
      (await page.textContent('#stmtbar'))?.startsWith('def eu'), true);
    check('and why it was rejected',
      await page.textContent('#errrow'), 'arg 0: deps reference a bound variable at or past 0');
    // The listing says why it is empty, where the commands would have been: an
    // empty pane reads as a declaration with no proof, which is a different
    // and unremarkable thing.
    check('the listing says why it is empty',
      await page.textContent('#steps'), 'initialization error');
    check('and says it the way every other failure is said',
      await page.locator('#steps .step.err').count(), 1);
    // The `!` is the same mark as on every other failed row, so it is not
    // slanted along with the text; and the text begins in the column a
    // command begins in, because the row has a command row's shape.
    {
      const style = await page.evaluate(() => ({
        mark: getComputedStyle(document.querySelector('#steps .step.norun')!, '::before')
          .fontStyle,
        text: getComputedStyle(document.querySelector('#steps .step.norun .why')!).fontStyle,
        gutter: document.querySelector('#steps .step.norun .i') !== null,
      }));
      check('the text is italic', style.text, 'italic');
      check('the mark is not', style.mark, 'normal');
      check('and it keeps the index gutter, so the text lines up', style.gutter, true);
    }
    check('with no commands to step', await page.locator('#steps .step:not(.norun)').count(), 0);
    // The view has to survive it, not just render it once.
    await nav(`#/bad_arg.mmb/thm/T_DEF/3`);
    await page.waitForSelector('#steps .step');
    check('and the next declaration still works',
      await page.locator('#steps .step').count() > 0, true);

    // A run carries on past a disjoint-variable violation or a failed unify,
    // so a proof can have several failures. Marking one of them would say the
    // others are fine.
    await open('many_bad');
    await nav(`#/many_bad.mmb/thm/SELECT_AX`);
    await page.waitForSelector('#steps .step');
    check('every failing step is marked, not just the first',
      await page.locator('#steps .step.err').count() > 1, true);
    // Marked, not moved. A rule written for the error *token* also matched the
    // failed *row*, since both were class `err`, so a failing step took a
    // border and 2px of padding where it should have had 10 and sat out of
    // line with the listing around it.
    check('and marking one does not move it out of line',
      await page.evaluate(() => {
        const rows = [...document.querySelectorAll('#steps .step')];
        // A failed row against a normal one -- comparing rows that all pass
        // proves nothing, and the failures here are a long way down.
        const bad = rows.find((e) => e.classList.contains('err'));
        const ok = rows.find((e) => !e.classList.contains('err'));
        if (bad === undefined || ok === undefined) return 'no pair to compare';
        // No helper function in here: the transpiler adds a `__name` shim for
        // named function expressions, which does not exist in the page.
        const a = Math.round(bad.children[0]!.getBoundingClientRect().left);
        const c = Math.round(ok.children[0]!.getBoundingClientRect().left);
        return a === c ? 'aligned' : `${a} vs ${c}`;
      }), 'aligned');
    check('and the offer says how many there are',
      /go to the first of \d+/.test(await page.textContent('#errrow') ?? ''), true);
    {
      // Taking it lands on the first, and the offer goes away there.
      await page.click('#errrow button');
      await page.waitForTimeout(200);
      check('taking it lands on one of them',
        await page.evaluate(() => document.querySelector('#steps .step.cur')
          ?.classList.contains('err')), true);
    }

    // An id past the end of a table names nothing. Drawn as an ordinary name
    // it reads as one that happens to be spelled `s48`, which is the reading
    // that hides the defect -- and it linked to an address that resolves to
    // nothing, so it looked live and went nowhere.
    await open('capped');
    await nav(`#/capped.mmb/thm/anr`);
    await page.waitForSelector('#stmtbar');
    await page.waitForTimeout(200);
    check('an out-of-range sort is marked as an error',
      await page.locator('#stmtbar .missing').allTextContents(), ['s48']);
    check('and is not a link', await page.evaluate(() =>
      document.querySelector('#stmtbar .missing')?.tagName), 'SPAN');
    check('nothing on the page links to nowhere', await page.evaluate(() =>
      [...document.querySelectorAll('a')].filter((a) => a.getAttribute('href') === '#').length),
    0);
    await nav(`#/capped.mmb`);
    await page.waitForSelector('#decls tr');

    // A step that failed recorded no pops, so the pane showed nothing consumed
    // on the one step worth looking at. `Term abs` wants three arguments and
    // the stack holds two, so all of it is what it would have taken.
    await open('underflow');
    await nav(`#/underflow.mmb/thm/absT/18`);
    await page.waitForSelector('#steps .step');
    check('a failed step still says what it would consume',
      /2 consumed here/i.test(await page.textContent('#h-stack') ?? ''), true);
    check('and marks it, all of it here',
      await page.locator('#b-stack .slot.doomed').count(), 2);

    // A disjoint-variable failure names the variables the applied theorem
    // declared and what they stand for here, rather than two indices.
    await open('disjoint');
    await nav(`#/disjoint.mmb/thm/lamTR/54`);
    await page.waitForSelector('#steps .step');
    // The message carries the binders' names and positions; the substitutions
    // are reconstructed from the stack at that step, and drawn the way every
    // other expression is.
    check('a disjoint-variable failure names both substitutions',
      await page.textContent('#errrow'),
      'step 54: beta: bound variable 0 (x ↦ x) is referenced in'
      + ' argument 3 (G ↦ an G ( ty x A ))');
    check('and they get the usual term rendering',
      await page.locator('#errrow .why *').evaluateAll(
        (es) => es.map((e) => `${e.className}:${e.textContent}`)),
      ['nm:beta', 'var:x', 'bvar:x', 'var:G', 'nm:an', 'var:G',
        'nm:ty', 'bvar:x', 'var:A']);

    // The callout describes the step you are standing on, so the failure it
    // carries has to be there too -- the error row says a declaration failed,
    // the callout says what this step was doing when it did.
    check('the callout carries it as well',
      (await page.textContent('#callout'))?.startsWith(
        'beta: bound variable 0 (x ↦ x) is referenced in argument 3'), true);
    check('rendered there too, not flattened',
      await page.locator('#callout .po-err .bvar').count() > 0, true);

    // A unify run can fail as a whole -- the target left partly matched --
    // rather than at one of its commands. There is no command to point at, and
    // pointing at the last one that worked blames it for something it did not
    // do; `/u-1` is not a place either.
    await open('unmatched');
    await nav(`#/unmatched.mmb/term/T`);
    await page.waitForSelector('#steps .step');
    check('a run that failed as a whole names no command',
      /def T header: unify stack not empty/.test(await page.textContent('#errrow') ?? ''), true);
    check('and gives no step number for it',
      /unify step -?\d/.test(await page.textContent('#errrow') ?? ''), false);
    await page.click('#failures');
    await page.waitForSelector('#err-modal.open');
    check('nor an address for one', await page.evaluate(() =>
      [...document.querySelectorAll('#err-list a')]
        .some((a) => (a.getAttribute('href') ?? '').includes('u-1'))), false);
    await page.keyboard.press('Escape');
    await page.waitForFunction(() =>
      !document.getElementById('err-modal')!.classList.contains('open'));

    // A sort in a message is a declaration like any other.
    await open('pure_sort');
    await page.click('#failures');
    await page.waitForSelector('#err-modal.open');
    check('and it goes to that sort',
      await page.locator('#err-list dd a').first().getAttribute('href'),
      '#/pure_sort.mmb/sort/wff');
    await page.keyboard.press('Escape');
    await page.waitForFunction(() =>
      !document.getElementById('err-modal')!.classList.contains('open'));

    // A run that gave up counted what it found, not what is there, so the
    // count is a floor and says so.
    await open('capped');
    check('a capped count is marked as a floor',
      /^\d+\+ failures\b/.test(await page.textContent('#failures') ?? ''), true);
    await page.click('#failures');
    await page.waitForSelector('#err-modal.open');
    check('and the list says the same',
      /^\d+\+ failures\b.* in /.test(await page.textContent('#err-title') ?? ''), true);
    await page.keyboard.press('Escape');
    await page.waitForFunction(() =>
      !document.getElementById('err-modal')!.classList.contains('open'));

    // The header can only carry a count and a line or two, and the list marks
    // only the declarations it can name.
    await open('bad_stream');
    await page.click('#status');
    await page.waitForSelector('#err-modal.open');
    check('the badge opens the full list',
      /2 failures/.test(await page.textContent('#err-title') ?? ''), true);
    // A name it cannot resolve is still a name: coloured, just not followable.
    // Only anchors were coloured, so the unresolvable case -- the one worth
    // noticing -- was the one that looked like ordinary text.
    check('a name it cannot link is still drawn as a name',
      await page.evaluate(() => {
        const s = document.querySelector('#err-list dd .nm');
        const probe = document.createElement('div');
        probe.style.color = 'var(--term)';
        document.body.append(probe);
        const term = getComputedStyle(probe).color;
        probe.remove();
        return s !== null && s.tagName === 'SPAN' && getComputedStyle(s).color === term;
      }), true);
    check('and says how far the stream got',
      /incomplete \(\d+\/\d+ terms, \d+\/\d+ theorems\)/.test(
        await page.textContent('#err-list') ?? ''), true);
    // Both lines are about the stream and both say where -- the crumb carries
    // that, so neither message repeats it.
    check('both are attributed to the stream, once each',
      await page.locator('#err-list dt').evaluateAll(
        (es) => es.map((e) => /^declaration stream, 0x[0-9a-f]+$/.test(e.textContent ?? ''))),
      [true, true]);
    // The offset leads the trail like every other crumb, rather than trailing
    // the sentence in brackets.
    check('the trail carries the byte it stopped at',
      /declaration stream, 0x[0-9a-f]+$/.test(
        await page.locator('#err-list dt').first().textContent() ?? ''), true);
    check('including the ones with no declaration to blame',
      /declaration stream/.test(await page.textContent('#err-list') ?? ''), true);
    await page.keyboard.press('Escape');
    await page.waitForFunction(() =>
      !document.getElementById('err-modal')!.classList.contains('open'));
    check('and Escape dismisses it', await page.isVisible('#err-modal'), false);

    // `Sorry` is a warning, not a verdict: every check passed and the file is
    // still not to be trusted. Marked the same as a broken file, the two are
    // indistinguishable at a glance.
    await open('uses_sorry');
    check('a file that only used sorry is a warning', await page.textContent('#status'), '⚠');
    // Warn, not bad. (The `.notes` class is also present -- these are hol
    // mutants, and hol carries notes -- but the point here is the tier.)
    {
      const cls = await page.getAttribute('#status', 'class') ?? '';
      check('not a failure', [cls.includes('warn'), cls.includes('bad')], [true, false]);
    }
    check('and the count is a warning too',
      (await page.getAttribute('#failures', 'class'))?.includes('warn'), true);
    {
      // Orange throughout, wherever a sorry is what is being pointed at.
      const same = await page.evaluate(() => {
        const probe = document.createElement('div');
        probe.style.color = 'var(--warn)';
        document.body.append(probe);
        const warn = getComputedStyle(probe).color;
        probe.remove();
        return [
          getComputedStyle(document.getElementById('status')!).color === warn,
          getComputedStyle(document.getElementById('timing')!).color === warn,
        ];
      });
      check('the badge and the time are drawn in it', same, [true, true]);
    }
    await nav(`#/uses_sorry.mmb/thm/eqcT/63`);
    await page.waitForSelector('#steps .step.cur');
    // The conversion form of `Sorry` discharges an obligation instead of
    // proving a goal. It is still the same admission, so it keeps the warning
    // colour rather than joining the conversion commands.
    check('the conversion form of sorry says so',
      (await page.locator('#steps .step.cur').textContent())?.trim(), '63ConvSorry');
    check('with a description that matches',
      /discharged without being shown/.test(await page.textContent('#callout') ?? ''), true);
    check('and so is the step that admitted its goal',
      await page.evaluate(() => {
        const s = document.querySelector('#steps .op-Sorry');
        const probe = document.createElement('div');
        probe.style.color = 'var(--warn)';
        document.body.append(probe);
        const warn = getComputedStyle(probe).color;
        probe.remove();
        return s !== null && getComputedStyle(s).color === warn;
      }), true);
    await nav(`#/uses_sorry.mmb`);
    await page.waitForSelector('#decls tr');

    // It is a declaration, and the list names it -- so it is reached the same
    // way everything else in the list is.
    await page.click('#status');
    await page.waitForSelector('#err-modal.open');
    check('a declaration that used sorry is a link too',
      await page.locator('#err-list dt a').first().getAttribute('href'),
      '#/uses_sorry.mmb/thm/eqcT');
    await page.locator('#err-list dt a').first().click();
    await page.waitForFunction(() => location.hash.includes('/thm/eqcT'));
    check('and following it closes the list', await page.isVisible('#err-modal'), false);

    await open('unify_mismatch');
    await page.click('#status');
    await page.waitForSelector('#err-modal.open');
    check('a named declaration is a link there',
      await page.locator('#err-list dt a').count() >= 2, true);
    // `theorem F_DEF, step 40, Unfold F, unify step 0` -- each part that names
    // somewhere goes there, so reading the list is enough to go and look.
    {
      const hrefs = await page.locator('#err-list dt a').evaluateAll(
        (es) => es.map((e) => (e as HTMLAnchorElement).getAttribute('href') ?? ''));
      check('the step is one too',
        hrefs.some((h) => /\/thm\/F_DEF\/\d+$/.test(h)), true);
      check('and the unify command within it',
        hrefs.some((h) => /\/thm\/F_DEF\/\d+\/u\d+$/.test(h)), true);
    }
    // A message naming a declaration is read in order to go and look at it,
    // wherever it is shown -- and it goes to the namespace the message
    // recorded, not to whichever one the spelling happens to match first.
    check('the modal links the names in the messages too',
      await page.locator('#err-list dd a').evaluateAll(
        (es) => [...new Set(es.map((e) => (e as HTMLAnchorElement).getAttribute('href')))]),
      ['#/unify_mismatch.mmb/term/lam', '#/unify_mismatch.mmb/term/allc']);
    await page.locator('#err-list dt a').first().click();
    await page.waitForFunction(() => location.hash.includes('/term/F'));
    check('following one opens it and closes the list',
      await page.isVisible('#err-modal'), false);

    // Notes: advisory facts about a file that still verifies. A missing index
    // is not a failure -- the badge stays ✓ green -- but there is now something
    // behind it, so it opens the modal, with a blue `N notes` count beside it.
    // no_index verifies with its whole index gone.
    await open('no_index');
    check('a verified file with notes still reads ok',
      await page.textContent('#status'), '✓');
    check('but the badge takes a pointer for what is behind it',
      (await page.getAttribute('#status', 'class'))?.includes('notes'), true);
    check('the count says how many', await page.textContent('#failures'), '1 note');
    {
      // Blue -- neither the red of a failure nor the orange of a sorry.
      const info = await page.evaluate(() => {
        const probe = document.createElement('div');
        probe.style.color = 'var(--info)';
        document.body.append(probe);
        const c = getComputedStyle(probe).color;
        probe.remove();
        return c === getComputedStyle(document.getElementById('failures')!).color;
      });
      check('in the informational hue', info, true);
    }
    // The ✓ opens the modal, like the failing badges -- but here it is the
    // notes section that fills, and the failure list folds away.
    await page.click('#status');
    await page.waitForSelector('#err-modal.open');
    check('the failure list is not shown',
      await page.locator('#err-list').evaluate((e) => e.classList.contains('hidden')), true);
    check('the notes section is',
      await page.locator('#note-section').evaluate((e) => !e.classList.contains('hidden')), true);
    check('and the note explains the absent index',
      /no index/.test(await page.textContent('#note-list') ?? ''), true);
    await page.keyboard.press('Escape');

    // A present-but-partial index reports each table it lost, so the count is
    // more than one and the list names them.
    await open('partial_index');
    check('a partial index is several notes',
      Number(((await page.textContent('#failures')) ?? '').match(/^(\d+) notes/)?.[1]) > 1, true);
    await page.click('#failures');
    await page.waitForSelector('#err-modal.open');
    check('the first names where the index broke',
      /incomplete/.test(await page.locator('#note-list li').first().textContent() ?? ''), true);
    check('and a later one names notation as lost',
      /Nota/.test(await page.textContent('#note-list') ?? ''), true);
    await page.keyboard.press('Escape');
  }

  console.log('a file the server was told to serve');
  {
    // `npm start path/to/file.mmb` serves that file under `/open/` and opens
    // the page at it, which is how the tool is launched from a checkout: the
    // address names the file and the page fetches it from there, with no
    // picking or dropping. Skipped when the server was started without one, so
    // `npm run serve` and this suite still work together locally; CI passes
    // `test/peano.mmb` so the path is covered there.
    const origin = new URL(url).origin;
    const served = await fetch(`${origin}/open/peano.mmb`, { method: 'HEAD' })
      .then((r) => r.ok).catch(() => false);
    if (!served) console.log('  (skipped: the server is not serving a file)');
    else {
      // A fresh browser context, so nothing kept from earlier in the run can
      // be what satisfies the address -- the point is that the *server*
      // supplies the file.
      const ctx = await browser.newContext();
      const p2 = await ctx.newPage();
      const seen: string[] = [];
      p2.on('console', (m) => { if (m.type() === 'error') seen.push(m.text()); });
      p2.on('pageerror', (e) => seen.push(e.message));
      // `?served` is the server saying `/open/` is here; the fragment is the
      // ordinary file address, so this is exactly what `--open` opens.
      await p2.goto(`${origin}/?served#/peano.mmb`, { waitUntil: 'load' });
      await p2.waitForSelector('#decls tr', { timeout: 60000 });
      check('the served file opens with no picking', await p2.isVisible('#open'), false);
      check('and verifies', await p2.textContent('#status'), '✓');
      check('the crumb names it',
        /peano\.mmb/.test(await p2.textContent('#crumb') ?? ''), true);

      // A deep link is the same address with more of it, and the file behind
      // it still comes from the server.
      await p2.goto(`${origin}/?served#/peano.mmb/thm/a1i/7`, { waitUntil: 'load' });
      await p2.waitForSelector('#steps .step', { timeout: 60000 });
      check('a deep link lands on the step', await p2.textContent('#crumb b'), 'a1i');

      // The whole point of serving it: `r` re-reads from the server, so the
      // recompile loop works for a file that was never dropped in.
      await p2.keyboard.press('r');
      await p2.waitForFunction(() => document.getElementById('status')!.textContent === '✓');
      check('r re-reads it from the server', await p2.textContent('#status'), '✓');
      check('and stays where it was', new URL(p2.url()).hash, '#/peano.mmb/thm/a1i/7');

      // Without the marker the page must not go looking, even for a name the
      // server is in fact serving: a request for a file that is not there is a
      // console error on every page it draws, which is why the server
      // announces itself rather than the page probing. Asked with a name
      // nothing else can supply, so the answer is about `/open/` and not about
      // the kept copy or the example that share peano's name.
      await p2.goto(`${origin}/#/nothing.mmb`, { waitUntil: 'load' });
      await p2.waitForTimeout(1200);
      check('unmarked, an unserved name is simply not found',
        await p2.isVisible('#open'), true);
      check('and logs nothing on the way', seen, []);
      await ctx.close();
    }
  }

  check('no console errors or exceptions', problems.slice(0, 5), []);
} catch (e) {
  // On a hang, dump what the page was showing and anything the app logged, so
  // an intermittent timeout leaves evidence rather than a bare stack.
  console.log(`\n=== CRASH: ${(e as Error).message.split('\n')[0]} ===`);
  try {
    const st = await page.evaluate(() => ({
      hash: location.hash,
      open: document.getElementById('open')?.className,
      detail: document.getElementById('detail')?.className,
      list: document.getElementById('list')?.className,
      status: document.getElementById('status')?.textContent,
      steps: (document.getElementById('steps')?.innerHTML ?? '').slice(0, 80),
      crumb: (document.getElementById('crumb')?.textContent ?? '').slice(0, 50),
      error: document.getElementById('error')?.textContent,
    }));
    console.log('state:', JSON.stringify(st, null, 1));
  } catch (e2) { console.log('could not read state:', (e2 as Error).message); }
  console.log('console/pageerror log:', JSON.stringify(problems.slice(-8), null, 1));
  failures++;
} finally {
  await browser.close();
}

console.log(failures === 0 ? '\nall checks passed' : `\n${failures} failure(s)`);
process.exit(failures === 0 ? 0 : 1);
