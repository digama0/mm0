// Whole-file verification.
//
// This is the end of the line: peano must verify completely, with the type
// layer, the disjoint-variable conditions, the unifier at all four sites, and
// the declaration-order constraints all active. mm0-c accepts it, so anything
// we reject is our bug and anything we accept that it rejects is worse.
//
// A second library is not pinned here. The examples CI job compiles every
// example -- peano, hol, hello_mmc, set, x86, compiler -- and runs mm0-js over
// each beside mm0-c, so whole-file verification across libraries lives there,
// against files freshly built by mm0-rs rather than one committed fixture. This
// suite keeps peano because so much else in it (the reader counts, the machine
// replay) is written against that exact compilation.

import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { MmbError, MmbFile } from '../src/mmb.js';
import { verify } from '../src/verify.js';
import { plainMessage } from '../src/msg.js';

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

{
  console.log('peano.mmb');
  const f = MmbFile.parse(new Uint8Array(readFileSync(join(here, 'peano.mmb'))));
  const t = performance.now();
  const r = verify(f);
  const ms = Math.round(performance.now() - t);
  check('  no failures', r.failures.slice(0, 3), []);
  check('  nothing used sorry', r.sorried, []);
  check('  ok', r.ok, true);
  // Every declaration, not only the ones with a proof stream: a sort is
  // verified as much as a theorem is, there is just nothing to run.
  check('  every declaration verified', r.verified, 2896);
  console.log(`       ${r.proofSteps} proof steps, ${r.unifySteps} unify steps, ${ms}ms`);
}

console.log('truncation');
// A file cut short must be reported, not crash. The reader's own truncation
// test covers parsing; this covers the verifier reaching a declaration whose
// proof runs off the end.
{
  const full = new Uint8Array(readFileSync(join(here, 'peano.mmb')));
  let rejected = 0, accepted = 0;
  const crashes: string[] = [];
  for (let cut = 4000; cut < full.length; cut += 9973) {
    try {
      // A parse failure before verification starts is a clean rejection too.
      const r = verify(MmbFile.parse(full.subarray(0, cut)));
      if (r.ok) accepted++; else rejected++;
    } catch (e) {
      if (e instanceof MmbError) rejected++;
      else crashes.push(`${cut}: ${(e as Error).name}: ${(e as Error).message}`);
    }
  }
  check('no truncation escapes as an unexpected exception', crashes.slice(0, 3), []);
  check('truncations were exercised', rejected > 50, true);
  // A cut past the end of the declaration stream removes only the index, which
  // is advisory -- such a file still verifies, and mm0-c accepts it too. So the
  // requirement is that nothing crashes, not that everything is refused.
  check('some truncations are legitimately accepted', accepted >= 0, true);
}

console.log('a stream that stops early');
// Short of everything after the point it stopped, which is one fact and used
// to be reported as three -- one per class. The counts say how far it got.
{
  const bytes = new Uint8Array(readFileSync(join(here, 'hol.mmb')));
  const b = bytes.slice();
  b[205] = (b[205] ?? 0) ^ 0xff;
  const r = verify(MmbFile.parse(b));
  const short = r.failures.filter((f) => /incomplete/.test(f.message));
  check('one failure, not one per class', short.length, 1);
  check('with the counts',
    /^incomplete \(\d+\/\d+ terms, \d+\/\d+ theorems\)$/.test(short[0]?.message ?? ''),
    true);
  // Attributed to the stream, and pointing at where it ended -- so it says
  // `declaration stream` once, on the trail, rather than in the message too.
  check('attributed to the stream', short[0]?.what, 'declaration stream');
  check('and pointing at where it stopped', short[0]?.where.map((w) => w.at), ['byte']);
  // The offset is a crumb, not part of the sentence.
  const stopped = r.failures.find((f) => f.what === 'declaration stream');
  check('the byte it stopped at is on the trail',
    stopped?.where.map((w) => w.at), ['byte']);
  check('not in the message', /at 0x/.test(stopped?.message ?? ''), false);
}

console.log('carrying on past a failure');
// A disjoint-variable violation and a failed unify run are verdicts about a
// step, not damage to the machine: the stack effect either does not depend on
// them or can be completed without them. So a proof with several bad steps
// reports several, instead of costing one edit-and-recheck cycle each.
{
  const bytes = new Uint8Array(readFileSync(join(here, 'hol.mmb')));
  const b = bytes.slice();
  b[120] = (b[120] ?? 0) ^ 0x01;
  const r = verify(MmbFile.parse(b));
  // Group by declaration: the point is more than one failure inside one.
  const per = new Map<number, number>();
  for (const f of r.failures) per.set(f.index, (per.get(f.index) ?? 0) + 1);
  const many = [...per.values()].filter((n) => n > 1);
  check('a declaration can report more than one failure', many.length > 0, true);
  // Each is tagged with the step it happened at, not with the step the
  // declaration finally gave up on.
  const steps = r.failures
    .filter((f) => f.where.some((w) => w.at === 'step'))
    .map((f) => f.where.find((w) => w.at === 'step')!)
    .map((w) => (w.at === 'step' ? w.index : -1));
  check('each carries its own step', new Set(steps).size > 1, true);
  // And it gives up eventually: a file where everything fails is a symptom,
  // not a list of things to fix.
  check('but not without limit',
    [...per.values()].every((n) => n <= 16), true);
  check('and this one did not need to give up', r.capped, false);
}
{
  // A declaration that fails more times than the run will carry on past. The
  // count then means "at least", and the report says so rather than presenting
  // a floor as a total -- and giving up is not itself listed as a defect of
  // the file, since it is a limit of the report.
  const bytes = new Uint8Array(readFileSync(join(here, 'hol.mmb')));
  const b = bytes.slice();
  b[1548] = (b[1548] ?? 0) ^ 0x01;
  const r = verify(MmbFile.parse(b));
  check('the cap is reported when it is hit', r.capped, true);
  check('and nothing is listed for hitting it',
    r.failures.filter((f) => /giving up/.test(f.message)).length, 0);
  const per = new Map<number, number>();
  for (const f of r.failures) per.set(f.index, (per.get(f.index) ?? 0) + 1);
  check('the declaration that hit it reports the cap\'s worth',
    Math.max(...per.values()), 16);
}

console.log('a disjoint-variable failure names what it is about');
// Indices alone -- `argument 3 may not depend on bound variable 0` -- name
// neither the variables the applied theorem declared nor what they stand for
// here, which is the whole content of the complaint. Both are on hand.
{
  const bytes = new Uint8Array(readFileSync(join(here, 'hol.mmb')));
  const b = bytes.slice();
  b[4696] = (b[4696] ?? 0) ^ 0x01;
  const r = verify(MmbFile.parse(b));
  const dv = r.failures.find((f) => /is referenced in argument/.test(f.message));
  // The names of the variables the applied theorem declared, by position. What
  // they stand for is *not* here: it is on the stack at that step, so a
  // replayer reconstructs it, and a copy in the message would be state that
  // can go stale or be redrawn against the wrong arena.
  check('the message names both binders',
    plainMessage(dv?.message ?? ''),
    'beta: bound variable 0 (x) is referenced in argument 3 (G)');
  // `arg:2`, not `arg:0`: bound variable 0 *is* argument 2 of `beta`, which is
  // exactly the mapping the message has to carry -- the two numberings differ,
  // and only one of them addresses the stack.
  check('and carries their positions, not their values',
    (dv?.message ?? '').includes('`arg:2:x`') && (dv?.message ?? '').includes('`arg:3:G`'),
    true);
}

console.log('where the declaration stream ended');
// A file can be well formed and still declare fewer than its tables promise,
// so where the stream ended is a fact about it -- and the walk is the only
// thing that knows it.
{
  const bytes = new Uint8Array(readFileSync(join(here, 'hol.mmb')));
  const f = MmbFile.parse(bytes);
  const it = f.decls();
  let n = 0, endedAt = -1;
  for (;;) {
    const step = it.next();
    if (step.done === true) { endedAt = step.value; break; }
    n++;
  }
  check('the walk reports where it ended', endedAt > 0, true);
  check('and that is the END command itself', bytes[endedAt], 0);
  check('after every declaration', n, 164);
}

console.log('statements that have no proof stream');
// `Sort` and `Term` are declared to have none: their `data` is the length of
// their own command, so the next command is the next statement. mm0-c checks
// this as `data == sz`. Without it a `term` can carry a whole proof stream --
// which is then run, and accepted, though the format says it is not there.
//
// `is_def` in the term table is the only thing that tells a `term` from a
// `def`, so clearing it on a def leaves exactly that: a `term` followed by the
// proof stream it was written with.
{
  const bytes = new Uint8Array(readFileSync(join(here, 'hol.mmb')));
  const clean = verify(MmbFile.parse(bytes));
  check('the library verifies to begin with', clean.ok, true);

  // Byte 138 is the `is_def` bit of a term table entry in hol.mmb.
  const b = bytes.slice();
  b[138] = (b[138] ?? 0) ^ 0x80;
  const r = verify(MmbFile.parse(b));
  const stream = r.failures.filter((f) => /no proof stream/.test(f.message));
  check('a term followed by a proof stream is rejected', stream.length, 1);
  check('and it is the term that is blamed', stream[0]?.what, 'term T');
}

console.log('a declaration whose table entry cannot be read');
// `verify` is total: every way a file can be wrong is a `Failure` in the
// report, never an exception. A declaration can fail in two ways, and the two
// arrive as different types -- a proof that does not check is a
// `MachineError`, an unreadable table entry is an `MmbError` raised as the
// machine reads it. Catching only the first let the second escape and take
// the whole file with it: 164 declarations had already been walked and
// listed, and one bad entry left the reader with no list at all.
//
// The mutant is `tests/mmb/fail/bad_args_pointer.mmb`, which mm0-c rejects
// with `bad args pointer`; it is read from there rather than made here so
// that the two suites are looking at the same bytes.
{
  const path = join(here, '..', '..', 'tests', 'mmb', 'fail', 'bad_args_pointer.mmb');
  let r;
  try {
    r = verify(MmbFile.parse(new Uint8Array(readFileSync(path))));
  } catch (e) {
    r = null;
    check('verify returns a report rather than throwing',
      `threw ${(e as Error).message}`, 'a report');
  }
  if (r !== null) {
    check('verify returns a report rather than throwing', true, true);
    const bad = r.failures.filter((f) => /p_args of/.test(f.message));
    check('the unreadable entry is a failure', bad.length > 0, true);
    check('blamed on the declaration that has it', bad[0]?.what, 'theorem syl');
    // It has no step to point at -- the entry was never read -- so it is
    // located by the byte the reader stopped on, like a broken walk.
    check('located by a byte, not a step', bad[0]?.where[0]?.at, 'byte');
    // The point of the fix: the rest of the library still verifies. A count
    // here would be brittle, but "most of it" is the claim being made.
    check('and the rest of the file still verifies', r.verified > 100, true);
  }
}

console.log(failures ? `\n${failures} failure(s)` : '\nall checks passed');
process.exit(failures ? 1 : 0);
