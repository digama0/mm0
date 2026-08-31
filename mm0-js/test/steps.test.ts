// Per-step snapshots.
//
// `a1i` is the design doc's worked example, so its numbers are checked against
// what that records: 16 steps, collapsing to four at proof level -- `Thm ax_1`,
// the `Ref` to its hypothesis, `Thm ax_mp`, and the end. That is the whole
// argument, with the expression plumbing removed.

import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { CLASS, PROOF, MmbFile, type Decl } from '../src/mmb.js';
import { EL } from '../src/el.js';
import { Machine } from '../src/machine.js';
import { replay, isProofStep, stackAt, StackCursor } from '../src/steps.js';

const here = join(dirname(fileURLToPath(import.meta.url)), '..', '..', 'test');
const f = MmbFile.parse(new Uint8Array(readFileSync(join(here, 'peano.mmb'))));

let failures = 0;
function check(name: string, actual: unknown, expected: unknown): void {
  const a = JSON.stringify(actual), e = JSON.stringify(expected);
  if (a === e) console.log(`  ok   ${name}`);
  else {
    console.log(`  FAIL ${name}\n         got ${a}\n    expected ${e}`);
    failures++;
  }
}

const declOf = new Map<string, Decl>();
for (const d of f.decls()) {
  if (d.cls === CLASS.THM) declOf.set(f.thmName(d.num), d);
  else if (d.cls === CLASS.TERM) declOf.set(`term ${f.termName(d.num)}`, d);
}

console.log('a1i');
{
  const d = declOf.get('a1i')!;
  const r = replay(f, d, { unify: true });
  check('verifies', r.error, null);
  check('16 snapshots', r.steps.length, 16);
  // The state shown at step i is *before* its command, so the first is empty.
  check('starts with an empty stack', stackAt(r, 0).length, 0);
  check('the heap starts with the binders', r.steps[0]!.heapLen, f.thm(d.num).numArgs);
  check('ends with one element', stackAt(r, 15).length, 1);
  check('and it is a proof', stackAt(r, 15)[0]!.k, EL.PROOF);

  const shown = r.steps.filter((s) => isProofStep(r, s));
  check('proof level shows four steps', shown.map((s) => s.i), [9, 10, 14, 15]);
  check('which are Thm, Ref, Thm, end',
    shown.map((s) => s.cmd), [PROOF.THM, PROOF.REF, PROOF.THM, null]);
  // The `Ref` survives the filter only because heap slot 2 holds a proof --
  // that is the hypothesis, put there by the `Hyp` command at step 1.
  check('the surviving Ref points at a proof', r.heap[shown[1]!.data]!.k, EL.PROOF);

  const traces = r.steps.flatMap((s) => s.unify);
  check('three unify runs', traces.map((t) => t.site),
    ['Thm ax_1', 'Thm ax_mp', 'a1i header']);
  check('none failed', traces.map((t) => t.error), [null, null, null]);
  // Every run must consume its target exactly: the last recorded state is the
  // terminal one, and its unify stack is what the spec requires to be empty.
  check('each ends with an empty unify stack',
    traces.map((t) => t.steps[t.steps.length - 1]!.ustack.length), [0, 0, 0]);
}

console.log('invariants over the library');
{
  let n = 0, snaps = 0;
  const bad: string[] = [];
  for (const d of f.decls()) {
    if (d.proof.isNull) continue;
    const r = replay(f, d);
    n++;
    snaps += r.steps.length;
    if (r.error !== null) { bad.push(`${d.index}: ${r.error}`); continue; }
    let prevHeap = -1, prevHyps = -1;
    for (const s of r.steps) {
      // The heap and hypothesis list are append-only; that is what lets a
      // snapshot store lengths instead of copies.
      if (s.heapLen < prevHeap) bad.push(`${d.index}@${s.i}: heap shrank`);
      if (s.hypsLen < prevHyps) bad.push(`${d.index}@${s.i}: hyps shrank`);
      prevHeap = s.heapLen; prevHyps = s.hypsLen;
      if (s.heapLen > r.heap.length) bad.push(`${d.index}@${s.i}: heapLen past the end`);
    }
  }
  check('every declaration replays', bad.slice(0, 5), []);
  check('declarations stepped', n, 2881);
  // One snapshot per command plus one terminal state each.
  check('snapshots', snaps, 244778 + 2881);
}

console.log('the stack delta reconstructs exactly');
// Storing `(pops, pushed)` instead of a copy is only sound if a command never
// disturbs the stack below the region it pops. That is true of every command
// in the spec, but it is an assumption this representation now depends on, so
// it is checked against the machine itself rather than argued: a second run
// produces the same arena ids, the arena being deterministic and append-only.
{
  const mismatches: string[] = [];
  let compared = 0;
  for (const d of f.decls()) {
    if (d.proof.isNull) continue;
    const r = replay(f, d);
    if (r.error !== null) continue;
    const m = new Machine(f, d);
    const cur = new StackCursor(r);
    const it = d.proof.clone();
    for (let i = 0; ; i++) {
      const want = m.stack, got = cur.seek(i);
      compared++;
      if (got.length !== want.length
        || got.some((e, k) => e.k !== want[k]!.k || e.a !== want[k]!.a || e.b !== want[k]!.b)) {
        mismatches.push(`${d.index}@${i}: ${got.length} vs ${want.length}`);
        break;
      }
      if (!it.step()) break;
      m.apply(it.cmd, it.data);
    }
  }
  check('no reconstruction mismatches', mismatches.slice(0, 5), []);
  check('states compared', compared, 244778 + 2881);
}

console.log('a failing declaration still steps');
{
  // Corrupt one proof command of `a1i` and require the snapshots up to the
  // failure to survive -- a broken proof is exactly the one worth stepping.
  const d = declOf.get('a1i')!;
  const bytes = new Uint8Array(readFileSync(join(here, 'peano.mmb')));
  const it = d.proof.clone();
  // `step()` leaves `at` on the command it just decoded, so three calls select
  // step 2.
  it.step(); it.step(); it.step();
  bytes[it.at] = PROOF.REFL; // a Ref becomes a Refl, which has nothing to pop
  const g = MmbFile.parse(bytes);
  const d2 = [...g.decls()].find((x) => x.index === d.index)!;
  const r = replay(g, d2);
  check('reports an error', r.error !== null, true);
  check('keeps the steps up to and including it', r.steps.length, 3);
  check('and marks the failing one', r.steps[2]!.err !== null, true);
  check('earlier steps are unmarked', r.steps.slice(0, 2).map((s) => s.err), [null, null]);
  // Replaying does not consume the declaration: a view re-renders constantly.
  check('replay is repeatable', replay(g, d2).steps.length, 3);
}

console.log(failures ? `\n${failures} failure(s)` : '\nall checks passed');
process.exit(failures ? 1 : 0);
