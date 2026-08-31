// Pins the arena's identity semantics.
//
// `Refl` is specified as an identity test on the two sides of an obligation --
// the verifier asks whether they are the same expression, never whether they
// are structurally equal. Sharing is therefore the producer's responsibility:
// a compiler that wants a `Refl` to succeed must have constructed both sides
// as one expression, which mm0-rs's exporter does (hence `Ref` being 62% of
// all proof commands).
//
// If this arena interned, two separately built but equal expressions would
// collapse to one id and `Refl` between them would succeed -- accepting a proof
// mm0-c rejects. These checks exist so that a future "optimisation" that adds
// hash-consing fails loudly instead of quietly widening what we accept.

import { Arena, NODE } from '../src/arena.js';

let failures = 0;
function check(name: string, actual: unknown, expected: unknown): void {
  const a = JSON.stringify(actual), e = JSON.stringify(expected);
  if (a === e) console.log(`  ok   ${name}`);
  else {
    console.log(`  FAIL ${name}\n         got ${a}\n    expected ${e}`);
    failures++;
  }
}

const a = new Arena();

console.log('identity, not structure');
const x = a.newVar(0, true, 1, 0);
const y = a.newVar(0, true, 2, 0);
check('separate variables are distinct', x !== y, true);

const f1 = a.app(7, [x], 1, 0, 0);
const f2 = a.app(7, [x], 1, 0, 0);
check('equal applications are distinct nodes', f1 !== f2, true);
check('...even with no arguments', a.app(9, [], 1, 0, 0) !== a.app(9, [], 1, 0, 0), true);

// Sharing still happens -- it just comes from the producer reusing an id, the
// way a `Ref` or a `TermSave` does, rather than from the arena merging nodes.
const shared = a.app(7, [f1, f1], 1, 0, 0);
const n = a.asApp(shared);
check('an id reused by the producer is shared', n?.args, [f1, f1]);

console.log('node contents');
check('variable index and sort', a.get(x),
  { k: NODE.VAR, idx: 0, sort: 0, bound: true, dummy: false, depsLo: 1, depsHi: 0 });
check('variable sorts are recorded in order', a.varSorts, [0, 0]);
check('application records its term and return sort',
  { term: n?.term, sort: n?.sort }, { term: 7, sort: 1 });
check('asApp on a variable is null', a.asApp(x), null);
// A dummy is bound, but local to the proof rather than an argument. Only the
// machine that creates it knows which, so the node carries it. Allocated last,
// since a new variable would shift the counts checked above.
{
  const d = a.get(a.newVar(0, true, 2, 0, true));
  check('a dummy is recorded as one', d.k === NODE.VAR && d.dummy, true);
  check('and is still bound', d.k === NODE.VAR && d.bound, true);
}

console.log('bounds');
let threw = false;
try { a.get(9999); } catch { threw = true; }
check('out-of-range id throws', threw, true);

console.log(failures ? `\n${failures} failure(s)` : '\nall checks passed');
process.exit(failures ? 1 : 0);
