// The unifier's rejection paths.
//
// Replaying peano exercises the unifier 28,151 times, but peano is a *valid*
// library: every one of those runs succeeds, so not one of the checks below is
// ever observed to fire. A verifier is defined by what it refuses, so these
// drive the unifier directly over hand-built arenas and require each failure.

import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { MmbFile, UNIFY } from '../src/mmb.js';
import { Arena } from '../src/arena.js';
import { EL, expr, proof, type El } from '../src/el.js';
import { UMODE, Unifier, UnifyError, type UMode } from '../src/unifier.js';

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

/** Require `fn` to throw a UnifyError whose message contains `want`. */
function rejects(name: string, want: string, fn: () => void): void {
  try {
    fn();
    console.log(`  FAIL ${name}\n         expected a UnifyError containing ${JSON.stringify(want)}, nothing thrown`);
    failures++;
  } catch (e) {
    if (e instanceof UnifyError && e.message.includes(want)) console.log(`  ok   ${name}`);
    else {
      console.log(`  FAIL ${name}\n         threw ${(e as Error).name}: ${(e as Error).message}`);
      failures++;
    }
  }
}

// A two-argument term and a one-argument term to build targets out of. Names
// come from peano so error messages are realistic; the arenas are our own.
const T2 = 0, T1 = 1;
const arity = (t: number): number => f.term(t).numArgs;

const mk = (
  mode: UMode, ustack: number[], uheap: number[], hstack: number[], mstack: El[], a: Arena,
): Unifier => new Unifier(f, a, mode, ustack, uheap, hstack, mstack);

console.log('UTerm');
{
  const a = new Arena();
  const x = a.newVar(0, true, 1, 0), y = a.newVar(0, true, 1, 0);
  const e = a.app(T2, [x, y], 0, 0, 0);
  const u = mk(UMODE.THM, [e], [], [], [], a);
  u.apply(UNIFY.TERM, T2);
  // Arguments are pushed in reverse, so e1 ends up on top and they are matched
  // in declaration order.
  check('destructures, arguments reversed', u.ustack, [y, x]);
  check('pops the target', u.popped, 1);
}
{
  const a = new Arena();
  const e = a.app(T2, [a.newVar(0, true, 1, 0), a.newVar(0, true, 1, 0)], 0, 0, 0);
  rejects('rejects the wrong term', 'expected', () => {
    mk(UMODE.THM, [e], [], [], [], a).apply(UNIFY.TERM, T1);
  });
}
{
  const a = new Arena();
  const x = a.newVar(0, true, 1, 0);
  rejects('rejects a variable where a term is expected', 'found a variable', () => {
    mk(UMODE.THM, [x], [], [], [], a).apply(UNIFY.TERM, T2);
  });
}
{
  const a = new Arena();
  const x = a.newVar(0, true, 1, 0), y = a.newVar(0, true, 1, 0);
  const e = a.app(T2, [x, y], 0, 0, 0);
  const u = mk(UMODE.THM, [e], [], [], [], a);
  u.apply(UNIFY.TERM_SAVE, T2);
  // `save` records the whole term *before* destructuring it.
  check('UTermSave saves the whole term first', u.uheap, [e]);
}

console.log('URef');
{
  const a = new Arena();
  const x = a.newVar(0, true, 1, 0);
  const u = mk(UMODE.THM, [x], [x], [], [], a);
  u.apply(UNIFY.REF, 0);
  check('matches the substitution', u.ustack, []);
}
{
  const a = new Arena();
  const x = a.newVar(0, true, 1, 0), y = a.newVar(0, true, 1, 0);
  rejects('rejects a different expression', 'does not match', () => {
    mk(UMODE.THM, [y], [x], [], [], a).apply(UNIFY.REF, 0);
  });
}
{
  // The identity semantics, matching `Refl`: two separately constructed but
  // structurally equal expressions are *not* the same expression, and mm0-c
  // rejects this. If the arena ever interns again, this starts passing and the
  // verifier silently accepts more than the spec allows. See arena.test.ts.
  const a = new Arena();
  const x = a.newVar(0, true, 1, 0);
  const e1 = a.app(T1, [x], 0, 0, 0);
  const e2 = a.app(T1, [x], 0, 0, 0);
  rejects('rejects an equal-but-separate expression', 'does not match', () => {
    mk(UMODE.THM, [e2], [e1], [], [], a).apply(UNIFY.REF, 0);
  });
}
{
  const a = new Arena();
  rejects('rejects an out-of-range slot', 'out of range', () => {
    mk(UMODE.THM, [a.newVar(0, true, 1, 0)], [], [], [], a).apply(UNIFY.REF, 3);
  });
}
{
  const a = new Arena();
  rejects('rejects an empty unify stack', 'underflow', () => {
    mk(UMODE.THM, [], [0], [], [], a).apply(UNIFY.REF, 0);
  });
}

console.log('UDummy');
{
  const a = new Arena();
  const x = a.newVar(0, true, 1, 0);
  const u = mk(UMODE.DEF, [x], [], [], [], a);
  u.apply(UNIFY.DUMMY, 0);
  // It *moves* the variable rather than allocating: the arena is read-only here.
  check('moves the variable into the substitution', u.uheap, [x]);
  check('and off the unify stack', u.ustack, []);
  check('the arena did not grow', a.length, 1);
}
{
  const a = new Arena();
  rejects('is illegal when applying a theorem', 'not allowed', () => {
    mk(UMODE.THM, [a.newVar(0, true, 1, 0)], [], [], [], a).apply(UNIFY.DUMMY, 0);
  });
}
{
  const a = new Arena();
  rejects('is illegal in a theorem header', 'not allowed', () => {
    mk(UMODE.THM_END, [a.newVar(0, true, 1, 0)], [], [], [], a).apply(UNIFY.DUMMY, 0);
  });
}
{
  const a = new Arena();
  const e = a.app(T1, [a.newVar(0, true, 1, 0)], 0, 0, 0);
  rejects('rejects a non-variable', 'expected a variable', () => {
    mk(UMODE.DEF, [e], [], [], [], a).apply(UNIFY.DUMMY, 0);
  });
}

console.log('UHyp');
{
  const a = new Arena();
  const x = a.newVar(0, true, 1, 0);
  const ms: El[] = [proof(x)];
  const u = mk(UMODE.THM, [], [], [], ms, a);
  u.apply(UNIFY.HYP, 0);
  check('THM takes a proof off the main stack', u.ustack, [x]);
  check('and the main stack shrinks', ms.length, 0);
  // It consumes nothing from the unify stack, so `popped` stays zero -- the
  // caller reports the main stack's depth separately.
  check('popped counts only unify-stack elements', u.popped, 0);
}
{
  const a = new Arena();
  rejects('THM rejects a non-proof', 'expected a proof', () => {
    mk(UMODE.THM, [], [], [], [expr(a.newVar(0, true, 1, 0))], a).apply(UNIFY.HYP, 0);
  });
}
{
  const a = new Arena();
  rejects('THM rejects an empty stack', 'underflow', () => {
    mk(UMODE.THM, [], [], [], [], a).apply(UNIFY.HYP, 0);
  });
}
{
  const a = new Arena();
  const x = a.newVar(0, true, 1, 0), y = a.newVar(0, true, 1, 0);
  const u = mk(UMODE.THM_END, [], [], [x, y], [], a);
  u.apply(UNIFY.HYP, 0);
  // Taken from the top, so the last-declared hypothesis comes first -- which is
  // the order the stream stores them in.
  check('THM_END takes the last hypothesis first', u.ustack, [y]);
}
{
  const a = new Arena();
  const x = a.newVar(0, true, 1, 0);
  // Each hypothesis must be fully matched before the next one starts; this is
  // what fixes the layout of the stream.
  rejects('THM_END requires the unify stack to be empty', 'must be empty', () => {
    mk(UMODE.THM_END, [x], [], [x], [], a).apply(UNIFY.HYP, 0);
  });
}
{
  const a = new Arena();
  rejects('THM_END rejects an empty hypothesis stack', 'underflow', () => {
    mk(UMODE.THM_END, [], [], [], [], a).apply(UNIFY.HYP, 0);
  });
}
{
  const a = new Arena();
  rejects('is illegal in a definition', 'not allowed in a definition', () => {
    mk(UMODE.DEF, [], [], [], [proof(a.newVar(0, true, 1, 0))], a).apply(UNIFY.HYP, 0);
  });
}

console.log('finish');
{
  const a = new Arena();
  const u = mk(UMODE.THM, [], [], [], [], a);
  u.finish();
  check('an empty unify stack succeeds', true, true);
}
{
  const a = new Arena();
  // The spec's success condition is `... --> S'; H'; .` -- the trailing `.` is
  // an empty unify stack. Without this a stream that stopped early would leave
  // part of the target unmatched and pass.
  rejects('a leftover target is rejected', 'not empty', () => {
    mk(UMODE.THM, [a.newVar(0, true, 1, 0)], [], [], [], a).finish();
  });
}
{
  const a = new Arena();
  // An unmatched hypothesis means the proof proves a weaker statement than the
  // one the declaration announces.
  rejects('an unmatched hypothesis is rejected', 'never matched', () => {
    mk(UMODE.THM_END, [], [], [a.newVar(0, true, 1, 0)], [], a).finish();
  });
}

console.log('sanity');
check('T2 is binary', arity(T2), 2);
check('T1 is unary', arity(T1), 1);
check('EL kinds are distinct', new Set(Object.values(EL)).size, 4);

console.log(failures ? `\n${failures} failure(s)` : '\nall checks passed');
process.exit(failures ? 1 : 0);
