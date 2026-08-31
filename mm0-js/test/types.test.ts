// The type layer's rejection paths.
//
// peano verifies, so none of these checks is ever observed to fire while
// verifying it -- the same problem as the unifier's. The pure type arithmetic
// is unit-tested, and the machine-level rules are driven by building a machine
// over a real peano declaration and feeding it a command that must be refused.

import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { CLASS, PROOF, MmbFile, type Decl } from '../src/mmb.js';
import { expr } from '../src/el.js';
import { Machine, MachineError, allLimits } from '../src/machine.js';
import { bitHi, bitLo, depsBelow, hasBit, sortsCompatible } from '../src/types.js';

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
function rejects(name: string, want: string, fn: () => void): void {
  try {
    fn();
    console.log(`  FAIL ${name}\n         expected a MachineError containing ${JSON.stringify(want)}, nothing thrown`);
    failures++;
  } catch (e) {
    if (e instanceof MachineError && e.message.includes(want)) console.log(`  ok   ${name}`);
    else {
      console.log(`  FAIL ${name}\n         threw ${(e as Error).name}: ${(e as Error).message}`);
      failures++;
    }
  }
}

console.log('type arithmetic');
// A bound variable may stand in for a regular one; never the reverse.
check('same sort, both regular', sortsCompatible(false, 1, false, 1), true);
check('same sort, both bound', sortsCompatible(true, 1, true, 1), true);
check('bound where regular is wanted', sortsCompatible(true, 1, false, 1), true);
check('regular where bound is wanted', sortsCompatible(false, 1, true, 1), false);
check('different sorts', sortsCompatible(true, 1, true, 2), false);

// The 55-bit dependency set is split 32 + 23, so the boundary is worth pinning.
check('bit 0', [bitLo(0), bitHi(0)], [1, 0]);
check('bit 31 is the last low bit', [bitLo(31), bitHi(31)], [0x80000000, 0]);
check('bit 32 is the first high bit', [bitLo(32), bitHi(32)], [0, 1]);
check('bit 54 is the last', [bitLo(54), bitHi(54)], [0, 1 << 22]);
check('hasBit across the split',
  [hasBit(1, 0, 0), hasBit(0, 1, 32), hasBit(1, 0, 32), hasBit(0, 1, 0)],
  [true, true, false, false]);
check('depsBelow, empty', depsBelow(0, 0, 0), true);
check('depsBelow, bit 0 not below 0', depsBelow(1, 0, 0), false);
check('depsBelow, bit 0 below 1', depsBelow(1, 0, 1), true);
check('depsBelow rejects a high bit when n is low', depsBelow(0, 1, 5), false);
check('depsBelow across the split', [depsBelow(0, 1, 32), depsBelow(0, 1, 33)], [false, true]);

// Find declarations to build machines over.
const declOf = new Map<string, Decl>();
for (const d of f.decls()) {
  if (d.cls === CLASS.THM) declOf.set(f.thmName(d.num), d);
}
const axGen = declOf.get('ax_gen');
if (axGen === undefined) throw new Error('peano has no ax_gen');
const limits = allLimits(f);

const IM = 0; // `im`, whose arguments and result are all wff
const WFF = 0, NAT = 1, SET = 2;
check('wff is strict and provable', [f.sortIsStrict(WFF), f.sortIsProvable(WFF)], [true, true]);
check('nat is neither', [f.sortIsStrict(NAT), f.sortIsProvable(NAT)], [false, false]);
check('set is strict, not provable', [f.sortIsStrict(SET), f.sortIsProvable(SET)], [true, false]);

console.log('Dummy');
// A strict sort admits no bound variables at all.
rejects('rejects a strict sort', 'strict or free', () => {
  new Machine(f, axGen, limits).apply(PROOF.DUMMY, WFF);
});
rejects('rejects the other strict sort', 'strict or free', () => {
  new Machine(f, axGen, limits).apply(PROOF.DUMMY, SET);
});
rejects('rejects an out-of-range sort', 'bad dummy sort', () => {
  new Machine(f, axGen, limits).apply(PROOF.DUMMY, 99);
});
{
  const m = new Machine(f, axGen, limits);
  m.apply(PROOF.DUMMY, NAT);
  // ax_gen binds one variable, so the dummy takes the next dependency bit.
  const n = m.arena.get(m.stack[0]!.a);
  check('a legal dummy is bound and takes the next bit',
    [n.bound, n.depsLo, n.depsHi], [true, bitLo(1), bitHi(1)]);
}

console.log('Hyp');
{
  // ax_gen's binders are `{x: nat} (p: wff x)`, so heap[0] is a nat variable.
  const m = new Machine(f, axGen, limits);
  m.stack.push(expr(m.heap[0]!.a));
  rejects('rejects a non-provable sort', 'provable', () => m.apply(PROOF.HYP, 0));
}
{
  const m = new Machine(f, axGen, limits);
  m.stack.push(expr(m.heap[1]!.a)); // the wff binder
  m.apply(PROOF.HYP, 0);
  check('accepts a provable sort', m.hyps.length, 1);
}

console.log('Term');
{
  // `im` takes two wffs; ax_gen's first binder is a nat.
  const m = new Machine(f, axGen, limits);
  m.stack.push(expr(m.heap[0]!.a));
  m.stack.push(expr(m.heap[0]!.a));
  rejects('rejects an argument of the wrong sort', 'type mismatch',
    () => m.apply(PROOF.TERM, IM));
}
{
  const m = new Machine(f, axGen, limits);
  m.stack.push(expr(m.heap[1]!.a));
  m.stack.push(expr(m.heap[1]!.a));
  m.apply(PROOF.TERM, IM);
  const n = m.arena.get(m.stack[0]!.a);
  // Both arguments depend on the bound `x`, and a theorem binds nothing, so
  // the result depends on it too.
  check('accepts wffs and accumulates dependencies',
    [n.sort, n.depsLo, n.depsHi], [WFF, bitLo(0), bitHi(0)]);
}

console.log('declaration order');
// A proof may only name what has already been declared: this is what stops a
// definition referring to itself or to a later one.
rejects('rejects a forward term reference', 'term out of range', () => {
  new Machine(f, axGen, { sorts: 3, terms: 0, thms: 0 }).apply(PROOF.TERM, IM);
});
rejects('rejects a forward theorem reference', 'theorem out of range', () => {
  new Machine(f, axGen, { sorts: 3, terms: 3, thms: 0 }).apply(PROOF.THM, 0);
});

console.log('disjoint variables');
// Look for a theorem whose signature is a bound binder followed by a regular
// binder that does *not* declare a dependency on it -- the classic shape that
// makes substituting a dependent expression unsound.
let dvThm = -1, dvBound = -1, dvFree = -1;
for (let i = 0; i < f.numThms && dvThm < 0; i++) {
  const args = f.thm(i).args;
  for (let b = 0; b < args.length; b++) {
    if (!args[b]!.bound || args[b]!.sort !== NAT) continue;
    for (let r = 0; r < args.length; r++) {
      const a = args[r]!;
      if (a.bound || a.sort !== WFF) continue;
      // Count which bound binder `b` is, and check `r` does not name it.
      let bi = 0;
      for (let k = 0; k < b; k++) if (args[k]!.bound) bi++;
      if (!hasBit(a.depsLo, a.depsHi, bi)) { dvThm = i; dvBound = b; dvFree = r; break; }
    }
    if (dvThm >= 0) break;
  }
}
check('found a theorem with a disjointness condition', dvThm >= 0, true);
if (dvThm >= 0) {
  const args = f.thm(dvThm).args;
  console.log(`       using ${f.thmName(dvThm)}, binder ${dvBound} bound, binder ${dvFree} free of it`);
  const m = new Machine(f, axGen, limits);
  // ax_gen gives us `x` (bound nat) and `p` (wff depending on x). Substitute
  // `x` for the bound binder and `p` for the one declared independent of it.
  const x = m.heap[0]!.a, p = m.heap[1]!.a;
  for (let i = 0; i < args.length; i++) {
    const a = args[i]!;
    m.stack.push(expr(i === dvBound ? x : i === dvFree ? p : a.bound ? x : p));
  }
  m.stack.push(expr(p)); // the target
  // Collected rather than thrown: a disjoint-variable violation is a verdict
  // about the step, not damage to the machine, so the run carries on and
  // reports every one it finds instead of only the first.
  m.apply(PROOF.THM, dvThm);
  check('rejects a dependent substitution for an independent binder',
    m.errors.some((e) => /bound variable \d+ .* is referenced in argument/.test(e.message)),
    true);
  check('and carries on rather than stopping there', m.errors.length > 0, true);
}

console.log(failures ? `\n${failures} failure(s)` : '\nall checks passed');
process.exit(failures ? 1 : 0);
