// Replays every declaration of peano.mmb on the stack machine.
//
// The end-state invariant table is from EXPLORER_DESIGN.md, which derived it
// from mm0-rs's `mmb::import`: the proof stream leaves exactly one element on
// the stack, and which kind it is depends on the statement. A machine that
// mis-popped anywhere would land on the wrong kind, the wrong count, or an
// error, so replaying a whole library against this is a strong check -- it is
// how the Rust implementation was validated (2881 decls, zero errors).

import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { CLASS, PROOF, MmbFile, declKind } from '../src/mmb.js';
import { EL, Machine, MachineError, stackPops } from '../src/machine.js';
import { NODE } from '../src/arena.js';

const here = join(dirname(fileURLToPath(import.meta.url)), '..', '..', 'test');

let failures = 0;
function canon(v: unknown): string {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return JSON.stringify(v);
  return JSON.stringify(
    Object.entries(v as Record<string, unknown>).sort(([a], [b]) => (a < b ? -1 : 1)));
}
function check(name: string, actual: unknown, expected: unknown): void {
  const a = canon(actual), e = canon(expected);
  if (a === e) console.log(`  ok   ${name}`);
  else {
    console.log(`  FAIL ${name}\n         got ${a}\n    expected ${e}`);
    failures++;
  }
}

const bytes = new Uint8Array(readFileSync(join(here, 'peano.mmb')));
const f = MmbFile.parse(bytes);

// The stack effects `ProofCmd` documents, for the fixed-arity commands. `Ref`
// is excluded: it pops 0, except as ConvRef where it pops 1, which is decided
// by the heap slot rather than the opcode. `Term`/`Thm` are excluded because
// their arity comes from the declaration they name.
const FIXED_POPS: Record<number, number> = {
  [PROOF.DUMMY]: 0,
  [PROOF.HYP]: 1,
  [PROOF.CONV]: 2,
  [PROOF.REFL]: 1,
  [PROOF.SYM]: 1,
  [PROOF.CONG]: 1,
  [PROOF.UNFOLD]: 2,
  [PROOF.CONV_CUT]: 1,
  [PROOF.CONV_SAVE]: 1,
  [PROOF.SAVE]: 0,
};

let replayed = 0, steps = 0, unifyRuns = 0, unifySteps = 0;
const errors: string[] = [];
const endKind: Record<string, number> = {};
const badEnd: string[] = [];
const badPops: string[] = [];
const covered = new Set<number>();

// Cross-checks that go beyond "it ran": a def's value must have the return sort
// the declaration promises, and every variable's sort must match its binder.
let defValues = 0, badDefSort = 0;
let varsChecked = 0, badVarSort = 0;
let refPops0 = 0, refPops1 = 0;

for (const d of f.decls()) {
  const it = d.proof;
  if (it.isNull) continue;
  replayed++;
  const m = new Machine(f, d);
  const name = `${declKind(d)} ${d.cls === CLASS.TERM ? f.termName(d.num) : f.thmName(d.num)}`;
  try {
    while (it.step()) {
      steps++;
      covered.add(it.cmd);
      const before = m.stack.length;
      m.apply(it.cmd, it.data);
      const want = FIXED_POPS[it.cmd];
      if (want !== undefined && m.popped !== want) {
        badPops.push(`${name}: 0x${it.cmd.toString(16)} popped ${m.popped}, want ${want}`);
      }
      if (it.cmd === PROOF.REF) {
        if (m.popped === 0) refPops0++;
        else if (m.popped === 1) refPops1++;
        else badPops.push(`${name}: Ref popped ${m.popped}`);
      }
      // The stack below the popped region must never be disturbed; if `popped`
      // were too small the machine would have eaten into it.
      if (m.stack.length < before - m.popped) {
        badPops.push(`${name}: stack fell below len - popped`);
      }
    }
    if (it.error) errors.push(`${name}: ${it.error.message}`);
    m.endCheck(d);
    unifyRuns += m.unifyRuns;
    unifySteps += m.unifySteps;

    // End state: exactly one element, of the kind the statement calls for.
    if (m.stack.length !== 1) {
      badEnd.push(`${name}: ${m.stack.length} elements left`);
    } else {
      const el = m.stack[0]!;
      const k = declKind(d);
      endKind[k] = (endKind[k] ?? 0) + 1;
      // sort/term have no stream; def/axiom end with an expr, thm with a proof.
      const wantProof = d.cls === CLASS.THM && d.isThm;
      if (el.k !== (wantProof ? EL.PROOF : EL.EXPR)) {
        badEnd.push(`${name}: ended with kind ${el.k}, wanted ${wantProof ? 'proof' : 'expr'}`);
      }
      // A def's proof stream *builds* its value, so the value's sort landing on
      // the declared return sort is a real end-to-end check of the machine.
      if (d.cls === CLASS.TERM && d.isDef && el.k === EL.EXPR) {
        defValues++;
        if (m.arena.sortOf(el.a) !== f.term(d.num).sort) badDefSort++;
      }
    }

    // Every variable's sort must match the binder it was seeded from.
    const binders = d.cls === CLASS.TERM ? f.term(d.num).args : f.thm(d.num).args;
    for (const node of m.arena.nodes) {
      if (node.k !== NODE.VAR) continue;
      const declared = binders[node.idx];
      if (declared === undefined) continue; // a Dummy, sorted by its command
      varsChecked++;
      if (node.sort !== declared.sort) badVarSort++;
    }
  } catch (e) {
    if (e instanceof MachineError) errors.push(`${name}: ${e.message}`);
    else throw e;
  }
}

console.log('replay');
check('declarations replayed', replayed, 2881);
check('steps applied', steps, 244778);
check('machine errors', errors.slice(0, 5), []);
check('all 15 opcodes exercised', covered.size, 15);

console.log('unification');
// A verification that never invoked the unifier would pass every other check
// here, so the counts are asserted rather than assumed. peano has 23,828 `Thm`
// and 1,442 `Unfold` steps, each running the unifier once; the 158 def and
// 2,723 theorem header checks are the other two sites, which a tool that
// unified only at proof steps would not perform at all.
check('unify runs', unifyRuns, 23828 + 1442 + 158 + 2723);
check('unify commands executed', unifySteps, 303904);

console.log('end states');
// From the invariant table: def/local def/axiom end with one expr, theorem and
// pub theorem with one proof.
check('bad end states', badEnd.slice(0, 5), []);
check('def', endKind['def'], 104);
check('local def', endKind['local def'], 54);
check('axiom', endKind['axiom'], 26);
check('theorem', endKind['theorem'], 2642);
check('pub theorem', endKind['pub theorem'], 55);

console.log('stack effects');
check('pops match the documented arities', badPops.slice(0, 5), []);
// `Ref` is 62% of all commands and almost always pushes; the ConvRef case is
// the rare one, and it must occur or the two-behaviour branch is untested.
check('Ref pushed (popped 0)', refPops0 > 100000, true);
check('ConvRef discharged (popped 1)', refPops1 > 0, true);

console.log('sorts');
check('every def value has its declared return sort', badDefSort, 0);
check('def values checked', defValues, 158);
check('every variable matches its binder', badVarSort, 0);
check('variables checked', varsChecked > 1000, true);

console.log('the arity a command would have taken');
// The machine counts what it actually popped, which is nothing for a command
// that failed before touching the stack -- so the view asks what it *would*
// have taken. That answer has to match what the machine really does, or the
// marks are decoration.
{
  let checked = 0, wrong = 0;
  for (const d of f.decls()) {
    const it = d.proof;
    if (it.isNull) continue;
    const m = new Machine(f, d);
    while (it.step()) {
      const want = stackPops(f, it.cmd, it.data);
      m.apply(it.cmd, it.data);
      // `Ref` is 0 or 1 by its heap slot and answers 0; everything else is
      // supposed to be exact.
      if (it.cmd === PROOF.REF) continue;
      checked++;
      if (want !== m.popped) wrong++;
    }
  }
  check('every command popped what the arity said', wrong, 0);
  check('over the whole library', checked, 93852);
}

console.log('a failing unify run stops at the command that failed');
// The trace a failing run hands the view ends *at* the command that did not
// match -- its pre-state is pushed before it is applied -- and no terminal
// step follows it. There is nothing after the failure to describe, and a row
// saying so would put the verdict one line below the thing it is about.
// Corrupt bytes until runs fail inside the unifier and check what comes out.
{
  const base = new Uint8Array(readFileSync(join(here, 'peano.mmb')));
  let traces = 0, terminal = 0, runs = 0;
  for (let off = 0; off < base.length && runs < 8; off += 997) {
    const bytes = base.slice();
    bytes[off] = (bytes[off] ?? 0) ^ 0xff;
    let f: MmbFile;
    try { f = MmbFile.parse(bytes); } catch { continue; }
    try {
      for (const d of f.decls()) {
        const seen: { error: string | null; steps: { cmd: number | null }[] }[] = [];
        const m = new Machine(f, d);
        m.onUnify = (t): void => { seen.push(t); };
        try {
          const it = d.proof;
          if (!it.isNull) while (it.step()) m.apply(it.cmd, it.data);
          m.endCheck(d);
        } catch {
          const failed = seen.filter((t) => t.error !== null);
          if (failed.length > 0) {
            runs++;
            for (const t of failed) {
              traces++;
              // A command, not the terminal marker -- except for a run that
              // never got to apply one, which has no other row to carry the
              // error and so keeps a terminal step.
              if (t.steps.length > 1 && t.steps[t.steps.length - 1]?.cmd === null) terminal++;
            }
          }
          break;
        }
      }
    } catch { /* a corrupt file may fail before any unifier runs */ }
  }
  check('failing unify runs were produced', traces > 0, true);
  check('none ends in a terminal step', terminal, 0);
}

console.log(failures ? `\n${failures} failure(s)` : '\nall checks passed');
process.exit(failures ? 1 : 0);
