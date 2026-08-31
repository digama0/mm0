// A synthetic mmb exercising the `Nota` table's two subtle rules.
//
// Neither peano nor hello_mmc has a term with more than one notation (74 of 74
// and 127 of 127 are distinct), so nothing in a real library covers this. The
// rules are:
//
//   1. Entries are per notation, in declaration order; a term may have several
//      and the *first* is the one MM1 prints with (mmb.md, "The `Nota` table").
//   2. The overflow area is one sequential run of strings, and the nth `0xFF`
//      literal encountered while walking entries in order takes the nth string.
//
// These interact: a skipped duplicate must still consume its overflow strings.
// The fixture below has three entries -- term 0 twice, then term 1 -- each with
// one overflow constant, so a reader that skips the cursor for the duplicate
// gives term 1 the *duplicate's* token and the mistake is visible rather than
// silent.

import { MmbFile } from '../src/mmb.js';

let failures = 0;
function check(name: string, actual: unknown, expected: unknown): void {
  const a = JSON.stringify(actual), e = JSON.stringify(expected);
  if (a === e) console.log(`  ok   ${name}`);
  else {
    console.log(`  FAIL ${name}\n         got ${a}\n    expected ${e}`);
    failures++;
  }
}

// ---- layout -------------------------------------------------------------
const P_TERMS = 48;   // 40 header + 1 sort byte, padded to 8
const P_TDATA = 64;   // two term entries of 8 bytes
const P_PROOF = 80;   // two term_data of one `arg` each (0 args + ret)
const P_INDEX = 88;   // one END byte, padded to 8
const P_NOTA = 112;   // 8-byte count + one 16-byte index entry
const P_ENTRIES = P_NOTA + 8;
const P_OVERFLOW = P_ENTRIES + 3 * 12; // three entries of 8 + 4 bytes
const SIZE = P_OVERFLOW + 3 * 6 + 1;   // three "XXXXX\0" runs and a terminator

const buf = new Uint8Array(SIZE);
const dv = new DataView(buf.buffer);

// header
buf.set([0x4d, 0x4d, 0x30, 0x42], 0); // "MM0B"
dv.setUint8(4, 1);                    // version
dv.setUint8(5, 1);                    // num_sorts
dv.setUint32(8, 2, true);             // num_terms
dv.setUint32(12, 0, true);            // num_thms
dv.setUint32(16, P_TERMS, true);
dv.setUint32(20, P_TDATA, true);      // p_thms: no theorems, so it just marks the end
dv.setUint32(24, P_PROOF, true);
dv.setUint32(32, P_INDEX, true);      // p_index (u64, high word zero)

// two terms, no arguments, sort 0, not defs
for (let i = 0; i < 2; i++) {
  dv.setUint16(P_TERMS + 8 * i, 0, true);        // num_args
  dv.setUint8(P_TERMS + 8 * i + 2, 0);           // sort 0, is_def clear
  dv.setUint32(P_TERMS + 8 * i + 4, P_TDATA + 8 * i, true);
}
// each term_data is just the return `arg`: sort 0, unbound, no deps
dv.setUint32(P_TDATA + 4, 0, true);
dv.setUint32(P_TDATA + 12, 0, true);

dv.setUint8(P_PROOF, 0); // an empty declaration stream

// index: one entry, "Nota"
dv.setUint32(P_INDEX, 1, true);                 // num_entries (u64)
buf.set([0x4e, 0x6f, 0x74, 0x61], P_INDEX + 8); // "Nota"
dv.setUint32(P_INDEX + 16, P_NOTA, true);       // ptr (u64)

// the Nota table
dv.setUint32(P_NOTA, P_OVERFLOW, true); // p_overflow (u64)
const entry = (i: number, termId: number, prec: number): void => {
  const p = P_ENTRIES + 12 * i;
  dv.setUint32(p, termId, true);
  dv.setUint16(p + 4, prec, true);
  dv.setUint8(p + 6, 1); // one literal
  dv.setUint8(p + 8, 0xff); // ...taken from the overflow area
};
entry(0, 0, 10); // term 0, first  -- should win
entry(1, 0, 20); // term 0, second -- should be skipped, but still consume "BBBBB"
entry(2, 1, 30); // term 1
for (const [i, s] of ['AAAAA', 'BBBBB', 'CCCCC'].entries()) {
  for (let k = 0; k < 5; k++) dv.setUint8(P_OVERFLOW + 6 * i + k, s.charCodeAt(k));
}

// ---- checks -------------------------------------------------------------
const f = MmbFile.parse(buf);
check('parses', f.indexError, undefined);
const nota = f.notations();
check('no nota error', f.notaError, undefined);
check('one entry per term, not per notation', nota.size, 2);

const t0 = nota.get(0);
check('term 0 keeps the first notation', t0?.prec, 10);
check('term 0 keeps the first token', t0?.lits, [{ const: 'AAAAA' }]);

// The load-bearing one: term 1 gets "CCCCC" only if the skipped duplicate still
// advanced the shared overflow cursor past "BBBBB".
const t1 = nota.get(1);
check('term 1 is unshifted by the skipped duplicate', t1?.lits, [{ const: 'CCCCC' }]);
check('term 1 keeps its precedence', t1?.prec, 30);

console.log(failures ? `\n${failures} failure(s)` : '\nall checks passed');
process.exit(failures ? 1 : 0);
