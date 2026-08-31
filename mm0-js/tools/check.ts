// Verifies a .mmb from the command line, for the shared test suite.
//
// The browser is where this verifier is meant to be used, and a browser is a
// poor thing to hang a CI job on. This is the same `verify` the explorer runs,
// reporting to an exit code instead of to a page, so `tests/mmb` can hold
// mm0-js to the same files as mm0-c.
//
// Usage: node dist/tools/check.js [--index] <file.mmb>
//
//   (default)  verification only, which is what mm0-c decides
//   --index    also require the index to be readable
//
// The flag exists because the two are different claims and the suite makes
// both. Verification says the proofs are sound; the index says the file can be
// *read* -- names, notation, variable names. The format is clear that the
// second is advisory, so a file with no index at all is perfectly valid and
// mm0-c accepts one without comment. But a file whose index is corrupt is a
// broken file by any useful standard, and nothing else in the suite catches
// it, because every verifier is entitled to ignore it.
//
// Exit codes: 0 accepted, 1 rejected, 2 could not be read at all.

import { readFileSync } from 'node:fs';
import { MmbFile, MmbError } from '../src/mmb.js';
import { verify } from '../src/verify.js';
import { plainMessage } from '../src/msg.js';

const args = process.argv.slice(2);
const wantIndex = args.includes('--index');
const path = args.find((a) => !a.startsWith('--'));
if (path === undefined) {
  console.error('usage: check.js [--index] <file.mmb>');
  process.exit(2);
}

let file: MmbFile;
try {
  file = MmbFile.parse(new Uint8Array(readFileSync(path)));
} catch (e) {
  // A file that cannot be parsed is not the same as one that fails its
  // checks, and the suite distinguishes them: this is the case with no
  // declarations to report on.
  console.error(`${path}: ${(e as Error).message}`);
  process.exit(e instanceof MmbError ? 1 : 2);
}

let bad = false;

// Checked first: without an index every message below names declarations by
// id, so saying why comes before saying what.
if (wantIndex && file.indexError !== undefined) {
  console.error(`${path}: index: ${file.indexError}`);
  bad = true;
}
// The index walk only places the `Nota` table; reading it is a separate pass
// that can fail on its own, and it fails *quietly* -- the whole library still
// renders, in prefix form. Nothing else in the suite would catch that, which is
// the same reason `--index` exists at all.
if (wantIndex) {
  file.notations();
  if (file.notaError !== undefined) {
    console.error(`${path}: index: notation: ${file.notaError}`);
    bad = true;
  }
}

const r = verify(file);
for (const f of r.failures) {
  console.error(`${path}: ${f.what}: ${plainMessage(f.message)}`);
}
if (r.failures.length > 0) {
  console.error(`${r.failures.length}${r.capped ? '+' : ''} failure(s),`
    + ` ${r.verified} declaration(s) verified`);
  bad = true;
}
// `Sorry` is not a failed check, it is the absence of one. The file is still
// not to be trusted, so it cannot be reported as accepted.
if (r.sorried.length > 0) {
  for (const s of r.sorried) console.error(`${path}: ${s.what}: uses sorry`);
  bad = true;
}

process.exit(bad ? 1 : 0);
