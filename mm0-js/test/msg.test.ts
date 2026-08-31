// Naming a declaration inside a failure message.
//
// The point of the encoding is that a name alone does not identify anything:
// sorts, terms and theorems are separate namespaces, and peano really does
// have `nat` in two of them. A message that said `` `nat` `` and left the view
// to resolve it would link to whichever namespace the view happened to try
// first, and be silently wrong about the other -- so the namespace is written
// down where the message is built, which is the only place that knows it.

import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { MmbFile } from '../src/mmb.js';
import { REF, nameRef, plainMessage } from '../src/msg.js';

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

console.log('the collision this exists for');
{
  const f = MmbFile.parse(new Uint8Array(readFileSync(join(here, 'peano.mmb'))));
  const sorts = new Set<string>();
  for (let i = 0; i < f.numSorts; i++) sorts.add(f.sortName(i));
  const both: string[] = [];
  for (let i = 0; i < f.numTerms; i++) {
    if (sorts.has(f.termName(i))) both.push(f.termName(i));
  }
  check('a name really can be in two namespaces at once', both, ['nat']);
}

console.log('references');
{
  const msg = `Unfold: ${nameRef('term', 'nat')} is not a def`;
  const found = [...msg.matchAll(REF)].map((m) => [m[1], m[2]]);
  check('a reference carries its namespace', found, [['term', 'nat']]);
  // The same spelling in the other namespace is a different reference, which
  // is the whole point -- resolving `nat` without one is a coin toss.
  check('and the other namespace is a different one',
    [...nameRef('sort', 'nat').matchAll(REF)].map((m) => [m[1], m[2]]), [['sort', 'nat']]);
  check('the markers are not for reading', plainMessage(msg), 'Unfold: nat is not a def');
}
{
  // Several in one message, which is what `expected …, found …` is.
  const msg = `expected ${nameRef('term', 'lam')}, found ${nameRef('term', 'allc')}`;
  check('several references in one message',
    [...msg.matchAll(REF)].map((m) => m[2]), ['lam', 'allc']);
  check('and all of them flatten', plainMessage(msg), 'expected lam, found allc');
}
check('a message with no reference is untouched',
  plainMessage('td.sort 3 is not a declared sort (3 so far)'),
  'td.sort 3 is not a declared sort (3 so far)');

console.log(failures ? `\n${failures} failure(s)` : '\nall checks passed');
process.exit(failures ? 1 : 0);
