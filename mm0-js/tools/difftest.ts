// Three-way differential testing of MMB verifiers.
//
// Mutates a known-good .mmb one byte at a time and runs every implementation
// on each mutant. Where they disagree, the *outlier* is the suspect -- this is
// not a harness for validating one implementation against an oracle, it is a
// way to find bugs in all of them.
//
// Participants:
//
//   * ours    -- src/verify.ts, in process.
//   * mm0-c   -- the reference verifier. Build with -DNO_PARSER, which stubs
//                out `parse_until`: that is the .mm0 interface check, which
//                reads a second file and which none of the others implement.
//   * mm0-rs  -- via `compile <file>.mmb`, which imports the mmb into an
//                Environment with VERIFY_ON_ADD, so elab/verify.rs checks each
//                declaration.
//
//     Caveat: mm0-rs is an *importer* plus a verifier of the imported
//     representation, not a verifier of the mmb encoding. It rebuilds a def's
//     value from the unify stream and never runs the def's proof stream, and
//     it does not validate binder dependency bitmasks. So it accepting what
//     the others reject is largely expected. The other direction, and its
//     crashes, are the interesting signals.
//
// A crash -- a signal, a Rust panic (exit 101), or an exception escaping ours
// -- is a bug regardless of verdict, and is bucketed by message so that many
// mutants hitting one bug are reported once.
//
// Usage: node dist/tools/difftest.js [iterations] [seed] [fixture]
//   MM0C=path   the mm0-c binary   (default: mm0-c)
//   MM0RS=path  the mm0-rs binary  (default: mm0-rs)
// An implementation that cannot run, or that rejects the unmutated fixture, is
// skipped with a warning rather than believed.

import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { MmbError, MmbFile } from '../src/mmb.js';
import { verify } from '../src/verify.js';

const here = dirname(fileURLToPath(import.meta.url));
const iterations = Number(process.argv[2] ?? 2000);
const seed = Number(process.argv[3] ?? 1);
const FIXTURE = process.argv[4] ?? join(here, '..', '..', 'test', 'peano.mmb');

interface Result {
  accept: boolean;
  /** It died rather than deciding. */
  crashed: boolean;
  /** A short signature of why, for bucketing. */
  detail: string;
}

interface Impl {
  name: string;
  run(path: string, bytes: Uint8Array): Result;
}

/** xorshift32, so any finding can be reproduced from its seed. */
function rng(state: number): () => number {
  let s = state | 0 || 1;
  return () => {
    s ^= s << 13; s |= 0;
    s ^= s >>> 17;
    s ^= s << 5; s |= 0;
    return (s >>> 0) / 0x100000000;
  };
}

/**
 * Collapse a message to something stable enough to group by.
 *
 * Source locations are deliberately *preserved*: normalising them collapsed
 * two distinct mm0-rs panics -- one in the verifier, one in its error
 * formatter -- into a single bucket, which hid the second until the first was
 * fixed and the count failed to reach zero.
 */
function signature(s: string): string {
  const locs: string[] = [];
  return s
    .replace(/[\w/.-]+\.rs:\d+:\d+/g, (m) => `\u0000${locs.push(m) - 1}\u0000`)
    .replace(/0x[0-9a-fA-F]+/g, '0x_')
    .replace(/\b\d+\b/g, 'N')
    .replace(/\u0000(\d+)\u0000/g, (_, i: string) => locs[Number(i)]!)
    .replace(/\s+/g, ' ')
    .trim()
    .slice(0, 150);
}

function subprocess(
  cmd: string, args: string[],
): { code: number | null; signal: string | null; err: string } {
  try {
    execFileSync(cmd, args, { stdio: ['ignore', 'ignore', 'pipe'], timeout: 30000 });
    return { code: 0, signal: null, err: '' };
  } catch (e) {
    const x = e as { status?: number | null; signal?: string | null; stderr?: Buffer };
    return {
      code: x.status ?? null,
      signal: x.signal ?? null,
      err: (x.stderr?.toString() ?? '').split('\n')
        .filter((l) => l.trim()).slice(0, 2).join(' | '),
    };
  }
}

const MM0C = process.env['MM0C'] ?? 'mm0-c';
const MM0RS = process.env['MM0RS'] ?? 'mm0-rs';

const impls: Impl[] = [
  {
    name: 'ours',
    run: (_path, bytes) => {
      try {
        const r = verify(MmbFile.parse(bytes));
        if (r.ok) return { accept: true, crashed: false, detail: '' };
        const f = r.failures[0];
        return { accept: false, crashed: false, detail: f ? f.message : 'used sorry' };
      } catch (e) {
        if (e instanceof MmbError) return { accept: false, crashed: false, detail: e.message };
        // Anything else escaping is our bug whatever the verdict.
        return {
          accept: false, crashed: true,
          detail: `${(e as Error).name}: ${(e as Error).message}`,
        };
      }
    },
  },
  {
    name: 'mm0-c',
    run: (path) => {
      const { code, signal, err } = subprocess(MM0C, [path]);
      return {
        accept: code === 0,
        crashed: signal !== null,
        detail: signal !== null ? `signal ${signal}` : err,
      };
    },
  },
  {
    name: 'mm0-rs',
    run: (path) => {
      const { code, signal, err } = subprocess(MM0RS, ['compile', path]);
      // 101 is a Rust panic: it fell over rather than deciding.
      return {
        accept: code === 0,
        crashed: signal !== null || code === 101,
        detail: signal !== null ? `signal ${signal}` : err,
      };
    },
  },
];

const original = new Uint8Array(readFileSync(FIXTURE));
const base = MmbFile.parse(original);

/**
 * Where the declaration stream actually ends. The gap between it and
 * `p_index` is not padding: it holds the index's name strings. Without this
 * the whole name area is misreported as "proof stream", which matters because
 * mutating a name is advisory-only for a verifier and mutating a proof is not.
 */
const declEnd = ((): number => {
  let end = base.pProof;
  try {
    for (const d of base.decls()) end = d.proof.endsAt;
  } catch { /* a clean fixture, so this should not happen */ }
  return end;
})();

/** Which structural region an offset falls in, for reporting. */
function region(off: number): string {
  if (off < 40) return 'header';
  if (off < 40 + base.numSorts) return 'sorts';
  if (off < base.pTerms) return 'padding';
  // The tables are only `8 * n` bytes each; everything after them and before
  // the proof stream is `term_data`/`thm_data` -- the binder arrays and the
  // unify streams, which is where the interesting mutations land.
  if (off < base.pTerms + 8 * base.numTerms) return 'term table';
  if (off < base.pThms) return 'term data';
  if (off < base.pThms + 8 * base.numThms) return 'thm table';
  if (off < base.pProof) return 'thm data';
  if (base.pIndex !== 0 && off >= base.pIndex) return 'index';
  if (off >= declEnd) return 'index strings';
  return 'proof stream';
}

interface Bucket { count: number; sample: string; detail: string }
const addTo = (m: Map<string, Bucket>, detail: string, at: string): void => {
  const k = signature(detail) || '(no message)';
  const b = m.get(k);
  if (b) b.count++;
  else m.set(k, { count: 1, sample: at, detail: k });
};

const dir = mkdtempSync(join(tmpdir(), 'mm0-difftest-'));
const mutantPath = join(dir, 'mutant.mmb');
const next = rng(seed);

const crashBuckets = new Map<string, Map<string, Bucket>>();
const outlierBuckets = new Map<string, Map<string, Bucket>>();
const outlierCount: Record<string, number> = {};
const byRegion: Record<string, number> = {};
let unanimous = 0, ambiguous = 0;
const active: Impl[] = [];

console.log(`fixture: ${FIXTURE} (${original.length} bytes)`);
console.log(`${iterations} iterations, seed ${seed}\n`);

try {
  writeFileSync(mutantPath, original);
  for (const impl of impls) {
    let r: Result;
    try {
      r = impl.run(mutantPath, original);
    } catch {
      console.log(`  skipping ${impl.name}: could not run it`);
      continue;
    }
    if (!r.accept) {
      console.log(`  skipping ${impl.name}: it rejects the unmutated fixture (${r.detail})`);
      continue;
    }
    active.push(impl);
    crashBuckets.set(impl.name, new Map());
    outlierBuckets.set(impl.name, new Map());
    outlierCount[impl.name] = 0;
  }
  if (active.length < 2) {
    console.log('FATAL: need at least two implementations');
    process.exit(2);
  }
  console.log(`baseline: ${active.map((i) => i.name).join(', ')} all accept\n`);

  for (let n = 0; n < iterations; n++) {
    const off = Math.floor(next() * original.length);
    const bytes = original.slice();
    const delta = 1 + Math.floor(next() * 255);
    bytes[off] = (bytes[off]! + delta) & 0xff;
    writeFileSync(mutantPath, bytes);

    const where = region(off);
    const at = `@0x${off.toString(16)} +${delta} (${where})`;
    byRegion[where] = (byRegion[where] ?? 0) + 1;

    const results = active.map((impl) => ({ impl, r: impl.run(mutantPath, bytes) }));
    for (const { impl, r } of results) {
      if (r.crashed) addTo(crashBuckets.get(impl.name)!, r.detail, at);
    }

    // Compare only those that actually returned a verdict.
    const decided = results.filter(({ r }) => !r.crashed);
    const accepts = decided.filter(({ r }) => r.accept).length;
    if (accepts === 0 || accepts === decided.length) {
      unanimous++;
    } else if (decided.length >= 3 && (accepts === 1 || accepts === decided.length - 1)) {
      // A clear majority: the odd one out is the suspect.
      const odd = decided.find(({ r }) => (accepts === 1 ? r.accept : !r.accept))!;
      outlierCount[odd.impl.name] = (outlierCount[odd.impl.name] ?? 0) + 1;
      addTo(outlierBuckets.get(odd.impl.name)!,
        `${odd.r.accept ? 'accepts' : 'rejects'}: ${odd.r.detail}`, at);
    } else {
      // Two implementations, or an even split: no majority to appeal to.
      ambiguous++;
    }

    if ((n + 1) % 500 === 0) {
      const parts = active.map((i) => `${i.name} out:${outlierCount[i.name]}`
        + ` crash:${[...crashBuckets.get(i.name)!.values()].reduce((a, b) => a + b.count, 0)}`);
      process.stdout.write(`  ${n + 1}/${iterations}  unanimous:${unanimous}  ${parts.join('  ')}\n`);
    }
  }
} finally {
  rmSync(dir, { recursive: true, force: true });
}

console.log(`\nregions: ${JSON.stringify(byRegion)}`);
console.log(`unanimous: ${unanimous}/${iterations}   no-majority: ${ambiguous}`);

let findings = 0;
for (const impl of active) {
  const crash = crashBuckets.get(impl.name)!;
  const out = outlierBuckets.get(impl.name)!;
  if (crash.size === 0 && out.size === 0) {
    console.log(`\n== ${impl.name} == clean`);
    continue;
  }
  console.log(`\n== ${impl.name} ==`);
  const dump = (title: string, m: Map<string, Bucket>): void => {
    if (m.size === 0) return;
    const rows = [...m.values()].sort((a, b) => b.count - a.count);
    console.log(`  ${title}: ${rows.length} distinct, ${rows.reduce((a, b) => a + b.count, 0)} total`);
    for (const r of rows.slice(0, 12)) {
      console.log(`    ${String(r.count).padStart(4)}x  ${r.detail}`);
      console.log(`          e.g. ${r.sample}`);
    }
  };
  dump('CRASHES (bug regardless of verdict)', crash);
  dump('outlier verdicts (the other two agreed)', out);
  findings += crash.size + out.size;
}

console.log(`\n${findings} distinct finding(s)`);
process.exit(0);
