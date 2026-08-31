// A zero-copy reader for the MMB binary format.
//
// Spec: mm0-c/mmb.md. This is a port of the *reading* half of
// components/mm0b_parser (parser.rs, ty.rs); the writer, the typed
// `MmbFile<X>` generics and the `zerocopy` machinery have no analogue here.
//
// Everything reads through a single `DataView` with explicit little-endian
// flags. Typed-array views would be faster but are not usable: the proof and
// unify streams are 1-byte aligned by spec, and `nota` entries are 4-aligned
// at best, so their immediates are unaligned by construction.
//
// No BigInt. The format has eight 64-bit fields, but seven of them are file
// offsets or counts into a file whose other pointers are u32, so the high word
// is zero in any real file and `u64at` asserts that. The eighth — `arg` — is a
// genuine 64-bit bitfield and is handled as a (lo, hi) pair; see `Arg`.

const MAGIC = 0x42304d4d; // "MM0B" read as a little-endian u32
const VERSION = 1;

// Index table ids, as little-endian u32s of their four ASCII bytes.
const INDEX_NAME = 0x656d614e; // "Name"
const INDEX_VAR = 0x4e726156; // "VarN"
const INDEX_HYP = 0x4e707948; // "HypN"
const INDEX_NOTA = 0x61746f4e; // "Nota"
const INDEX_DELM = 0x6d6c6544; // "Delm"

/** Statement opcodes. `STMT_LOCAL` is an OR-flag, not an opcode of its own. */
export const STMT = {
  END: 0x00,
  AXIOM: 0x02,
  SORT: 0x04,
  TERM: 0x05, // also DEF; which one is decided by the term table's is_def bit
  THM: 0x06,
  LOCAL_DEF: 0x0d,
  LOCAL_THM: 0x0e,
} as const;
const STMT_LOCAL = 0x08;

/** Proof stream opcodes. Note 0x1d is unused. */
export const PROOF = {
  END: 0x00,
  TERM: 0x10,
  TERM_SAVE: 0x11,
  REF: 0x12,
  DUMMY: 0x13,
  THM: 0x14,
  THM_SAVE: 0x15,
  HYP: 0x16,
  CONV: 0x17,
  REFL: 0x18,
  SYM: 0x19,
  CONG: 0x1a,
  UNFOLD: 0x1b,
  CONV_CUT: 0x1c,
  CONV_SAVE: 0x1e,
  SAVE: 0x1f,
  SORRY: 0x20,
} as const;

/** Unify stream opcodes. */
export const UNIFY = {
  END: 0x00,
  TERM: 0x30,
  TERM_SAVE: 0x31,
  REF: 0x32,
  DUMMY: 0x33,
  HYP: 0x36,
} as const;

/** Sort modifier bits. */
export const SORT = { PURE: 1, STRICT: 2, PROVABLE: 4, FREE: 8 } as const;

// `nota` literal discriminants, on byte 0 of the 4-byte literal.
const NOTA_VAR = 0x00;
const NOTA_OVERFLOW = 0xff;

/**
 * The encoding of MM0's `Prec::Max`. It needs no special case: it is the
 * largest `u16`, and a writer omits any notation whose precedence would reach
 * it, so every representable precedence is strictly below and ordinary
 * numeric comparison already puts `max` on top.
 *
 * The one thing this would not survive is arithmetic — `PREC_MAX + 1` is a
 * different number rather than still-max — but printing only ever compares,
 * since the compiler bakes each literal's precedence into the `Nota` table.
 */
export const PREC_MAX = 0xffff;
export const APP_PREC = 1024;

const decoder = new TextDecoder('utf-8', { fatal: false });

/**
 * Which of the three independent id namespaces a declaration lives in. These
 * are the classes that `s0`/`t0`/`T0` name and that URLs must carry: peano has
 * `nat` as both a sort and a term, so a bare name does not identify anything.
 */
export const CLASS = { SORT: 0, TERM: 1, THM: 2 } as const;
export type DeclClass = (typeof CLASS)[keyof typeof CLASS];

/** The `s`/`t`/`T` prefix that names an id in each class. */
const CLASS_PREFIX = ['s', 't', 'T'] as const;

/**
 * One declaration kind, spelled as MM1 source spells it. This is a *label*,
 * derived by `declKind` from the three orthogonal facts the format actually
 * records (`cls`, `isDef`, `local`) — never the source of truth. Anything that
 * needs to branch should read those fields; picking a string apart with
 * `endsWith` costs ~10x a field test and, worse, silently stops being a
 * pointer comparison the moment the string has been through `JSON.parse` or a
 * `postMessage` clone.
 *
 * Note the default visibility differs by class: `pub` is the default for defs,
 * `local` for theorems, so `local === false` reads as `def` but `pub theorem`.
 */
export type DeclKind =
  | 'sort' | 'term' | 'def' | 'local def' | 'axiom' | 'theorem' | 'pub theorem';

/** One command yielded by a stream iterator, with the position it started at. */
export interface StreamCmd {
  cmd: number;
  data: number;
  pos: number;
}

/**
 * One literal of a notation: either an argument printed at a given precedence,
 * or a constant token.
 */
export type Lit = { var: number; prec: number } | { const: string };

// Term and theorem entries are cached and shared, so they hold the *offset* of
// their unify stream rather than a cursor over it: a cursor is mutable, and
// handing the same one to two callers would have them consume each other's
// stream. Use `MmbFile.unifyAt` to mint a fresh cursor.

export interface TermEntry {
  id: number;
  numArgs: number;
  isDef: boolean;
  /** The return sort. */
  sort: number;
  args: Arg[];
  ret: Arg;
  /** Byte offset of the def's value; null for a plain term, which has none. */
  unifyStart: number | null;
}

export interface ThmEntry {
  id: number;
  numArgs: number;
  args: Arg[];
  /** Byte offset of the statement: the conclusion, then the hypotheses. */
  unifyStart: number;
}

export interface Decl {
  /** Position in the declaration stream. */
  index: number;
  /** Byte offset of the statement. */
  pos: number;
  cls: DeclClass;
  /** The id within this declaration's own class. */
  num: number;
  /** A def rather than a plain term; meaningless unless `cls` is `TERM`. */
  isDef: boolean;
  /** A theorem rather than an axiom; meaningless unless `cls` is `THM`. */
  isThm: boolean;
  local: boolean;
  /** Null (`isNull`) for a sort or a plain term. */
  proof: StreamIter;
}

/** The label for a declaration, as MM1 source spells it. */
export function declKind(d: Decl): DeclKind {
  switch (d.cls) {
    case CLASS.SORT: return 'sort';
    case CLASS.TERM: return d.isDef ? (d.local ? 'local def' : 'def') : 'term';
    case CLASS.THM: return !d.isThm ? 'axiom' : d.local ? 'theorem' : 'pub theorem';
  }
}

/** The id as it is written when there is no name for it: `s0`, `t12`, `T301`. */
export function declId(d: Decl): string {
  return `${CLASS_PREFIX[d.cls]}${d.num}`;
}

import { nameRef, type NameKind } from './msg.js';

export class MmbError extends Error {
  /** Byte offset the error was detected at, when known. */
  pos: number | undefined;

  constructor(message: string, pos?: number) {
    // The offset is kept beside the message rather than appended to it: it
    // says *where*, which is what the trail in front of a failure is for, and
    // reads there with the rest of the path instead of trailing the sentence.
    super(message);
    this.name = 'MmbError';
    this.pos = pos;
  }
}

/**
 * A binder, or a term's return type: a 64-bit bitfield.
 *
 * Bit 63 marks a bound variable, bits 56-62 are the sort, and bits 0-54 are a
 * bitset of the earlier bound variables this one may depend on (bit 55 is
 * reserved and must be zero, so there are at most 55 bound variables).
 *
 * Held as two 32-bit halves rather than a BigInt: the dependency set splits
 * 32 bits in `depsLo` and 23 in `depsHi`, and set operations work pairwise.
 */
export class Arg {
  lo: number;
  hi: number;

  constructor(lo: number, hi: number) {
    this.lo = lo;
    this.hi = hi;
  }

  get bound(): boolean { return (this.hi & 0x80000000) !== 0; }
  get sort(): number { return (this.hi >>> 24) & 0x7f; }
  get depsLo(): number { return this.lo >>> 0; }
  get depsHi(): number { return this.hi & 0x007fffff; }

  /** True if this argument depends on bound variable `i` (0-based). */
  dependsOn(i: number): boolean {
    return i < 32 ? (this.depsLo & (1 << i)) !== 0
                  : (this.depsHi & (1 << (i - 32))) !== 0;
  }

  /** The indices of the bound variables this argument depends on. */
  deps(): number[] {
    const out: number[] = [];
    for (let i = 0; i < 55; i++) if (this.dependsOn(i)) out.push(i);
    return out;
  }

  eq(other: Arg): boolean { return this.lo === other.lo && this.hi === other.hi; }

  /** A key for grouping consecutive binders that the source wrote together. */
  key(): string { return `${this.lo},${this.hi}`; }
}

/**
 * A cursor over a proof or unify stream.
 *
 * Used as `while (it.step()) { ... it.cmd, it.data, it.at ... }`. The decoded
 * command lands in fields on the cursor rather than in a fresh object, which
 * is 3x faster over a whole library (0.99 ms vs 3.01 ms for peano's 245k
 * commands) — the JS iterator protocol would allocate one result object and
 * one payload object per command, and a proof stream is the hottest loop here
 * by two orders of magnitude. The fields are only valid until the next
 * `step()`; anything that needs to outlive it must copy.
 *
 * Deliberately fused and bounded by `endsAt`, unlike `ProofIter`/`UnifyIter`
 * upstream: those advance no position on error (yielding `Some(Err(..))`
 * forever) and only compare against `ends_at` on the terminating path, so
 * iterating a *null* stream runs off into the following declarations until it
 * meets a stray zero byte and then spins. Here the end of the range, an END
 * command and the first error all latch `done`, so every loop terminates.
 */
export class StreamIter {
  dv: DataView;
  pos: number;
  endsAt: number;
  done: boolean;
  error: MmbError | null;

  /** The current command's opcode. Valid only after a `step()` returned true. */
  cmd = 0;
  /** The current command's immediate, widened to a u32. */
  data = 0;
  /** The byte offset the current command started at. */
  at = 0;

  constructor(dv: DataView, pos: number, endsAt: number) {
    this.dv = dv;
    this.pos = pos;
    this.endsAt = endsAt;
    this.done = false;
    this.error = null;
  }

  /** True if the stream has no commands at all (a sort, or a non-def term). */
  get isNull(): boolean { return this.pos === this.endsAt; }

  /** A fresh cursor over the same range, positioned where this one is. */
  clone(): StreamIter {
    const it = new StreamIter(this.dv, this.pos, this.endsAt);
    it.done = this.done;
    it.error = this.error;
    return it;
  }

  /**
   * Decode the next command into `cmd`/`data`/`at`. Returns false at the end
   * of the stream, on END, and on error — check `error` to tell them apart.
   *
   * This is the only place the `(cmd, data)` packing is decoded: the low 6
   * bits of the leading byte are the opcode, and the high 2 bits select the
   * width of the immediate that follows. `data` is always widened to a u32, so
   * callers never see a BigInt and every id, heap index and statement length
   * is an ordinary number.
   */
  step(): boolean {
    if (this.done || this.pos >= this.endsAt) {
      this.done = true;
      return false;
    }
    const p = this.pos;
    const b = this.dv.getUint8(p);
    const cmd = b & 0x3f;
    if (cmd === 0) {
      // END. The stream is over whether or not it lands exactly on `endsAt`.
      this.done = true;
      return false;
    }
    // The width is known from the leading byte alone, so the bound is checked
    // *before* the immediate is read: a stream truncated mid-command must
    // report an MmbError, not throw a RangeError out of the DataView.
    const w = b & 0xc0;
    const next = p + (w === 0x00 ? 1 : w === 0x40 ? 2 : w === 0x80 ? 3 : 5);
    if (next > this.endsAt) {
      this.done = true;
      this.error = new MmbError('command overruns its stream', p);
      return false;
    }
    this.cmd = cmd;
    this.data = w === 0x00 ? 0
      : w === 0x40 ? this.dv.getUint8(p + 1)
      : w === 0x80 ? this.dv.getUint16(p + 1, true)
      : this.dv.getUint32(p + 1, true);
    this.at = p;
    this.pos = next;
    return true;
  }

  /**
   * The remaining commands as objects. Allocates one per command, so this is
   * for tests, debugging and cold paths — the machine uses `step()`.
   */
  *rest(): Generator<StreamCmd, void, void> {
    while (this.step()) yield { cmd: this.cmd, data: this.data, pos: this.at };
  }
}

/**
 * One entry of the `Nota` table: how a term is printed.
 *
 * `lits` is empty exactly when the notation is a coercion, which prints its
 * single argument transparently at the caller's precedence.
 */
export class Nota {
  termId: number;
  prec: number;
  lits: Lit[];

  constructor(termId: number, prec: number, lits: Lit[]) {
    this.termId = termId;
    this.prec = prec;
    this.lits = lits;
  }

  get isCoercion(): boolean { return this.lits.length === 0; }
}

export class Delimiters {
  /** Byte values after which a token boundary follows. */
  left: Set<number>;
  /** Byte values before which a token boundary precedes. */
  right: Set<number>;

  constructor(left: Set<number>, right: Set<number>) {
    this.left = left;
    this.right = right;
  }

  isLeft(ch: number): boolean { return this.left.has(ch); }
  isRight(ch: number): boolean { return this.right.has(ch); }
}

interface NameTable {
  sorts: number[];
  terms: number[];
  thms: number[];
}

export class MmbFile {
  bytes: Uint8Array;
  dv: DataView;

  numSorts = 0;
  numTerms = 0;
  numThms = 0;
  pTerms = 0;
  pThms = 0;
  pProof = 0;
  pIndex = 0;

  /** Set if the index was malformed; the file stays readable regardless. */
  indexError: string | undefined;
  notaError: string | undefined;

  private names: NameTable | null = null;
  private varNames: { terms: number[]; thms: number[] } | null = null;
  private hypNames: number[] | null = null;
  private notaPtr: number | null = null;
  private delims: Delimiters | null = null;
  /** Whether the file carried an index at all, so "absent" can mean "corrupt". */
  private indexPresent = false;
  private notaCache: Map<number, Nota> | null = null;
  private strCache = new Map<number, string>();
  private strListCache = new Map<number, (string | null)[] | null>();
  // Dense by id: every id below the table count is a real entry, so an array
  // is both faster and tighter than a Map here.
  private termCache: (TermEntry | undefined)[] = [];
  private thmCache: (ThmEntry | undefined)[] = [];

  constructor(bytes: Uint8Array) {
    this.bytes = bytes;
    this.dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  }

  /**
   * Read a u64 that is known to be a file offset or a count, and assert the
   * high word is zero. Every 64-bit field in the format except `arg` is one of
   * these, and any file we can hold in an ArrayBuffer has a zero high word.
   */
  u64at(pos: number): number {
    const hi = this.dv.getUint32(pos + 4, true);
    if (hi !== 0) throw new MmbError('64-bit value exceeds 4GB', pos);
    return this.dv.getUint32(pos, true);
  }

  static parse(input: Uint8Array | ArrayBuffer): MmbFile {
    const bytes = input instanceof Uint8Array ? input : new Uint8Array(input);
    if (bytes.byteLength < 40) throw new MmbError('file shorter than the header');
    const f = new MmbFile(bytes);
    const dv = f.dv;
    if (dv.getUint32(0, true) !== MAGIC) throw new MmbError('bad magic: not an MMB file');
    const version = dv.getUint8(4);
    if (version !== VERSION) throw new MmbError(`unsupported MMB version ${version}`);
    f.numSorts = dv.getUint8(5);
    f.numTerms = dv.getUint32(8, true);
    f.numThms = dv.getUint32(12, true);
    f.pTerms = dv.getUint32(16, true);
    f.pThms = dv.getUint32(20, true);
    f.pProof = dv.getUint32(24, true);
    // `p_index` is read tolerantly, unlike every other header field. The index
    // is advisory -- nothing in it affects verification and a file may have
    // none -- so an unusable pointer means "no index", not "bad file". mm0-c
    // never validates it at all. Being stricter here would reject files the
    // reference verifier accepts, and would contradict the tolerance the index
    // parser below already implements for a malformed index *body*.
    const idxHi = dv.getUint32(36, true);
    f.pIndex = idxHi === 0 ? dv.getUint32(32, true) : 0;
    if (idxHi !== 0) f.indexError = 'index pointer exceeds 4GB; ignoring the index';

    // The same ordering checks the Rust `Header::check` performs. They are
    // loose — the term/thm space bounds there use 4 bytes per entry where the
    // real stride is 8 — but they catch a truncated or scrambled file early.
    const headerSpace = 40 + f.numSorts;
    if (!(headerSpace <= f.pTerms && f.pTerms <= f.pThms && f.pThms <= f.pProof
      && f.pProof <= bytes.byteLength)) {
      throw new MmbError('header pointers are out of order or out of range');
    }
    if (f.pIndex !== 0 && !(f.pProof < f.pIndex && f.pIndex <= bytes.byteLength)) {
      f.indexError = 'index pointer out of range; ignoring the index';
      f.pIndex = 0;
    }
    if (f.numSorts > 128) throw new MmbError('too many sorts');
    if (f.pTerms + 8 * f.numTerms > bytes.byteLength) {
      throw new MmbError('term table overruns the file');
    }
    if (f.pThms + 8 * f.numThms > bytes.byteLength) {
      throw new MmbError('theorem table overruns the file');
    }

    if (f.pIndex !== 0) { f.indexPresent = true; f.parseIndex(); }
    return f;
  }

  /**
   * Advisory facts about the index, for a reader.
   *
   * The index -- declaration names, notation, variable names -- affects nothing
   * in verification, so a file may be missing any part of it, or all of it, and
   * still be perfectly sound. But then a reader is left with `t19` where a name
   * belongs and prefix notation where an operator belongs, with nothing on the
   * page to say why. These notes say why: each is a table that is absent and
   * what its absence costs.
   *
   * Empty when the index is whole, which is the common case.
   */
  indexNotes(): string[] {
    // `Nota` is the one table parsed lazily, so force it before reporting.
    // Its pointer surviving the index walk says nothing about the table behind
    // it, and a report that did not force the parse would call a table present
    // whose every entry failed to read.
    this.notations();
    const nota = this.notaError === undefined ? this.notaPtr : null;
    const tables: [unknown, string][] = [
      [this.names, 'no declaration names (Name table): declarations appear as t19, T4, …'],
      [this.varNames, 'no variable names (VarN table): variables appear as e1, e2, …'],
      [this.hypNames, 'no hypothesis names (HypN table): hypotheses appear by number'],
      [nota, 'no notation (Nota table): expressions appear in prefix form'],
      [this.delims, 'no delimiters (Delm table): every token is spaced apart'],
    ];
    const present = tables.filter(([t]) => t !== null).length;
    // Nothing loaded: a single note, because there are no per-table specifics
    // to give. Why it is empty is the whole story -- a corrupt pointer, or no
    // index at all, which are different facts and read as different notes.
    if (present === 0) {
      if (this.notaError !== undefined) {
        return [`the notation table could not be read: ${this.notaError}`];
      }
      if (this.indexError !== undefined) return [`the index could not be read: ${this.indexError}`];
      if (!this.indexPresent) {
        return ['this file has no index: declaration names, notation and variable names are unavailable'];
      }
      return [];
    }
    // A partial index: the tables are parsed in order and the first bad one
    // stops the rest, so name what was reached and then what is therefore gone.
    const notes: string[] = [];
    if (this.indexError !== undefined) notes.push(`the index is incomplete: ${this.indexError}`);
    if (this.notaError !== undefined) {
      notes.push(`the notation table could not be read: ${this.notaError}`);
    }
    for (const [t, msg] of tables) if (t === null) notes.push(msg);
    return notes;
  }

  // ---- the index ----------------------------------------------------------
  //
  // The index is entirely advisory: nothing in it affects verification, every
  // table is independently optional, and a file may have no index at all. So a
  // malformed index must never make the file unreadable — it is recorded in
  // `indexError` and the affected tables are simply left absent, which the name
  // accessors already handle by falling back to synthetic ids.

  private parseIndex(): void {
    try {
      // The count itself must be in range before it is read: the header check
      // only established that `p_index` is, not that there are eight bytes
      // there. Without this a file truncated exactly at `p_index` raises a
      // RangeError out of the DataView, which the catch below deliberately
      // does not swallow.
      if (this.pIndex + 8 > this.bytes.byteLength) {
        throw new MmbError('index header overruns the file', this.pIndex);
      }
      const numEntries = this.u64at(this.pIndex);
      const base = this.pIndex + 8;
      if (base + 16 * numEntries > this.bytes.byteLength) {
        throw new MmbError('index entry table overruns the file', this.pIndex);
      }
      for (let i = 0; i < numEntries; i++) {
        const e = base + 16 * i;
        const id = this.dv.getUint32(e, true);
        const ptr = this.u64at(e + 8);
        switch (id) {
          case INDEX_NAME: this.parseNames(ptr); break;
          case INDEX_VAR: this.parseVarNames(ptr); break;
          case INDEX_HYP: this.parseHypNames(ptr); break;
          case INDEX_NOTA: this.notaPtr = ptr; break;
          case INDEX_DELM: this.parseDelims(ptr); break;
          default: break; // unknown tables are ignored by design
        }
      }
    } catch (e) {
      if (!(e instanceof MmbError)) throw e;
      this.indexError = e.message;
    }
  }

  /**
   * `Name` is three concatenated arrays of 16-byte entries — sorts, then
   * terms, then thms — each `{p_proof: u64?, p_name: u64?}`. We keep only the
   * name pointers; `p_proof` (a pointer back into the proof stream) is unused
   * here because we walk the stream in order anyway.
   */
  private parseNames(ptr: number): void {
    const total = this.numSorts + this.numTerms + this.numThms;
    if (ptr + 16 * total > this.bytes.byteLength) {
      throw new MmbError('Name table overruns the file', ptr);
    }
    const read = (start: number, n: number): number[] => {
      const out: number[] = new Array(n);
      for (let i = 0; i < n; i++) out[i] = this.u64at(ptr + 16 * (start + i) + 8);
      return out;
    };
    this.names = {
      sorts: read(0, this.numSorts),
      terms: read(this.numSorts, this.numTerms),
      thms: read(this.numSorts + this.numTerms, this.numThms),
    };
  }

  private parseVarNames(ptr: number): void {
    const n = this.numTerms + this.numThms;
    if (ptr + 8 * n > this.bytes.byteLength) {
      throw new MmbError('VarN table overruns the file', ptr);
    }
    const read = (start: number, k: number): number[] => {
      const out: number[] = new Array(k);
      for (let i = 0; i < k; i++) out[i] = this.u64at(ptr + 8 * (start + i));
      return out;
    };
    this.varNames = {
      terms: read(0, this.numTerms),
      thms: read(this.numTerms, this.numThms),
    };
  }

  private parseHypNames(ptr: number): void {
    if (ptr + 8 * this.numThms > this.bytes.byteLength) {
      throw new MmbError('HypN table overruns the file', ptr);
    }
    const out: number[] = new Array(this.numThms);
    for (let i = 0; i < this.numThms; i++) out[i] = this.u64at(ptr + 8 * i);
    this.hypNames = out;
  }

  /**
   * `Delm` is two NUL-terminated byte runs back to back, `left` then `right`.
   * Zero is never a legal delimiter, so the terminator is unambiguous.
   */
  private parseDelims(ptr: number): void {
    const readRun = (p: number): { set: Set<number>; next: number } => {
      const set = new Set<number>();
      while (p < this.bytes.byteLength) {
        const b = this.bytes[p++]!;
        if (b === 0) return { set, next: p };
        set.add(b);
      }
      throw new MmbError('unterminated Delm run', ptr);
    };
    const l = readRun(ptr);
    const r = readRun(l.next);
    this.delims = new Delimiters(l.set, r.set);
  }

  /** A NUL-terminated UTF-8 string at `ptr`, or null if `ptr` is 0. */
  cstr(ptr: number | null | undefined): string | null {
    if (!ptr) return null;
    const hit = this.strCache.get(ptr);
    if (hit !== undefined) return hit;
    let end = ptr;
    while (end < this.bytes.byteLength && this.bytes[end] !== 0) end++;
    const s = decoder.decode(this.bytes.subarray(ptr, end));
    this.strCache.set(ptr, s);
    return s;
  }

  /**
   * `str_list = { num_strs: u64; strs: [p64?<cstr>; num_strs] }`.
   *
   * Cached by pointer. The name accessors below are called once per variable
   * of every rendered expression, and each one wants a single element, so
   * without this a lookup would reparse the whole list and allocate a fresh
   * array every time.
   */
  private strList(ptr: number | null | undefined): (string | null)[] | null {
    if (!ptr) return null;
    const hit = this.strListCache.get(ptr);
    if (hit !== undefined) return hit;
    let out: (string | null)[] | null = null;
    // The count itself has to be in the file before it can be read. The table
    // of entry pointers was bounds-checked, but nothing checked where an entry
    // *points*, and a `DataView` read past the end throws a `RangeError` --
    // which is neither `MmbError` nor `MachineError`, so it would escape every
    // catch between here and the caller. A missing name is `null`, as it is for
    // any other unreadable one.
    if (ptr + 8 > this.bytes.byteLength) {
      this.strListCache.set(ptr, null);
      return null;
    }
    const n = this.u64at(ptr);
    if (ptr + 8 + 8 * n <= this.bytes.byteLength) {
      out = new Array(n);
      for (let i = 0; i < n; i++) out[i] = this.cstr(this.u64at(ptr + 8 + 8 * i));
    }
    this.strListCache.set(ptr, out);
    return out;
  }

  // ---- names --------------------------------------------------------------
  //
  // Every name goes through one of these accessors, and each falls back to the
  // synthetic id that `mm0b_parser` and `mm0-c` use when the index is absent.
  // Nothing should ever format a name any other way: a stripped file must
  // render `T4` consistently rather than showing an id in one pane and a blank
  // in another.

  /**
   * A declaration as a message should name it: by name where the file gives
   * one, and by id where it does not -- a stripped index, or an id past the
   * end of the table. `t19` says which entry is meant; the name says which
   * declaration, and can be followed.
   */
  private ref(kind: NameKind, i: number): string {
    const ptr = kind === 'sort' ? this.names?.sorts[i]
      : kind === 'term' ? this.names?.terms[i] : this.names?.thms[i];
    const n = this.cstr(ptr);
    const tag = kind === 'sort' ? 's' : kind === 'term' ? 't' : 'T';
    return n === null || n === '' ? `${tag}${i}` : nameRef(kind, n);
  }

  sortName(i: number): string {
    return this.cstr(this.names?.sorts[i]) || `s${i}`;
  }
  termName(i: number): string {
    return this.cstr(this.names?.terms[i]) || `t${i}`;
  }
  thmName(i: number): string {
    return this.cstr(this.names?.thms[i]) || `T${i}`;
  }

  /**
   * Variable names for a term. The list runs past the declared arguments to
   * cover dummies, in order of their `Dummy` commands, so it is indexed by the
   * machine's variable counter rather than by argument index.
   */
  /**
   * A declaration's variable names, positional where there is no name.
   *
   * MM1's anonymous marker `_` is treated as absent, as it is for hypotheses:
   * a term declared `(_: type) (_: term x)` printed `lam x _ _`, in which the
   * two underscores are neither distinguishable from each other nor usable to
   * say which argument anything refers to. `e1..en` is the same positional
   * naming the callout already falls back to when a term's arity does not
   * match its recorded names.
   */
  private varName(list: (string | null)[] | null | undefined, i: number): string {
    const s = list?.[i];
    return (s !== undefined && s !== null && s !== '' && s !== '_') ? s : `e${i + 1}`;
  }
  termVarName(tid: number, i: number): string {
    return this.varName(this.strList(this.varNames?.terms[tid]), i);
  }
  thmVarName(tid: number, i: number): string {
    return this.varName(this.strList(this.varNames?.thms[tid]), i);
  }

  /**
   * Hypothesis names, in order of the theorem's `Hyp` commands. MM1's
   * anonymous marker `_` is treated as absent: a column of identical
   * underscores says less than positional `h0`/`h1`.
   */
  hypName(tid: number, i: number): string {
    const s = this.strList(this.hypNames?.[tid])?.[i];
    return (s && s !== '_') ? s : `h${i}`;
  }

  // ---- sorts, terms, theorems --------------------------------------------

  sortData(i: number): number { return this.dv.getUint8(40 + i); }
  /**
   * A sort's modifiers, in the order MM0 writes them: `strict provable sort
   * wff`. They are part of the declaration's syntax, like `pub` and `local`
   * on the others, so they belong with the keyword rather than after the name.
   */
  sortMods(i: number): string[] {
    const d = this.sortData(i);
    const out: string[] = [];
    if ((d & SORT.PURE) !== 0) out.push('pure');
    if ((d & SORT.STRICT) !== 0) out.push('strict');
    if ((d & SORT.PROVABLE) !== 0) out.push('provable');
    if ((d & SORT.FREE) !== 0) out.push('free');
    return out;
  }

  sortIsPure(i: number): boolean { return (this.sortData(i) & SORT.PURE) !== 0; }
  sortIsStrict(i: number): boolean { return (this.sortData(i) & SORT.STRICT) !== 0; }
  sortIsProvable(i: number): boolean { return (this.sortData(i) & SORT.PROVABLE) !== 0; }
  sortIsFree(i: number): boolean { return (this.sortData(i) & SORT.FREE) !== 0; }

  argAt(pos: number): Arg {
    return new Arg(this.dv.getUint32(pos, true), this.dv.getUint32(pos + 4, true));
  }

  /**
   * A term entry: `num_args` u16, then a byte whose high bit is `is_def` and
   * whose low 7 bits are the return sort, then a reserved byte and `p_args`.
   *
   * The unify stream is stored *inline*, right after the `num_args + 1` args
   * (the last of which is the return type) — not behind a pointer. mmb.md
   * describes it as `p32<unify_stream>`, which is wrong; both mm0b_parser's
   * `term_ref` and mm0-c's types.c store it as a suffix.
   */
  /**
   * Cached: the machine looks a term up on every `Term`/`TermSave`/`Unfold`
   * command — about 60k times over peano — and each miss allocates the entry,
   * an args array and one `Arg` per argument. The entry is immutable and
   * shared, so callers must not mutate it.
   */
  term(i: number): TermEntry {
    const hit = this.termCache[i];
    if (hit !== undefined) return hit;
    if (i >= this.numTerms) throw new MmbError(`term id ${i} out of range`);
    const e = this.pTerms + 8 * i;
    const numArgs = this.dv.getUint16(e, true);
    const sortByte = this.dv.getUint8(e + 2);
    const pArgs = this.dv.getUint32(e + 4, true);
    const isDef = (sortByte & 0x80) !== 0;
    // The table itself is bounds-checked at parse, but `p_args` points
    // somewhere else entirely and must be checked per entry, or a corrupted
    // pointer reads past the buffer and the DataView throws a RangeError
    // instead of this reporting a malformed file.
    if (pArgs + 8 * (numArgs + 1) > this.bytes.byteLength) {
      throw new MmbError(`p_args of ${this.ref('term', i)} points outside the file`, pArgs);
    }
    const args: Arg[] = new Array(numArgs);
    for (let k = 0; k < numArgs; k++) args[k] = this.argAt(pArgs + 8 * k);
    const entry: TermEntry = {
      id: i, numArgs, isDef, sort: sortByte & 0x7f, args,
      ret: this.argAt(pArgs + 8 * numArgs),
      // Only a def has a unify stream; for a plain term the bytes that would
      // follow the args belong to whatever comes next and must not be read.
      unifyStart: isDef ? pArgs + 8 * (numArgs + 1) : null,
    };
    this.termCache[i] = entry;
    return entry;
  }

  /** Cached, like `term`; one lookup per `Thm`/`ThmSave` command. */
  thm(i: number): ThmEntry {
    const hit = this.thmCache[i];
    if (hit !== undefined) return hit;
    if (i >= this.numThms) throw new MmbError(`theorem id ${i} out of range`);
    const e = this.pThms + 8 * i;
    const numArgs = this.dv.getUint16(e, true);
    const pArgs = this.dv.getUint32(e + 4, true);
    if (pArgs + 8 * numArgs > this.bytes.byteLength) {
      throw new MmbError(`p_args of ${this.ref('thm', i)} points outside the file`, pArgs);
    }
    const args: Arg[] = new Array(numArgs);
    for (let k = 0; k < numArgs; k++) args[k] = this.argAt(pArgs + 8 * k);
    const entry: ThmEntry = { id: i, numArgs, args, unifyStart: pArgs + 8 * numArgs };
    this.thmCache[i] = entry;
    return entry;
  }

  /**
   * A fresh cursor over the unify stream at `start`, from a `TermEntry`'s
   * `unifyStart` or a `ThmEntry`'s. Fresh per call, because cursors are
   * mutable and entries are shared.
   *
   * The end bound is the end of the file: a unify stream's extent is implied
   * by its own structure (`UTerm` takes exactly `num_args` subexpressions,
   * `URef`/`UDummy` take none) and terminated by END, not framed by a length
   * the way a declaration's proof stream is.
   */
  unifyAt(start: number): StreamIter {
    return new StreamIter(this.dv, start, this.bytes.byteLength);
  }

  // ---- the declaration stream --------------------------------------------

  /**
   * Walk the declaration stream. Each statement's `data` field is the offset
   * from the *start of the statement* to the start of the next one, so the
   * proof stream is the gap between the end of the `(cmd, data)` pair and that
   * boundary.
   *
   * Ids are implicit: a running counter per class, assigned in stream order.
   */
  /**
   * Walk the declaration stream, returning the offset it ended at.
   *
   * The end offset is the `END` command's own position, which is where a
   * stream that stopped short stopped -- a fact about *where*, and so worth
   * having, since a file can be well formed and still declare fewer
   * declarations than its tables promise.
   */
  *decls(): Generator<Decl, number, void> {
    // Driven by a `StreamIter` so that the `(cmd, data)` bit-packing has
    // exactly one decoder. The declaration stream differs from a proof stream
    // only in what `data` means and hence where the next command begins, which
    // is a single assignment to `pos` per iteration.
    const it = new StreamIter(this.dv, this.pProof, this.bytes.byteLength);
    let sortId = 0, termId = 0, thmId = 0;
    let index = 0;
    // Where the last statement finished, which is where `END` sits.
    let last = this.pProof;
    const end = this.bytes.byteLength;
    while (it.step()) {
      const start = it.at;
      const stmtEnd = start + it.data;
      // `it.pos` is just past the (cmd, data) pair, so an in-range statement
      // must reach at least that far.
      if (stmtEnd < it.pos || stmtEnd > end) {
        throw new MmbError('bad statement length', start);
      }

      const local = (it.cmd & STMT_LOCAL) !== 0;
      const base = it.cmd & ~STMT_LOCAL;
      const proof = new StreamIter(this.dv, it.pos, stmtEnd);
      let cls: DeclClass;
      let num: number;
      let isDef = false;
      let isThm = false;
      switch (base) {
        case STMT.SORT:
          cls = CLASS.SORT;
          num = sortId++;
          break;
        case STMT.TERM:
          // `term` and `def` share opcode 0x05; only the term table's is_def
          // bit tells them apart.
          cls = CLASS.TERM;
          num = termId++;
          isDef = this.term(num).isDef;
          break;
        case STMT.AXIOM:
          cls = CLASS.THM;
          num = thmId++;
          break;
        case STMT.THM:
          cls = CLASS.THM;
          num = thmId++;
          isThm = true;
          break;
        default:
          throw new MmbError(`unknown statement command 0x${it.cmd.toString(16)}`, start);
      }
      yield { index: index++, pos: start, cls, num, isDef, isThm, local, proof };
      // Skip the body: `data` measures from the start of the statement, not
      // from the end of its header.
      it.pos = stmtEnd;
      last = stmtEnd;
    }
    if (it.error) throw it.error;
    return last;
  }

  // ---- Nota / Delm --------------------------------------------------------

  /**
   * The `Nota` table, as a Map from term id to the *first* notation for that
   * term -- entries are per notation and in declaration order, and a term may
   * have several, of which MM1 prints with the first.
   *
   * Built in one pass and cached, because it *cannot* be read randomly: the
   * overflow area is a single sequential run of strings, and the nth `0xFF`
   * literal encountered while walking entries in order consumes the nth
   * string. There is no way to start at an arbitrary entry.
   */
  notations(): Map<number, Nota> {
    if (this.notaCache) return this.notaCache;
    const out = new Map<number, Nota>();
    this.notaCache = out;
    if (this.notaPtr === null) return out;
    try {
      const base = this.notaPtr;
      // The header has to be in the file before it can be read: the index entry
      // pointing here was never checked against the file's length, and reading
      // past the end raises a `RangeError`, which the catch below deliberately
      // rethrows -- taking the whole file down over an advisory table.
      if (base + 8 > this.bytes.byteLength) {
        throw new MmbError('Nota table starts outside the file', base);
      }
      const overflowStart = this.u64at(base);
      if (overflowStart < base + 8 || overflowStart > this.bytes.byteLength) {
        throw new MmbError('Nota overflow pointer out of range', base);
      }
      let p = base + 8;
      let ov = overflowStart; // the shared, sequential overflow cursor
      while (p < overflowStart) {
        // Every read below is inside the entry area, which ends where the
        // overflow strings begin. A truncated final entry is a malformed table,
        // not a malformed file: raising `MmbError` leaves the entries already
        // read in the map and records why the rest are missing.
        if (p + 8 > overflowStart) {
          throw new MmbError('Nota entry runs past the overflow area', p);
        }
        const termId = this.dv.getUint32(p, true);
        const prec = this.dv.getUint16(p + 4, true);
        const numLits = this.dv.getUint8(p + 6);
        p += 8;
        if (p + 4 * numLits > overflowStart) {
          throw new MmbError('Nota entry claims more literals than it has', p);
        }
        const lits: Lit[] = [];
        for (let i = 0; i < numLits; i++, p += 4) {
          const b0 = this.dv.getUint8(p);
          if (b0 === NOTA_VAR) {
            lits.push({
              var: this.dv.getUint8(p + 1),
              prec: this.dv.getUint16(p + 2, true),
            });
          } else if (b0 === NOTA_OVERFLOW) {
            const s = this.cstr(ov);
            // advance past this string and its NUL
            while (ov < this.bytes.byteLength && this.bytes[ov] !== 0) ov++;
            ov++;
            lits.push({ const: s ?? '' });
          } else {
            // An inline constant: up to 4 bytes, NUL-padded. A 4-byte token
            // fills the field with no terminator at all.
            let n = 0;
            while (n < 4 && this.dv.getUint8(p + n) !== 0) n++;
            lits.push({ const: decoder.decode(this.bytes.subarray(p, p + n)) });
          }
        }
        // There is one entry per *notation*, not per term, so a term with
        // several is listed once for each and the first is the one MM1 prints
        // with. Note the entry above is parsed either way: skipping the insert
        // must not skip the overflow cursor, or every later constant shifts.
        if (!out.has(termId)) out.set(termId, new Nota(termId, prec, lits));
      }
    } catch (e) {
      if (!(e instanceof MmbError)) throw e;
      this.notaError = e.message;
    }
    return out;
  }

  delimiters(): Delimiters | null { return this.delims; }
}
