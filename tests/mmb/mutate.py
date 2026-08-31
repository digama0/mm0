#!/usr/bin/env python3
"""Regenerates the checked-in .mmb counterexamples from a compiled hol.mmb.

The .mmb files in fail/ and pass/ are checked in, and this script is the
record of where they came from. They are checked in rather than built on
demand because their base is not stable: hol.mmb is itself a build artifact
(`mm0-rs compile examples/hol.mm1 hol.mmb`), and every offset below is a
position in one particular compilation of it. Recompile hol.mm1 and the same
offsets land somewhere else and mean something different -- which is exactly
what `--check` is for.

Most are a single flipped bit, found by mutating hol.mmb at random and
classifying what came out; a bit flip is a blunt instrument, so what each one
actually breaks is written down beside it. The index cases at the end cannot
be reached that way -- a flip in the index body lands in a string far more
often than in a pointer -- so they edit the structure instead.

The folders are the combinations of verdict, because the two verifiers do not
agree and the disagreement is the point:

    fail/        mm0-c (NO_PARSER) rejects, and mm0-js rejects
    fail-index/  mm0-c accepts, mm0-js rejects under `--index`
    pass/        both accept
    run/         older cases, run under a parser build with their own .mm0

`fail-index/` exists because the index is advisory: nothing in it affects
verification, so a verifier is entitled to ignore it however broken it is, and
mm0-c does. Those files are counterexamples for a *reader* rather than a
verifier -- the library verifies and is no longer legible. `pass/no_index` is
the control that keeps the distinction honest: having no index at all is
valid, and must not be confused with having one that is broken.

Usage:
    ./mutate.py [--check] [path/to/hol.mmb]

    (no flag)  overwrite fail/ and pass/ with freshly mutated copies
    --check    mutate in memory and report whether the result still matches
               what is checked in, without writing anything

The suite runs these through `run-np.sh` and `run-mm0-js.sh`; see the README
for what has to be on PATH. To try one by hand:

    gcc mm0-c/main.c -O2 -DNO_PARSER -o mm0-c-np
    ./mm0-c-np tests/mmb/fail/bad_magic.mmb < /dev/null    # rejects

These have no .mm0 companion, so a parser build fails all of them at
`invalid command keyword` before it ever looks at the .mmb -- which is why
they need NO_PARSER rather than merely tolerating it.
"""

import struct
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_BASE = HERE.parent.parent / 'mm0-js' / 'test' / 'hol.mmb'

# Header fields, from mm0-c/mmb.md.
P_THMS = 20    # u32: start of the theorem table
P_INDEX = 32   # u64: start of the index, the one field a reader may ignore


def u32(b, at):
    return struct.unpack_from('<I', b, at)[0]


def set_u64(b, at, v):
    struct.pack_into('<Q', b, at, v)


def flip(at, mask):
    """XOR a byte -- the mutation that found most of these."""
    def go(b):
        b[at] ^= mask
    return go


def put(at, val):
    """Replace a byte outright, for writing a whole opcode."""
    def go(b):
        b[at] = val
    return go


def index_entry(b, name):
    """Offset of the index entry for a table, by its 4-byte id."""
    p_index = u32(b, P_INDEX)
    n = struct.unpack_from('<Q', b, p_index)[0]
    want = struct.unpack('<I', name.encode())[0]
    for i in range(n):
        e = p_index + 8 + 16 * i
        if u32(b, e) == want:
            return e
    raise SystemExit(f'the base file has no {name} table')


# -- structural mutations ---------------------------------------------------
#
# These lie about the file's own metadata rather than its proofs: what is
# being tested is how a reader survives bad structure, not bad reasoning.

def bad_args_pointer(b):
    """`syl` claims 8195 arguments, so its argument array leaves the file.

    A theorem table entry is `{num_args: u16, reserved: u16, p_args: u32}`.
    `syl` is entry 1 and really has 3 arguments, so the high byte of its
    `num_args` is zero; setting bit 5 of that byte makes it 0x2003. `p_args`
    is untouched and still points at a real argument list -- it is the length
    that runs off the end, which is why mm0-c reports it as a bad args
    pointer rather than as a bad count.
    """
    at = u32(b, P_THMS) + 8 * 1 + 1
    b[at] ^= 0x20


def no_index(b):
    """No index at all: `p_index` is null.

    Wholly legal -- the index is advisory and a file may have none -- and the
    library still verifies. Every name falls back to its id, so declarations
    read `T0`, `t0`, `s0` and variables read `e1`, and there is no notation.
    """
    set_u64(b, P_INDEX, 0)


def bad_index_pointer(b):
    """An index that cannot be read: `p_index` lands 3 bytes from the end.

    Indistinguishable from `no_index` in what survives, and different in what
    can be *said* about it: here the file claims an index and the claim is
    unusable, which is a fact worth reporting rather than one to infer from
    names that turned into numbers.
    """
    set_u64(b, P_INDEX, len(b) - 3)


def partial_index(b):
    """One index table fails and takes the later ones with it.

    The tables are parsed in the order the entry list gives them, which here
    is Name, VarN, HypN, Nota, Delm. Breaking VarN's pointer keeps Name --
    every declaration is still named -- and loses Nota and Delm, so the whole
    library silently renders in prefix form. That is the case worth having:
    total loss is obvious, and this one is not.
    """
    set_u64(b, index_entry(b, 'VarN') + 8, len(b) - 2)


# -- the cases --------------------------------------------------------------
#
# `note` says what the file is for, which is not always what mm0-c calls it:
# these were cut to exercise a *reader*, and several land on a different
# check than the one they were aimed at.

CASES = [
    # The file cannot be read at all, so there is no list to show.
    ('fail', 'bad_magic', flip(0, 0x01),
     'the magic number, so nothing parses'),
    # The declaration walk breaks partway: some of the file is still readable,
    # and a reader should get what was read rather than nothing.
    ('fail', 'bad_stream', flip(205, 0xff),
     'the declaration walk stops partway'),
    # One declaration fails its own checks and the rest verify -- the case a
    # whole-file verdict cannot express.
    ('fail', 'one_bad_decl', flip(290, 0x01),
     'one declaration fails, the rest verify'),
    # A unify run fails, which has its own pane and its own error.
    ('fail', 'unify_mismatch', flip(260, 0x10),
     'a unify run fails against its header'),
    # The failure trail has four shapes and the four files above only produce
    # two of them, so each of the others gets a file.
    ('fail', 'bad_arg', flip(284, 0x04),
     'a binder fails: `arg 0: ...`'),
    ('fail', 'bad_return', flip(124, 0x20),
     'ret.sort disagrees with td.sort'),
    # The flipped bit is `is_def` in the term table, which is the only thing
    # that tells a `term` from a `def`: the statement keeps the proof stream it
    # was written with, and a `term` is not allowed one. So this fails twice --
    # once for the stream that should not be there, and once at the `Unfold`
    # that expected a def.
    ('fail', 'bad_step', flip(138, 0x80),
     'a proof step fails mid-proof, not at its header'),
    ('fail', 'underflow', flip(152, 0x02),
     'a step wants more stack than there is'),
    # Not one failure but a hundred: the list, the failed-only filter and the
    # error modal all behave differently at that size.
    ('fail', 'many_bad', flip(120, 0x01),
     'most of the file fails'),
    # One declaration fails more times than a run will carry on past, so the
    # count reported is a floor: `173+ failures`.
    ('fail', 'capped', flip(1548, 0x01),
     'a declaration hits the failure cap'),
    # A disjoint-variable violation: the check a run carries on past rather
    # than stopping at.
    ('fail', 'disjoint', flip(4696, 0x01),
     'a binder depends on what it may not'),
    # The unify stream runs out with the target only partly matched, so the
    # failure is after the last command rather than at one of them.
    ('fail', 'unmatched', flip(140, 0x20),
     'a unify run ends with work left'),
    # A stack element of the wrong kind: `|- e` where `e` was wanted.
    ('fail', 'wrong_kind', flip(1904, 0x01),
     'a proof where an expression belongs'),
    # A command the format does not define, which has no name to print.
    ('fail', 'unknown_op', flip(10958, 0xff),
     'an unrecognised proof command'),
    ('fail', 'pure_sort', flip(40, 0x01),
     'a term in a pure sort'),
    # Nothing is *wrong* here by mm0-js's reckoning: every check passes and
    # the file is still not to be trusted, which it reports as a warning
    # rather than a failure. mm0-c has no `Sorry` opcode at all, so to it this
    # is a bad stack slot -- hence fail/ despite the softer reading.
    # `Sorry` is one byte, so it is written over a command rather than flipped.
    ('fail', 'uses_sorry', put(11688, 0x20),
     'a proof admits its goal'),
    # A declaration whose argument list cannot be read. The walk still lists
    # every declaration, so this is `one_bad_decl` in shape -- but mm0-js
    # raises it as an `MmbError` while reading the table rather than a
    # `MachineError` while checking a proof, and its `verify` catches only the
    # latter, so the whole file becomes unopenable.
    ('fail', 'bad_args_pointer', bad_args_pointer,
     'a declaration has an unreadable arg list'),
    # Valid by every verifier's reckoning, and it really is valid: a file may
    # have no index, and mm0-c accepts one without comment. It is here as the
    # control for the two below -- the thing they must not be confused with.
    ('pass', 'no_index', no_index,
     'no index at all: every name falls back to its id'),
    # Accepted by mm0-c, rejected by mm0-js under `--index`. Nothing is wrong
    # with the proofs; the file claims an index and the claim is unusable,
    # which no verifier is obliged to notice because the index is advisory.
    ('fail-index', 'bad_index_pointer', bad_index_pointer,
     'an index that cannot be read: names fall back to ids, and there is a reason'),
    ('fail-index', 'partial_index', partial_index,
     'one index table fails and takes the later ones with it'),
]


def main():
    args = sys.argv[1:]
    check = '--check' in args
    if check:
        args.remove('--check')
    base_path = Path(args[0]) if args else DEFAULT_BASE
    if not base_path.exists():
        raise SystemExit(f'{base_path} not found;'
                         ' build it with `mm0-rs compile examples/hol.mm1 <path>`')
    base = base_path.read_bytes()
    print(f'base: {base_path} ({len(base)} bytes)')

    stale = 0
    for folder, name, mutate, note in CASES:
        b = bytearray(base)
        mutate(b)
        out = HERE / folder / f'{name}.mmb'
        if check:
            # Say which way it differs: a missing file is a different problem
            # from a file that no longer matches its recipe.
            if not out.exists():
                print(f'  {folder}/{name}: MISSING')
                stale += 1
            elif out.read_bytes() != bytes(b):
                print(f'  {folder}/{name}: STALE -- the base has changed under it')
                stale += 1
            else:
                print(f'  {folder}/{name}: ok')
        else:
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_bytes(bytes(b))
            print(f'  {folder}/{name}.mmb -- {note}')

    if check and stale:
        print(f'\n{stale} file(s) no longer match. Either this is a different'
              ' hol.mmb than\nthe one they were cut from -- in which case the'
              ' offsets above now mean\nsomething else and want rechecking --'
              ' or they were edited by hand.')
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
