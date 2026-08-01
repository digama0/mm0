#!/usr/bin/env python3
"""Disassemble each test's bytes with objdump and diff against gen/disasm.expected.

This is the obligation that pins instruction *length* exactly.  The runtime
harness corroborates length only coarsely -- a wrong-length instruction runs on
into the trampoline's jump and typically faults -- and the proofs cannot check it
at all, since `readMemX k (readRIP k) <bytes>` is a hypothesis a test states
rather than something it establishes.  An independent decoder settling how many
bytes the encoding actually occupies is what closes that gap, and it needs no
execution.

Each test's bytes are disassembled alone, so the expected output is exactly one
instruction consuming exactly the manifest's bytes.  Anything else shows up as a
diff: a short decode leaves trailing bytes that objdump renders as further
instructions, and an encoding the assembler got wrong renders as `(bad)`.

A failure here is a *finding* -- the model and an independent decoder disagree
about an encoding -- not a build regression.

    ./check_disasm.py           diff objdump against the expected listing
    ./check_disasm.py --write   print the actual listing (to seed a new expected)

Override the tool with OBJDUMP if it is not on PATH.
"""

import difflib
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import manifest as M

HERE = Path(__file__).resolve().parent
EXPECTED = HERE / "gen" / "disasm.expected"

OBJDUMP = os.environ.get("OBJDUMP", "objdump")
ARGS = ["-D", "-b", "binary", "-m", "i386:x86-64", "-M", "intel"]

# `   0:\t48 f7 d8             \tneg    rax`, and continuation lines carrying the
# overflow of an instruction longer than seven bytes, which have no text field:
# `   7:\t66 77 88 `.
LINE = re.compile(r"^\s*([0-9a-f]+):\t([0-9a-f ]+?)\s*(?:\t(.*))?$")


def disassemble(code):
    """Decode `code` in isolation; returns a list of `(bytes, text)`."""
    with tempfile.NamedTemporaryFile(suffix=".bin") as f:
        f.write(bytes(code))
        f.flush()
        try:
            out = subprocess.run([OBJDUMP] + ARGS + [f.name],
                                 capture_output=True, text=True, check=True).stdout
        except FileNotFoundError:
            raise SystemExit("%s not found; set OBJDUMP" % OBJDUMP)
        except subprocess.CalledProcessError as e:
            raise SystemExit("objdump failed:\n%s" % e.stderr)

    insns = []
    for line in out.splitlines():
        m = LINE.match(line)
        if not m:
            continue
        _, raw, text = m.groups()
        if text is None:
            if not insns:            # stray bytes before any instruction
                raise SystemExit("unparsable objdump output:\n%s" % out)
            insns[-1][0] += " " + raw.strip()
        else:
            insns.append([raw.strip(), " ".join(text.split())])
    return [(b, t) for b, t in insns]


def listing_expected() -> str:
    rows = ["%s\t%s\t%s" % (t.name, " ".join("%02x" % b for b in t.code), t.disasm)
            for t in M.TESTS]
    return "\n".join([HEADER] + rows) + "\n"


def listing_actual() -> str:
    rows = []
    for t in M.TESTS:
        for raw, text in disassemble(t.code):
            rows.append("%s\t%s\t%s" % (t.name, raw, text))
    return "\n".join([HEADER] + rows) + "\n"


HEADER = ("# test name <TAB> bytes objdump consumed <TAB> objdump's disassembly.\n"
          "# One line per test: more than one means the encoding decoded short.")


def main() -> int:
    if "--write" in sys.argv[1:]:
        sys.stdout.write(listing_actual())
        return 0

    if not EXPECTED.exists():
        raise SystemExit("%s missing; run ./gen.py" % EXPECTED.name)
    want = EXPECTED.read_text()
    got = listing_actual()
    if want == got:
        print("%d encodings agree with objdump" % len(M.TESTS))
        return 0

    sys.stdout.writelines(difflib.unified_diff(
        want.splitlines(True), got.splitlines(True),
        fromfile="expected (from manifest)", tofile="actual (from objdump)"))
    print("\nThe model and an independent decoder disagree about an encoding.\n"
          "This is a finding about x86.mm0 or about the test vector.",
          file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
