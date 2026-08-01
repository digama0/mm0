"""Single source of truth for the x86 spec test suite.

Each entry describes one test: the instruction bytes, the register state loaded
before the step, and everything that must be observable after it.  `gen.py`
turns this into `x86_tests.mm0`, the contract that the hand-written proofs in
`x86_tests.mm1` are checked against by `mm0-c`.  Change a value here and the
regenerated contract stops matching the proofs, and the existing verifier says
so -- there is no separate consistency check to write or to forget to run.

Order is canonical.  mm0-c requires the `.mm0` and the `.mmb` to agree on
relative declaration order, so `x86_tests.mm1` must prove the tests in the order
they appear below.

Every test asserts `readRIP k2 = rip +_64 len(code)` implicitly; that is the
instruction-length check and it is not optional, so it is not spelled out in the
`post` list.
"""

from dataclasses import dataclass


# ---------------------------------------------------------------------------
# Post-state clauses
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Reg:
    """`readReg k2 <reg> = <value>` -- a register holds a concrete value."""
    reg: str
    value: int


@dataclass(frozen=True)
class RegsSame:
    """`readReg k2 r = readReg k r` at a symbolic `r` -- no register changed.

    Stronger than listing every register, and it is what caught the opcode-90
    bug: the pre-fix model's `nop` cleared `RAX[63:32]`.
    """


@dataclass(frozen=True)
class FlagsSame:
    """`readFlags k2 = readFlags k` -- no flag changed."""


@dataclass(frozen=True)
class Flag:
    """`CF (readFlags k2)`, or `~CF (readFlags k2)` when `on` is false."""
    flag: str
    on: bool


@dataclass(frozen=True)
class FlagSame:
    """`(ZF (readFlags k2) <-> ZF (readFlags k))` -- this flag is untouched."""
    flag: str


@dataclass(frozen=True)
class Test:
    name: str       # theorem name, and the harness's name for the case
    disasm: str    # the instruction, as a disassembler would print it
    doc: str        # doc comment on the generated theorem
    code: tuple     # instruction bytes
    post: tuple     # observables after the step, in statement order
    pre: tuple = () # (register, value) loaded before the step


ALL_ONES = 0xffffffffffffffff

#: Registers in x86 encoding order.  `x86.mm0` names only the first eight, so a
#: row needing `R8`..`R15` in a *statement* needs those defs added upstream
#: first; `gen.py` rejects them until then.  `RSP` is rejected outright: the
#: runtime harness commandeers the stack, so it can neither load nor read it.
REGS = ("RAX", "RCX", "RDX", "RBX", "RSP", "RBP", "RSI", "RDI",
        "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15")
REGS_NAMED_IN_MM0 = 8
RSP = 4

#: The flags `x86.mm0` models, and their `rflags` bit positions.  `PF` and `AF`
#: are deliberately absent from the model, so the harness must not check them.
FLAG_BIT = {"CF": 0, "ZF": 6, "SF": 7, "OF": 11}
FLAGS = tuple(FLAG_BIT)

#: Value loaded into every register a test does not name.  Distinct per register
#: so a transposed slot in the trampoline shows up, high bits set so a 32 bit
#: truncation shows up, and the low byte identifies the register.
def filler(i: int) -> int:
    return 0xa5a5a5a5a5a50000 | (i << 8) | i


TESTS = [
    Test(
        name="test_nop",
        disasm="nop",
        code=(0x90,),
        doc="`nop` advances RIP by one and changes nothing else.",
        post=(RegsSame(), FlagsSame()),
    ),
    Test(
        name="test_stc",
        disasm="stc",
        code=(0xf9,),
        doc="`stc` sets CF, leaves the other flags and all registers alone, and "
            "advances RIP by one.",
        post=(RegsSame(), Flag("CF", True),
              FlagSame("ZF"), FlagSame("SF"), FlagSame("OF")),
    ),
    # The four unops, in the order x86.mm0 lists them.  Each is at the boundary
    # value that makes the most flags observable, and each pins CF: `inc` and
    # `dec` must leave it alone (the SDM's defining quirk of those two), `not`
    # must leave every flag alone, and `neg` must set it.
    Test(
        name="test_inc_rax_minus1",
        disasm="inc rax",
        code=(0x48, 0xff, 0xc0),
        doc="`inc rax` with `rax = -1`: the result is zero, so `ZF` is set and "
            "`SF` clear; there is a carry out but no signed overflow, and `inc` "
            "discards the carry -- `CF` comes back exactly as it went in.",
        pre=(("RAX", ALL_ONES),),
        post=(Reg("RAX", 0), FlagSame("CF"),
              Flag("ZF", True), Flag("SF", False), Flag("OF", False)),
    ),
    Test(
        name="test_dec_rax_zero",
        disasm="dec rax",
        code=(0x48, 0xff, 0xc8),
        doc="`dec rax` with `rax = 0`: wraps to `-1`, so `ZF` is clear and `SF` "
            "set.  The borrow is discarded for the same reason as `inc`'s carry, "
            "so `CF` is preserved rather than set.",
        pre=(("RAX", 0),),
        post=(Reg("RAX", ALL_ONES), FlagSame("CF"),
              Flag("ZF", False), Flag("SF", True), Flag("OF", False)),
    ),
    Test(
        name="test_not_rax_minus1",
        disasm="not rax",
        code=(0x48, 0xf7, 0xd0),
        doc="`not rax` with `rax = -1`: the result is zero and no flag moves at "
            "all.  `not` is the one unop the model routes straight to `writeEA`, "
            "with neither `writeResultFlags` nor `eraseFlags`, so the whole flag "
            "word is asserted equal rather than flag by flag.",
        pre=(("RAX", ALL_ONES),),
        post=(Reg("RAX", 0), FlagsSame()),
    ),
    Test(
        name="test_neg_rax_minus1",
        disasm="neg rax",
        code=(0x48, 0xf7, 0xd8),
        doc="`neg rax` with `rax = -1`: RIP advances by three, `rax` becomes 1, "
            "`CF` is set and `ZF`/`SF`/`OF` are clear.  `-1` is the operand that "
            "makes all four flags observable at once; `OF` is the interesting "
            "one, since the model computes it as `MSB a /\\ MSB (-a)`.",
        pre=(("RAX", ALL_ONES),),
        post=(Reg("RAX", 1), Flag("CF", True),
              Flag("ZF", False), Flag("SF", False), Flag("OF", False)),
    ),

    # The register-to-register ALU binops, `48 <8n+3> C1` (`rax` <- `rax` op `rcx`).
    # `add`/`sub` are the same arithmetic as `inc`/`dec` but *publish* the carry
    # instead of discarding it, so the CF column is what tells the two pairs apart.
    Test(
        name="test_add_rax_rcx",
        disasm="add rax,rcx",
        code=(0x48, 0x03, 0xc1),
        doc="`add rax, rcx` with `rax = -1, rcx = 1`: wraps to zero.  Same "
            "arithmetic as `inc rax` at `-1`, but `add` publishes the carry, so "
            "`CF` is set here where `inc` left it alone.",
        pre=(("RAX", ALL_ONES), ("RCX", 1)),
        post=(Reg("RAX", 0), Flag("CF", True),
              Flag("ZF", True), Flag("SF", False), Flag("OF", False)),
    ),
    Test(
        name="test_or_rax_rcx",
        disasm="or rax,rcx",
        code=(0x48, 0x0b, 0xc1),
        doc="`or rax, rcx` with `rax = 0, rcx = -1`: the logical binops clear `CF` "
            "and `OF` outright rather than computing them, and the result's sign "
            "bit is set.",
        pre=(("RAX", 0), ("RCX", ALL_ONES)),
        post=(Reg("RAX", ALL_ONES), Flag("CF", False),
              Flag("ZF", False), Flag("SF", True), Flag("OF", False)),
    ),
    Test(
        name="test_and_rax_rcx",
        disasm="and rax,rcx",
        code=(0x48, 0x23, 0xc1),
        doc="`and rax, rcx` with `rax = -1, rcx = 0`: masks everything off.",
        pre=(("RAX", ALL_ONES), ("RCX", 0)),
        post=(Reg("RAX", 0), Flag("CF", False),
              Flag("ZF", True), Flag("SF", False), Flag("OF", False)),
    ),
    Test(
        name="test_sub_rax_rcx",
        disasm="sub rax,rcx",
        code=(0x48, 0x2b, 0xc1),
        doc="`sub rax, rcx` with `rax = 0, rcx = 1`: borrows to `-1`.  Same "
            "arithmetic as `dec rax` at `0`, but `sub` publishes the borrow, so "
            "`CF` is set here where `dec` left it alone.",
        pre=(("RAX", 0), ("RCX", 1)),
        post=(Reg("RAX", ALL_ONES), Flag("CF", True),
              Flag("ZF", False), Flag("SF", True), Flag("OF", False)),
    ),
    Test(
        name="test_cmp_rax_rcx",
        disasm="cmp rax,rcx",
        code=(0x48, 0x3b, 0xc1),
        doc="`cmp rax, rcx` with `rax = 0, rcx = 1`: the same flags as `sub`, but "
            "`rax` is left alone.  The model's `cmp` clause ends in "
            "`k2 = writeResultFlags ...` with no `writeEA` at all, so this is the "
            "test that would catch a stray write-back.",
        pre=(("RAX", 0), ("RCX", 1)),
        post=(Reg("RAX", 0), Flag("CF", True),
              Flag("ZF", False), Flag("SF", True), Flag("OF", False)),
    ),
    Test(
        name="test_xor_rax_rcx",
        disasm="xor rax,rcx",
        code=(0x48, 0x33, 0xc1),
        doc="`xor rax, rcx` with two interleaved byte patterns: every bit "
            "differs, so the result is all ones.  The first test whose "
            "arithmetic is a real bitwise evaluation rather than an algebraic "
            "identity -- the proof computes it digit by digit with x86.mm1's "
            "`to-bitop`.",
        pre=(("RAX", 0xff00ff00ff00ff00), ("RCX", 0x00ff00ff00ff00ff)),
        post=(Reg("RAX", ALL_ONES), Flag("CF", False),
              Flag("ZF", False), Flag("SF", True), Flag("OF", False)),
    ),
    Test(
        name="test_neg_rax_intmin",
        disasm="neg rax",
        code=(0x48, 0xf7, 0xd8),
        doc="`neg rax` at `INT_MIN`.  The *only* operand at which `neg` sets OF, "
            "and what makes the model's `MSB a /\\ MSB (-a)` the right formula "
            "rather than a suspicious-looking conjunction: `INT_MIN` is the fixed "
            "point of negation, so it is the one value whose negation keeps the "
            "sign bit.",
        pre=(("RAX", 0x8000000000000000),),
        post=(Reg("RAX", 0x8000000000000000), Flag("CF", True),
              Flag("ZF", False), Flag("SF", True), Flag("OF", True)),
    ),
    Test(
        name="test_add_eax_ecx",
        disasm="add eax,ecx",
        code=(0x03, 0xc1),
        doc="`add eax, ecx` at 32 bits, which does two things at once, both the "
            "shape of bugs the audit already found: the operands are *truncated* "
            "to 32 bits before the addition, and the result goes back through "
            "`writeReg32`, a full `setReg` -- so the upper half of `rax` is "
            "**cleared**, not preserved.  The flags are the 32 bit boundary: "
            "`INT_MAX + 1` sets OF but leaves CF clear, since it does not carry "
            "out of 32 bits.",
        pre=(("RAX", 0xffffffff7fffffff), ("RCX", 0xffffffff00000001)),
        post=(Reg("RAX", 0x80000000), Flag("CF", False),
              Flag("ZF", False), Flag("SF", True), Flag("OF", True)),
    ),
    Test(
        name="test_mul_rcx",
        disasm="mul rcx",
        code=(0x48, 0xf7, 0xe1),
        doc="`mul rcx` with `rax = rcx = 2^32`: the product is exactly `2^64`, so "
            "`rax` comes back zero, `rdx` one, and CF and OF are set because the "
            "result does not fit in the destination.  Regression test for the "
            "audit finding that the model left `mul`'s flags untouched -- before "
            "the fix `CF (readFlags k2)` was not provable at all, while the "
            "hardware sets it.  Only CF and OF are asserted: `eraseFlags` leaves "
            "ZF and SF genuinely unconstrained, which is right, since the SDM "
            "calls them undefined.",
        pre=(("RAX", 0x100000000), ("RCX", 0x100000000)),
        post=(Reg("RAX", 0), Reg("RDX", 1), Flag("CF", True), Flag("OF", True)),
    ),
    Test(
        name="test_lea_rax_abs",
        disasm="lea rax,ds:0x12345678",
        code=(0x49, 0x8d, 0x04, 0x25, 0x78, 0x56, 0x34, 0x12),
        doc="`lea rax, [0x12345678]` with REX.B set.  The prefix addresses "
            "nothing: a SIB base field of `101` with `mod=00` is "
            "disp32-with-no-base whatever REX.B says, which is the behaviour "
            "audit finding A6 corrected -- pre-fix the model read these bytes as "
            "`[r13]` and consumed four rather than eight, so both the result and "
            "the instruction length would be wrong.  `lea` computes the address "
            "without dereferencing it, so this needs no mapped memory.",
        post=(Reg("RAX", 0x12345678), FlagsSame()),
    ),
]
