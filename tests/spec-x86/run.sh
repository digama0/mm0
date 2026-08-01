#!/bin/sh
# Run every obligation the spec test suite has.  Each check fails for exactly one
# reason, and that reason is what the label says -- the point of splitting them.
#
#   gen.py --check   the committed generated files are stale w.r.t. the manifest
#   mm0-rs compile   a proof is broken
#   mm0-c            proofs and test vectors disagree, or a proof leaked an axiom
#   check_disasm.py  the model and an independent decoder disagree about an encoding
#   harness x2       the model and a runtime oracle disagree
#
# The last two are *findings*, not regressions, and are reported as such.
#
# There are two runtime oracles, run as independent signals:
#
#   native      the silicon.  Needs an x86-64 host.  The only one whose verdict
#               is evidence about a real CPU.
#   emulated    qemu-x86_64 (or $EMULATOR).  A second *implementation* of x86
#               semantics, not a reference: a disagreement means the model and
#               the emulator differ and either may be wrong.  Available on any
#               host, which is the point.
#
# Every check degrades on its own.  A missing emulator, cross-compiler or x86-64
# host skips that one signal and leaves the rest of the run intact.
#
# STRICT=1 turns a skipped oracle into a failure.  CI sets it, so that "the
# emulator is installed" is enforced rather than assumed -- without it a runner
# that lost qemu would keep reporting green on one oracle instead of two.
#
# Output: on its own `./run.sh` prints a verbose log, because a failure here is
# usually a finding to read rather than a red light. TERSE=1 switches to the
# one-line-per-check form that tests/run-tests.sh uses, showing the detail only
# when something fails, so the suite looks like the rest of the test tree when
# run from there.
#
# Override with MM0_RS / MM0_C / OBJDUMP / CC / XCC / EMULATOR.

cd "$(dirname "$0")" || exit 2
MM0_RS=${MM0_RS:-mm0-rs}
MM0_C=${MM0_C:-mm0-c}
TMP=$(mktemp -d) || exit 2
trap 'rm -rf "$TMP"' EXIT

CC=${CC:-cc}
XCC=${XCC:-x86_64-linux-gnu-gcc}
EMU=${EMULATOR:-qemu-x86_64}
EMU_NAME=$(basename "$EMU")
HOST=$(uname -m)

rc=0
ran_oracle=0

esc=$(printf '\033')
red="$esc[0;31m"; green="$esc[0;32m"; cyan="$esc[0;36m"
white="$esc[0;97m"; off="$esc[0m"

# step <short> <label> <cmd>...
step() {
	short=$1 label=$2
	shift 2
	if [ -z "$TERSE" ]; then
		printf '== %s\n' "$label"
		if "$@"; then return 0; fi
		rc=1
		return 1
	fi
	printf 'test spec-x86/%s%s%s: ' "$white" "$short" "$off"
	if out=$("$@" 2>&1); then
		note=$(printf '%s\n' "$out" |
			sed -n 's/^\([0-9][0-9]* \(tests\|encodings\)\).*/ (\1)/p' | head -1)
		printf '%s%s\n' "${green}ok${off}" "$note"
		return 0
	fi
	printf '%s\n' "${red}failed${off}"
	rc=1
	printf -- '---------------------------------------\n%s\n' "$out"
	printf -- '---------------------------------------\n\n'
	return 1
}

# skip <short> <label> <reason>
skip() {
	if [ -n "$STRICT" ]; then
		rc=1
		if [ -z "$TERSE" ]; then
			printf '== %s -- MISSING (%s), and STRICT is set\n' "$2" "$3"
		else
			printf 'test spec-x86/%s%s%s: %s (%s)\n' \
				"$white" "$1" "$off" "${red}missing${off}" "$3"
		fi
	elif [ -z "$TERSE" ]; then
		printf '== %s -- SKIPPED (%s)\n' "$2" "$3"
	else
		printf 'test spec-x86/%s%s%s: %s (%s)\n' \
			"$white" "$1" "$off" "${cyan}skipped${off}" "$3"
	fi
}

step manifest "manifest -> generated files are up to date" ./gen.py --check

step proofs "proofs compile" "$MM0_RS" compile x86_tests.mm1 "$TMP/x86_tests.mmb"

if [ -f "$TMP/x86_tests.mmb" ]; then
	"$MM0_RS" join x86_tests.mm0 > "$TMP/join.mm0" &&
		step contract "proofs discharge the contract" \
			sh -c "\"$MM0_C\" \"$TMP/x86_tests.mmb\" < \"$TMP/join.mm0\"" &&
		[ -n "$TERSE" ] || echo "   contract VERIFIED"
fi

step objdump "encodings agree with objdump" ./check_disasm.py

# ---------------------------------------------------------------------
# The two runtime oracles, run and reported independently.
#
# They are not redundant.  Native is the only one that is evidence about a real
# CPU; emulated is the only one available on a non-x86 developer machine.  When
# both run they also cross-check the two implementations against each other
# through the model: native passing while emulated fails points at the emulator
# (or at a test that is under-specified), not at x86.mm0.
#
# Each degrades independently -- a missing toolchain or emulator skips that
# signal and leaves the other one's verdict alone.
# ---------------------------------------------------------------------

# run_oracle <short> <label> <runner...> -- <binary> <oracle> <mode>
run_oracle() {
	short=$1 label=$2
	shift 2
	if [ -z "$TERSE" ]; then
		printf '== %s\n' "$label"
		"$@" || rc=1
	else
		step "$short" "$label" "$@" || :
	fi
	ran_oracle=1
}

if [ "$HOST" != x86_64 ]; then
	skip native "native oracle" "host is $HOST, not x86_64"
elif step native-build "harness builds (native)" \
	$CC -O1 -Wall -Wextra -o "$TMP/h-native" harness.c trampoline.S
then
	run_oracle native "native oracle: the silicon" "$TMP/h-native" hardware native
fi

if ! command -v "$EMU" >/dev/null 2>&1; then
	skip emulated "emulated oracle" "$EMU_NAME not found"
elif [ "$HOST" = x86_64 ] && [ -f "$TMP/h-native" ]; then
	# Same binary; the host loader works under qemu-user on an x86-64 host.
	run_oracle emulated "emulated oracle: $EMU_NAME" \
		"$EMU" "$TMP/h-native" "$EMU_NAME" emulated
elif ! command -v "$XCC" >/dev/null 2>&1; then
	skip emulated "emulated oracle" "$XCC not found"
elif step emulated-build "harness builds (static, for $EMU_NAME)" \
	$XCC -O1 -Wall -Wextra -static -o "$TMP/h-emu" harness.c trampoline.S
then
	run_oracle emulated "emulated oracle: $EMU_NAME" \
		"$EMU" "$TMP/h-emu" "$EMU_NAME" emulated
fi

if [ "$ran_oracle" = 0 ]; then
	echo "!! no runtime oracle available: the model was proved and disassembled," >&2
	echo "!! but never executed.  Install $EMU_NAME, or run on x86-64." >&2
fi

exit $rc
