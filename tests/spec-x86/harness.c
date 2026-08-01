/* Runtime half of the x86 spec test suite: run each instruction on the silicon
 * and check it against what the manifest -- and hence x86_tests.mm0 -- says.
 *
 * A failure here is a *finding*, not a regression: the model and the hardware
 * disagree about an instruction, and one of them is wrong.  The exit status
 * distinguishes that (1) from the harness itself being broken (2).
 *
 * Two things this deliberately does not do:
 *
 *   - It never recomputes an expected value.  Everything comes out of
 *     gen/cases.inc.  A recomputation would be a second implementation of the
 *     semantics, and would eventually grow the same bug as the first.
 *   - It never checks something the specification does not assert.  A register
 *     in neither `reg_fixed` nor `reg_same` is left alone: x86.mm0 says nothing
 *     about it, so a mismatch would not be evidence of anything.
 *
 * Each case runs in a forked child, so a fault is a test result rather than the
 * end of the run -- which is also what will let tier 4 (`ud2`, division by
 * zero, writes to unmapped pages) be expected-signal tests rather than
 * exclusions.
 */

#define _GNU_SOURCE
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

#if !defined(__x86_64__) || !defined(__linux__)
#error "the runtime half of this suite is x86-64 Linux only"
#endif

struct x86_state {
	uint64_t r[16];
	uint64_t rflags;
};

void x86_run_case(const struct x86_state *in, struct x86_state *out, void *code);
extern char x86_epilogue[];

/* The flags x86.mm0 models.  PF and AF are absent from the model on purpose, so
 * checking them here would be checking something the specification never
 * claimed -- see the parity finding in the audit. */
#define FLAG_CF (1u << 0)
#define FLAG_ZF (1u << 6)
#define FLAG_SF (1u << 7)
#define FLAG_OF (1u << 11)
#define FLAGS_MODELLED (FLAG_CF | FLAG_ZF | FLAG_SF | FLAG_OF)

/* Bit 1 reads as 1; IF stays set (user mode `popfq` ignores it anyway).  TF and
 * DF must stay clear or the harness breaks rather than the test. */
#define RFLAGS_BASE 0x202u

/* Each case runs under both, so that "flag unchanged" is a real check in both
 * directions rather than only for one polarity. */
static const uint64_t SEEDS[] = {RFLAGS_BASE, RFLAGS_BASE | FLAGS_MODELLED};
#define NSEEDS (sizeof SEEDS / sizeof SEEDS[0])

#define RSP_INDEX 4

static const char *const REG_NAME[16] = {
	"rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
	"r8",  "r9",  "r10", "r11", "r12", "r13", "r14", "r15",
};

static const struct { unsigned bit; const char *name; } FLAG_NAME[] = {
	{FLAG_CF, "CF"}, {FLAG_ZF, "ZF"}, {FLAG_SF, "SF"}, {FLAG_OF, "OF"},
};
#define NFLAGS (sizeof FLAG_NAME / sizeof FLAG_NAME[0])

typedef struct {
	const char *name;
	const char *disasm;
	const uint8_t *code;
	size_t code_len;
	uint64_t reg_in[16];
	unsigned reg_fixed;	/* registers pinned to reg_out[] */
	uint64_t reg_out[16];
	unsigned reg_same;	/* registers that must come back unchanged */
	unsigned flag_fixed;	/* flags pinned to flag_val */
	unsigned flag_val;
	unsigned flag_same;	/* flags that must come back unchanged */
} test_case;

#include "gen/cases.inc"

/* ------------------------------------------------------------------ */

static void die(const char *what)
{
	perror(what);
	exit(2);
}

/* The instruction under test, followed by `jmp *[rip+0]; .quad x86_epilogue`.
 * The indirect form avoids needing the buffer within rel32 of the epilogue, and
 * needs no scratch register. */
static void *make_code(const uint8_t *code, size_t n)
{
	static const uint8_t jmp_indirect[] = {0xff, 0x25, 0x00, 0x00, 0x00, 0x00};
	uint64_t target = (uint64_t)(uintptr_t)x86_epilogue;
	uint8_t *p = mmap(NULL, 4096, PROT_READ | PROT_WRITE,
			  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
	if (p == MAP_FAILED)
		die("mmap");
	memcpy(p, code, n);
	memcpy(p + n, jmp_indirect, sizeof jmp_indirect);
	memcpy(p + n + sizeof jmp_indirect, &target, sizeof target);
	if (mprotect(p, 4096, PROT_READ | PROT_EXEC))
		die("mprotect");
	return p;
}

/* Run one case in a child.  Returns 0 on a clean run, or the signal number if
 * the child died -- which for tiers 1-3 means the instruction faulted, and is
 * itself a finding. */
static int run_child(const test_case *c, const struct x86_state *in,
		     struct x86_state *out)
{
	void *code = make_code(c->code, c->code_len);
	pid_t pid = fork();
	int status;

	if (pid < 0)
		die("fork");
	if (pid == 0) {
		x86_run_case(in, out, code);
		_exit(0);
	}
	if (waitpid(pid, &status, 0) < 0)
		die("waitpid");
	munmap(code, 4096);

	if (WIFSIGNALED(status))
		return WTERMSIG(status);
	if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
		fprintf(stderr, "child exited %d\n", WEXITSTATUS(status));
		exit(2);
	}
	return 0;
}

/* Report every disagreement, not just the first: which registers went wrong
 * together is usually what identifies the cause. */
static int compare(const test_case *c, const struct x86_state *in,
		   const struct x86_state *out)
{
	unsigned mask, expect_flags;
	int bad = 0;

	for (int i = 0; i < 16; i++) {
		uint64_t want;
		if (i == RSP_INDEX)
			continue;	/* the harness owns the stack */
		if (c->reg_fixed >> i & 1)
			want = c->reg_out[i];
		else if (c->reg_same >> i & 1)
			want = in->r[i];
		else
			continue;
		if (out->r[i] != want) {
			printf("      %-3s want %#018" PRIx64 "  got %#018" PRIx64 "\n",
			       REG_NAME[i], want, out->r[i]);
			bad = 1;
		}
	}

	mask = c->flag_same | c->flag_fixed;
	expect_flags = (unsigned)(in->rflags & c->flag_same) | (c->flag_val & c->flag_fixed);
	for (size_t f = 0; f < NFLAGS; f++) {
		unsigned bit = FLAG_NAME[f].bit;
		if (!(mask & bit))
			continue;
		if ((out->rflags & bit) != (expect_flags & bit)) {
			printf("      %s  want %d  got %d\n", FLAG_NAME[f].name,
			       !!(expect_flags & bit), !!(out->rflags & bit));
			bad = 1;
		}
	}
	return bad;
}

/* ------------------------------------------------------------------ */

/* Validate the prologue against the epilogue before trusting either: run a
 * `nop` and require all 16 registers and the modelled flags to round-trip.  A
 * transposed slot or a stale read shows up here as one failure rather than as a
 * wall of test failures with no common cause. */
static const uint8_t nop_code[] = {0x90};

static int self_test(struct x86_state *out)
{
	static const test_case identity = {
		.name = "harness identity",
		.disasm = "nop",
		.code = nop_code,
		.code_len = sizeof nop_code,
		.reg_in = {
			0x0123456789abcdefull, 0xfedcba9876543210ull,
			0x1111111111111111ull, 0x2222222222222222ull,
			0x3333333333333333ull, 0x4444444444444444ull,
			0x5555555555555555ull, 0x6666666666666666ull,
			0x7777777777777777ull, 0x8888888888888888ull,
			0x9999999999999999ull, 0xaaaaaaaaaaaaaaaaull,
			0xbbbbbbbbbbbbbbbbull, 0xccccccccccccccccull,
			0xddddddddddddddddull, 0xeeeeeeeeeeeeeeeeull,
		},
		.reg_same = 0xffff,
		.flag_same = FLAGS_MODELLED,
	};

	for (size_t s = 0; s < NSEEDS; s++) {
		struct x86_state in = {{0}, 0};
		int sig;
		memcpy(in.r, identity.reg_in, sizeof in.r);
		in.rflags = SEEDS[s];
		memset(out, 0, sizeof *out);
		sig = run_child(&identity, &in, out);
		if (sig) {
			printf("  self-test died with signal %d (%s)\n",
			       sig, strsignal(sig));
			return 1;
		}
		if (compare(&identity, &in, out))
			return 1;
	}
	return 0;
}

/* argv: <oracle> <mode>.  The oracle is what the run is checked against -- on an
 * x86-64 host the silicon, under an emulator another *implementation* of x86
 * semantics.  The mode says which, because a disagreement is much weaker evidence
 * in the second case.  See run.sh. */
int main(int argc, char **argv)
{
	const char *oracle = argc > 1 ? argv[1] : "hardware";
	const char *mode = argc > 2 ? argv[2] : "native";
	struct x86_state *out;
	size_t ncases = sizeof CASES / sizeof CASES[0];
	int findings = 0;

	/* Line buffered even when piped, so the diagnostics printed here stay
	 * interleaved with the summaries printed on stderr. */
	setvbuf(stdout, NULL, _IOLBF, 0);
	printf("oracle: %s (%s)\n", oracle, mode);

	/* Shared, so the parent can read a child's result -- and so a faulting
	 * child leaves behind whatever it managed to store. */
	out = mmap(NULL, sizeof *out, PROT_READ | PROT_WRITE,
		   MAP_SHARED | MAP_ANONYMOUS, -1, 0);
	if (out == MAP_FAILED)
		die("mmap");

	if (self_test(out)) {
		fprintf(stderr,
			"HARNESS FAILURE: the trampoline does not round-trip a nop.\n"
			"No test result below would mean anything; fix trampoline.S first.\n");
		return 2;
	}

	for (size_t i = 0; i < ncases; i++) {
		const test_case *c = &CASES[i];
		int bad = 0;

		for (size_t s = 0; s < NSEEDS; s++) {
			struct x86_state in = {{0}, 0};
			int sig;
			memcpy(in.r, c->reg_in, sizeof in.r);
			in.rflags = SEEDS[s];
			memset(out, 0, sizeof *out);

			sig = run_child(c, &in, out);
			if (sig) {
				printf("  %s (%s) [rflags %#" PRIx64 "]: faulted, "
				       "signal %d (%s)\n",
				       c->name, c->disasm, in.rflags, sig,
				       strsignal(sig));
				bad = 1;
				continue;
			}
			if (compare(c, &in, out)) {
				printf("    ^ %s (%s) under rflags %#" PRIx64 "\n",
				       c->name, c->disasm, in.rflags);
				bad = 1;
			}
		}

		if (bad)
			printf("%-24s %-12s DISAGREES WITH %s (%s)\n",
			       c->name, c->disasm, oracle, mode);
		else
			printf("%-24s %-12s ok\n", c->name, c->disasm);
		findings += bad;
	}

	printf("\n%zu tests, %d disagreement%s  [%s, %s]\n", ncases, findings,
	       findings == 1 ? "" : "s", oracle, mode);
	if (findings)
		fprintf(stderr,
			"\nThe model and %s (%s) disagree.  This is a finding about\n"
			"x86.mm0 or about the test vector, not a build regression.\n",
			oracle, mode);
	return findings ? 1 : 0;
}
