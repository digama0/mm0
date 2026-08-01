/* One trampoline, shared by every test.
 *
 * This code is in the trusted computing base of every runtime result, and it
 * cannot be otherwise: the teardown stores registers RIP-relative (`mod=00,
 * rm=101`) because that is the only addressing form needing no scratch
 * register, and so the only one that survives a test that clobbers everything.
 * That encoding is precisely one of the things the suite exists to test, so
 * modelling the harness would make the test for RIP-relative addressing depend
 * on RIP-relative addressing being right.  Hence: one copy, kept small enough
 * to read in full, checked against itself by the identity self-test in
 * harness.c before any real test runs.
 *
 *   void x86_run_case(const struct x86_state *in,   // rdi
 *                     struct x86_state *out,        // rsi
 *                     void *code);                  // rdx
 *
 *   struct x86_state { uint64_t r[16]; uint64_t rflags; };
 *
 * `code` points at a buffer holding the instruction under test followed by an
 * indirect jump back to x86_epilogue, so control returns however long the
 * instruction turned out to be.
 *
 * RSP is neither loaded nor meaningfully stored: the trampoline needs a stack of
 * its own for `popfq`/`pushfq`, and a test that reloaded RSP would take that
 * away.  Stack tests need a different arrangement (see the design doc, tier 3).
 */

	.text

	.globl	x86_run_case
	.type	x86_run_case, @function
x86_run_case:
	push	%rbx
	push	%rbp
	push	%r12
	push	%r13
	push	%r14
	push	%r15

	mov	%rsi, out_ptr(%rip)
	mov	%rdx, code_ptr(%rip)
	mov	%rsp, saved_rsp(%rip)

	lea	test_stack_top(%rip), %rsp

	/* Flags first: nothing below this point disturbs them, since `mov` does
	 * not write flags and the indirect `jmp` does not either. */
	pushq	128(%rdi)
	popfq

	mov	  0(%rdi), %rax
	mov	  8(%rdi), %rcx
	mov	 16(%rdi), %rdx
	mov	 24(%rdi), %rbx
	/* 32: RSP, deliberately not loaded */
	mov	 40(%rdi), %rbp
	mov	 48(%rdi), %rsi
	mov	 64(%rdi), %r8
	mov	 72(%rdi), %r9
	mov	 80(%rdi), %r10
	mov	 88(%rdi), %r11
	mov	 96(%rdi), %r12
	mov	104(%rdi), %r13
	mov	112(%rdi), %r14
	mov	120(%rdi), %r15
	mov	 56(%rdi), %rdi		/* the base register, so it goes last */

	jmp	*code_ptr(%rip)
	.size	x86_run_case, . - x86_run_case

/* Entered from the code buffer with every register holding whatever the
 * instruction under test left there, and no usable scratch register. */
	.globl	x86_epilogue
	.type	x86_epilogue, @function
x86_epilogue:
	mov	%rax, tmp_rax(%rip)	/* free one register, RIP-relative */
	mov	out_ptr(%rip), %rax

	mov	%rcx,	  8(%rax)
	mov	%rdx,	 16(%rax)
	mov	%rbx,	 24(%rax)
	mov	%rsp,	 32(%rax)	/* the test stack, not a test result */
	mov	%rbp,	 40(%rax)
	mov	%rsi,	 48(%rax)
	mov	%rdi,	 56(%rax)
	mov	%r8,	 64(%rax)
	mov	%r9,	 72(%rax)
	mov	%r10,	 80(%rax)
	mov	%r11,	 88(%rax)
	mov	%r12,	 96(%rax)
	mov	%r13,	104(%rax)
	mov	%r14,	112(%rax)
	mov	%r15,	120(%rax)
	mov	tmp_rax(%rip), %rcx
	mov	%rcx,	  0(%rax)

	/* Still the flags the instruction left: every store above is a `mov`. */
	pushfq
	pop	%rcx
	mov	%rcx,	128(%rax)

	mov	saved_rsp(%rip), %rsp
	pop	%r15
	pop	%r14
	pop	%r13
	pop	%r12
	pop	%rbp
	pop	%rbx
	ret
	.size	x86_epilogue, . - x86_epilogue

	.data
	.align	8
out_ptr:	.quad	0
code_ptr:	.quad	0
saved_rsp:	.quad	0
tmp_rax:	.quad	0

	.bss
	.align	16
test_stack:	.space	65536
test_stack_top:

	.section	.note.GNU-stack,"",@progbits
