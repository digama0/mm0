#include <stdint.h>

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

// Each sort has one byte associated to it, which
// contains flags for the sort modifiers.
// The high four bits are unused.
#define SORT_PURE     1
#define SORT_STRICT   2
#define SORT_PROVABLE 4
#define SORT_FREE     8

#define MM0B_MAGIC (u32)0x42304D4D // = "MM0B"
#define MM0B_VERSION (u32)1
#define MAX_SORTS 128

typedef struct {
  u32 magic;         // = MM0B_MAGIC
  u32 version;       // = MM0B_VERSION

  u32 num_sorts;     // number of declared sorts ( <= MAX_SORTS )
  u32 num_terms;     // number of terms and defs
  u32 num_thms;      // number of axioms and theorems

  /* term* */ u32 p_terms;  // pointer to start of term table
  /* thm*  */ u32 p_thms;   // pointer to start of theorem table
  u32 p_proof;              // pointer to start of proof section
  u64 p_index;              // pointer to start of index, or 0

  // The list of all sorts. The number of sorts is
  // limited to 128 because of the data layout.
  // So don't monomorphize too much.
  u8 sorts[128];
} header;

// The term arguments table is composed of 64 bit values, where:
// * the low 56 bits (7 bytes) are used for encoding the list of bound variables
//   this variable depends on. bit i is 1 if this is a regular var and
//   depends on the ith *bound* variable
// * Bits 57-62 (the 7 low bits of the high byte) encode the sort of the expression
// * Bit 63 (the MSB / sign bit) is 1 if this is a bound var
#define TYPE_DEPS_MASK (((u64)1<<56)-1)
#define TYPE_BOUND_MASK ((u64)1<<63)
#define TYPE_SORT(type) (((type) >> 56) & 0x7F)

// An entry in the term table
typedef struct {
  u8 sort;               // sort of the return value, 1 in high bit means
                         // ret_deps is filled
  u8 num_args;           // number of arguments
  u16 heap_sz;           // = FFFF if term, = heap_size if definition
  /* u64* */ u32 p_args; // pointer to list of binders
  u64 ret_deps[3];       // space for three binders, including the optional return deps
                         // p_args is permitted to point right here if the term is small
} term;

// An entry in the theorem table
typedef struct {
  u8 num_args;           // number of arguments (expression assumptions)
  u8 num_hyps;           // number of hypotheses (theorem assumptions)
  u16 heap_sz;           // size of (expression) heap
  /* u64* */ u32 p_args; // pointer to list of binders
  // The expression heap comes after the list of binders, and the
  // command list comes after that.
} thm;

#define INDEX_KIND_TERM      (u8)0x01 // This is a term
#define INDEX_KIND_AXIOM     (u8)0x02 // This is an axiom
#define INDEX_KIND_VAR       (u8)0x03 // This is a variable
#define INDEX_KIND_SORT      (u8)0x04 // This is a sort
#define INDEX_KIND_DEF       (u8)0x05 // This is a def
#define INDEX_KIND_THM       (u8)0x06 // This is a theorem
#define INDEX_KIND_LOCAL_DEF (u8)0x0D // This is a def that does not appear in the spec
#define INDEX_KIND_LOCAL_THM (u8)0x0E // This is a theorem that does not appear in the spec

// The index contains information not needed for the verifier but
// helpful for display and debugging (like string representations of the
// constants).
typedef struct {
  u64 left;                  // pointer to left subchild (for binary searching by strings)
  u64 right;                 // pointer to right subchild
  u8 kind;                   // sort, term, thm, var
  u32 ix;                    // Index of the object in the relevant table
  u32 row, col;              // For locating in the spec file
  u64 proof;                 // pointer to the command that declares this item
  // followed by a zero-terminated char* buffer
} index;

// A command is a variable length instruction that forms the bulk of the proof
// file. The commands are processed by a stack machine, but the stack is implicit
// in the file itself, as the history of a persistent linked list over time,
// which appears as a tree. For example, the s-expression
//
//    A a (B z z b)    [z=(C a)]                  A
//                                               / \
// is processed in RPN order (with reversed     a  B
// applications) to obtain                        /|\
//                                               C C b
//    b a z=C z B a A                            | |
//                                               a a
// and the stack at each stage looks like
//
//  1:  b
//  2:  b <- a1
//  3:  b <- z1=C
//  4:  b <- z1=C <- z2
//  5:  B
//  6:  B <- a2
//  7:  A
//
// where the arrows represent pointers in a singly linked list. Since every
// stack object has a unique parent, this entire structure can be represented as
// a forest (the roots are drawn to the left), with all pointers going backwards:
//
//      /-a1
//     /
//    b <---- z1 <- z2
//
//                      B <- a2
//                               A
//
// The advantage of this representation is that we can traverse the original
// tree without a stack.
//
// So every command has a backpointer to the previous item on the stack.
// Stack item z2 would additionally have a backreference pointer to z1=C,
// to handle subterm duplication in the original s-expression.
//
// The high two bits denote the backpointer size (an unsigned number giving the
// number of bytes backwards to the last command):

#define CMD_BP(opcode) ((opcode) & 0xC0)
#define CMD_BP_0  0x00
#define CMD_BP_8  0x40
#define CMD_BP_16 0x80
#define CMD_BP_32 0xC0

// Backpointers always come at the end of an instruction, after the regular
// arguments to the instruction.
//
// The low five bits (0-4) give the opcode, what kind of instruction follows.
// Bit 5 is unused. The opcode determines the data layout of following fields.
// In each data layout, the fields are marked as:
//
//   (input) if they are new information for the verifier
//   (output) if they are determinable from information the verifier already
//            knows, and the verifier is responsible for checking that the data
//            is correct
//   (unverified) if the information should be well formed but the verifier
//                can't check it. This info is ignored in core verification

// Opcodes 0 - 15 are command keywords; they start a new statement (axiom, def, theorem, etc).
// Except the END instruction, each is followed by a pointer to the next command keyword.
// BP and backreference pointers are relative to the last command keyword.

// End: A null statement, the end of a command sequence. No additional data, BP = 0.
// Although the command does not reserve space after it, no command can appear
// within 20 bytes (the longest command structure) of the end of the file,
// to allow for preloading. So if CMD_END is the last thing in the file there
// should be another 19 bytes padding.
#define CMD_MAX_SIZE 20
#define CMD_END 0x00

// The statement commands are the same as the corresponding INDEX_KINDs, except
// that there is no CMD_VAR, and CMD_TERM is the same as CMD_DEF
#define CMD_TERM      0x05
#define CMD_AXIOM     0x02
#define CMD_SORT      0x04
#define CMD_DEF       0x05
#define CMD_THM       0x06
#define CMD_LOCAL_DEF 0x0D
#define CMD_LOCAL_THM 0x0E

// is CMD_THM or CMD_LOCAL_THM
#define IS_CMD_THM(opcode) (((opcode) & 0xF7) == CMD_THM)

// For statement commands, BP = 0. They have a forward reference to the next
// command.
typedef struct {
  u8 cmd;           // statement command, BP = 0
                    // 3 bytes padding
  u32 next;         // the number of bytes to the next statement command (output)
} cmd_stmt;

typedef struct {
  u8 cmd;           // statement command, BP = 0
                    // 3 bytes padding
  u32 next;         // the number of bytes to the next statement command (output)
  u32 heap_sz;      // Size of the expression heap.
  u32 theap_sz;     // Size of the theorem heap.
  // The expression heap (u64[]) begins after this, and the
  // theorem heap (u32[]) after that, and then the beginning of
  // proof commands.
} cmd_thm;

// Generic template for expression instructions, opcodes 0x10 - 0x17
#define IS_EXPR(opcode) (((opcode) & 0x18) == 0x10)
typedef struct {
  u8 cmd;              // = expression command
  u8 _[3];             // 3 bytes padding
  u8 type[8];          // the expression type (output)
} cmd_expr;

// The BP and data fields are arranged depending on the size of BP
typedef struct { u8 cmd; u8 bp; u16 data; u8 type[8]; } cmd_expr8;
typedef struct { u8 cmd; u8 data; u16 bp; u8 type[8]; } cmd_expr16;
typedef struct { u8 cmd; u8 _[3]; u8 type[8]; u32 bp; u32 data; } cmd_expr32;

// Term: Pop n expressions from the stack (n is determined from the term ID),
// and push a term applied to these expressions. (Note: stack items are popped
// one by one, so they end up reversed from the usual application order.)
// Uses expr format with data = termid
#define CMD_EXPR_TERM 0x10

// Save: Same as Term, but also adds the resulting expression to the heap.
// Uses expr format with data = termid
#define CMD_EXPR_SAVE 0x11

// Var: Push a variable or previously constructed expression.
// Uses expr format with data = heapid, a reference to the heap element.
#define CMD_EXPR_VAR 0x13

// Dummy: Push a new variable on the stack, and add it to the heap.
// Uses expr format with data unused.
#define CMD_EXPR_DUMMY 0x14

// Unfold: Pop an expression e, pop n+m expressions ei from the stack,
// where n is the number of args and m is the number of heap items,
// and push e, after determining that e is the result of unfolding the
// definition with the given substitutions.
// Uses expr format with data = termid
#define CMD_EXPR_UNFOLD 0x15

// Generic template for proof instructions, opcodes 0x18 - 0x1F. Same as expr
// without the type field
#define IS_PROOF(opcode) (((opcode) & 0x18) == 0x18)
typedef struct { u8 cmd; u8 bp; u16 data; } cmd_proof8;
typedef struct { u8 cmd; u8 data; u16 bp; } cmd_proof16;
typedef struct { u8 cmd; u8 _[3]; u32 bp; u32 data; } cmd_proof32;

// Hyp: Pop an expression from the stack, push an assumption
// that the expr is true and add it to the hyp list.
// Uses proof format with data ignored
#define CMD_PROOF_HYP 0x1B

// DeclHyp: A special version of Hyp for use in axiom/theorem declaraions.
// Pop an expression from the stack; this command is an assumption
// that the expr is true, but it is not saved to the heap or stack.
// Uses proof format with data ignored, BP = 0
#define CMD_PROOF_DECL_HYP 0x1A

// Ref: Pop an expression from the stack, check that the input hypid has the
// same expression.
// Uses proof format with data = hypid (input)
#define CMD_PROOF_REF 0x18

// Thm: Pop an expression from the stack, pop n subproofs, pop m expressions
// (m and n are determined from the theorem) and check that the substitution
// of the expressions into the conclusion of the theorem is the given
// expression, and the hyps match their substitutions as well.
// Uses proof format with data = thmid (input)
#define CMD_PROOF_THM 0x1E

// Save: Same as Thm, but also adds the theorem to the hyp list.
// Uses proof format with data = thmid (input)
#define CMD_PROOF_SAVE 0x1F
