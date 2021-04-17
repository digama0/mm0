#include <stdint.h>

#if defined(__clang__) || defined(__GNUC__) || defined(__GNUG__)
#define ALIGNED(n) __attribute__((aligned(n)))
#define PACKED __attribute__((packed))
#define UNREACHABLE() __builtin_unreachable()
#else
#include <assert.h>
#define ALIGNED(n)
#define PACKED
#define UNREACHABLE() assert(0)
#endif

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

// This is called by the ENSURE macro on failure. The verifier is optimized
// for the non-failure case, and keeps very little nonessential information
// about what is going on, so this function is responsible for reconstructing
// the command that failed, loading the index so that the names of terms
// and theorems can be found, and printing the surrounding information.
//
// err: a static error message
// e: the nonzero return code (default -1)
void fail(char* err, int e);

#define EENSURE(err, e, cond) \
  if (__builtin_expect(!(cond), 0)) { \
    fail(err, e); \
  }
#define ENSURE(err, cond) EENSURE(err, -1, cond)

// Each sort has one byte associated to it, which
// contains flags for the sort modifiers.
// The high four bits are unused.
#define SORT_PURE     1
#define SORT_STRICT   2
#define SORT_PROVABLE 4
#define SORT_FREE     8

#define MM0B_MAGIC (u32)0x42304D4D // = "MM0B"
#define MM0B_VERSION (u8)1
#define MAX_SORTS 128

typedef struct {
  u32 magic;         // = MM0B_MAGIC
  u8 version;        // = MM0B_VERSION

  u8 num_sorts;      // number of declared sorts ( <= MAX_SORTS )
  u16 reserved;
  u32 num_terms;     // number of terms and defs
  u32 num_thms;      // number of axioms and theorems

  // /* name** */ u32 p_sort_names; // pointer to start of sort name table
  /* term* */ u32 p_terms;  // pointer to start of term table
  /* thm*  */ u32 p_thms;   // pointer to start of theorem table
  u32 p_proof;              // pointer to start of proof section
  u32 reserved2;
  /* index_header* */ u64 p_index; // pointer to start of index, or 0

  // The list of all sorts. The number of sorts is
  // limited to 128 because of the data layout.
  // So don't monomorphize too much.
  u8 sorts[];
} PACKED header;

// The term arguments table is composed of 64 bit values, where:
// * the low 56 bits (7 bytes) are used for encoding the list of bound variables
//   this variable depends on. bit i is 1 if this is a regular var and
//   depends on the ith *bound* variable
// * Bits 57-62 (the 7 low bits of the high byte) encode the sort of the expression
// * Bit 63 (the MSB / sign bit) is 1 if this is a bound var
#define TYPE_DEPS_MASK (((u64)1<<56)-1)
#define TYPE_BOUND_MASK ((u64)1<<63)
#define TYPE_SORT(type) (((type) >> 56) & 0x7F)

// This struct contains data on symbol names used by the verfifier to ensure
// that there are no name collisions. It has similar data but a different
// purpose to the index, which contains more information about the names
// and is unverified.
// typedef struct {
//   u32 ix;       // index into the relevant table
//   u8 kind;      // One of INDEX_KIND_SORT, INDEX_KIND_TERM, INDEX_KIND_AXIOM
//   char name[];
// } PACKED name;

// An entry in the term table (8 byte aligned)
typedef struct {
  u16 num_args;          // number of arguments
  u8 sort;               // sort of the return value, 1 in high bit means this
                         // is a definition
  u8 reserved;
  // /* name* */ u32 p_name; // pointer to the name of the term, or 0
  /* u64* */ u32 p_args; // pointer to list of binders
  // The list of binders has n+1 elements, with the last element being
  // the return type, followed by a CMD_END-terminated unification command list
  // for definitions.
} PACKED term;

// An entry in the theorem table (4 byte aligned)
typedef struct {
  u16 num_args;           // number of arguments (expression assumptions)
  u16 reserved;
  // /* name* */ u32 p_name; // pointer to the name of the theorem, or 0
  /* u64* */ u32 p_args; // pointer to list of binders
  // The list of binders has n elements, followed by a CMD_END-terminated
  // unification command list.
} PACKED thm;

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
// constants). All index entries and the index header should be 8 byte aligned.

// The p_index pointer from the file header points to this structure,
// an array of 1 + num_sorts + num_terms + num_thms pointers (all file-relative)
// to index entries.
typedef struct {
  /* index* */ u64 p_root;    // pointer to root of BST of index structures
  /* index* */ u64 p_sorts[]; // pointers to sort indexes
  /* index* */ // u64[num_terms] p_terms; pointers to term indexes
  /* index* */ // u64[num_thms] p_thms; pointers to thm indexes
} index_header;

// An index entry contains information necessary for translating between
// string and index representations of entities. The left/right pointers lace
// the entries into a binary search tree on the string values. If multiple
// entries have the same string key, they should be right-associated (they
// should be enumerable by following right-child pointers once the first entry
// with that key is reached).
typedef struct {
  u64 proof;                 // pointer to the command that declares this item
  u64 name;                  // pointer to the name of the item
} name_entry;

// A command is a variable length instruction that forms the bulk of the proof
// file. The commands are processed by a stack machine.
//
// The high two bits denote the data size. The value 0 can be encoded in 0
// bytes, and unsigned integers of 8, 16, 32 bytes are encoded here. This is
// sufficient to determine the length of a command.

#define CMD_DATA(opcode) ((opcode) & 0xC0)
#define CMD_DATA_0  0x00
#define CMD_DATA_8  0x40
#define CMD_DATA_16 0x80
#define CMD_DATA_32 0xC0

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

// End: A null statement, the end of a command sequence. Data = 0.
// Although the command does not reserve space after it, no command can appear
// within 5 bytes (the longest command structure) of the end of the file,
// to allow for preloading. So if CMD_END is the last thing in the file there
// should be another 4 bytes padding.
#define CMD_MAX_SIZE 5
#define CMD_END 0x00

// The statement commands are the same as the corresponding INDEX_KINDs, except
// that there is no CMD_STMT_VAR, and CMD_STMT_TERM is the same as CMD_STMT_DEF
#define CMD_STMT_TERM      0x05
#define CMD_STMT_AXIOM     0x02
#define CMD_STMT_SORT      0x04
#define CMD_STMT_DEF       0x05
#define CMD_STMT_THM       0x06
#define CMD_STMT_LOCAL_DEF 0x0D
#define CMD_STMT_LOCAL_THM 0x0E

// is CMD_STMT_THM or CMD_STMT_LOCAL_THM
#define IS_CMD_STMT_THM(opcode) (((opcode) & 0x37) == CMD_STMT_THM)

#define IS_CMD_STMT_LOCAL(opcode) (((opcode) & 0x08) != 0)

// All commands are byte aligned, and have a forward reference to the
// next command to allow for quick scanning skipping proofs.

// For statement commands, the data field contains the number of bytes to the
// next statement command, starting from the beginning of the command.

// The length of the data field depends on the high bits of the command
typedef struct { u8 cmd; } PACKED cmd0;
typedef struct { u8 cmd; u8 data; } PACKED cmd8;
typedef struct { u8 cmd; u16 data; } PACKED cmd16;
typedef struct { u8 cmd; u32 data; } PACKED cmd32;

// Term: Pop n expressions from the stack (n is determined from the term ID),
// and push a term applied to these expressions. (The n elements are popped
// as a group so that they end up in the same order as they were pushed.)
// Uses data = termid
#define CMD_PROOF_TERM 0x10

// TermSave: Same as Term, but also adds the resulting expression to the heap.
// Uses data = termid
#define CMD_PROOF_TERM_SAVE 0x11

// Ref: Push a variable / hypothesis or previously constructed
// expression / theorem.
// Uses data = heapid, a reference to the heap element.
#define CMD_PROOF_REF 0x12

// Dummy: Push a new variable on the stack, and add it to the heap.
// Uses data = sortid
#define CMD_PROOF_DUMMY 0x13

// Thm: Pop an expression from the stack, pop m expressions, pop n subproofs
// (m and n are determined from the theorem) and check that the substitution
// of the expressions into the conclusion of the theorem is the given
// expression, and the hyps match their substitutions as well.
// Uses data = thmid
#define CMD_PROOF_THM 0x14

// ThmSave: Same as Thm, but also adds the resulting subproof to the heap.
// Uses data = thmid
#define CMD_PROOF_THM_SAVE 0x15

// Hyp: Pop an expression e from the stack, and ensure that the unifier for
// the current theorem declares this hypothesis correctly. Put a proof of e on
// the heap.
// Uses data = 0
#define CMD_PROOF_HYP 0x16

// Conv: Pop a proof of e2, pop an expression e1, push a proof of e1, push
// a convertibility obligation e1 =?= e2.
// Uses data = 0
#define CMD_PROOF_CONV 0x17

// Refl: Pop a convertibility obligation e =?= e. The two sides should be
// references to the same heap element.
// Uses data = 0
#define CMD_PROOF_REFL 0x18

// Symm: Pop a convertibility obligation e1 =?= e2, push a convertibility
// obligation e2 =?= e1.
// Uses data = 0
#define CMD_PROOF_SYMM 0x19

// Cong: Pop a convertibility obligation t e1 ... en =?= t e1' ... en',
// push en =?= en', ..., push e1 =?= e1'.
// Uses data = 0
#define CMD_PROOF_CONG 0x1A

// Unfold: Pop an expression e, pop an expression t e1 ... en,
// where t is a definition, and execute the unifier for t to verify that
// t e1 ... en  unfolds to e, which will pop an additional m expressions from
// the stack, where m is the number of heap elements in the definition of t.
// Pop a convertibility obligation t e1 ... en =?= e',
// and push e =?= e' to the stack.
// Uses data = 0
#define CMD_PROOF_UNFOLD 0x1B

// ConvCut: Pop a convertibility obligation e1 =?= e2, push a proof of
// e1 = e2, push a convertibility obligation e1 =?= e2.
// Uses data = 0
#define CMD_PROOF_CONV_CUT 0x1C

// ConvSave: Pop a convertibility proof e1 = e2, add e1 = e2 to the heap.
// Uses data = 0
#define CMD_PROOF_CONV_SAVE 0x1E

// Save: Save the top of the stack to the heap, without popping it.
// Uses data = 0
#define CMD_PROOF_SAVE 0x1F

// Sorry: Pop an expression e from the stack, and push |- e. This step exists
// only for debugging purposes and incomplete proofs, it is not a valid step
// under any circumstances.
//
// ConvSorry: Pop a convertibility obligation e1 =?= e2. This reuses the Sorry
// command, and depends on the type of the head of stack for its behavior.
// Uses data = 0
#define CMD_PROOF_SORRY 0x20

// Unify commands are used in definitions and theorem statements.
// They are consumed when a definition is unfolded, or when a theorem is
// applied, and interact with both the main stack and a separate unification
// stack, which stores expressions that will be matched relative to an input
// substitution. The substitution is stored on a separate unify heap, which
// may be extended during unification via Save commands.

// Term: Pop an expression from the unify stack, ensure that the head
// of the expression is the given term ID, and push the n arguments to the
// unify stack.
// Uses data = termid
#define CMD_UNIFY_TERM 0x30

// TermSave: Same as Term, but also puts the expression popped from the
// unify stack on the substitution heap.
// Uses data = termid
#define CMD_UNIFY_TERM_SAVE 0x31

// Ref: Pop an expression from the unify stack, and ensure it is equal
// to the referenced element on the substitution heap.
// Uses data = heapid, a reference to the substitution heap.
#define CMD_UNIFY_REF 0x32

// Dummy: (Only in definitions) Pop an expression from the unify stack,
// check that it is a bound variable with the specified sort, and
// put it on the substitution heap.
// Uses data = sortid
#define CMD_UNIFY_DUMMY 0x33

// Hyp: (Only in theorem statements) Pop a proof of e from the main stack,
// and push e to the unify stack.
// Uses data = 0
#define CMD_UNIFY_HYP 0x36
