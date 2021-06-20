#pragma once
#include "index.c"

// The stack is stored as a sequence of 32-bit words.
// The 2 low bits are used for discriminating, and
// the 30 high bits are an index into the expr store.
// 0: expr e
// 1: proof e (a proof of e on the stack)
// 2: e1 = e2, where e1 is here and expr e2 is below this on the stack
// 3: e1 =?= e2, where e1 is here and expr e2 is below this on the stack

#define STACK_TYPE_EXPR    0x00
#define STACK_TYPE_PROOF   0x01
#define STACK_TYPE_CONV    0x02
#define STACK_TYPE_CO_CONV 0x03
#define STACK_TYPE_MASK (u32)0x03
#define STACK_DATA_MASK (u32)(~0x03)

#define STACK_SIZE 65536
u32 g_stack[STACK_SIZE];
u32* g_stack_top = g_stack;

// The "heap" here is more of a collection of pointers into the store, where
// the actual data is kept. The heap contains stack elements in the same format
// as the stack, except that everything is only one word; CONV and CO_CONV
// cells are allocated on the store in place of the two word storage on the
// stack.
#define HEAP_SIZE 65536
u32 g_heap[HEAP_SIZE];
u32 g_heap_size = 0;

// The store contains all the expressions used by the stack and heap. Internal
// pointers in the store (from a term to its children), as well as pointers from
// the stack and heap, are all 4 byte aligned offsets from g_store.
#define STORE_SIZE (1 << 26)
u8 g_store[STORE_SIZE];
u32 g_store_size = 0;

typedef struct {
  u64 PACKED ALIGNED(4) type;
  u8 tag;
} store_expr;

#define EXPR_VAR 0
typedef struct {
  u64 PACKED ALIGNED(4) type;
  u8 tag; // = EXPR_VAR
  u16 var;
} store_var;

#define EXPR_TERM 1
typedef struct {
  u64 PACKED ALIGNED(4) type;
  u8 tag; // = EXPR_TERM
  u16 num_args;
  u32 termid;
  u32 args[];
} store_term;

typedef struct {
  u32 e1;
  u32 e2;
} store_conv;

#define HYP_STACK_SIZE 256
u32 g_hstack[HYP_STACK_SIZE];
u32* g_hstack_top = g_hstack;

#define UNIFY_STACK_SIZE 256
u32 g_ustack[UNIFY_STACK_SIZE];
u32* g_ustack_top = g_ustack;

#define UNIFY_HEAP_SIZE 65536
u32 g_uheap[UNIFY_HEAP_SIZE];
u32 g_uheap_size = 0;

/****************
  Parser types
****************/

#ifdef NO_PARSER
#define g_parsing false
#else
u8 g_parsing = false;


// In order to ensure nonduplication of identifiers and parse efficiently,
// we maintain a trie data structure, with 16-way branching.
// The data field of the trie stores the negated sort/term/thm ID,
// and variable IDs are stored in the data field of the name of the variable
// plus the 0 nibble. The indexes of these variable nodes are stored
// so they can be popped later.

// Each trie is initialized to size 2, with trie[1] being the root node and
// trie[0] an always-zero trie node so that searches that go off the end of
// the tree end up in the zero node.

typedef struct {
  u32 data;
  u32 next[16];
} trie_node;
typedef trie_node* trie;

#define SORT_TRIE_SIZE 1024
trie_node gt_sorts[SORT_TRIE_SIZE];
trie_node* gt_sorts_end = gt_sorts + 2;

#define THM_TRIE_SIZE (1 << 20)
trie_node gt_thms[THM_TRIE_SIZE];
trie_node* gt_thms_end = gt_thms + 2;

#define TERM_TRIE_SIZE (1 << 16)
trie_node gt_terms[TERM_TRIE_SIZE];
trie_node* gt_terms_end = gt_terms + 2;

#define TOKEN_TRIE_SIZE (1 << 16)
trie_node gt_tokens[TOKEN_TRIE_SIZE];
trie_node* gt_tokens_end = gt_tokens + 2;
trie g_open_paren = 0;
trie g_close_paren = 0;

#define DELIM_LEFT 0x1
#define DELIM_RIGHT 0x2
#define DELIM_SPACE 0x4
u8 g_delims[256];

// This is an unsorted array. We could use a hashmap if it gets larger
#define PREC_ASSOC_SIZE (1 << 16)
typedef struct {
  u16 prec;
  u8 rassoc;
} prec_assoc;
prec_assoc g_prec_assoc[PREC_ASSOC_SIZE];
u32 g_prec_assoc_size = 0;

#define COE_EMPTY 0 // initial value: there is no coercion s1 -> s2
#define COE_ONE   1 // There is a coercion s1 -> s2, in termid
#define COE_TRANS 2 // There is a path s1 -> trans -> s2
#define COE_PROV  3 // There is a null path s1 -> PROV because s1 is provable
typedef struct {
  u8 tag;
  union {
    u32 termid;
    u8 trans;
  };
} coe;
// The last column PROV represents an extra sink for provable sorts
#define PROV MAX_SORTS
coe g_coes[MAX_SORTS][MAX_SORTS+1];

#define PARSER_ARENA_SIZE (1 << 20)
u32 g_parser_arena[PARSER_ARENA_SIZE];
u32 g_parser_arena_size = 1;

#define NUM_VARS (1 << 16)
struct {u32 trie; u32 var;} g_var_nodes[NUM_VARS];
u8 g_var_sorts[NUM_VARS];
u32 g_num_vars = 0;

typedef struct {
  u8 tag; // = EXPR_VAR
  u16 var;
} parse_var;

typedef struct {
  u8 tag; // = EXPR_TERM
  u16 num_args;
  u32 termid;
  u32 args[];
} parse_term;

typedef struct {
  u32 hd;
  u32 tl; // -1 = null
} parse_expr_list;

#define LIT_CONST 0
#define LIT_VAR 1
typedef struct {
  u32 tag;
  union {
    struct lit_const { u32 token; } cnst;
    struct lit_var { u16 var; u16 prec; } var;
  };
} literal;

typedef struct {
  u32 termid;
  u16 num_args;
  u16 num_lits;
  literal lits[];
} prefix_info;

typedef struct {
  u32 termid;
  u8 rassoc;
} infix_info;

typedef struct {
  u32 prefix;
  u32 infix;
  u16 prec;
  u8 prec_set;
} token_info;

// For simplicity, we rely on paging for the input,
// and preallocate all the space we will ever need.
// It is easy to reduce memory consumption here by releasing
// memory behind the cursor if necessary.
#define INPUT_SIZE (1 << 29)
// This ensures that cursor[n] is always readable for n < 10,
// although these may be zero bytes in the space after buffer_end
#define BUFFER_OVERSHOOT 10
u8 buffer[INPUT_SIZE];
// The actual read data is between cursor and buffer_end
u8* cursor = buffer;
u8* buffer_end = buffer;
// eof is true if we have performed our last read (so whatever is
// in the buffer is all of the data).
int eof = 0;

#endif

#ifdef HIGHWATER
u32* g_stack_highwater;
u32 g_heap_highwater;
u32 g_store_highwater;
u32* g_hstack_highwater;
u32* g_ustack_highwater;
u32 g_uheap_highwater;
#define UPDATE_HIGHWATER(p, hw) if (hw <= p) hw = p;
#else
#define UPDATE_HIGHWATER(p, hw)
#endif

u64 g_next_bv = 0;
