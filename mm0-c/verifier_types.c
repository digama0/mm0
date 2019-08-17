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
u32* g_stack_top;

// The "heap" here is more of a collection of pointers into the store, where
// the actual data is kept. The heap contains stack elements in the same format
// as the stack, except that everything is only one word; CONV and CO_CONV
// cells are allocated on the store in place of the two word storage on the
// stack.
#define HEAP_SIZE 65536
u32 g_heap[HEAP_SIZE];
u32 g_heap_size;

// The store contains all the expressions used by the stack and heap. Internal
// pointers in the store (from a term to its children), as well as pointers from
// the stack and heap, are all 4 byte aligned offsets from g_store.
#define STORE_SIZE (1 << 26)
u8 g_store[STORE_SIZE];
u32 g_store_size;

typedef struct {
  u64 type;
  u8 tag;
} store_expr;

#define EXPR_VAR 0
typedef struct {
  u64 type;
  u8 tag; // = EXPR_VAR
  u16 var;
} store_var;

#define EXPR_TERM 1
typedef struct {
  u64 type;
  u8 tag; // = EXPR_TERM
  u16 num_args;
  u32 termid;
  u32 args[];
} store_term;

#define EXPR_CONV 2
typedef struct {
  u32 e1;
  u32 e2;
  u8 tag; // = EXPR_CONV
  u8 padding[3];
} store_conv;

#define HYP_STACK_SIZE 256
u32 g_hstack[HYP_STACK_SIZE];
u32* g_hstack_top;

#define UNIFY_STACK_SIZE 256
u32 g_ustack[UNIFY_STACK_SIZE];
u32* g_ustack_top;

#define UNIFY_HEAP_SIZE 65536
u32 g_uheap[UNIFY_HEAP_SIZE];
u32 g_uheap_size;

u64 g_next_bv;
