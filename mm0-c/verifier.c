#include <stdbool.h>
#include "types.c"

#define UNREACHABLE() __builtin_unreachable()
#define EENSURE(err, e, cond) \
  if (__builtin_expect(!(cond), 0)) { \
    fprintf(stderr, err); \
    abort(e); \
  }
#define ENSURE(err, cond) EENSURE(err, -1, cond)

u8* g_file; u8* g_end;
u8 g_num_sorts; u8*   g_sorts;
u8 g_num_terms; term* g_terms;
u8 g_num_thms;  thm*  g_thms;

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
ALIGNED(4) u8 g_store[STORE_SIZE];
u32 g_store_size;

typedef struct ALIGNED(4) {
  u64 type;
  u8 tag;
} store_expr;

#define EXPR_VAR 0
typedef struct ALIGNED(4) {
  u64 type;
  u8 tag; // = EXPR_VAR
  u16 var;
} store_var;

#define EXPR_TERM 1
typedef struct ALIGNED(4) {
  u64 type;
  u8 tag; // = EXPR_TERM
  u16 num_args;
  u32 termid;
  u32 args[];
} store_term;

u64 g_next_bv;
u8* g_unify_cmd;
u8* g_proof_cmd;
// scratch space
u8* g_subst[256];
u64 g_deps[256];
u32 g_bp, g_data; u64 g_type;

u32 push_stack(u32 val) {
  ENSURE("stack overflow", g_stack_top < &g_stack[STACK_SIZE]);
  *g_stack_top++ = val;
}

u32 push_heap(u32 val) {
  ENSURE("heap overflow", g_heap_size < HEAP_SIZE);
  g_heap[g_heap_size++] = val;
}

#define ALLOC(val, size) ({ \
  ENSURE("store overflow", g_store_size + size <= STORE_SIZE); \
  u32 p = g_store_size; \
  *(typeof(val)*)&g_store[p] = val; \
  g_store_size += size; \
  p; \
})

u32 cmd_unpack(u8* cmd) {
  switch (CMD_DATA(*cmd)) {
    case CMD_DATA_0:
    case CMD_DATA_8: {
      cmd8* p = (cmd8*)cmd;
      g_data = p->data;
      return sizeof(cmd8);
    } break;

    case CMD_DATA_16: {
      cmd16* p = (cmd16*)cmd;
      g_data = p->data;
      return sizeof(cmd16);
    } break;

    case CMD_DATA_32: {
      cmd32* p = (cmd32*)cmd;
      g_data = p->data;
      return sizeof(cmd32);
    } break;
  }
  UNREACHABLE();
}

bool sorts_compatible(u64 from, u64 to) {
  u64 diff = from ^ to;
  return (diff & ~TYPE_DEPS_MASK) == 0 ||
    ((diff & (TYPE_BOUND_MASK | ~TYPE_DEPS_MASK)) == 0 &&
    (from & TYPE_BOUND_MASK) != 0);
}

void load_args(u64* args, u32 num_args) {
  g_next_bv = 1;
  for (int i = 0; i < num_args; i++) {
    u64 ty = args[i];
    u64 vars_bitset = ty & TYPE_DEPS_MASK;
    u8 sort = TYPE_SORT(ty);
    ENSURE("bad binder sort", sort < g_num_sorts);
    if (ty & TYPE_BOUND_MASK) {
      ENSURE("bound variable in strict sort", (g_sorts[sort] & SORT_STRICT) == 0);
      ENSURE("bad binder deps", vars_bitset == g_next_bv);
      g_next_bv *= 2;
    } else {
      ENSURE("bad binder deps", (vars_bitset & ~(g_next_bv - 1)) == 0);
    }
    push_heap(STACK_TYPE_EXPR |
      ALLOC((store_var){ty, EXPR_VAR, i}, sizeof(store_var)));
  }
}

typedef enum { Def, Thm } proof_mode;

void run_proof(proof_mode mode) {
  u8* last_cmd = g_proof_cmd;
  while (true) {
    ENSURE("command out of range", g_proof_cmd + CMD_MAX_SIZE <= g_end);
    if (*g_proof_cmd == CMD_END) break;

    u32 sz = cmd_unpack(g_proof_cmd); // sets g_data
    switch (*g_proof_cmd & 0x1F) {
      case CMD_PROOF_REF: {
        ENSURE("bad ref step", g_data < g_heap_size);
        push_stack(g_heap[g_data]);
      } break;

      case CMD_PROOF_DUMMY: {
        push_heap(STACK_TYPE_EXPR |
          ALLOC((store_var){ty, EXPR_VAR, i}, sizeof(store_var)));
        ENSURE("heap overflow", heap_end < heap_cap);
        ENSURE("dummy type mismatch", type == *heap_end);
        if ((type & TYPE_DEPS_MASK) != *g_next_bv) {
          ENSURE("too many bound variables, please rewrite the verifier",
            *g_next_bv & TYPE_BOUND_MASK);
          ENSURE("bad dummy deps", false);
        }
        u8 sort = TYPE_SORT(type);
        ENSURE("bad dummy sort", sort < g_num_sorts);
        ENSURE("dummy variable in strict sort",
          (g_sorts[sort] & SORT_STRICT) == 0);
        ENSURE("non-bound dummy", type & TYPE_BOUND_MASK);
        heap_end++;
        *g_next_bv *= 2;
        ENSURE("bad BP", g_proof_cmd == last_cmd + bp);
      } break;

      case CMD_PROOF_TERM:
      case CMD_PROOF_SAVE: {
        sz = cmd_unpack(g_proof_cmd, &bp, &data, &type);
        ENSURE("term out of range", data < g_num_terms);
        term* t = &g_terms[data];
        u8* p = last_cmd;
        ENSURE("stack underflow", t->num_args == 0 || p != g_proof_cmd);
        u64* targs = (u64*)&g_file[t->p_args];
        // alloc g_deps;
        u8 bound = 0;
        u64 accum = (u64)t->sort << 56;
        for (u8 i = 0; i < t->num_args; i++) {
          // alloc g_bp, g_data, g_type;
          ENSURE("bad stack slot", IS_EXPR(*p));
          cmd_unpack(p, &g_bp, &g_data, &g_type);
          u64 target = targs[i];
          ENSURE("type mismatch", sorts_compatible(g_type, target));
          u64 deps = g_type & TYPE_DEPS_MASK;
          if (target & TYPE_BOUND_MASK) {
            g_deps[bound++] = deps;
          } else {
            if (mode == Def)
              for (u8 j = 0; j < bound; j++)
                if (target & ((u64)1<<j))
                  deps &= ~g_deps[j];
            accum |= deps;
          }
          ENSURE("stack underflow", g_bp != 0);
          p -= g_bp;
          // free g_bp, g_data, g_type;
        }
        if (mode == Def) {
          if (accum & TYPE_BOUND_MASK) {
            accum &= ~TYPE_BOUND_MASK;
            u64 target = *t->ret_deps;
            for (u8 j = 0; j < bound; j++)
              if (target & ((u64)1<<j))
                accum |= g_deps[j];
          }
        } else {
          accum &= ~TYPE_BOUND_MASK;
        }
        // free g_deps;
        ENSURE("bad BP", g_proof_cmd == p + bp);
        ENSURE("bad term type/deps", type == accum);
        if (*p_stmt & 0x01) { // save
          ENSURE("heap overflow", heap_end < heap_cap);
          ENSURE("save type mismatch", type == *heap_end);
          heap_end++;
        }
      } break;

      case CMD_PROOF_DECL_HYP: {
        ENSURE("DeclHyp instruction used outside theorem statement", mode == Thm);
        ENSURE("DeclHyp instruction should have BP = 0", CMD_DATA(*g_proof_cmd) == CMD_DATA_0);
        ENSURE("bad stack slot", IS_EXPR(*last_cmd));
        ENSURE("hypothesis should have provable sort",
          (g_sorts[TYPE_SORT(type)] & SORT_PROVABLE) != 0)
      } break;

      // case CMD_PROOF_UNFOLD: not permitted
      default: ENSURE("Unknown opcode in def", false); break;
    }
    last_cmd = g_proof_cmd;
    g_proof_cmd += sz;
  }
}

void verify(u64 len, u8* file) {
  ENSURE("header not long enough", len >= sizeof(header));
  header* p = (header*)file;
  ENSURE("Not a MM0B file", p->magic == MM0B_MAGIC);
  ENSURE("Wrong version", p->version == MM0B_VERSION);
  ENSURE("Too many sorts", p->num_sorts <= MAX_SORTS);
  ENSURE("Term table out of range",
    len >= p->p_terms + p->num_terms * sizeof(term));
  ENSURE("Theorem table out of range",
    len >= p->p_thms + p->num_thms * sizeof(term));
  ENSURE("Proof section out of range", len > p->p_proof);
  g_file = file; g_end = file + len;
  g_num_sorts = 0; g_sorts = p->sorts;
  g_num_terms = 0; g_terms = (term*)&file[p->p_terms];
  g_num_thms  = 0; g_thms  = (thm*)&file[p->p_thms];

  u8* p_stmt = &file[p->p_proof];

  while (*p_stmt != CMD_END) {
    cmd_stmt* stmt = (cmd_stmt*)p_stmt;
    u8* next_stmt = p_stmt + stmt->next;
    ENSURE("proof command out of range", next_stmt + CMD_MAX_SIZE <= g_end);

    switch (*p_stmt) {
      case CMD_SORT: {
        ENSURE("Next statement incorrect", stmt->next == sizeof(cmd_stmt));
        ENSURE("Step sort overflow", g_num_sorts < p->num_sorts);
        g_num_sorts++;
      } break;

      // case CMD_TERM: // = CMD_DEF
      case CMD_DEF:
      case CMD_LOCAL_DEF: {
        ENSURE("Next statement incorrect", stmt->next == sizeof(cmd_stmt));
        term* t = &g_terms[g_num_terms];
        ENSURE("Step term overflow", g_num_terms < p->num_terms);
        u8 sort = t->sort & 0x7F;
        ENSURE("bad sort", sort < g_num_sorts);
        ENSURE("term in pure sort", (g_sorts[sort] & SORT_PURE) == 0);
        u64* args = (u64*)&file[t->p_args];
        u64* args_ret = &args[t->num_args];
        u64* args_end = &args_ret[1];
        ENSURE("bad args pointer", (u8*)args_end <= g_end);
        g_store_size = 0;
        g_heap_size = 0;
        g_stack_top = &g_stack;
        load_args(args, t->num_args + 1);
        ENSURE("bad return type", (*args_ret >> 56) == sort);
        g_heap_size--;

        if (t->sort & 0x80) {
          u8* cmd;
          run_proof(Def, args, args_end, &cmd);
          ENSURE("bad stack slot", IS_EXPR(*cmd));
          // alloc g_bp, g_data, g_type;
          cmd_unpack(cmd, &g_bp, &g_data, &g_type);
          ENSURE("stack has more than one element", g_bp == 0);
          ENSURE("type mismatch", sorts_compatible(g_type, t->sort));
          ENSURE("type has unaccounted dependencies",
            (g_type & TYPE_DEPS_MASK & ~ret_deps) == 0);
          // free g_bp, g_data, g_type;
        }
        g_num_terms++;
      } break;

      case CMD_AXIOM:
      case CMD_THM:
      case CMD_LOCAL_THM: {
        thm* t = &g_thms[g_num_thms];
        ENSURE("Step theorem overflow", g_num_thms < p->num_thms);
        u64* args = (u64*)&file[t->p_args];
        u64* args_end = &args[t->num_args];
        u64* heap_end = args_end;
        u64* heap_cap = &args_end[t->heap_sz];
        u8* cmd;
        load_args(args, args_end);
        run_proof(Thm, args, args_end, &cmd);
        ENSURE("bad stack slot", IS_EXPR(*cmd));
        // alloc g_bp, g_data, g_type;
        cmd_unpack(cmd, &g_bp, &g_data, &g_type);
        ENSURE("stack has more than one element", g_bp == 0);
        ENSURE("conclusion should have provable sort",
          (g_sorts[TYPE_SORT(g_type)] & SORT_PROVABLE) != 0)
        // free g_bp, g_data, g_type;

        if (IS_CMD_STMT_THM(*p_stmt)) {
          cmd_thm* c = (cmd_thm*)p_stmt;
          u64* args2 = (u64*)(c+1);
          u64* args_end2 = &args2[t->num_args];
          u64* heap_end2 = args_end2;
          u64* heap_cap2 = &args_end2[c->heap_sz];
          u32* theap_end2 = (u32*)heap_cap2;
          u32* theap_cap2 = &theap_end2[c->theap_sz];

          u8* cmd2;
          for (u64 *p = args, *q = args2; p < args_end; p++, q++)
            ENSURE("bad variable on heap", *p == *q);
          u8* cmd;

          ENSURE("unimplemented", false);
        }
        g_num_thms++;
      } break;

      default: {
        ENSURE("bad statement command", false);
      } break;
    }
    p_stmt = next_stmt;
  }

  ENSURE("not all sorts proved", g_num_sorts == p->num_sorts);
  ENSURE("not all terms proved", g_num_terms == p->num_terms);
  ENSURE("not all theorems proved", g_num_thms == p->num_thms);
}
