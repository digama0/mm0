#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include "types.c"

#define UNREACHABLE() __builtin_unreachable()
#define EENSURE(err, e, cond) \
  if (__builtin_expect(!(cond), 0)) { \
    fprintf(stderr, err); \
    exit(e); \
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
ALIGNED(4) u8 g_store[STORE_SIZE];
u32 g_store_size;

typedef struct ALIGNED(4) {
  u64 type;
  u8 tag;
} store_expr;
#define get_expr(p) ((store_expr*)&g_store[p])

#define EXPR_VAR 0
typedef struct ALIGNED(4) {
  u64 type;
  u8 tag; // = EXPR_VAR
  u16 var;
} store_var;
#define get_var(p) ({ \
  store_var* e = (store_var*)&g_store[p]; \
  ENSURE("store type error", e->tag == EXPR_VAR); \
  e; \
})

#define EXPR_TERM 1
typedef struct ALIGNED(4) {
  u64 type;
  u8 tag; // = EXPR_TERM
  u16 num_args;
  u32 termid;
  u32 args[];
} store_term;
#define get_term(p) ({ \
  store_term* e = (store_term*)&g_store[p]; \
  ENSURE("store type error", e->tag == EXPR_TERM); \
  e; \
})

#define EXPR_CONV 2
typedef struct ALIGNED(4) {
  u32 e1;
  u32 e2;
  u8 tag; // = EXPR_CONV
} store_conv;
#define get_conv(p) ({ \
  store_conv* e = (store_conv*)&g_store[p]; \
  ENSURE("store type error", e->tag == EXPR_CONV); \
  e; \
})

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
// scratch space
u64 g_deps[256];
u32 g_data;

#define push_stack(val) { \
  ENSURE("stack overflow", g_stack_top < &g_stack[STACK_SIZE]); \
  *g_stack_top++ = val; \
}

#define push_heap(val) { \
  ENSURE("heap overflow", g_heap_size < HEAP_SIZE); \
  g_heap[g_heap_size++] = val; \
}

#define ALLOC(val, size) ({ \
  ENSURE("store overflow", g_store_size + size <= STORE_SIZE); \
  u32 p = g_store_size; \
  *(typeof(val)*)&g_store[p] = val; \
  g_store_size += size; \
  p; \
})

static inline u32 as_type(u32 val, u32 type) {
  ENSURE("bad stack slot", (val & STACK_TYPE_MASK) == type);
  return val & STACK_DATA_MASK;
}

#define pop_stack() ({ \
  ENSURE("unify stack underflow", g_stack_top > g_stack); \
  *(--g_stack_top); \
})

#define pop_ustack() ({ \
  ENSURE("unify stack underflow", g_ustack_top > g_ustack); \
  *(--g_ustack_top); \
})

#define push_uheap(val) { \
  ENSURE("unify heap overflow", g_uheap_size < UNIFY_HEAP_SIZE); \
  g_uheap[g_uheap_size++] = val; \
}

u32 cmd_unpack(u8* cmd) {
  ENSURE("command out of range", cmd + CMD_MAX_SIZE <= g_end);
  switch (CMD_DATA(*cmd)) {
    case CMD_DATA_0: {
      g_data = 0;
      return sizeof(cmd);
    } break;

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

void load_args(u64 args[], u32 num_args) {
  g_next_bv = 1;
  ENSURE("bad args pointer", (u8*)&args[num_args] <= g_end);
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
      ALLOC(((store_var){ty, EXPR_VAR, i}), sizeof(store_var)));
  }
}

typedef enum { UDef, UThm, UThmEnd } unify_mode;

void run_unify(unify_mode mode, u8* cmd, u32 tgt) {
  g_ustack_top = &g_ustack[1];
  g_ustack[0] = tgt;
  u8* last_cmd = cmd;
  while (true) {
    u32 sz = cmd_unpack(cmd); // sets g_data
    ENSURE("command out of range", cmd + CMD_MAX_SIZE <= g_end);

    switch (*cmd & 0x3F) {
      case CMD_END: goto loop_end;

      case CMD_UNIFY_REF: {
        ENSURE("bad ref step", g_data < g_uheap_size);
        ENSURE("unify failure at ref", g_uheap[g_data] == pop_ustack());
      } break;

      case CMD_UNIFY_TERM:
      case CMD_UNIFY_TERM_SAVE: {
        u32 p = pop_ustack();
        store_term* e = get_term(p);
        ENSURE("unify failure at term", e->termid == g_data);
        ENSURE("unify stack overflow",
          &g_ustack_top[e->num_args] <= &g_ustack[UNIFY_STACK_SIZE]);
        for (int i = 0; i < e->num_args; i++) {
          g_ustack_top[i] = e->args[i];
        }
        if (*cmd & 0x01) // save
          push_uheap(p);
      } break;

      case CMD_UNIFY_DUMMY: {
        ENSURE("Dummy command not allowed in theorem statements", mode == UDef);
        u32 p = pop_ustack();
        store_var* e = get_var(p);
        u64 type = e->type;
        ENSURE("unify failure at dummy", (type >> 56) == (0x80 | g_data));
        type &= TYPE_DEPS_MASK;
        for (int i = 0; i < g_uheap_size; i++) {
          ENSURE("dummy DV violation",
            (get_var(g_uheap[i])->type & type) == 0);
        }
        push_uheap(p);
      } break;

      case CMD_UNIFY_HYP: {
        switch (mode) {
          case UThm: {
            push_uheap(as_type(pop_stack(), STACK_TYPE_PROOF));
          } break;

          case UThmEnd: {
            ENSURE("Unfinished unify stack", g_ustack_top == g_ustack);
            ENSURE("unify stack overflow",
              g_ustack_top < &g_ustack[UNIFY_STACK_SIZE]);
            ENSURE("hypothesis stack underflow", g_hstack_top > g_hstack);
            *(g_ustack_top++) = *(--g_hstack_top);
          } break;

          default: {
            ENSURE("Hyp command not allowed in definition statements", false);
          } break;
        }
      } break;

      default: {
        if (mode == UDef) {
          ENSURE("Unknown opcode in def statement", false);
        } else {
          ENSURE("Unknown opcode in theorem statement", false);
        }
      } break;
    }
    last_cmd = cmd;
    cmd += sz;
  }
  loop_end:
  if (mode == UThmEnd)
    ENSURE("Unfinished hypothesis stack", g_hstack_top == g_hstack);
  ENSURE("Unfinished unify stack", g_ustack_top == g_ustack);
}

typedef enum { Def, Thm } proof_mode;

u8* run_proof(proof_mode mode, u8* cmd) {
  u8* last_cmd = cmd;
  while (true) {
    u32 sz = cmd_unpack(cmd); // sets g_data
    switch (*cmd & 0x3F) {
      case CMD_END: goto loop_end;

      case CMD_PROOF_REF: {
        ENSURE("bad ref step", g_data < g_heap_size);
        push_stack(g_heap[g_data]);
      } break;

      case CMD_PROOF_DUMMY: {
        ENSURE("bad dummy sort", g_data < g_num_sorts);
        ENSURE("dummy variable in strict sort",
          (g_sorts[g_data] & SORT_STRICT) == 0);
        ENSURE("too many bound variables, please rewrite the verifier",
          (g_next_bv >> 56) == 0);
        u64 type = TYPE_BOUND_MASK | ((u64)g_data << 56) | g_next_bv;
        g_next_bv *= 2;
        push_heap(STACK_TYPE_EXPR |
          ALLOC(((store_var){type, EXPR_VAR, g_heap_size}), sizeof(store_var)));
      } break;

      case CMD_PROOF_TERM:
      case CMD_PROOF_TERM_SAVE: {
        ENSURE("term out of range", g_data < g_num_terms);
        term* t = &g_terms[g_data];
        u64* targs = (u64*)&g_file[t->p_args];
        ENSURE("stack underflow", g_stack_top >= &g_stack[t->num_args]);
        g_stack_top -= t->num_args;
        // alloc g_deps;
        u8 bound = 0;
        u64 accum = 0;
        u32 p = ALLOC(((store_term){(u64)(t->sort & 0x7F) << 56,
          EXPR_TERM, t->num_args, g_data}), sizeof(store_term) + 4 * t->num_args);
        store_term* result = get_term(p);
        for (u16 i = 0; i < t->num_args; i++) {
          u32 arg = as_type(g_stack_top[i], STACK_TYPE_EXPR);
          result->args[i] = arg;
          store_expr* e = get_expr(arg);
          u64 target = targs[i];
          ENSURE("type mismatch", sorts_compatible(e->type, target));
          u64 deps = e->type & TYPE_DEPS_MASK;
          if (target & TYPE_BOUND_MASK) {
            g_deps[bound++] = deps;
          } else {
            if (mode == Def)
              for (u8 j = 0; j < bound; j++)
                if (target & ((u64)1<<j))
                  deps &= ~g_deps[j];
            accum |= deps;
          }
        }
        if (mode == Def) {
          u64 target = targs[t->num_args] & TYPE_DEPS_MASK;
          if (target)
            for (u8 j = 0; j < bound; j++)
              if (target & ((u64)1<<j))
                accum |= g_deps[j];
        }
        // free g_deps;
        result->type = accum;
        push_stack(STACK_TYPE_EXPR | p);
        if (*cmd & 0x01) // save
          push_heap(STACK_TYPE_EXPR | p);
      } break;

      case CMD_PROOF_THM:
      case CMD_PROOF_THM_SAVE: {
        ENSURE("Invalid opcode in def", cmd != Def);
        ENSURE("theorem out of range", g_data < g_num_thms);
        thm* t = &g_thms[g_data];
        u64* targs = (u64*)&g_file[t->p_args];
        u32 e = as_type(pop_stack(), STACK_TYPE_EXPR);
        ENSURE("stack underflow", g_stack_top >= &g_stack[t->num_args]);
        g_stack_top -= t->num_args;
        g_uheap_size = t->num_args;
        for (u16 i = 0; i < t->num_args; i++) {
          g_uheap[i] = as_type(g_stack_top[i], STACK_TYPE_EXPR);
          // TODO: DV conditions
        }
        run_unify(UThm, (u8*)&targs[t->num_args], e);
        push_stack(STACK_TYPE_PROOF | e);
        if (*cmd & 0x01) // save
          push_heap(STACK_TYPE_PROOF | e);
      } break;

      case CMD_PROOF_HYP: {
        ENSURE("Invalid opcode in def", cmd != Def);
        u32 e = as_type(pop_stack(), STACK_TYPE_EXPR);
        ENSURE("hypothesis stack overflow", g_hstack_top < &g_hstack[HYP_STACK_SIZE]);
        *g_hstack_top++ = e;
        push_heap(STACK_TYPE_PROOF | e);
      } break;

      case CMD_PROOF_CONV: {
        u32 e2 = as_type(pop_stack(), STACK_TYPE_PROOF);
        u32 e1 = as_type(pop_stack(), STACK_TYPE_EXPR);
        push_stack(STACK_TYPE_PROOF | e1);
        push_stack(STACK_TYPE_EXPR | e2);
        push_stack(STACK_TYPE_CO_CONV | e1);
      } break;

      case CMD_PROOF_REFL: {
        u32 e1 = as_type(pop_stack(), STACK_TYPE_CO_CONV);
        u32 e2 = as_type(pop_stack(), STACK_TYPE_EXPR);
        ENSURE("Refl unify failure", e1 == e2);
      } break;

      case CMD_PROOF_SYMM: {
        u32 e1 = as_type(pop_stack(), STACK_TYPE_CO_CONV);
        u32 e2 = as_type(pop_stack(), STACK_TYPE_EXPR);
        push_stack(STACK_TYPE_EXPR | e1);
        push_stack(STACK_TYPE_CO_CONV | e2);
      } break;

      case CMD_PROOF_CONG: {
        store_term* e1 = get_term(as_type(pop_stack(), STACK_TYPE_CO_CONV));
        store_term* e2 = get_term(as_type(pop_stack(), STACK_TYPE_EXPR));
        ENSURE("Cong unify error", e1->termid == e2->termid);
        for (int i = e1->num_args - 1; i >= 0; i--) {
          push_stack(STACK_TYPE_EXPR | e2->args[i]);
          push_stack(STACK_TYPE_CO_CONV | e1->args[i]);
        }
      } break;

      case CMD_PROOF_UNFOLD: {
        u32 e = as_type(pop_stack(), STACK_TYPE_EXPR);
        u32 e1 = as_type(pop_stack(), STACK_TYPE_EXPR);
        store_term* p = get_term(e1);
        term* t = &g_terms[p->termid];
        ENSURE("Unfold: not a definition", (t->sort & 0x80) != 0);
        u64* targs = (u64*)&g_file[t->p_args];
        g_uheap_size = p->num_args;
        for (u16 i = 0; i < p->num_args; i++) {
          g_uheap[i] = p->args[i];
          // TODO: DV conditions
        }
        run_unify(UThm, (u8*)&targs[p->num_args], e);
        ENSURE("Unfold unify error", e1 == as_type(pop_stack(), STACK_TYPE_CO_CONV));
        u32 e2 = as_type(pop_stack(), STACK_TYPE_EXPR);
        push_stack(STACK_TYPE_EXPR | e2);
        push_stack(STACK_TYPE_CO_CONV | e);
      } break;

      case CMD_PROOF_CONV_CUT: {
        u32 e2 = as_type(pop_stack(), STACK_TYPE_EXPR);
        u32 e1 = as_type(pop_stack(), STACK_TYPE_EXPR);
        push_stack(STACK_TYPE_EXPR | e2);
        push_stack(STACK_TYPE_CONV | e1);
        push_stack(STACK_TYPE_EXPR | e2);
        push_stack(STACK_TYPE_CO_CONV | e1);
      } break;

      case CMD_PROOF_CONV_REF: {
          ENSURE("bad ConvRef step", g_data < g_heap_size);
        store_conv* c = get_conv(as_type(g_heap[g_data], STACK_TYPE_CONV));
        u32 e1 = as_type(pop_stack(), STACK_TYPE_CO_CONV);
        u32 e2 = as_type(pop_stack(), STACK_TYPE_EXPR);
        ENSURE("ConvRef unify error", c->e1 == e1 && c->e2 == e2);
      } break;

      default: {
        if (mode == Def) {
          ENSURE("Unknown opcode in def", false);
        } else {
          ENSURE("Unknown opcode in theorem", false);
        }
      } break;
    }
    last_cmd = cmd;
    cmd += sz;
  }
  loop_end:
  return cmd;
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
      case CMD_STMT_SORT: {
        ENSURE("Next statement incorrect", stmt->next == sizeof(cmd_stmt));
        ENSURE("Step sort overflow", g_num_sorts < p->num_sorts);
        g_num_sorts++;
      } break;

      // case CMD_STMT_TERM: // = CMD_STMT_DEF
      case CMD_STMT_DEF:
      case CMD_STMT_LOCAL_DEF: {
        term* t = &g_terms[g_num_terms];
        ENSURE("Step term overflow", g_num_terms < p->num_terms);
        u8 sort = t->sort & 0x7F;
        ENSURE("bad sort", sort < g_num_sorts);
        ENSURE("term in pure sort", (g_sorts[sort] & SORT_PURE) == 0);
        u64* args = (u64*)&file[t->p_args];
        u64* args_ret = &args[t->num_args];
        u8* ucmd = (u8*)&args_ret[1];
        g_store_size = 0;
        g_heap_size = 0;
        g_stack_top = g_stack;
        load_args(args, t->num_args + 1);
        u64 ret = *args_ret;
        ENSURE("bad return type", (ret >> 56) == sort);
        g_heap_size--;

        if (t->sort & 0x80) {
          ENSURE("Next statement incorrect",
            next_stmt == run_proof(Def, stmt->proof));
          ENSURE("stack has != one element", g_stack_top == &g_stack[1]);
          u32 val = g_stack[0];
          ENSURE("bad stack slot", (val & STACK_TYPE_MASK) == STACK_TYPE_EXPR);
          val &= STACK_DATA_MASK;
          u64 type = get_expr(val)->type;
          ENSURE("type mismatch", sorts_compatible(type, ret));
          ENSURE("type has unaccounted dependencies",
            (type & TYPE_DEPS_MASK & ~ret) == 0);
          run_unify(UDef, ucmd, val);
        } else {
          ENSURE("Next statement incorrect", stmt->next == sizeof(cmd_stmt));
        }
        g_num_terms++;
      } break;

      case CMD_STMT_AXIOM:
      case CMD_STMT_THM:
      case CMD_STMT_LOCAL_THM: {
        thm* t = &g_thms[g_num_thms];
        ENSURE("Step theorem overflow", g_num_thms < p->num_thms);
        u64* args = (u64*)&file[t->p_args];
        load_args(args, t->num_args);
        ENSURE("Next statement incorrect",
          next_stmt == run_proof(Thm, stmt->proof));
        ENSURE("stack has != one element", g_stack_top == &g_stack[1]);
        u32 val = g_stack[0];
        ENSURE("bad stack slot", (val & STACK_TYPE_MASK) ==
          (IS_CMD_STMT_THM(stmt->cmd) ? STACK_TYPE_PROOF : STACK_TYPE_EXPR));
        val &= STACK_DATA_MASK;
        ENSURE("conclusion should have provable sort",
          (g_sorts[TYPE_SORT(get_expr(val)->type)] & SORT_PROVABLE) != 0)
        run_unify(UThmEnd, (u8*)&args[t->num_args], val);
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
