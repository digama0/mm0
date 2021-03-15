#include "verifier_types.c"
#ifndef BARE
#include <stdio.h>
#include <stdlib.h>

void debug_print_expr(u32 n, u32 max, bool type) {
  if (n % 4 != 0) {fprintf(stderr, "unaligned expr"); return;}
  if (n >= max) {fprintf(stderr, "expr out of range"); return;}
  store_expr* p = (store_expr*)&g_store[n];
  bool bound = (p->type & TYPE_BOUND_MASK) != 0;
  if (type && bound) fprintf(stderr, "{");
  switch (((store_expr*)&g_store[n])->tag) {
    case EXPR_VAR: {
      store_var* v = (store_var*)p;
      char* name = lookup_var_name(v->var);
      if (name) fprintf(stderr, "%s", name);
      else fprintf(stderr, "v%d", v->var);
    } break;

    case EXPR_TERM: {
      store_term* t = (store_term*)p;
      char* name = lookup_term(t->termid);
      if (name) fprintf(stderr, "(%s", name);
      else fprintf(stderr, "(t%d", t->termid);
      for (int i = 0; i < t->num_args; i++) {
        fprintf(stderr, " ");
        debug_print_expr(t->args[i], n, false);
      }
      fprintf(stderr, ")");
    } break;

    default: fprintf(stderr, "?"); break;
  }
  char* name;
  if (type && (name = lookup_sort((p->type >> 56) & 0x7F))) {
    fprintf(stderr, ":%s", name);
  }
  if (type && bound) fprintf(stderr, "}");
}

void debug_print_conv(u32 n, u32 max, bool type) {
  if (n % 4 != 0) {fprintf(stderr, "unaligned expr"); return;}
  if (n >= max) {fprintf(stderr, "expr out of range"); return;}
  store_conv* c = (store_conv*)&g_store[n];
  debug_print_expr(c->e1, n, false);
  fprintf(stderr, " = ");
  debug_print_expr(c->e2, n, type);
}

#ifdef NO_PARSER
void debug_print_parse_expr(u32 n) {}
#else
void debug_print_parse_expr(u32 n) {
  if (n % 4 != 0) {fprintf(stderr, "unaligned expr"); return;}
  if (n >= g_store_size) {fprintf(stderr, "expr out of range"); return;}
  switch (g_store[n]) {
    case EXPR_VAR: {
      fprintf(stderr, "v%d", ((parse_var*)&g_store[n])->var);
    } break;

    case EXPR_TERM: {
      parse_term* t = (parse_term*)&g_store[n];
      char* name = lookup_term(t->termid);
      if (name) fprintf(stderr, "(%s", name);
      else fprintf(stderr, "(t%d", t->termid);
      for (int i = 0; i < t->num_args; i++) {
        fprintf(stderr, " ");
        debug_print_parse_expr(t->args[i]);
      }
      fprintf(stderr, ")");
    } break;

    default: fprintf(stderr, "?"); break;
  }
}
#endif

u32 debug_stackel_size(u32* p) {
  switch (*p & STACK_TYPE_MASK) {
    case STACK_TYPE_EXPR: return 1;
    case STACK_TYPE_PROOF: return 1;
    case STACK_TYPE_CONV: return 2;
    case STACK_TYPE_CO_CONV: return 2;
    default: UNREACHABLE();
  }
}

void debug_print_stackel(u32* p) {
  switch (*p & STACK_TYPE_MASK) {
    case STACK_TYPE_EXPR: {
      fprintf(stderr, "expr ");
      debug_print_expr(*p & STACK_DATA_MASK, g_store_size, true);
    } break;
    case STACK_TYPE_PROOF: {
      fprintf(stderr, "proof ");
      debug_print_expr(*p & STACK_DATA_MASK, g_store_size, true);
    } break;
    case STACK_TYPE_CONV: {
      debug_print_expr(*p & STACK_DATA_MASK, g_store_size, false);
      fprintf(stderr, " = ");
      debug_print_expr(*(p-1) & STACK_DATA_MASK, g_store_size, true);
    } break;
    case STACK_TYPE_CO_CONV: {
      debug_print_expr(*p & STACK_DATA_MASK, g_store_size, false);
      fprintf(stderr, " =?= ");
      debug_print_expr(*(p-1) & STACK_DATA_MASK, g_store_size, true);
    } break;
    default: UNREACHABLE();
  }
}

void debug_print_heapel(u32* p) {
  switch (*p & STACK_TYPE_MASK) {
    case STACK_TYPE_EXPR: {
      fprintf(stderr, "expr ");
      debug_print_expr(*p & STACK_DATA_MASK, g_store_size, true);
    } break;
    case STACK_TYPE_PROOF: {
      fprintf(stderr, "proof ");
      debug_print_expr(*p & STACK_DATA_MASK, g_store_size, true);
    } break;
    case STACK_TYPE_CONV: {
      debug_print_conv(*p & STACK_DATA_MASK, g_store_size, true);
    } break;
    default: fprintf(stderr, "?");
  }
}

void debug_print_stack() {
  if (!g_parsing) {
    fprintf(stderr, "stack:\n");
    for (u32* p = g_stack_top - 1; p >= g_stack; p -= debug_stackel_size(p)) {
      debug_print_stackel(p);
      fprintf(stderr, "\n");
    }
  }
}

void debug_print_heap() {
  if (!g_parsing) {
    fprintf(stderr, "heap:\n");
    for (int i = 0; i < g_heap_size; i++) {
      fprintf(stderr, "%d: ", i); debug_print_heapel(&g_heap[i]); fprintf(stderr, "\n");
    }
  }
}

void debug_print_ustack() {
  fprintf(stderr, "unify stack:\n");
  for (u32* p = g_ustack_top - 1; p >= g_ustack; p--) {
    if (g_parsing)
      debug_print_parse_expr(*p);
    else
      debug_print_expr(*p, g_store_size, true);
    fprintf(stderr, "\n");
  }
}

void debug_print_uheap() {
  fprintf(stderr, "unify heap:\n");
  for (int i = 0; i < g_uheap_size; i++) {
    fprintf(stderr, "%d: ", i);
    if (g_parsing)
      debug_print_parse_expr(g_uheap[i]);
    else
      debug_print_expr(g_uheap[i], g_store_size, true);
    fprintf(stderr, "\n");
  }
}

u32 debug_cmd_unpack(u8* cmd, u32* data_out) {
  if (!cmd) {
    fprintf(stderr, "null");
    return 0;
  }
  if (cmd < g_file || cmd + CMD_MAX_SIZE > g_end) {
    fprintf(stderr, "%lX: command out of range", cmd - g_file);
    return 0;
  }
  switch (CMD_DATA(*cmd)) {
    case CMD_DATA_0: {
      *data_out = 0;
      return sizeof(cmd0);
    } break;

    case CMD_DATA_8: {
      cmd8* p = (cmd8*)cmd;
      *data_out = p->data;
      return sizeof(cmd8);
    } break;

    case CMD_DATA_16: {
      cmd16* p = (cmd16*)cmd;
      *data_out = p->data;
      return sizeof(cmd16);
    } break;

    case CMD_DATA_32: {
      cmd32* p = (cmd32*)cmd;
      *data_out = p->data;
      return sizeof(cmd32);
    } break;
  }
  UNREACHABLE();
}

void debug_print_cmd(u8* cmd, u32 data) {
  if (!cmd) return;
  u64 pos = cmd - g_file;
  if (cmd < g_file || cmd + CMD_MAX_SIZE > g_end) {
    fprintf(stderr, "%lX: command out of range", pos);
    return;
  }
  switch (*cmd & 0x3F) {
    case CMD_END: fprintf(stderr, "%lX: End", pos); break;

    case CMD_PROOF_REF: {
      fprintf(stderr, "%lX: Ref %d", pos, data);
      if (data < g_heap_size) {
        fprintf(stderr, "  // = ");
        debug_print_stackel(&g_heap[data]);
      }
    } break;

    case CMD_PROOF_TERM:
    case CMD_PROOF_TERM_SAVE: {
      fprintf(stderr, "%lX: Term %d", pos, data);
      char* name;
      if (data < g_num_terms && (name = lookup_term(data))) {
        fprintf(stderr, "  // = %s", name);
      }
      if (*cmd & 0x01) fprintf(stderr, "\n  %lX: Save", pos);
    } break;

    case CMD_PROOF_DUMMY: {
      fprintf(stderr, "%lX: Dummy %d", pos, data);
      char* name;
      if (data < g_num_sorts && (name = lookup_sort(data))) {
        fprintf(stderr, "  // = %s", name);
      }
    } break;

    case CMD_PROOF_THM:
    case CMD_PROOF_THM_SAVE: {
      fprintf(stderr, "%lX: Thm %d", pos, data);
      char* name;
      if (data < g_num_thms && (name = lookup_thm(data))) {
        fprintf(stderr, "  // = %s", name);
      }
      if (*cmd & 0x01) fprintf(stderr, "\n%lX: Save", pos);
    } break;

    case CMD_PROOF_HYP: fprintf(stderr, "%lX: Hyp", pos); break;
    case CMD_PROOF_CONV: fprintf(stderr, "%lX: Conv", pos); break;
    case CMD_PROOF_REFL: fprintf(stderr, "%lX: Refl", pos); break;
    case CMD_PROOF_SYMM: fprintf(stderr, "%lX: Symm", pos); break;
    case CMD_PROOF_CONG: fprintf(stderr, "%lX: Cong", pos); break;
    case CMD_PROOF_UNFOLD: fprintf(stderr, "%lX: Unfold", pos); break;
    case CMD_PROOF_CONV_CUT: fprintf(stderr, "%lX: ConvCut", pos); break;

    case CMD_PROOF_CONV_REF: {
      fprintf(stderr, "%lX: ConvRef %d", pos, data);
      if (data < g_heap_size) {
        fprintf(stderr, "  // = ");
        debug_print_stackel(&g_heap[data]);
      }
    } break;

    case CMD_PROOF_CONV_SAVE: fprintf(stderr, "%lX: ConvSave", pos); break;
    case CMD_PROOF_SAVE: fprintf(stderr, "%lX: Save", pos); break;

    case CMD_UNIFY_REF: {
      fprintf(stderr, "%lX: URef %d", pos, data);
      if (data < g_uheap_size) {
        fprintf(stderr, "  // = ");
        if (g_parsing)
          debug_print_parse_expr(g_uheap[data]);
        else
          debug_print_expr(g_uheap[data], g_store_size, true);
      }
    } break;

    case CMD_UNIFY_TERM:
    case CMD_UNIFY_TERM_SAVE: {
      fprintf(stderr, "%lX: UTerm %d", pos, data);
      char* name;
      if (data < g_num_terms && (name = lookup_term(data))) {
        fprintf(stderr, "  // = %s", name);
      }
      if (*cmd & 0x01) fprintf(stderr, "\n%lX: Save", pos);
    } break;

    case CMD_UNIFY_DUMMY: {
      fprintf(stderr, "%lX: UDummy", pos);
    } break;

    case CMD_UNIFY_HYP: {
      fprintf(stderr, "%lX: UHyp", pos);
    } break;

    default: {
      fprintf(stderr, "%lX: ?%02X", pos, *cmd);
    } break;
  }
  fprintf(stderr, "\n");
}

void debug_print_cmds(u8* cmd, u8* stop) {
  if (!cmd) return;
  if (cmd < g_file || cmd + CMD_MAX_SIZE > g_end) {
    fprintf(stderr, "%lX: command out of range", cmd - g_file);
    return;
  }
  while (*cmd != CMD_END) {
    u32 data;
    u32 sz = debug_cmd_unpack(cmd, &data);
    if (!sz) return;
    if (cmd == stop) fprintf(stderr, "> ");
    else fprintf(stderr, "  ");
    debug_print_cmd(cmd, data);
    // if (cmd == stop) return;
    cmd += sz;
  }
}

void debug_print_input();

#endif
