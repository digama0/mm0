#include "verifier_types.c"

void debug_print_expr(u32 n, bool type) {
  if (n % 4 != 0) {printf("unaligned expr"); return;}
  if (n >= g_store_size) {printf("expr out of range"); return;}
  store_expr* p = (store_expr*)&g_store[n];
  bool bound = (p->type & TYPE_BOUND_MASK) != 0;
  if (type && bound) printf("{");
  switch (((store_expr*)&g_store[n])->tag) {
    case EXPR_VAR: {
      printf("v%d", ((store_var*)p)->var);
    } break;

    case EXPR_TERM: {
      store_term* t = (store_term*)p;
      index* ix = lookup_term(t->termid);
      if (ix) printf("(%s", ix->value);
      else printf("(t%d", t->termid);
      for (int i = 0; i < t->num_args; i++) {
        printf(" ");
        debug_print_expr(t->args[i], false);
      }
      printf(")");
    } break;

    case EXPR_CONV: {
      store_conv* c = (store_conv*)p;
      debug_print_expr(c->e1, false);
      printf(" = ");
      debug_print_expr(c->e2, false);
    } break;

    default: printf("?"); break;
  }
  index* ix;
  if (type && (ix = lookup_sort((p->type >> 56) & 0x7F))) {
    printf(":%s", ix->value);
  }
  if (type && bound) printf("}");
}

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
      printf("expr ");
      debug_print_expr(*p & STACK_DATA_MASK, true);
    } break;
    case STACK_TYPE_PROOF: {
      printf("proof ");
      debug_print_expr(*p & STACK_DATA_MASK, true);
    } break;
    case STACK_TYPE_CONV: {
      debug_print_expr(*p & STACK_DATA_MASK, false);
      printf(" = ");
      debug_print_expr(*(p-1) & STACK_DATA_MASK, true);
    } break;
    case STACK_TYPE_CO_CONV: {
      debug_print_expr(*p & STACK_DATA_MASK, false);
      printf(" =?= ");
      debug_print_expr(*(p-1) & STACK_DATA_MASK, true);
    } break;
    default: UNREACHABLE();
  }
}

void debug_print_stack_rec(u32* p) {
  if (p < g_stack) return;
  debug_print_stack_rec(p - debug_stackel_size(p));
  debug_print_stackel(p);
  printf("\n");
}

void debug_print_stack() {
  printf("stack:\n");
  debug_print_stack_rec(g_stack_top - 1);
}

void debug_print_heap() {
  printf("heap:\n");
  for (int i = 0; i < g_heap_size; i++) {
    printf("%d: "); debug_print_stackel(&g_heap[i]); printf("\n");
  }
}

void debug_print_ustack() {
  printf("ustack:\n");
  for (u32* p = g_ustack; p < g_ustack_top; p++) {
    debug_print_expr(*p, true);
    printf("\n");
  }
}

void debug_print_uheap() {
  printf("uheap:\n");
  for (int i = 0; i < g_uheap_size; i++) {
    printf("%d: ");
    debug_print_expr(g_uheap[i], true);
    printf("\n");
  }
}

u32 debug_cmd_unpack(u8* cmd, u32* data_out) {
  if (cmd + CMD_MAX_SIZE > g_end) {
    printf("command out of range");
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
  if (cmd + CMD_MAX_SIZE > g_end) {
    printf("command out of range");
    return;
  }
  u64 pos = cmd - g_file;
  switch (*cmd & 0x3F) {
    case CMD_END: printf("%X: End", pos); break;

    case CMD_PROOF_REF: {
      printf("%X: Ref %d", pos, data);
      if (data < g_heap_size) {
        printf("  // = ");
        debug_print_stackel(&g_heap[data]);
      }
    } break;

    case CMD_PROOF_TERM:
    case CMD_PROOF_TERM_SAVE: {
      printf("%X: Term %d", pos, data);
      index* ix;
      if (data < g_num_terms && (ix = lookup_term(data))) {
        printf("  // = %s", ix->value);
      }
      if (*cmd & 0x01) printf("\n%X: Save", pos);
    } break;

    case CMD_PROOF_DUMMY: {
      printf("%X: Dummy %d", pos, data);
      index* ix;
      if (data < g_num_sorts && (ix = lookup_sort(data))) {
        printf("  // = %s", ix->value);
      }
    } break;

    case CMD_PROOF_THM:
    case CMD_PROOF_THM_SAVE: {
      printf("%X: Thm %d", pos, data);
      index* ix;
      if (data < g_num_thms && (ix = lookup_thm(data))) {
        printf("  // = %s", ix->value);
      }
      if (*cmd & 0x01) printf("\n%X: Save", pos);
    } break;

    case CMD_PROOF_HYP: printf("%X: Hyp", pos); break;
    case CMD_PROOF_CONV: printf("%X: Conv", pos); break;
    case CMD_PROOF_REFL: printf("%X: Refl", pos); break;
    case CMD_PROOF_SYMM: printf("%X: Symm", pos); break;
    case CMD_PROOF_CONG: printf("%X: Cong", pos); break;
    case CMD_PROOF_UNFOLD: printf("%X: Unfold", pos); break;
    case CMD_PROOF_CONV_CUT: printf("%X: ConvCut", pos); break;

    case CMD_PROOF_CONV_REF: {
      printf("%X: ConvRef %d", pos, data);
      if (data < g_heap_size) {
        printf("  // = ");
        debug_print_stackel(&g_heap[data]);
      }
    } break;

    case CMD_UNIFY_REF: {
      printf("%X: URef %d", pos, data);
      if (data < g_uheap_size) {
        printf("  // = ");
        debug_print_expr(g_uheap[data], true);
      }
    } break;

    case CMD_UNIFY_TERM:
    case CMD_UNIFY_TERM_SAVE: {
      printf("%X: UTerm %d", pos, data);
      index* ix;
      if (data < g_num_terms && (ix = lookup_term(data))) {
        printf("  // = %s", ix->value);
      }
      if (*cmd & 0x01) printf("\n%X: Save", pos);
    } break;

    case CMD_UNIFY_DUMMY: {
      printf("%X: UDummy", pos);
    } break;

    case CMD_UNIFY_HYP: {
      printf("%X: UHyp", pos);
    } break;

    default: {
      printf("%X: ?%02X", pos, *cmd);
    } break;
  }
  printf("\n");
}

void debug_print_cmds(u8* cmd, u8* stop) {
  if (cmd + CMD_MAX_SIZE > g_end) {
    printf("command out of range");
    return;
  }
  while (*cmd != CMD_END) {
    u32 data;
    u32 sz = debug_cmd_unpack(cmd, &data);
    if (!sz) return;
    debug_print_cmd(cmd, data);
    if (cmd == stop) return;
    cmd += sz;
  }
}
