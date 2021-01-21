#include <unistd.h>
#include <stdio.h>
#include <string.h>
#include "verifier.c"

#ifdef NO_PARSER
void parse_until(u8 stmt_type) {}
void init_parser() {}
#ifndef BARE
void debug_print_input() {}
#endif
#else

#define PARSER_ALLOC(val, size) ({ \
  ENSURE("parser store overflow", g_parser_arena_size + (size) <= PARSER_ARENA_SIZE); \
  u32 p = g_parser_arena_size; \
  *(typeof(val)*)&g_parser_arena[p] = val; \
  g_parser_arena_size += (size)/4; \
  p; \
})

void fill_buffer() {
  if (!eof) {
    // Always at least 10 readable bytes after buffer_end
    EENSURE("Input buffer overflow", 2,
      buffer_end < buffer + (INPUT_SIZE - BUFFER_OVERSHOOT));
    ssize_t count = read(STDIN_FILENO,
      buffer_end, (buffer + (INPUT_SIZE-1)) - buffer_end);
    EENSURE("IO error", 4, count >= 0);
    if (count == 0) {
      eof = 1;
      *buffer_end++ = 0;
    } else while (count-- > 0) {
      ENSURE("Null character in input", *buffer_end++);
    }
  }
}

int fill_to(int n) {
  while ((buffer_end - cursor < n) && !eof) fill_buffer();
  return !eof;
}

#define CUR() (*cursor || eof ? *cursor : ({fill_buffer(); *cursor;}))

// True if this is a valid whitespace character
#define is_ws(c) (c == '\n' || c == ' ')

void ws() {
  start: while(1) {
    fill_to(2);
    if (*cursor == 0) {
      if (eof) return;
    } else if (*cursor == '-' && cursor[1] == '-') {
      cursor += 2;
      while (1) {
        while (*cursor) {
          if (*cursor++ == '\n') goto start;
        }
        if (eof) return;
        fill_buffer();
      }
    } else if (is_ws(*cursor)) {
      cursor++;
    } else return;
  }
}

#define KW_AXIOM     1
#define KW_COERCION  2
#define KW_DEF       3
#define KW_DELIMITER 4
#define KW_FREE      5
#define KW_INFIXL    6
#define KW_INFIXR    7
// #define KW_INPUT     8
#define KW_MAX       9
#define KW_NOTATION  10
#define KW_OUTPUT    11
#define KW_PREC      12
#define KW_PREFIX    13
#define KW_PROVABLE  14
#define KW_PURE      15
#define KW_SORT      16
#define KW_STRICT    17
#define KW_TERM      18
#define KW_THEOREM   19

// True if this is a valid indentifier starting character, _[A-Z][a-z]
int ident_start(u8 c) {
  return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '_';
}
// True if this is a valid indentifier remainder character, _[A-Z][a-z][0-9]
int ident_rest(u8 c) {
  return ident_start(c) || (c >= '0' && c <= '9');
}

// If the next len(str) bytes of the buffer match str, then
// add len(str) and return val, otherwise return 0.
// Note that len(str) = sizeof(str) - 1 because of the null terminator
#define check_kw(str, val) { \
  if (memcmp(str, cursor, sizeof(str)-1) == 0 && !ident_rest(cursor[sizeof(str)-1])) { \
    cursor += sizeof(str)-1; ws(); return val; \
  } else return 0; \
}

int kw() {
  fill_to(10); // size of longest keyword + 1
  switch (*cursor) {
    case 'a': check_kw("axiom", KW_AXIOM);
    case 'c': check_kw("coercion", KW_COERCION);
    case 'd': switch (cursor[2]) {
      case 'f': check_kw("def", KW_DEF);
      case 'l': check_kw("delimiter", KW_DELIMITER);
      default: return 0;
    }
    case 'f': check_kw("free", KW_FREE);
    case 'i': switch (cursor[5]) {
      case 'l': check_kw("infixl", KW_INFIXL);
      case 'r': check_kw("infixr", KW_INFIXR);
      default: return 0;
    }
    case 'm': check_kw("max", KW_MAX);
    case 'n': check_kw("notation", KW_NOTATION);
    case 'o': check_kw("output", KW_OUTPUT);
    case 'p': switch (cursor[3]) {
      case 'c': check_kw("prec", KW_PREC);
      case 'f': check_kw("prefix", KW_PREFIX);
      case 'v': check_kw("provable", KW_PROVABLE);
      case 'e': check_kw("pure", KW_PURE);
      default: return 0;
    }
    case 's': switch (cursor[1]) {
      case 'o': check_kw("sort", KW_SORT);
      case 't': check_kw("strict", KW_STRICT);
      default: return 0;
    }
    case 't': switch (cursor[1]) {
      case 'e': check_kw("term", KW_TERM);
      case 'h': check_kw("theorem", KW_THEOREM);
      default: return 0;
    }
    default: return 0;
  }
}

int ch(u8 c) {
  if (CUR() == c) {
    cursor++; ws();
    return 1;
  } else return 0;
}

u16 prec() {
  fill_to(5);
  u8 c = *cursor;
  if (c < '0' || c > '9') {
    ENSURE("expected a number or 'max'", kw() == KW_MAX);
    return -1;
  }
  for (u16 val = c - '0';;) {
    cursor++;
    c = CUR();
    if (c < '0' || c > '9') {
      ENSURE("invalid number", !ident_rest(c));
      ws();
      return val;
    }
    ENSURE("number out of range", val < 0xffff/10);
    val = val * 10 + (c - '0');
  }
}

trie extend(trie T, u32* tgt, trie* end, u32 lim) {
  if (*tgt) return T + *tgt;
  EENSURE("trie overflow", 2, *end < T+lim);
  trie result = (*end)++;
  *tgt = result - T;
  return result;
}

typedef struct { int blank; trie x; } ident_blank;

ident_blank lookup_ident_(trie T) {
  fill_to(2);
  u8 c = *cursor;
  if (!ident_start(c)) return (ident_blank){0, T};
  ident_blank res = (ident_blank){
    c == '_' && !ident_rest(cursor[1]),
    T + 1,
  };
  do {
    res.x = T + T[res.x->next[c & 0xF]].next[(c >> 4) & 0xF];
    cursor++;
    c = CUR();
  } while (ident_rest(c));
  ws();
  return res;
}

trie lookup_ident(trie T) {
  ident_blank res = lookup_ident_(T);
  ENSURE("expecting an identifier, not '_'", !res.blank);
  return res.x;
}

u32 lookup_var() {
  return ~gt_terms[lookup_ident(gt_terms)->next[0]].data;
}

ident_blank parse_new_ident_(trie T, trie* end, u32 lim) {
  fill_to(2);
  u8 c = *cursor;
  ENSURE("expecting identifier", ident_start(c));
  ident_blank res = (ident_blank){
    c == '_' && !ident_rest(cursor[1]),
    T + 1,
  };
  do {
    res.x = extend(T, &res.x->next[c & 0xF], end, lim);
    res.x = extend(T, &res.x->next[(c >> 4) & 0xF], end, lim);
    cursor++;
    c = CUR();
  } while (ident_rest(c));
  ws();
  return res;
}

trie parse_new_ident(trie T, trie* end, u32 lim) {
  ident_blank res = parse_new_ident_(T, end, lim);
  ENSURE("expecting an identifier, not '_'", !res.blank);
  return res.x;
}

u32 parse_new_token() {
  ENSURE("expecting '$'", CUR() == '$');
  do {cursor++;} while (is_ws(CUR()));
  u8 c = *cursor;
  ENSURE("expecting token character", c != '$' && c != 0);
  trie p = gt_tokens + 1;
  do {
    p = extend(gt_tokens, &p->next[c & 0xF], &gt_tokens_end, TOKEN_TRIE_SIZE);
    p = extend(gt_tokens, &p->next[(c >> 4) & 0xF], &gt_tokens_end, TOKEN_TRIE_SIZE);
    cursor++;
    c = CUR();
  } while (!is_ws(c) && c != '$');
  while (is_ws(CUR())) cursor++;
  ENSURE("expecting '$'", ch('$'));
  ENSURE("parentheses are not valid tokens", p != g_open_paren && p != g_close_paren);
  return p->data ? p->data :
    (p->data = PARSER_ALLOC(((token_info){}), sizeof(token_info)));
}

typedef struct { trie var; trie tk; } token_result;
token_result token() {
  trie var = gt_terms + 1;
  trie tk = gt_tokens + 1;
  u8 c = CUR();
  ENSURE("expecting token", c != '$' && c != 0);
  do {
    var = gt_terms + gt_terms[var->next[c & 0xF]].next[(c >> 4) & 0xF];
    tk = gt_tokens + gt_tokens[tk->next[c & 0xF]].next[(c >> 4) & 0xF];
    cursor++;
    if (g_delims[c] & DELIM_LEFT) break;
    c = CUR();
  } while (!(g_delims[c] & DELIM_RIGHT));
  while (is_ws(CUR())) cursor++;
  return (token_result){var, tk};
}

typedef struct {u32 expr; u8 sort;} expr_sort;
u32 coerce(expr_sort es, u8 tgt) {
  if (es.sort == tgt) return es.expr;
  coe* c = &g_coes[es.sort][tgt];
  switch (c->tag) {
    case COE_ONE: {
      u32 e = ALLOC(((parse_term){EXPR_TERM, 1, c->termid}),
        sizeof(parse_term) + 1 * sizeof(u32));
      ((parse_term*)&g_store[e])->args[0] = es.expr;
      return e;
    }
    case COE_TRANS:
      return coerce(((expr_sort){coerce(es, c->trans), c->trans}), tgt);
    case COE_PROV: return es.expr;
    default: ENSURE("type mismatch", false);
  }
  UNREACHABLE();
}

expr_sort expr(u16 prec);
#define APP_PREC 1024

expr_sort prefix_expr(u16 prec) {
  token_result t = token();
  if (t.tk == g_open_paren) {
    expr_sort e = expr(0);
    ENSURE("expecting ')'", token().tk == g_close_paren);
    return e;
  }
  u32 tk = t.tk->data;
  if (tk) {
    token_info* info = (token_info*)&g_parser_arena[tk];
    if (info->prefix) {
      ENSURE("expecting prefix expression, precedence mismatch",
        info->prec >= prec);
      prefix_info* pfx = (prefix_info*)&g_parser_arena[info->prefix];
      u16 nargs = pfx->num_args;
      u32 e = ALLOC(((parse_term){EXPR_TERM, nargs, pfx->termid}),
        sizeof(parse_term) + nargs * sizeof(u32));
      u32* args = ((parse_term*)&g_store[e])->args;
      term* t = &g_terms[pfx->termid];
      u64* targs = (u64*)&g_file[t->p_args];
      for (int i = 0; i < pfx->num_lits; i++) {
        literal* lit = &pfx->lits[i];
        if (lit->tag == LIT_CONST) {
          ENSURE("expecting notation token",
            token().tk->data == lit->cnst.token);
        } else {
          args[lit->var.var] =
            coerce(expr(lit->var.prec), TYPE_SORT(targs[lit->var.var]));
        }
      }
      return (expr_sort){e, t->sort & 0x7f};
    }
  }
  u32 var = gt_terms[t.var->next[0]].data;
  if (var) return (expr_sort){g_var_nodes[~var].var, g_var_sorts[~var]};
  ENSURE("expecting prefix expression, unrecognized token", t.var->data);
  u32 termid = ~t.var->data;
  term* tm = &g_terms[termid];
  u16 nargs = tm->num_args;
  u32 e = ALLOC(((parse_term){EXPR_TERM, nargs, termid}),
    sizeof(parse_term) + nargs * sizeof(u32));
  if (nargs > 0) {
    ENSURE("unexpected application at this precedence", prec <= APP_PREC);
    u32* args = ((parse_term*)&g_store[e])->args;
    u64* targs = (u64*)&g_file[tm->p_args];
    for (int i = 0; i < nargs; i++)
      args[i] = coerce(expr(-1), TYPE_SORT(targs[i]));
  }
  return (expr_sort){e, tm->sort & 0x7f};
}

expr_sort lhs_expr(u16 prec, expr_sort lhs) {
  while (CUR() != '$' && CUR() != 0) {
    u8* start = cursor;
    token_result t = token();
    if (!t.tk->data) {cursor = start; break;}
    token_info* info = (token_info*)&g_parser_arena[t.tk->data];
    u16 p1 = info->prec;
    if (!info->infix || p1 < prec) {cursor = start; break;}
    infix_info ifx = *(infix_info*)&g_parser_arena[info->infix];
    u16 p2 = ifx.rassoc ? p1 : p1+1;
    expr_sort rhs = prefix_expr(p2);
    start = cursor;
    while (CUR() != '$' && CUR() != 0) {
      token_result t2 = token();
      cursor = start;
      if (!t2.tk->data) break;
      token_info* info2 = (token_info*)&g_parser_arena[t2.tk->data];
      if (!info2->infix) break;
      if (info2->prec < p2) break;
      rhs = lhs_expr(info2->prec, rhs);
      start = cursor;
    }
    u32 e = ALLOC(((parse_term){EXPR_TERM, 2, ifx.termid}),
      sizeof(parse_term) + 2 * sizeof(u32));
    u32* args = ((parse_term*)&g_store[e])->args;
    term* tm = &g_terms[ifx.termid];
    u64* targs = (u64*)&g_file[tm->p_args];
    args[0] = coerce(lhs, TYPE_SORT(targs[0]));
    args[1] = coerce(rhs, TYPE_SORT(targs[1]));
    lhs = (expr_sort){e, tm->sort & 0x7f};
  }
  return lhs;
}

expr_sort expr(u16 prec) {
  return lhs_expr(prec, prefix_expr(prec));
}

u32 binders(int kind, u16 num_args, u64* args, u64 ret) {
  g_store_size = 0;
  g_num_vars = num_args;
  int arg_idx = 0;
  u32 p_hyps = -1;
  while (!ch(':')) {
    int curly = ch('{');
    ENSURE("expecting an argument binder", curly || ch('('));
    char close = curly ? '}' : ')';
    int var_group_start = arg_idx;
    int dummy_group_start = g_num_vars;

    // lookahead to see if this is a hypothesis binder
    u8* start = cursor;
    while (!ch(':')) {
      ch('.');
      parse_new_ident_(gt_terms, &gt_terms_end, TERM_TRIE_SIZE);
    }
    int is_hyp = CUR() == '$';
    cursor = start;

    while (!ch(':')) {
      int dummy = ch('.');
      int i;
      if (dummy) {
        EENSURE("variable number overflow", 2, (i = g_num_vars++) < NUM_VARS);
        ENSURE("dummies are only allowed in defs", kind == KW_DEF);
      } else {
        i = arg_idx++;
      }
      ident_blank x = parse_new_ident_(gt_terms, &gt_terms_end, TERM_TRIE_SIZE);
      if (!x.blank && !is_hyp) {
        ENSURE("hypotheses must follow variables", p_hyps == (u32)-1);
        u32* p = &x.x->next[0];
        u32* dat = &extend(gt_terms, p, &gt_terms_end, TERM_TRIE_SIZE)->data;
        ENSURE("variable shadowing is not allowed", *dat == 0);
        *dat = ~i;
        g_var_nodes[i].trie = *p;
        g_var_nodes[i].var = ALLOC(((parse_var){EXPR_VAR, i}), sizeof(parse_var));
      }
    }
    if (CUR() == '$') {
      do {cursor++;} while (is_ws(CUR()));
      ENSURE("hypotheses are only allowed in axioms/theorems", kind == KW_THEOREM);
      ENSURE("hypotheses are only allowed in regular binders", !curly);
      u32 e = coerce(expr(0), PROV);
      ENSURE("expecting '$)'", ch('$') && ch(')'));
      for (; arg_idx > var_group_start; arg_idx--)
        p_hyps = ALLOC(((parse_expr_list){e, p_hyps}), sizeof(parse_expr_list));
    } else {
      ENSURE("too many arguments", arg_idx <= num_args);
      trie x = lookup_ident(gt_sorts);
      ENSURE("expecting sort", x->data);
      u8 sort = (u8)~x->data;
      u64 type = ((u64)sort << 56) | ((u64)curly << 63);
      if (!ch(close)) {
        ENSURE("bound variables should not have dependencies", !curly);
        ENSURE("dummies should not have dependencies", dummy_group_start == g_num_vars);
        do {
          u32 var = lookup_var();
          ENSURE("expecting variable", var < var_group_start);
          ENSURE("expecting bound variable", args[var] & TYPE_BOUND_MASK);
          type |= args[var] & TYPE_DEPS_MASK;
        } while (!ch(close));
      }
      for (; var_group_start < arg_idx; var_group_start++) {
        ENSURE("variable type does not match theorem", type ==
          (curly ? args[var_group_start] & ~TYPE_DEPS_MASK : args[var_group_start]));
        g_var_sorts[var_group_start] = sort;
      }
      while (dummy_group_start < g_num_vars)
        g_var_sorts[dummy_group_start++] = sort;
    }
  }

  while (true) {
    if (CUR() == '$') {
      do {cursor++;} while (is_ws(CUR()));
      ENSURE("hypotheses are only allowed in axioms/theorems", kind == KW_THEOREM);
      u32 e = coerce(expr(0), PROV);
      ENSURE("expecting '$'", ch('$'));
      p_hyps = ALLOC(((parse_expr_list){e, p_hyps}), sizeof(parse_expr_list));
      if (!ch('>')) break;
    } else {
      ENSURE("hypotheses must follow variables", p_hyps == (u32)-1);
      trie x = lookup_ident(gt_sorts);
      ENSURE("expecting sort", x->data);
      u8 sort = (u8)~x->data;
      u64 type = ((u64)sort << 56);
      while (ident_start(CUR())) {
        u32 var = lookup_var();
        ENSURE("expecting variable", var < arg_idx);
        ENSURE("expecting bound variable", args[var] & TYPE_BOUND_MASK);
        type |= args[var] & TYPE_DEPS_MASK;
      }
      if (ch('>')) {
        ENSURE("variable type does not match theorem", type == args[arg_idx++]);
      } else {
        ENSURE("return type does not match theorem", type == ret);
        break;
      }
    }
  }
  ENSURE("incorrect number of arguments", arg_idx == num_args);
  for (u16 i = 0; i < num_args; i++)
    g_uheap[i] = g_var_nodes[i].var;
  g_uheap_size = num_args;
  return p_hyps;
}

void pop_vars() {
  for (int i = 0; i < g_num_vars; i++)
    gt_terms[g_var_nodes[i].trie].data = 0;
  g_num_vars = 0;
}

void deep_eq(u32 e1, u32 e2) {
  if (e1 == e2) return;
  u32* top = g_ustack_top;
  push_ustack(e1);
  push_ustack(e2);
  while (g_ustack_top > top) {
    u32 e2 = *(--g_ustack_top);
    u32 e1 = *(--g_ustack_top);
    if (e1 == e2) continue;
    ENSURE("expression mismatch", g_store[e1] == g_store[e2]);
    if (g_store[e1] == EXPR_TERM) {
      parse_term* p1 = (parse_term*)&g_store[e1];
      parse_term* p2 = (parse_term*)&g_store[e2];
      ENSURE("expression mismatch", p1->termid == p2->termid);
      for (int i = 0; i < p1->num_args; i++) {
        push_ustack(p1->args[i]);
        push_ustack(p2->args[i]);
      }
    } else {
      parse_var* p1 = (parse_var*)&g_store[e1];
      parse_var* p2 = (parse_var*)&g_store[e2];
      ENSURE("expression mismatch", p1->var == p2->var);
    }
  }
}

void check_expr(u16 num_vars, u8* cmd, u32 tgt, u32 hyps) {
  g_ustack_top = &g_ustack[1];
  g_ustack[0] = tgt;
  g_ucmd_start = cmd;
  // u8* last_cmd = cmd;
  while (true) {
    g_ucmd = cmd;
    cmd_unpack_result r = cmd_unpack(cmd);
    u32 sz = r.sz;
    u32 data = r.data;
    // debug_print_ustack();
    // debug_print_uheap();
    switch (*cmd & 0x3F) {
      // End: the end of the command stream.
      // The unify stack should be empty at this point
      case CMD_END: {
        ENSURE("unfinished hypothesis stack", hyps == -1);
        g_ucmd_start = 0;
      } return;

      case CMD_UNIFY_REF: {
        deep_eq(g_uheap[data], *(--g_ustack_top));
      } break;

      case CMD_UNIFY_TERM:
      case CMD_UNIFY_TERM_SAVE: {
        u32 p = *(--g_ustack_top);
        parse_term* e = (parse_term*)&g_store[p];
        ENSURE("store type error", e->tag == EXPR_TERM);
        ENSURE("unify failure at term", e->termid == data);
        ENSURE("unify stack overflow",
          &g_ustack_top[e->num_args] <= &g_ustack[UNIFY_STACK_SIZE]);
        for (int i = e->num_args - 1; i >= 0; i--) {
          *g_ustack_top++ = e->args[i];
        }
        UPDATE_HIGHWATER(g_ustack_top, g_ustack_highwater)
        if (*cmd & 0x01) // save
          push_uheap(p);
      } break;

      case CMD_UNIFY_DUMMY: {
        u32 p = *(--g_ustack_top);
        parse_var* e = (parse_var*)&g_store[p];
        ENSURE("store type error", e->tag == EXPR_VAR);
        ENSURE("expected a dummy", e->var >= num_vars);
        ENSURE("unify failure at dummy",
          data == g_var_sorts[e->var]);
        push_uheap(p);
      } break;

      case CMD_UNIFY_HYP: {
        ENSURE("hypothesis number mismatch", hyps != -1);
        parse_expr_list* p = (parse_expr_list*)&g_store[hyps];
        push_ustack(p->hd);
        hyps = p->tl;
      } break;
    }
    // last_cmd = cmd;
    cmd += sz;
  }
}

void set_prec(token_info* tk, u16 pr) {
  if (tk->prec_set) {
    ENSURE("precedence mismatch", tk->prec == pr);
  } else {
    tk->prec_set = true;
    tk->prec = pr;
  }
}

void insert_prec_assoc(u16 prec, u8 rassoc) {
  for (int i = 0; i < g_prec_assoc_size; i++) {
    if (g_prec_assoc[i].prec == prec) {
      ENSURE("precedence level is both left and right assoc",
        g_prec_assoc[i].rassoc == rassoc);
      return;
    }
  }
  ENSURE("prec assoc overflow", g_prec_assoc_size < PREC_ASSOC_SIZE);
  g_prec_assoc[g_prec_assoc_size++] = (prec_assoc){prec, rassoc};
}

void parse_until(u8 stmt_type) {
  int mods = 0;
  g_parsing = true;
  start: { // this is a loop, but the switches mess with break/continue
    int k = kw();
    switch (k) {
      case KW_PURE:     mods |= SORT_PURE;     goto start;
      case KW_STRICT:   mods |= SORT_STRICT;   goto start;
      case KW_PROVABLE: mods |= SORT_PROVABLE; goto start;
      case KW_FREE:     mods |= SORT_FREE;     goto start;
      case KW_SORT: {
        ENSURE("expecting a sort", stmt_type == CMD_STMT_SORT);
        trie x = parse_new_ident(gt_sorts, &gt_sorts_end, SORT_TRIE_SIZE);
        ENSURE("duplicate sort name", x->data == 0);
        ENSURE("sort modifiers do not match", mods == g_sorts[g_num_sorts]);
        x->data = ~(u32)g_num_sorts;
        if (mods & SORT_PROVABLE)
          g_coes[g_num_sorts][PROV].tag = COE_PROV;
        ENSURE("expecting ';'", ch(';'));
        g_parsing = false;
      } return;
    }
    ENSURE("modifiers not expected at this position", mods == 0);
    switch (k) {
      case KW_TERM:
      case KW_DEF: {
        ENSURE("expecting a term/def", stmt_type == CMD_STMT_DEF);
        term* t = &g_terms[g_num_terms];
        if (k == KW_TERM) {
          ENSURE("expecting a term", !(t->sort & 0x80));
        } else {
          ENSURE("expecting a def", t->sort & 0x80);
        }
        trie x = parse_new_ident(gt_terms, &gt_terms_end, TERM_TRIE_SIZE);
        u64* args = (u64*)&g_file[t->p_args];
        binders(k, t->num_args, args, args[t->num_args]);
        if (k == KW_DEF && ch('=')) {
          ENSURE("expecting '$'", ch('$'));
          check_expr(t->num_args, (u8*)&args[t->num_args+1],
            coerce(expr(0), t->sort & 0x7f), -1);
          ENSURE("expecting '$'", ch('$'));
        }
        ENSURE("duplicate term/def name", x->data == 0);
        x->data = ~g_num_terms;
        pop_vars();
        ENSURE("expecting ';'", ch(';'));
        g_parsing = false;
      } return;

      case KW_AXIOM:
      case KW_THEOREM: {
        if (k == KW_AXIOM) {
          ENSURE("expecting an axiom", stmt_type == CMD_STMT_AXIOM);
        } else {
          ENSURE("expecting a theorem", stmt_type == CMD_STMT_THM);
        }
        thm* t = &g_thms[g_num_thms];
        trie x = parse_new_ident(gt_thms, &gt_thms_end, THM_TRIE_SIZE);
        u64* args = (u64*)&g_file[t->p_args];
        parse_expr_list hyps_ret =
          *(parse_expr_list*)&g_store[binders(KW_THEOREM, t->num_args, args, 0)];
        check_expr(t->num_args, (u8*)&args[t->num_args], hyps_ret.hd, hyps_ret.tl);
        ENSURE("duplicate term/def name", x->data == 0);
        x->data = ~g_num_thms;
        pop_vars();
        ENSURE("expecting ';'", ch(';'));
        g_parsing = false;
      } return;

      case KW_DELIMITER: {
        ENSURE("expecting '$'", CUR() == '$');
        do {cursor++;} while (is_ws(CUR()));
        u8* start = cursor;
        while (!ch('$')) {
          g_delims[*cursor++] |= DELIM_LEFT;
          u8 w = CUR();
          ENSURE("multi-character delimiters not supported", is_ws(w) || w == '$');
          while (is_ws(CUR())) cursor++;
        }
        if (CUR() == ';')
          cursor = start; // reread the delimiter sequence
        else {
          ENSURE("expecting '$' or ';'", CUR() == '$');
          do {cursor++;} while (is_ws(CUR()));
        }
        while (!ch('$')) {
          g_delims[*cursor++] |= DELIM_RIGHT;
          u8 w = CUR();
          ENSURE("multi-character delimiters not supported", is_ws(w) || w == '$');
          while (is_ws(CUR())) cursor++;
        }
        ENSURE("expecting ';'", ch(';'));
      } goto start;

      case KW_PREFIX:
      case KW_INFIXL:
      case KW_INFIXR: {
        u32 x = lookup_ident(gt_terms)->data;
        ENSURE("unknown term", x);
        u32 termid = ~x;
        ENSURE("expecting ':'", ch(':'));
        token_info* tk = (token_info*)&g_parser_arena[parse_new_token()];
        ENSURE("expecting 'prec'", kw() == KW_PREC);
        u16 pr = prec();
        set_prec(tk, pr);
        if (k == KW_PREFIX) {
          u16 nargs = g_terms[termid].num_args;
          tk->prefix = PARSER_ALLOC(((prefix_info){termid, nargs, nargs}),
            sizeof(prefix_info) + nargs * sizeof(literal));
          if (nargs > 0) {
            literal* lits = ((prefix_info*)&g_parser_arena[tk->prefix])->lits;
            for (u16 i = 0;; i++) {
              lits[i].tag = LIT_VAR;
              if (i < nargs-1) {
                lits[i].var = (struct lit_var){i, -1};
              } else {
                lits[i].var = (struct lit_var){i, pr};
                break;
              }
            }
            insert_prec_assoc(pr, true);
          }
        } else {
          ENSURE("expected a binary operator", g_terms[termid].num_args == 2);
          ENSURE("precedence out of range", pr < (u16)-2);
          u8 rassoc = k == KW_INFIXR;
          tk->infix = PARSER_ALLOC(((infix_info){termid, rassoc}),
            sizeof(infix_info));
          insert_prec_assoc(pr, rassoc);
        }
        ENSURE("expecting ';'", ch(';'));
      } goto start;

      case KW_NOTATION: {
        u32 x = lookup_ident(gt_terms)->data;
        ENSURE("unknown term", x);
        u32 termid = ~x;
        term* t = &g_terms[termid];
        u16 nargs = t->num_args;
        u64* args = (u64*)&g_file[t->p_args];
        binders(KW_TERM, nargs, args, args[nargs]);
        ENSURE("expecting '='", ch('='));
        ENSURE("expecting '('", ch('('));
        token_info* tk = (token_info*)&g_parser_arena[parse_new_token()];
        ENSURE("expecting ':'", ch(':'));
        u16 pr = prec();
        ENSURE("expecting ')'", ch(')'));
        set_prec(tk, pr);

        // pre-scan to get the length
        u8* start = cursor;
        u16 nlits = 0;
        while (CUR() != ';') {
          if (ch('(')) {
            parse_new_token();
            ENSURE("expecting ':'", ch(':'));
            prec();
            ENSURE("expecting ')'", ch(')'));
          } else {
            lookup_ident(gt_terms);
          }
          ENSURE("literal number overflow", nlits++ != (u16)-1);
        }
        cursor = start;

        prefix_info* info = (prefix_info*)&g_parser_arena[
          tk->prefix = PARSER_ALLOC(((prefix_info){termid, nargs, nlits}),
            sizeof(prefix_info) + nlits * sizeof(literal))];
        u16* last_prec = 0;
        for (int i = 0; i < nlits; i++) {
          literal* lit = &info->lits[i];
          if ((lit->tag = !ch('('))) {
            if (last_prec) *last_prec = -1;
            u32 var = lookup_var();
            ENSURE("expecting variable", var < nargs);
            lit->var.var = var;
            last_prec = &lit->var.prec;
          } else {
            token_info* c = (token_info*)&g_parser_arena[
              lit->cnst.token = parse_new_token()];
            ENSURE("expecting ':'", ch(':'));
            u16 q = prec();
            ENSURE("expecting ')'", ch(')'));
            set_prec(c, q);
            if (last_prec) {
              ENSURE("precedence out of range", q < (u16)-2);
              *last_prec = q+1;
              last_prec = 0;
            }
          }
        }
        if (last_prec) {
          *last_prec = pr;
          insert_prec_assoc(pr, true);
        }
        pop_vars();
        ENSURE("expecting ';'", ch(';'));
      } goto start;

      case KW_COERCION: {
        u32 x = lookup_ident(gt_terms)->data;
        ENSURE("unknown term", x);
        u32 termid = ~x;
        ENSURE("expected a unary operator", g_terms[termid].num_args == 1);
        ENSURE("expecting ':'", ch(':'));
        u8 s1 = ({
          trie x = lookup_ident(gt_sorts);
          ENSURE("expecting sort", x->data);
          (u8)~x->data;
        });
        ENSURE("expecting '>'", ch('>'));
        u8 s2 = ({
          trie x = lookup_ident(gt_sorts);
          ENSURE("expecting sort", x->data);
          (u8)~x->data;
        });
        ENSURE("expecting ';'", ch(';'));
        for (int sl = 0; sl < g_num_sorts; sl++) {
          if (g_coes[sl][s1].tag != COE_EMPTY) {
            ENSURE("coercion cycle detected", sl != s2);
            coe* c = &g_coes[sl][s2];
            ENSURE("coercion diamond detected", c->tag == COE_EMPTY);
            c->tag = COE_TRANS;
            c->trans = s1;
          }
        }
        {
          ENSURE("coercion cycle detected", s1 != s2);
          coe* c = &g_coes[s1][s2];
          ENSURE("coercion diamond detected", c->tag == COE_EMPTY);
          c->tag = COE_ONE;
          c->termid = termid;
        }
        for (int sr = 0; sr < g_num_sorts; sr++) {
          if (g_coes[s2][sr].tag != COE_EMPTY) {
            ENSURE("coercion cycle detected", s1 != sr);
            coe* c = &g_coes[s1][sr];
            ENSURE("coercion diamond detected", c->tag == COE_EMPTY);
            c->tag = COE_TRANS;
            c->trans = s2;
          }
        }
        if (g_coes[s2][PROV].tag != COE_EMPTY) {
          coe* c = &g_coes[s1][PROV];
          ENSURE("coercion diamond to provable detected", c->tag == COE_EMPTY);
          c->tag = COE_TRANS;
          c->trans = s2;
        }
      } goto start;

      default: {
        ENSURE("invalid command keyword", !CUR() && stmt_type == CMD_END);
        g_parsing = false;
      } return;
    }
  }
}

void init_parser() {
  g_delims[' '] = DELIM_SPACE | DELIM_RIGHT;
  g_delims['\n'] = DELIM_SPACE | DELIM_RIGHT;
  g_delims['$'] = DELIM_RIGHT;
  trie p = gt_tokens + 1;
  p = extend(gt_tokens, &p->next['(' & 0xF], &gt_tokens_end, TOKEN_TRIE_SIZE);
  g_open_paren = extend(gt_tokens, &p->next[('(' >> 4) & 0xF], &gt_tokens_end, TOKEN_TRIE_SIZE);
  p = gt_tokens + 1;
  p = extend(gt_tokens, &p->next[')' & 0xF], &gt_tokens_end, TOKEN_TRIE_SIZE);
  g_close_paren = extend(gt_tokens, &p->next[(')' >> 4) & 0xF], &gt_tokens_end, TOKEN_TRIE_SIZE);
  ws();
}

#ifndef BARE

void debug_print_input() {
  u8* start = buffer;
  if (start < cursor - 200) start = cursor - 200;
  int col = 0;
  u8* p = cursor-1;
  while (p >= start && *p-- != '\n') col++;
  while (p >= start && *p != '\n') p--;
  start = p+1;
  fill_to(200);
  u8* end = cursor;
  while (*end && *end != '\n') end++;
  if (write(STDERR_FILENO, start, end-start) < 0) {}
  putc('\n', stderr);
  while (col-- > 0) putc(' ', stderr);
  fputs("^\n\n", stderr);
}

#endif

#endif