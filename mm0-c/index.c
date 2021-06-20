#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include "types.c"

u8* g_file; u8* g_end;
u8 g_num_sorts;  u8*   g_sorts;
u32 g_num_terms; term* g_terms;
u32 g_num_thms;  thm*  g_thms;

#ifndef BARE
bool gi_init = false;
header* gi_header;
name_entry* gi_sort_names;
name_entry* gi_term_names;
name_entry* gi_thm_names;
u64* gi_term_vars;
u64* gi_thm_vars;
u64* gi_thm_hyps;
u64* gi_cur_vars;
u64* gi_cur_hyps;

typedef struct {
  u32 id;
  u32 pad;
  u64 ptr;
} index_record;

bool init_index() {
  if (gi_init) return true;
  gi_header = (header*)g_file;
  if (gi_header->p_index &&
      gi_header->p_index < (g_end - g_file)) {
    u64* p = (u64*)&g_file[gi_header->p_index];
    if ((u8*)(p+1) >= g_end) return false;
    u64 num = *p++;
    index_record* ir = (index_record*)p;
    index_record* end = &ir[num];
    if ((u8*)end > g_end) return false;
    for (; ir < end; ir++) {
      switch (ir->id) {
        case 0x656d614eU: { // "Name"
          gi_sort_names = (name_entry*)&g_file[ir->ptr];
          gi_term_names = &gi_sort_names[gi_header->num_sorts];
          gi_thm_names = &gi_term_names[gi_header->num_terms];
          if ((u8*)&gi_thm_names[gi_header->num_thms] > g_end) return false;
        } break;
        case 0x4e726156U: { // "VarN"
          gi_term_vars = (u64*)&g_file[ir->ptr];
          gi_thm_vars = &gi_term_vars[gi_header->num_terms];
          if ((u8*)&gi_thm_vars[gi_header->num_thms] > g_end) return false;
        } break;
        case 0x4e707948U: { // "HypN"
          gi_thm_hyps = (u64*)&g_file[ir->ptr];
          if ((u8*)&gi_thm_hyps[gi_header->num_thms] > g_end) return false;
        } break;
        default:;
      }
    }
    return gi_init = true;
  }
  return false;
}

char* name_value(name_entry* p) {
  u8* name = &g_file[p->name];
  if (name < g_end) return (char*)name;
  return 0;
}

char* lookup_sort(u8 sort) {
  if (!init_index()) return 0;
  if (gi_sort_names && sort < gi_header->num_sorts) {
    return name_value(&gi_sort_names[sort]);
  }
  return 0;
}

char* lookup_term(u32 term) {
  if (!init_index()) return 0;
  if (gi_term_names && term < gi_header->num_terms) {
    return name_value(&gi_term_names[term]);
  }
  return 0;
}

char* lookup_thm(u32 thm) {
  if (!init_index()) return 0;
  if (gi_thm_names && thm < gi_header->num_thms) {
    return name_value(&gi_thm_names[thm]);
  }
  return 0;
}

u64* check_vars(u64 pos) {
  u64* p = ((u64*)&g_file[pos]) + 1;
  if ((u8*)p < g_end && (u8*)&p[p[-1]] < g_end) return p;
  return 0;
}

u64* lookup_term_vars(u32 term) {
  if (!init_index()) return 0;
  if (gi_term_vars && term < gi_header->num_terms) {
    return check_vars(gi_term_vars[term]);
  }
  return 0;
}

u64* lookup_thm_vars(u32 thm) {
  if (!init_index()) return 0;
  if (gi_thm_vars && thm < gi_header->num_thms) {
    return check_vars(gi_thm_vars[thm]);
  }
  return 0;
}

u64* lookup_thm_hyps(u32 thm) {
  if (!init_index()) return 0;
  if (gi_thm_hyps && thm < gi_header->num_thms) {
    return check_vars(gi_thm_hyps[thm]);
  }
  return 0;
}

char* lookup_stmt(u8* cmd) {
  switch (*cmd & 0x3F) {
    case CMD_STMT_SORT:
      gi_cur_vars = 0;
      gi_cur_hyps = 0;
      return lookup_sort(g_num_sorts);
    case CMD_STMT_DEF:
    case CMD_STMT_LOCAL_DEF:
      gi_cur_vars = lookup_term_vars(g_num_terms);
      gi_cur_hyps = 0;
      return lookup_term(g_num_terms);
    case CMD_STMT_AXIOM:
    case CMD_STMT_THM:
    case CMD_STMT_LOCAL_THM:
      gi_cur_vars = lookup_thm_vars(g_num_thms);
      gi_cur_hyps = lookup_thm_hyps(g_num_thms);
      return lookup_thm(g_num_thms);
    default: return 0;
  }
}

char* lookup_var_name(u32 var) {
  if (!gi_cur_vars || var >= gi_cur_vars[-1]) return 0;
  u64 name = gi_cur_vars[var];
  if (!name) return 0;
  u8* p = &g_file[name];
  if (p < g_end) return (char*)p;
  return 0;
}

char* lookup_hyp_name(u32 hyp) {
  if (!gi_cur_hyps || hyp >= gi_cur_hyps[-1]) return 0;
  u64 name = gi_cur_hyps[hyp];
  if (!name) return 0;
  u8* p = &g_file[name];
  if (p < g_end) return (char*)p;
  return 0;
}

#endif
