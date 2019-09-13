#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include "types.c"

u8* g_file; u8* g_end;
u8 g_num_sorts; u8*   g_sorts;
u32 g_num_terms; term* g_terms;
u32 g_num_thms;  thm*  g_thms;

#ifndef BARE
bool gi_init = false;
header* gi_header;
u64* gi_sorts;
u64* gi_terms;
u64* gi_thms;

bool init_index() {
  if (gi_init) return true;
  gi_header = (header*)g_file;
  if (gi_header->p_index) {
    index_header* ih = (index_header*)&g_file[gi_header->p_index];
    gi_sorts = ih->p_sorts;
    gi_terms = &gi_sorts[gi_header->num_sorts];
    gi_thms = &gi_terms[gi_header->num_terms];
    return gi_init = (u8*)&gi_thms[gi_header->num_thms] <= g_end;
  }
  return false;
}

index* lookup_sort(u8 sort) {
  if (!init_index()) return 0;
  if (sort < gi_header->num_sorts) {
    u8* p = &g_file[gi_sorts[sort]];
    if (p < g_end) return (index*)p;
  }
  return 0;
}

index* lookup_term(u32 term) {
  if (!init_index()) return 0;
  if (term < gi_header->num_terms) {
    u8* p = &g_file[gi_terms[term]];
    if (p < g_end) return (index*)p;
  }
  return 0;
}

index* lookup_thm(u32 thm) {
  if (!init_index()) return 0;
  if (thm < gi_header->num_thms) {
    u8* p = &g_file[gi_thms[thm]];
    if (p < g_end) return (index*)p;
  }
  return 0;
}

index* lookup_stmt(u8* cmd) {
  switch (*cmd & 0x3F) {
    case CMD_STMT_SORT:
      return lookup_sort(g_num_sorts);
    case CMD_STMT_DEF:
    case CMD_STMT_LOCAL_DEF:
      return lookup_term(g_num_terms);
    case CMD_STMT_AXIOM:
    case CMD_STMT_THM:
    case CMD_STMT_LOCAL_THM:
      return lookup_thm(g_num_thms);
    default: return 0;
  }
}
#endif
