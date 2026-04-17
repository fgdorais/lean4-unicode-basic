#include <lean/lean.h>
#include <arpa/inet.h>
#include "basic.h"

static inline int unicode_script_is_valid(uint32_t c) {
  int c0 = (int)(c >> 24 & 0xff);
  int c1 = (int)(c >> 16 & 0xff);
  int c2 = (int)(c >> 8 & 0xff);
  int c3 = (int)(c & 0xff);
  return
    c0 <= 'Z' && 'A' <= c0 &&
    c1 <= 'z' && 'a' <= c1 &&
    c2 <= 'z' && 'a' <= c2 &&
    c3 <= 'z' && 'a' <= c3;
}

uint32_t unicode_script_of_abbrev(b_lean_obj_arg abbr) {
  lean_string_object * str = lean_to_string(abbr);
  assert(str->m_size > 4);
  uint32_t val = *((uint32_t*)(str->m_data));
  return ntohl(val);
}

lean_obj_res unicode_script_to_abbrev(uint32_t scr) {
  assert(unicode_script_is_valid(scr));
  lean_object * abbr = lean_alloc_string(5, 5, 4);
  lean_to_string(abbr)->m_data[4] = 0;
  *((uint32_t*)lean_to_string(abbr)->m_data) = htonl(scr);
  return abbr;
}
