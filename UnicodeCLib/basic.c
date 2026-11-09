#include <lean/lean.h>
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
  assert(lean_string_size(abbr) > 4);
  const unsigned char * s = (const unsigned char *)lean_string_cstr(abbr);
  return (uint32_t)s[0] << 24 | (uint32_t)s[1] << 16 | (uint32_t)s[2] << 8 | (uint32_t)s[3];
}

lean_obj_res unicode_script_to_abbrev(uint32_t scr) {
  assert(unicode_script_is_valid(scr));
  lean_object * abbr = lean_alloc_string(5, 5, 4);
  char * s = lean_to_string(abbr)->m_data;
  s[0] = (char)(scr >> 24 & 0xff);
  s[1] = (char)(scr >> 16 & 0xff);
  s[2] = (char)(scr >> 8 & 0xff);
  s[3] = (char)(scr & 0xff);
  s[4] = 0;
  return abbr;
}
