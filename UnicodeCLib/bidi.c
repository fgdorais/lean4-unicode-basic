#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>

#include "bidiref/brutils.c"
#include "bidiref/brtable.c"
#include "bidiref/brrule.c"
#include "bidiref/brtest.c"

static int unicode_bidi_initialized = 0;

static int unicode_bidi_init(void) {
  if (!unicode_bidi_initialized) {
    int rc = br_InitWithPath(UBACUR, "data/ucd/core/");
    if (rc != BR_TESTOK) {
      return rc;
    }
    unicode_bidi_initialized = 1;
  }
  return BR_TESTOK;
}

static uint32_t unicode_bidi_class_code(lean_obj_arg v) {
  return lean_unbox_uint32(v);
}

LEAN_EXPORT lean_obj_res unicode_bidi_query_case(
    lean_obj_arg text,
    uint32_t paragraphDirection,
    uint32_t fileFormat) {
  int rc = unicode_bidi_init();
  if (rc != BR_TESTOK) {
    return lean_mk_string("ERR:init");
  }

  SetFileFormat((int)fileFormat);

  size_t len = lean_array_size(text);
  U_Int_32 *buf = (U_Int_32 *)malloc(len * sizeof(U_Int_32));
  if (buf == NULL) {
    return lean_mk_string("ERR:alloc");
  }

  for (size_t i = 0; i < len; i++) {
    lean_object *v = lean_array_uget_borrowed(text, i);
    buf[i] = unicode_bidi_class_code(v);
  }

  int embeddingLevel = -1;
  char levels[4096];
  char order[4096];
  int qrc = br_QueryOneTestCase(buf, (int)len, (int)paragraphDirection,
    &embeddingLevel, levels, (int)sizeof(levels), order, (int)sizeof(order));
  free(buf);

  if (qrc != BR_TESTOK && qrc != BR_OUTPUTERR && qrc != BR_TESTERR) {
    return lean_mk_string("ERR:query");
  }

  char out[8192];
  snprintf(out, sizeof(out), "%d;%s;%s", embeddingLevel, levels, order);
  return lean_mk_string(out);
}
