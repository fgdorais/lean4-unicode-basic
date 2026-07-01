#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "bidiref/brutils.c"
#include "bidiref/brtable.c"
#include "bidiref/brrule.c"
#include "bidiref/brtest.c"

static int unicode_bidi_initialized = 0;

static lean_object *unicode_bidi_mk_except_error(lean_object *err) {
  lean_object *r = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(r, 0, err);
  return r;
}

static lean_object *unicode_bidi_mk_except_ok(lean_object *value) {
  lean_object *r = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(r, 0, value);
  return r;
}

static lean_object *unicode_bidi_mk_init_failed(int64_t code) {
  lean_object *r = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(r, 0, lean_int64_to_int(code));
  return r;
}

static lean_object *unicode_bidi_mk_allocation_failed(void) {
  return lean_alloc_ctor(1, 0, 0);
}

static lean_object *unicode_bidi_mk_query_failed(int64_t code) {
  lean_object *r = lean_alloc_ctor(2, 1, 0);
  lean_ctor_set(r, 0, lean_int64_to_int(code));
  return r;
}

static lean_object *unicode_bidi_mk_invalid_output(const char *output) {
  lean_object *r = lean_alloc_ctor(3, 1, 0);
  lean_ctor_set(r, 0, lean_mk_string(output));
  return r;
}

static int unicode_bidi_init_impl(const char *path) {
  if (!unicode_bidi_initialized) {
    int rc = br_InitWithPath(UBACUR, (char *)path);
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

LEAN_EXPORT lean_obj_res unicode_bidi_init(lean_obj_arg data_dir) {
  const char *path = lean_string_cstr(data_dir);
  int rc = unicode_bidi_init_impl(path);
  if (rc != BR_TESTOK) {
    return unicode_bidi_mk_except_error(unicode_bidi_mk_init_failed(rc));
  }

  lean_object *ctx = lean_alloc_ctor(0, 1, 0);
  if (ctx == NULL) {
    return unicode_bidi_mk_except_error(unicode_bidi_mk_allocation_failed());
  }
  lean_ctor_set(ctx, 0, lean_mk_string(path));
  return unicode_bidi_mk_except_ok(ctx);
}

LEAN_EXPORT lean_obj_res unicode_bidi_query_case(
    lean_obj_arg ctx_obj,
    lean_obj_arg text,
    uint32_t paragraphDirection,
    uint32_t fileFormat) {
  if (!unicode_bidi_initialized) {
    const char *path = lean_string_cstr(lean_ctor_get(ctx_obj, 0));
    int rc = unicode_bidi_init_impl(path);
    if (rc != BR_TESTOK) {
      return unicode_bidi_mk_except_error(unicode_bidi_mk_init_failed(rc));
    }
  }

  SetFileFormat((int)fileFormat);

  size_t len = lean_array_size(text);
  U_Int_32 *buf = (U_Int_32 *)malloc(len * sizeof(U_Int_32));
  if (buf == NULL) {
    return unicode_bidi_mk_except_error(unicode_bidi_mk_allocation_failed());
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
    return unicode_bidi_mk_except_error(unicode_bidi_mk_query_failed(qrc));
  }

  char out[8192];
  snprintf(out, sizeof(out), "%d;%s;%s", embeddingLevel, levels, order);
  return unicode_bidi_mk_except_ok(lean_mk_string(out));
}
