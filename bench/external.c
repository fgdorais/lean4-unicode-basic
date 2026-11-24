/*
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

/* Benchmark of the UnicodeCLib lookups against ICU, utf8proc and libunistring.
   See `bench/README.md`. */

#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <time.h>
#include "basic.h"
#ifdef HAVE_UTF8PROC
#include "utf8proc.h"
#endif

#define N 1000000
#define REPEAT 50

static uint32_t input[N];

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + t.tv_nsec * 1e-9;
}

/* xorshift64, so that every run uses the same input */
static uint64_t state = 88172645463325252u;
static uint32_t next(void) {
  state ^= state << 13;
  state ^= state >> 7;
  state ^= state << 17;
  return (uint32_t)state;
}

static const char *inputs[] = {"ASCII", "Latin", "CJK", "mixed", "text"};

/* Code points of `text/samples.txt`, the first article of the UDHR in eleven languages */
static uint32_t text[4096];
static int text_len;

static void load_text(void) {
  FILE *f = fopen("text/samples.txt", "rb");
  if (!f) return;
  int b;
  while ((b = fgetc(f)) != EOF && text_len < 4096) {
    uint32_t c = b;
    int more = b < 0x80 ? 0 : b < 0xE0 ? 1 : b < 0xF0 ? 2 : 3;
    if (more) c &= 0x3F >> more;
    while (more-- > 0) c = c << 6 | (fgetc(f) & 0x3F);
    text[text_len++] = c;
  }
  fclose(f);
}

static void fill(int kind) {
  for (int i = 0; i < N; i++) {
    uint32_t r = next();
    switch (kind) {
    case 0: input[i] = 0x20 + r % 95; break;            /* U+0020-007E */
    case 1: input[i] = 0xA0 + r % (0x250 - 0xA0); break; /* U+00A0-024F */
    case 2: input[i] = 0x4E00 + r % (0xA000 - 0x4E00); break; /* U+4E00-9FFF */
    case 4: input[i] = text[i % text_len]; break;
    default: {                                           /* 70% ASCII, 15% Latin, */
      uint32_t k = r % 100;                              /* 7% Greek and Cyrillic, 8% CJK */
      r = next();
      input[i] = k < 70 ? 0x20 + r % 95 : k < 85 ? 0xA0 + r % 0x1B0
        : k < 92 ? 0x391 + r % 0x200 : 0x4E00 + r % 0x5000;
    }
    }
  }
}

/* ICU, loaded at run time so that no headers are needed; its symbols carry a version suffix */
static int8_t (*icu_charType)(int32_t);
static int32_t (*icu_toupper)(int32_t);
static int32_t (*icu_getScript)(int32_t, int *);
static int32_t (*icu_charDirection)(int32_t);
static uint8_t (*icu_getCombiningClass)(int32_t);
static int icu_version;

static void *icu_symbol(void *lib, const char *name) {
  char full[64];
  snprintf(full, sizeof full, "%s_%d", name, icu_version);
  return dlsym(lib, full);
}

static void load_icu(void) {
  void *lib = NULL;
  for (int v = 90; v >= 50 && !lib; v--) {
    char path[32];
    snprintf(path, sizeof path, "libicuuc.so.%d", v);
    if ((lib = dlopen(path, RTLD_NOW))) icu_version = v;
  }
  if (!lib) lib = dlopen("libicucore.dylib", RTLD_NOW); /* macOS: unsuffixed symbols */
  if (!lib) return;
  if (icu_version) {
    icu_charType = icu_symbol(lib, "u_charType");
    icu_toupper = icu_symbol(lib, "u_toupper");
    icu_getScript = icu_symbol(lib, "uscript_getScript");
    icu_charDirection = icu_symbol(lib, "u_charDirection");
    icu_getCombiningClass = icu_symbol(lib, "u_getCombiningClass");
  } else {
    icu_charType = dlsym(lib, "u_charType");
    icu_toupper = dlsym(lib, "u_toupper");
    icu_getScript = dlsym(lib, "uscript_getScript");
    icu_charDirection = dlsym(lib, "u_charDirection");
    icu_getCombiningClass = dlsym(lib, "u_getCombiningClass");
  }
}

/* libunistring, also loaded at run time */
typedef struct {
  uint32_t bitmask : 31;
  unsigned int generic : 1;
  const void *lookup;
} uc_general_category_t;
static uc_general_category_t (*us_general_category)(uint32_t);
static uint32_t (*us_toupper)(uint32_t);
static const void *(*us_script)(uint32_t);
static int (*us_bidi_class)(uint32_t);
static int (*us_combining_class)(uint32_t);

static void load_unistring(void) {
  void *lib = dlopen("libunistring.so.5", RTLD_NOW);
  if (!lib) lib = dlopen("libunistring.so.2", RTLD_NOW);
  if (!lib) lib = dlopen("libunistring.dylib", RTLD_NOW);
  if (!lib) return;
  us_general_category = dlsym(lib, "uc_general_category");
  us_toupper = dlsym(lib, "uc_toupper");
  us_script = dlsym(lib, "uc_script");
  us_bidi_class = dlsym(lib, "uc_bidi_class");
  if (!us_bidi_class) us_bidi_class = dlsym(lib, "uc_bidi_category"); /* before 0.9.4 */
  us_combining_class = dlsym(lib, "uc_combining_class");
}

static int icu_script(int32_t c) {
  int err = 0;
  return icu_getScript(c, &err);
}

/* Time `expr` over the input, in nanoseconds per call */
#define TIME(expr) ({ \
  volatile uint64_t sink = 0; \
  double t = now(); \
  for (int r = 0; r < REPEAT; r++) \
    for (int i = 0; i < N; i++) { uint32_t c = input[i]; sink += (uint64_t)(expr); } \
  (void)sink; \
  (now() - t) * 1e9 / ((double)N * REPEAT); })

#define COLS 4
static const char *libs[COLS] = {"ours", "ICU", "utf8proc", "unistring"};

static void row(const char *name, const double t[COLS]) {
  printf("| %-15s |", name);
  for (int j = 0; j < COLS; j++)
    if (t[j] >= 0) printf(" %9.2f |", t[j]); else printf(" %9s |", "-");
  printf("\n");
}

int main(void) {
  load_icu();
  load_unistring();
  load_text();
  if (icu_version) printf("ICU %d", icu_version); else printf(icu_charType ? "ICU" : "no ICU");
#ifdef HAVE_UTF8PROC
  printf(", utf8proc %s", utf8proc_version());
#else
  printf(", no utf8proc");
#endif
  printf(us_toupper ? ", libunistring" : ", no libunistring");
  printf("; ns per call, %d code points x %d\n", N, REPEAT);
  for (int k = 0; k < 5; k++) {
    if (k == 4 && !text_len) break;
    fill(k);
    printf("\n%s\n\n| %-15s |", inputs[k], "lookup");
    for (int j = 0; j < COLS; j++) printf(" %9s |", libs[j]);
    printf("\n|---|---|---|---|---|\n");
    double t[5][COLS];
    for (int i = 0; i < 5; i++) for (int j = 0; j < COLS; j++) t[i][j] = -1;
    t[0][0] = TIME(unicode_prop_lookup(c));
    t[1][0] = TIME(unicode_case_lookup(c));
    t[2][0] = TIME(unicode_script_lookup(c));
    t[3][0] = TIME(unicode_bidi_class_lookup(c));
    t[4][0] = TIME(unicode_combining_class_lookup(c));
    if (icu_charType) {
      t[0][1] = TIME(icu_charType(c));
      t[1][1] = TIME(icu_toupper(c));
      t[2][1] = TIME(icu_script(c));
      t[3][1] = TIME(icu_charDirection(c));
      t[4][1] = TIME(icu_getCombiningClass(c));
    }
#ifdef HAVE_UTF8PROC
    t[0][2] = TIME(utf8proc_category(c));
    t[1][2] = TIME(utf8proc_toupper(c));
    t[3][2] = TIME(utf8proc_get_property(c)->bidi_class);
    t[4][2] = TIME(utf8proc_get_property(c)->combining_class);
#endif
    if (us_toupper) {
      t[0][3] = TIME(us_general_category(c).bitmask);
      t[1][3] = TIME(us_toupper(c));
      t[2][3] = TIME((uintptr_t)us_script(c));
      t[3][3] = TIME(us_bidi_class(c));
      t[4][3] = TIME(us_combining_class(c));
    }
    static const char *names[5] =
      {"general cat.", "uppercase", "script", "bidi class", "combining class"};
    for (int i = 0; i < 5; i++) row(names[i], t[i]);
  }
  return 0;
}
