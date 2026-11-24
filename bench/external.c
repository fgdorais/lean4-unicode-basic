/*
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

/* Benchmark of the UnicodeCLib lookups against ICU and utf8proc. See `bench/README.md`. */

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

static const char *inputs[] = {"ASCII", "Latin", "CJK", "mixed"};

static void fill(int kind) {
  for (int i = 0; i < N; i++) {
    uint32_t r = next();
    switch (kind) {
    case 0: input[i] = 0x20 + r % 95; break;            /* U+0020-007E */
    case 1: input[i] = 0xA0 + r % (0x250 - 0xA0); break; /* U+00A0-024F */
    case 2: input[i] = 0x4E00 + r % (0xA000 - 0x4E00); break; /* U+4E00-9FFF */
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

static void row(const char *name, double ours, double icu, double u8p) {
  printf("| %-15s | %7.2f |", name, ours);
  if (icu >= 0) printf(" %7.2f |", icu); else printf(" %7s |", "-");
  if (u8p >= 0) printf(" %8.2f |\n", u8p); else printf(" %8s |\n", "-");
}

int main(void) {
  load_icu();
  if (icu_version) printf("ICU %d", icu_version); else printf(icu_charType ? "ICU" : "no ICU");
#ifdef HAVE_UTF8PROC
  printf(", utf8proc %s", utf8proc_version());
#else
  printf(", no utf8proc");
#endif
  printf("; ns per call, %d random code points x %d\n", N, REPEAT);
  for (int k = 0; k < 4; k++) {
    fill(k);
    printf("\n%s\n\n| %-15s | %7s | %7s | %8s |\n|---|---|---|---|\n",
      inputs[k], "lookup", "ours", "ICU", "utf8proc");
    double u8p[5] = {-1, -1, -1, -1, -1};
#ifdef HAVE_UTF8PROC
    u8p[0] = TIME(utf8proc_category(c));
    u8p[1] = TIME(utf8proc_toupper(c));
    u8p[3] = TIME(utf8proc_get_property(c)->bidi_class);
    u8p[4] = TIME(utf8proc_get_property(c)->combining_class);
#endif
    int icu = icu_charType != NULL;
    row("general cat.", TIME(unicode_prop_lookup(c)), icu ? TIME(icu_charType(c)) : -1, u8p[0]);
    row("uppercase", TIME(unicode_case_lookup(c)), icu ? TIME(icu_toupper(c)) : -1, u8p[1]);
    row("script", TIME(unicode_script_lookup(c)), icu ? TIME(icu_script(c)) : -1, u8p[2]);
    row("bidi class", TIME(unicode_bidi_class_lookup(c)), icu ? TIME(icu_charDirection(c)) : -1,
      u8p[3]);
    row("combining class", TIME(unicode_combining_class_lookup(c)),
      icu ? TIME(icu_getCombiningClass(c)) : -1, u8p[4]);
  }
  return 0;
}
