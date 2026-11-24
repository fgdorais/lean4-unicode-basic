#!/bin/sh
# Build and run bench/external.c. See bench/README.md.
set -e
cd "$(dirname "$0")"
CC=${CC:-cc}
LEAN_INCLUDE="$(lean --print-prefix)/include"
SRC="../UnicodeCLib/prop.c ../UnicodeCLib/case.c ../UnicodeCLib/script.c \
  ../UnicodeCLib/bidi_class.c ../UnicodeCLib/combining_class.c"
U8P=""
if [ -n "$UTF8PROC" ]; then
  U8P="-DHAVE_UTF8PROC -DUTF8PROC_STATIC -I$UTF8PROC $UTF8PROC/utf8proc.c"
fi
mkdir -p .build
$CC -O2 -std=gnu11 -I"$LEAN_INCLUDE" -I../UnicodeCLib $U8P -o .build/external external.c $SRC -ldl
.build/external
