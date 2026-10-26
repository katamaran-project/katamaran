#!/usr/bin/env bash
# Compile the BearSSL i31 RSA-private call tree to RV32IM, in two variants:
#   unmodified  -- the sources as cloned
#   hardened    -- plus hardening.patch (opaque() barriers, PLAN-rsa.md §0)
# Per-file, -O2, no LTO: every helper stays a real function (PLAN-rsa.md D1).
#
# Usage: build.sh <BearSSL checkout> <out dir>
#   git clone https://www.bearssl.org/git/BearSSL   (PLAN-rsa.md pins 7bea48e)
# Writes <out>/<variant>/<file>.s and .o.  The committed listings/ are this
# script's .s output; regenerate them rather than editing them.
set -euo pipefail

BEARSSL=$(cd "$1" && pwd)
OUT=$(mkdir -p "$2" && cd "$2" && pwd)
HERE=$(cd "$(dirname "$0")" && pwd)
PIN=7bea48e

head=$(git -C "$BEARSSL" rev-parse --short=7 HEAD)
[ "$head" = "$PIN" ] || echo "warning: BearSSL HEAD is $head, PLAN-rsa.md pins $PIN" >&2

FILES="rsa/rsa_i31_priv.c int/i31_modpow2.c int/i31_montmul.c int/i31_tmont.c
int/i31_fmont.c int/i31_ninv31.c int/i31_mulacc.c int/i31_decred.c
int/i31_reduce.c int/i31_decode.c int/i31_encode.c int/i31_add.c int/i31_sub.c
int/i31_rshift.c int/i31_bitlen.c int/i31_muladd.c int/i32_div32.c codec/ccopy.c"

CFLAGS="--target=riscv32 -march=rv32im -mabi=ilp32 -O2 -ffreestanding -nostdinc
-isystem $(clang -print-resource-dir)/include -isystem $HERE/stubinc"

for variant in unmodified hardened; do
  tree=$(mktemp -d)
  cp -r "$BEARSSL/inc" "$BEARSSL/src" "$tree/"
  if [ $variant = hardened ]; then
    patch -s -d "$tree" -p1 < "$HERE/hardening.patch"
  fi
  mkdir -p "$OUT/$variant"
  for f in $FILES; do
    b=$(basename "$f" .c)
    clang $CFLAGS -I"$tree/inc" -I"$tree/src" -S "$tree/src/$f" -o "$OUT/$variant/$b.s"
    clang $CFLAGS -I"$tree/inc" -I"$tree/src" -c "$tree/src/$f" -o "$OUT/$variant/$b.o"
  done
  rm -rf "$tree"
done
echo "built $(ls "$OUT"/*/*.s | wc -l) listings in $OUT"
