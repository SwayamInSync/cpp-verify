#!/usr/bin/env bash
# One-shot build: Clang + cpp-verify with vendored Z3.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
BUILD_DIR="${BUILD_DIR:-$ROOT/build}"

if [ -f "$ROOT/.gitmodules" ] && command -v git >/dev/null 2>&1; then
  echo "==> Initializing submodules (Z3)"
  git -C "$ROOT" submodule update --init third_party/z3
fi
GENERATOR="${GENERATOR:-Ninja}"
LLVM_TARGETS="${LLVM_TARGETS:-Native}"
BUILD_TYPE="${BUILD_TYPE:-Release}"

need() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "error: missing '$1' on PATH" >&2
    exit 1
  fi
}

need cmake
need ninja
need "${CXX:-c++}"

echo "==> Configuring LLVM + Clang + CppVerify (vendored Z3)"
cmake -S "$ROOT/llvm" -B "$BUILD_DIR" -G "$GENERATOR" \
  -DCMAKE_BUILD_TYPE="$BUILD_TYPE" \
  -DLLVM_ENABLE_PROJECTS=clang \
  -DLLVM_TARGETS_TO_BUILD="$LLVM_TARGETS" \
  -DCPPVERIFY_VENDOR_Z3=ON \
  -DCPPVERIFY_PREFER_SYSTEM_Z3=OFF

echo "==> Building clang and cpp-verify"
JOBS="${JOBS:-$( (nproc 2>/dev/null) || echo 8 )}"
ninja -C "$BUILD_DIR" -j"$JOBS" clang cpp-verify

echo ""
echo "Done."
echo "  Verifier:  $BUILD_DIR/bin/cpp-verify"
echo "  Compiler:  $BUILD_DIR/bin/clang++"
echo ""
