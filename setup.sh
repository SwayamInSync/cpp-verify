#!/usr/bin/env bash
# One-shot build: Clang, cpp-verify with vendored Z3, and the editor tools.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
BUILD_DIR="${BUILD_DIR:-$ROOT/build}"

if [ -e "$ROOT/.git" ] && command -v git >/dev/null 2>&1; then
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

PLATFORM_ARGS=()
# On macOS, clang finds the SDK as Xcode's tools do, without SDKROOT.
if [ "$(uname -s)" = Darwin ]; then
  PLATFORM_ARGS+=(-DCLANG_USE_XCSELECT=ON)
fi

echo "==> Configuring LLVM + Clang + clang-tools-extra + CppVerify (vendored Z3)"
cmake -S "$ROOT/llvm" -B "$BUILD_DIR" -G "$GENERATOR" \
  -DCMAKE_BUILD_TYPE="$BUILD_TYPE" \
  -DLLVM_ENABLE_PROJECTS="clang;clang-tools-extra" \
  -DLLVM_TARGETS_TO_BUILD="$LLVM_TARGETS" \
  -DCPPVERIFY_VENDOR_Z3=ON \
  -DCPPVERIFY_PREFER_SYSTEM_Z3=OFF \
  ${PLATFORM_ARGS[@]+"${PLATFORM_ARGS[@]}"}

echo "==> Building clang, cpp-verify, clangd, and clang-format"
JOBS_ARGS=()
if [ -n "${JOBS:-}" ]; then JOBS_ARGS=(-j"$JOBS"); fi
ninja -C "$BUILD_DIR" ${JOBS_ARGS[@]+"${JOBS_ARGS[@]}"} clang cpp-verify clangd clang-format

echo ""
echo "Done."
echo "  Verifier:  $BUILD_DIR/bin/cpp-verify"
echo "  Compiler:  $BUILD_DIR/bin/clang++"
echo "  Editors:   $BUILD_DIR/bin/clangd, $BUILD_DIR/bin/clang-format"
echo ""
