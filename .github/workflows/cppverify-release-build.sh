#!/bin/bash
# Builds the release distribution into dist/cpp-verify in two stages: stage 1
# builds Clang with the host compiler, and stage 2 builds the distribution with
# that Clang, so every platform's release is built by the Clang it ships.
set -euo pipefail

common=(
  -G Ninja
  -DCMAKE_BUILD_TYPE=Release
  -DLLVM_TARGETS_TO_BUILD=Native
  -DCPPVERIFY_VENDOR_Z3=ON
  -DCPPVERIFY_PREFER_SYSTEM_Z3=OFF
  -DLLVM_ENABLE_ZLIB=OFF -DLLVM_ENABLE_ZSTD=OFF
  -DLLVM_ENABLE_LIBXML2=OFF -DLLVM_ENABLE_LIBEDIT=OFF
)
stage2=()
case "$(uname)" in
  Linux) stage2+=(-DLLVM_STATIC_LINK_CXX_STDLIB=ON) ;;
  Darwin) common+=(-DCMAKE_OSX_DEPLOYMENT_TARGET=13.0 -DCLANG_USE_XCSELECT=ON) ;;
esac

cmake -S llvm -B stage1 "${common[@]}" -DLLVM_ENABLE_PROJECTS=clang
ninja -C stage1 clang

cmake -S llvm -B build "${common[@]}" "${stage2[@]}" \
  -DCMAKE_C_COMPILER="$PWD/stage1/bin/clang" \
  -DCMAKE_CXX_COMPILER="$PWD/stage1/bin/clang++" \
  -DLLVM_ENABLE_PROJECTS="clang;clang-tools-extra" \
  -DLLVM_DISTRIBUTION_COMPONENTS="clang;clang-resource-headers;clangd;clang-format;cpp-verify" \
  -DCMAKE_INSTALL_PREFIX="$PWD/dist/cpp-verify"
ninja -C build install-distribution
