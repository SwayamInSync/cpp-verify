# Repository layout

This repository **is** the CppVerify codebase: an LLVM monorepo fork extended at the root.

| Path | Role |
|------|------|
| `clang/lib/Verify/` | Verification engine |
| `clang/include/clang/Basic/CppVerifyConstructs.def`, `clang/lib/Parse/ParseCppVerify.cpp`, `clang/lib/Headers/cppverify.h` | The contract language: its constructs, their parsing, and their documented declarations |
| `clang/tools/cpp-verify/` | Standalone verifier |
| `clang/test/Verify/` | Frontend and end-to-end lit tests (`suite/` for backends) |
| `clang/unittests/Verify/` | Encoding oracle and parity unit tests (`VerifyTests`) |
| `llvm/` | CMake entry for LLVM + Clang |
| `website/` | Published user docs (Sphinx + Doxygen) |
| `docs/` | Design notes |
| `third_party/z3/` | Z3 git submodule (`z3-4.13.4`) |
| `setup.sh` / `setup.ps1` | One-shot build |

## Clone

```bash
git clone --recurse-submodules https://github.com/SwayamInSync/cpp-verify.git
cd cpp-verify
./setup.sh
```

Without `--recurse-submodules`, run `git submodule update --init third_party/z3` before building (or rely on CMake FetchContent on first configure).

## LLVM base

The branch `llvm-upstream` holds only untouched LLVM releases: its first commit
is the `llvmorg-22.1.3` import that `main` starts from, and each later commit
replaces the tree with the next release (`llvmorg-23.1.3`). `main` merges that
branch, so an upgrade is one merge whose base is the previous release:

```bash
git fetch --depth 1 https://github.com/llvm/llvm-project refs/tags/llvmorg-X.Y.Z:refs/tags/llvmorg-X.Y.Z
git branch -f llvm-upstream "$(git commit-tree 'llvmorg-X.Y.Z^{tree}' -p llvm-upstream -m 'llvmorg-X.Y.Z base')"
git merge llvm-upstream
```

`cpp-verify --version` reports the LLVM release a build is based on.

## Z3

`CppVerifyZ3.cmake` prefers `third_party/z3` when present, else fetches from GitHub.