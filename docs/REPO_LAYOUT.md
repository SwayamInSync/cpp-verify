# Repository layout

This repository **is** the CppVerify codebase: an LLVM monorepo fork extended at the root.

| Path | Role |
|------|------|
| `clang/lib/Verify/` | Verification engine |
| `clang/tools/cpp-verify/` | Standalone verifier |
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

## Z3

`CppVerifyZ3.cmake` prefers `third_party/z3` when present, else fetches from GitHub.