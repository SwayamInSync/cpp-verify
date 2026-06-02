# Vendored dependencies for CppVerify

## Z3 (SMT solver)

**You do not need to install Z3 separately.** The Clang build fetches and compiles Z3 automatically
(`CPPVERIFY_VENDOR_Z3=ON`, default) unless you opt into a system library.

### Offline / pinned source (optional)

To avoid `FetchContent` downloading at configure time:

```bash
git clone --recurse-submodules https://github.com/SwayamInSync/cpp-verify.git
cd cpp-verify
git submodule update --init third_party/z3
./setup.sh
```

This fork renames Z3’s internal `opt` CMake component to `z3opt` so it does not clash with LLVM’s `opt` tool target.

### Use system Z3 instead (optional)

```bash
cmake ... -DCPPVERIFY_PREFER_SYSTEM_Z3=ON
```

Requires `libz3` and headers on your system (`apt install libz3-dev`, `brew install z3`, etc.).

## Windows

CppVerify builds on Windows with **MSVC** (Visual Studio 2022 Build Tools or full VS) and CMake.

```powershell
# From repo root (PowerShell)
.\setup.ps1
# Or use WSL/Linux flow: ./setup.sh
```

Prerequisites:

- [CMake](https://cmake.org/download/)
- [Ninja](https://github.com/ninja-build/ninja/releases) (recommended) or pass `-Generator "Visual Studio 17 2022"`
- **Visual Studio Build Tools** with “Desktop development with C++”
- **Git** (for FetchContent Z3 clone)

Binaries: `build\bin\cpp-verify.exe` and `build\bin\clang++.exe` (Ninja), or
`build\bin\Release\` when using the Visual Studio generator.

**WSL2** is also supported — use `./setup.sh` inside Ubuntu on WSL for the same flow as Linux.

Known constraints on Windows:

- Full LLVM+Clang builds are slow and need ample disk (~30GB+).
- Enable long paths if CMake hits `MAX_PATH` issues.
- MVP verifier features are developed primarily on macOS/Linux; report Windows-specific issues on GitHub.