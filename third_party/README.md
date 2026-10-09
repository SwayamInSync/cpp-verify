# Vendored dependencies for CppVerify

## Z3 (SMT solver)

**You do not need to install Z3 separately.** The Clang build compiles Z3 4.13.4 automatically
(`CPPVERIFY_VENDOR_Z3=ON`, default) unless you opt into a system library: from the `third_party/z3`
submodule, or, without it, from a clone the first build makes.

### Offline / pinned source (optional)

To build without network access during the build, check out the submodule first:

```bash
git clone --recurse-submodules https://github.com/SwayamInSync/cpp-verify.git
cd cpp-verify
git submodule update --init third_party/z3
./setup.sh
```

Z3 is built as a separate CMake project, so its internal `opt` component never clashes with LLVM's `opt` tool.

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
- [Python 3](https://www.python.org/downloads/windows/), which LLVM's configuration requires
- **Git** (for the submodules, or the Z3 clone without them)

With Ninja, run `setup.ps1` from an x64 Developer PowerShell for VS 2022 (or an x64 Native Tools
prompt) so that CMake finds `cl`.

Binaries: `build\bin\cpp-verify.exe` and `build\bin\clang++.exe` (Ninja), or
`build\Release\bin\` when using the Visual Studio generator.

**WSL2** is also supported — use `./setup.sh` inside Ubuntu on WSL for the same flow as Linux.

Known constraints on Windows:

- Full LLVM+Clang builds are slow and need ample disk (~30GB+).
- Enable long paths if CMake hits `MAX_PATH` issues.
- CI builds and smoke-tests Windows on every change, but the full test suite runs on Linux; report Windows-specific issues on GitHub.