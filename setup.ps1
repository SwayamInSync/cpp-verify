# Build Clang + cpp-verify with vendored Z3 on Windows (no separate Z3 install).
# Requires: CMake, Ninja (or use Visual Studio generator), MSVC Build Tools, Git.
param(
    [string]$BuildDir = "",
    [string]$Generator = "Ninja",
    [string]$BuildType = "Release",
    [string]$LLVMTargets = "Native"
)

$ErrorActionPreference = "Stop"
$Root = $PSScriptRoot
if (-not $BuildDir) { $BuildDir = Join-Path $Root "build" }

function Require-Command($name) {
    if (-not (Get-Command $name -ErrorAction SilentlyContinue)) {
        Write-Error "Missing '$name' on PATH. Install CMake/Ninja/VS Build Tools and retry."
    }
}

Require-Command cmake
if ($Generator -eq "Ninja") { Require-Command ninja }
Require-Command git

Write-Host "==> Configuring LLVM + Clang + CppVerify (vendored Z3)"
$cmakeArgs = @(
    "-S", (Join-Path $Root "llvm"),
    "-B", $BuildDir,
    "-G", $Generator,
    "-DLLVM_ENABLE_PROJECTS=clang",
    "-DLLVM_TARGETS_TO_BUILD=$LLVMTargets",
    "-DCPPVERIFY_VENDOR_Z3=ON",
    "-DCPPVERIFY_PREFER_SYSTEM_Z3=OFF"
)
if ($Generator -eq "Ninja") {
    $cmakeArgs += "-DCMAKE_BUILD_TYPE=$BuildType"
}
# Visual Studio generator: multi-config; build with --config Release below.
& cmake @cmakeArgs

Write-Host "==> Building clang and cpp-verify"
if ($Generator -match "Visual Studio") {
    & cmake --build $BuildDir --config $BuildType --target clang cpp-verify -m
    $BinDir = Join-Path $BuildDir "bin\$BuildType"
} else {
    & cmake --build $BuildDir --target clang cpp-verify -m
    $BinDir = Join-Path $BuildDir "bin"
}

Write-Host ""
Write-Host "Done."
Write-Host "  Verifier:  $(Join-Path $BinDir 'cpp-verify.exe')"
Write-Host "  Compiler:  $(Join-Path $BinDir 'clang++.exe')"
Write-Host ""
