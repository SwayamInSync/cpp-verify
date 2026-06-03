# CppVerify Z3 backend — vendored by default (no system Z3 required).
#
# Resolution order (when CPPVERIFY_VENDOR_Z3=ON, default):
#   1. Already-defined target cppverify_z3
#   2. third_party/z3 at repo root (offline / submodule)
#   3. FetchContent from GitHub (first configure needs network)
#
# When CPPVERIFY_PREFER_SYSTEM_Z3=ON, try Z3::libz3 / find_package / find_library first.
#
# Cache variables:
#   CPPVERIFY_VENDOR_Z3 (default ON)
#   CPPVERIFY_PREFER_SYSTEM_Z3 (default OFF)
#   CPPVERIFY_Z3_GIT_TAG (default z3-4.13.4)
#   CPPVERIFY_Z3_SOURCE_DIR (override local Z3 tree)

include_guard(GLOBAL)

option(CPPVERIFY_VENDOR_Z3
  "Build and link Z3 for cpp-verify (FetchContent or third_party/z3)" ON)
option(CPPVERIFY_PREFER_SYSTEM_Z3
  "Prefer a system-installed Z3 instead of the vendored build" OFF)
set(CPPVERIFY_Z3_GIT_TAG "z3-4.13.4" CACHE STRING "Z3 git tag when fetching")
set(CPPVERIFY_Z3_SOURCE_DIR "" CACHE PATH "Path to a Z3 source tree (overrides third_party/z3)")

# Repo root = this repository (LLVM monorepo + CppVerify product files)
get_filename_component(CPPVERIFY_REPO_ROOT
  "${CMAKE_CURRENT_LIST_DIR}/../../.." ABSOLUTE)

# Build vendored Z3 as an isolated ExternalProject rather than add_subdirectory.
#
# Why ExternalProject and not add_subdirectory: Z3's CMake declares a library
# component target literally named `opt` (z3_add_component(opt ...)). LLVM's
# monorepo also declares an `opt` executable (llvm/tools/opt). Pulling Z3 into
# the same CMake project via add_subdirectory/FetchContent makes both `opt`
# targets live in one namespace and configure fails with CMP0002 (duplicate
# target). ExternalProject runs Z3's CMake in a separate build, so its targets
# never collide with LLVM's. We then consume the installed static lib through an
# IMPORTED target.
#
# Sources for the build (either an on-disk tree or a git clone) are handled by
# the SOURCE_DIR / GIT_REPOSITORY arguments threaded in by the callers.
function(cppverify_z3_build_external)
  cmake_parse_arguments(Z3EP "" "SOURCE_DIR;GIT_REPOSITORY;GIT_TAG" "" ${ARGN})
  include(ExternalProject)

  set(_prefix  "${CMAKE_BINARY_DIR}/cppverify-z3")
  set(_install "${_prefix}/install")
  set(_incdir  "${_install}/include")
  set(_libpath "${_install}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}z3${CMAKE_STATIC_LIBRARY_SUFFIX}")

  if(Z3EP_SOURCE_DIR)
    set(_src_args SOURCE_DIR "${Z3EP_SOURCE_DIR}")
    message(STATUS "CppVerify: building vendored Z3 (ExternalProject) from ${Z3EP_SOURCE_DIR}")
  else()
    set(_src_args
      GIT_REPOSITORY "${Z3EP_GIT_REPOSITORY}"
      GIT_TAG        "${Z3EP_GIT_TAG}"
      GIT_SHALLOW    TRUE)
    message(STATUS "CppVerify: building vendored Z3 (ExternalProject) ${Z3EP_GIT_TAG} "
      "(first build needs network)")
  endif()

  ExternalProject_Add(cppverify_z3_ep
    ${_src_args}
    PREFIX "${_prefix}"
    CMAKE_CACHE_ARGS
      -DCMAKE_BUILD_TYPE:STRING=Release
      -DCMAKE_INSTALL_PREFIX:PATH=${_install}
      -DCMAKE_POSITION_INDEPENDENT_CODE:BOOL=ON
      -DZ3_BUILD_LIBZ3_SHARED:BOOL=OFF
      -DZ3_BUILD_EXECUTABLE:BOOL=OFF
      -DZ3_BUILD_TEST_EXECUTABLES:BOOL=OFF
      -DZ3_BUILD_DOCUMENTATION:BOOL=OFF
      -DZ3_ENABLE_EXAMPLE_TARGETS:BOOL=OFF
    BUILD_BYPRODUCTS "${_libpath}"
    USES_TERMINAL_DOWNLOAD TRUE
    USES_TERMINAL_BUILD TRUE)

  # INTERFACE_INCLUDE_DIRECTORIES must exist at configure time.
  file(MAKE_DIRECTORY "${_incdir}")

  find_package(Threads REQUIRED)
  add_library(cppverify_z3 STATIC IMPORTED GLOBAL)
  set_target_properties(cppverify_z3 PROPERTIES
    IMPORTED_LOCATION "${_libpath}"
    INTERFACE_INCLUDE_DIRECTORIES "${_incdir}"
    INTERFACE_LINK_LIBRARIES "Threads::Threads;${CMAKE_DL_LIBS}")

  # Ensure the ExternalProject is built before anything links the imported lib.
  # BUILD_BYPRODUCTS handles Ninja ordering; this property lets consuming targets
  # add an explicit dependency for the Makefiles generator too.
  set_property(GLOBAL PROPERTY CPPVERIFY_Z3_EP_TARGET cppverify_z3_ep)
endfunction()

function(cppverify_z3_try_system out_var)
  set(_target "")
  if(TARGET Z3::libz3)
    set(_target Z3::libz3)
  else()
    find_package(Z3 4.8.9 QUIET)
    if(TARGET Z3::libz3)
      set(_target Z3::libz3)
    elseif(Z3_FOUND AND Z3_LIBRARIES)
      if(NOT TARGET cppverify_z3)
        add_library(cppverify_z3 UNKNOWN IMPORTED GLOBAL)
        set_target_properties(cppverify_z3 PROPERTIES
          IMPORTED_LOCATION "${Z3_LIBRARIES}"
          INTERFACE_INCLUDE_DIRECTORIES "${Z3_INCLUDE_DIR}")
      endif()
      set(_target cppverify_z3)
    else()
      find_path(Z3_C_INCLUDE_DIR NAMES z3.h)
      find_path(Z3_CXX_INCLUDE_DIR NAMES z3++.h)
      find_library(Z3_LIBRARY NAMES z3)
      if(Z3_C_INCLUDE_DIR AND Z3_CXX_INCLUDE_DIR AND Z3_LIBRARY)
        if(NOT TARGET cppverify_z3)
          add_library(cppverify_z3 UNKNOWN IMPORTED GLOBAL)
          set_target_properties(cppverify_z3 PROPERTIES
            IMPORTED_LOCATION "${Z3_LIBRARY}"
            INTERFACE_INCLUDE_DIRECTORIES "${Z3_C_INCLUDE_DIR};${Z3_CXX_INCLUDE_DIR}")
        endif()
        set(_target cppverify_z3)
      endif()
    endif()
  endif()
  if(_target)
    message(STATUS "CppVerify: using system Z3 (${_target})")
  endif()
  set(${out_var} "${_target}" PARENT_SCOPE)
endfunction()

function(cppverify_z3_try_local out_var)
  set(_src "")
  if(CPPVERIFY_Z3_SOURCE_DIR AND EXISTS "${CPPVERIFY_Z3_SOURCE_DIR}/CMakeLists.txt")
    set(_src "${CPPVERIFY_Z3_SOURCE_DIR}")
  elseif(EXISTS "${CPPVERIFY_REPO_ROOT}/third_party/z3/CMakeLists.txt")
    set(_src "${CPPVERIFY_REPO_ROOT}/third_party/z3")
  endif()
  if(NOT _src)
    set(${out_var} "" PARENT_SCOPE)
    return()
  endif()
  cppverify_z3_build_external(SOURCE_DIR "${_src}")
  set(${out_var} cppverify_z3 PARENT_SCOPE)
endfunction()

function(cppverify_z3_try_fetch out_var)
  cppverify_z3_build_external(
    GIT_REPOSITORY https://github.com/Z3Prover/z3.git
    GIT_TAG        ${CPPVERIFY_Z3_GIT_TAG})
  set(${out_var} cppverify_z3 PARENT_SCOPE)
endfunction()

function(cppverify_ensure_z3)
  if(TARGET cppverify_z3)
    set(CPPVERIFY_Z3_TARGET cppverify_z3 PARENT_SCOPE)
    return()
  endif()

  set(_target "")

  if(CPPVERIFY_PREFER_SYSTEM_Z3)
    cppverify_z3_try_system(_target)
  endif()

  # Prefer third_party/z3 when present (offline). FetchContent is fallback.
  if(NOT _target AND CPPVERIFY_VENDOR_Z3)
    cppverify_z3_try_local(_target)
  endif()

  if(NOT _target AND CPPVERIFY_VENDOR_Z3)
    cppverify_z3_try_fetch(_target)
  endif()

  if(NOT _target AND NOT CPPVERIFY_PREFER_SYSTEM_Z3)
    cppverify_z3_try_system(_target)
  endif()

  if(NOT _target AND NOT CPPVERIFY_VENDOR_Z3)
    message(WARNING
      "CppVerify: Z3 not found. Enable -DCPPVERIFY_VENDOR_Z3=ON (default) "
      "or install Z3 and use -DCPPVERIFY_PREFER_SYSTEM_Z3=ON")
  endif()

  set(CPPVERIFY_Z3_TARGET "${_target}" PARENT_SCOPE)
endfunction()