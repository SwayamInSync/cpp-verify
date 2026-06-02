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

function(cppverify_z3_apply_build_options)
  set(Z3_BUILD_LIBZ3_SHARED OFF CACHE BOOL "" FORCE)
  set(Z3_BUILD_EXECUTABLE OFF CACHE BOOL "" FORCE)
  set(Z3_BUILD_TEST_EXECUTABLES OFF CACHE BOOL "" FORCE)
endfunction()

function(cppverify_z3_register_alias)
  if(TARGET libz3)
    if(NOT TARGET cppverify_z3)
      add_library(cppverify_z3 ALIAS libz3)
    endif()
  elseif(TARGET z3)
    if(NOT TARGET cppverify_z3)
      add_library(cppverify_z3 ALIAS z3)
    endif()
  else()
    message(FATAL_ERROR "Z3 build did not produce libz3 or z3 CMake target")
  endif()
endfunction()

function(cppverify_z3_from_subdirectory z3_src binary_dir)
  cppverify_z3_apply_build_options()
  message(STATUS "CppVerify: building vendored Z3 from ${z3_src}")
  add_subdirectory("${z3_src}" "${binary_dir}" EXCLUDE_FROM_ALL)
  cppverify_z3_register_alias()
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
  cppverify_z3_from_subdirectory("${_src}" "${CMAKE_BINARY_DIR}/cppverify-z3-build")
  set(${out_var} cppverify_z3 PARENT_SCOPE)
endfunction()

function(cppverify_z3_try_fetch out_var)
  include(FetchContent)
  cppverify_z3_apply_build_options()
  message(STATUS "CppVerify: fetching Z3 ${CPPVERIFY_Z3_GIT_TAG} (first build needs network)")
  FetchContent_Declare(
    cppverify_z3_src
    GIT_REPOSITORY https://github.com/Z3Prover/z3.git
    GIT_TAG        ${CPPVERIFY_Z3_GIT_TAG}
    GIT_SHALLOW    TRUE
  )
  FetchContent_MakeAvailable(cppverify_z3_src)
  cppverify_z3_register_alias()
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