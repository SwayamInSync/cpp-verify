// RUN: %clang_cc1 -std=c++17 -fverify-contracts -E -dM %s | FileCheck %s --check-prefix=ON
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -undef -E -dM %s | FileCheck %s --check-prefix=ON
// RUN: %clang -std=c++17 -fverify-contracts -E -dM %s | FileCheck %s --check-prefix=ON
// RUN: %clang_cc1 -std=c++17 -E -dM %s | FileCheck %s --check-prefix=OFF
// RUN: %clang_cc1 -x c -std=c11 -fverify-contracts -E -dM %s | FileCheck %s --check-prefix=OFF
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -U__cppverify__ -E -dM %s | FileCheck %s --check-prefix=UNDEF
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -E -P %s -o %t.i
// RUN: %cpp-verify --version > %t.version
// RUN: cat %t.i %t.version | FileCheck %s --check-prefix=VERSION
//
// With -fverify-contracts in C++, where the parser recognizes the constructs,
// __cppverify__ is defined, with the release in __cppverify_major__,
// __cppverify_minor__, __cppverify_patchlevel__, and __cppverify_version__,
// the release cpp-verify --version names. They describe the language, as
// __cplusplus does, so -undef keeps them and -U removes them.

RELEASE __cppverify_version__ PARTS __cppverify_major__ . __cppverify_minor__ . __cppverify_patchlevel__ DEFINED __cppverify__

// ON-DAG: #define __cppverify__ 1
// ON-DAG: #define __cppverify_major__ {{[0-9]+$}}
// ON-DAG: #define __cppverify_minor__ {{[0-9]+$}}
// ON-DAG: #define __cppverify_patchlevel__ {{[0-9]+$}}
// ON-DAG: #define __cppverify_version__ "{{[0-9]+\.[0-9]+\.[0-9]+.*}}"

// OFF-NOT: __cppverify

// UNDEF-NOT: #define __cppverify__
// UNDEF: #define __cppverify_major__
// UNDEF-NOT: #define __cppverify__

// VERSION: RELEASE "[[MAJOR:[0-9]+]].[[MINOR:[0-9]+]].[[PATCH:[0-9]+]][[SUFFIX:[^"]*]]" PARTS [[MAJOR]] . [[MINOR]] . [[PATCH]] DEFINED 1
// VERSION: cpp-verify [[MAJOR]].[[MINOR]].[[PATCH]][[SUFFIX]]{{( |$)}}
