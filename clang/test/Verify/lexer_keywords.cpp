// RUN: %clang_cc1 -std=c++17 -fverify-contracts -dump-tokens %s 2>&1 | FileCheck %s
//
// The lexer sees a construct as the tokens of a qualified name; the parser
// forms it where the construct may appear.

// CHECK:      identifier 'cppverify' {{.*}}lexer_keywords.cpp
// CHECK-NEXT: coloncolon '::'
// CHECK-NEXT: identifier 'pre'
// CHECK-NEXT: identifier 'cv'
// CHECK-NEXT: coloncolon '::'
// CHECK-NEXT: identifier 'check'
// CHECK-NEXT: identifier 'old'
// CHECK-NEXT: identifier 'result'

cppverify::pre cv::check old result
