// RUN: rm -rf %t && mkdir -p %t
// RUN: %clang -### -std=c++17 -fverify-contracts -fverify-backend=cvc5 -fverify-timeout=5000 -fverify-jobs=2 -fverify-cache=%t/cache -fverify-report -c %s -o %t/x.o 2>&1 | FileCheck %s --check-prefix=DRIVER
// RUN: %clang -### -std=c++17 -fverify-contracts -fverify-report=%t/named.json -c %s -o %t/x.o 2>&1 | FileCheck %s --check-prefix=NAMED
// RUN: not %clang_cc1 -std=c++17 -fverify-contracts -fverify-backend=lean -emit-obj -o %t/x.o %s 2>&1 | FileCheck %s --check-prefix=BACKEND
// RUN: not %clang_cc1 -std=c++17 -fverify-contracts -fverify-timeout=soon -emit-obj -o %t/x.o %s 2>&1 | FileCheck %s --check-prefix=TIMEOUT
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -emit-obj -o %t/plain.o %S/Inputs/no_contracts.cpp 2>&1 | count 0
// RUN: not %clang_cc1 -std=c++17 -fverify-contracts -Rcppverify -fverify-backend=bmc -fverify-report=%t/report.json -emit-obj -o %t/x.o %s 2>&1 | FileCheck %s
// RUN: FileCheck %s --check-prefix=REPORT < %t/report.json
// RUN: not %clang_cc1 -std=c++17 -fverify-contracts -fverify-cache=%t/cache -emit-obj -o %t/x.o %s
// RUN: ls %t/cache | FileCheck %s --check-prefix=CACHE
//
// The -fverify-* options of a compilation: the driver forwards them, naming
// a bare -fverify-report's file after the object; the compiler rejects an
// invalid value; a file without a function to verify says nothing; and each
// option reaches the verifier.

namespace cv = cppverify;

int inc(int x)
  cv::pre(x < 100)
  cv::post(cv::result == x + 1)
{
  return x + 1;
}

int dec(int x)
  cv::post(cv::result == x - 1)
{
  return x - 1;
}

// DRIVER: "-cc1"
// DRIVER-SAME: "-fverify-backend=cvc5" "-fverify-timeout=5000" "-fverify-jobs=2" "-fverify-cache={{[^"]*}}cache" "-fverify-report={{[^"]*}}x.o.cppverify.json"

// NAMED: "-fverify-report={{[^"]*}}named.json"
// NAMED-NOT: cppverify.json

// BACKEND: error: invalid value 'lean' in '-fverify-backend=lean'
// TIMEOUT: error: invalid integral value 'soon' in '-fverify-timeout=soon'

// CHECK: remark: Verified: inc [backend=bmc, bound=0]
// CHECK: error: verification failed: dec [overflow] [backend=bmc{{.*}}]

// REPORT: "function":"inc",{{.*}}"status":"verified"
// REPORT: "function":"dec",{{.*}}"status":"failed"
// REPORT: {"bounded_safe":0,{{.*}}"failed":1,{{.*}}"schema":"cppverify.summary/1",{{.*}}"verified":1}

// CACHE: llvmcache-cppverify-
