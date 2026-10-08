#include <cppverify.h>

cppverify::spec int assigns(int n) cppverify::post(cppverify::result >= 0) by { n = 1; } { return 0; }

cppverify::spec int returns(int n) cppverify::post(cppverify::result >= 0) by { return 0; } { return 0; }

cppverify::spec int stores(int *p) cppverify::post(cppverify::result >= 0) by { *p = 1; } { return 0; }
