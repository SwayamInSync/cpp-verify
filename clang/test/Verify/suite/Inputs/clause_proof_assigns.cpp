#include <cppverify.h>

spec int assigns(int n) post(result >= 0) by { n = 1; } { return 0; }

spec int returns(int n) post(result >= 0) by { return 0; } { return 0; }

spec int stores(int *p) post(result >= 0) by { *p = 1; } { return 0; }
