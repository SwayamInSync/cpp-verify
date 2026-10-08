#ifndef FROM_DATABASE
#error compiled without the flags of the compilation database
#endif

int identity(int x) cppverify::post(cppverify::result == x) { return x; }
