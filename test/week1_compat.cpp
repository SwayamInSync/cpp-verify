// week1_compat.cpp — backward compatibility check
//
// This file is PLAIN C++. It uses all 12 contract keyword names as ordinary
// identifiers to prove that existing code is unaffected when -fverify-contracts
// is absent. This file must compile cleanly without any flags.
//
// COMMAND:
//   ./build/bin/clang -std=c++20 -c test/week1_compat.cpp -o /dev/null
//   echo "exit: $?"   # must print 0

// All 12 names used as regular C++ identifiers.
int pre      = 1;
int post     = 2;
int invariant = 3;
int decreases = 4;
int ghost    = 5;
int spec     = 6;
int proof    = 7;
int contract_assert = 8;
int forall   = 9;
int exists   = 10;
int old      = 11;
int result   = 12;

// Used as function names (different names from the variables above).
int compute_pre(int x)  { return x + 1; }
int compute_post(int x) { return x - 1; }
int compute_old(int x)  { return x * 2; }

// Used as parameter names.
void process(int invariant, int decreases, int ghost) {
    int local = invariant + decreases + ghost;
    (void)local;
}

// Used as struct member names.
struct Spec {
    int pre;
    int post;
    int result;
    int forall;
    int exists;
};
