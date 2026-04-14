// =============================================================================
// CppVerify Comprehensive Test
//
// This file exercises every contract construct and is designed to catch
// regressions in: keyword lexing, contract parsing, AST node types,
// return-type resolution for 'result', context restrictions for 'old'/'result',
// quantifier type checking, loop contracts on both while and for, ghost blocks,
// contract_assert, spec/proof function qualifiers, and multiple pre/post
// clauses.
//
// Build & test:
//   ./build/bin/clang++ -cc1 -fverify-contracts -ast-dump samples/test1.cpp
//   ./build/bin/clang++ -cc1 -fverify-contracts -emit-llvm -o /dev/null samples/test1.cpp
// =============================================================================

// ---------------------------------------------------------------------------
// 1. Spec function (int return) with decreases
// ---------------------------------------------------------------------------
spec int factorial(int n)
  decreases(n)
{
    if (n <= 1) return 1;
    return n * factorial(n - 1);
}

// ---------------------------------------------------------------------------
// 2. Proof function (void return) with pre/post/decreases + recursion
// ---------------------------------------------------------------------------
proof void lemma_factorial_positive(int n)
  pre(n >= 1)
  post(factorial(n) >= 1)
  decreases(n)
{
    if (n == 1) {
        // base case: factorial(1) == 1 >= 1
    } else {
        lemma_factorial_positive(n - 1);
    }
}

// ---------------------------------------------------------------------------
// 3. Regular function with multiple pre/post, while-loop contracts,
//    ghost block, contract_assert, result, and spec function calls in
//    contracts.
// ---------------------------------------------------------------------------
int safe_factorial(int n)
  pre(n >= 0)
  pre(n <= 12)
  post(result == factorial(n))
  post(result >= 1)
{
    if (n == 0) return 1;

    int acc = 1;
    int i = 1;

    while (i <= n)
      invariant(1 <= i && i <= n + 1)
      invariant(acc == factorial(i - 1))
      decreases(n - i + 1)
    {
        ghost {
            lemma_factorial_positive(i);
            contract_assert(acc * i >= acc);
        }

        acc = acc * i;
        i = i + 1;
    }

    return acc;
}

// ---------------------------------------------------------------------------
// 4. Spec functions returning bool — exercises forall/exists quantifiers
// ---------------------------------------------------------------------------
spec bool all_positive(int arr[], int n)
{
    return forall(i, 0, n, arr[i] > 0);
}

spec bool has_zero(int arr[], int n)
{
    return exists(i, 0, n, arr[i] == 0);
}

// ---------------------------------------------------------------------------
// 5. Function with old() and result — exercises postcondition-only keywords
// ---------------------------------------------------------------------------
int increment(int x)
  pre(x < 2147483647)
  post(result == old(x) + 1)
{
    return x + 1;
}

// ---------------------------------------------------------------------------
// 6. Non-int return types — catches stale CurrentContractReturnType bugs.
//    Each function's 'result' must get the correct QualType from the DeclSpec.
// ---------------------------------------------------------------------------

// 6a. bool return type
bool is_positive(int x)
  post(result == (old(x) > 0))
{
    return x > 0;
}

// 6b. unsigned int return type
unsigned int safe_subtract(unsigned int a, unsigned int b)
  pre(a >= b)
  post(result == old(a) - old(b))
{
    return a - b;
}

// 6c. long return type
long wide_add(long a, long b)
  pre(a >= 0)
  pre(b >= 0)
  post(result >= old(a))
  post(result >= old(b))
{
    return a + b;
}

// 6d. short return type
short clamp_to_short(int x)
  pre(x >= -32768)
  pre(x <= 32767)
  post(result == old(x))
{
    return (short)x;
}

// ---------------------------------------------------------------------------
// 7. For-loop contracts — catches missing VisitForStmt in AST dumper
// ---------------------------------------------------------------------------
int sum_range(int n)
  pre(n >= 0)
  post(result >= 0)
{
    int s = 0;
    for (int i = 0; i < n; i = i + 1)
      invariant(s >= 0)
      invariant(i >= 0)
      decreases(n - i)
    {
        s = s + i;
    }
    return s;
}

// ---------------------------------------------------------------------------
// 8. Multiple ghost blocks + interleaved contract_asserts
// ---------------------------------------------------------------------------
int double_val(int x)
  pre(x >= 0)
  pre(x <= 1000000)
  post(result == old(x) + old(x))
{
    ghost {
        contract_assert(x >= 0);
    }

    int r = x + x;

    ghost {
        contract_assert(r == x + x);
        contract_assert(r >= 0);
    }

    return r;
}

// ---------------------------------------------------------------------------
// 9. Spec function calling another spec function — exercises spec-to-spec
//    call resolution and return type propagation
// ---------------------------------------------------------------------------
spec int double_factorial(int n)
{
    return factorial(n) * factorial(n);
}

spec bool factorial_is_positive(int n)
{
    return factorial(n) >= 1;
}

// ---------------------------------------------------------------------------
// 10. Proof function with multiple lemma calls in ghost block
// ---------------------------------------------------------------------------
proof void lemma_factorials_positive(int a, int b)
  pre(a >= 1)
  pre(b >= 1)
  post(factorial(a) + factorial(b) >= 2)
{
    lemma_factorial_positive(a);
    lemma_factorial_positive(b);
}

// ---------------------------------------------------------------------------
// 11. Function with only preconditions (no postconditions) — verifies that
//     missing post doesn't cause issues
// ---------------------------------------------------------------------------
int checked_div(int a, int b)
  pre(b != 0)
{
    return a / b;
}

// ---------------------------------------------------------------------------
// 12. Function with only postconditions (no preconditions)
// ---------------------------------------------------------------------------
int abs_val(int x)
  post(result >= 0)
{
    if (x < 0) return -x;
    return x;
}

// ---------------------------------------------------------------------------
// 13. Back-to-back functions with different return types — stress test for
//     CurrentContractReturnType resetting between function definitions
// ---------------------------------------------------------------------------
bool flag_a(int x)
  post(result == (old(x) > 0))
{
    return x > 0;
}

int value_b(int x)
  pre(x >= 0)
  post(result == old(x) + 1)
{
    return x + 1;
}

bool flag_c(int y)
  post(result == (old(y) != 0))
{
    return y != 0;
}

unsigned int value_d(unsigned int z)
  post(result == old(z))
{
    return z;
}

// ---------------------------------------------------------------------------
// 14. While-loop with only invariant (no decreases) — exercises optional
//     decreases clause
// ---------------------------------------------------------------------------
int find_first_nonzero(int arr[], int n)
  pre(n > 0)
{
    int i = 0;
    while (i < n)
      invariant(i >= 0)
    {
        if (arr[i] != 0) return i;
        i = i + 1;
    }
    return -1;
}

// ---------------------------------------------------------------------------
// 15. Quantifier in postcondition — exercises forall inside post()
// ---------------------------------------------------------------------------
spec bool all_zero(int arr[], int n)
{
    return forall(i, 0, n, arr[i] == 0);
}

void zero_fill(int arr[], int n)
  pre(n >= 0)
  post(all_zero(arr, n))
{
    for (int i = 0; i < n; i = i + 1)
      invariant(i >= 0)
      invariant(all_zero(arr, i))
      decreases(n - i)
    {
        arr[i] = 0;
    }
}

// ---------------------------------------------------------------------------
// 16. Pointer return types — exercises full-Declarator return type resolution.
//     The 'result' keyword must be typed as 'int *', not just 'int'.
// ---------------------------------------------------------------------------
int *find_ptr(int arr[], int n, int val)
  pre(n > 0)
{
    for (int i = 0; i < n; i = i + 1)
    {
        if (arr[i] == val) return &arr[i];
    }
    return (int *)0;
}

// ---------------------------------------------------------------------------
// 17. Const pointer return — exercises pointer + const qualifier on return.
// ---------------------------------------------------------------------------
const int *find_const(const int arr[], int n, int val)
  pre(n > 0)
{
    for (int i = 0; i < n; i = i + 1)
    {
        if (arr[i] == val) return &arr[i];
    }
    return (const int *)0;
}

// ---------------------------------------------------------------------------
// 18. Struct return type — exercises struct return with contracts.
// ---------------------------------------------------------------------------
struct Point {
    int x;
    int y;
};

Point make_origin()
  post(result.x == 0)
  post(result.y == 0)
{
    Point p;
    p.x = 0;
    p.y = 0;
    return p;
}

Point translate(Point p, int dx, int dy)
  post(result.x == old(p.x) + old(dx))
  post(result.y == old(p.y) + old(dy))
{
    Point r;
    r.x = p.x + dx;
    r.y = p.y + dy;
    return r;
}

// ---------------------------------------------------------------------------
// 19. Typedef return type — exercises TST_typename path through Declarator.
// ---------------------------------------------------------------------------
typedef unsigned long usize;

usize safe_len(int arr[], int n)
  pre(n >= 0)
  post(result >= 0)
{
    return (usize)n;
}

// ---------------------------------------------------------------------------
// 20. Pointer return with postcondition — 'result' must be typed 'int *'
//     (this is the key regression test for the DeclSpec-only bug).
// ---------------------------------------------------------------------------
int *max_ptr(int *a, int *b)
  post(result == old(a) || result == old(b))
{
    if (*a >= *b) return a;
    return b;
}
