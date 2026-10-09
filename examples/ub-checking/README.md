# Undefined-Behavior Checking examples

Runnable examples for Layer-A UB checking (signed integer overflow, division /
modulo by zero). See `docs/UB-CHECKING.md` for the design.

Each file is ordinary C++ with contracts. Verify it with:

```bash
./build/bin/cpp-verify examples/ub-checking/<file>.cpp
```

These definedness checks are always on; no flag enables or disables them.
Memory checking (`--check-ub`) is on by default as well, and
`--no-check-ub` turns it off, which changes none of these verdicts: no file
here accesses memory.

| File | Verdict |
|---|---|
| `add_unsafe.cpp` | **fails** — `a + b` can overflow |
| `add_safe.cpp` | verifies — operands bounded |
| `negate_unsafe.cpp` | **fails** — `-x` overflows at `INT_MIN` |
| `negate_safe.cpp` | verifies — precondition excludes `INT_MIN` |
| `divide_unsafe.cpp` | **fails** — divisor may be `0` |
| `divide_safe.cpp` | verifies — `b > 0` rules out `/0` and `INT_MIN/-1` |
| `unsigned_wraps.cpp` | verifies — unsigned overflow is defined, never flagged |

In `divide_unsafe.cpp` the postcondition holds on every path, so only the
definedness check finds the bug. Each failure reports the exact
counterexample (e.g. `x = -2147483648`), telling you the precondition your
function actually needs instead of making you discover it by hand.
