# Undefined-Behavior Checking examples

Runnable examples for Layer-A UB checking (signed integer overflow, division /
modulo by zero). See `docs/UB-CHECKING.md` for the design.

Each file is ordinary C++ with contracts. Verify it two ways:

```bash
# Functional only (signed overflow wraps silently — the old behavior):
./build/bin/cpp-verify examples/ub-checking/<file>.cpp

# Functional + UB freedom (signed overflow / div-by-zero become errors):
./build/bin/cpp-verify --check-ub examples/ub-checking/<file>.cpp
```

| File | Without `--check-ub` | With `--check-ub` |
|---|---|---|
| `add_unsafe.cpp` | verifies | **fails** — `a + b` can overflow |
| `add_safe.cpp` | verifies | verifies — operands bounded |
| `negate_unsafe.cpp` | verifies | **fails** — `-x` overflows at `INT_MIN` |
| `negate_safe.cpp` | verifies | verifies — precondition excludes `INT_MIN` |
| `divide_unsafe.cpp` | verifies | **fails** — divisor may be `0` |
| `divide_safe.cpp` | verifies | verifies — `b > 0` rules out `/0` and `INT_MIN/-1` |
| `unsigned_wraps.cpp` | verifies | verifies — unsigned overflow is defined, never flagged |

Notice every `*_unsafe` example **verifies without `--check-ub`**: under silent
wrapping the postcondition still holds, so functional verification alone is
blind to the bug. `--check-ub` is what makes the runtime contract mean something
— and it reports the exact counterexample (e.g. `x = INT_MIN`), telling you the
precondition your function actually needs instead of making you discover it by
hand.
