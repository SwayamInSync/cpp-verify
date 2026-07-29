// RUN: not %cpp-verify --backend=bmc --unroll=4 --jobs=4 %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=TEXT
// RUN: not %cpp-verify --backend=bmc --unroll=4 --jobs=4 \
// RUN:   --diagnostics-format=json %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=JSON
// RUN: not %cpp-verify --backend=bmc --unroll=4 \
// RUN:   --obligation-out=%t.obligations %s > /dev/null 2>&1
// RUN: not %cpp-verify --obligation-in=%t.obligations \
// RUN:   --diagnostics-format=json 2>&1 \
// RUN:   | FileCheck %s --check-prefix=REPLAY

int loop_free(int value)
  post(result == value)
{
  return value;
}

int completes_at_two()
  post(result == 2)
{
  int index = 0;
  while (index < 2)
    invariant(index >= 0 && index <= 2)
  {
    ++index;
  }
  return index;
}

int bug_on_second_iteration()
  post(result == 3)
{
  int index = 0;
  while (index < 3)
    invariant(index >= 0 && index <= 3)
  {
    contract_assert(index != 1);
    ++index;
  }
  return index;
}

int open_frontier(int limit)
  pre(limit >= 0)
  post(result >= 0)
{
  int index = 0;
  while (index < limit)
    invariant(index >= 0)
  {
    ++index;
  }
  return index;
}

// TEXT: Verified: loop_free [backend=bmc, bound=0]
// TEXT: Verified: completes_at_two [backend=bmc, bound=2]
// TEXT-SAME: [bounds=0,1,2] [reused-queries={{[1-9][0-9]*}}]
// TEXT: error: verification failed: bug_on_second_iteration
// TEXT-SAME: trace: loop.iteration 1
// TEXT-SAME: -> loop.iteration 2
// TEXT-SAME: [backend=bmc, bound=2]
// TEXT-SAME: [bounds=0,1,2] [reused-queries={{[1-9][0-9]*}}]
// TEXT: BoundedSafe: open_frontier [backend=bmc, bound=4]
// TEXT-SAME: [reason=bmc.incomplete-bound]
// TEXT-SAME: [bounds=0,1,2,3,4] [reused-queries={{[1-9][0-9]*}}]

// JSON: "bound":0,"explored_bounds":[0],"function":"loop_free"
// JSON: "bound":2,"explored_bounds":[0,1,2],"function":"completes_at_two"
// JSON-SAME: "reused_queries":{{[1-9][0-9]*}}
// JSON: "bound":2,"explored_bounds":[0,1,2],"function":"bug_on_second_iteration"
// JSON-SAME: "message":"iteration 1"
// JSON-SAME: "message":"iteration 2"
// JSON: "bound":4,"explored_bounds":[0,1,2,3,4],"function":"open_frontier"
// JSON-SAME: "reason":"bmc.incomplete-bound"

// REPLAY: "backend":"bmc","bound":0
// REPLAY-NOT: "explored_bounds"
// REPLAY: "backend":"bmc","bound":2
// REPLAY-NOT: "explored_bounds"
// REPLAY: "backend":"bmc","bound":2
// REPLAY-NOT: "explored_bounds"
// REPLAY: "backend":"bmc","bound":4
// REPLAY-NOT: "explored_bounds"
