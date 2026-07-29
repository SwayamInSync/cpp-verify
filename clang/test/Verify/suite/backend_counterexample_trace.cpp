// RUN: not %cpp-verify --diagnostics-format=json %s 2>&1 | FileCheck %s --check-prefix=TRACE
// RUN: %cpp-verify --lower-only --obligation-out=%t.obligations %s
// RUN: not %cpp-verify --obligation-in=%t.obligations --diagnostics-format=json 2>&1 | FileCheck %s --check-prefix=ARCHIVE
// RUN: not %cpp-verify --backend=bmc --unroll=1 --diagnostics-format=json %s 2>&1 | FileCheck %s --check-prefix=BMC

void set_value(int &target, int value)
  modifies(target)
  post(target == value)
{
  target = value;
}

int pass_through(int value)
  post(result == value)
{
  return value;
}

int require_positive(int value)
  pre(value > 0)
  post(result == value)
{
  return value;
}

spec int trace_only_identity(int value)
{
  return value;
}

int unreachable_trace_only_spec(int value)
  post(result == 0)
{
  return 0;
  return trace_only_identity(value);
}

int path_and_call(int value)
  pre(value == 1)
  post(result == 0)
{
  int answer = 0;
  if (value > 0)
    answer = pass_through(value);
  else
    answer = 2;
  return answer;
}

int failing_call_precondition()
  post(result == -1)
{
  return require_positive(-1);
}

int heap_and_provenance()
  post(result == 0)
{
  int *owner = new int(1);
  *owner = 2;
  int observed = *owner;
  delete owner;
  return observed;
}

int lexical_lifetime()
  post(result == 0)
{
  {
    int local = 0;
    set_value(local, 1);
  }
  return 1;
}

int unknown_branch_guard(bool choose)
  post(result == 0)
{
  if (choose) {
  } else {
  }
  return 1;
}

int loop_path()
  post(result == 0)
{
  int index = 0;
  while (index < 1)
    invariant(index >= 0 && index <= 1)
    decreases(1 - index)
  {
    index = index + 1;
  }
  return index;
}

// TRACE: "function":"path_and_call"
// TRACE-SAME: "kind":"branch","message":"then"
// TRACE-SAME: "kind":"call","message":"pass_through"
// TRACE-SAME: "kind":"return","message":"return"
// TRACE: "function":"failing_call_precondition"
// TRACE-SAME: "kind":"call","message":"require_positive"
// TRACE: "function":"heap_and_provenance"
// TRACE-SAME: "kind":"allocation","message":"allocation"
// TRACE-SAME: "label":"provenance"
// TRACE-SAME: "kind":"heap-write","message":"store"
// TRACE-SAME: "kind":"deallocation","message":"delete"
// TRACE: "function":"lexical_lifetime"
// TRACE-SAME: "kind":"call","message":"set_value"
// TRACE-SAME: "kind":"lifetime-end","message":"lifetime end"
// TRACE: "function":"unknown_branch_guard"
// TRACE-SAME: "active":null,"kind":"branch","message":"then"
// TRACE-SAME: "active":null,"kind":"branch","message":"else"
// TRACE: "function":"loop_path"
// TRACE-SAME: "kind":"loop","message":"entry"
// TRACE-SAME: "kind":"loop","message":"exit"

// ARCHIVE: "function":"path_and_call"
// ARCHIVE-SAME: "kind":"branch","message":"then"
// ARCHIVE-SAME: "kind":"call","message":"pass_through"
// ARCHIVE: "function":"failing_call_precondition"
// ARCHIVE-SAME: "kind":"call","message":"require_positive"
// ARCHIVE: "function":"heap_and_provenance"
// ARCHIVE-SAME: "kind":"allocation","message":"allocation"
// ARCHIVE-SAME: "kind":"deallocation","message":"delete"
// ARCHIVE: "function":"lexical_lifetime"
// ARCHIVE-SAME: "kind":"lifetime-end","message":"lifetime end"
// ARCHIVE: "function":"unknown_branch_guard"
// ARCHIVE-SAME: "active":null,"kind":"branch","message":"then"
// ARCHIVE-SAME: "active":null,"kind":"branch","message":"else"

// BMC: "function":"loop_path"
// BMC-SAME: "kind":"loop","message":"iteration"
