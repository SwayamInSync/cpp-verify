// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Cell {
  int value;

  template <typename T>
  Cell &operator=(T &other) {
    value = other.value + 1;
    return *this;
  }
};

Cell runtime_cell;

void write_value(int *target)
  pre(target != nullptr)
  modifies(*target)
  post(*target == 2)
{
  *target = 2;
}

int ghost_local_escape(int value)
  post(result == 2)
{
  ghost {
    value = 2;
  }
  return value;
}

void ghost_heap_store(int *target)
  pre(target != nullptr)
  modifies(*target)
  post(*target == 2)
{
  ghost {
    *target = 2;
  }
}

int ghost_exec_call(int value)
  post(result == 2)
{
  ghost {
    write_value(&value);
  }
  return value;
}

proof void proof_heap_store(int *target)
  modifies(*target)
  post(*target == 2)
{
  *target = 2;
}

proof void proof_exec_call(int *target)
{
  write_value(target);
}

int ghost_pointer_store(Cell *target)
  pre(target != nullptr)
  modifies(*target)
{
  ghost {
    Cell *alias = target;
    alias->value = 2;
  }
  return target->value;
}

proof void proof_global_store()
{
  runtime_cell.value = 2;
}

Cell user_defined_assignment(Cell input)
  post(result.value == input.value)
{
  Cell output{0};
  output = input;
  return output;
}

int ghost_return()
  post(result == 1)
{
  ghost {
    return 1;
  }
  return 0;
}

int ghost_nonterminating_loop()
  post(result == 1)
{
  ghost {
    while (true) {
    }
  }
  return 0;
}

proof void nonterminating_proof()
  post(false)
{
  while (true) {
  }
}

// VERIFY-DAG: error: ghost_local_escape: ghost code cannot modify executable state
// VERIFY-DAG: error: ghost_heap_store: ghost code cannot modify executable state
// VERIFY-DAG: error: ghost_exec_call: proof-only code cannot call executable functions
// VERIFY-DAG: error: proof_heap_store: proof functions cannot modify executable memory
// VERIFY-DAG: error: proof_exec_call: proof-only code cannot call executable functions
// VERIFY-DAG: error: ghost_pointer_store: ghost code cannot modify executable state
// VERIFY-DAG: error: proof_global_store: global aggregate assignment is unsupported
// VERIFY-DAG: error: user_defined_assignment: user-defined aggregate assignment is unsupported
// VERIFY-DAG: error: ghost_return: ghost code cannot alter executable control flow
// VERIFY-DAG: error: ghost_nonterminating_loop: proof-only loops require a decreases clause
// VERIFY-DAG: error: nonterminating_proof: proof-only loops require a decreases clause
