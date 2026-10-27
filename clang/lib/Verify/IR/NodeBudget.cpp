//===--- NodeBudget.cpp ---------------------------------------------------===//
#include "NodeBudget.h"

using namespace clang;
using namespace verify;

thread_local NodeBudget *NodeBudget::Active = nullptr;

static thread_local uint64_t ThreadLimit = 0;

NodeBudget::Limit::Limit(uint64_t Nodes) : Saved(ThreadLimit) {
  ThreadLimit = Nodes;
}

NodeBudget::Limit::~Limit() { ThreadLimit = Saved; }

NodeBudget::NodeBudget() : Outer(Active), Max(ThreadLimit) { Active = this; }

NodeBudget::~NodeBudget() {
  Active = Outer;
  if (Outer)
    Outer->Built += Built;
}
