//===--- Passivize.cpp ----------------------------------------------------===//
#include "Passivize.h"
#include <map>
#include <set>

using namespace clang;
using namespace verify;

template <typename T, typename U> static T *cast(U *p) {
  return static_cast<T *>(p);
}
template <typename T, typename U> static const T *cast(const U *p) {
  return static_cast<const T *>(p);
}

static std::unique_ptr<VExpr>
cloneExpr(const VExpr *E, const std::map<std::string, std::string> &Renames);

static std::unique_ptr<VExpr>
cloneExpr(const VExpr *E, const std::map<std::string, std::string> &Renames) {
  if (!E)
    return nullptr;
  switch (E->K) {
  case VExpr::Literal: {
    const auto *L = static_cast<const VLiteralExpr *>(E);
    return std::make_unique<VLiteralExpr>(L->Value, L->Ty, L->Loc);
  }
  case VExpr::Var: {
    const auto *V = static_cast<const VVarExpr *>(E);
    std::string Name = V->Name;
    if (auto It = Renames.find(Name); It != Renames.end())
      Name = It->second;
    return std::make_unique<VVarExpr>(Name, V->Ty, V->Loc);
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return std::make_unique<VBinOpExpr>(
        B->Op, cloneExpr(B->Lhs.get(), Renames), cloneExpr(B->Rhs.get(), Renames),
        B->Ty, B->Loc);
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    return std::make_unique<VUnaryOpExpr>(
        U->Op, cloneExpr(U->Operand.get(), Renames), U->Ty, U->Loc);
  }
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    return std::make_unique<VCastExpr>(cloneExpr(C->Inner.get(), Renames),
                                       C->FromTy, C->Ty, C->Loc);
  }
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    return std::make_unique<VLoadExpr>(cloneExpr(L->Ptr.get(), Renames), L->Ty,
                                       L->Loc);
  }
  case VExpr::Result: {
    const auto *R = static_cast<const VResultExpr *>(E);
    if (auto It = Renames.find("result"); It != Renames.end())
      return std::make_unique<VVarExpr>(It->second, R->Ty, R->Loc);
    return std::make_unique<VResultExpr>(R->Ty, R->Loc);
  }
  case VExpr::Old: {
    const auto *O = static_cast<const VOldExpr *>(E);
    return std::make_unique<VOldExpr>(cloneExpr(O->Inner.get(), Renames),
                                      O->Ty, O->Loc);
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return std::make_unique<VConditionalExpr>(
        cloneExpr(C->Cond.get(), Renames), cloneExpr(C->Then.get(), Renames),
        cloneExpr(C->Else.get(), Renames), C->Ty, C->Loc);
  }
  }
  return nullptr;
}

static std::unique_ptr<VExpr>
substituteResult(std::unique_ptr<VExpr> E, const std::unique_ptr<VExpr> &RetVal) {
  if (!E)
    return nullptr;
  if (E->K == VExpr::Result)
    return cloneExpr(RetVal.get(), {});
  if (E->K == VExpr::BinOp) {
    auto *B = static_cast<VBinOpExpr *>(E.get());
    return std::make_unique<VBinOpExpr>(
        B->Op, substituteResult(cloneExpr(B->Lhs.get(), {}), RetVal),
        substituteResult(cloneExpr(B->Rhs.get(), {}), RetVal), B->Ty, B->Loc);
  }
  if (E->K == VExpr::UnaryOp) {
    auto *U = static_cast<VUnaryOpExpr *>(E.get());
    return std::make_unique<VUnaryOpExpr>(
        VUnaryOp::Not, substituteResult(cloneExpr(U->Operand.get(), {}), RetVal),
        U->Ty, U->Loc);
  }
  return cloneExpr(E.get(), {});
}

class PassivizerImpl {
  std::map<std::string, int> Versions;
  std::map<std::string, std::unique_ptr<VExpr>> OldState;
  std::string ResultVar = "__result";

  std::string versionedName(const std::string &N) {
    int &V = Versions[N];
    return N + "_" + std::to_string(V);
  }

  std::string bump(const std::string &N) {
    return N + "_" + std::to_string(++Versions[N]);
  }

public:
  PassiveProgram run(const VFunction &Fn) {
    PassiveProgram P;
    for (const auto &Pre : Fn.Preconditions)
      P.EntryAssumes.push_back(cloneExpr(Pre.get(), {}));

    for (const auto &Param : Fn.Params)
      OldState[Param.first] = cloneExpr(
          std::make_unique<VVarExpr>(Param.first, Param.second, SourceLocation())
              .get(),
          {});

    std::map<std::string, std::string> Renames;
    for (const auto &Param : Fn.Params)
      Renames[Param.first] = versionedName(Param.first);

    for (const auto &S : Fn.Body)
      processStmt(*S, P, Renames);

    if (auto It = Renames.find("result"); It != Renames.end())
      P.ResultVarName = It->second;
    for (const auto &Post : Fn.Postconditions) {
      auto PostCopy = cloneExpr(Post.get(), Renames);
      P.ExitAsserts.push_back(std::move(PostCopy));
    }
    return P;
  }

  void processStmt(const VStmt &S, PassiveProgram &P,
                   std::map<std::string, std::string> &Renames) {
    switch (S.K) {
    case VStmt::Assign: {
      const auto &A = static_cast<const VAssignStmt &>(S);
      auto Val = cloneExpr(A.Value.get(), Renames);
      std::string NewName = bump(A.Target);
      Renames[A.Target] = NewName;
      auto PS = std::make_unique<PassiveStmt>();
      PS->K = PassiveStmt::Assume;
      PS->Cond = std::make_unique<VBinOpExpr>(
          VBinOp::Eq,
          std::make_unique<VVarExpr>(NewName, Val->Ty, A.Loc),
          std::move(Val), VType::makeBool(), A.Loc);
      P.Stmts.push_back(std::move(PS));
      break;
    }
    case VStmt::If: {
      const auto &I = static_cast<const VIfStmt &>(S);
      auto Cond = cloneExpr(I.Cond.get(), Renames);
      auto ThenRenames = Renames;
      auto ElseRenames = Renames;
      for (const auto &TS : I.Then)
        processStmt(*TS, P, ThenRenames);
      for (const auto &ES : I.Else)
        processStmt(*ES, P, ElseRenames);
      // Merge: for each changed variable, assume (cond -> then_ver) & (!cond -> else_ver)
      std::set<std::string> Changed;
      for (const auto &[Name, Ver] : ThenRenames)
        if (Renames.count(Name) && Renames[Name] != Ver)
          Changed.insert(Name);
      for (const auto &[Name, Ver] : ElseRenames)
        if (Renames.count(Name) && Renames[Name] != Ver)
          Changed.insert(Name);
      for (const std::string &Name : Changed) {
        auto ThenVal = std::make_unique<VVarExpr>(ThenRenames[Name],
                                                  VType::makeInt32(VIntMode::Machine),
                                                  I.Loc);
        auto ElseVal = std::make_unique<VVarExpr>(ElseRenames[Name],
                                                  VType::makeInt32(VIntMode::Machine),
                                                  I.Loc);
        auto Merged = bump(Name);
        Renames[Name] = Merged;
        auto MergeExpr = std::make_unique<VConditionalExpr>(
            cloneExpr(Cond.get(), {}), std::move(ThenVal), std::move(ElseVal),
            VType::makeInt32(VIntMode::Machine), I.Loc);
        auto PS = std::make_unique<PassiveStmt>();
        PS->K = PassiveStmt::Assume;
        PS->Cond = std::make_unique<VBinOpExpr>(
            VBinOp::Eq, std::make_unique<VVarExpr>(Merged, VType::makeInt32(VIntMode::Machine), I.Loc),
            std::move(MergeExpr), VType::makeBool(), I.Loc);
        P.Stmts.push_back(std::move(PS));
      }
      break;
    }
    case VStmt::Return: {
      const auto &R = static_cast<const VReturnStmt &>(S);
      std::unique_ptr<VExpr> Ret = R.Value
          ? cloneExpr(R.Value.get(), Renames)
          : std::make_unique<VLiteralExpr>(0, VType::makeInt32(VIntMode::Machine), R.Loc);
      std::string RetVer = bump(ResultVar);
      Renames["result"] = RetVer;
      auto PS = std::make_unique<PassiveStmt>();
      PS->K = PassiveStmt::Assume;
      PS->Cond = std::make_unique<VBinOpExpr>(
          VBinOp::Eq, std::make_unique<VVarExpr>(RetVer, Ret->Ty, R.Loc),
          std::move(Ret), VType::makeBool(), R.Loc);
      P.Stmts.push_back(std::move(PS));
      break;
    }
    default:
      break;
    }
  }
};

PassiveProgram Passivizer::run(const VFunction &Fn) {
  PassivizerImpl Impl;
  return Impl.run(Fn);
}