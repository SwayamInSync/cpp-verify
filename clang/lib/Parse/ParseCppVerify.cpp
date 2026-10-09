//===--- ParseCppVerify.cpp - cpp-verify contract parsing -----------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// cpp-verify constructs are written qualified by the namespace cppverify,
// directly or through an alias: cppverify::pre(x > 0), cv::check(e). The
// parser turns each such qualified name into one annot_cppverify token, at
// the positions where the construct may appear.
//
//===----------------------------------------------------------------------===//

#include "clang/AST/ASTContext.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/ExprContract.h"
#include "clang/AST/StmtContract.h"
#include "clang/Basic/CppVerifyConstructs.h"
#include "clang/Basic/DiagnosticParse.h"
#include "clang/Parse/Parser.h"
#include "clang/Parse/RAIIObjectsForParser.h"
#include "clang/Sema/DeclSpec.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/Scope.h"
#include "llvm/Support/SaveAndRestore.h"

using namespace clang;

namespace {

/// The value of an annot_cppverify token.
struct CppVerifyAnnotation {
  CppVerifyConstruct Construct;
  /// The construct's declaration in <cppverify.h>, as written.
  Expr *Reference;
  bool Recorded = false;
};

bool isCppVerifyNamespace(const NamespaceDecl *NS) {
  return NS && NS->getIdentifier() && NS->getIdentifier()->isStr("cppverify") &&
         NS->getParent()->getRedeclContext()->isTranslationUnit();
}

/// The namespace cppverify, when \p SS names it.
const NamespaceDecl *cppVerifyNamespaceOf(const CXXScopeSpec &SS) {
  NestedNameSpecifier NNS = SS.getScopeRep();
  if (NNS.getKind() != NestedNameSpecifier::Kind::Namespace)
    return nullptr;
  const NamespaceDecl *NS =
      NNS.getAsNamespaceAndPrefix().Namespace->getNamespace();
  return isCppVerifyNamespace(NS) ? NS : nullptr;
}

/// A construct's declaration in <cppverify.h>: deleted, or an enumerator.
bool isCppVerifyDeclaration(const NamedDecl *D) {
  const DeclContext *DC = D->getDeclContext();
  if (isa<EnumDecl>(DC))
    DC = DC->getParent();
  const auto *NS = dyn_cast<NamespaceDecl>(DC);
  if (!isCppVerifyNamespace(NS) || !D->getIdentifier() ||
      !lookupCppVerifyConstruct(D->getName()))
    return false;
  const auto *FD = dyn_cast<FunctionDecl>(D);
  return isa<EnumConstantDecl>(D) || (FD && FD->isDeleted());
}

/// Index into err_cppverify_misplaced: where \p C belongs.
unsigned homeOf(CppVerifyConstruct C) {
  using namespace CppVerifyPosition;
  unsigned P = getCppVerifyPositions(C);
  if (P == (FunctionClause | LoopClause))
    return 6;
  if (P & FunctionClause)
    return 0;
  if (P & LoopClause)
    return 1;
  if (P & ClassMember)
    return 2;
  if (P & Specifier)
    return 3;
  if (P & Statement)
    return 4;
  return 5;
}

/// A construct word written without its qualifier: whether the tokens after
/// it fit the construct.
bool fitsBareConstruct(CppVerifyConstruct C, const Token &Next,
                       const LangOptions &LangOpts) {
  switch (C) {
  case CppVerifyConstruct::Result:
  case CppVerifyConstruct::CompleteBehaviors:
  case CppVerifyConstruct::DisjointBehaviors:
    return true;
  case CppVerifyConstruct::Inductive:
    return Next.isNot(tok::l_paren);
  case CppVerifyConstruct::Spec:
  case CppVerifyConstruct::Proof:
    return Next.isOneOf(tok::identifier, tok::coloncolon, tok::kw_const) ||
           Next.isSimpleTypeSpecifier(LangOpts);
  case CppVerifyConstruct::Ghost:
    return Next.isOneOf(tok::l_brace, tok::identifier, tok::coloncolon) ||
           Next.isSimpleTypeSpecifier(LangOpts);
  case CppVerifyConstruct::Calc:
    return Next.is(tok::l_brace);
  default:
    return Next.is(tok::l_paren);
  }
}

} // namespace

CppVerifyConstruct Parser::getCppVerifyConstruct(const Token &T) const {
  assert(T.is(tok::annot_cppverify));
  return static_cast<const CppVerifyAnnotation *>(T.getAnnotationValue())
      ->Construct;
}

bool Parser::tryAnnotateCppVerify(unsigned Position) {
  if (Tok.is(tok::annot_cppverify))
    return true;
  if (!getLangOpts().VerifyContracts || !getLangOpts().CPlusPlus)
    return false;
  ASTContext &Ctx = Actions.getASTContext();

  // A construct word without its qualifier, where nothing else is visible by
  // that name: say how to write it, and parse it as the construct.
  if (Tok.is(tok::identifier) && NextToken().isNot(tok::coloncolon)) {
    IdentifierInfo *II = Tok.getIdentifierInfo();
    std::optional<CppVerifyConstruct> C =
        II->isStr("contract_assert") ? CppVerifyConstruct::Check
                                     : lookupCppVerifyConstruct(II->getName());
    if (!C || !(getCppVerifyPositions(*C) & Position) ||
        !fitsBareConstruct(*C, NextToken(), getLangOpts()))
      return false;
    // After a using-directive the word names the construct's declaration in
    // <cppverify.h>; otherwise it must name nothing, and an expression word
    // is taken for a construct only in contracts and verification code.
    NamedDecl *Found = Actions.LookupSingleName(
        getCurScope(), II, Tok.getLocation(), Sema::LookupOrdinaryName);
    if (Found && !isCppVerifyDeclaration(Found))
      return false;
    if (!Found && (Position & CppVerifyPosition::Expression) &&
        !CppVerifyContextDepth) {
      const FunctionDecl *FD = Actions.getCurFunctionDecl();
      const FunctionContractInfo *FCI =
          FD ? Ctx.getFunctionContract(FD) : nullptr;
      if (!FCI || !(FCI->IsSpec || FCI->IsProof))
        return false;
    }
    StringRef Spelling = getCppVerifySpelling(*C);
    FixItHint Fix = FixItHint::CreateReplacement(
        Tok.getLocation(), ("cppverify::" + Spelling).str());
    if ((*C == CppVerifyConstruct::Pre || *C == CppVerifyConstruct::Post) &&
        (Position & CppVerifyPosition::FunctionClause))
      Diag(Tok, diag::err_cppverify_cxx26_contract)
          << (*C == CppVerifyConstruct::Post) << Spelling << Fix;
    else
      Diag(Tok, diag::err_cppverify_unqualified)
          << II->getName() << Spelling << Fix;
    SourceLocation Loc = Tok.getLocation();
    Tok.setKind(tok::annot_cppverify);
    Tok.setAnnotationValue(new (Ctx) CppVerifyAnnotation{*C, nullptr});
    Tok.setAnnotationEndLoc(Loc);
    PP.AnnotateCachedTokens(Tok);
    return true;
  }

  if (!Tok.isOneOf(tok::identifier, tok::coloncolon, tok::annot_cxxscope))
    return false;
  SourceLocation Start = Tok.getLocation();
  if (Tok.isNot(tok::annot_cxxscope)) {
    // The construct word ends the qualified name: [::] (id ::)+ word.
    unsigned N = Tok.is(tok::coloncolon) ? 1 : 0;
    while (GetLookAheadToken(N).is(tok::identifier) &&
           GetLookAheadToken(N + 1).is(tok::coloncolon))
      N += 2;
    if (N < 2)
      return false;
    const Token &Last = GetLookAheadToken(N);
    if (Last.is(tok::code_completion)) {
      // Complete the members of the namespace, the constructs among them.
      TryAnnotateCXXScopeToken();
      return false;
    }
    if (Last.isNot(tok::identifier))
      return false;
    std::optional<CppVerifyConstruct> Spelled =
        lookupCppVerifyConstruct(Last.getIdentifierInfo()->getName());
    if (!Spelled && !(Position & CppVerifyPosition::FunctionClause))
      return false;
    // Without <cppverify.h> the namespace does not exist: say why, and parse
    // cppverify::word as the construct.
    const Token &First = Tok.is(tok::coloncolon) ? NextToken() : Tok;
    if (Spelled && N == (Tok.is(tok::coloncolon) ? 3u : 2u) &&
        First.getIdentifierInfo()->isStr("cppverify") &&
        !Actions.LookupSingleName(getCurScope(), First.getIdentifierInfo(),
                                  First.getLocation(),
                                  Sema::LookupNestedNameSpecifierName)) {
      if (!DiagnosedMissingCppVerifyHeader) {
        DiagnosedMissingCppVerifyHeader = true;
        Diag(First, diag::err_cppverify_header_missing)
            << Last.getIdentifierInfo()->getName();
      }
      SourceLocation WordLoc = Last.getLocation();
      while (Tok.getLocation() != WordLoc)
        ConsumeAnyToken();
      Tok.setKind(tok::annot_cppverify);
      Tok.setAnnotationValue(new (Ctx) CppVerifyAnnotation{*Spelled, nullptr});
      Tok.setAnnotationEndLoc(WordLoc);
      Tok.setLocation(Start);
      PP.AnnotateCachedTokens(Tok);
      return true;
    }
    if (TryAnnotateCXXScopeToken() || Tok.isNot(tok::annot_cxxscope))
      return false;
  }
  // The name after the scope, possibly already resolved by Clang's name
  // classification during disambiguation.
  const Token &Next = NextToken();
  IdentifierInfo *Word = nullptr;
  ValueDecl *Declared = nullptr;
  if (Next.is(tok::identifier)) {
    Word = Next.getIdentifierInfo();
  } else if (Next.is(tok::annot_non_type)) {
    if (NamedDecl *ND = getNonTypeAnnotation(Next)) {
      Word = ND->getIdentifier();
      Declared = dyn_cast<ValueDecl>(ND);
    }
  } else if (Next.is(tok::annot_overload_set)) {
    if (auto *OE =
            dyn_cast_or_null<OverloadExpr>(getExprAnnotation(Next).get()))
      Word = OE->getName().getAsIdentifierInfo();
  }
  if (!Word)
    return false;
  CXXScopeSpec SS;
  Actions.RestoreNestedNameSpecifierAnnotation(Tok.getAnnotationValue(),
                                               Tok.getAnnotationRange(), SS);
  const NamespaceDecl *NS = cppVerifyNamespaceOf(SS);
  if (!NS)
    return false;
  std::optional<CppVerifyConstruct> C =
      lookupCppVerifyConstruct(Word->getName());
  if (!C) {
    // After a declarator nothing but a clause may follow.
    if (!(Position & CppVerifyPosition::FunctionClause))
      return false;
    StringRef Best;
    unsigned BestDistance = 3;
#define CPPVERIFY_CONSTRUCT(Name, Spelling, Positions)                         \
  if (unsigned Distance = Word->getName().edit_distance(Spelling);             \
      Distance < BestDistance &&                                               \
      (getCppVerifyPositions(CppVerifyConstruct::Name) &                       \
       CppVerifyPosition::FunctionClause)) {                                   \
    BestDistance = Distance;                                                   \
    Best = Spelling;                                                           \
  }
#include "clang/Basic/CppVerifyConstructs.def"
    SourceLocation WordLoc = NextToken().getLocation();
    if (Best.empty())
      Diag(WordLoc, diag::err_cppverify_unknown) << Word->getName();
    else
      Diag(WordLoc, diag::err_cppverify_unknown_suggest)
          << Word->getName() << Best
          << FixItHint::CreateReplacement(WordLoc, Best);
    ConsumeAnnotationToken();
    ConsumeAnyToken();
    if (Tok.is(tok::l_paren)) {
      BalancedDelimiterTracker T(*this, tok::l_paren);
      T.consumeOpen();
      T.skipToEnd();
    }
    return tryAnnotateCppVerify(Position);
  }

  ConsumeAnnotationToken();
  SourceLocation WordLoc = Tok.getLocation();
  Expr *Reference = nullptr;
  if (!Declared) {
    LookupResult R(Actions, Word, WordLoc, Sema::LookupOrdinaryName);
    Actions.LookupQualifiedName(R, const_cast<NamespaceDecl *>(NS));
    Declared = R.getAsSingle<ValueDecl>();
  }
  if (ValueDecl *VD = Declared)
    Reference = DeclRefExpr::Create(
        Ctx, SS.getWithLocInContext(Ctx), SourceLocation(), VD,
        /*RefersToEnclosingVariableOrCapture=*/false, WordLoc, VD->getType(),
        isa<EnumConstantDecl>(VD) ? VK_PRValue : VK_LValue);
  Tok.setKind(tok::annot_cppverify);
  Tok.setAnnotationValue(new (Ctx) CppVerifyAnnotation{*C, Reference});
  Tok.setAnnotationEndLoc(WordLoc);
  Tok.setLocation(Start);
  PP.AnnotateCachedTokens(Tok);
  return true;
}

SourceLocation Parser::ConsumeCppVerify() {
  auto *A = static_cast<CppVerifyAnnotation *>(Tok.getAnnotationValue());
  if (A->Reference && !A->Recorded) {
    A->Recorded = true;
    if (FunctionDecl *FD = Actions.getCurFunctionDecl())
      Actions.getASTContext().addCppVerifyReference(FD, A->Reference);
    else
      PendingCppVerifyReferences.push_back(A->Reference);
  }
  return ConsumeAnnotationToken();
}

/// Moves the pending references written since \p D began to it; the clauses
/// are parsed before its range covers them.
static void takePendingReferences(ASTContext &Ctx, Decl *D,
                                  SmallVectorImpl<Expr *> &Pending) {
  if (D && D->getBeginLoc().isValid()) {
    const SourceManager &SM = Ctx.getSourceManager();
    for (Expr *Ref : Pending)
      if (!SM.isBeforeInTranslationUnit(Ref->getBeginLoc(), D->getBeginLoc()))
        Ctx.addCppVerifyReference(D, Ref);
  }
  Pending.clear();
}

void Parser::diagnoseMisplacedCppVerify() {
  CppVerifyConstruct C = getCppVerifyConstruct(Tok);
  Diag(Tok, diag::err_cppverify_misplaced)
      << getCppVerifySpelling(C) << homeOf(C)
      << SourceRange(Tok.getLocation(), Tok.getAnnotationEndLoc());
  ConsumeCppVerify();
  if (Tok.isOneOf(tok::l_paren, tok::l_brace)) {
    BalancedDelimiterTracker T(*this, Tok.getKind());
    T.consumeOpen();
    T.skipToEnd();
  }
}

//===----------------------------------------------------------------------===//
// Function clauses
//===----------------------------------------------------------------------===//

bool Parser::isFunctionContractClause() {
  // Anything written cppverify:: after a declarator is parsed as a clause;
  // a construct of another kind is diagnosed there.
  return tryAnnotateCppVerify(CppVerifyPosition::FunctionClause);
}

void Parser::ParseFunctionContractClauses(ParsingDeclarator &D,
                                          FunctionContractClauses &Clauses) {
  FunctionContractInfo &I = Clauses.Info;
  // Detect spec/proof from DeclSpec bits set during declaration parsing.
  const bool IsSpecFn = D.getDeclSpec().isSpecFunctionSpecified();
  const bool IsProofFn = D.getDeclSpec().isProofFunctionSpecified();
  I.IsSpec = IsSpecFn;
  I.IsProof = IsProofFn;
  PendingClauseProofs.clear();
  if (!D.isFunctionDeclarator() || !isFunctionContractClause())
    return;

  // Re-enter function parameters into scope so contract conditions can
  // reference them. This mirrors ParseTrailingRequiresClause in
  // ParseDeclCXX.cpp: create a FunctionPrototypeScope and push params.
  ParseScope ContractParamScope(this, Scope::DeclScope |
                                          Scope::FunctionDeclarationScope |
                                          Scope::FunctionPrototypeScope);
  Actions.ActOnStartTrailingRequiresClause(getCurScope(), D);

  // Compute the return type from the full Declarator (not just the DeclSpec)
  // so that result in postconditions gets the correct type: pointers,
  // references, typedefs, trailing return types, and struct returns.
  {
    TypeSourceInfo *TSI = Actions.GetTypeForDeclarator(D);
    QualType FullType = TSI->getType();
    if (const auto *FT = FullType->getAs<FunctionType>())
      CurrentContractReturnType = FT->getReturnType();
    else
      CurrentContractReturnType = Actions.getASTContext().IntTy;
  }

  llvm::SaveAndRestore<unsigned> ContextRAII(CppVerifyContextDepth,
                                             CppVerifyContextDepth + 1);
  // ACSL behaviors: pre and post clauses after behavior(name, assumes)
  // belong to it; complete_behaviors and disjoint_behaviors relate the
  // assumptions of all, or of the named, behaviors.
  struct Behavior {
    IdentifierInfo *Name;
    Expr *Assumes;
  };
  SmallVector<Behavior, 2> Behaviors;
  struct BehaviorRelation {
    bool Complete;
    SourceLocation Loc;
    SmallVector<std::pair<IdentifierInfo *, SourceLocation>, 2> Names;
  };
  SmallVector<BehaviorRelation, 1> BehaviorRelations;
  auto implies = [&](Expr *Condition, Expr *Consequence) -> ExprResult {
    SourceLocation Loc = Consequence->getBeginLoc();
    ExprResult Negated =
        Actions.ActOnUnaryOp(getCurScope(), Loc, tok::exclaim, Condition);
    if (Negated.isInvalid())
      return ExprError();
    return finishCppVerifyExpression(
        Actions.ActOnContractCondition(Actions.ActOnBinOp(
            getCurScope(), Loc, tok::pipepipe, Negated.get(), Consequence)));
  };
  while (isFunctionContractClause()) {
    const CppVerifyConstruct C = getCppVerifyConstruct(Tok);
    if (!(getCppVerifyPositions(C) & CppVerifyPosition::FunctionClause)) {
      diagnoseMisplacedCppVerify();
      continue;
    }
    if (C == CppVerifyConstruct::Inductive) {
      I.Inductive = ConsumeCppVerify();
      if (!IsSpecFn)
        Diag(I.Inductive, diag::err_contract_inductive_not_spec);
      continue;
    }
    if (C == CppVerifyConstruct::Behavior ||
        C == CppVerifyConstruct::CompleteBehaviors ||
        C == CppVerifyConstruct::DisjointBehaviors) {
      SourceLocation ClauseLoc = ConsumeCppVerify();
      if (IsSpecFn)
        Diag(ClauseLoc, diag::err_contract_behavior_on_spec);
      if (C == CppVerifyConstruct::Behavior) {
        BalancedDelimiterTracker T(*this, tok::l_paren);
        if (T.expectAndConsume())
          continue;
        if (Tok.isNot(tok::identifier) ||
            !NextToken().isOneOf(tok::comma, tok::r_paren)) {
          Diag(Tok, diag::err_contract_behavior_name);
          T.skipToEnd();
          continue;
        }
        IdentifierInfo *Name = Tok.getIdentifierInfo();
        SourceLocation NameLoc = ConsumeToken();
        for (const Behavior &Other : Behaviors)
          if (Other.Name == Name)
            Diag(NameLoc, diag::err_contract_behavior_redefined) << Name;
        Expr *Assumes = nullptr;
        if (TryConsumeToken(tok::comma)) {
          ExprResult E = finishCppVerifyExpression(
              Actions.ActOnContractCondition(ParseExpression()));
          if (!E.isInvalid())
            Assumes = E.get();
        } else {
          Assumes = Actions.ActOnCXXBoolLiteral(NameLoc, tok::kw_true).get();
        }
        T.consumeClose();
        if (Assumes) {
          Behaviors.push_back({Name, Assumes});
          I.Behaviors.push_back({Name, Assumes});
        }
        continue;
      }
      BehaviorRelation Relation{
          C == CppVerifyConstruct::CompleteBehaviors, ClauseLoc, {}};
      if (Tok.is(tok::l_paren)) {
        BalancedDelimiterTracker T(*this, tok::l_paren);
        T.consumeOpen();
        while (Tok.is(tok::identifier)) {
          Relation.Names.push_back(
              {Tok.getIdentifierInfo(), Tok.getLocation()});
          ConsumeToken();
          if (!TryConsumeToken(tok::comma))
            break;
        }
        T.consumeClose();
      }
      BehaviorRelations.push_back(std::move(Relation));
      continue;
    }
    const bool IsPre = C == CppVerifyConstruct::Pre;
    const bool IsPost = C == CppVerifyConstruct::Post;
    const bool IsDecreases = C == CppVerifyConstruct::Decreases;
    const bool IsModifies = C == CppVerifyConstruct::Modifies;
    const bool IsAliases = C == CppVerifyConstruct::Aliases;
    const bool IsRecommends = C == CppVerifyConstruct::Recommends;
    const bool IsReads = C == CppVerifyConstruct::Reads;
    const bool IsWhen = C == CppVerifyConstruct::When;
    const std::string ClauseName =
        ("cppverify::" + getCppVerifySpelling(C)).str();
    ConsumeCppVerify();

    if (Tok.isNot(tok::l_paren)) {
      Diag(Tok, diag::err_contract_expected_lparen) << ClauseName;
      break;
    }
    ConsumeParen();

    llvm::SaveAndRestore<bool> InPost(InContractPostcondition, IsPost);
    if (IsModifies) {
      ParseContractFootprints(I.Modifies);
    } else if (IsReads || IsAliases) {
      // reads(pointer, count): the cells pointer[0..count); aliases(p, q).
      ExprResult First = finishCppVerifyExpression(ParseAssignmentExpression());
      if (First.isInvalid() || Tok.isNot(tok::comma)) {
        if (!First.isInvalid())
          Diag(Tok, diag::err_contract_expected_comma) << ClauseName;
      } else {
        ConsumeToken();
        ExprResult Second =
            finishCppVerifyExpression(ParseAssignmentExpression());
        if (!Second.isInvalid() && IsReads)
          I.Reads.push_back(std::make_pair(First.get(), Second.get()));
        else if (!Second.isInvalid())
          I.Aliases.push_back(std::make_pair(First.get(), Second.get()));
      }
    } else if (IsDecreases && Tok.is(tok::star) &&
               NextToken().is(tok::r_paren)) {
      I.MayDiverge = ConsumeToken();
      if (IsSpecFn || IsProofFn)
        Diag(I.MayDiverge, diag::err_contract_decreases_star_must_terminate)
            << (IsSpecFn ? 0 : 1);
      else if (!I.Decreases.empty())
        Diag(I.MayDiverge, diag::err_contract_decreases_star_with_measure);
    } else if (IsDecreases) {
      if (I.MayDiverge.isValid())
        Diag(Tok, diag::err_contract_decreases_star_with_measure);
      // Lexicographic termination measure: a comma-separated tuple of integer
      // expressions. Parse each with ParseAssignmentExpression so the comma is
      // a tuple separator, not the C comma operator.
      do {
        ExprResult E = finishCppVerifyExpression(ParseAssignmentExpression());
        if (E.isInvalid())
          break;
        if (!E.get()->getType()->isIntegerType())
          Diag(E.get()->getExprLoc(), diag::err_contract_decreases_not_int);
        else
          I.Decreases.push_back(E.get());
        if (Tok.is(tok::comma))
          ConsumeToken();
        else
          break;
      } while (Tok.isNot(tok::r_paren));
    } else {
      ExprResult E = ParseExpression();
      if (!E.isInvalid() && (IsPre || IsPost || IsRecommends || IsWhen)) {
        E = finishCppVerifyExpression(Actions.ActOnContractCondition(E));
        if (!E.isInvalid() && (IsPre || IsPost) && !Behaviors.empty()) {
          Expr *Assumes = Behaviors.back().Assumes;
          if (IsPost)
            Assumes = new (Actions.getASTContext())
                OldExpr(Assumes->getBeginLoc(), Assumes->getBeginLoc(),
                        Assumes->getEndLoc(), Assumes);
          E = implies(Assumes, E.get());
        }
        if (!E.isInvalid() && IsPre)
          I.Preconditions.push_back(E.get());
        else if (!E.isInvalid() && IsPost)
          I.Postconditions.push_back(E.get());
        else if (IsWhen)
          I.When.push_back(E.get());
        else
          I.Recommends.push_back(E.get());
      }
    }

    if (!Tok.is(tok::r_paren)) {
      unsigned Depth = 0;
      while (Tok.isNot(tok::eof)) {
        if (Tok.is(tok::l_paren))
          ++Depth;
        else if (Tok.is(tok::r_paren)) {
          if (Depth == 0)
            break;
          --Depth;
        }
        // ConsumeAnyToken: the recovery stream may contain annotation/special
        // tokens, which ConsumeToken() asserts against.
        ConsumeAnyToken();
      }
    }
    if (Tok.is(tok::r_paren))
      ConsumeParen();
    else
      Diag(Tok, diag::err_contract_expected_rparen) << ClauseName;

    // clause(...) by { proof }: `by` is contextual. The block is parsed
    // once the definition's parameters are in scope.
    if (Tok.is(tok::identifier) && Tok.getIdentifierInfo()->isStr("by") &&
        NextToken().is(tok::l_brace)) {
      PendingClauseProof Proof;
      Proof.Loc = ConsumeToken();
      Proof.K = IsPost        ? FunctionContractInfo::ClauseProof::Post
                : IsDecreases ? FunctionContractInfo::ClauseProof::Decreases
                              : FunctionContractInfo::ClauseProof::Reads;
      Proof.Toks.push_back(Tok);
      ConsumeBrace();
      ConsumeAndStoreUntil(tok::r_brace, Proof.Toks, /*StopAtSemi=*/false,
                           /*ConsumeFinalToken=*/true);
      if (!IsSpecFn || !(IsPost || IsDecreases || IsReads))
        Diag(Proof.Loc, diag::err_contract_clause_proof_misplaced);
      else
        PendingClauseProofs.push_back(std::move(Proof));
    }
  }

  for (const BehaviorRelation &Relation : BehaviorRelations) {
    SmallVector<Expr *, 2> Assumptions;
    if (Relation.Names.empty())
      for (const Behavior &B : Behaviors)
        Assumptions.push_back(B.Assumes);
    for (const auto &[Name, NameLoc] : Relation.Names) {
      auto It = llvm::find_if(Behaviors, [Name = Name](const Behavior &B) {
        return B.Name == Name;
      });
      if (It == Behaviors.end())
        Diag(NameLoc, diag::err_contract_behavior_unknown) << Name;
      else
        Assumptions.push_back(It->Assumes);
    }
    if (Assumptions.size() < (Relation.Complete ? 1u : 2u)) {
      Diag(Relation.Loc, diag::err_contract_behavior_relation_empty)
          << Relation.Complete;
      continue;
    }
    // complete: some behavior applies; disjoint: no two apply together.
    ExprResult Check;
    if (Relation.Complete) {
      Check = Assumptions.front();
      for (size_t J = 1; J < Assumptions.size(); ++J)
        Check = Actions.ActOnBinOp(getCurScope(), Relation.Loc, tok::pipepipe,
                                   Check.get(), Assumptions[J]);
    } else {
      for (size_t J = 0; J < Assumptions.size(); ++J)
        for (size_t K = J + 1; K < Assumptions.size(); ++K) {
          ExprResult Both =
              Actions.ActOnBinOp(getCurScope(), Relation.Loc, tok::ampamp,
                                 Assumptions[J], Assumptions[K]);
          ExprResult Apart = Actions.ActOnUnaryOp(getCurScope(), Relation.Loc,
                                                  tok::exclaim, Both.get());
          Check =
              Check.isUsable()
                  ? Actions.ActOnBinOp(getCurScope(), Relation.Loc, tok::ampamp,
                                       Check.get(), Apart.get())
                  : Apart;
        }
    }
    Check = finishCppVerifyExpression(Actions.ActOnContractCondition(Check));
    if (Check.isUsable())
      I.BehaviorChecks.push_back(Check.get());
  }
}

void Parser::attachFunctionContract(Decl *Result,
                                    FunctionContractClauses &Clauses) {
  CurrentContractReturnType = QualType();
  ASTContext &Ctx = Actions.getASTContext();
  FunctionDecl *FD = Result ? Result->getAsFunction() : nullptr;
  takePendingReferences(Ctx, FD, PendingCppVerifyReferences);
  FunctionContractInfo &I = Clauses.Info;
  if (!FD || (I.Preconditions.empty() && I.Postconditions.empty() &&
              I.Modifies.empty() && I.Aliases.empty() && I.Recommends.empty() &&
              I.Reads.empty() && I.When.empty() && I.Decreases.empty() &&
              I.MayDiverge.isInvalid() && I.Inductive.isInvalid() &&
              I.BehaviorChecks.empty() && !I.IsSpec && !I.IsProof))
    return;
  FunctionContractInfo &FCI = Ctx.getOrCreateFunctionContract(FD);
  if (FCI.ContractDecl && FCI.ContractDecl != FD) {
    Diag(FD->getLocation(), diag::err_contract_redeclaration);
    return;
  }
  FCI.ContractDecl = FD;
  FCI.Preconditions = std::move(I.Preconditions);
  FCI.Postconditions = std::move(I.Postconditions);
  FCI.Modifies = std::move(I.Modifies);
  FCI.Aliases = std::move(I.Aliases);
  FCI.Recommends = std::move(I.Recommends);
  FCI.Reads = std::move(I.Reads);
  FCI.When = std::move(I.When);
  FCI.Decreases = std::move(I.Decreases);
  FCI.MayDiverge = I.MayDiverge;
  FCI.Inductive = I.Inductive;
  FCI.BehaviorChecks = std::move(I.BehaviorChecks);
  FCI.Behaviors = std::move(I.Behaviors);
  FCI.IsSpec = I.IsSpec;
  FCI.IsProof = I.IsProof;
  CurrentContractFunction = Result;
}

Decl *Parser::ParseContractedFunctionDeclaration(
    ParsingDeclarator &D, const ParsedTemplateInfo &TemplateInfo,
    FunctionContractClauses &Clauses) {
  // The canonical contract side table lets a later definition inherit the
  // clauses.
  Decl *Res = ParseDeclarationAfterDeclaratorAndAttributes(D, TemplateInfo);
  D.complete(Res);
  attachFunctionContract(Res, Clauses);
  if (!PendingClauseProofs.empty()) {
    Diag(PendingClauseProofs.front().Loc,
         diag::err_contract_clause_proof_on_declaration);
    PendingClauseProofs.clear();
  }
  D.getMutableDeclSpec().abort();
  ConsumeToken();
  return Res;
}

void Parser::ParseContractClauseProofs(Decl *Function) {
  SmallVector<PendingClauseProof, 1> Proofs = std::move(PendingClauseProofs);
  PendingClauseProofs.clear();
  auto *FD = Function ? Function->getAsFunction() : nullptr;
  llvm::SaveAndRestore<unsigned> ContextRAII(CppVerifyContextDepth,
                                             CppVerifyContextDepth + 1);
  for (PendingClauseProof &Proof : Proofs) {
    Token End;
    End.startToken();
    End.setKind(tok::eof);
    End.setLocation(Proof.Toks.back().getEndLoc());
    End.setEofData(&Proof);
    Proof.Toks.push_back(End);
    // Keep the token that follows, the start of the body.
    Proof.Toks.push_back(Tok);
    PP.EnterTokenStream(Proof.Toks, /*DisableMacroExpansion=*/true,
                        /*IsReinject=*/true);
    ConsumeAnyToken(/*ConsumeCodeCompletionTok=*/true);
    StmtResult Body;
    {
      llvm::SaveAndRestore<bool> InPost(
          InContractPostcondition,
          Proof.K == FunctionContractInfo::ClauseProof::Post);
      Body = ParseCompoundStatement();
    }
    while (Tok.isNot(tok::eof))
      ConsumeAnyToken();
    if (Tok.getEofData() == &Proof)
      ConsumeAnyToken();
    if (FD && Body.isUsable())
      Actions.getASTContext()
          .getOrCreateFunctionContract(FD)
          .ClauseProofs.push_back({Proof.K, Body.get(), Proof.Loc});
  }
}

//===----------------------------------------------------------------------===//
// Loop and class clauses
//===----------------------------------------------------------------------===//

void Parser::ParseContractFootprints(SmallVectorImpl<Expr *> &Footprints) {
  llvm::SaveAndRestore<bool> FootprintRAII(InContractFootprint, true);
  do {
    ExprResult E = finishCppVerifyExpression(ParseAssignmentExpression());
    if (E.isInvalid())
      break;
    Footprints.push_back(E.get());
    if (Tok.is(tok::comma))
      ConsumeToken();
    else
      break;
  } while (Tok.isNot(tok::r_paren));
}

/// Parse loop contract clauses: invariant(expr), decreases(expr), and
/// modifies(footprints), after the loop head and before its body.
void Parser::ParseLoopContractClauses(LoopContractInfo &Contract) {
  llvm::SaveAndRestore<unsigned> ContextRAII(CppVerifyContextDepth,
                                             CppVerifyContextDepth + 1);
  while (tryAnnotateCppVerify(CppVerifyPosition::LoopClause) &&
         (isCppVerify(CppVerifyConstruct::Invariant) ||
          isCppVerify(CppVerifyConstruct::Decreases) ||
          isCppVerify(CppVerifyConstruct::Modifies))) {
    const bool IsInvariant = isCppVerify(CppVerifyConstruct::Invariant);
    const bool IsModifies = isCppVerify(CppVerifyConstruct::Modifies);
    const char *ClauseName = IsInvariant  ? "cppverify::invariant"
                             : IsModifies ? "cppverify::modifies"
                                          : "cppverify::decreases";
    ConsumeCppVerify();

    if (Tok.isNot(tok::l_paren)) {
      Diag(Tok, diag::err_contract_expected_lparen) << ClauseName;
      return;
    }
    ConsumeParen();

    if (IsModifies) {
      // Footprints are read in each iteration's state; old(...) denotes
      // function entry, as in an invariant.
      llvm::SaveAndRestore<bool> LoopInvariantRAII(InLoopContractInvariant,
                                                   true);
      ParseContractFootprints(Contract.Modifies);
    } else if (IsInvariant) {
      llvm::SaveAndRestore<bool> LoopInvariantRAII(InLoopContractInvariant,
                                                   true);
      ExprResult E = ParseExpression();
      if (E.isInvalid()) {
        SkipUntil(tok::r_paren, StopAtSemi);
        return;
      }
      E = finishCppVerifyExpression(Actions.ActOnContractCondition(E));
      if (E.isInvalid()) {
        SkipUntil(tok::r_paren, StopAtSemi);
        return;
      }
      Contract.Invariants.push_back(E.get());
    } else if (Tok.is(tok::star) && NextToken().is(tok::r_paren)) {
      Contract.MayDiverge = ConsumeToken();
      if (!Contract.Decreases.empty())
        Diag(Contract.MayDiverge,
             diag::err_contract_decreases_star_with_measure);
    } else {
      if (Contract.MayDiverge.isValid())
        Diag(Tok, diag::err_contract_decreases_star_with_measure);
      // decreases: a comma-separated lexicographic tuple of integer measures.
      // Parse each component with ParseAssignmentExpression so the comma is a
      // tuple separator, not the C comma operator.
      while (true) {
        ExprResult D = finishCppVerifyExpression(ParseAssignmentExpression());
        if (D.isInvalid()) {
          SkipUntil(tok::r_paren, StopAtSemi);
          return;
        }
        if (!D.get()->getType()->isIntegerType()) {
          Diag(D.get()->getExprLoc(), diag::err_contract_decreases_not_int);
          SkipUntil(tok::r_paren, StopAtSemi);
          return;
        }
        Contract.Decreases.push_back(D.get());
        if (Tok.isNot(tok::comma))
          break;
        ConsumeToken(); // eat ','
      }
    }

    if (Tok.isNot(tok::r_paren)) {
      Diag(Tok, diag::err_contract_expected_rparen) << ClauseName;
      SkipUntil(tok::r_paren, StopAtSemi);
      return;
    }
    ConsumeParen();
  }
}

void Parser::attachLoopContract(StmtResult &Loop, LoopContractInfo &Contract) {
  if (Loop.isUsable() &&
      (!Contract.Invariants.empty() || !Contract.Decreases.empty() ||
       Contract.MayDiverge.isValid() || !Contract.Modifies.empty()))
    Actions.getASTContext().getOrCreateLoopContract(Loop.get()) =
        std::move(Contract);
}

/// Parse cppverify::type_invariant(expr); inside a class or struct body.
void Parser::ParseTypeInvariant(Decl *TagDecl) {
  assert(isCppVerify(CppVerifyConstruct::TypeInvariant));
  auto *RD = dyn_cast<CXXRecordDecl>(TagDecl);
  ConsumeCppVerify();
  auto Finish = [&] {
    takePendingReferences(Actions.getASTContext(), RD,
                          PendingCppVerifyReferences);
  };
  if (!RD) {
    SkipUntil(tok::semi, StopAtSemi);
    if (Tok.is(tok::semi))
      ConsumeToken();
    return Finish();
  }
  if (Tok.isNot(tok::l_paren)) {
    Diag(Tok, diag::err_contract_expected_lparen)
        << "cppverify::type_invariant";
    SkipUntil(tok::semi, StopAtSemi);
    if (Tok.is(tok::semi))
      ConsumeToken();
    return Finish();
  }
  ConsumeParen();
  llvm::SaveAndRestore<unsigned> ContextRAII(CppVerifyContextDepth,
                                             CppVerifyContextDepth + 1);
  Sema::CXXThisScopeRAII ThisScope(Actions, RD, Qualifiers(), true);
  Actions.PushExpressionEvaluationContext(
      Sema::ExpressionEvaluationContext::Unevaluated);
  ExprResult E = ParseExpression();
  Actions.PopExpressionEvaluationContext();
  if (Tok.isNot(tok::r_paren)) {
    Diag(Tok, diag::err_expected) << tok::r_paren;
    SkipUntil(tok::semi, StopAtSemi);
    if (Tok.is(tok::semi))
      ConsumeToken();
    return Finish();
  }
  ConsumeParen();
  if (!E.isInvalid()) {
    E = Actions.ActOnTypeInvariantExpr(E, RD);
    if (!E.isInvalid())
      Actions.getASTContext().getOrCreateTypeContract(RD).Invariants.push_back(
          E.get());
  }
  if (Tok.isNot(tok::semi))
    Diag(Tok, diag::err_expected) << tok::semi;
  else
    ConsumeToken();
  Finish();
}

bool Parser::ParseCppVerifySpecifier(DeclSpec &DS, bool &IsInvalid,
                                     const char *&PrevSpec, unsigned &DiagID,
                                     SourceLocation &ConsumedEnd) {
  const CppVerifyConstruct C = getCppVerifyConstruct(Tok);
  if (C != CppVerifyConstruct::Spec && C != CppVerifyConstruct::Proof) {
    // After other specifiers it ends them, as a clause after a trailing
    // return type does; first, it starts no declaration.
    if (DS.isEmpty()) {
      diagnoseMisplacedCppVerify();
      DS.SetTypeSpecError();
    }
    return false;
  }
  // Also mark inline so Clang's normal function machinery works; the
  // dedicated spec and proof bits preserve the original intent.
  SourceLocation Loc = Tok.getLocation();
  ConsumedEnd = Tok.getAnnotationEndLoc();
  IsInvalid = DS.setFunctionSpecInline(Loc, PrevSpec, DiagID);
  if (!IsInvalid) {
    DS.SetRangeStart(Loc);
    if (C == CppVerifyConstruct::Spec)
      DS.setSpecFunctionSpec();
    else
      DS.setProofFunctionSpec();
  }
  ConsumeCppVerify();
  return true;
}

//===----------------------------------------------------------------------===//
// Statements
//===----------------------------------------------------------------------===//

StmtResult Parser::ParseCppVerifyStatement(const char *&SemiError) {
  switch (getCppVerifyConstruct(Tok)) {
  case CppVerifyConstruct::Ghost:
    return ParseGhostBlock();
  case CppVerifyConstruct::Calc:
    return ParseCalcStatement();
  case CppVerifyConstruct::Check: {
    StmtResult Res = ParseContractAssert();
    // A proof block ends the statement, like a compound statement.
    if (!Res.isUsable() || !cast<ContractAssertStmt>(Res.get())->getBy())
      SemiError = "cppverify::check";
    return Res;
  }
  case CppVerifyConstruct::RevealWithFuel:
    SemiError = "cppverify::reveal_with_fuel";
    return ParseRevealWithFuel();
  case CppVerifyConstruct::Hide:
    SemiError = "cppverify::hide";
    return ParseHideSpec();
  case CppVerifyConstruct::Reveal:
    SemiError = "cppverify::reveal";
    return ParseRevealSpec();
  default:
    diagnoseMisplacedCppVerify();
    SemiError = "";
    return StmtError();
  }
}

StmtResult Parser::ParseCalcStatement() {
  SourceLocation CalcLoc = ConsumeCppVerify();
  BalancedDelimiterTracker Braces(*this, tok::l_brace);
  if (Braces.expectAndConsume())
    return StmtError();
  llvm::SaveAndRestore<unsigned> ContextRAII(CppVerifyContextDepth,
                                             CppVerifyContextDepth + 1);
  auto term = [&]() -> Expr * {
    ExprResult E = finishCppVerifyExpression(ParseExpression());
    if (E.isInvalid() || ExpectAndConsume(tok::semi)) {
      SkipUntil(tok::r_brace, StopBeforeMatch);
      return nullptr;
    }
    return E.get();
  };
  Expr *First = term();
  if (!First) {
    Braces.consumeClose();
    return StmtError();
  }
  Expr *Previous = First;
  StmtVector Steps;
  bool Increasing = false, Decreasing = false, Strict = false;
  while (Tok.isOneOf(tok::equalequal, tok::lessequal, tok::less,
                     tok::greaterequal, tok::greater)) {
    const tok::TokenKind Op = Tok.getKind();
    SourceLocation OpLoc = ConsumeToken();
    Stmt *Proof = nullptr;
    if (Tok.is(tok::l_brace)) {
      StmtResult Body = ParseCompoundStatement();
      if (Body.isInvalid()) {
        SkipUntil(tok::r_brace, StopBeforeMatch);
        break;
      }
      Proof = new (Actions.getASTContext()) GhostBlockStmt(OpLoc, Body.get());
    }
    Expr *Next = term();
    if (!Next)
      break;
    ExprResult Step = finishCppVerifyExpression(Actions.ActOnContractCondition(
        Actions.ActOnBinOp(getCurScope(), OpLoc, Op, Previous, Next)));
    if (Step.isInvalid())
      break;
    Steps.push_back(new (Actions.getASTContext()) ContractAssertStmt(
        OpLoc, OpLoc, Next->getEndLoc(), Step.get(), Proof));
    Increasing |= Op == tok::lessequal || Op == tok::less;
    Decreasing |= Op == tok::greaterequal || Op == tok::greater;
    Strict |= Op == tok::less || Op == tok::greater;
    Previous = Next;
  }
  if (Braces.consumeClose())
    return StmtError();
  if (Steps.empty()) {
    Diag(CalcLoc, diag::err_calc_no_steps);
    return StmtError();
  }
  if (Increasing && Decreasing) {
    Diag(CalcLoc, diag::err_calc_mixed_directions);
    return StmtError();
  }
  // Each step is proved, with its proof's facts kept local, and the chain
  // proves only First R Last.
  const tok::TokenKind Relation =
      Increasing   ? (Strict ? tok::less : tok::lessequal)
      : Decreasing ? (Strict ? tok::greater : tok::greaterequal)
                   : tok::equalequal;
  ExprResult Conclusion = finishCppVerifyExpression(
      Actions.ActOnContractCondition(Actions.ActOnBinOp(
          getCurScope(), CalcLoc, Relation, First, Previous)));
  if (Conclusion.isInvalid())
    return StmtError();
  SourceLocation EndLoc = Braces.getCloseLocation();
  CompoundStmt *Body = CompoundStmt::Create(
      Actions.getASTContext(), Steps, FPOptionsOverride(), CalcLoc, EndLoc);
  Stmt *By = new (Actions.getASTContext()) GhostBlockStmt(CalcLoc, Body);
  return new (Actions.getASTContext())
      ContractAssertStmt(CalcLoc, CalcLoc, EndLoc, Conclusion.get(), By);
}

/// Parse cppverify::ghost { ... } and cppverify::ghost T x = e;
StmtResult Parser::ParseGhostBlock() {
  SourceLocation GhostLoc = ConsumeCppVerify();
  llvm::SaveAndRestore<unsigned> ContextRAII(CppVerifyContextDepth,
                                             CppVerifyContextDepth + 1);

  // A ghost declaration declares function-scoped ghost variables: the
  // declaration joins the enclosing scope, and the statement is erased.
  if (Tok.isNot(tok::l_brace) && isDeclarationStatement()) {
    StmtVector Stmts;
    StmtResult Declaration =
        ParseStatementOrDeclaration(Stmts, ParsedStmtContext::Compound);
    if (Declaration.isInvalid())
      return StmtError();
    auto *DS = dyn_cast<DeclStmt>(Declaration.get());
    if (!DS || llvm::any_of(DS->decls(),
                            [](const Decl *D) { return !isa<VarDecl>(D); })) {
      Diag(GhostLoc, diag::err_ghost_declaration_not_variable);
      return StmtError();
    }
    for (Decl *D : DS->decls())
      Actions.getASTContext().markGhostVariable(cast<VarDecl>(D));
    CompoundStmt *Body =
        CompoundStmt::Create(Actions.getASTContext(), {DS}, FPOptionsOverride(),
                             DS->getBeginLoc(), DS->getEndLoc());
    return new (Actions.getASTContext()) GhostBlockStmt(GhostLoc, Body);
  }
  if (Tok.isNot(tok::l_brace)) {
    Diag(Tok, diag::err_contract_expected_body);
    return StmtError();
  }

  StmtResult Body = ParseCompoundStatement();
  if (Body.isInvalid())
    return StmtError();

  return new (Actions.getASTContext()) GhostBlockStmt(GhostLoc, Body.get());
}

/// Parse cppverify::check(expr) [by { proof }]
StmtResult Parser::ParseContractAssert() {
  SourceLocation CALoc = ConsumeCppVerify();
  llvm::SaveAndRestore<unsigned> ContextRAII(CppVerifyContextDepth,
                                             CppVerifyContextDepth + 1);

  if (Tok.isNot(tok::l_paren)) {
    Diag(Tok, diag::err_contract_expected_lparen) << "cppverify::check";
    return StmtError();
  }
  SourceLocation LParenLoc = ConsumeParen();

  ExprResult Cond = ParseExpression();
  if (Cond.isInvalid()) {
    SkipUntil(tok::r_paren, StopAtSemi);
    return StmtError();
  }

  Cond = finishCppVerifyExpression(Actions.ActOnContractCondition(Cond));
  if (Cond.isInvalid()) {
    SkipUntil(tok::r_paren, StopAtSemi);
    return StmtError();
  }

  if (Tok.isNot(tok::r_paren)) {
    Diag(Tok, diag::err_contract_expected_rparen) << "cppverify::check";
    SkipUntil(tok::r_paren, StopAtSemi);
    return StmtError();
  }
  SourceLocation RParenLoc = ConsumeParen();

  // check(e) by { ghost proof }: `by` is contextual.
  Stmt *By = nullptr;
  if (Tok.is(tok::identifier) && Tok.getIdentifierInfo()->isStr("by") &&
      NextToken().is(tok::l_brace)) {
    SourceLocation ByLoc = ConsumeToken();
    // check(forall(k, ...)) by { ... } proves the body for one arbitrary k,
    // so the block sees k.
    ParseScope BinderScope(this, Scope::DeclScope);
    if (const auto *Forall =
            dyn_cast<ForallExpr>(Cond.get()->IgnoreParenImpCasts()))
      if (VarDecl *Binder = Forall->getBoundVar())
        Actions.PushOnScopeChains(Binder, getCurScope(),
                                  /*AddToContext=*/false);
    StmtResult Body = ParseCompoundStatement();
    BinderScope.Exit();
    if (Body.isInvalid())
      return StmtError();
    By = new (Actions.getASTContext()) GhostBlockStmt(ByLoc, Body.get());
  }

  return new (Actions.getASTContext())
      ContractAssertStmt(CALoc, LParenLoc, RParenLoc, Cond.get(), By);
}

/// Parse cppverify::reveal_with_fuel(fn, depth);
StmtResult Parser::ParseRevealWithFuel() {
  SourceLocation Loc = ConsumeCppVerify();

  if (Tok.isNot(tok::l_paren)) {
    Diag(Tok, diag::err_contract_expected_lparen)
        << "cppverify::reveal_with_fuel";
    return StmtError();
  }
  SourceLocation LParenLoc = ConsumeParen();

  ExprResult Fn = finishCppVerifyExpression(ParseAssignmentExpression());
  if (Fn.isInvalid() || Tok.isNot(tok::comma)) {
    if (!Fn.isInvalid())
      Diag(Tok, diag::err_contract_expected_comma)
          << "cppverify::reveal_with_fuel";
    SkipUntil(tok::r_paren, StopAtSemi);
    return StmtError();
  }
  ConsumeToken();

  ExprResult Fuel = finishCppVerifyExpression(ParseExpression());
  if (Fuel.isInvalid()) {
    SkipUntil(tok::r_paren, StopAtSemi);
    return StmtError();
  }

  if (Tok.isNot(tok::r_paren)) {
    Diag(Tok, diag::err_contract_expected_rparen)
        << "cppverify::reveal_with_fuel";
    SkipUntil(tok::r_paren, StopAtSemi);
    return StmtError();
  }
  SourceLocation RParenLoc = ConsumeParen();

  return new (Actions.getASTContext())
      RevealWithFuelStmt(Loc, LParenLoc, RParenLoc, Fn.get(), Fuel.get());
}

/// Parse cppverify::hide(fn);
StmtResult Parser::ParseHideSpec() {
  SourceLocation Loc = ConsumeCppVerify();
  if (Tok.isNot(tok::l_paren)) {
    Diag(Tok, diag::err_contract_expected_lparen) << "cppverify::hide";
    return StmtError();
  }
  SourceLocation LParenLoc = ConsumeParen();
  ExprResult Fn = finishCppVerifyExpression(ParseAssignmentExpression());
  if (Fn.isInvalid()) {
    SkipUntil(tok::r_paren, StopAtSemi);
    return StmtError();
  }
  if (Tok.isNot(tok::r_paren)) {
    Diag(Tok, diag::err_contract_expected_rparen) << "cppverify::hide";
    SkipUntil(tok::r_paren, StopAtSemi);
    return StmtError();
  }
  SourceLocation RParenLoc = ConsumeParen();
  return new (Actions.getASTContext())
      HideSpecStmt(Loc, LParenLoc, RParenLoc, Fn.get());
}

/// Parse cppverify::reveal(fn);
StmtResult Parser::ParseRevealSpec() {
  SourceLocation Loc = ConsumeCppVerify();
  if (Tok.isNot(tok::l_paren)) {
    Diag(Tok, diag::err_contract_expected_lparen) << "cppverify::reveal";
    return StmtError();
  }
  SourceLocation LParenLoc = ConsumeParen();
  ExprResult Fn = finishCppVerifyExpression(ParseAssignmentExpression());
  if (Fn.isInvalid()) {
    SkipUntil(tok::r_paren, StopAtSemi);
    return StmtError();
  }
  if (Tok.isNot(tok::r_paren)) {
    Diag(Tok, diag::err_contract_expected_rparen) << "cppverify::reveal";
    SkipUntil(tok::r_paren, StopAtSemi);
    return StmtError();
  }
  SourceLocation RParenLoc = ConsumeParen();
  return new (Actions.getASTContext())
      RevealSpecStmt(Loc, LParenLoc, RParenLoc, Fn.get());
}

//===----------------------------------------------------------------------===//
// Expressions
//===----------------------------------------------------------------------===//

ExprResult Parser::ParseCppVerifyExpression() {
  switch (getCppVerifyConstruct(Tok)) {
  case CppVerifyConstruct::Forall:
  case CppVerifyConstruct::Exists:
  case CppVerifyConstruct::Choose:
    return ParseQuantifierExpr();
  case CppVerifyConstruct::Old:
    return ParseOldExpr();
  case CppVerifyConstruct::Result:
    return ParseResultExpr();
  case CppVerifyConstruct::Trigger: {
    // trigger(term) in a quantifier body marks term as an instantiation
    // pattern.
    if (QuantifierBodyDepth == 0) {
      Diag(Tok, diag::err_cppverify_trigger_outside_quantifier);
      ConsumeCppVerify();
      if (Tok.is(tok::l_paren)) {
        BalancedDelimiterTracker T(*this, tok::l_paren);
        T.consumeOpen();
        T.skipToEnd();
      }
      return ExprError();
    }
    ConsumeCppVerify();
    BalancedDelimiterTracker T(*this, tok::l_paren);
    if (T.expectAndConsume())
      return ExprError();
    ExprResult Term = ParseExpression();
    if (Term.isInvalid() || T.consumeClose())
      return ExprError();
    Actions.getASTContext().markTriggerTerm(Term.get());
    return Term;
  }
  default:
    diagnoseMisplacedCppVerify();
    return ExprError();
  }
}

/// Parse cppverify::forall(binder, [lo, hi,] body), and the same for exists
/// and choose.
ExprResult Parser::ParseQuantifierExpr() {
  const CppVerifyConstruct C = getCppVerifyConstruct(Tok);
  const bool IsChoose = C == CppVerifyConstruct::Choose;
  const bool IsForall = C == CppVerifyConstruct::Forall;
  const char *Keyword = IsChoose   ? "cppverify::choose"
                        : IsForall ? "cppverify::forall"
                                   : "cppverify::exists";
  SourceLocation KwLoc = ConsumeCppVerify();

  if (Tok.isNot(tok::l_paren)) {
    Diag(Tok, diag::err_contract_expected_lparen) << Keyword;
    return ExprError();
  }
  SourceLocation LParenLoc = ConsumeParen();

  // Parse binder name (an identifier that becomes a fresh int variable).
  if (Tok.isNot(tok::identifier)) {
    Diag(Tok, diag::err_expected) << tok::identifier;
    SkipUntil(tok::r_paren, StopAtSemi);
    return ExprError();
  }
  IdentifierInfo *BinderII = Tok.getIdentifierInfo();
  SourceLocation BinderLoc = ConsumeToken();

  if (ExpectAndConsume(tok::comma)) {
    SkipUntil(tok::r_paren, StopAtSemi);
    return ExprError();
  }

  // forall(k, body) ranges over all integers: one more top-level comma
  // before the closing parenthesis, where the bounded form has three.
  bool Unbounded = false;
  {
    TentativeParsingAction Scan(*this);
    unsigned Depth = 0, Commas = 0;
    while (Tok.isNot(tok::eof) && Tok.isNot(tok::semi)) {
      if (Tok.isOneOf(tok::l_paren, tok::l_square, tok::l_brace))
        ++Depth;
      else if (Tok.isOneOf(tok::r_paren, tok::r_square, tok::r_brace)) {
        if (Depth == 0)
          break;
        --Depth;
      } else if (Tok.is(tok::comma) && Depth == 0)
        ++Commas;
      ConsumeAnyToken();
    }
    Unbounded = Commas == 0;
    Scan.Revert();
  }

  ASTContext &Ctx = Actions.getASTContext();
  ExprResult Lo, Hi;
  if (!Unbounded) {
    Lo = ParseAssignmentExpression();
    if (Lo.isInvalid() || ExpectAndConsume(tok::comma)) {
      SkipUntil(tok::r_paren, StopAtSemi);
      return ExprError();
    }
    Hi = ParseAssignmentExpression();
    if (Hi.isInvalid() || ExpectAndConsume(tok::comma)) {
      SkipUntil(tok::r_paren, StopAtSemi);
      return ExprError();
    }
  }

  // Create the bound variable and push it into scope for the body.
  VarDecl *BoundVar = VarDecl::Create(
      Ctx, Actions.CurContext, BinderLoc, BinderLoc, BinderII, Ctx.IntTy,
      Ctx.getTrivialTypeSourceInfo(Ctx.IntTy, BinderLoc), SC_None);
  ParseScope QuantifierScope(this, Scope::DeclScope);
  Actions.PushOnScopeChains(BoundVar, getCurScope(), /*AddToContext=*/false);
  ++QuantifierBodyDepth;
  ExprResult Body = ParseAssignmentExpression();
  --QuantifierBodyDepth;
  QuantifierScope.Exit();
  if (Body.isInvalid()) {
    SkipUntil(tok::r_paren, StopAtSemi);
    return ExprError();
  }

  // Validate bound types: lo and hi must be integer.
  for (const ExprResult &Bound : {Lo, Hi})
    if (Bound.isUsable() && !Bound.get()->getType()->isIntegerType()) {
      Diag(Bound.get()->getExprLoc(),
           diag::err_contract_quantifier_bound_not_int);
      SkipUntil(tok::r_paren, StopAtSemi);
      return ExprError();
    }

  // Validate body: must be contextually convertible to bool.
  ExprResult BodyBool = Actions.ActOnContractCondition(Body);
  if (BodyBool.isInvalid()) {
    SkipUntil(tok::r_paren, StopAtSemi);
    return ExprError();
  }

  if (Tok.isNot(tok::r_paren)) {
    Diag(Tok, diag::err_contract_expected_rparen) << Keyword;
    SkipUntil(tok::r_paren, StopAtSemi);
    return ExprError();
  }
  SourceLocation RParenLoc = ConsumeParen();

  Expr *LoE = Lo.isUsable() ? Lo.get() : nullptr;
  Expr *HiE = Hi.isUsable() ? Hi.get() : nullptr;
  if (IsChoose)
    return new (Ctx) ContractChooseExpr(KwLoc, LParenLoc, RParenLoc, BoundVar,
                                        LoE, HiE, BodyBool.get(), Ctx.IntTy);
  if (IsForall)
    return new (Ctx) ForallExpr(KwLoc, LParenLoc, RParenLoc, BoundVar, LoE, HiE,
                                BodyBool.get(), Ctx.BoolTy);
  return new (Ctx) ExistsExpr(KwLoc, LParenLoc, RParenLoc, BoundVar, LoE, HiE,
                              BodyBool.get(), Ctx.BoolTy);
}

/// Parse cppverify::old(expr)
ExprResult Parser::ParseOldExpr() {
  SourceLocation OldLoc = ConsumeCppVerify();

  // In a loop invariant, old(...) still denotes the function-entry state.
  if (!InContractPostcondition && !InLoopContractInvariant) {
    Diag(OldLoc, diag::err_old_outside_postcondition);
    if (Tok.is(tok::l_paren)) {
      BalancedDelimiterTracker T(*this, tok::l_paren);
      T.consumeOpen();
      T.skipToEnd();
    }
    return ExprError();
  }

  if (Tok.isNot(tok::l_paren)) {
    Diag(Tok, diag::err_contract_expected_lparen) << "cppverify::old";
    return ExprError();
  }
  SourceLocation LParenLoc = ConsumeParen();

  ExprResult Inner;
  {
    llvm::SaveAndRestore<bool> InOld(InOldExpression, true);
    Inner = ParseExpression();
  }
  if (Inner.isInvalid()) {
    SkipUntil(tok::r_paren, StopAtSemi);
    return ExprError();
  }

  if (Tok.isNot(tok::r_paren)) {
    Diag(Tok, diag::err_contract_expected_rparen) << "cppverify::old";
    SkipUntil(tok::r_paren, StopAtSemi);
    return ExprError();
  }
  SourceLocation RParenLoc = ConsumeParen();

  ASTContext &Ctx = Actions.getASTContext();
  return new (Ctx) OldExpr(OldLoc, LParenLoc, RParenLoc, Inner.get());
}

/// Parse cppverify::result
ExprResult Parser::ParseResultExpr() {
  SourceLocation EndLoc = Tok.getAnnotationEndLoc();
  SourceLocation ResultLoc = ConsumeCppVerify();

  // result is only valid in postconditions.
  if (!InContractPostcondition) {
    Diag(ResultLoc, diag::err_result_outside_postcondition);
    return ExprError();
  }
  if (InOldExpression) {
    Diag(ResultLoc, diag::err_result_in_old_expression);
    return ExprError();
  }

  // Use the return type computed from the full Declarator before contract
  // parsing, so it reflects the true return type including pointers,
  // references, and typedefs.
  QualType RetTy = CurrentContractReturnType;
  if (RetTy.isNull())
    if (CurrentContractFunction)
      if (auto *FD = dyn_cast<FunctionDecl>(CurrentContractFunction))
        RetTy = FD->getReturnType();
  if (RetTy.isNull())
    RetTy = Actions.getASTContext().IntTy; // last-resort fallback

  ASTContext &Ctx = Actions.getASTContext();
  return new (Ctx) ResultExpr(ResultLoc, EndLoc, RetTy);
}
