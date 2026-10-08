//===--- CppVerifyClauses.cpp - Format cpp-verify clauses -----------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// cpp-verify clauses after a function declarator or a loop head, written
// cppverify::pre(...) or through an alias, are laid out like a trailing
// requires clause: each on its own line, and the body's brace on the next.
//
//===----------------------------------------------------------------------===//

#include "FormatTokenSource.h"
#include "UnwrappedLineParser.h"
#include "clang/Basic/CppVerifyConstructs.h"

namespace clang {
namespace format {

namespace {

/// Whether \p Tok names a clause allowed where \p Where is.
bool isClauseWord(const FormatToken &Tok, CppVerifyClausePosition Where,
                  bool &TakesArguments) {
  if (Tok.isNot(tok::identifier))
    return false;
  std::optional<CppVerifyConstruct> C = lookupCppVerifyConstruct(Tok.TokenText);
  if (!C)
    return false;
  TakesArguments = *C != CppVerifyConstruct::Inductive &&
                   *C != CppVerifyConstruct::CompleteBehaviors &&
                   *C != CppVerifyConstruct::DisjointBehaviors;
  unsigned Positions = getCppVerifyPositions(*C);
  return Where == CppVerifyClausePosition::Function
             ? Positions & CppVerifyPosition::FunctionClause
             : Positions & CppVerifyPosition::LoopClause;
}

} // namespace

bool UnwrappedLineParser::mayFollowCppVerifyDeclarator(
    const FormatToken &Previous) const {
  if (Previous.ClosesRequiresClause ||
      Previous.isOneOf(tok::r_paren, tok::kw_const, tok::kw_volatile, tok::amp,
                       tok::ampamp, tok::r_square, tok::kw_noexcept,
                       Keywords.kw_override, Keywords.kw_final)) {
    return true;
  }
  // The end of a trailing return type: `-> T` after the parameters.
  if (Previous.isNoneOf(tok::identifier, tok::greater, tok::star) &&
      !Previous.isTypeName(LangOpts)) {
    return false;
  }
  const FormatToken *Before = nullptr;
  for (const UnwrappedLineNode &Node : Line->Tokens) {
    if (Node.Tok->is(tok::arrow) && Before && Before->is(tok::r_paren))
      return true;
    Before = Node.Tok;
  }
  return false;
}

void UnwrappedLineParser::noteCppVerifyAlias() {
  // namespace Name = [::] cppverify;
  unsigned StoredPosition = Tokens->getPosition();
  FormatToken *Name = Tokens->getNextToken();
  FormatToken *Tok = Name->is(tok::identifier) ? Tokens->getNextToken() : Name;
  if (Tok != Name && Tok->is(tok::equal)) {
    Tok = Tokens->getNextToken();
    if (Tok->is(tok::coloncolon))
      Tok = Tokens->getNextToken();
    if (Tok->is(tok::identifier) &&
        (Tok->TokenText == "cppverify" ||
         CppVerifyAliases.contains(Tok->TokenText)) &&
        Tokens->getNextToken()->is(tok::semi)) {
      CppVerifyAliases.insert(Name->TokenText);
    }
  }
  FormatTok = Tokens->setPosition(StoredPosition);
}

bool UnwrappedLineParser::tryToParseCppVerifyClauses(
    CppVerifyClausePosition Where) {
  bool Parsed = false;
  while (FormatTok->isOneOf(tok::identifier, tok::coloncolon)) {
    // Look ahead for [::] (name ::)+ word [( ... )], and what follows it.
    unsigned StoredPosition = Tokens->getPosition();
    FormatToken *Tok = FormatTok;
    if (Tok->is(tok::coloncolon))
      Tok = Tokens->getNextToken();
    const FormatToken *Qualifier = Tok;
    unsigned Names = 0;
    FormatToken *Word = nullptr;
    FormatToken *After = nullptr;
    while (Tok->is(tok::identifier)) {
      FormatToken *Next = Tokens->getNextToken();
      if (Next->isNot(tok::coloncolon)) {
        Word = Tok;
        After = Next;
        break;
      }
      ++Names;
      Tok = Tokens->getNextToken();
    }
    bool TakesArguments = false;
    bool Accept =
        Word && Names > 0 && isClauseWord(*Word, Where, TakesArguments);
    // After a clause only a clause may follow: NAME(...) is one a macro
    // writes.
    if (!Accept && Word && Names == 0 && After->is(tok::l_paren) &&
        Where == CppVerifyClausePosition::Function &&
        CppVerifyClauseEnds.contains(FormatTok->Previous)) {
      Accept = TakesArguments = true;
    }
    if (Accept && After->is(tok::l_paren)) {
      for (int Depth = 0; After->isNot(tok::eof);
           After = Tokens->getNextToken()) {
        if (After->is(tok::l_paren))
          ++Depth;
        else if (After->is(tok::r_paren) && --Depth == 0)
          break;
      }
      After = Tokens->getNextToken();
    } else if (TakesArguments) {
      Accept = false;
    }
    if (Accept) {
      // Elsewhere C++ allows none of these, except that a call statement can
      // follow a loop head, or a statement such as `if (c)`, before a ';'.
      const bool Known =
          Names == 1 && (Qualifier->TokenText == "cppverify" ||
                         CppVerifyAliases.contains(Qualifier->TokenText));
      switch (Where) {
      case CppVerifyClausePosition::Function:
        Accept = After->is(tok::semi) ? Known : true;
        break;
      case CppVerifyClausePosition::Loop:
        Accept = After->isOneOf(tok::l_brace, tok::identifier, tok::coloncolon)
                     ? After->is(tok::l_brace) || Known
                     : false;
        break;
      case CppVerifyClausePosition::DoWhile:
        Accept = After->isOneOf(tok::semi, tok::identifier, tok::coloncolon);
        break;
      }
    }
    FormatTok = Tokens->setPosition(StoredPosition);
    if (!Accept)
      break;

    FormatTok->setFinalizedType(TT_RequiresClause);
    if (FormatTok->is(tok::coloncolon))
      nextToken();
    for (unsigned I = 0; I < Names; ++I) {
      nextToken();
      nextToken();
    }
    nextToken();
    if (FormatTok->is(tok::l_paren))
      parseParens();
    // A spec's clause proof: post(...) by { ... }.
    if (Where == CppVerifyClausePosition::Function &&
        FormatTok->is(tok::identifier) && FormatTok->TokenText == "by" &&
        Tokens->peekNextToken()->is(tok::l_brace)) {
      nextToken();
      parseChildBlock();
    }
    FormatTok->Previous->ClosesRequiresClause = true;
    CppVerifyClauseEnds.insert(FormatTok->Previous);
    Parsed = true;
  }
  return Parsed;
}

} // namespace format
} // namespace clang
