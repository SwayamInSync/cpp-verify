---
name: clang-modification
description: Patterns for modifying Clang's parser, AST, Sema, and CodeGen. Use when adding new keywords, AST nodes, parsing rules, or semantic checks to the Clang frontend for the CppVerify contracts system.
---

# Clang Modification Patterns

## Adding a New Keyword

1. `clang/include/clang/Basic/TokenKinds.def` — add `KEYWORD(name, FLAGS)`
2. If context-sensitive, use a flag like `KEYCONTRACT` and gate on `-fverify-contracts`
3. Test: the lexer will now produce `tok::kw_name` tokens

## Adding a New AST Expression Node

1. `clang/include/clang/AST/Expr.h` — define class inheriting from `Expr`
2. `clang/include/clang/Basic/StmtNodes.td` — register the new node class
3. `clang/lib/AST/Expr.cpp` — implement constructors, child iterators
4. `clang/lib/AST/StmtPrinter.cpp` — add pretty-printing
5. `clang/lib/AST/StmtProfile.cpp` — add profiling for template dedup
6. `clang/lib/Serialization/` — add read/write for PCH (can skip for MVP)

Key: every Expr needs `getBeginLoc()`, `getEndLoc()`, `children()` iterators.

## Adding a New AST Statement Node

Same as expression but inherit from `Stmt` and add to `StmtNodes.td`.

## Parsing a New Construct

Pattern — recursive descent:
```cpp
StmtResult Parser::ParseMyConstruct() {
    SourceLocation KwLoc = ConsumeToken(); // eat keyword
    
    BalancedDelimiterTracker T(*this, tok::l_paren);
    if (T.consumeOpen()) // expect '('
        return StmtError();
    
    ExprResult E = ParseExpression(); // reuse full expression parser
    if (E.isInvalid())
        return StmtError();
    
    T.consumeClose(); // expect ')'
    
    return Actions.ActOnMyConstruct(KwLoc, E.get());
}
```

- `ConsumeToken()` — eat current token, advance
- `ExpectAndConsume(tok::something)` — eat or emit error
- `BalancedDelimiterTracker` — handles matching parens/braces with error recovery
- `ParseExpression()` — parses any C++ expression with full operator precedence
- `Actions.ActOnXxx()` — calls into Sema for semantic checking

## Sema Pattern

```cpp
ExprResult Sema::ActOnMyConstruct(SourceLocation Loc, Expr *E) {
    // Type-check the expression
    if (!E->getType()->isBooleanType()) {
        ExprResult BoolE = PerformContextuallyConvertToBool(E);
        if (BoolE.isInvalid())
            return ExprError();
        E = BoolE.get();
    }
    // Build and return the AST node
    return new (Context) MyConstructExpr(Loc, E, Context.BoolTy);
}
```

## CodeGen Skip Pattern

```cpp
// In CodeGenFunction::EmitStmt or similar
case Stmt::GhostBlockStmtClass:
case Stmt::ContractAssertStmtClass:
    return; // emit nothing
```

## Key Clang Types to Know

- `QualType` — type + qualifiers (const, volatile). Use `getCanonicalType()` for comparison.
- `SourceLocation` — position in source. Carry through everything for diagnostics.
- `ExprResult` / `StmtResult` — result-or-error wrapper. Check `.isInvalid()`.
- `ASTContext` — owns all AST memory. Allocate nodes with `new (Context) MyNode(...)`.
- `Scope` — lexical scope for name lookup. Push/pop when adding quantifier binders.

## Debugging Tips

- `clang -ast-dump file.cpp` — see the full AST
- `clang -dump-tokens file.cpp` — see lexer output
- Build with `RelWithDebInfo` and use gdb/lldb to step through parser
- Add `llvm::errs() << "DEBUG: ..." ;` for quick printf debugging
