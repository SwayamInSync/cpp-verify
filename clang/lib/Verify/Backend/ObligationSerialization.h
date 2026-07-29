//===--- ObligationSerialization.h - Stable obligation archives -*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_OBLIGATIONSERIALIZATION_H
#define LLVM_CLANG_VERIFY_BACKEND_OBLIGATIONSERIALIZATION_H

#include "Obligation.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <string>
#include <vector>

namespace clang {
namespace verify {

inline constexpr uint32_t ObligationSerializationVersion = 1;
inline constexpr uint32_t ObligationSemanticHashVersion = 3;

/// Serialize one module as a deterministic, versioned binary record. Records
/// may be concatenated to form an archive.
std::string serializeObligationModule(const ObligationModule &Module);

/// Decode and validate every record in an archive. Unknown versions, malformed
/// lengths, invalid enums, and modules whose declared features do not match
/// their contents fail closed.
llvm::Expected<std::vector<ObligationModule>>
deserializeObligationModules(llvm::StringRef Archive);

/// SHA-256 over the canonical module semantics. Portable source paths,
/// display-only names, and diagnostic identities are excluded from the digest.
std::string obligationSemanticHash(const ObligationModule &Module);

/// SHA-256 for an individual goal together with every logical declaration on
/// which it may depend. Positional and source-anchored identities are excluded.
std::string obligationSemanticHash(const ObligationModule &Module,
                                   const Obligation &Item);

} // namespace verify
} // namespace clang

#endif
