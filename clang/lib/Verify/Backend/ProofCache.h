//===--- ProofCache.h - Persistent verified-obligation cache -----*- C++
//-*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_PROOFCACHE_H
#define LLVM_CLANG_VERIFY_BACKEND_PROOFCACHE_H

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <string>

namespace clang {
namespace verify {

enum class ProofCacheLookupKind { Miss, Hit, Corrupt, IOFailure };

struct ProofCacheLookup {
  ProofCacheLookupKind Kind = ProofCacheLookupKind::Miss;
  std::string Message;
};

/// Stores only successful proof verdicts. Cache entries bind a dependency-
/// scoped semantic hash to the exact backend adapter and solver version.
class ProofCache {
  std::string Root;
  std::string BackendIdentity;
  uint64_t MaxBytes;
  uint64_t MaxEntries;
  std::string InitializationError;

  std::string entryContents(llvm::StringRef SemanticHash) const;
  std::string entryPath(llvm::StringRef Contents) const;
  llvm::Error pruneImpl(uint64_t ReserveBytes, uint64_t ReserveEntries,
                        bool EvictOne) const;

public:
  ProofCache(std::string Root, std::string BackendIdentity, uint64_t MaxBytes,
             uint64_t MaxEntries);

  bool enabled() const { return !Root.empty(); }
  ProofCacheLookup lookup(llvm::StringRef SemanticHash) const;
  llvm::Error store(llvm::StringRef SemanticHash) const;
  llvm::Error prune() const;
};

} // namespace verify
} // namespace clang

#endif
