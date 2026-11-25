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

/// A record a run stored under a key: what one function's verification
/// established.
struct ProofCacheRecord {
  ProofCacheLookupKind Kind = ProofCacheLookupKind::Miss;
  std::string Message;
  std::string Payload;
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
  std::string recordHeader(llvm::StringRef Key) const;
  ProofCacheRecord readEntry(llvm::StringRef Header) const;
  llvm::Error installEntry(llvm::StringRef Header, llvm::StringRef Body,
                           bool Replace = false) const;
  llvm::Error pruneImpl(uint64_t ReserveBytes, uint64_t ReserveEntries,
                        bool EvictOne) const;

public:
  ProofCache(std::string Root, std::string BackendIdentity, uint64_t MaxBytes,
             uint64_t MaxEntries);

  bool enabled() const { return !Root.empty(); }
  ProofCacheLookup lookup(llvm::StringRef SemanticHash) const;
  llvm::Error store(llvm::StringRef SemanticHash) const;
  /// A record with its payload, which its checksum guards.
  ProofCacheRecord lookupRecord(llvm::StringRef Key) const;
  llvm::Error storeRecord(llvm::StringRef Key, llvm::StringRef Payload) const;
  /// Removes the record under a key, if there is one.
  llvm::Error removeRecord(llvm::StringRef Key) const;
  llvm::Error prune() const;
};

/// Prunes the cache at \p Root to the limits. Pruning removes entries that a
/// concurrent lookup may still need, so a run prunes once, after its last
/// lookup. A missing directory has nothing to prune.
llvm::Error pruneProofCache(llvm::StringRef Root, uint64_t MaxBytes,
                            uint64_t MaxEntries);

} // namespace verify
} // namespace clang

#endif
