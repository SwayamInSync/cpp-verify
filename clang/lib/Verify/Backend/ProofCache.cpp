//===--- ProofCache.cpp
//----------------------------------------------------===//
#include "ProofCache.h"
#include "ObligationSerialization.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <cerrno>
#include <chrono>
#include <system_error>
#include <vector>

using namespace clang;
using namespace verify;

namespace {
constexpr llvm::StringLiteral CachePrefix = "llvmcache-cppverify-";
constexpr llvm::StringLiteral TempPrefix = ".cppverify-tmp-";
constexpr auto StaleTempAge = std::chrono::hours(24);

std::string digest(llvm::StringRef Value) {
  return llvm::toHex(llvm::SHA256::hash(llvm::arrayRefFromStringRef(Value)),
                     /*LowerCase=*/true);
}

bool isCapacityError(std::error_code EC) {
  if (EC == std::errc::no_space_on_device)
    return true;
#ifdef EDQUOT
  return EC == std::error_code(EDQUOT, std::generic_category()) ||
         EC == std::error_code(EDQUOT, std::system_category());
#else
  return false;
#endif
}
} // namespace

ProofCache::ProofCache(std::string Root, std::string BackendIdentity,
                       uint64_t MaxBytes, uint64_t MaxEntries)
    : Root(std::move(Root)), BackendIdentity(std::move(BackendIdentity)),
      MaxBytes(MaxBytes), MaxEntries(MaxEntries) {
  if (this->Root.empty())
    return;
  llvm::sys::fs::file_status Status;
  std::error_code EC = llvm::sys::fs::status(this->Root, Status);
  if (!EC && llvm::sys::fs::exists(Status)) {
    if (!llvm::sys::fs::is_directory(Status))
      InitializationError = "proof cache path is not a directory";
    return;
  }
  if (EC && EC != std::errc::no_such_file_or_directory) {
    InitializationError = "cannot inspect proof cache: " + EC.message();
    return;
  }
  EC = llvm::sys::fs::create_directories(this->Root);
  if (EC)
    InitializationError = "cannot create proof cache: " + EC.message();
}

std::string ProofCache::entryContents(llvm::StringRef SemanticHash) const {
  return "cppverify.proof-cache/1\nbackend=" + BackendIdentity +
         "\nsemantic-hash-version=" +
         std::to_string(ObligationSemanticHashVersion) +
         "\nsemantic-hash=sha256:" + SemanticHash.str() + "\n";
}

std::string ProofCache::entryPath(llvm::StringRef Contents) const {
  llvm::SmallString<256> Path(Root);
  llvm::sys::path::append(Path, CachePrefix + digest(Contents));
  return Path.str().str();
}

ProofCacheLookup ProofCache::lookup(llvm::StringRef SemanticHash) const {
  if (!enabled())
    return {};
  if (!InitializationError.empty())
    return {ProofCacheLookupKind::IOFailure, InitializationError};

  const std::string Expected = entryContents(SemanticHash);
  auto Buffer = llvm::MemoryBuffer::getFile(entryPath(Expected));
  if (!Buffer) {
    if (Buffer.getError() == std::errc::no_such_file_or_directory)
      return {};
    return {ProofCacheLookupKind::IOFailure,
            "cannot read proof cache entry: " + Buffer.getError().message()};
  }
  if ((*Buffer)->getBuffer() != Expected)
    return {ProofCacheLookupKind::Corrupt,
            "corrupt or incompatible proof cache entry"};
  return {ProofCacheLookupKind::Hit, {}};
}

llvm::Error ProofCache::store(llvm::StringRef SemanticHash) const {
  if (!enabled())
    return llvm::Error::success();
  if (!InitializationError.empty())
    return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                   InitializationError.c_str());

  const std::string Contents = entryContents(SemanticHash);
  const std::string Path = entryPath(Contents);
  if (llvm::sys::fs::exists(Path)) {
    ProofCacheLookup Existing = lookup(SemanticHash);
    if (Existing.Kind == ProofCacheLookupKind::Hit)
      return llvm::Error::success();
    if (Existing.Kind == ProofCacheLookupKind::Corrupt ||
        Existing.Kind == ProofCacheLookupKind::IOFailure)
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     Existing.Message.c_str());
  }

  auto Install = [&]() -> llvm::Error {
    llvm::SmallString<256> TempModel(Root);
    llvm::sys::path::append(TempModel, TempPrefix + "%%%%%%");
    auto Temp = llvm::sys::fs::TempFile::create(
        TempModel, llvm::sys::fs::owner_read | llvm::sys::fs::owner_write);
    if (!Temp)
      return Temp.takeError();
    {
      llvm::raw_fd_ostream Out(Temp->FD, /*shouldClose=*/false);
      Out << Contents;
      Out.flush();
      if (Out.has_error()) {
        std::error_code WriteError = Out.error();
        llvm::Error DiscardError = Temp->discard();
        llvm::consumeError(std::move(DiscardError));
        return llvm::errorCodeToError(WriteError);
      }
    }
    if (llvm::Error Error = Temp->keep(Path)) {
      // A concurrent process may have installed the same immutable entry.
      ProofCacheLookup Existing = lookup(SemanticHash);
      if (Existing.Kind == ProofCacheLookupKind::Hit) {
        llvm::consumeError(std::move(Error));
        return llvm::Error::success();
      }
      return Error;
    }
    return llvm::Error::success();
  };

  llvm::Error Error = Install();
  if (!Error)
    return llvm::Error::success();
  std::error_code EC = llvm::errorToErrorCode(std::move(Error));
  if (!isCapacityError(EC))
    return llvm::errorCodeToError(EC);

  // A full cache can prevent the new temporary file from being created.
  // Evict at least one old record, reserve room for this entry, and retry once.
  if (llvm::Error PruneError = pruneImpl(Contents.size(), 1, true))
    return llvm::joinErrors(llvm::errorCodeToError(EC), std::move(PruneError));
  return Install();
}

llvm::Error ProofCache::pruneImpl(uint64_t ReserveBytes,
                                  uint64_t ReserveEntries,
                                  bool EvictOne) const {
  if (!enabled())
    return llvm::Error::success();
  if (!InitializationError.empty())
    return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                   InitializationError.c_str());
  if (MaxBytes && ReserveBytes > MaxBytes)
    return llvm::createStringError(
        std::make_error_code(std::errc::no_space_on_device),
        "proof cache byte limit cannot fit one entry");
  if (MaxEntries && ReserveEntries > MaxEntries)
    return llvm::createStringError(
        std::make_error_code(std::errc::no_space_on_device),
        "proof cache entry limit cannot fit one entry");

  struct Entry {
    std::string Path;
    llvm::sys::TimePoint<> Modified;
    uint64_t Size;
  };
  std::vector<Entry> Entries;
  uint64_t TotalBytes = 0;
  const auto StaleBefore = std::chrono::system_clock::now() - StaleTempAge;
  std::error_code EC;
  for (llvm::sys::fs::directory_iterator It(Root, EC), End; It != End && !EC;
       It.increment(EC)) {
    llvm::StringRef Name = llvm::sys::path::filename(It->path());
    const bool IsEntry = Name.starts_with(CachePrefix);
    const bool IsTemporary = Name.starts_with(TempPrefix);
    if (!IsEntry && !IsTemporary)
      continue;
    auto Status = It->status();
    if (!Status) {
      if (Status.getError() == std::errc::no_such_file_or_directory)
        continue;
      return llvm::errorCodeToError(Status.getError());
    }
    if (!llvm::sys::fs::is_regular_file(*Status))
      continue;
    if (IsTemporary) {
      if (Status->getLastModificationTime() <= StaleBefore) {
        std::error_code RemoveError = llvm::sys::fs::remove(It->path());
        if (RemoveError && RemoveError != std::errc::no_such_file_or_directory)
          return llvm::errorCodeToError(RemoveError);
      }
      continue;
    }
    Entries.push_back(
        {It->path(), Status->getLastModificationTime(), Status->getSize()});
    TotalBytes += Status->getSize();
  }
  if (EC)
    return llvm::errorCodeToError(EC);

  std::sort(Entries.begin(), Entries.end(),
            [](const Entry &Left, const Entry &Right) {
              if (Left.Modified != Right.Modified)
                return Left.Modified < Right.Modified;
              return Left.Path < Right.Path;
            });
  size_t Remaining = Entries.size();
  bool RemovedOne = false;
  auto Fits = [&]() {
    return (!MaxBytes || TotalBytes <= MaxBytes - ReserveBytes) &&
           (!MaxEntries || Remaining <= MaxEntries - ReserveEntries);
  };
  for (const Entry &Item : Entries) {
    if (Fits() && (!EvictOne || RemovedOne))
      break;
    if (std::error_code RemoveError = llvm::sys::fs::remove(Item.Path)) {
      if (RemoveError == std::errc::no_such_file_or_directory) {
        --Remaining;
        TotalBytes = Item.Size > TotalBytes ? 0 : TotalBytes - Item.Size;
        RemovedOne = true;
        continue;
      }
      return llvm::errorCodeToError(RemoveError);
    }
    --Remaining;
    TotalBytes = Item.Size > TotalBytes ? 0 : TotalBytes - Item.Size;
    RemovedOne = true;
  }
  return llvm::Error::success();
}

llvm::Error ProofCache::prune() const { return pruneImpl(0, 0, false); }
