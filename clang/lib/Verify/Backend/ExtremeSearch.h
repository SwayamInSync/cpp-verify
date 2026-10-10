//===--- ExtremeSearch.h - Search for the end of an integer's range -------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_EXTREMESEARCH_H
#define LLVM_CLANG_VERIFY_BACKEND_EXTREMESEARCH_H

#include <cstdint>
#include <optional>

namespace clang {
namespace verify {

/// The search for the greatest (or least) value an integer may take, by
/// questions of the form "is a value at least this distance beyond the
/// current one possible?". The distance doubles while the answer is yes;
/// after the first no, the gap below that distance is halved, so a range of
/// 2^k values takes at most about 2k questions.
class ExtremeSearch {
  static constexpr int64_t MaxStep = int64_t(1) << 40;
  int64_t Step = 1;
  /// Once known, no value lies Gap or more beyond the current one.
  int64_t Gap = 0;
  unsigned Asked = 0;
  unsigned MaxQuestions;
  bool Ended = false;

public:
  explicit ExtremeSearch(unsigned MaxQuestions) : MaxQuestions(MaxQuestions) {}

  /// The distance of the next question; none once the search has ended.
  std::optional<int64_t> next() {
    if (Ended || Asked == MaxQuestions) {
      Ended = true;
      return std::nullopt;
    }
    ++Asked;
    return Gap ? Gap / 2 : Step;
  }

  /// Yes: a value \p Moved beyond the current one, which becomes current.
  /// \p Moved is needed only once a no has been answered.
  void reached(std::optional<int64_t> Moved) {
    if (!Gap) {
      if (Step < MaxStep)
        Step *= 2;
      return;
    }
    if (!Moved || *Moved < 1 || *Moved >= Gap) {
      Ended = true;
      return;
    }
    Gap -= *Moved;
    Ended = Gap == 1;
  }

  /// No: no value lies \p Distance or more beyond the current one.
  void blocked(int64_t Distance) {
    Gap = Distance;
    Ended = Gap == 1;
  }

  /// The question was not answered: the search ends without the extreme.
  void abandon() {
    Ended = true;
    Gap = 0;
  }

  bool ended() const { return Ended; }
  /// Whether the current value is proved to be the extreme.
  bool atExtreme() const { return Ended && Gap == 1; }
  unsigned questions() const { return Asked; }
};

} // namespace verify
} // namespace clang

#endif
