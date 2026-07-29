#include "llvm/Support/LEB128.h"

#include <cstdint>

int main() {
  const uint8_t Bytes[] = {0x80, 0x80, 0x80, 0x80, 0x80, 0x80,
                           0x80, 0x80, 0x80, 0x80, 0x00};
  unsigned Consumed = 0;
  const char *Error = nullptr;
  return static_cast<int>(
      llvm::decodeULEB128(Bytes, &Consumed, Bytes + sizeof(Bytes), &Error));
}
