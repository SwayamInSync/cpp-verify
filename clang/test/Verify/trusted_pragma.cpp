// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s
//
// Each assumed contract is marked on its own function, so no pragma can mark
// a region trusted.

#pragma clang attribute push ([[cppverify::trusted]], apply_to = function) // expected-error {{attribute 'cppverify::trusted' is not supported by '#pragma clang attribute'}}
int read_sensor(int channel);
#pragma clang attribute pop // expected-error {{'#pragma clang attribute pop' with no matching '#pragma clang attribute push'}}

[[cppverify::trusted]] int clamp_byte(int v)
  cppverify::post(0 <= cppverify::result && cppverify::result <= 255);
