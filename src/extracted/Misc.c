/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -verify -skip-linking -bundle WasmSupport ../Ring.fst ../Reader.fst ../Writer.fst -I ../
  F* version: b55bb590
  KreMLin version: 2f843633
 */

#include "Misc.h"

uint32_t Misc_myshift(uint8_t h, uint32_t m)
{
  return (uint32_t)h * m;
}

uint32_t Misc_make_double_word(uint8_t h1, uint8_t h2, uint8_t h3, uint8_t h4)
{
  uint32_t a1 = Misc_myshift(h1, (uint32_t)16777216U);
  uint32_t a2 = Misc_myshift(h1, (uint32_t)65536U);
  uint32_t a3 = Misc_myshift(h1, (uint32_t)256U);
  uint32_t a4 = Misc_myshift(h1, (uint32_t)1U);
  uint32_t a5 = a2 + a3;
  uint32_t a6 = a5 + a4;
  return a1 + a6;
}

