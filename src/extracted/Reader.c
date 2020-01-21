/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -verify -skip-linking -bundle WasmSupport ../Ring.fst ../Reader.fst ../Writer.fst ../Misc.fst -I ../
  F* version: b55bb590
  KreMLin version: 2f843633
 */

#include "Reader.h"

Ring_ringstruct__uint8_t Reader_init(uint32_t s)
{
  return Ring_init__uint8_t((uint8_t)0U, s);
}

K___uint8_t_uint8_t_uint8_t_uint8_t Ring_pop4__uint8_t(Ring_ringstruct__uint8_t r)
{
  uint8_t m1 = Ring_pop__uint8_t(r);
  uint8_t m2 = Ring_pop__uint8_t(r);
  uint8_t m3 = Ring_pop__uint8_t(r);
  uint8_t m4 = Ring_pop__uint8_t(r);
  return ((K___uint8_t_uint8_t_uint8_t_uint8_t){ .fst = m1, .snd = m2, .thd = m3, .f3 = m4 });
}

bool Ring_is_poppable__uint8_t(Ring_ringstruct__uint8_t r)
{
  uint32_t head1 = *r.headptr;
  uint32_t tail1 = *r.tailptr;
  uint32_t rsize = r.rsize;
  uint32_t space = Ring_get_current_size(head1, tail1, rsize);
  if (space > (uint32_t)0U)
    return true;
  else
    return false;
}

uint32_t Reader_read(Ring_ringstruct__uint8_t r)
{
  K___uint8_t_uint8_t_uint8_t_uint8_t scrut = Ring_pop4__uint8_t(r);
  uint8_t h1 = scrut.fst;
  uint8_t h2 = scrut.snd;
  uint8_t h3 = scrut.thd;
  uint8_t h4 = scrut.f3;
  uint32_t len = Misc_make_double_word(h1, h2, h3, h4);
  bool canpop = Ring_is_poppable__uint8_t(r);
  if (canpop)
  {
    uint8_t m = Ring_pop__uint8_t(r);
    uint8_t *mptr = KRML_HOST_MALLOC(sizeof (uint8_t));
    mptr[0U] = m;
    return (uint32_t)1U;
  }
  else
    return (uint32_t)0U;
}

