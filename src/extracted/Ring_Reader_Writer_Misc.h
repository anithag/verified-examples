/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -tmpdir extracted -verify -skip-compilation -bundle WasmSupport -bundle Ring+Reader+Writer+Misc= Ring.fst Reader.fst Writer.fst Misc.fst
  F* version: b6f857f3
  KreMLin version: 508d64eb
 */

#include "kremlib.h"
#ifndef __Ring_Reader_Writer_Misc_H
#define __Ring_Reader_Writer_Misc_H




uint32_t Ring_get_current_size(uint32_t head1, uint32_t tail1, uint32_t rsize);

typedef struct Ring_ringstruct__uint8_t_s
{
  uint8_t *rbuf;
  uint32_t *headptr;
  uint32_t *tailptr;
  uint32_t rsize;
}
Ring_ringstruct__uint8_t;

typedef Ring_ringstruct__uint8_t Reader_ringstruct8;

typedef uint32_t Reader_message;

typedef uint8_t Reader_chartype;

typedef uint8_t *Reader_datapointer;

typedef uint64_t Reader_m_size_t;

Ring_ringstruct__uint8_t Ring_init__uint8_t(uint8_t i, uint32_t s);

Ring_ringstruct__uint8_t Reader_init(uint32_t s);

uint8_t Ring_pop__uint8_t(Ring_ringstruct__uint8_t r);

typedef struct K___uint8_t_uint8_t_uint8_t_uint8_t_s
{
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
}
K___uint8_t_uint8_t_uint8_t_uint8_t;

K___uint8_t_uint8_t_uint8_t_uint8_t Ring_pop4__uint8_t(Ring_ringstruct__uint8_t r);

bool Ring_is_dword_poppable__uint8_t(Ring_ringstruct__uint8_t r);

bool Ring_is_poppable__uint8_t(Ring_ringstruct__uint8_t r);

uint32_t
Reader_read(Ring_ringstruct__uint8_t r, uint32_t (*f)(uint32_t x0, uint8_t *x1, uint64_t x2));

void Ring_push__uint8_t(Ring_ringstruct__uint8_t r, uint8_t v1);

void Writer_write(Ring_ringstruct__uint8_t r, uint8_t v1);

uint32_t Misc_myshift(uint8_t h, uint32_t m);

uint32_t Misc_make_double_word(uint8_t h1, uint8_t h2, uint8_t h3, uint8_t h4);

#define __Ring_Reader_Writer_Misc_H_DEFINED
#endif
