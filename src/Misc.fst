module Misc

open FStar.Int.Cast


(*
Some handy numbers
2^24 = 16777216ul
2^16 = 65536ul
2^8 = 256ul

2^8 << 24 = 4278190080ul
2^8 << 16 = 16711680ul
2^8 << 8  = 65280ul 
*)

let myshift (h:UInt8.t) (m:UInt32.t{UInt32.lte m 16777216ul}) : Tot UInt32.t
  =
   let a = UInt32.mul (uint8_to_uint32 h) m in
   a




//#set-options "--z3rlimit 80 --initial_fuel 1 --max_fuel 1"
(*
 Given 4 bytes, append them to get a 32-bit integer
*)
let make_double_word (h1:UInt8.t) (h2:UInt8.t) (h3:UInt8.t) (h4:UInt8.t) : Tot UInt32.t
= 
let a1 = myshift h1   16777216ul in
let a2 = myshift h1   65536ul in
let a3 = myshift h1   256ul in
let a4 = myshift h1   1ul in
assert(UInt32.lte a1 4278190080ul);
assert(UInt32.lte a2 16711680ul);
assert(UInt32.lte a3 65280ul);
assert(UInt32.lte a4 255ul);
let a5 = UInt32.add a2 a3 in
let a6 = UInt32.add a5 a4 in
let a7 = UInt32.add a1 a6 in
a7
