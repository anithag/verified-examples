module Reader

open Ring
open Misc
module U8 = FStar.UInt8
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.UInt32
module B = LowStar.Buffer
open LowStar.BufferOps
open FStar.HyperStack
open FStar.HyperStack.ST

type ringstruct8 = ringstruct UInt8.t

  
type message = UInt32.t
type chartype = UInt8.t
type datapointer = B.pointer chartype
type m_size_t = UInt64.t     

let init (s:UInt32.t {gt s 1ul}) (hid: rid) : ST ringstruct8
(requires fun h -> true
/\ is_eternal_region hid)
(ensures fun h0 res h1 -> B.modifies B.loc_none h0 h1 
/\ live_rb h1 res
/\ well_formed_rb h1 res
)
 = Ring.init 0uy s hid
   
 
#set-options "--z3rlimit 80 --initial_fuel 1 --max_fuel 1"
abstract let read (r: ringstruct8) (f:message -> datapointer  -> m_size_t -> UInt32.t) : ST UInt32.t
  (requires fun h -> 
     live_rb h r
     /\ well_formed_rb h r
     /\ not (is_rb_empty_spec h r)
     /\ UInt32.gt (get_current_size_spec h r) 4ul
  )
  (ensures fun h0 _ h1 -> 
  live_rb h1 r
  /\ well_formed_rb h1 r) 
  =
    let  (h1, h2, h3, h4) = Ring.pop4 r in
  // process header and get message length
  let len = Misc.make_double_word h1 h2 h3 h4  in
  let canpop_dword = Ring.is_dword_poppable r in
  if canpop_dword then
    //message type
    let (m1, m2, m3, m4) = Ring.pop4 r in
    let m = Misc.make_double_word m1 m2 m3 m4  in
    let canpop' = Ring.is_poppable r in
    if canpop' then
     let d = Ring.pop r in
     let dptr = B.malloc HS.root d 1ul in
    // call handler. For now hard coding the size of the message
    let s = f m  dptr 1uL in
    s
    else 0ul
  else
    0ul
     

