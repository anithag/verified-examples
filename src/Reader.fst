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

(*
private val regid : B.pointer rid
let regid = let hid = host_memory_region () in
 B.malloc HyperStack.root hid 1ul 

val host_rid : unit -> ST rid
(requires fun h -> B.live h regid
/\ is_eternal_region (B.get h regid 0)
)
(ensures fun h0 res h1 -> is_eternal_region res)
let host_rid _ = (!* regid)

val create_ringst : unit -> ST (B.pointer ringstruct8)
(requires fun h -> B.live h regid 
 /\ is_eternal_region (B.get h regid 0)
 )
(ensures fun h0 res h1 -> true)
let create_ringst _ =
    let tmp = {rbuf = B.null; head = 0ul; tail = 0ul; rsize = 0ul} in
    let hid = host_rid () in
    B.malloc hid tmp  1ul


val host_rid : unit -> ST rid
(requires fun h -> true)
(ensures fun h0 res h1 -> is_eternal_region res)
let host_rid _ = host_memory_region ()
*)

  
type message = UInt8.t
type datapointer = B.pointer message
     

let init (s:UInt32.t {gt s 1ul}) (hid: rid) : ST ringstruct8
(requires fun h -> true
/\ is_eternal_region hid)
(ensures fun h0 res h1 -> B.modifies B.loc_none h0 h1 
/\ live_rb h1 res
/\ well_formed_rb h1 res
)
 = Ring.init 0uy s hid
   
 

abstract let read (r: ringstruct8) (f:datapointer  -> UInt32.t -> UInt32.t) : ST UInt32.t
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
  let canpop = Ring.is_poppable r in
  if canpop then
    let m = Ring.pop r in
    let mptr = B.malloc HS.root m 1ul in
    // call handler. For now hard coding the size of the message
    let s = f mptr 1ul in
    s
  else
     0ul
     

