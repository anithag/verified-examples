module Reader

open Ring
module U8 = FStar.UInt8
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.UInt32
module B = LowStar.Buffer
open LowStar.BufferOps


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
     

let init (s:UInt32.t {gt s 0ul}) (hid: rid) : ST ringstruct8
(requires fun h -> true
/\ is_eternal_region hid)
(ensures fun h0 res h1 -> B.modifies B.loc_none h0 h1 
/\ live_rb h1 res
/\ well_formed_rb res
)
 = Ring.init 0uy s hid
   
 

abstract let read (r: ringstruct8) (f:datapointer  -> UInt32.t -> unit) : ST ringstruct8
  (requires fun h -> 
     live_rb h r
     /\ well_formed_rb r
  )
  (ensures fun h0 r h1 -> 
  live_rb h1 r
  /\ well_formed_rb r) 
  =
  let (r', header) = Ring.pop r in
  let (r'', o) = Ring.pop r' in
  match o with
  | Error -> r
  | Value m ->  // copy to datapointer
    let mptr = B.gcmalloc root m 1ul in
    // call handler. For now hard coding the size of the message
    let _ = f mptr 1ul in
    r''
  

