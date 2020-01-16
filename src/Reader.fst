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
*)

val host_rid : unit -> ST rid
(requires fun h -> true)
(ensures fun h0 res h1 -> is_eternal_region res)
let host_rid _ = host_memory_region ()


val create_ringst : unit -> ST (B.pointer ringstruct8)
(requires fun h -> true )
(ensures fun h0 res h1 -> true)
let create_ringst _ =
    let tmp = {rbuf = B.null; head = 0ul; tail = 0ul; rsize = 0ul} in
    let hid = host_rid ()  in
    B.malloc hid tmp  1ul

private val ringst:B.pointer ringstruct8
let ringst = create_ringst ()

  
type message = UInt32.t
type size_t = UInt32.t
     

let constructor (s:size_t {gt s 0ul}) (hid: rid) : ST unit 
(requires fun h -> B.live h ringst
/\ is_eternal_region hid)
(ensures fun h0 res h1 -> B.live h1 ringst)
 =
  let tmp = {rbuf = B.malloc hid 0uy s; head = 0ul; tail = 0ul; rsize=s} in
 ringst *= tmp


let wellformed_rs_spec (r:ringstruct8) : Tot bool
  = if (UInt32.lt r.head r.rsize &&  UInt32.lt r.tail r.rsize) then
       true
    else
      false 


abstract val read :  f:(message -> ringstruct8  ->UInt32.t -> ringstruct8) -> ST bool
  (requires fun h -> forall m r u. (wellformed_rs_spec r = true)  ==>   (wellformed_rs_spec (f m r u) = true)
  /\ (wellformed_rs_spec r = true) 
  )
  (ensures fun h0 r h1 -> true)


// read a serialized message by deserializing it
abstract val read_message : (#a:eqtype)-> r:(ringstruct a) -> size:U8.t-> ST (ringstruct a)
  (requires fun h -> true)
  (ensures fun h0 r h1 -> true)
