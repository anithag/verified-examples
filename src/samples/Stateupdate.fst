module Stateupdate

open FStar.UInt8
open FStar.Ref
module B = LowStar.Buffer
module HS = FStar.HyperStack
open LowStar.BufferOps
open FStar.HyperStack.ST
open LowStar.Monotonic.Buffer
module ST=FStar.HyperStack.ST

(*
Updates abstract state. Checks that what is read is what is written
*)
abstract type state = B.lbuffer UInt8.t 4

let init () : ST state
(requires fun h -> true)
(ensures fun h0 st h1 -> B.live h1 st)
= B.malloc HS.root 1uy 4ul


let read (st: state) (f:(B.pointer UInt8.t) -> UInt32.t -> unit) : ST UInt8.t
(requires fun h -> B.live h st)
(ensures fun h0 s h1 -> B.live h1 st
/\ B.modifies B.loc_none h0 h1
/\ as_seq h0 st = as_seq h1 st
/\ s = Seq.index (as_seq h1 st) 0 
) = 
 let t = B.index st 0ul in
 let data = B.malloc HS.root t 1ul in 
 let _ = (f data 0ul) in
 t



let write (st: state) (v:UInt8.t) : ST unit
(requires fun h -> B.live h st)
(ensures fun h0 s h1 -> B.live h1 st
/\ B.modifies (B.loc_buffer st) h0 h1
/\ Seq.upd (as_seq h0 st) 0 v = as_seq h1 st
) = 
 B.upd st 0ul v


val main : unit -> ST UInt8.t
(requires fun h -> true)
(ensures fun h0 v h1 -> true)
let main _ = 
  let st = init () in
  let _ = write st 3uy in
  let f = fun d i -> () in 
//  let _ = assert(UInt8.eq (B.get h st 0) 3uy) in
  let _ = write st 2uy in
  let v = read st f in
  let h = ST.get () in
  let _ = assert(UInt8.eq v 2uy) in
  v
  
