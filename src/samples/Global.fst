module Global

open FStar.UInt8
open FStar.Ref
module B = LowStar.Buffer
open LowStar.BufferOps
open FStar.HyperStack.ST



(*
Snippet that shows how to update global variable in-place
*)
noeq
type teststruct a = {rbuf: B.buffer a; head: UInt32.t; tail: UInt32.t; rsize: UInt32.t}

private val i : B.pointer (teststruct UInt32.t)
let i =  let tmp = {rbuf = B.null; head = 0ul; tail = 0ul; rsize = 0ul} in
  B.malloc FStar.HyperStack.root tmp 1ul

let inc _ : ST unit
(requires fun h -> B.live h i)
(ensures fun h0 r h1 -> true)
=  let tmp = {rbuf = B.null; head = 0ul; tail = 0ul; rsize = 0ul} in
   i *= tmp

