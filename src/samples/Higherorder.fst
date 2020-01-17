module Higherorder

open FStar.UInt8
open FStar.Ref
module B = LowStar.Buffer
open LowStar.BufferOps
open FStar.HyperStack.ST

(*

The goal is to see how the specs are unfolded during typechecking.
Interesting when higher-order functions are used as arguments

*)
let even2 (u:UInt8.t) : Pure bool
  (requires true)
  (ensures fun r -> true) = 
  if UInt8.rem u 2uy = 0uy then true
  else false

let even3 (u: UInt8.t): Tot bool
  = UInt8.rem u 2uy = 0uy


// fails to satisfy postcondition
let mytest (f:(UInt8.t->UInt8.t)) (u:UInt8.t) : Pure UInt8.t
  (requires (forall x. ((even3 x) = true) ==>  ((f x) = x))
  /\ even3 u = true
  )
  (ensures fun r -> r = u)
  =  f u

