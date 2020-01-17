module Writer

open Reader
open Ring
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.UInt32
module B = LowStar.Buffer
open LowStar.BufferOps


abstract let writer (r: ringstruct8) (v:message) : ST ringstruct8
  (requires fun h -> 
     live_rb h r
     /\ well_formed_rb r
  )
  (ensures fun h0 res h1 -> 
  live_rb h1 res
  /\ well_formed_rb res) 
  =
  let (r', s) = (Ring.push r v) in
  r'
  
