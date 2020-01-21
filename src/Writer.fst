module Writer

open Reader
open Ring
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.UInt32
module B = LowStar.Buffer
open LowStar.BufferOps


abstract let write (r: ringstruct8) (v:message) : ST unit
  (requires fun h -> 
     live_rb h r
     /\ well_formed_rb h r
     /\ not (is_rb_full_spec h r)
  )
  (ensures fun h0 _ h1 -> 
  live_rb h1 r
  /\ well_formed_rb h1 r) 
  =
  Ring.push r v
  
  
