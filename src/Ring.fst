module Ring

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U64 =   FStar.UInt64
module I8 =   FStar.Int8
module U8 =   FStar.UInt8
open LowStar.BufferOps
open FStar.HyperStack.ST
include LowStar.Monotonic.Buffer





//abstract noeq
//type ringstruct a = { rbuf: B.buffer a; head: UInt32.t; tail: UInt32.t; rsize: UInt32.t}

abstract noeq
type ringstruct a = { rbuf: B.buffer a; headptr: B.pointer UInt32.t; tailptr: B.pointer UInt32.t; rsize: UInt32.t}


let is_rb_full (rsize:UInt32.t) (head:UInt32.t {UInt32.lt head rsize}) (tail:UInt32.t{ UInt32.lt tail rsize}) : Tot bool
  = (UInt32.add head 1ul) = tail

let is_rb_empty (rsize:UInt32.t) (head:UInt32.t {UInt32.lt head rsize}) (tail:UInt32.t {UInt32.lt tail rsize}) : Tot bool
  = UInt32.eq head tail

let live_rb (#a:eqtype) (h:HS.mem) (r:ringstruct a) : GTot Type0
= B.live h r.rbuf
/\ B.live h r.headptr
/\ B.live h r.tailptr
/\ loc_disjoint (loc_buffer r.rbuf) (loc_buffer r.headptr)
/\ loc_disjoint (loc_buffer r.rbuf) (loc_buffer r.tailptr)
/\ loc_disjoint (loc_buffer r.headptr) (loc_buffer r.tailptr)

let well_formed_rb (#a:eqtype) (h:HS.mem) (r:ringstruct a): GTot bool
  = 
  let head = B.get h r.headptr 0 in
  let tail = B.get h r.tailptr 0 in
  UInt32.lt head r.rsize && 
  UInt32.lt tail r.rsize &&
  B.length r.rbuf = UInt32.v r.rsize &&
  B.length r.rbuf > 0
//  B.length r.headptr = 1 &&
//  B.length r.tailptr = 1


let incr_ht_spec (ht:UInt32.t) (rsize:UInt32.t{ UInt32.lt ht rsize}) : GTot  (l:UInt32.t {UInt32.lt l rsize})
  // increment by 1 and check if the buffer is full
  // if so, reset it
 = let ht' = UInt32.add ht 1ul in
  if UInt32.eq ht' rsize then 0ul
  else ht'

let is_rb_full_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r}): GTot bool
  = 
//  let rsize = r.rsize in
  let head =  B.get h r.headptr 0 in
  let tail = B.get h  r.tailptr 0 in
  let rsize = r.rsize in
  let head' = incr_ht_spec head rsize in  
  head' = tail

let is_rb_empty_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a): GTot bool
  = 
//  let rsize = r.rsize in
  let head =  B.get h r.headptr 0 in
  let tail = B.get h  r.tailptr 0 in
   UInt32.eq head tail




let get_head_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r}): GTot (r':UInt32.t {UInt32.lt r' r.rsize})
= B.get h r.headptr 0

let get_tail_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r}): GTot (r':UInt32.t {UInt32.lt r' r.rsize})
= B.get h r.tailptr 0

let incr_head_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r}): GTot (r':UInt32.t {UInt32.lt r' r.rsize})
 = let head = B.get h r.headptr 0 in
  incr_ht_spec head r.rsize
  
let incr_tail_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r}): GTot (r':UInt32.t {UInt32.lt r' r.rsize})
  = let tail = B.get h r.tailptr 0 in
  incr_ht_spec tail r.rsize
  
let tail_unmodified_spec (#a:eqtype) (h0:HS.mem) (h1:HS.mem) (r0:ringstruct a) (r1: ringstruct a) : GTot bool
 = UInt32.eq (B.get h0 r0.tailptr 0) (B.get h1 r1.tailptr 0) 

let head_unmodified_spec (#a:eqtype) (h0:HS.mem) (h1:HS.mem) (r0:ringstruct a) (r1: ringstruct a) : GTot bool
 = UInt32.eq (B.get h0 r0.headptr 0) (B.get h1 r1.headptr 0) 

let rsize_unmodified_spec (#a:eqtype) (r0:ringstruct a) (r1: ringstruct a) : GTot bool
 = UInt32.eq r0.rsize r1.rsize 

let incr_ht (ht:UInt32.t) (rsize:UInt32.t{UInt32.lt ht rsize}) : Tot  (i:UInt32.t {UInt32.lt i rsize})
//(requires UInt32.lt ht rsize)
//(ensures fun i -> UInt32.lt i rsize)
  // increment by 1 and check if the buffer is full
  // if so, reset it
 = let ht' = UInt32.add ht 1ul in
  if UInt32.eq ht' rsize then 0ul
  else ht'


(* push: pushes an element at the head position
 * The pre-condition says that the invariants of the ringbuffer, namely,
 * 1. head and tail are always less than the size of the buffer
 * 2. size of the buffer is at least 1
 * 3. Buffer is live
 * hold. The post-condition says that if the 'push' is successful, then
 * the resulting buffer in the new heap is same as the buffer in the old heap with the element
 * pushed into the head position. If not, buffer remains the same.
 * The post-condition also says that the invariants are preserved, and that the buffer is live.
 *)
let push (#a:eqtype) (r: ringstruct a) (v: a) : ST unit
  (requires fun h -> live_rb h r
                  /\  well_formed_rb h r
                  /\ not (is_rb_full_spec h r)
                   )
  (ensures fun h0 _ h1 -> 
                    live_rb h1 r 
                    /\ modifies (loc_union (loc_buffer r.rbuf)  (loc_buffer r.headptr)) h0 h1
//                    /\ (s == false ==>  as_seq h1 r.rbuf == as_seq h0 r.rbuf)
//                    /\ (s == false ==>  modifies loc_none h0 h1)
                    /\ tail_unmodified_spec h0 h1 r r 
                    /\ well_formed_rb h1 r
//                    /\ (s = true ==>  as_seq h1 r.rbuf == Seq.upd (as_seq h0 r.rbuf) (UInt32.v (get_head_spec h0 r)) v)
//                    /\ (s = true) ==>  (get_head_spec h1 r == incr_head_spec h0 r)
                      /\ as_seq h1 r.rbuf == Seq.upd (as_seq h0 r.rbuf) (UInt32.v (get_head_spec h0 r)) v
                      /\  get_head_spec h1 r == incr_head_spec h0 r
                      /\ not (is_rb_empty_spec h1 r)
                    )
  =
(* 
  let tail = !* r.tailptr in
  let b = is_rb_full rsize head tail in
  if (not b) then
 *)   // update the buffer at head and then
    // increment the head
  let rsize = r.rsize in
  let head =  !* r.headptr in
  let _ =  r.headptr *= (incr_ht head rsize) in
  B.upd r.rbuf head v
     
noeq
type option 'a =
 | Error : option 'a
 | Value : v:'a -> option 'a
 
(* pop:  pop off the element at tail
 * The pre-condition checks that the invariants of the ringbuffer hold while
 * the post-condition says that the element read from the ringbuffer is same as the 
 * one read from the same index in the sequence formed from buffer. When the ringbuffer is full
 * tail is not modified other tail is modified.
 * The post-condition also says that the invariants are preserved
 *)
let pop (#a:eqtype) (r: ringstruct a) : ST a 
  (requires fun h0 -> live_rb h0 r 
                     /\ well_formed_rb h0 r
                     /\ not (is_rb_empty_spec h0 r)
                    )
  (ensures fun h0 v h1 -> live_rb h1 r
                   /\ well_formed_rb h1 r
                   /\ modifies (loc_buffer r.tailptr) h0 h1
                   /\ as_seq h1 r.rbuf == as_seq h0 r.rbuf
                   /\ head_unmodified_spec h0 h1 r r 
                   /\ (v == Seq.index (as_seq h1 r.rbuf) (UInt32.v (get_tail_spec h0 r)))
                   /\ (get_tail_spec h1 r == incr_tail_spec h0 r)
  )
  = 
  let rsize = r.rsize in
  let head =  !* r.headptr in
  let tail = !* r.tailptr in
  let b = is_rb_empty rsize head tail in
  if (not b) then
    // First deref the buffer and then increment the tail
    let v = B.index r.rbuf tail  in
    let _ = r.tailptr *=  incr_ht tail rsize in
    v
  


// The way the fullness of ringbuffer is checked requires that the minimum size is 2
let init (#a:eqtype) (i: a) (s:UInt32.t {UInt32.gt s 1ul}) (hid: HS.rid) : ST (ringstruct a)
(requires fun h -> true
/\ is_eternal_region hid)
(ensures fun h0 res h1 -> B.modifies B.loc_none h0 h1
/\ B.fresh_loc (loc_buffer res.rbuf) h0 h1 
/\ B.fresh_loc (loc_buffer res.headptr) h0 h1 
/\ B.fresh_loc (loc_buffer res.tailptr) h0 h1 
/\ well_formed_rb h1 res
/\ live_rb h1 res
/\ B.length res.rbuf == UInt32.v s
/\ (is_rb_empty_spec h1 res)
/\ not (is_rb_full_spec h1 res)
/\ res.rsize = s
)
 =
  {rbuf = B.malloc hid i s; headptr =  B.malloc hid 0ul 1ul; tailptr =  B.malloc hid 0ul 1ul; rsize=s}
 


(* A simple program that pushes and pops an element from ring buffer
 * The specification says that when operations are successful, the popped element 
 * should be equal to the pushed element. Else, we don't care.
 *)
let test_ringbuffer (): ST UInt8.t
(requires fun h0 -> true)
(requires fun h0 v h1 -> v == 4uy)
= 
let rlen = 32ul in
  let rinit = 1uy in
  //ringbuffer is located in host memory region but is disjoint from the host_memory
  let rb = init rinit rlen HS.root in
//  let h' = HST.get () in
//  assert(live_rb h' rb);
//  assert(not (is_rb_full_spec h' rb));
  let _ = push rb 3uy in
//  let h'' = HST.get () in
//  assert(B.live h'' rb.headptr);
//  assert(not (is_rb_empty_spec h'' rb));
 // let hd = !* (rb.headptr) in
//  assert(B.live h'' rb.headptr);
//  assert((B.get h'' rb.headptr 0) = (incr_head_spec h' rb));
//  assert(hd = (incr_head_spec h' rb));
  let _ = pop rb in  
  let _ = push rb 4uy in
  let v = pop rb in
  v

   
(*
let main () : ST Int32.t
  (requires fun h0 -> true)
  (ensures fun h0 r h1 -> true)
  = 
  let _ = test_ringbuffer () in
  0l

*)
