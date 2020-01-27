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
open FStar.Seq




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



let get_head_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r}): GTot (r':UInt32.t {UInt32.lt r' r.rsize})
= B.get h r.headptr 0

let get_tail_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r}): GTot (r':UInt32.t {UInt32.lt r' r.rsize})
= B.get h r.tailptr 0

//increment the head by 1 push
let incr_head_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r}): GTot (r':UInt32.t {UInt32.lt r' r.rsize})
 = let head = B.get h r.headptr 0 in
  incr_ht_spec head r.rsize

//increment the head by 2 push
let incr2_head_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r /\ (UInt32.gt r.rsize 2ul)}): GTot (r':UInt32.t {UInt32.lt r' r.rsize})
=
let ht = B.get h r.headptr 0 in
let rsize = r.rsize in
let _ = assert(UInt32.lt ht rsize) in
let ht1 = UInt32.add ht 1ul in
  if (UInt32.eq ht1 rsize) then 1ul
  else
    let _ = assert(UInt32.lt ht1 rsize) in
    let ht2 = UInt32.add ht1 1ul in
       if (UInt32.eq ht2 rsize)  then 0ul
         else ht2

//increment the head by 3 push
let incr3_head_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r /\ (UInt32.gt r.rsize 3ul)}): GTot (r':UInt32.t {UInt32.lt r' r.rsize})
=
let ht = B.get h r.headptr 0 in
let rsize = r.rsize in
let _ = assert(UInt32.lt ht rsize) in
let ht1 = UInt32.add ht 1ul in
  if (UInt32.eq ht1 rsize) then 2ul
  else
    let _ = assert(UInt32.lt ht1 rsize) in
    let ht2 = UInt32.add ht1 1ul in
       if (UInt32.eq ht2 rsize)  then 1ul
         else 
           let _ = assert(UInt32.lt ht2 rsize) in
           let ht3 = UInt32.add ht2 1ul in
           if (UInt32.eq ht3 rsize)  then 0ul
             else ht3

//increment the head by 4 push
let incr4_head_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r /\ (UInt32.gt r.rsize 4ul)}): GTot (r':UInt32.t {UInt32.lt r' r.rsize})
=
let ht = B.get h r.headptr 0 in
let rsize = r.rsize in
let _ = assert(UInt32.lt ht rsize) in
let ht1 = UInt32.add ht 1ul in
  if (UInt32.eq ht1 rsize) then 3ul
  else
    let _ = assert(UInt32.lt ht1 rsize) in
    let ht2 = UInt32.add ht1 1ul in
       if (UInt32.eq ht2 rsize)  then 2ul
         else 
           let _ = assert(UInt32.lt ht2 rsize) in
           let ht3 = UInt32.add ht2 1ul in
           if (UInt32.eq ht3 rsize)  then 1ul
             else 
               let _ = assert(UInt32.lt ht3 rsize) in
               let ht4 = UInt32.add ht3 1ul in
               if (UInt32.eq ht4 rsize) then 0ul
               else ht4
  

let incr_tail_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r}): GTot (r':UInt32.t {UInt32.lt r' r.rsize})
  = let tail = B.get h r.tailptr 0 in
  incr_ht_spec tail r.rsize

let incr2_tail_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r /\ (UInt32.gt r.rsize 2ul)}): GTot (r':UInt32.t {UInt32.lt r' r.rsize})
=
let ht = B.get h r.tailptr 0 in
let rsize = r.rsize in
let _ = assert(UInt32.lt ht rsize) in
let ht1 = UInt32.add ht 1ul in
  if (UInt32.eq ht1 rsize) then 1ul
  else
    let _ = assert(UInt32.lt ht1 rsize) in
    let ht2 = UInt32.add ht1 1ul in
       if (UInt32.eq ht2 rsize)  then 0ul
         else ht2

let incr3_tail_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r /\ (UInt32.gt r.rsize 3ul)}): GTot (r':UInt32.t {UInt32.lt r' r.rsize})
=
let ht = B.get h r.tailptr 0 in
let rsize = r.rsize in
let _ = assert(UInt32.lt ht rsize) in
let ht1 = UInt32.add ht 1ul in
  if (UInt32.eq ht1 rsize) then 2ul
  else
    let _ = assert(UInt32.lt ht1 rsize) in
    let ht2 = UInt32.add ht1 1ul in
       if (UInt32.eq ht2 rsize)  then 1ul
         else 
           let _ = assert(UInt32.lt ht2 rsize) in
           let ht3 = UInt32.add ht2 1ul in
           if (UInt32.eq ht3 rsize)  then 0ul
             else ht3

let incr4_tail_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r /\ (UInt32.gt r.rsize 4ul)}): GTot (r':UInt32.t {UInt32.lt r' r.rsize})
=
let ht = B.get h r.tailptr 0 in
let rsize = r.rsize in
let _ = assert(UInt32.lt ht rsize) in
let ht1 = UInt32.add ht 1ul in
  if (UInt32.eq ht1 rsize) then 3ul
  else
    let _ = assert(UInt32.lt ht1 rsize) in
    let ht2 = UInt32.add ht1 1ul in
       if (UInt32.eq ht2 rsize)  then 2ul
         else 
           let _ = assert(UInt32.lt ht2 rsize) in
           let ht3 = UInt32.add ht2 1ul in
           if (UInt32.eq ht3 rsize)  then 1ul
             else 
               let _ = assert(UInt32.lt ht3 rsize) in
               let ht4 = UInt32.add ht3 1ul in
               if (UInt32.eq ht4 rsize) then 0ul
               else ht4
  

let tail_unmodified_spec (#a:eqtype) (h0:HS.mem) (h1:HS.mem) (r0:ringstruct a) (r1: ringstruct a) : GTot bool
 = UInt32.eq (B.get h0 r0.tailptr 0) (B.get h1 r1.tailptr 0) 

let head_unmodified_spec (#a:eqtype) (h0:HS.mem) (h1:HS.mem) (r0:ringstruct a) (r1: ringstruct a) : GTot bool
 = UInt32.eq (B.get h0 r0.headptr 0) (B.get h1 r1.headptr 0) 

let rsize_unmodified_spec (#a:eqtype) (r0:ringstruct a) (r1: ringstruct a) : GTot bool
 = UInt32.eq r0.rsize r1.rsize 

let incr_ht (ht:UInt32.t) (rsize:UInt32.t{UInt32.lt ht rsize}) : Tot  (i:UInt32.t {UInt32.lt i rsize})
  // increment by 1 and check if the buffer is full
  // if so, reset it
 = let ht' = UInt32.add ht 1ul in
  if UInt32.eq ht' rsize then 0ul
  else ht'



let get_current_size (head:UInt32.t) (tail:UInt32.t) (rsize:UInt32.t{UInt32.lt head rsize /\ UInt32.lt tail rsize}) : Tot  (i:UInt32.t {UInt32.lte i rsize})
 =
  (*
   *  ----------------------
   *  |  |  |  |  |  |  |  | 
   *  ----------------------
   *   t        h
   *  ----------------------
   *  |  |  |  |  |  |  |  | 
   *  ----------------------
   *      h     t
   *)
   if (UInt32.gte head  tail) then (UInt32.sub head tail)
   else //  (UInt32.lt head  tail)
   (UInt32.sub rsize (UInt32.sub tail head))
   

let get_remaining_space (head:UInt32.t) (tail:UInt32.t) (rsize:UInt32.t{UInt32.lt head rsize /\ UInt32.lt tail rsize}) : Tot  (i:UInt32.t {UInt32.lte i rsize})
 =
  (*
   *  ----------------------
   *  |  |  |  |  |  |  |  | 
   *  ----------------------
   *   t        h
   *  ----------------------
   *  |  |  |  |  |  |  |  | 
   *  ----------------------
   *      h     t
   *)
   let c = get_current_size head tail rsize in
     (UInt32.sub rsize c)
   
let get_current_size_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r}) : GTot (i:UInt32.t {UInt32.lte i r.rsize})
= 
let head = B.get h r.headptr 0 in
let tail = B.get h r.tailptr 0 in
let rsize = r.rsize in
get_current_size head tail rsize


let remaining_space_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a{well_formed_rb h r}): GTot  (r':UInt32.t {UInt32.lte r' r.rsize})
 =
  let head = B.get h r.headptr 0 in
  let tail = B.get h  r.tailptr 0 in
  let rsize = r.rsize in
  (*
   *  ----------------------
   *  |  |  |  |  |  |  |  | 
   *  ----------------------
   *   t        h
   *)
   let c = get_current_size head tail rsize in
     (UInt32.sub rsize c)
   

let is_rb_full_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r}): GTot bool
  = let sz = get_current_size_spec h r in
  (UInt32.eq sz (UInt32.sub r.rsize 1ul))

let is_rb_empty_spec (#a:eqtype) (h:HS.mem) (r:ringstruct a {well_formed_rb h r}): GTot bool
  = let sz = get_current_size_spec h r in
  (UInt32.eq sz 0ul)


let is_poppable (#a:eqtype) (r:ringstruct a): ST bool
(requires fun h -> live_rb h r
                /\ well_formed_rb h r
)
(ensures fun h0 s h1 -> live_rb h1 r
                     /\ well_formed_rb h1 r
                     /\ modifies loc_none h0 h1
                     /\ ((s == true) ==>  not (is_rb_empty_spec h1 r))
)
= let head = !* r.headptr in
let tail = !* r.tailptr in
let rsize = r.rsize in
let space = get_current_size head tail rsize in
if (UInt32.gt space 0ul) then true
else false

let is_dword_poppable (#a:eqtype) (r:ringstruct a): ST bool
(requires fun h -> live_rb h r
                /\ well_formed_rb h r
)
(ensures fun h0 s h1 -> live_rb h1 r
                     /\ well_formed_rb h1 r
                     /\ modifies loc_none h0 h1
                     /\ ((s == true) ==>  (UInt32.gte (get_current_size_spec h1 r) 4ul))
)
= let head = !* r.headptr in
let tail = !* r.tailptr in
let rsize = r.rsize in
let space = get_current_size head tail rsize in
if (UInt32.gte space 4ul) then true
else false


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
   // update the buffer at head and then
    // increment the head
  let rsize = r.rsize in
  let head =  !* r.headptr in
  let _ =  r.headptr *= (incr_ht head rsize) in
  B.upd r.rbuf head v

let push2 (#a:eqtype) (r: ringstruct a) (v1:a) (v2:a) : ST unit
  (requires fun h -> live_rb h r
                  /\  well_formed_rb h r
//                  /\ not (is_rb_full_spec h r)
                     /\ UInt32.gt (remaining_space_spec h r) 4ul
                     /\ (UInt32.gt r.rsize 4ul)
                   )
  (ensures fun h0 _ h1 -> 
                    live_rb h1 r 
                    /\ modifies (loc_union (loc_buffer r.rbuf)  (loc_buffer r.headptr)) h0 h1
                    /\ tail_unmodified_spec h0 h1 r r 
                    /\ well_formed_rb h1 r
                    /\ as_seq h1 r.rbuf == (Seq.upd (Seq.upd (as_seq h0 r.rbuf) (UInt32.v (get_head_spec h0 r)) v1)  (UInt32.v (incr_head_spec h0 r)) v2)
                    /\  get_head_spec h1 r == incr2_head_spec h0 r
//                    /\ not (is_rb_empty_spec h1 r)
                    )
  =
  push r v1;
  push r v2

(*
SMT timing out. Fix this later
let push4 (#a:eqtype) (r: ringstruct a) (v1:a) (v2:a) (v3:a) (v4:a) : ST unit
  (requires fun h -> live_rb h r
                  /\  well_formed_rb h r
//                  /\ not (is_rb_full_spec h r)
                     /\ UInt32.gt (remaining_space_spec h r) 4ul
                     /\ (UInt32.gt r.rsize 4ul)
                   )
  (ensures fun h0 _ h1 -> 
                    live_rb h1 r 
                    /\ modifies (loc_union (loc_buffer r.rbuf)  (loc_buffer r.headptr)) h0 h1
                    /\ tail_unmodified_spec h0 h1 r r 
                    /\ well_formed_rb h1 r
                    /\ as_seq h1 r.rbuf == (Seq.upd (Seq.upd (Seq.upd (Seq.upd (as_seq h0 r.rbuf) (UInt32.v (get_head_spec h0 r)) v1)  (UInt32.v (incr_head_spec h0 r)) v2)  (UInt32.v (incr2_head_spec h0 r)) v3)  (UInt32.v (incr3_head_spec h0 r)) v4)
//                    /\ as_seq h1 r.rbuf == (Seq.upd (Seq.upd (Seq.upd (as_seq h0 r.rbuf) (UInt32.v (get_head_spec h0 r)) v1)  (UInt32.v (incr_head_spec h0 r)) v2)  (UInt32.v (incr2_head_spec h0 r)) v3)
                    /\  get_head_spec h1 r == incr4_head_spec h0 r
//                    /\ not (is_rb_empty_spec h1 r)
                    )
  =
  push r v1;
  push r v2;
  push r v3;
  push r v4

*)
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
//                     /\ not (is_rb_empty_spec h0 r)
                     /\ (UInt32.gt (get_current_size_spec h0 r) 0ul)
                    )
  (ensures fun h0 v h1 -> live_rb h1 r
                   /\ well_formed_rb h1 r
                   /\ modifies (loc_buffer r.tailptr) h0 h1
                   /\ as_seq h1 r.rbuf == as_seq h0 r.rbuf
                   /\ head_unmodified_spec h0 h1 r r 
                   /\ (v == Seq.index (as_seq h1 r.rbuf) (UInt32.v (get_tail_spec h0 r)))
                   /\ (get_tail_spec h1 r == incr_tail_spec h0 r)
                   /\ (get_current_size_spec h1 r) = UInt32.sub (get_current_size_spec h0 r) 1ul
//                   /\ UInt32.lte (get_current_size_spec h1 r)  (get_current_size_spec h0 r)
  )
  = 
  let rsize = r.rsize in
  let tail = !* r.tailptr in
//  let head = !* r.headptr in
  // First deref the buffer and then increment the tail
  let _ = r.tailptr *=  (incr_ht tail rsize) in
  B.index r.rbuf tail



#set-options "--z3rlimit 80 --initial_fuel 1 --max_fuel 1"
//Handy routines
// Return a sequence of bytes
let pop4 (#a:eqtype) (r: ringstruct a) : ST (a*a*a*a) 
  (requires fun h0 -> live_rb h0 r 
                     /\ well_formed_rb h0 r
                     /\ UInt32.gte (get_current_size_spec h0 r) 4ul
//                     /\ (UInt32.gt r.rsize 4ul)
                    )
  (ensures fun h0 (v1, v2, v3, v4) h1 -> live_rb h1 r
                   /\ well_formed_rb h1 r
                   /\ modifies (loc_buffer r.tailptr) h0 h1
                   /\ as_seq h1 r.rbuf == as_seq h0 r.rbuf
                   /\ head_unmodified_spec h0 h1 r r 
                   /\ (v1 == Seq.index (as_seq h1 r.rbuf) (UInt32.v (get_tail_spec h0 r)))
                   /\ (v2 == Seq.index (as_seq h1 r.rbuf) (UInt32.v (incr_tail_spec h0 r)))
                   /\ (v3 == Seq.index (as_seq h1 r.rbuf) (UInt32.v (incr2_tail_spec h0 r)))
                   /\ (v4 == Seq.index (as_seq h1 r.rbuf) (UInt32.v (incr3_tail_spec h0 r)))
                   /\ (get_tail_spec h1 r == incr4_tail_spec h0 r)
                     /\ (get_current_size_spec h0 r) = UInt32.add (get_current_size_spec h1 r) 4ul  
  )
  = 
   let m1 = pop r in
   let m2 = pop r in
   let m3 = pop r in
   let m4 = pop r in
   (m1, m2, m3, m4)
   
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
  push2 rb 5uy 6uy;
//  push2 rb 7uy 8uy;
//  let (v1, v2, v3, v4) = pop4 rb in
  v

   

