module Ring

module M = LowStar.Modifies
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U64 =   FStar.UInt64
module I8 =   FStar.Int8
module U8 =   FStar.UInt8
open LowStar.BufferOps
open FStar.HyperStack.ST
include LowStar.Monotonic.Buffer

let host_memory_region (_:unit) : ST HS.rid
  (requires fun _ -> true)
  (requires fun h0 r h1 -> is_eternal_region r) 
  = new_region HS.root

let enclave_memory_region (_:unit) : ST HS.rid
  (requires fun _ -> true)
  (requires fun h0 r h1 -> is_eternal_region r) 
  = new_region HS.root

//allocate external memory
let create_host_memory (#a:eqtype) (host_rid: HS.rid)  (init: a)  (size: UInt32.t) : ST (B.buffer a)
  (requires fun _ -> is_eternal_region host_rid 
                  /\ UInt32.v size > 0)
  (ensures fun h0 b h1 -> live h1 b) 
  = B.malloc host_rid init size  

//allocate enclave memory
let create_enclave_memory (#a:eqtype) (e_rid: HS.rid) (init: a) (size: UInt32.t) : ST (B.buffer a)
  (requires fun _ -> is_eternal_region e_rid 
                  /\ UInt32.v size > 0)
  (ensures fun h0 b h1 -> live h1 b) 
  = B.malloc e_rid init size  


// reading external memory. This function simulates the external adversary
let read_host_memory (host_buffer:B.buffer Int8.t) (addr:UInt32.t) : ST Int8.t
  (requires fun x -> True)
  (ensures fun h0 b h1 -> M.modifies (loc_buffer host_buffer) h0 h1) = (FStar.Int8.int_to_t 0)


abstract noeq
type ringstruct a = { rbuf: B.buffer a; head: UInt32.t; tail: UInt32.t; rsize: UInt32.t}


let incr_ht (ht:UInt32.t) (rsize:UInt32.t) : Pure  UInt32.t
  (requires UInt32.lt ht rsize)
  (ensures fun r -> UInt32.lt r rsize) =
  // increment by 1 and check if the buffer is full
  // if so, reset it
  let ht' = UInt32.add ht 1ul in
  if UInt32.eq ht' rsize then 0ul
  else ht'

let is_rb_full (#a:eqtype) (r:ringstruct a) : Pure bool
  (requires UInt32.lt r.head r.rsize
            /\ UInt32.lt r.head r.rsize
  )
  (ensures fun _ -> true)
  = (UInt32.add r.head 1ul) = r.tail

let is_rb_empty (#a:eqtype) (r:ringstruct a) : Pure bool
  (requires UInt32.lt r.tail r.rsize
            /\ UInt32.lt r.head r.rsize
  )
  (ensures fun _ -> true)
  = UInt32.eq r.head r.tail

let well_formed_rb (#a:eqtype) (r:ringstruct a): GTot bool
//(requires true)
//(ensures fun _ -> true)
  = 
   UInt32.lt r.head r.rsize && 
   UInt32.lt r.tail r.rsize &&
   B.length r.rbuf = UInt32.v r.rsize &&
   B.length r.rbuf > 0
  
let live_rb (#a:eqtype) (h:HS.mem) (r:ringstruct a) : GTot Type0
= B.live h r.rbuf

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
let push (#a:eqtype) (r: ringstruct a) (v: a) : ST ((ringstruct a)*bool)
  (requires fun h0 -> live_rb h0 r
//                   /\ (B.length r.rbuf > 0)
//                   /\ UInt32.lt r.head r.rsize
//                   /\ UInt32.lt r.tail r.rsize
                   /\  well_formed_rb r
                   )
  (ensures fun h0 res h1 -> modifies (loc_buffer r.rbuf) h0 h1
                      /\ live_rb h1 (fst res) 
                      /\ ((snd res) == true ==>  as_seq h1 (fst res).rbuf == Seq.upd (as_seq h0 r.rbuf) (UInt32.v (incr_ht r.head r.rsize)) v)
                      /\ ((snd res) == false ==>  as_seq h1 (fst res).rbuf == as_seq h0 r.rbuf)
                      /\ B.length (fst res).rbuf = UInt32.v (fst res).rsize
                      /\ (fst res).tail == r.tail 
                      /\ UInt32.lt (fst res).head r.rsize
                      /\ (fst res).rsize == r.rsize
                      /\ well_formed_rb (fst res)
                     )
  =
  let b = is_rb_full r in
  if (not b) then
    let head' = incr_ht r.head r.rsize in
    let r' = {r with head = head'} in
    // increment the head and then update the buffer at head
    let _ = B.upd r'.rbuf r'.head v in
    (r', true)
  // buffer not updated  
  else  (r, false)

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
let pop (#a:eqtype) (r: ringstruct a) : ST ((ringstruct a) * (option a)) 
  (requires fun h0 -> live_rb h0 r 
//                   /\ UInt32.lt r.head r.rsize
//                   /\ UInt32.lt r.tail r.rsize
                     /\ well_formed_rb r
                    )
  (ensures fun h0 (r', o) h1 -> live_rb h1 r'
                    /\ modifies_none h0 h1
                    /\ as_seq h1 r'.rbuf == as_seq h0 r.rbuf
                    /\ ( match o with 
                    | Error -> r'.tail == r.tail
                    | Value v -> (v == Seq.index (as_seq h1 r'.rbuf) (UInt32.v (incr_ht r.tail r.rsize)))
                    )
                    /\ r'.head == r.head 
                    /\ r'.rsize == r.rsize
                    /\ UInt32.lt r'.head r'.rsize
                    /\ UInt32.lt r'.tail r'.rsize
                    /\ B.length r'.rbuf = UInt32.v r'.rsize
                    /\ well_formed_rb r'
  )
  = 
  let b = is_rb_empty r in
  if (not b) then
    let tail' = incr_ht r.tail r.rsize in
    let r' = {r with tail = tail'} in
    let v = B.index r'.rbuf r'.tail  in
    (r', (Value v))
  // buffer not updated  
  else  (r, Error)



let init (#a:eqtype) (i: a) (s:UInt32.t {UInt32.gt s 0ul}) (hid: HS.rid) : ST (ringstruct a)
(requires fun h -> true
/\ is_eternal_region hid)
(ensures fun h0 res h1 -> B.modifies B.loc_none h0 h1
/\ B.fresh_loc (loc_buffer res.rbuf) h0 h1 
)
 =
  {rbuf = B.malloc hid i s; head = 0ul; tail = 0ul; rsize=s}
 


(* A simple program that pushes and pops an element from ring buffer
 * The specification says that when operations are successful, the popped element 
 * should be equal to the pushed element. Else, we don't care.
 * For simplicity, 16l is hardcoded.
 *)
let test_ringbuffer (): ST (option I8.t)
     (requires fun h0 -> true)
     (ensures fun h0 r h1 -> match r with
     | Value v -> v == 1y
     | Error -> true
     ) =
  let host_rid = host_memory_region () in   
  // create host memory
  let host_memory = create_host_memory host_rid 0l 256ul in
  //create enclave memory
  let e_rid = enclave_memory_region () in
  let enclave_memory = create_enclave_memory e_rid 0l 128ul in
  let rlen = 32ul in
  let rinit = 1y in
  //ringbuffer is located in host memory region but is disjoint from the host_memory
  let rb = {rbuf = B.malloc host_rid rinit rlen; head = 0ul; tail = 0ul; rsize=rlen}  in
  let (rb', status) = push rb 1y in
  if status then 
      let (rb'', o) = pop rb' in
      o
  else
    Error

let main () : ST Int32.t
  (requires fun h0 -> true)
  (ensures fun h0 r h1 -> true)
  = 
  let _ = test_ringbuffer () in
  0l

