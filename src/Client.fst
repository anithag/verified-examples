module Client


open Reader
open Writer
module HS = FStar.HyperStack
module B = LowStar.Buffer 
open FStar.HyperStack.ST

type byte = UInt8.t

let host_memory_region (_:unit) : ST HS.rid
  (requires fun _ -> true)
  (requires fun h0 r h1 -> is_eternal_region r) 
  = new_region HS.root

// reading external memory. This function simulates the external adversary
let read_host_memory (host_buffer:B.buffer byte) (addr:UInt32.t) : ST byte
  (requires fun x -> True)
  (ensures fun h0 b h1 -> B.modifies (B.loc_buffer host_buffer) h0 h1) = (UInt8.uint_to_t 0)

let enclave_memory_region (_:unit) : ST HS.rid
  (requires fun _ -> true)
  (requires fun h0 r h1 -> is_eternal_region r) 
  = new_region HS.root

(*
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
*)

let main () : ST UInt8.t
  (requires fun h0 -> true)
  (ensures fun h0 r h1 -> true)
  = 
  let host_rid = host_memory_region () in   
  let rs = init 36ul host_rid in
  let rs' = write rs 2uy in
  let f = fun (d:datapointer) (u:UInt32.t) ->() in  
  let r = read rs' f in
  0uy
