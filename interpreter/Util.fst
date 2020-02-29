
module Util
open FStar.UInt64
open FStar.IO
open FStar.Buffer
open Ast



val cast_to_word: m:address{UInt.fits (UInt64.v m) 32} -> Tot word
let cast_to_word  m = 
	let n: x:int{UInt.size x 32} = UInt64.v m in
        UInt32.uint_to_t n

val cast_to_nat: address -> Tot nat
let cast_to_nat _ = 0
(*
   Bitmap layout
  ==============
	         ____________________
		| 8-bytes /64-bits   |
		+____________________+
bitmapstart->	|bbbbbbb.......bbbbb |
		+____________________+
bitmapoffset->	|bbbbbbb.......bbbbb |
		|  |    	     |
		|  idx    	     |
		+____________________+

 Each entry is a 8 bytes long and each bit represents if the corresponding 64-bytes at an 
 address(computed by the formula below) is writable.
Each offset represents the bit array for 64 64-bit addresses.
 
 To obtain address represented index 'idx' at 'bitmapoffset' is given as:
	address = ((bitmapoffset * 64) + idx) + heap_start_address 

 To check if 'addr' is writable, compute the index 'idx' as follows:
	bitmapoffset  = (addr - heap_start_address) / 64 + bitmapstart
	idx 	      = (addr - heap_start_address) % 64

 Stack Layout
 ============
	 	 ____________________
		| 8-bytes /64-bits   |
		+____________________+___
framepointer->	|bbbbbbb.......bbbbb |   |
		+____________________+   |
		|bbbbbbb.......bbbbb |   |--> current stack frame
		|____________________|   | stackpointer < framepointer
		|bbbbbbb.......bbbbb |   |
stackpointer->	+____________________+___|

rbp = frame pointer
rsp = stack pointer

*)

(* Given a bitmap offset, this function returns the address of the memory that is being toggled*)
val get_address_represented_in_bitmap:(heapstart:address)->(bitmapstart:address)->(addr:address{UInt64.gte addr bitmapstart})->Tot address
let get_address_represented_in_bitmap heapstart bitmapstart addr = 
 	let bitmapoffset = (UInt64.sub addr bitmapstart) in
	let tmp = (UInt64.mul bitmapoffset 64uL) in
	(UInt64.add heapstart tmp)
	

(* Given an address, this function returns the offset in rwbitmap *)
val get_bitmap_offset: address->address->address->Tot address
let get_bitmap_offset heapstart bitmapstart addr =
 let bitmapoffset = (UInt64.sub addr heapstart) in
       let tmp = (UInt64.mul bitmapoffset 64uL) in
       (* Not including index, since a store can operate only on 8byte granularity
         Optimize it later to get precise address
       *)
       let addroffset = (UInt64.add tmp heapstart) in
        addroffset


(* Given an address, this function returns the index in rwbitmap *)
val get_bitmap_index:address->address->Tot address
let get_bitmap_index heapstart addr = 
	let index = (UInt64.sub addr heapstart) in
	(UInt64.rem index 64uL)

val get_callentries: calltable -> Tot (list callentry)
let get_callentries calltab = match calltab with
 |(MkCalltable li) -> li

val get_arguments_number:calltable -> string->Tot nat
let get_arguments_number calltab func_name = 
	let callentries = (get_callentries calltab) in
	let rec search_func_name (callentries:list callentry): Tot nat = match callentries with
		|[] -> 0 (* raise Halt *)
		|(MkCallentry entry fname arglist access iswrapper)::tail -> if (fname = func_name) then
									List.Tot.length arglist
								   else
									search_func_name tail
	in search_func_name callentries
val get_func_name :calltable -> address->Tot string
let get_func_name calltab instraddr = 
	let callentries = (get_callentries calltab) in
	let rec search_func_name (callentries:list callentry): Tot string = match callentries with
		|[] -> "" (* raise Halt *)
		|(MkCallentry entry fname arglist access iswrapper)::tail -> if (eq entry instraddr) then
									fname
								   else
									search_func_name tail
	in search_func_name callentries

val search_func: calltable -> address -> Tot bool
let search_func calltab instraddr = 
	let callentries = (get_callentries calltab) in
	let rec search_func_name (callentries:list callentry): Tot bool= match callentries with
		|[] -> false
		|(MkCallentry entry fname arglist access iswrapper)::tail -> if (eq entry instraddr) then
									true
								   else
									search_func_name tail
	in search_func_name callentries

val get_func_attributes:calltable -> string->Tot accesstype
let get_func_attributes calltab func_name = 
	let callentries = (get_callentries calltab) in
	let rec search_func_name (callentries:list callentry): Tot accesstype = match callentries with
		|[] -> Private (* raise Halt *)
		|(MkCallentry entry fname arglist access iswrapper)::tail -> if (fname = func_name) then
									access
								   else
									search_func_name tail
	in search_func_name callentries

let invert_stmt s = match s with
 |Seq(_, li) -> li
 | _ -> [s]

let rec print_stmt (stli:list stmt) :Tot bool = match stli with
  | [] -> debug_print_string "end-of-stament-list\n" 
  | (Skip iaddr)::tail -> let _ = debug_print_string "skip\n" in print_stmt tail
  | (Add(iaddr,_, _,_))::tail -> let _ = debug_print_string "add\n" in print_stmt tail
  | (Sub(iaddr,_, _,_))::tail -> let _ = debug_print_string "sub\n" in print_stmt tail
  | (Cmp(iaddr,_, _,_))::tail -> let _ = debug_print_string "cmp\n" in print_stmt tail
  | (Div(iaddr,_, _,_))::tail -> let _ = debug_print_string "div\n" in print_stmt tail
  | (Mul(iaddr,_, _,_))::tail -> let _ = debug_print_string "mul\n" in print_stmt tail
  | (Mod(iaddr,_, _,_))::tail -> let _ = debug_print_string "mod\n" in print_stmt tail
  | (Lor(iaddr,_, _,_))::tail -> let _ = debug_print_string "lor\n" in print_stmt tail
  | (Lsr(iaddr,_, _,_))::tail -> let _ = debug_print_string "lsr\n" in print_stmt tail
  | (Push(iaddr,_))::tail -> let _ = debug_print_string "push\n" in print_stmt tail
  | (Pop(iaddr,_))::tail -> let _ = debug_print_string "pop\n" in print_stmt tail
  | (Store(iaddr, _, _, _))::tail-> let _ = debug_print_string "store\n" in print_stmt tail
  | (Load (iaddr, _, _, _))::tail-> let _ = debug_print_string "load\n" in print_stmt tail
  | (Call (iaddr, _))::tail-> let _ = debug_print_string "call\n" in print_stmt tail
  | (If (iaddr, _, _, _))::tail -> let _ = debug_print_string "if\n" in print_stmt tail
  | (Assign (iaddr, _, _))::tail-> let _ = debug_print_string "assign\n" in print_stmt tail
  | (Jump (iaddr, _))::tail -> let _ = debug_print_string "jump\n" in print_stmt tail
  | (Return iaddr)::tail -> let _ = debug_print_string "return\n" in print_stmt tail
 
let rec print_prog (myprogram:program): Tot bool = match myprogram with
 |[] -> debug_print_string "end-of-program\n" 
 |(fname, stli)::tail -> let _ = debug_print_string "FUNCTION: \n" in
			 let _ = print_stmt (invert_stmt stli) in
			 print_prog tail

val get_stmt_list : string->program->Tot (list stmt) 
let get_stmt_list funcname myprogram =
	let rec loop (fli:program): Tot (list stmt) = begin match fli with
	 |[] -> let _ = debug_print_string funcname in [] (* Ideally throw error *)
	 |(fname, stli)::tail -> if fname = funcname then (invert_stmt stli) else loop tail
	end in
	let stli = loop myprogram in
	stli


(* Returns the name of the function corresponding to this address *)
let get_function_given_address (instraddr:address) (myprogram:program) =
	let rec loop (fli:program): Tot string = begin match fli with
	 |[] -> "" (* Ideally throw error *)
	 |(fname, stli)::tail -> 
		let rec search_ins (stli:list stmt):Tot bool = begin match stli with 
			  | [] -> false
			  | (Skip iaddr)::tail 
			  | (Add(iaddr,_,  _, _))::tail
			  | (Sub(iaddr,_,  _, _))::tail
			  | (Cmp(iaddr,_,  _, _))::tail
			  | (Div(iaddr,_,  _, _))::tail
			  | (Mul(iaddr,_,  _, _))::tail
			  | (Mod(iaddr,_,  _, _))::tail
			  | (Lsr(iaddr,_,  _, _))::tail
			  | (Lor(iaddr,_,  _, _))::tail
			  | (Store(iaddr, _, _, _))::tail
			  | (Load (iaddr, _, _, _))::tail
			  | (Push(iaddr, _))::tail
			  | (Pop(iaddr, _))::tail
			  | (Call (iaddr, _))::tail
			  | (If (iaddr, _, _, _))::tail 
			  | (Assign (iaddr, _, _))::tail
			  | (Jump (iaddr, _))::tail 
			  | (Return iaddr)::tail -> if (eq instraddr iaddr) then true else search_ins tail
			end
		in 
		let instrexists = search_ins (invert_stmt stli) in
		if instrexists then fname else loop tail
	end in
	loop myprogram 

(* Returns the list of stmt from the given address to end of current function *)
val get_stmt_list_in_current_function : address ->program->Tot (list stmt) 
let get_stmt_list_in_current_function instraddr myprogram =
	let funcname = get_function_given_address instraddr myprogram in
	let stli = get_stmt_list funcname myprogram in
	let rec search_ins (stli:list stmt):Tot (list stmt) = begin match stli with 
		  | [] -> []
		  | (Skip iaddr)::tail 
		  | (Add(iaddr,_, _, _))::tail
		  | (Sub(iaddr,_, _, _))::tail
		  | (Cmp(iaddr,_, _, _))::tail
		  | (Div(iaddr,_, _, _))::tail
		  | (Mul(iaddr,_, _, _))::tail
		  | (Mod(iaddr,_, _, _))::tail
		  | (Lsr(iaddr,_,  _, _))::tail
		  | (Lor(iaddr,_,  _, _))::tail
		  | (Store(iaddr, _, _, _))::tail
		  | (Load (iaddr, _, _, _))::tail
		  | (Push(iaddr, _))::tail
		  | (Pop(iaddr, _))::tail
		  | (Call (iaddr, _))::tail
		  | (If (iaddr, _, _, _))::tail 
		  | (Assign (iaddr, _, _))::tail
		  | (Jump (iaddr, _))::tail 
		  | (Return iaddr)::tail -> if (eq instraddr iaddr) then stli else search_ins tail
		end
	in search_ins stli 

