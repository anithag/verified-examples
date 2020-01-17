module Recall

open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST

module B = LowStar.Buffer

let client (b:B.buffer int{B.recallable b})
: ST unit
  (requires fun _ -> True)  //note the trivial precondition
  (ensures fun _ _ _ -> True)
= B.recall b;

  let h = ST.get () in
  assert (B.live h b)
