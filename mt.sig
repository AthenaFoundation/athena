(*
Code by Neophytos Michael, implementing the Mersenni Twister
algorithm of Makoto Matsumoto and Takuji Nishimura
*)

signature MT =

sig
  type rand
  type state
  val sgenold  : Word32.word -> state
  val sgenrand : Word32.word -> state
  val sarray   : Word32.word array -> state
  val rand     : state -> rand

  val makeRandomGen: int -> unit -> int 

(* makeRandomGen takes a positive integer k and returns a function f:unit->int *)
(* that returns random integers in the interval 1 ... k *)

  val makeRealNumRandGen: real -> unit -> real 

(* makeRealNumRandGen takes a positive real number r and returns a function  *)
(* f:unit -> real that generates random real numbers in the interval 0 ... r. *)

  val getRandomInt: int -> int 

(* Takes a positive integer k and returns a random integer in the range 1 .. k *)

  val randReal : rand -> real
  val randWord : rand -> Word32.word
 
end