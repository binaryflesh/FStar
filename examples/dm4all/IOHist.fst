module IOHist

open FStar.List
open FStar.WellFounded

(* Reasoning about IO, with access to the history of output previous to
 * running the program. Postconditions are over the (accumulated) output
 * of the program and its return value. Preconditions are over the
 * history. Inputs are treated as a demonic non-deterministic choice. *)

type input = int
type output = int

noeq
type io a =
  | Read    : (input -> io a) -> io a
  | Write   : output -> io a -> io a
  | Return  : a -> io a

let return (a:Type u#a) (x:a) = Return x

let rec bind (a : Type u#aa) (b : Type u#bb)
         (l : io a) (k : a -> io b) : io b =
  match l with
  | Read f -> Read (fun i -> axiom1 f i; bind _ _ (f i) k)
  | Write o k' -> Write o (bind _ _ k' k)
  | Return v -> k v

let post a = a -> list output -> Type0
(* flipping these arguments will break the gen_wps_for_free logic, FIXME *)
let wpty a = list output -> post a -> Type0

unfold
let return_wp (a:Type) (x:a) : wpty a =
  fun h p -> p x h

unfold
let bind_wp (_ : range) (a:Type) (b:Type) (w : wpty a) (kw : a -> wpty b) : wpty b =
  fun h p -> w h (fun x h' -> kw x h' (fun y h'' -> p y h''))
  
let rec interpretation #a (m : io a) (h : list output) (p : post a) : Type0 =
  match m with
  | Write o m -> interpretation m (o :: h) p
  | Read f -> forall (i : input). (axiom1 f i ; interpretation (f i) h p)
  | Return x -> p x h

total
reifiable
reflectable
new_effect {
  IO : a:Type -> Effect
  with
       repr      = io
     ; return    = return
     ; bind      = bind

     ; wp_type   = wpty
     ; return_wp = return_wp
     ; bind_wp   = bind_wp

     ; interp = interpretation
}

val read : unit -> IO int (fun h p -> forall x. p x h)
let read () =
    IO?.reflect (Read (fun i -> Return i))

(* Keeping the log backwards, since otherwise the VCs are too contrived for z3.
 * Likely something we should fix separately.. *)

val write : i:int -> IO unit (fun h p -> p () (i::h))
let write i =
    IO?.reflect (Write i (Return ()))

val need_a_1 : unit -> IO int (fun h p -> List.memP 1 h /\ p 42 h)
let need_a_1 () = 42

open FStar.Tactics

let test_hist_1 () : IO unit (fun h p -> p () (1::h)) =
  write 1;
  let _ = need_a_1 () in
  ()

[@expect_failure]
let test_hist_2 () : IO unit (fun h p -> p () (1::h)) =
  let _ = need_a_1 () in
  write 1;
  ()

let test1 () : IO int (fun h p -> p 1 (3::2::h)) =
  write 2;
  write 3;
  1

let test2 () : IO int (fun h p -> p 1 (3::2::h)) =
  write 2;
  let x = read () in
  write 3;
  1

let test3 () : IO int (fun h p -> forall x. p 1 (x::2::h)) =
  write 2;
  let x = read () in
  let x = read () in
  let x = read () in
  let x = read () in
  write x;
  1

[@expect_failure]
let test4 () : IO int (fun h p -> forall x. p 1 (x::x::h)) =
  write 2;
  let x = read () in
  let x = read () in
  let x = read () in
  let x = read () in
  write x;
  1

let test5 () : IO int (fun h p -> forall x. p 1 (x::x::h)) =
  let x = read () in
  write x;
  write x;
  1

[@expect_failure]
let mustHaveOccurred (i:int) : IO unit (fun h p -> mem i h) =
  ()