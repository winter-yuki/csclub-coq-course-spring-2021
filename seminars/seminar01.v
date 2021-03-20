From mathcomp Require Import ssreflect.

(* implement functions with the given signatures *)

Definition prodA (A B C : Type) :
  (A * B) * C -> A * (B * C)
:= fun '(a, b, c) => (a, (b, c)).

Definition sumA (A B C : Type) :
  (A + B) + C -> A + (B + C)
:= fun s =>
     match s with
     | inr c => inr (inr c)
     | inl (inl a) => inl a
     | inl (inr b) => inr (inl b)
     end.

Definition prod_sumD (A B C : Type) :
  A * (B + C) -> (A * B) + (A * C)
:= fun x =>
     match x with
     | (a, inl b) => inl (a, b)
     | (a, inr c) => inr (a, c)
     end.

(* Definition sum_prodD (A B C : Type) :
  A + (B * C) -> (A + B) * (A + C)
:=  *)


(* function composition *)
Definition comp A B C (f : B -> A) (g : C -> B) : C -> A
:= fun x => f (g x).


(* Introduce a notation that lets us use composition like so: f \o g.
   You might need to tweak the implicit status of some comp's arguments *)


(* Introduce empty type, call `void` *)
Inductive void : Type := .

Definition void_terminal (A : Type) :
  void -> A
:= fun v => match v with end.


(* Introduce `unit` type (a type with exactly one canonical form) *)
Inductive unit : Type := tt.

Definition unit_initial (A : Type) :
  A -> unit
:= fun _ => tt.


(* Think of some more type signatures involving void, unit, sum, prod *)
