From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom todo : forall {A : Type}, A.


(*
Use your solution of Homework 2 and prove correctness of your implementations.
I'm repeating some (partial) definitions here just to make sure
the lemma statements make sense.
*)

(* A language of arithmetic expression *)
Inductive expr : Type :=
| Const of nat
| Plus of expr & expr
| Minus of expr & expr
| Mult of expr & expr.

Fixpoint eval (e : expr) : nat :=
  todo.
(* or use the following one

Fixpoint eval (e : expr) : nat :=
  match e with
  | Const n => n
  | Plus e1 e2 => eval e1 + eval e2
  | Minus e1 e2 => eval e1 - eval e2
  | Mult e1 e2 => eval e1 * eval e2
  end.

*)



(* Stack language *)
Inductive instr := Push (n : nat) | Add | Sub | Mul.

Definition prog := seq instr.
Definition stack := seq nat.

Fixpoint run (p : prog) (s : stack) : stack :=
  todo.
(* or use the following one

Fixpoint run (p : prog) (s : stack) : stack :=
  if p is (i :: p') then
    let s' :=
      match i with
      | Push n => n :: s
      | Add => if s is (a1 :: a2 :: s') then a2 + a1 :: s'
                else s
      | Sub => if s is (a1 :: a2 :: s') then a2 - a1 :: s'
                else s
      | Mul => if s is (a1 :: a2 :: s') then a2 * a1 :: s'
                else s
      end
    in run p' s'
  else s.

*)


(* Compiler from the expression language to the stack language *)
Fixpoint compile (e : expr) : prog :=
  todo.
(* or use the following one

Fixpoint compile (e : expr) : prog :=
  match e with
  | Const n => [:: Push n]
  | Plus e1 e2 => compile e1 ++ compile e2 ++ [:: Add]
  | Minus e1 e2 => compile e1 ++ compile e2 ++ [:: Sub]
  | Mult e1 e2 => compile e1 ++ compile e2 ++ [:: Mul]
  end.

*)


(** Here is a correctness theorem for the compiler: it preserves the
meaning of programs. By "meaning", in this case, we just mean the final
answer computed by the program. For a high-level expression, the answer
is the result of calling [eval]. For stack programs, the answer
is whatever [run] leaves on the top of the stack. The correctness
theorem states that these answers are the same for an expression and
the corresponding compiled program. *)
Theorem compile_correct e :
  run (compile e) [::] = [:: eval e].
Proof.
Admitted.


(* ==== OPTIONAL part: decompiler ==== *)

Fixpoint decompile' (p : prog) (acc : seq expr) : seq expr :=
  if p is (i :: p') then
    let acc' :=
        match i with
        | Push n => Const n :: acc
        | Add => if acc is (e1 :: e2 :: acc') then Plus e2 e1 :: acc'
                 else acc
        | Sub => if acc is (e1 :: e2 :: acc') then Minus e2 e1 :: acc'
                 else acc
        end
    in
    decompile' p' acc'
  else acc.

(** return a default value for the empty program *)
Definition decompile (p : prog) : option expr :=
  if decompile' p [::] is [:: result] then some result
  else None.
Arguments decompile p / : simpl nomatch.


Definition decompile (p : prog) : option expr :=
  todo.

(** Prove [decompile] cancels [compile]. *)
Lemma decompile_compile e :
  decompile (compile e) = Some e.
Proof.
Admitted.

(* Prove the [compile] function is injective *)
Lemma compile_inj :
  injective compile.
Proof.
Admitted.
