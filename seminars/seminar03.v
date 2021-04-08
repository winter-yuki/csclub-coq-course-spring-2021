From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom todo : forall {A : Type}, A.



(** * Exercise: show that [ex] is a more general case of [and].
    This is because terms of type [ex] are dependent pairs, while terms of type [and]
    are non-dependent pairs, i.e. the type of the second component in independent of the
    value of the first one. *)

Definition and_via_ex (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B
:= conj
  (fun '(ex_intro a b) => conj a b)
  (fun '(conj a b) => ex_intro (fun _ => B) a b).


(** * Exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:= fun e =>
  match e in _ = (a2', b2') return (a1 = a2') /\ (b1 = b2') with
  | erefl => conj erefl erefl
  end.


(** * Exercise (optional) *)
Definition J :
  forall (A : Type) (P : forall (x y : A), x = y -> Prop),
    (forall x : A, P x x erefl) ->
    forall x y (p : x = y), P x y p
:= todo.

(* fun A P pxxe x y p =>
  (match p in (_ = y') return (p -> P x y' p) with
  | erefl => fun p' => p' x x (erefl)
  end) p. *)


(** * Exercise *)
Definition false_eq_true_implies_False :
  forall n, n.+1 = 0 -> False
:= fun _ e =>
  match e
    in _ = z
    return if z is O then False else True
  with
  | erefl => I
  end.

(** * Exercise *)
Definition addnS :
  forall m n, m + n.+1 = (m + n).+1
:= fix rec m n :=
  match m return m + n.+1 = (m + n).+1 with
  | O => erefl
  | S m' => congr1 S (rec m' n)
  end.

(** * Exercise *)
Definition addA : associative addn
:= todo.


(** * Exercise: *)
Definition addnCA : left_commutative addn
:= todo.


(** * Exercise (optional): *)
Definition addnC : commutative addn
:= todo.


(** * Exercise (optional):
Formalize and prove
 - bool ≡ unit + unit,
 - A + B ≡ {b : bool & if b then A else B},
 - A * B ≡ forall b : bool, if b then A else B,
where ≡ means "is isomorphic to".
 *)


(** * Exercise (optional): *)
Definition unit_neq_bool:
  unit <> bool
:= todo.

