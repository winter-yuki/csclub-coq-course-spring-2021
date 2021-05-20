From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* SSReflect tactic practice *)

Section IntLogic.

Variables A B C : Prop.

(** * Exercise *)
Lemma andA :
  (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
  case=> [[a b] c].
  done.
Qed.


(** * Exercise *)
Lemma conj_disjD :
  A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
  case=> [a [b|c]]; [by left | by right].
Qed.


(** * Exercise *)
Lemma disj_conjD :
  A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
  case=> [a|[b c]].
  { split; by left. }
  split; by right.
Qed.


(** * Exercise *)
Lemma notTrue_iff_False :
  (~ True) <-> False.
Proof. split; done. Qed.


(** Hint 1: use [case] tactic on a proof of [False] to apply the explosion
principle. *)
(** Hint 2: to solve the goal of the form [True], use [exact: I], or simple
automation. *)


(** * Exercise *)
Lemma imp_trans :
  (A -> B) -> (B -> C) -> (A -> C).
Proof.
  move=> ab bc a.
  apply: bc.
  apply: ab.
  done.
Qed.


(** * Exercise *)
Lemma dne_False :
  ~ ~ False -> False.
Proof.
  move=> nnf.
  apply: nnf.
  move=> f.
  done.
Qed.


(** * Exercise *)
Lemma dne_True :
  ~ ~ True -> True.
Proof.
  done.
Qed.


(** * Exercise *)
Lemma LEMisNotFalse :
  ~ ~ (A \/ ~ A).
Proof.
  move=> naa.
  apply: (naa).
  right.
  move=> a.
  apply: naa.
  left.
  done.
Qed.

(** Hint : use `apply: (identifier)`
to apply a hypothesis from the context to
the goal and keep the hypothesis in the context *)


(** * Exercise *)
Lemma weak_Peirce :
  ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
  move=> abaab.
  apply: (abaab).
  move=> aba.
  apply: (aba).
  move=> a.
  apply abaab.
  intros.
  done.
Qed.

End IntLogic.


Section EquationalReasoning.

Variables A B : Type.

(** * Exercise 10 *)
Lemma eqext_refl (f : A -> B) :
  f =1 f.
Proof.
  red.
  intros.
  done.
Qed.


(** * Exercise 11 *)
Lemma eqext_sym (f g : A -> B) :
  f =1 g -> g =1 f.
Proof.
  red; intros.
  done.
Qed.

(** Hint: `rewrite` tactic also works with
universally quantified equalities. I.e. if you
have a hypothesis `eq` of type `forall x, f x = g
x`, you can use `rewrite eq` and Coq will usually
figure out the concrete `x` it needs to specialize
`eq` with, meaning that `rewrite eq` is
essentially `rewrite (eq t)` here. *)


(** * Exercise *)
Lemma eqext_trans (f g h : A -> B) :
  f =1 g -> g =1 h -> f =1 h.
Proof.
  move=> fg gh x.
  rewrite -gh.
  rewrite -fg.
  done.
Qed.

End EquationalReasoning.



(** * Exercise *)
Lemma and_via_ex (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B.
Proof.
  split; intros.
  { destruct H. auto. }
  constructor; destruct H; auto.
Qed.

Lemma and_via_ex' (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B.
Proof.
  (* TODO *)
  split; intros.
  { destruct H. auto. }
  constructor; destruct H; auto.
Qed.


(** * Exercise *)
(* Hint: the `case` tactic understands constructors are injective *)
Lemma pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2).
Proof.
  case.
  done.
Qed.


(** * Exercise *)
Lemma false_eq_true_implies_False :
  forall n, n.+1 = 0 -> False.
Proof.
  case=> //.
Qed.


(** * Exercise *)
Lemma addn0 :
  right_id 0 addn.
Proof.
  red.
  elim=> //.
  intros.
  apply (congr1 S) in H.
  rewrite -H.
Admitted.


(** * Exercise *)
Lemma addnS :
  forall m n, m + n.+1 = (m + n).+1.
Proof.
  elim=> //.
  intros.
  


Admitted.


(** * Exercise: *)
Lemma addnCA : left_commutative addn.
Proof.

Admitted.


(** * Exercise: *)
Lemma addnC : commutative addn.
Proof.

Admitted.


(** * Exercise (optional): *)
Lemma unit_neq_bool:
  unit <> bool.
Proof.

Admitted.
