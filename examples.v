From Stdlib Require Import List Permutation ssreflect.
Import ListNotations.

From NonIdempotent Require Import ulc nitlc nitlc_facts.
Import NitlcNotations.

(* \x.x *)
Definition I := lam (var 0).

(* [a] -> a *)
Definition I_ty :=
  niarr [niatom 0] (niatom 0).

Lemma I_ty_spec :
  nitlc [] I I_ty.
Proof.
  constructor.
  constructor.
  simpl.
  now left.
Qed.

Lemma I_ty_spec' :
  nitlc [] I (niarr [I_ty] I_ty).
Proof.
  constructor.
  constructor.
  simpl.
  now left.
Qed.

(* \x.x x *)
Definition omega :=
  lam (app (var 0) (var 0)).

(* [A, [A] -> A] -> A *)
Definition omega_ty A :=
  niarr [A; niarr [A] A] A.

Lemma omega_ty_spec : forall A,
  nitlc [] omega (omega_ty A).
Proof.
  intros A.
  constructor.
  assert (H :
    bag_equiv [[[A; niarr [A] A]]] ([[niarr [A] A]] :: [[[A]]])).
  { intros [|[|x]]; simpl.
    { now apply perm_swap. }
    all: easy. }
  econstructor.
  - apply H.
  - constructor.
    simpl.
    now left.
  - constructor.
    + constructor.
      simpl.
      now left.
    + constructor.
Qed.

Goal nitlc [] (app omega I) I_ty.
Proof.
  assert (H :
    bag_equiv [[]] ([] :: [[]; []])).
  { intros [|[|x]]; simpl.
    all: easy. }
  econstructor.
  - apply H.
  - apply omega_ty_spec.
  - constructor; [|constructor].
    + apply I_ty_spec.
    + apply I_ty_spec'.
    + constructor.
Qed.

(* example of weakening *)
Goal forall Gamma, nitlc Gamma I I_ty.
Proof.
  intros Gamma.
  apply (nitlc_weakening [] [[]; Gamma]).
  - simpl.
    now left.
  - intros [|x]; simpl.
    all: easy.
  - apply I_ty_spec.
Qed.

(* example of renaming *)
Goal forall A, nitlc [[]; [A]] (var 1) A.
Proof.
  intros A.
  change (var 1) with (ren swap (var 0)).
  apply (nitlc_renaming [[A]; []]).
  - intros [|[|x1]] [|[|x2]]; simpl.
    all: easy.
  - intros [|[|[|x]]]; simpl.
    all: easy.
  - constructor.
    simpl.
    now left.
Qed.

(* (x x)[x := I] = I I *)
Goal subst (scons I var) (app (var 0) (var 0)) = app I I.
Proof.
  simpl.
  reflexivity.
Qed.

(* example of substitution *)
Goal forall A1 A2 B,
  nitlc [[A1; A2]] (app (var 0) (var 0)) B ->
  nitlc [] I A1 ->
  nitlc [] I A2 ->
  nitlc [] (app I I) B.
Proof.
  intros A1 A2 B HB HA1 HA2.
  change (app I I) with (subst (scons I var) (app (var 0) (var 0))).
  apply (nitlc_substitution [A1; A2] [] [[]; []]).
  - constructor; [|constructor; [|constructor]].
    + apply HA1.
    + apply HA2.
  - intros [|x]; simpl.
    all: easy.
  - apply HB.
Qed.

(* (\x.x x) (\x.x) -> (\x.x) (\x.x) *)
Goal step (app omega I) (app I I).
Proof.
  constructor.
Qed.

(* example of subject reduction *)
Goal forall Gamma A,
  nitlc Gamma (app omega I) A ->
  nitlc Gamma I A.
Proof.
  intros Gamma A HA.
  apply (nitlc_subject_reduction Gamma (app I I)).
  - constructor.
  - apply (nitlc_subject_reduction Gamma (app omega I)).
    + constructor.
    + apply HA.
Qed.

Hint Extern 1 (Forall2 _ _ _) => apply: Forall2_impl; last by eassumption : core.
Hint Extern 1 (nitlc _ _ _) => match goal with [H : nitlc _ (app _ _) _ |- _] => move=> /nitlcE in H; firstorder subst end : core.
Hint Extern 1 (nitlc _ _ _) => match goal with [H : nitlc _ (lam _) _ |- _] => move=> /nitlcE in H; firstorder subst end : core.
Hint Extern 1 (nitlc _ _ _) => match goal with [H : niarr _ _ = niarr _ _ |- _] => case: H; firstorder subst end : core.

Theorem nitlc_subject_reduction' Gamma M N A : step M N -> nitlc Gamma M A -> nitlc Gamma N A.
Proof.
  move=> HMN. elim: HMN Gamma A.
  all: eauto using nitlc_substitution, nitlc.
Qed.
