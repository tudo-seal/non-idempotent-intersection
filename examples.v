From Stdlib Require Import List Permutation.
Import ListNotations.

From NonIdempotent Require Import ulc nitlc.
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
  