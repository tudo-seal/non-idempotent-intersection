(*
  definitions for the non-idempotently typed lambda-calculus
  "nitlc Gamma M A" means that in the type environment Gamma the term M is assigned the type A
*)

From Stdlib Require Import List Permutation.
Import ListNotations.
From NonIdempotent Require Import ulc.

(* non-itempotent intersection types *)
Inductive nity : Type :=
  | niatom (x : nat) : nity (* atom *)
  | niarr (u : list nity) (A : nity) : nity.  (* arrow *)

(* type environment *)
Notation environment := (list (list nity)).

(* environment permutation equivalence *)
Definition bag_equiv Gammas Deltas :=
  (forall x, @Permutation nity
    (concat (map (fun Gamma => nth x Gamma nil) Gammas))
    (concat (map (fun Delta => nth x Delta nil) Deltas))).

(* non-idempotently typed lambda-calculus *)
(* nitlc Gamma M A means that in the type environment Gamma the term M is assigned the type A *)
Inductive nitlc (Gamma : environment) : tm -> nity -> Prop :=
  | nitlc_var x A :
      In A (nth x Gamma nil) ->
      nitlc Gamma (var x) A
  | nitlc_app Gamma' Deltas M N u A :
      bag_equiv [Gamma] (Gamma' :: Deltas) ->
      nitlc Gamma' M (niarr u A) ->
      Forall2 (fun Delta B => nitlc Delta N B) Deltas u ->
      nitlc Gamma (app M N) A
  | nitlc_lam M u A :
      nitlc (cons u Gamma) M A ->
      nitlc Gamma (lam M) (niarr u A).

Module NitlcNotations.
Notation "u --> A" := (niarr u A) (at level 70, right associativity).
Notation "( Gamma |- M : A )" := (nitlc Gamma M A) (at level 0, no associativity).
End NitlcNotations.
