(*
  definitions for the untyped lambda-calculus
*)

From Stdlib Require Import Relations.

(* function composition *)
Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y) :=
  fun x => g (f x).

Arguments funcomp {X Y Z} (g f) /.

(* stream cons *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with | 0 => x | S n => xi n end.

(* untyped lambda-terms *)
Inductive tm : Type :=
  | var (x : nat)           (* de Bruijn term variable *)
  | app (M N : tm)          (* application *)
  | lam (M : tm). (* abstraction *)

(* parallel term renaming *)
Fixpoint ren (xi : nat -> nat) (t : tm) : tm  :=
  match t with
  | var x => var (xi x)
  | app M N => app (ren xi M) (ren xi N)
  | lam M => lam (ren (scons 0 (funcomp S xi)) M)
  end.

(* parallel term substitution *)
Fixpoint subst (sigma: nat -> tm) (s: tm) : tm :=
  match s with
  | var n => sigma n
  | app M N => app (subst sigma M) (subst sigma N)
  | lam M => lam (subst (scons (var 0) (funcomp (ren S) sigma)) M)
  end.

Fixpoint allfv (P : nat -> Prop) (M: tm) : Prop :=
  match M with
  | var n => P n
  | app M N => allfv P M /\ allfv P N
  | lam M =>  allfv (scons True P) M
  end.

(* normal form property *)
Inductive nf : tm -> Prop :=
  | nf_lam M : nf M -> nf (lam M)
  | nf_neutral M : neutral M -> nf M
with neutral : tm -> Prop :=
  | neutral_var x : neutral (var x)
  | neutral_app M N : neutral M -> nf N -> neutral (app M N).

(* head form property: x M1 .. Mn *)
Inductive hf : tm -> Prop :=
  | hf_var x : hf (var x)
  | hf_app M N : hf M -> hf (app M N).

(* traditional I reduction *)
Inductive step : tm -> tm -> Prop :=
  | stepRed M N   : step (app (lam M) N) (subst (scons N var) M)
  | stepLam M M'  : step M M' -> step (lam M) (lam M')
  | stepAppL M M' N : step M M' -> step (app M N) (app M' N)
  | stepAppR M N N' : step N N' -> step (app M N) (app M N').

(* reflexive, transitive closure of step *)
Notation steps := (clos_refl_trans tm step).
