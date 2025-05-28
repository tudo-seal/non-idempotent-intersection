(*
  facts about the simplty typed lambda-calculus
*)

From Stdlib Require Import Lia List Relations PeanoNat.
Import ListNotations.

From NonIdempotent Require Import facts ulc.
Require Import ssreflect ssrbool.

Arguments nth_error_split {A l n a}.
Arguments in_split {A x}.

Scheme nf_ind' := Induction for nf Sort Prop
  with neutral_ind' := Induction for neutral Sort Prop.

Lemma ren_ext M xi1 xi2 :
  (forall x, xi1 x = xi2 x) ->
  ren xi1 M = ren xi2 M.
Proof.
  elim: M xi1 xi2=> /=.
  - move=> *. by congr var.
  - move=> ? IH1 ? IH2 > ?. congr app.
    + by apply: IH1.
    + by apply: IH2.
  - move=> ? IH > ?. congr lam.
    apply: IH. move=> [|x] /=; by [|congr S].
Qed.

Lemma subst_ext M sigma1 sigma2 :
  (forall x, sigma1 x = sigma2 x) ->
  subst sigma1 M = subst sigma2 M.
Proof.
  elim: M sigma1 sigma2=> /=.
  - move=> >. apply.
  - move=> ? IH1 ? IH2 > ?. congr app.
    + by apply: IH1.
    + by apply: IH2.
  - move=> ? IH > Hsigma. congr lam.
    apply: IH. move=> [|x] /=; by [|congr ren].
Qed.

Lemma ren_id M : ren id M = M.
Proof.
  elim: M=> /=.
  - done.
  - by move=> ? -> ? ->.
  - move=> ? IH. congr lam. rewrite -[RHS]IH.
    apply: ren_ext. by case.
Qed.

Lemma subst_var M : subst var M = M.
Proof.
  elim: M=> /=.
  - done.
  - by move=> ? -> ? ->.
  - move=> ? IH. congr lam. rewrite -[RHS]IH.
    apply: subst_ext. by case.
Qed.

Lemma ren_as_subst xi M : ren xi M = subst (funcomp var xi) M.
Proof.
  elim: M xi=> /=.
  - done.
  - move=> ? IH1 ? IH2 ?. by rewrite IH1 IH2.
  - move=> ? IH ?. congr lam. rewrite IH.
    apply: subst_ext. by case.
Qed.

Lemma ren_ren xi1 xi2 M :
  ren xi2 (ren xi1 M) = ren (funcomp xi2 xi1) M.
Proof.
  elim: M xi1 xi2=> /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. congr lam. rewrite IH.
    rewrite !ren_as_subst. apply: subst_ext. by case.
Qed.

Lemma ren_subst xi sigma M :
  ren xi (subst sigma M) = subst (funcomp (ren xi) sigma) M.
Proof.
  elim: M xi sigma=> /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. congr lam. rewrite IH.
    apply: subst_ext.
    move=> [|x] /=; [done|].
    rewrite !ren_ren.
    rewrite !ren_as_subst. by apply: subst_ext.
Qed.

Lemma subst_ren xi sigma M :
  subst sigma (ren xi M) = subst (funcomp sigma xi) M.
Proof.
  elim: M xi sigma=> /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. congr lam. rewrite IH.
    apply: subst_ext. by case.
Qed.

Lemma subst_subst sigma1 sigma2 M :
  subst sigma2 (subst sigma1 M) = subst (funcomp (subst sigma2) sigma1) M.
Proof.
  elim: M sigma1 sigma2=> /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. congr lam. rewrite IH.
    apply: subst_ext=> - [|x] /=; [done|].
    rewrite ren_subst subst_ren.
    by apply: subst_ext.
Qed.

Lemma allfv_trivial (P : nat -> Prop) t : (forall x, P x) -> allfv P t.
Proof.
  elim: t P=> /=; [by auto..|].
  move=> ? IH *. by apply: IH => - [|?].
Qed.

Lemma allfv_impl (P Q : nat -> Prop) t : 
  (forall x, P x -> Q x) -> allfv P t -> allfv Q t.
Proof.
  elim: t P Q => /=.
  - move=> >. by apply.
  - move=> ? IH1 ? IH2 > /[dup] /IH1 {}IH1 /IH2 {}IH2. tauto.
  - move=> > IH > H /=. apply: IH.
    by case.
Qed.

Lemma allfv_allfv_impl (P Q : nat -> Prop) t : 
  allfv (fun x => P x -> Q x) t -> allfv P t -> allfv Q t.
Proof.
  elim: t P Q => /=.
  - move=> >. by apply.
  - move=> ? IH1 ? IH2 > [/IH1 {}IH1] /IH2 {}IH2.
    by move=> [/IH1] {}IH1 /IH2 {}IH2.
  - move=> > IH > H /=. apply: IH.
    apply: allfv_impl H. by case.
Qed.

Lemma allfv_dec P M : (forall x, {P x} + {not (P x)}) -> {allfv P M} + {not (allfv P M)}.
Proof.
  elim: M P=> /=.
  - done.
  - move=> s IH1 t IH2 P /[dup] /(IH1 P) {}IH1 /(IH2 P) {}IH2. tauto.
  - move=> ? IH P H.
    case: (IH (scons True P)); [|by auto..].
    move=> [|?] /=; by auto.
Qed.

Lemma allfv_ren (P : nat -> Prop) xi t :
  allfv (funcomp P xi) t -> allfv P (ren xi t).
Proof.
  elim: t P xi.
  - done.
  - move=> ? IH1 ? IH2 > /= [??]. by auto.
  - move=> ? IH > /= H. apply: IH.
    by apply: allfv_impl H => - [|?].
Qed.

Lemma allfv_ren' (P : nat -> Prop) xi t :
  allfv P (ren xi t) -> allfv (funcomp P xi) t.
Proof.
  elim: t P xi.
  - done.
  - move=> ? IH1 ? IH2 > /= [??]. split.
    + by apply: IH1.
    + by apply: IH2.
  - move=> ? IH > /= /IH.
    by apply: allfv_impl => - [|?].
Qed.

Lemma allfv_subst (P : nat -> Prop) sigma t :
  allfv (fun x => allfv P (sigma x)) t -> allfv P (subst sigma t).
Proof.
  elim: t P sigma.
  - done.
  - move=> ? IH1 ? IH2 > /= [??]. by auto.
  - move=> ? IH > /= H. apply: IH.
    apply: allfv_impl H => - [|?] /= H; [done|].
    apply /allfv_ren. by apply: allfv_impl H.
Qed.

Lemma allfv_subst' (P : nat -> Prop) sigma t :
  allfv P (subst sigma t) -> allfv (fun x => allfv P (sigma x)) t.
Proof.
  elim: t P sigma.
  - done.
  - move=> ? IH1 ? IH2 > /= [??]. by auto.
  - move=> ? IH > /= /IH.
    apply: allfv_impl => - [|?] /=; [done|].
    move=> /allfv_ren'. by apply: allfv_impl.
Qed.

Lemma ext_allfv_subst sigma1 sigma2 t : allfv (fun x=> sigma1 x = sigma2 x) t ->
  subst sigma1 t = subst sigma2 t.
Proof.
  elim: t sigma1 sigma2.
  - by move=> > /= ?.
  - by move=> ? IH1 ? IH2 ?? /= [/IH1 -> /IH2 ->].
  - move=> ? IH > /= Hsigma. congr lam. apply: IH.
    apply: allfv_impl Hsigma.
    by move=> [|x] /= => [|->].
Qed.

Lemma ext_allfv_ren xi1 xi2 t : allfv (fun x=> xi1 x = xi2 x) t -> ren xi1 t = ren xi2 t.
Proof.
  move=> H. rewrite !ren_as_subst. apply: ext_allfv_subst.
  by apply: allfv_impl H => ? /= ->.
Qed.

Lemma allfv_list M : exists l, forall P, allfv P M <-> Forall P l.
Proof.
  elim: M.
  - move=> x. exists [x] => P /=. split.
    + move=> ?. by constructor.
    + by move=> /Forall_cons_iff [].
  - move=> > [l1 IH1] > [l2 IH2]. exists (l1 ++ l2) => P /=. split.
    + move=> [??]. apply /Forall_app. split.
      * by apply /IH1.
      * by apply /IH2.
    + by move=> /Forall_app [/IH1 ?] /IH2.
  - move=> > [l IH]. exists (concat (map (fun x => match x with 0 => [] | S x => [x] end) l)).
    move=> P /=. split.
    + move=> /IH. elim; first done.
      move=> [|x] ? /=; first done.
      by constructor.
    + move=> H. apply /IH. elim: l {IH} H; first done.
      move=> [|x] ? IH /=.
      * move=> ?. constructor; first done.
        by apply: IH.
      * move=> /Forall_cons_iff [??].
        constructor; first done.
        by apply: IH.
Qed.

Fixpoint size_tm (M : tm) :=
  match M with
  | var _ => 1
  | app M N => S (size_tm M) + (size_tm N)
  | lam M => S (size_tm M)
  end.

Lemma size_tm_ren xi M : size_tm (ren xi M) = size_tm M.
Proof.
  elim: M xi.
  - done.
  - move=> > IH1 ? IH2 ? /=. by rewrite IH1 IH2.
  - move=> > IH ? /=. by rewrite IH.
Qed.
