From Stdlib Require Import Relations List Lia PeanoNat Permutation Wellfounded.
Import ListNotations.
Require Import ssreflect ssrfun.

Arguments nth_error_split {A l n a}.
Arguments Permutation_nil_cons {A l x}.
Arguments in_split {A x}.

(* point-wise list concatenation *)
Fixpoint merge {X : Type} (Gamma : list (list X)) (Delta : list (list X)) : list (list X) :=
  match Gamma with
  | nil => Delta
  | cons u Gamma =>
    match Delta with
    | nil => cons u Gamma
    | cons v Delta => cons (u ++ v) (merge Gamma Delta)
    end
  end.

Lemma Forall2E {X Y : Type} {P : X -> Y -> Prop} l1 l2 : Forall2 P l1 l2 ->
  match l1 with
  | nil => l2 = nil
  | cons x l1 =>
      match l2 with
      | nil => False
      | cons y l2 => P x y /\ Forall2 P l1 l2
      end
  end.
Proof.
  by case.
Qed.

Lemma Forall2_trans {X Y Z : Type} (P : X -> Y -> Prop) (Q : Y -> Z -> Prop) (R : X -> Z -> Prop) l1 l2 l3 :
  (forall x y z, P x y -> Q y z -> R x z) -> Forall2 P l1 l2 -> Forall2 Q l2 l3 -> Forall2 R l1 l3.
Proof.
  move=> HPQR H. elim: H l3.
  - move=> ? /Forall2E ->. by constructor.
  - move=> > ??? [|? l3] /Forall2E; [done|].
    move=> [? ?]. constructor; by eauto.
Qed.

Lemma Forall2_map_l {X Y Z : Type} (P : X -> Y -> Prop) (f : Z -> X) l1 l2 :
  Forall2 (fun x y => P (f x) y) l1 l2 -> Forall2 P (map f l1) l2.
Proof.
  elim.
  - constructor.
  - move=> * /=. by constructor.
Qed.

Lemma Forall2_map_r {X Y Z : Type} (P : X -> Y -> Prop) (f : Z -> Y) l1 l2 :
  Forall2 (fun x y => P x (f y)) l1 l2 -> Forall2 P l1 (map f l2).
Proof.
  elim.
  - constructor.
  - move=> * /=. by constructor.
Qed.

Lemma Forall2_eq {X : Type} (P : X -> X -> Prop) l :
  Forall (fun x => P x x) l -> Forall2 P l l.
Proof. elim; by constructor. Qed.

Lemma merge_nil_r {X : Type} (Gamma : list (list X)) : merge Gamma nil = Gamma.
Proof.
  by case: Gamma.
Qed.

Lemma cons_app {X : Type} (x : X) x1s x2s : x :: x1s ++ x2s = [x] ++ x1s ++ x2s.
Proof. done. Qed.

Lemma map_neq_nil {X Y : Type} {f : X -> Y} l : map f l <> [] -> l <> [].
Proof.
  by case: l.
Qed.

Lemma nth_merge {X : Type} (Gamma1 Gamma2 : list (list X)) x :
  nth x (merge Gamma1 Gamma2) nil = nth x Gamma1 nil ++ nth x Gamma2 nil.
Proof.
  elim: x Gamma1 Gamma2.
  - by move=> [|??] [|??]; rewrite /= ?app_nil_r.
  - by move=> x IH [|??] [|??]; rewrite /= ?app_nil_r.
Qed.

Lemma In_nth_merge_l {X : Type} (Gamma2 Gamma1 : list (list X)) A x :
  In A (nth x Gamma1 nil) -> In A (nth x (merge Gamma1 Gamma2) nil).
Proof.
  move=> ?. rewrite nth_merge. apply /in_app_iff. by left.
Qed.

Lemma In_nth_merge_r {X : Type} (Gamma1 Gamma2 : list (list X)) A x :
  In A (nth x Gamma2 nil) -> In A (nth x (merge Gamma1 Gamma2) nil).
Proof.
  move=> ?. rewrite nth_merge. apply /in_app_iff. by right.
Qed.

Lemma nth_map_seq_lt {X : Type} {f : nat -> X} {i n d} : i < n -> nth i (map f (seq 0 n)) d = f i.
Proof.
  suff: (forall k, i < n -> nth i (map f (seq k n)) d = f (k + i)).
  { move=> /(_ 0). by apply. }
  elim: n i.
  - lia.
  - move=> n IH [|i] k ? /=.
    + by rewrite Nat.add_0_r.
    + rewrite IH; [lia|].
      by rewrite Nat.add_succ_r.
Qed.

Lemma nth_map_seq_ge {X : Type} {f : nat -> X} {i n d} : i >= n -> nth i (map f (seq 0 n)) d = d.
Proof.
  suff: (forall k, i >= n -> nth i (map f (seq k n)) d = d).
  { move=> /(_ 0). by apply. }
  elim: n i.
  - by case.
  - move=> n IH [|i] k ? /=.
    + lia.
    + by rewrite IH; [lia|].
Qed.

Lemma In_nth {X : Type} {n l} {x : X} : In x (nth n l []) ->
  exists l1 ys1 ys2 l2, l = l1 ++ (ys1 ++ x :: ys2) :: l2 /\ length l1 = n.
Proof.
  elim: n l.
  - move=> [|y l] /=; first done.
    move=> /in_split [ys1] [ys2] ->.
    by exists nil, ys1, ys2, l.
  - move=> n IH [|y l] /=; first done.
    move=> /IH [l1] [ys1] [ys2] [l2] [->] <-.
    by exists (y :: l1), ys1, ys2, l2.
Qed.

Lemma nth_middle_neq {X : Type} {n l1 l2 d} (x y : X) :
  n <> length l1 ->
  nth n (l1 ++ x :: l2) d = nth n (l1 ++ y :: l2) d.
Proof.
  elim: n l1.
  * by case.
  * move=> n IH [|??] /= ?; first done.
    apply: IH. lia.
Qed.

Fixpoint insert {X : Type} (x : X) n l :=
  match n with
  | 0 =>
    match l with
    | [] => [[x]]
    | xs :: l => (x :: xs) :: l
    end
  | S n =>
    match l with
    | [] => [] :: insert x n l
    | xs :: l => xs :: insert x n l
    end
  end.

Lemma nth_insert_neq {X : Type} {x : X} n1 n2 l : n1 <> n2 -> nth n1 (insert x n2 l) [] = nth n1 l [].
Proof.
  elim: n2 n1 l.
  - by move=> [|[|n1]] [|??] /=.
  - move=> n2 IH [|n1] [|??] /= ?; [done|done|..].
    * rewrite IH; [lia|]. by case: (n1).
    * apply: IH. lia.
Qed.

Lemma nth_insert {X : Type} {x : X} n l :
  nth n (insert x n l) [] = x :: nth n l [].
Proof.
  elim: n l.
  - by case.
  - move=> n IH [|??] /=; rewrite IH; by case: (n).
Qed.

Lemma nth_error_combine {X Y : Type} {n} {l1 : list X} {l2 : list Y} {x y} : nth_error (combine l1 l2) n = Some (x, y) <->
  (nth_error l1 n = Some x /\ nth_error l2 n = Some y).
Proof.
  split.
  - elim: l1 l2 n.
    + by move=> [|??] [|?] /=.
    + move=> ?? IH [|??] [|n] /= ?; [split; congruence..|].
      by apply: IH.
  - elim: l1 l2 n.
    + by move=> [|??] [|?] [] /=.
    + move=> ?? IH [|??] [|?] /= []; [congruence..|].
      move=> *. by apply: IH.
Qed.

Lemma map_nil {X Y : Type} (f : X -> Y) : map f [] = [].
Proof. done. Qed.

Lemma list_sum_cons n ns : list_sum (n :: ns) = n + list_sum ns.
Proof. done. Qed.

Lemma nth_error_length_neq {X Y : Type} (l1 : list X) (l2 : list Y) n : 
  nth_error l1 n <> None ->
  nth_error l2 n = None ->
  length l1 <> length l2.
Proof.
  move=> /nth_error_Some ? /nth_error_None ?. lia.
Qed.

Lemma Forall2_concat {X Y : Type} (P : X -> Y -> Prop) (l1s : list (list X)) (l2s : list (list Y)) :
  Forall2 (Forall2 P) l1s l2s -> Forall2 P (concat l1s) (concat l2s).
Proof.
  elim; first done.
  move=> * /=. by apply: Forall2_app.
Qed.

Lemma In_In_combine_l {X Y : Type} {x : X} l1 l2 : In x l1 -> length l1 = length l2 -> exists (y : Y), In (x, y) (combine l1 l2).
Proof.
  elim: l1 l2; first done.
  move=> ?? IH [|??] /=; first done.
  move=> [?|/IH].
  - subst=> ?. eexists. by left.
  - move=> H [/H] [??].
    eexists. right. by eassumption.
Qed.

Lemma In_In_combine_r {X Y : Type} {y : Y} l1 l2 : In y l2 -> length l1 = length l2 -> exists (x : X), In (x, y) (combine l1 l2).
Proof.
  elim: l2 l1; first done.
  move=> ?? IH [|??] /=; first done.
  move=> [?|/IH].
  - subst=> ?. eexists. by left.
  - move=> H [/H] [??].
    eexists. right. by eassumption.
Qed.

Lemma Forall2_Forall {X Y : Type} (P : X -> Y -> Prop) l1 l2 :
  (Forall (fun xy => P (fst xy) (snd xy)) (combine l1 l2) /\ length l1 = length l2) <-> Forall2 P l1 l2.
Proof.
  split.
  - elim: l1 l2.
    + by move=> [|??] [].
    + move=> ?? IH [|??] [] /=; first done.
      move=> /Forall_cons_iff [??] [?].
      constructor; first done.
      by apply: IH.
  - elim; first done.
    move=> > ?? /= [? ->]. by split; [constructor|].
Qed.

Lemma Forall2_exists_exists_Forall2 {X Y Z : Type} (P : X -> Y -> Z -> Prop) l1 l2 :
  Forall2 (fun x y => exists z, P x y z) l1 l2 ->
  exists zs, Forall2 (fun z xy => P (fst xy) (snd xy) z) zs (combine l1 l2).
Proof.
  elim.
  - by exists nil.
  - move=> > [z ?] ? [zs ?]. exists (z :: zs). by constructor.
Qed.

Lemma Permutation_Forall {A : Type} (P : A -> Prop) (l1 l2 : list A) : Permutation l1 l2 -> Forall P l1 -> Forall P l2.
Proof.
  elim.
  - done.
  - move=> > ?? /Forall_cons_iff [??]. by constructor; auto.
  - move=> > /Forall_cons_iff [? /Forall_cons_iff [??]]. by do ? constructor.
  - by auto.
Qed.

Lemma nth_skipn {A : Type} n1 n2 (a : A) l : nth n1 (skipn n2 l) a = nth (n2 + n1) l a.
Proof.
  elim: n2 l; first done.
  move=> n2 IH [|??] /=.
  - by case: (n1).
  - by apply: IH.
Qed.

Lemma concat_cons {A : Type} (l1 : list A) ls : concat (l1 :: ls) = l1 ++ concat ls.
Proof. done. Qed.

Lemma Permutation_eq {X : Type} {l1 l2 : list X} : l1 = l2 -> Permutation l1 l2.
Proof. by move=> ->. Qed.

Lemma Forall2_permutation_app {X Y : Type} (P : X -> Y -> Prop) l l' l1 l2 : Forall2 P l l' -> Permutation l (l1 ++ l2) ->
  exists l'1 l'2, Permutation l' (l'1 ++ l'2) /\ Forall2 P l1 l'1 /\ Forall2 P l2 l'2.
Proof.
  move=> H. elim: H l1 l2.
  { move=> > /Permutation_nil /app_eq_nil [-> ->]. by exists nil, nil. }
  move=> x y {}l {}l' Hxy ? IH l1 l2.
  have : In x (x :: l) by left.
  move=> /(@Permutation_in X) + /[dup] => /[apply] /in_app_iff [].
  - move=> /in_split [l3] [l4] ?. subst.
    rewrite -app_assoc /=.
    move=> /(@Permutation_app_inv X nil).
    rewrite app_assoc=> /IH [l'3] [l'4] [?].
    move=> [/Forall2_app_inv_l] [l'31] [l'32] [?] [?] *. subst.
    exists (l'31 ++ y :: l'32), l'4. split; [|split].
    + rewrite -app_assoc /=.
      apply: (Permutation_app_middle [_] nil).
      by rewrite !app_assoc.
    + apply: Forall2_app; first done.
      by constructor.
    + done.
  - move=> /in_split [l3] [l4] ?. subst.
    rewrite app_assoc /=.
    move=> /(@Permutation_app_inv X nil).
    rewrite -app_assoc=> /IH [l'3] [l'4] [?] [?].
    move=> /Forall2_app_inv_l [l'41] [l'42] [?] [?] *. subst.
    exists l'3, (l'41 ++ y :: l'42). split; [|split].
    + rewrite app_assoc /=.
      apply: (Permutation_app_middle [_] nil).
      by rewrite -!app_assoc.
    + done.
    + apply: Forall2_app; first done.
      by constructor.
Qed.

Lemma Permutation_remove_elt {X : Type} {x : X} {Delta1 xs Delta2 Gamma xi} f:
  (forall x1 x2, xi x1 = xi x2 -> x1 = x2) ->
  (forall y, Permutation (nth y (Delta1 ++ (x :: xs) :: Delta2) [] ++ f y) (nth (xi y) Gamma [])) ->
  exists Gamma1 : list (list X),
    length Gamma1 = xi (length Delta1) /\
    (exists (ys1 ys2 : list X) (Gamma2 : list (list X)),
      Gamma = Gamma1 ++ (ys1 ++ x :: ys2) :: Gamma2 /\
      (forall y,
        Permutation
          (nth y (Delta1 ++ xs :: Delta2) [] ++ f y)
          (nth (xi y) (Gamma1 ++ (ys1 ++ ys2) :: Gamma2) []))).
Proof.
  move=> Hxi H.
  have : In x (nth (xi (length Delta1)) Gamma []).
  { have := H (length Delta1). rewrite nth_middle /=.
    move=> /(@Permutation_in _ _ _ x). apply. by left. }
  move=> /In_nth [Gamma1] [ys1] [ys2] [Gamma2] [?] HG1.
  subst Gamma. exists Gamma1. split; first done.
  exists ys1, ys2, Gamma2. split; first done.
  move=> y. have /= := H y.
  have [->|Hy] : (y = length Delta1) \/ (y <> length Delta1) by lia.
  - rewrite -HG1 !nth_middle. by apply: (@Permutation_app_inv _ nil).
  - congr Permutation.
    + congr List.app. by apply: nth_middle_neq.
    + apply: nth_middle_neq. move=> ?. apply: Hy. apply: Hxi. lia.
Qed.

Lemma Permutation_concat_split {X : Type} xi (Deltas : list (list (list X))) Gamma :
  (forall x1 x2, xi x1 = xi x2 -> x1 = x2) ->
  (forall x, Permutation (concat (map (fun Delta => nth x Delta []) Deltas)) (nth (xi x) Gamma [])) ->
  exists Delta' Deltas',
    (forall x, Permutation (nth x Gamma []) (concat (map (fun Delta => nth x Delta []) (Delta' :: Deltas')))) /\
    Forall2 (fun Delta Delta' => forall x, nth x Delta [] = nth (xi x) Delta' []) Deltas Deltas'.
Proof.
  move=> Hxi.
  elim /(Nat.measure_induction _ (fun Deltas => list_sum (map (fun Delta => 1 + list_sum (map (@length X) Delta)) Deltas))) : Deltas Gamma.
  move=> [|Delta Deltas].
  { move=> _ Gamma HG. exists Gamma, nil. split.
    + move=> x /=. by rewrite app_nil_r.
    + done. }
  move=> IH Gamma.
  have [|[Delta1 [x [xs [Delta2 Hx]]]]] : (forall x, nth x Delta [] = []) \/
    exists Delta1 x xs Delta2, Delta = Delta1 ++ (x :: xs) :: Delta2.
  { elim: (Delta).
    - left. by case.
    - move=> [|??] ? [?|].
      + by left=> - [|?] /=.
      + move=> [?] [?] [?] [?] ->.
        right. by eexists (nil :: _), _, _, _.
      + right. by eexists nil, _, _, _.
      + move=> [?] [?] [?] [?] ->.
        right. by eexists ((_ :: _) :: _), _, _, _. }
  - move=> HD /= HDDs.
    have := IH Deltas _ Gamma. case.
    + move=> /=. lia.
    + move=> x. apply: Permutation_trans; [|by apply: HDDs x].
      by rewrite HD.
    + move=> Delta' [Deltas'] [IH1 IH2].
      exists Delta', ([] :: Deltas'). split=> /=.
      * move=> [|x]; by apply: IH1.
      * constructor; [|done].
        move=> x. by move: (xi x) => [|?]; rewrite HD.
  - subst Delta. move=> /= Hx.
    have [Gamma1 [HD1 [ys1 [ys2 [Gamma2 [? HG]]]]]] := Permutation_remove_elt _ Hxi Hx.
    subst Gamma.
    have := IH ((Delta1 ++ xs :: Delta2) :: Deltas) _ (Gamma1 ++ (ys1 ++ ys2) :: Gamma2). case.
    + rewrite /= !map_app !list_sum_app /=. lia.
    + done.
    + move=> Delta'' [[|Delta' Deltas']] [IH1 /Forall2E]; [done|].
      move=> [IH2 ?].
      exists Delta'', ((insert x (xi (length Delta1)) Delta') :: Deltas'). split.
      * move=> y. have /= := IH1 y.
        have [->|Hy] : (y = length Gamma1) \/ (y <> length Gamma1) by lia.
        ** rewrite !nth_middle HD1 nth_insert. by apply: Permutation_elt.
        ** have : y <> xi (length Delta1) by lia.
           move=> /nth_insert_neq ->.
           apply: Permutation_trans.
           by rewrite (nth_middle_neq _ (ys1 ++ ys2)).
      * constructor; [|done].
        move=> y. have := IH2 y.
        have [->|Hy] : (y = length Delta1) \/ (y <> length Delta1) by lia.
        ** rewrite !nth_middle nth_insert. by move=> ->.
        ** have : xi y <> xi (length Delta1).
           { move=> ?. apply: Hy. by apply: Hxi. }
           move=> /nth_insert_neq -> <-.
           by apply: nth_middle_neq.
Qed.

Lemma concat_nils {A: Type} (l : list (list A)) : (forall x, In x l -> x = []) -> concat l = [].
Proof.
  move=> ?.
  by apply /concat_nil_Forall /Forall_forall.
Qed.

Lemma Forall2_concat_split {A B : Type} (P : A -> B -> Prop) ls l' :
  Forall2 P l' (concat ls) ->
  exists l's,
    l' = concat l's /\
    Forall2 (Forall2 P) l's ls.
Proof.
  elim: ls l'.
  - move=> [|??] /= H; last by inversion H.
    by exists [].
  - move=> l ls IH l' /=.
    move=> /Forall2_app_inv_r [l'1] [l'2] [?] [/IH {}IH] ?.
    subst.
    move: IH => [l's] [->] ?.
    exists (l'1 :: l's). split; first done.
    by constructor.
Qed.

Lemma nth_error_Forall2 {A B : Type} (P : A -> B -> Prop) l1 l2 :
  length l1 = length l2 ->
  (forall n a b, nth_error l1 n = Some a -> nth_error l2 n = Some b -> P a b) ->
  Forall2 P l1 l2.
Proof.
  elim: l1 l2; first by case.
  move=> ?? IH [|??] /=; first done.
  move=> [/IH] {}IH H. constructor.
  - by apply: (H 0).
  - apply: IH => - n *.
    by apply: (H (S n)).
Qed.

Lemma Forall2_nth_error {A B : Type} (P : A -> B -> Prop) l1 l2 :
  Forall2 P l1 l2 ->
  (forall n a b, nth_error l1 n = Some a -> nth_error l2 n = Some b -> P a b).
Proof.
  elim; first by case.
  move=> > ?? IH [|n] > /=; first by congruence.
  by apply: IH.
Qed.
