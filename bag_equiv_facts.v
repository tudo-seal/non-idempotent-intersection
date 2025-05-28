(* facts about the bag_equiv relation *)

From Stdlib Require Import PeanoNat Lia List Permutation ssreflect.
Import ListNotations.
From NonIdempotent Require Import facts nitlc.

#[local] Arguments Permutation_in {A l l' x}.
#[local] Arguments Permutation_nil_cons {A l x}.
#[local] Arguments in_split {A x l}.
#[local] Arguments Permutation_cons_app_inv {A l l1 l2 a}.

Lemma bag_equiv_trans Gammas1 Gammas2 Gammas3 :
  bag_equiv Gammas1 Gammas2 ->
  bag_equiv Gammas2 Gammas3 ->
  bag_equiv Gammas1 Gammas3.
Proof.
  move=> H1 H2 x. move: (H1 x) (H2 x). apply: Permutation_trans.
Qed.

Lemma bag_equiv_sym Gammas1 Gammas2 :
  bag_equiv Gammas1 Gammas2 ->
  bag_equiv Gammas2 Gammas1.
Proof.
  move=> H x. by apply: Permutation_sym.
Qed.

Lemma bag_equiv_app Gammas1 Gammas2 Deltas1 Deltas2 :
  bag_equiv Gammas1 Deltas1 ->
  bag_equiv Gammas2 Deltas2 ->
  bag_equiv (Gammas1 ++ Gammas2) (Deltas1 ++ Deltas2).
Proof.
  move=> H1 H2 x. rewrite !map_app !concat_app. by apply: Permutation_app.
Qed.

Lemma bag_equiv_app_comm Gammas1 Gammas2 :
  bag_equiv (Gammas1 ++ Gammas2) (Gammas2 ++ Gammas1).
Proof.
  move=> x. rewrite !map_app !concat_app. by apply: Permutation_app_comm.
Qed.

Lemma bag_equiv_merge (Deltas : list (environment)) :
  bag_equiv [fold_right merge [] Deltas] Deltas.
Proof.
  elim: Deltas; first by case.
  move=> Delta Deltas IH /= x.
  have /= := IH x.
  rewrite !app_nil_r.
  clear.
  rewrite nth_merge=> ?.
  by apply: Permutation_app.
Qed.

Lemma bag_equiv_fold_right_merge Gamma Deltas : bag_equiv [fold_right merge Gamma Deltas] (Gamma :: Deltas).
Proof.
  elim: Deltas Gamma.
  - cbn. by intros Gamma x.
  - move=> Delta Deltas IH Gamma x.
    rewrite /= !app_nil_r nth_merge.
    apply: (Permutation_app_middle _ []).
    have /= := IH Gamma x.
    by rewrite app_nil_r.
Qed.


Lemma bag_equiv_In_nth Gamma Delta Deltas x A :
  bag_equiv [Gamma] Deltas ->
  In A (nth x Delta []) ->
  In Delta Deltas ->
  In A (nth x Gamma []).
Proof.
  move=> /(_ x) /=. rewrite app_nil_r.
  move=> /Permutation_sym /Permutation_in H ??.
  apply: H. apply /in_concat.
  do ? econstructor; [|by eassumption].
  apply /in_map_iff.
  by do ? econstructor.
Qed.

Lemma bag_equiv_skipn n Gamma Deltas :
  bag_equiv [Gamma] Deltas ->
  bag_equiv [skipn n Gamma] (map (skipn n) Deltas).
Proof.
  move=> H x. move: (H (n + x))=> /=.
  rewrite nth_skipn map_map.
  congr Permutation. congr concat.
  apply: map_ext=> ?. by rewrite nth_skipn.
Qed.

Lemma bag_equiv_middle l l1s l2s l3s l4s :
  bag_equiv (l1s ++ l2s) (l3s ++ l4s) ->
  bag_equiv (l1s ++ l :: l2s) (l3s ++ l :: l4s).
Proof.
  move=> ?.
  change (l1s ++ l :: l2s) with (l1s ++ [l] ++ l2s).
  change (l3s ++ l :: l4s) with (l3s ++ [l] ++ l4s).
  rewrite app_assoc.
  apply: bag_equiv_trans.
  { apply: bag_equiv_app; last done.
    by apply: bag_equiv_app_comm. }
  rewrite -app_assoc.
  apply: bag_equiv_trans.
  { by apply: bag_equiv_app; last by eassumption. }
  rewrite app_assoc.
  apply: bag_equiv_trans.
  { apply: bag_equiv_app; last done.
    by apply: bag_equiv_app_comm. }
  by rewrite -app_assoc.
Qed.

Lemma Forall2_Permutation_app_split P (l : list nity) l1 l2 (ls : list environment) :
  Forall2 P ls l ->
  Permutation l (l1 ++ l2) ->
  exists l1s l2s,
    bag_equiv ls (l1s ++ l2s) /\
    Forall2 P l1s l1 /\
    Forall2 P l2s l2.
Proof.
  move=> H. elim: H l1 l2.
  - move=> [|? l1] [|? l2]; [|by move=> /Permutation_nil_cons..].
    move=> _. exists [], []. by split.
  - move=> Gamma A {}ls {}l ?? IH l1 l2.
    move=> /[dup] /Permutation_in - /(_ A (or_introl eq_refl)) /in_app_iff [|].
    + move=> /in_split [l3] [l4] ->.
      rewrite -app_assoc /=.
      move=> /Permutation_cons_app_inv.
      rewrite app_assoc.
      move=> /IH [l1s] [l2s] [Hls] [Hl1s Hl2s].
      exists ((firstn (length l3) l1s) ++ Gamma :: (skipn (length l3) l1s)), l2s.
      split; [|split].
      * rewrite -app_assoc /=. apply: (bag_equiv_middle _ []).
        by rewrite app_assoc firstn_skipn.
      * apply: Forall2_app; [|constructor].
        ** move: Hl1s => /Forall2_app_inv_r [l3s] [l4s].
           move=> [+] [_] ?. subst l1s.
           move=> /[dup] /Forall2_length <-.
           by rewrite firstn_app Nat.sub_diag /= app_nil_r firstn_all.
        ** done.
        ** move: Hl1s => /Forall2_app_inv_r [l3s] [l4s].
           move=> [+] [Hl4] ?. subst l1s.
           move=> /Forall2_length <-.
           by rewrite skipn_app Nat.sub_diag /= skipn_all.
      * done.
    + move=> /in_split [l3] [l4] ->.
      rewrite app_assoc /=.
      move=> /Permutation_cons_app_inv.
      rewrite -app_assoc.
      move=> /IH [l1s] [l2s] [Hls] [Hl1s Hl2s].
      exists l1s, ((firstn (length l3) l2s) ++ Gamma :: (skipn (length l3) l2s)).
      split; [|split].
      * rewrite app_assoc /=. apply: (bag_equiv_middle _ []).
        by rewrite -app_assoc firstn_skipn.
      * done.
      * apply: Forall2_app; [|constructor].
        ** move: Hl2s => /Forall2_app_inv_r [l3s] [l4s].
           move=> [+] [_] ?. subst l2s.
           move=> /[dup] /Forall2_length <-.
           by rewrite firstn_app Nat.sub_diag /= app_nil_r firstn_all.
        ** done.
        ** move: Hl2s => /Forall2_app_inv_r [l3s] [l4s].
           move=> [+] [Hl4] ?. subst l2s.
           move=> /Forall2_length <-.
           by rewrite skipn_app Nat.sub_diag /= skipn_all.
Qed.

Lemma bag_equiv_map_combine (l1 : list environment) (l2s : list (list environment)) f : 
  length l1 = length l2s ->
  (forall a b, bag_equiv [f (a, b)] (a :: b)) ->
  bag_equiv (map f (combine l1 l2s)) (l1 ++ concat l2s).
Proof.
  move=> + Hf.
  elim: l1 l2s.
  - by move=> [|??] /= ?; last done.
  - move=> ?? IH [|??] /=; first done.
    move=> [/IH] {}IH.
    apply: bag_equiv_trans.
    { by apply: (bag_equiv_app [_]); last by eassumption. }
    cbn.
    apply: (bag_equiv_app [_] _ [_]); first done.
    rewrite !app_assoc.
    apply: bag_equiv_trans; last done.
    apply: bag_equiv_app; last done.
    by apply: bag_equiv_app_comm.
Qed.

Lemma bag_equiv_app_concat Deltas Gammas Gammas's :
  length Gammas = length Gammas's ->
  Forall2 (fun Delta '(Gamma, Gammas') => bag_equiv [Delta] (Gamma :: Gammas')) Deltas (combine Gammas Gammas's) ->
  bag_equiv Deltas (Gammas ++ concat Gammas's).
Proof.
  move=> H H' x.
  elim: Deltas Gammas Gammas's H H'.
  - by move=> [|??] [|??] /= ? /Forall2_length /=.
  - move=> ?? IH [|??] [|??] /= ? /[dup] /Forall2_length /= ?; [done..|].
    move=> /Forall2E [] /(_ x) /= H /IH ->; [lia|].
    rewrite app_nil_r in H.
    apply: Permutation_trans; [by apply: Permutation_app; [eassumption|]|].
    rewrite !map_app !concat_app !app_assoc. apply: Permutation_app_tail.
    rewrite -!app_assoc. apply: Permutation_app_head.
    by apply: Permutation_app_comm.
Qed.
