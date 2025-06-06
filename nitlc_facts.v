(*
  facts about the non-idempotently typed lambda-calculus
*)

From Stdlib Require Import PeanoNat Lia List Relations Permutation ssreflect.
Import ListNotations.

From NonIdempotent Require Import facts ulc ulc_facts nitlc bag_equiv_facts.
Import NitlcNotations.

#[local] Arguments Permutation_in {A l l' x}.
#[local] Arguments in_split {A x l}.

(* useful case analysis principle *)
Lemma nitlcE Gamma M A : nitlc Gamma M A ->
  match M with
  | var x => In A (nth x Gamma nil)
  | app M N => exists Gamma' Deltas u,
      bag_equiv [Gamma] (Gamma' :: Deltas) /\
      nitlc Gamma' M (niarr u A) /\
      Forall2 (fun Delta B => nitlc Delta N B) Deltas u
  | lam M => exists u B,
      A = niarr u B /\
      nitlc (cons u Gamma) M B
  end.
Proof.
  case; firstorder done.
Qed.

(*
  Useful induction principle to show that a property (P Gamma M A)
  holds for all Gamma, M, A such that Gamma |- M : A.

  The proof is by induction on M.
*)
Lemma nitlc_ind' (P : environment -> tm -> nity -> Prop) :
  (forall Gamma x A,
    In A (nth x Gamma nil) -> 
    P Gamma (var x) A) ->
  (forall Gamma Deltas Gamma' M N u A,
    bag_equiv [Gamma] (Gamma' :: Deltas) ->
    nitlc Gamma' M (niarr u A) ->
    P Gamma' M (niarr u A) ->
    Forall2 (fun Delta B => nitlc Delta N B) Deltas u ->
    Forall2 (fun Delta B => P Delta N B) Deltas u ->
    P Gamma (app M N) A) ->
  (forall Gamma M u B,
    nitlc (u :: Gamma) M B ->
    P (u :: Gamma) M B ->
    P Gamma (lam M) (niarr u B)) ->
  forall Gamma M A, nitlc Gamma M A -> P Gamma M A.
Proof.
  move=> IH1 IH2 IH3 + M. elim: M.
  - move=> > /nitlcE ?. by apply: IH1.
  - move=> M IHM N IHN Gamma A.
    move=> /nitlcE [Gamma'] [Deltas] [u] [?] [HM HN].
    apply: IH2; try eassumption.
    + by apply: IHM.
    + apply: Forall2_impl HN => *. by apply: IHN.
  - move=> M IHM Gamma A /nitlcE.
    move=> [?] [?] [??]. subst A.
    apply: IH3; [assumption..|].
    by apply: IHM.
Qed.

(*
  Weakening Theorem
    If Delta is a sub-environment of Deltas, and Gamma equivalent to Deltas,
    then if Delta |- M : A, then Gamma |- M : A.

  The proof is by induction on the nitlc relation
  using the induction principle nitlc_ind'.
*)
Theorem nitlc_weakening Delta Deltas Gamma M A :
  In Delta Deltas ->
  bag_equiv [Gamma] Deltas ->
  nitlc Delta M A -> nitlc Gamma M A.
Proof.
  move=> ++ H. elim /nitlc_ind': H Gamma Deltas.
  - move=> ? x ? ? > ? /(_ x) /= Hx.
    constructor.
    move: Hx => /Permutation_sym /Permutation_in.
    rewrite app_nil_r.
    apply.
    apply /in_concat.
    eexists.
    split; last by eassumption.
    apply /in_map_iff.
    eexists.
    by split; last by eassumption.
  - move=> {}Gamma Deltas Gamma' {}M N u {}A.
    move=> H1Gamma IHM IH'M IHN IH'N Gamma'' Deltas' H2Gamma HGamma''.
    move: H2Gamma => /in_split => - [Deltas'1] [Deltas'2] ?. subst.
    have: bag_equiv [Gamma''] ((fold_right merge [] (Gamma' :: Deltas'1 ++ Deltas'2)) :: Deltas).
    { apply: bag_equiv_trans; first by eassumption.
      apply: bag_equiv_trans.
      { apply: bag_equiv_app; first done.
        by apply: (bag_equiv_app [_]); first by eassumption. }
      apply: bag_equiv_sym.
      apply: bag_equiv_trans.
      { apply: (bag_equiv_app [_]); last done.
        by apply: bag_equiv_merge. }
      rewrite /=. apply: (bag_equiv_middle Gamma' []).
      rewrite /= -app_assoc.
      apply: bag_equiv_app; first done.
      by apply: bag_equiv_app_comm. }
    move=> /nitlc_app. apply; last by eassumption.
    apply: (IH'M _ (Gamma' :: Deltas'1 ++ Deltas'2)); first by left.
    by apply: bag_equiv_merge.
  - move=> {}Gamma {}M u B IH'M IHM Gamma' Deltas HGamma HGamma'.
    constructor.
    move: HGamma => /in_split => - [Deltas1] [Deltas2] ?.
    subst Deltas.
    apply: (IHM _ (map (cons []) Deltas1 ++ (u :: Gamma) :: map (cons []) Deltas2)).
    + apply /in_app_iff. right.
      by left.
    + move=> [|x] /=.
      * rewrite app_nil_r.
        rewrite map_app /= !map_map /= concat_app /= !concat_nils ?app_nil_r; last done.
        all: by move=> ? /in_map_iff [?] [<-].
      * move: (HGamma' x).
        by rewrite /= !map_app /= !map_map /=.
Qed.

(*
  Renaming Theorem
    If xi is a an injective renaming function, and Gamma is a a xi-permutation of Delta,
    then if Gamma |- M : A, then Delta |- ren xi M : A.

  The proof is by induction on the nitlc relation
  using the induction principle nitlc_ind'.
*)
Theorem nitlc_renaming Gamma Delta xi A M :
  (forall x1 x2, xi x1 = xi x2 -> x1 = x2) ->
  (forall x, nth x Gamma nil = nth (xi x) Delta nil) ->
  nitlc Gamma M A ->
  nitlc Delta (ren xi M) A.
Proof.
  intros H1xi H2xi H.
  revert xi Delta H1xi H2xi.
  induction H as [ | Gamma Deltas Gamma' M N u A HGamma HM IHM HN IHN | Gamma M u B HN IH ] using nitlc_ind'.
  - intros xi Delta H1xi H2xi.
    cbn.
    constructor.
    rewrite <- H2xi.
    assumption.
  - intros xi Gamma'' H1xi H2xi.
    cbn.
    have : forall x, Permutation (concat (map (fun Delta => nth x Delta []) (Gamma' :: Deltas))) (nth (xi x) Gamma'' []).
    { move=> x. rewrite -H2xi. apply /Permutation_sym.
      have := HGamma x.
      by rewrite /= app_nil_r. }
    move: (H1xi) => /Permutation_concat_split /[apply].
    move=> [G0] [[|Gamma''' Deltas']].
    { by move=> [?] /Forall2_length. }
    move=> [HG''] /= /Forall2E [HG' /Forall2_flip HD].
    apply: (nitlc_app _ (merge G0 Gamma''') Deltas' _ _ u).
    + move=> x /=.
      by rewrite app_nil_r nth_merge -app_assoc.
    + apply: (nitlc_weakening Gamma''' [Gamma'''; _]).
      * by left.
      * by apply: (bag_equiv_fold_right_merge _ [_]).
      * by apply: IHM.
    + apply: Forall2_trans; [|by eassumption..].
      move=> > H' /=. by apply.
  - intros xi Delta H1xi H2xi.
    cbn.
    constructor.
    + apply IH.
      * intros [|x1] [|x2]; cbn; [lia..|].
        intros [= E].
        apply H1xi in E.
        lia.
      * intros [|x]; cbn.
        ** easy.
        ** now apply H2xi.
Qed.

(* swap the first two indices *)
Definition swap (x : nat) :=
  match x with
  | 0 => 1
  | 1 => 0
  | _ => x
  end.

(*
  Substitution Theorem
    If u is a list of types, Gamma is an environment, Gamma' is an environment equavalent to Gamma :: Thetas,
    and Thetas_i |- N : u_i,
    then if u :: Gamma |- M : A, then Gamma' |- M[0 := N] : A.

  The proof is by induction on the size of M.
  The induction principle nitlc_ind' does not suffice.
*)
Theorem nitlc_substitution u Gamma (Thetas : list environment) Gamma' M N A :
  (Forall2 (fun Theta B => nitlc Theta N B) Thetas u) ->
  bag_equiv [Gamma'] (Gamma :: Thetas) ->
  nitlc (u :: Gamma) M A ->
  nitlc Gamma' (subst (scons N var) M) A.
Proof.
  elim /(Nat.measure_induction _ size_tm): M u Gamma A Thetas Gamma' N. case.
  - move=> [|x] _ u Gamma A Thetas Gamma' N HThetas HGamma' /nitlcE /= Hx.
    + have [Theta [HTheta HN]] : exists Theta, In Theta Thetas /\ nitlc Theta N A.
      { elim: HThetas Hx; first done.
        move=> > ?? IH /= [<-|/IH [? [??]]].
        - eexists. by split; first by left.
        - firstorder. }
      apply: (nitlc_weakening Theta); [| eassumption | done].
      by right.
    + constructor.
      move: HGamma' => /bag_equiv_In_nth.
      by apply; last by left.
  - move=> M1 M2 IH u Gamma A Thetas Gamma' N HThetas HGamma'.
    move=> /nitlcE [Gamma''] [Deltas] [u'] [HuGamma] [HM1 HM2] /=.
    have [u1 [Gamma''' HGamma'']]: exists u1 Gamma''', bag_equiv [Gamma''] [u1 :: Gamma'''].
    { case: (Gamma'') => [|??].
      - exists [], []. by move=> [|[|x]].
      - by do 2 eexists. }
    set u2s := map (fun Delta => nth 0 Delta []) Deltas.
    set Deltas' := map (fun Delta => skipn 1 Delta) Deltas.
    have : Permutation u (u1 ++ concat u2s).
    { subst u2s.
      have /Permutation_trans := HuGamma 0.
      rewrite /= app_nil_r. apply.
      apply: Permutation_app; last done.
      have := HGamma'' 0.
      by rewrite /= !app_nil_r. }
    move: HThetas => /Forall2_Permutation_app_split /[apply].
    move=> [Theta1s] [Theta2s] [HThetas] [Hu1Thetas1].
    move=> /Forall2_concat_split [Theta2ss] [?] Hu2sTheta2ss.
    subst Theta2s.
    apply: (nitlc_app _ (fold_right merge Gamma''' Theta1s) (map (fun DeltaTheta2s => fold_right merge (fst DeltaTheta2s) (snd DeltaTheta2s)) (combine Deltas' Theta2ss))). (* NO to each Delta I have to merge all of Thetas2ss item *)
    + apply: bag_equiv_trans; first by eassumption.
      apply: bag_equiv_trans.
      { by apply: (bag_equiv_app [_]); last by eassumption. }
      apply: bag_equiv_sym.
      apply: bag_equiv_trans.
      { apply: (bag_equiv_app [_]); last done.
        by apply: bag_equiv_fold_right_merge. }
      apply: bag_equiv_trans.
      { apply: bag_equiv_app; first done.
        apply: bag_equiv_map_combine.
        - move: Hu2sTheta2ss => /Forall2_length ->.
          subst Deltas' u2s.
          by rewrite !length_map.
        - move=> ??. by apply: bag_equiv_fold_right_merge. }
      rewrite !app_assoc.
      apply: bag_equiv_app; last done.
      apply: bag_equiv_trans; first by apply: bag_equiv_app_comm.
      change (Gamma''' :: Theta1s) with ([Gamma'''] ++ Theta1s).
      rewrite !app_assoc.
      apply: bag_equiv_app; last done.
      apply: bag_equiv_trans; first by apply: bag_equiv_app_comm.
      apply: bag_equiv_sym.
      have : bag_equiv [u :: Gamma] ((u1 :: Gamma''') :: Deltas).
      { apply: bag_equiv_trans; first by eassumption.
        by apply: (bag_equiv_app [_] _ [_]). }
      by move=> /(bag_equiv_skipn 1).
    + apply: (IH _ _ _ Gamma''' _ _ (fold_right merge Gamma''' Theta1s)).
      * cbn. lia.
      * by apply: Hu1Thetas1.
      * by apply: bag_equiv_fold_right_merge.
      * apply: (nitlc_weakening _ [_]) HM1; first by left.
        by apply: bag_equiv_sym.
    + subst Deltas'.
      apply Forall2_map_l.
      apply: nth_error_Forall2.
      { rewrite length_combine length_map.
        move: Hu2sTheta2ss => /Forall2_length ->.
        subst u2s.
        rewrite length_map Nat.min_id.
        apply: Forall2_length.
        by eassumption. }
      move=> n [Delta' Theta2s] B /nth_error_combine [HDeltasn HTheta2ssn] Hu'n /=.
      move: Hu2sTheta2ss HTheta2ssn => /Forall2_nth_error /[apply] HN.
      move: HM2 (Hu'n) => /Forall2_nth_error /[apply] HM2.
      rewrite nth_error_map in HDeltasn.
      case EDelta: (nth_error Deltas n) HDeltasn => [Delta|] HDeltasn; last done.
      have ?: option_map (fun l => nth 0 l []) (nth_error Deltas n) = Some (nth 0 Delta []).
      { by rewrite EDelta. }
      destruct Delta as [|u2 Delta].
      { (* Delta is empty *)
        apply: IH.
        - cbn. lia.
        - apply: HN.
          subst u2s.
          by rewrite nth_error_map EDelta /=.
        - by apply: bag_equiv_fold_right_merge.
        - move: (HM2 _ EDelta).
          apply: (nitlc_weakening _ ([] :: [[] :: Delta'])); first by left.
          apply: (bag_equiv_app [] [_] [_] [_]); last done.
          by case. }
      apply: (IH _ _ _ Delta).
      * cbn. lia.
      * apply: HN.
        subst u2s.
        by rewrite nth_error_map EDelta /=.
      * apply: bag_equiv_trans; first by apply: bag_equiv_fold_right_merge.
        apply: (bag_equiv_app [_] _[_]); last done.
        by move: HDeltasn => [<-].
      * by apply: HM2.
  - move=> M IH u Gamma A Thetas Gamma' N.
    move=> HThetas HGamma' /nitlcE [v] [B] [?] HM.
    subst A.
    cbn.
    constructor.
    have ->: subst (scons (var 0) (fun x : nat => ren S (scons N var x))) M =
      subst (scons (ren S N) var) (ren swap M).
    { rewrite subst_ren /=. apply: subst_ext.
      by move=> [|[|x]] /=. }
    apply: (IH _ _ u (v :: Gamma) _ (map (cons []) Thetas)).
    + rewrite size_tm_ren /=. lia.
    + apply: Forall2_map_l.
      apply: Forall2_impl HThetas.
      move=> Theta C. by apply: nitlc_renaming; [lia|].
    + move=> [|x] /=.
      * rewrite map_map concat_nils; last done.
        by move=> ? /= /in_map_iff [?] [].
      * move: (HGamma' x). by rewrite /= map_map /=.
    + apply: nitlc_renaming HM.
      * move=> [|[|x1]] [|[|x2]]; cbn; lia.
      * by move=> [|[|x]].
Qed.

(*
  Subject Reduction Theorem
    If M reduces to to N, and Gamma |- M : A, then Gamma |- N : A.

  The proof is by induction on the step relation using the Substitution Theorem.
*)
Theorem nitlc_subject_reduction Gamma M N A : step M N -> nitlc Gamma M A -> nitlc Gamma N A.
Proof.
  intros HMN.
  revert Gamma A.
  induction HMN as [ | M M' ? IH | M M' N HMM' IH | M N N' ? IH ].
  - intros Gamma A H%nitlcE.
    destruct H as [Gamma' [Deltas [u [HGamma [HM%nitlcE HN]]]]].
    destruct HM as [u' [A' [[=Eu Ea] HM]]].
    subst u' A'.
    revert HM.
    eapply nitlc_substitution.
    + eassumption.
    + assumption.
  - intros Gamma A H%nitlcE.
    destruct H as [u [B [EA H]]].
    rewrite EA.
    constructor.
    apply IH.
    apply H.
  - intros Gamma A H%nitlcE.
    destruct H as [Gamma' [Deltas [u [HGamma [HM HN]]]]].
    econstructor.
    + apply HGamma.
    + apply IH.
      apply HM.
    + apply HN.
  - intros Gamma A H%nitlcE.
    destruct H as [Gamma' [Deltas [u [HGamma [HM HN]]]]].
    econstructor.
    + apply HGamma.
    + apply HM.
    + revert HN.
      apply Forall2_impl.
      apply IH.
Qed.

Check nitlc_subject_reduction.
Print Assumptions nitlc_subject_reduction.
