From Stdlib Require Import Lia List ZArith.
From PAR Require Import par_statement eval_property.

Import ListNotations.
Open Scope Z_scope.

Module PAR_EVAL.

Definition force_sign (s : sign) (l : list (sign * nat)) : list (sign * nat) :=
  map (fun x => (s, snd x)) l.

Fixpoint abs_sum_pairs (l : list (sign * nat)) : Z :=
  match l with
  | [] => 0
  | (_, n) :: tl => Z.of_nat n + abs_sum_pairs tl
  end.

Fixpoint pos_prefix_sum_pairs (l : list (sign * nat)) : Z :=
  match l with
  | [] => 0
  | (P, n) :: tl => Z.of_nat n + pos_prefix_sum_pairs tl
  | (N, _) :: _ => 0
  end.

Lemma value_of_consistent_signs :
  forall xs s,
    map fst xs = s ->
    value (combine s (map snd xs)) = value xs.
Proof.
  induction xs as [|[sg n] tl IH]; intros [|s tl']; simpl; intros H; try discriminate; auto.
  injection H as Hsg Htl.
  subst s.
  rewrite IH by exact Htl.
  destruct sg; lia.
Qed.

Lemma map_fst_app_inv :
  forall (l1 l2 : list sign) (xs : list (sign * nat)),
    map fst xs = l1 ++ l2 ->
    exists xs1 xs2,
      xs = xs1 ++ xs2 /\
      map fst xs1 = l1 /\
      map fst xs2 = l2.
Proof.
  intros l1 l2 xs H.
  exists (firstn (length l1) xs), (skipn (length l1) xs).
  repeat split.
  - symmetry. apply firstn_skipn.
  - rewrite <- firstn_map.
    rewrite H.
    rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_0, app_nil_r; auto.
  - rewrite <- skipn_map.
    rewrite H.
    rewrite skipn_app.
    rewrite skipn_all2 by lia.
    rewrite Nat.sub_diag.
    simpl.
    reflexivity.
Qed.

Lemma combine_full_prefix :
  forall {A B : Type} (l1 : list A) (v1 v2 : list B),
    length l1 = length v1 ->
    combine l1 (v1 ++ v2) = combine l1 v1.
Proof.
  intros A B l1.
  induction l1 as [|a l1 IH]; intros [|b v1] v2 Hlen; simpl in *; try discriminate; auto.
  injection Hlen as Hlen'.
  f_equal.
  apply IH.
  exact Hlen'.
Qed.

Lemma value_combine_snd_split :
  forall (s1 s2 : list sign) (xs1 xs2 : list (sign * nat)),
    length s1 = length xs1 ->
    value (combine (s1 ++ s2) (map snd (xs1 ++ xs2))) =
    value (combine s1 (map snd xs1)) +
    value (combine s2 (map snd xs2)).
Proof.
  intros s1 s2 xs1 xs2 Hlen.
  assert (Hlen_values : length s1 = length (map snd xs1)).
  { rewrite length_map. exact Hlen. }
  rewrite map_app.
  rewrite combine_app, value_app.
  rewrite combine_full_prefix by exact Hlen_values.
  rewrite Hlen_values.
  rewrite skipn_app.
  rewrite Nat.sub_diag.
  simpl.
  rewrite skipn_all2 by lia.
  reflexivity.
Qed.

Lemma force_sign_fst :
  forall s l,
    map fst (force_sign s l) = repeat s (length l).
Proof.
  induction l as [|a tl IH]; simpl; auto.
  rewrite IH. auto.
Qed.

Lemma force_sign_snd :
  forall s l,
    map snd (force_sign s l) = map snd l.
Proof.
  induction l as [|a tl IH]; simpl; auto.
  destruct a. simpl. rewrite IH. auto.
Qed.

Lemma value_force_sign_P :
  forall l,
    value (force_sign P l) = abs_sum_pairs l.
Proof.
  induction l as [|a tl IH]; simpl.
  - lia.
  - destruct a. simpl. rewrite IH. lia.
Qed.

Lemma value_force_sign_N :
  forall l,
    value (force_sign N l) = - abs_sum_pairs l.
Proof.
  induction l as [|a tl IH]; simpl.
  - lia.
  - destruct a. simpl. rewrite IH. lia.
Qed.

Lemma abs_sum_pairs_app :
  forall l1 l2,
    abs_sum_pairs (l1 ++ l2) = abs_sum_pairs l1 + abs_sum_pairs l2.
Proof.
  induction l1 as [|[sg n] tl IH]; simpl; intros; [lia|].
  rewrite IH. lia.
Qed.

Lemma pos_prefix_sum_pairs_P_block :
  forall mids y z2,
    map fst mids = repeat P (length mids) ->
    pos_prefix_sum_pairs (mids ++ (N, y) :: z2) = abs_sum_pairs mids.
Proof.
  induction mids as [|[sg n] tl IH]; intros y z2 Hmids; simpl in *.
  - reflexivity.
  - injection Hmids as Hsg Htl.
    subst sg.
    rewrite IH by exact Htl.
    lia.
Qed.

Lemma greedy_output_value_local :
  forall x mids y z2,
    value (combine (N :: repeat N (length mids) ++ P :: repeat P (length z2))
      (map snd ((N, x) :: mids ++ (N, y) :: z2))) =
    value ((N, x) :: force_sign N mids ++ (P, y) :: force_sign P z2).
Proof.
  intros x mids y z2.
  replace (map snd ((N, x) :: mids ++ (N, y) :: z2)) with
    (map snd ((N, x) :: force_sign N mids ++ (P, y) :: force_sign P z2)).
  2: {
    simpl.
    rewrite !map_app.
    simpl.
    rewrite force_sign_snd, force_sign_snd.
    reflexivity.
  }
  apply value_of_consistent_signs.
  simpl.
  rewrite !map_app.
  simpl.
  rewrite force_sign_fst, force_sign_fst.
  reflexivity.
Qed.

Lemma flip_candidate_value :
  forall pre x mids y z2,
    map fst mids = repeat P (length mids) ->
    pre + value ((N, x) :: force_sign N mids ++ (P, y) :: force_sign P z2) =
    pre - Z.of_nat x - 2 * pos_prefix_sum_pairs (mids ++ (N, y) :: z2) + abs_sum_pairs (mids ++ (N, y) :: z2).
Proof.
  intros pre x mids y z2 Hmids.
  replace ((N, x) :: force_sign N mids ++ (P, y) :: force_sign P z2) with
    (((N, x) :: force_sign N mids) ++ (P, y) :: force_sign P z2) by reflexivity.
  rewrite value_app.
  remember 2 as two.
  simpl.
  rewrite pos_prefix_sum_pairs_P_block by auto.
  rewrite value_force_sign_N, value_force_sign_P.
  rewrite abs_sum_pairs_app.
  simpl.
  lia.
Qed.

Lemma par_fix_spec :
  forall l pre,
    let '(abs_sum, pos_sum, max_sum) := par_fix l pre in
    abs_sum = abs_sum_pairs l /\
    pos_sum = pos_prefix_sum_pairs l /\
    pre + value l <= max_sum.
Proof.
  induction l as [|[s n] tl IH]; intros pre; simpl.
  - repeat split; lia.
  - destruct s.
    + destruct (par_fix tl (pre + Z.of_nat n)) as [[abs_sum pos_sum] max_sum] eqn:Hfix.
      specialize (IH (pre + Z.of_nat n)).
      rewrite Hfix in IH.
      simpl in IH.
      destruct IH as [Habs [Hpos Hmax]].
      repeat split.
      * rewrite Habs. lia.
      * rewrite Hpos. lia.
      * rewrite Z.add_assoc. exact Hmax.
    + destruct (par_fix tl (pre - Z.of_nat n)) as [[abs_sum pos_sum] max_sum] eqn:Hfix.
      specialize (IH (pre - Z.of_nat n)).
      rewrite Hfix in IH.
      simpl in IH.
      destruct IH as [Habs [Hpos Hmax]].
      repeat split.
      * rewrite Habs. lia.
      * rewrite Z.add_assoc. eapply Z.le_trans.
        -- exact Hmax.
        -- apply Z.le_max_l.
Qed.

Lemma par_fix_max_suffix :
  forall prefix l pre,
    let '(_, _, max_sum_suffix) := par_fix l (pre + value prefix) in
    max_sum_suffix <= let '(_, _, max_sum) := par_fix (prefix ++ l) pre in max_sum.
Proof.
  induction prefix as [|[s n] prefix IH]; intros l pre; simpl.
  - replace (pre + 0) with pre by lia.
    destruct (par_fix l pre) as [[abs_sum pos_sum] max_sum_suffix].
    lia.
  - destruct s.
    + specialize (IH l (pre + Z.of_nat n)).
      destruct (par_fix (prefix ++ l) (pre + Z.of_nat n)) as [[abs_sum pos_sum] max_sum] eqn:Hmid.
      destruct (par_fix l (pre + Z.of_nat n + value prefix)) as [[abs_sum_suffix pos_sum_suffix] max_sum_suffix] eqn:Hsuffix.
      rewrite Z.add_assoc, Hsuffix.
      simpl.
      exact IH.
    + specialize (IH l (pre - Z.of_nat n)).
      destruct (par_fix (prefix ++ l) (pre - Z.of_nat n)) as [[abs_sum pos_sum] max_sum] eqn:Hmid.
      destruct (par_fix l (pre - Z.of_nat n + value prefix)) as [[abs_sum_suffix pos_sum_suffix] max_sum_suffix] eqn:Hsuffix.
      unfold Z.sub in Hsuffix.
      rewrite Z.add_assoc, Hsuffix.
      eapply Z.le_trans.
      * exact IH.
      * apply Z.le_max_l.
Qed.

Lemma par_fix_flip_bound :
  forall pre x mids y z2,
    map fst mids = repeat P (length mids) ->
    pre + value ((N, x) :: force_sign N mids ++ (P, y) :: force_sign P z2) <=
    let '(_, _, max_sum) := par_fix ((N, x) :: mids ++ (N, y) :: z2) pre in max_sum.
Proof.
  intros pre x mids y z2 Hmids.
  simpl.
  destruct (par_fix (mids ++ (N, y) :: z2) (pre - Z.of_nat x)) as [[abs_sum pos_sum] max_sum] eqn:Hfix.
  pose proof (par_fix_spec (mids ++ (N, y) :: z2) (pre - Z.of_nat x)) as Hspec.
  rewrite Hfix in Hspec.
  simpl in Hspec.
  destruct Hspec as [Habs [Hpos _]].
  rewrite Habs, Hpos.
  replace
    (pre + (- Z.of_nat x + value (force_sign N mids ++ (P, y) :: force_sign P z2)))
    with (pre + value ((N, x) :: force_sign N mids ++ (P, y) :: force_sign P z2)) by reflexivity.
  rewrite flip_candidate_value by exact Hmids.
  apply Z.le_max_r.
Qed.

Lemma value_le_par_algo :
  forall xs,
    value xs <= par_algo xs.
Proof.
  intros xs.
  unfold par_algo.
  destruct (par_fix xs 0) as [[abs_sum pos_sum] max_sum] eqn:Hfix.
  pose proof (par_fix_spec xs 0) as Hspec.
  rewrite Hfix in Hspec.
  simpl in Hspec.
  lia.
Qed.

Lemma par_algo_flip_candidate :
  forall prefix x mids y z2,
    map fst mids = repeat P (length mids) ->
    value (prefix ++ (N, x) :: force_sign N mids ++ (P, y) :: force_sign P z2) <=
    par_algo (prefix ++ (N, x) :: mids ++ (N, y) :: z2).
Proof.
  intros prefix x mids y z2 Hmids.
  unfold par_algo.
  eapply (Z.le_trans _ (let '(_, _, max_sum) := par_fix ((N, x) :: mids ++ (N, y) :: z2) (value prefix) in max_sum)).
  - rewrite value_app.
    apply par_fix_flip_bound.
    exact Hmids.
  - destruct (par_fix ((N, x) :: mids ++ (N, y) :: z2) (value prefix)) as [[abs_sum pos_sum] max_sum_suffix] eqn:Hsuffix.
    change (max_sum_suffix <= (let '(_, _, max_sum) := par_fix (prefix ++ (N, x) :: mids ++ (N, y) :: z2) 0 in max_sum)).
    pose proof (par_fix_max_suffix prefix ((N, x) :: mids ++ (N, y) :: z2) 0) as Hbound.
    Opaque par_fix. simpl in Hbound. Transparent par_fix.
    rewrite Hsuffix in Hbound.
    simpl in Hbound.
    exact Hbound.
Qed.

Theorem par_algo_greedy_eval :
  forall l l' xs,
    greedy_eval l l' ->
    map fst xs = l ->
    value (combine l' (map snd xs)) <= par_algo xs.
Proof.
  intros l l' xs Hgreedy Hmap.
  revert xs Hmap.
  induction Hgreedy as [l | l1 l2 n]; intros xs Hmap.
  - rewrite value_of_consistent_signs with (xs:=xs) (s:=l) by exact Hmap.
    apply value_le_par_algo.
  - destruct (map_fst_app_inv l1 (N :: repeat P n ++ N :: l2) xs Hmap)
      as [xs1 [xsrest [Hxs [Hprefix Hrest]]]].
    subst xs.
    destruct xsrest as [|[s x] rest].
    { simpl in Hrest. discriminate. }
    destruct s.
    { simpl in Hrest. discriminate. }
    simpl in Hrest.
    injection Hrest as Hrest.
    destruct (map_fst_app_inv (repeat P n) (N :: l2) rest Hrest)
      as [mids [rest2 [Hrest_eq [Hmids Hrest2]]]].
    subst rest.
    destruct rest2 as [|[s y] z2].
    { simpl in Hrest2. discriminate. }
    destruct s.
    { simpl in Hrest2. discriminate. }
    simpl in Hrest2.
    assert (Hlen_z2 : length l2 = length z2).
    {
      apply (f_equal (@length sign)) in Hrest2.
      simpl in Hrest2.
      rewrite length_map in Hrest2.
      lia.
    }
    rewrite <- Hprefix.
    rewrite Hlen_z2.
    rewrite value_combine_snd_split with
      (s1:=map fst xs1)
      (s2:=N :: repeat N n ++ P :: repeat P (length z2))
      (xs1:=xs1)
      (xs2:=(N, x) :: mids ++ (N, y) :: z2) by apply length_map.
    rewrite value_of_consistent_signs with (xs:=xs1) (s:=map fst xs1) by reflexivity.
    assert (Hlen_mids : n = length mids).
    {
      apply (f_equal (@length sign)) in Hmids.
      rewrite length_map in Hmids.
      rewrite repeat_length in Hmids.
      lia.
    }
    rewrite Hlen_mids.
    rewrite greedy_output_value_local.
    rewrite <- value_app.
    rewrite Hlen_mids in Hmids.
    apply par_algo_flip_candidate.
    exact Hmids.
Qed.

Fixpoint split_first_neg (l : list (sign * nat)) : option (list (sign * nat) * nat * list (sign * nat)) :=
  match l with
  | [] => None
  | (P, n) :: tl =>
      match split_first_neg tl with
      | Some (mids, y, z2) => Some ((P, n) :: mids, y, z2)
      | None => None
      end
  | (N, n) :: tl => Some ([], n, tl)
  end.

Lemma split_first_neg_some :
  forall l mids y z2,
    split_first_neg l = Some (mids, y, z2) ->
    l = mids ++ (N, y) :: z2 /\
    map fst mids = repeat P (length mids).
Proof.
  induction l as [|[s n] tl IH]; intros mids y z2 Hsplit; simpl in Hsplit; try discriminate.
  destruct s.
  - destruct (split_first_neg tl) as [[[mids' y'] z2']|] eqn:Htl; try discriminate.
    injection Hsplit as Hmids Hy Hz2. subst mids y z2.
    destruct (IH _ _ _ eq_refl) as [-> Hfst].
    split.
    + reflexivity.
    + simpl. rewrite Hfst. reflexivity.
  - injection Hsplit as Hmids Hy Hz2. subst mids y z2.
    split.
    + reflexivity.
    + reflexivity.
Qed.

Lemma split_first_neg_none :
  forall l,
    split_first_neg l = None ->
    map fst l = repeat P (length l).
Proof.
  induction l as [|[s n] tl IH]; intros Hsplit; simpl in *; auto.
  destruct s.
  - destruct (split_first_neg tl) as [[[mids y] z2]|] eqn:Htl; try discriminate.
    simpl. rewrite IH by exact Hsplit. reflexivity.
  - discriminate.
Qed.

Lemma lift_greedy_eval_cons :
  forall a l l',
    greedy_eval l l' ->
    greedy_eval (a :: l) (a :: l').
Proof.
  intros a l l' H.
  destruct H.
  - apply greedy_eval_refl.
  - replace (a :: (l1 ++ N :: repeat P n ++ N :: l2)) with
      ((a :: l1) ++ N :: repeat P n ++ N :: l2) by reflexivity.
    replace (a :: (l1 ++ N :: repeat N n ++ P :: repeat P (length l2))) with
      ((a :: l1) ++ N :: repeat N n ++ P :: repeat P (length l2)) by reflexivity.
    apply greedy_eval_flip.
Qed.

Lemma par_fix_shift :
  forall l pre delta,
    let '(abs_sum1, pos_sum1, max_sum1) := par_fix l (pre + delta) in
    let '(abs_sum2, pos_sum2, max_sum2) := par_fix l pre in
    abs_sum1 = abs_sum2 /\
    pos_sum1 = pos_sum2 /\
    max_sum1 = max_sum2 + delta.
Proof.
  induction l as [|[s n] tl IH]; intros pre delta; simpl.
  - repeat split; lia.
  - destruct s.
    + destruct (par_fix tl (pre + delta + Z.of_nat n)) as [[abs_sum1 pos_sum1] max_sum1] eqn:H1.
      destruct (par_fix tl (pre + Z.of_nat n)) as [[abs_sum2 pos_sum2] max_sum2] eqn:H2.
      specialize (IH (pre + Z.of_nat n) delta).
      replace (pre + delta + Z.of_nat n) with (pre + Z.of_nat n + delta) in H1 by lia.
      rewrite H1, H2 in IH.
      simpl in IH.
      destruct IH as [Habs [Hpos Hmax]].
      repeat split; lia.
    + destruct (par_fix tl (pre + delta - Z.of_nat n)) as [[abs_sum1 pos_sum1] max_sum1] eqn:H1.
      destruct (par_fix tl (pre - Z.of_nat n)) as [[abs_sum2 pos_sum2] max_sum2] eqn:H2.
      specialize (IH (pre - Z.of_nat n) delta).
      replace (pre + delta - Z.of_nat n) with (pre - Z.of_nat n + delta) in H1 by lia.
      rewrite H1, H2 in IH.
      simpl in IH.
      destruct IH as [Habs [Hpos Hmax]].
      repeat split.
      * lia.
      * rewrite Hmax, Habs, Hpos.
        rewrite <- Z.add_max_distr_r.
        lia.
Qed.

Lemma par_algo_P :
  forall n tl,
    par_algo ((P, n) :: tl) = Z.of_nat n + par_algo tl.
Proof.
  intros n tl.
  unfold par_algo.
  destruct (par_fix tl (Z.of_nat n)) as [[abs_sum1 pos_sum1] max_sum1] eqn:H1.
  destruct (par_fix tl 0) as [[abs_sum2 pos_sum2] max_sum2] eqn:H2.
  pose proof (par_fix_shift tl 0 (Z.of_nat n)) as Hshift.
  replace (0 + Z.of_nat n) with (Z.of_nat n) in Hshift by lia.
  rewrite H1, H2 in Hshift.
  simpl. rewrite H1. lia.
Qed.

Lemma par_algo_N_formula :
  forall n tl,
    par_algo ((N, n) :: tl) =
    Z.max (- Z.of_nat n + par_algo tl)
      (- Z.of_nat n - 2 * pos_prefix_sum_pairs tl + abs_sum_pairs tl).
Proof.
  intros n tl.
  unfold par_algo.
  destruct (par_fix tl (- Z.of_nat n)) as [[abs_sum1 pos_sum1] max_sum1] eqn:H1.
  destruct (par_fix tl 0) as [[abs_sum2 pos_sum2] max_sum2] eqn:H2.
  pose proof (par_fix_shift tl 0 (- Z.of_nat n)) as Hshift.
  pose proof (par_fix_spec tl 0) as Hspec.
  replace (0 + - Z.of_nat n) with (- Z.of_nat n) in Hshift by lia.
  rewrite H1, H2 in Hshift.
  rewrite H2 in Hspec.
  destruct Hspec as [Habs [Hpos Hmax]].
  simpl. rewrite H1.
  destruct Hshift as [Habs' [Hpos' Hmax']].
  rewrite Hmax', <- Hpos, Hpos'.
  lia.
Qed.

Lemma par_algo_all_positive :
  forall l,
    map fst l = repeat P (length l) ->
    par_algo l = abs_sum_pairs l.
Proof.
  induction l as [|[s n] tl IH]; intros Hsigns; simpl in *.
  - reflexivity.
  - injection Hsigns as Hs Htl.
    subst s.
    rewrite par_algo_P.
    rewrite IH by exact Htl.
    lia.
Qed.

Lemma pos_prefix_sum_pairs_all_positive :
  forall l,
    map fst l = repeat P (length l) ->
    pos_prefix_sum_pairs l = abs_sum_pairs l.
Proof.
  induction l as [|[s n] tl IH]; intros Hsigns; simpl in *.
  - reflexivity.
  - injection Hsigns as Hs Htl.
    subst s.
    rewrite IH by exact Htl.
    lia.
Qed.

Fixpoint par_witness (l : list (sign * nat)) : list (sign * nat) :=
  match l with
  | [] => []
  | (P, n) :: tl => (P, n) :: par_witness tl
  | (N, x) :: tl =>
      let tail_witness := par_witness tl in
      match split_first_neg tl with
      | None => (N, x) :: tail_witness
      | Some (mids, y, z2) =>
          let current := (N, x) :: force_sign N mids ++ (P, y) :: force_sign P z2 in
          if Z.leb (value ((N, x) :: tail_witness)) (value current)
          then current
          else (N, x) :: tail_witness
      end
  end.

Lemma par_witness_values :
  forall l,
    map snd (par_witness l) = map snd l.
Proof.
  induction l as [|[s n] tl IH]; simpl; auto.
  destruct s.
  - simpl. rewrite IH. reflexivity.
  - destruct (split_first_neg tl) as [[[mids y] z2]|] eqn:Hsplit.
    + simpl.
      destruct (Z.leb (- Z.of_nat n + value (par_witness tl))
                      (- Z.of_nat n + value (force_sign N mids ++ (P, y) :: force_sign P z2)));
        simpl.
      * destruct (split_first_neg_some _ _ _ _ Hsplit) as [Htl _].
        rewrite Htl. simpl. rewrite !map_app. simpl.
        rewrite force_sign_snd, force_sign_snd. reflexivity.
      * rewrite IH. reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.

Lemma par_witness_greedy_eval :
  forall l,
    greedy_eval (map fst l) (map fst (par_witness l)).
Proof.
  induction l as [|[s n] tl IH]; simpl.
  - apply greedy_eval_refl.
  - destruct s.
    + apply lift_greedy_eval_cons. exact IH.
    + destruct (split_first_neg tl) as [[[mids y] z2]|] eqn:Hsplit.
      * destruct (Z.leb (- Z.of_nat n + value (par_witness tl))
                      (- Z.of_nat n + value (force_sign N mids ++ (P, y) :: force_sign P z2))); simpl.
        -- destruct (split_first_neg_some _ _ _ _ Hsplit) as [-> Hmids].
           simpl. rewrite !map_app.
           simpl. rewrite force_sign_fst, force_sign_fst.
           rewrite Hmids.
           replace (length z2) with (length (map fst z2)).
           apply greedy_eval_flip with (l1:=[]).
           apply length_map.
        -- apply lift_greedy_eval_cons. exact IH.
      * apply lift_greedy_eval_cons. exact IH.
Qed.

Lemma par_witness_peval :
  forall l,
    peval l (par_witness l).
Proof.
  intros l.
  split.
  - apply greedy_eval_sound.
    apply par_witness_greedy_eval.
  - unfold values.
    symmetry.
    apply par_witness_values.
Qed.

Lemma current_value_formula :
  forall n mids y z2,
    map fst mids = repeat P (length mids) ->
    - Z.of_nat n + value (force_sign N mids ++ (P, y) :: force_sign P z2) =
    - Z.of_nat n - 2 * pos_prefix_sum_pairs (mids ++ (N, y) :: z2) + abs_sum_pairs (mids ++ (N, y) :: z2).
Proof.
  intros n mids y z2 Hmids.
  pose proof (flip_candidate_value 0 n mids y z2 Hmids) as Hflip.
  simpl in Hflip.
  exact Hflip.
Qed.

Lemma abs_sum_pairs_ge0 : forall l, abs_sum_pairs l >= 0.
Proof.
  induction l; simpl; try destruct a; lia.
Qed.

Lemma par_witness_value :
  forall l,
    value (par_witness l) = par_algo l.
Proof.
  induction l as [|[s n] tl IH]; simpl.
  - reflexivity.
  - destruct s.
    + simpl. rewrite IH, par_algo_P. reflexivity.
    + destruct (split_first_neg tl) as [[[mids y] z2]|] eqn:Hsplit.
      * destruct (split_first_neg_some _ _ _ _ Hsplit) as [Htl Hmids].
        pose proof (current_value_formula n mids y z2 Hmids) as Hcurr.
        rewrite par_algo_N_formula, <- IH.
        rewrite <- Htl in Hcurr.
        rewrite <- Hcurr.
        remember (- Z.of_nat n + value (par_witness tl)).
        remember (- Z.of_nat n + value (force_sign N mids ++ (P, y) :: force_sign P z2)).
        destruct (z <=? z0) eqn:E.
        {
          simpl. rewrite <- Heqz0. lia.
        }
        {
          simpl. rewrite <- Heqz. lia.
        }
      * pose proof (split_first_neg_none tl Hsplit) as Hpos.
        simpl.
        rewrite IH.
        rewrite par_algo_N_formula.
        rewrite pos_prefix_sum_pairs_all_positive by exact Hpos.
        rewrite par_algo_all_positive by exact Hpos.
        symmetry.
        apply Z.max_l.
        pose proof (abs_sum_pairs_ge0 tl).
        lia.
Qed.

Close Scope Z_scope.

End PAR_EVAL.
