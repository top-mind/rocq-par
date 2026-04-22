From Stdlib Require Import List ZArith Lia.
From PAR Require Import par_statement eval_property.
Import ListNotations.

Definition neg_pair (p : sign * nat) : sign * nat :=
  let '(s, v) := p in (neg s, v).

Fixpoint to (t : tree) : list (sign * nat) :=
  match t with
  | V v => [(P, v)]
  | T l P r => to l ++ to r
  | T l N r => to l ++ map neg_pair (to r)
  end.

Definition teval (l1 l2 : list (sign * nat)) : Prop :=
  exists t, l1 = from P t /\ l2 = to t.

Theorem tvalue_value : forall t : tree, tvalue t = value (to t).
Proof.
  induction t.
  - simpl. lia.
  - destruct s; simpl;
    rewrite value_app, IHt1, IHt2; auto.
    unfold Z.sub. f_equal. clear. induction (to t2); auto.
    destruct a, s; simpl; lia.
Qed.

Lemma values_neg_pair : forall l, values (map neg_pair l) = values l.
Proof.
  induction l as [| [s v] tl IH]; simpl; auto.
  now rewrite IH.
Qed.

Lemma signs_neg_pair : forall l, signs (map neg_pair l) = map neg (signs l).
Proof.
  induction l as [| [s v] tl IH]; simpl; auto.
  now rewrite IH.
Qed.

Lemma neg_pair_involutive : forall l, map neg_pair (map neg_pair l) = l.
Proof.
  induction l as [| [s v] tl IH]; simpl; auto.
  destruct s; simpl; now rewrite IH.
Qed.

Lemma eval_P_cons_inv : forall l l', eval (P :: l) (P :: l') -> eval l l'.
Proof.
  intros l l' H.
  remember (P :: l) as src eqn:Esrc.
  remember (P :: l') as dst eqn:Edst.
  revert l l' Esrc Edst.
  induction H; intros l0 l0' Esrc Edst.
  - discriminate.
  - destruct l as [| a l1], l' as [| b l2]; simpl in Esrc, Edst.
    + inversion Esrc; inversion Edst; subst. exact H0.
    + apply eval_len in H. simpl in H. discriminate.
    + apply eval_len in H. simpl in H. discriminate.
    + inversion Esrc; inversion Edst; subst.
      apply eval_P.
      * exact (IHeval1 _ _ eq_refl eq_refl).
      * exact H0.
  - destruct l as [| a l1], l' as [| b l2]; simpl in Esrc, Edst.
    + discriminate.
    + discriminate.
    + discriminate.
    + inversion Esrc; inversion Edst; subst.
      apply eval_N with (r':=r').
      * exact (IHeval1 _ _ eq_refl eq_refl).
      * exact H0.
      * reflexivity.
Qed.

Lemma peval_teval_aux :
  forall s v l l' src_tl dst_tl,
    eval l l' ->
    signs src_tl = l ->
    signs dst_tl = l' ->
    values src_tl = values dst_tl ->
    exists t,
      from s t = (s, v) :: src_tl /\
      to t = (P, v) :: dst_tl.
Proof.
  intros s v l l' src_tl dst_tl Heval.
  revert s v src_tl dst_tl.
  induction Heval; intros s0 v src_tl dst_tl Hsrc Hdst Hvals.
  - destruct src_tl as [| [ss sv] src_tl], dst_tl as [| [ds dv] dst_tl]; simpl in *; try discriminate.
    inversion Hsrc. inversion Hdst. subst.
    exists (V v). simpl. auto.
  - pose proof (eval_len _ _ Heval1) as Hlen.
    set (n := length l).
    set (src_l := firstn n src_tl).
    set (src_r := skipn n src_tl).
    set (dst_l := firstn n dst_tl).
    set (dst_r := skipn n dst_tl).
    assert (Hsrc_l : signs src_l = l).
    {
      unfold src_l, n.
      unfold signs.
      rewrite <- firstn_map.
      change (map fst src_tl) with (signs src_tl).
      rewrite Hsrc.
      rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_0, app_nil_r.
      reflexivity.
    }
    assert (Hdst_l : signs dst_l = l').
    {
      unfold dst_l, n.
      unfold signs.
      rewrite <- firstn_map.
      change (map fst dst_tl) with (signs dst_tl).
      rewrite Hdst.
      rewrite firstn_app, Hlen, firstn_all, Nat.sub_diag, firstn_0, app_nil_r.
      reflexivity.
    }
    assert (Hvals_l : values src_l = values dst_l).
    {
      unfold src_l, dst_l.
      unfold values.
      rewrite <- !firstn_map.
      change (map snd src_tl) with (values src_tl).
      change (map snd dst_tl) with (values dst_tl).
      now rewrite Hvals.
    }
    assert (Hsrc_r : signs src_r = P :: r).
    {
      unfold src_r, n.
      unfold signs.
      rewrite <- skipn_map.
      change (map fst src_tl) with (signs src_tl).
      rewrite Hsrc.
      rewrite skipn_app, skipn_all, Nat.sub_diag, skipn_0.
      reflexivity.
    }
    assert (Hdst_r : signs dst_r = P :: r').
    {
      unfold dst_r, n.
      unfold signs.
      rewrite <- skipn_map.
      change (map fst dst_tl) with (signs dst_tl).
      rewrite Hdst.
      rewrite skipn_app, Hlen, skipn_all, Nat.sub_diag, skipn_0.
      reflexivity.
    }
    assert (Hvals_r : values src_r = values dst_r).
    {
      unfold src_r, dst_r.
      unfold values.
      rewrite <- !skipn_map.
      change (map snd src_tl) with (values src_tl).
      change (map snd dst_tl) with (values dst_tl).
      now rewrite Hvals.
    }
    destruct src_r as [| [ss sv] src_rt] eqn:Esrc_r,
      dst_r as [| [ds dv] dst_rt] eqn:Edst_r;
      simpl in Hsrc_r, Hdst_r, Hvals_r; try discriminate.
    destruct ss, ds; simpl in Hsrc_r, Hdst_r; try discriminate.
    injection Hsrc_r as Hsrc_rt.
    injection Hdst_r as Hdst_rt.
    injection Hvals_r as Hsv Hvals_rt. subst dv.
    destruct (IHHeval1 s0 v src_l dst_l Hsrc_l Hdst_l Hvals_l) as [tl [Hfrom_l Hto_l]].
    destruct (IHHeval2 P sv src_rt dst_rt Hsrc_rt Hdst_rt Hvals_rt) as [tr [Hfrom_r Hto_r]].
    exists (T tl P tr). split.
    + simpl. rewrite Hfrom_l, Hfrom_r.
      subst src_l.
      rewrite <- Esrc_r.
      change ((s0, v) :: (firstn n src_tl ++ skipn n src_tl) = (s0, v) :: src_tl).
      rewrite firstn_skipn.
      reflexivity.
    + simpl. rewrite Hto_l, Hto_r.
      subst dst_l.
      rewrite <- Edst_r.
      change ((P, v) :: (firstn n dst_tl ++ skipn n dst_tl) = (P, v) :: dst_tl).
      rewrite firstn_skipn.
      reflexivity.
  - pose proof (eval_len _ _ Heval1) as Hlen.
    set (n := length l).
    set (src_l := firstn n src_tl).
    set (src_r := skipn n src_tl).
    set (dst_l := firstn n dst_tl).
    set (dst_r := skipn n dst_tl).
    assert (Hsrc_l : signs src_l = l).
    {
      unfold src_l, n.
      unfold signs.
      rewrite <- firstn_map.
      change (map fst src_tl) with (signs src_tl).
      rewrite Hsrc.
      rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_0, app_nil_r.
      reflexivity.
    }
    assert (Hdst_l : signs dst_l = l').
    {
      unfold dst_l, n.
      unfold signs.
      rewrite <- firstn_map.
      change (map fst dst_tl) with (signs dst_tl).
      rewrite Hdst.
      rewrite firstn_app, Hlen, firstn_all, Nat.sub_diag, firstn_0, app_nil_r.
      reflexivity.
    }
    assert (Hvals_l : values src_l = values dst_l).
    {
      unfold src_l, dst_l.
      unfold values.
      rewrite <- !firstn_map.
      change (map snd src_tl) with (values src_tl).
      change (map snd dst_tl) with (values dst_tl).
      now rewrite Hvals.
    }
    assert (Hsrc_r : signs src_r = N :: r).
    {
      unfold src_r, n.
      unfold signs.
      rewrite <- skipn_map.
      change (map fst src_tl) with (signs src_tl).
      rewrite Hsrc.
      rewrite skipn_app, skipn_all, Nat.sub_diag, skipn_0.
      reflexivity.
    }
    assert (Hdst_r : signs dst_r = N :: r'').
    {
      unfold dst_r, n.
      unfold signs.
      rewrite <- skipn_map.
      change (map fst dst_tl) with (signs dst_tl).
      rewrite Hdst.
      rewrite skipn_app, Hlen, skipn_all, Nat.sub_diag, skipn_0.
      reflexivity.
    }
    assert (Hvals_r : values src_r = values dst_r).
    {
      unfold src_r, dst_r.
      unfold values.
      rewrite <- !skipn_map.
      change (map snd src_tl) with (values src_tl).
      change (map snd dst_tl) with (values dst_tl).
      now rewrite Hvals.
    }
    destruct src_r as [| [ss sv] src_rt] eqn:Esrc_r,
      dst_r as [| [ds dv] dst_rt] eqn:Edst_r;
      simpl in Hsrc_r, Hdst_r, Hvals_r; try discriminate.
    destruct ss, ds; simpl in Hsrc_r, Hdst_r; try discriminate.
    injection Hsrc_r as Hsrc_rt.
    injection Hdst_r as Hdst_rt.
    injection Hvals_r as Hsv Hvals_rt. subst dv.
    destruct (IHHeval1 s0 v src_l dst_l Hsrc_l Hdst_l Hvals_l) as [tl [Hfrom_l Hto_l]].
    assert (Hdst_rt_unneg : signs (map neg_pair dst_rt) = r').
    {
      rewrite signs_neg_pair, Hdst_rt.
      match goal with
      | Hneg : map neg r' = r'' |- _ => rewrite <- Hneg, map_neg_neg
      end.
      reflexivity.
    }
    assert (Hvals_rt_unneg : values src_rt = values (map neg_pair dst_rt)).
    {
      rewrite values_neg_pair.
      exact Hvals_rt.
    }
    destruct (IHHeval2 N sv src_rt (map neg_pair dst_rt) Hsrc_rt Hdst_rt_unneg Hvals_rt_unneg)
      as [tr [Hfrom_r Hto_r]].
    exists (T tl N tr). split.
    + simpl. rewrite Hfrom_l, Hfrom_r.
      subst src_l.
      rewrite <- Esrc_r.
      change ((s0, v) :: (firstn n src_tl ++ skipn n src_tl) = (s0, v) :: src_tl).
      rewrite firstn_skipn.
      reflexivity.
    + simpl. rewrite Hto_l, Hto_r. simpl.
      rewrite neg_pair_involutive.
      subst dst_l.
      rewrite <- Edst_r.
      change ((P, v) :: (firstn n dst_tl ++ skipn n dst_tl) = (P, v) :: dst_tl).
      rewrite firstn_skipn.
      reflexivity.
Qed.

Lemma from_cons : forall s t, exists v tl, from s t = (s, v) :: tl.
Proof.
  intros s t.
  induction t as [w | tl IHl sg tr IHr].
  - exists w, []. reflexivity.
  - destruct IHl as [v [tl' Hfrom_l]].
    simpl.
    rewrite Hfrom_l. destruct sg; simpl.
    + exists v, (tl' ++ from P tr). reflexivity.
    + exists v, (tl' ++ from N tr). reflexivity.
Qed.

Lemma to_cons : forall t, exists v tl, to t = (P, v) :: tl.
Proof.
  intros t.
  induction t as [w | tl IHl sg tr IHr].
  - exists w, []. reflexivity.
  - destruct IHl as [v [tl' Hto_l]].
    simpl.
    rewrite Hto_l. destruct sg; simpl.
    + exists v, (tl' ++ to tr). reflexivity.
    + exists v, (tl' ++ map neg_pair (to tr)). reflexivity.
Qed.

Lemma from_to_values_eq : forall s t, values (from s t) = values (to t).
Proof.
  intros s t.
  revert s.
  induction t as [w | tl IHl sg tr IHr]; intros s; simpl.
  - reflexivity.
  - unfold values in *.
    destruct sg; simpl.
    + rewrite !map_app, (IHl s), (IHr P). reflexivity.
    + rewrite !map_app, values_neg_pair, (IHl s), (IHr N). reflexivity.
Qed.

Lemma from_to_cons_inv_split :
  forall s v t tl tl2,
    from s t = (s, v) :: tl ->
    to t = (P, v) :: tl2 ->
    eval (signs tl) (signs tl2) /\ values tl = values tl2.
Proof.
  intros s v t.
  revert s v.
  induction t as [w | tl IHl sg tr IHr]; intros s v tl0 tl2 Hfrom Hto.
  - simpl in Hfrom, Hto. inversion Hfrom; inversion Hto; subst.
    split; [apply eval_refl | reflexivity].
  - destruct sg.
    + destruct (from_cons s tl) as [vl [src_l Hfrom_l]].
      destruct (to_cons tl) as [wl [dst_l Hto_l]].
      destruct (from_cons P tr) as [vr [src_r Hfrom_r]].
      destruct (to_cons tr) as [wr [dst_r Hto_r]].
      simpl in Hfrom, Hto.
      rewrite Hfrom_l, Hfrom_r in Hfrom.
      rewrite Hto_l, Hto_r in Hto.
      injection Hfrom as Hhead_from Htail_from.
      injection Hto as Hhead_to Htail_to.
      subst vl wl tl0 tl2.
      assert (Hvrw : vr = wr).
      {
        pose proof (from_to_values_eq P tr) as Hrvals.
        rewrite Hfrom_r, Hto_r in Hrvals. simpl in Hrvals.
        inversion Hrvals. reflexivity.
      }
      subst wr.
      destruct (IHl s v src_l dst_l Hfrom_l Hto_l) as [Heval_l Hvals_l].
      destruct (IHr P vr src_r dst_r Hfrom_r Hto_r) as [Heval_r Hvals_r].
      split.
      * unfold signs. rewrite !map_app. simpl. apply eval_P; assumption.
      * unfold values. rewrite !map_app. simpl.
        change (map snd src_l) with (values src_l).
        change (map snd dst_l) with (values dst_l).
        change (map snd src_r) with (values src_r).
        change (map snd dst_r) with (values dst_r).
        now rewrite Hvals_l, Hvals_r.
    + destruct (from_cons s tl) as [vl [src_l Hfrom_l]].
      destruct (to_cons tl) as [wl [dst_l Hto_l]].
      destruct (from_cons N tr) as [vr [src_r Hfrom_r]].
      destruct (to_cons tr) as [wr [dst_r Hto_r]].
      simpl in Hfrom, Hto.
      rewrite Hfrom_l, Hfrom_r in Hfrom.
      rewrite Hto_l, Hto_r in Hto.
      injection Hfrom as Hhead_from Htail_from.
      injection Hto as Hhead_to Htail_to.
      subst vl wl tl0 tl2.
      assert (Hvrw : vr = wr).
      {
        pose proof (from_to_values_eq N tr) as Hrvals.
        rewrite Hfrom_r, Hto_r in Hrvals. simpl in Hrvals.
        inversion Hrvals. reflexivity.
      }
      subst wr.
      destruct (IHl s v src_l dst_l Hfrom_l Hto_l) as [Heval_l Hvals_l].
      destruct (IHr N vr src_r dst_r Hfrom_r Hto_r) as [Heval_r Hvals_r].
      split.
      * unfold signs. rewrite !map_app. simpl. apply eval_N with (r':=signs dst_r).
        -- exact Heval_l.
        -- exact Heval_r.
        -- rewrite signs_neg_pair. reflexivity.
      * unfold values. rewrite !map_app. simpl. rewrite values_neg_pair.
        change (map snd src_l) with (values src_l).
        change (map snd dst_l) with (values dst_l).
        change (map snd src_r) with (values src_r).
        change (map snd dst_r) with (values dst_r).
        now rewrite Hvals_l, Hvals_r.
Qed.

Theorem peval_teval :
  forall l1 l2 : list (sign * nat), normal l1 -> (peval l1 l2 <-> teval l1 l2).
Proof.
  intros l1 l2 Hn.
  destruct l1 as [| [s head_v] tl].
  - contradiction.
  - destruct s.
    2: contradiction.
    unfold peval, teval.
    split; intros H.
    + destruct H as [Heval Hvals].
      destruct l2 as [| [s2 v2] tl2].
      { apply eval_len in Heval. simpl in Heval. discriminate. }
      pose proof (eval_hd_eq _ _ _ _ Heval) as Hhd.
      destruct s2.
      * simpl in Hvals. inversion Hvals; subst.
        assert (Heval_tl : eval (signs tl) (signs tl2)).
        { apply eval_P_cons_inv. exact Heval. }
        destruct (peval_teval_aux P v2 (signs tl) (signs tl2) tl tl2 Heval_tl eq_refl eq_refl H1)
          as [t [Hfrom Hto]].
        exists t. split; symmetry; assumption.
      * inversion Hhd.
    + destruct H as [t [Hfrom Hto]].
      destruct (to_cons t) as [v2 [tl2 Hto_cons]].
      rewrite Hto_cons in Hto. subst l2.
      pose proof (from_to_values_eq P t) as Hvals_ft.
      rewrite <- Hfrom, Hto_cons in Hvals_ft. simpl in Hvals_ft.
      injection Hvals_ft as Hv Hvals_tl. subst v2.
      destruct (from_to_cons_inv_split P head_v t tl tl2 (eq_sym Hfrom) Hto_cons) as [Heval_tl _].
      split.
      * change (eval ([] ++ P :: signs tl) ([] ++ P :: signs tl2)).
        apply eval_P.
        -- apply eval_refl.
        -- exact Heval_tl.
      * simpl. now rewrite Hvals_tl.
Qed.

Lemma teval_normal :
  forall l1 l2 : list (sign * nat), teval l1 l2 -> normal l1.
Proof.
  intros l1 l2 [t [Hfrom _]].
  destruct (from_cons P t) as [v [tl Hcons]].
  rewrite Hcons in Hfrom.
  inversion Hfrom; subst.
  exact I.
Qed.

Corollary peval_to_teval :
  forall l1 l2 : list (sign * nat), normal l1 -> peval l1 l2 -> teval l1 l2.
Proof.
  intros l1 l2 Hnormal Hpeval.
  apply (proj1 (peval_teval l1 l2 Hnormal)).
  exact Hpeval.
Qed.

Corollary teval_to_peval :
  forall l1 l2 : list (sign * nat), normal l1 -> teval l1 l2 -> peval l1 l2.
Proof.
  intros l1 l2 Hnormal Hteval.
  apply (proj2 (peval_teval l1 l2 Hnormal)).
  exact Hteval.
Qed.