From Stdlib Require Import Lia List ZArith.
From PAR Require Import par_statement par_theorem par_eval.

Import ListNotations.
Open Scope Z_scope.

Fixpoint par_dp_fix (l : list (sign * nat)) : (Z * Z * Z) :=
  match l with
  | [] => (0, 0, 0)
  | (P, n) :: tl =>
      let z := Z.of_nat n in
      let '(sum_tl, dp0_tl, dp1_tl) := par_dp_fix tl in
      (sum_tl + z, dp0_tl + z, Z.max (dp1_tl - z) (dp0_tl + z))
  | (N, n) :: tl =>
      let z := Z.of_nat n in
      let '(sum_tl, dp0_tl, dp1_tl) := par_dp_fix tl in
      let sum := sum_tl + z in
      (sum, dp1_tl - z, sum)
  end.

Definition par_dp (l : list (sign * nat)) : Z :=
  let '(_, answer, _) := par_dp_fix l in
  answer.

Lemma par_fix_shift :
  forall l pre delta,
    par_fix l (pre + delta) =
    let '(abs_sum, pos_sum, max_sum) := par_fix l pre in
    (abs_sum, pos_sum, max_sum + delta).
Proof.
  intros.
  pose proof (PAR_EVAL.par_fix_shift l pre delta).
  destruct (par_fix l (pre + delta)) as [[abs_sum1 pos_sum1] max_sum1].
  destruct (par_fix l pre) as [[abs_sum2 pos_sum2] max_sum2].
  repeat f_equal; tauto.
Qed.

Lemma par_fix_pos_bound :
  forall l pre,
    let '(_, pos_sum, _) := par_fix l pre in
    0 <= pos_sum.
Proof.
  induction l as [|[s n] tl IH]; intros pre; simpl.
  - lia.
  - set (z := Z.of_nat n).
    destruct s.
    + destruct (par_fix tl (pre + z)) as [[abs_sum pos_sum] max_sum] eqn:Hfix.
      specialize (IH (pre + z)).
      rewrite Hfix in IH.
      simpl in IH.
      lia.
    + destruct (par_fix tl (pre - z)) as [[abs_sum pos_sum] max_sum] eqn:Hfix.
      lia.
Qed.

Opaque Z.mul.

Lemma par_fix_abs_bound :
  forall l pre,
    let '(abs_sum, _, max_sum) := par_fix l pre in
    max_sum <= pre + abs_sum.
Proof.
  induction l as [|[s n] tl IH]; intros pre; simpl.
  - lia.
  - set (z := Z.of_nat n).
    destruct s.
    + destruct (par_fix tl (pre + z)) as [[abs_sum pos_sum] max_sum] eqn:Hfix.
      specialize (IH (pre + z)).
      rewrite Hfix in IH.
      simpl in IH.
      lia.
    + destruct (par_fix tl (pre - z)) as [[abs_sum pos_sum] max_sum] eqn:Hfix.
      specialize (IH (pre - z)).
      rewrite Hfix in IH.
      pose proof (par_fix_pos_bound tl (pre - z)) as Hpos.
      rewrite Hfix in Hpos.
      apply Z.max_lub; lia.
Qed.

Lemma par_dp_fix_spec :
  forall l,
    let '(sum, dp0, dp1) := par_dp_fix l in
    let '(abs_sum, pos_sum, max_sum) := par_fix l 0 in
    sum = abs_sum /\
    dp0 = max_sum /\
    dp1 = Z.max max_sum (abs_sum - 2 * pos_sum).
Proof.
  induction l as [|[s n] tl IH]; simpl.
  - tauto.
  - set (z := Z.of_nat n).
    destruct s.
    1: pose proof (par_fix_shift tl 0 z) as Hshift; simpl in Hshift; rewrite Hshift.
    2: pose proof (par_fix_shift tl 0 (-z)) as Hshift; simpl in Hshift; rewrite Hshift.
    all:
      destruct (par_dp_fix tl) as [[sum_tl dp0_tl] dp1_tl] eqn:Hdp;
      destruct (par_fix tl 0) as [[abs_tl pos_tl] max_tl] eqn:Hfix;
      destruct IH as [Hsum [Hdp0 Hdp1]];
      repeat split; try lia.
      replace (abs_tl + z - 2 * 0) with (abs_tl + z) by lia.
      subst. symmetry. apply Z.max_r, Z.max_lub.
      1: pose proof (par_fix_abs_bound tl 0).
      2: pose proof (par_fix_pos_bound tl 0).
      all: rewrite Hfix in H; lia.
Qed.

Theorem par_dp_eq_par_algo :
  forall l,
    par_dp l = par_algo l.
Proof.
  intros; unfold par_dp, par_algo.
  pose proof (par_dp_fix_spec l) as Hspec.
  destruct (par_dp_fix l) as [[]].
  destruct (par_fix l 0) as [[]].
  tauto.
Qed.

Theorem par_dp_correct :
  correct par_dp.
Proof.
  split; unfold maximum, exists_maximum; intros; try rewrite par_dp_eq_par_algo; auto using par_algo_maximum, par_algo_exists_maximum.
Qed.
