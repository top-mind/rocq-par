From Stdlib Require Import List ZArith.

From PAR Require Import par_statement tree_eval par_theorem.

Open Scope Z_scope.

Theorem correct_tree_correct :
  forall A, correct A -> tree_correct A.
Proof.
  intros A [Hmaximum Hexists].
  split.
  - intros l t Hfrom.
    assert (Hteval : teval l (to t)).
    {
      exists t.
      split; [exact Hfrom | reflexivity].
    }
    pose proof (teval_normal _ _ Hteval) as Hnormal.
    specialize (Hmaximum _ _ (teval_to_peval _ _ Hnormal Hteval)).
    rewrite <- tvalue_value in Hmaximum.
    exact Hmaximum.
  - intros l Hnormal.
    destruct (Hexists l) as [l2 [Hpeval Hvalue]].
    destruct (peval_to_teval _ _ Hnormal Hpeval) as [t [Hfrom Hto]].
    exists t.
    split.
    + exact Hfrom.
    + rewrite tvalue_value.
      rewrite <- Hto.
      exact Hvalue.
Qed.

Theorem par_algo_tree_correct :
  tree_correct par_algo.
Proof.
  apply correct_tree_correct.
  apply par_algo_correct.
Qed.

Close Scope Z_scope.