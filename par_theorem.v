From Stdlib Require Import List ZArith.
From PAR Require Import par_statement eval_property par_eval.

Import PAR_EVAL.

Open Scope Z_scope.

Theorem par_algo_maximum :
	maximum par_algo.
Proof.
	unfold maximum.
	intros l1 l2 [Heval Hvals].
	destruct (greedy_eval_complete _ _ Heval) as [L [Hweaker Hgreedy]].
	rewrite <- (value_of_consistent_signs l2 (map fst l2) eq_refl).
	specialize (Hweaker (map snd l2)).
	eapply Z.le_trans.
	- exact Hweaker.
	- pose proof (par_algo_greedy_eval _ _ l1 Hgreedy eq_refl) as Hmax.
		unfold values in Hvals.
		rewrite Hvals in Hmax.
		exact Hmax.
Qed.

Theorem par_algo_exists_maximum :
	exists_maximum par_algo.
Proof.
	unfold exists_maximum.
	intro l.
	exists (par_witness l).
	split.
	- apply par_witness_peval.
	- apply par_witness_value.
Qed.

Theorem par_algo_correct :
	correct par_algo.
Proof.
	split.
	- apply par_algo_maximum.
	- apply par_algo_exists_maximum.
Qed.

Print Assumptions par_algo_correct.

Close Scope Z_scope.
