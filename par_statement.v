From Stdlib Require Import List ZArith.
From PAR Require Export par_tree_statement.
Import ListNotations.
Open Scope Z_scope.

Definition neg (s : sign) : sign := if s then N else P.

Inductive eval : list sign -> list sign -> Prop :=
| eval_nil : eval [] []
| eval_P : forall l l' r r',
    eval l l' ->
    eval r r' ->
    eval (l ++ P :: r) (l' ++ P :: r')
| eval_N : forall l l' r r' r'',
    eval l l' ->
    eval r r' ->
    map neg r' = r'' ->
    eval (l ++ N :: r) (l' ++ N :: r'').

Fixpoint value (l : list (sign * nat)) : Z :=
  match l with
  | [] => 0
  | (P, x) :: tl => (Z.of_nat x + value tl)%Z
  | (N, x) :: tl => (- Z.of_nat x + value tl)%Z
  end.

Definition signs (l : list (sign * nat)) : list sign := map fst l.

Definition values (l : list (sign * nat)) : list nat := map snd l.

Definition peval (l1 : list (sign * nat)) (l2 : list (sign * nat)) : Prop :=
  eval (signs l1) (signs l2) /\
  values l1 = values l2.

Fixpoint par_fix (l : list (sign * nat)) (pre_sum : Z) : (Z * Z * Z) :=
  match l with
  | [] => (0, 0, pre_sum)
  | (P, n) :: tl =>
      let z := Z.of_nat n in
      let '(abs_sum, pos_sum, max_sum) := par_fix tl (pre_sum + z) in
      (abs_sum + z, pos_sum + z, max_sum)
  | (N, n) :: tl =>
      let z := Z.of_nat n in
      let '(abs_sum, pos_sum, max_sum) := par_fix tl (pre_sum - z) in
      (abs_sum + z, 0, Z.max max_sum (pre_sum - z - 2 * pos_sum + abs_sum))
  end.

Definition par_algo (l : list (sign * nat)) : Z := let '(_, _, x) := par_fix l 0 in x.

Module par_algo_example.

Open Scope nat_scope.

Example example1 :
  par_algo [(P, 1); (P, 3); (N, 5); (N, 4); (P, 6)] = 9%Z.
Proof. reflexivity. Qed.

Example example2 :
  par_algo
    [(P, 1); (P, 3); (N, 6); (N, 9);
     (P, 4); (N, 5); (N, 7); (P, 8)] = 31%Z.
Proof. reflexivity. Qed.

End par_algo_example.

Definition maximum (A : list (sign * nat) -> Z) : Prop :=
  forall l1 l2 : list (sign * nat), peval l1 l2 -> value l2 <= A l1.

Definition exists_maximum (A : list (sign * nat) -> Z) : Prop :=
  forall l1, exists l2, peval l1 l2 /\
    value l2 = A l1.

Definition correct (A : list (sign * nat) -> Z) : Prop := maximum A /\
  exists_maximum A.

Close Scope Z_scope.