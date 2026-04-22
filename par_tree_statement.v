(** 本文件包含 贪心算法 par_algo 和算法正确性 correct 的定义，和表述出它们所必要的定义 *)
From Stdlib Require Import List ZArith.

Import ListNotations.

Open Scope Z_scope.

Inductive sign := P | N.

Inductive tree :=
| V : nat -> tree
| T : tree -> sign -> tree -> tree.

Fixpoint from (s : sign) (t : tree) : list (sign * nat) :=
  match t with
  | V v => [(s, v)]
  | T l P r => from s l ++ from P r
  | T l N r => from s l ++ from N r
  end.

Fixpoint tvalue (t : tree) : Z :=
  match t with
  | V v => Z.of_nat v
  | T l P r => tvalue l + tvalue r
  | T l N r => tvalue l - tvalue r
  end.

Definition normal (l : list (sign * nat)) : Prop :=
  match l with
  | (P, _) :: _ => True
  | _ => False
  end.

Definition tree_maximum (A : list (sign * nat) -> Z) : Prop :=
  forall l t, l = from P t -> tvalue t <= A l.

Definition tree_exists_maximum (A : list (sign * nat) -> Z) : Prop :=
  forall l, normal l -> exists t, l = from P t /\
    tvalue t = A l.

Definition tree_correct (A : list (sign * nat) -> Z) : Prop :=
  tree_maximum A /\ tree_exists_maximum A.

Close Scope Z_scope.