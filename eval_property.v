(*
  添加括号改变求值顺序, 最大化表达式
    c_1 x_1 c_2 x_2 c_3 ... c_n x_n
  其中 x_i 是非负整数, c_i 是 '+' 或 '-', c_1 = '+'


  设与括号表达式等价的去括号表达式为 c_1' x_1 c_2' x_2 c_3' ... c_n' x_n，
  定义符号序列的二元关系 eval，表示能够通过添加括号从符号序列 c 变换到 c'，规则为
    - eval [] []
    - eval (l ++ P :: r) (l' ++ P :: r') 如果 eval l l' 且 eval r r'
    - eval (l ++ N :: r) (l' ++ N :: r'') 如果 eval l l' 且 eval r r' 且 r'' 是 r' 中每个符号取反后的结果
  我们只需要考虑贪心的求值策略 greedy_eval c c'，定义为
    - greedy_eval l l
    - greedy_eval (l1 ++ N :: repeat P n ++ N :: l2)
                   (l1 ++ N :: repeat N n ++ P :: repeat P (length l2))
  这是因为
    - weaker l l' 定义为对于任意非负整数序列 values，有 value (combine l values) <= value (combine l' values)
    - 对于任意 eval l l'，都存在 L 使得 weaker l' L 且 greedy_eval l L
*)

(*
  Add parentheses to change the order of evaluation to maximize the value of the expression
    c_1 x_1 c_2 x_2 c_3 ... c_n x_n
  where x_i are non-negative integers, c_i are '+' or '-', and c_1 = '+'.

  Let the parenthesized expression's equivalent unparenthesized expression be c_1' x_1 c_2' x_2 c_3' ... c_n' x_n.  
  Define the binary relation eval for symbol sequences, indicating that the symbol sequence c can be transformed into c' by adding parentheses, with the rules:  
    - eval [] []  
    - eval (l ++ P :: r) (l' ++ P :: r') if eval l l' and eval r r'  
    - eval (l ++ N :: r) (l' ++ N :: r'') if eval l l', eval r r', and r'' is the result of negating every symbol in r'  
    
  We only need to consider the greedy evaluation strategy greedy_eval c c', defined as  
    - greedy_eval l l  
    - greedy_eval (l1 ++ N :: repeat P n ++ N :: l2)  
      (l1 ++ N :: repeat N n ++ P :: repeat P (length l2))  
                   
  This is because:  
    - weaker l l' is defined as, for any non-negative integer sequence values, value (combine l values) <= value (combine l' values)  
    - For any eval l l', there exists L such that weaker l' L and greedy_eval l L
*)

Ltac inv H := inversion H; clear H; subst.

From Stdlib Require Import List Lia ZArith.
Import ListNotations.

From PAR Require Import par_statement.

Hint Constructors eval : core.

Theorem eval_refl :
  forall l, eval l l.
Proof.
  induction l using rev_ind.
  - constructor.
  - destruct x.
    + apply eval_P; auto.
    + apply eval_N with (l:=l) (l':=l) (r':=[]); auto.
Qed.

Hint Resolve eval_refl : core.

Theorem eval_len :
  forall l l',
    eval l l' ->
    length l = length l'.
Proof.
  intros l l' H.
  induction H; auto; repeat rewrite length_app; simpl; auto.
  subst. rewrite length_map; simpl. auto.
Qed.

Theorem eval_hd_eq :
  forall a l b l',
    eval (a :: l) (b :: l') ->
    a = b.
Proof.
  intros.
  remember (a :: l) as L eqn:E.
  remember (b :: l') as L' eqn:E'.
  revert a b l l' E E'.
  induction H; intros; subst; auto.
  all: destruct l, l'.
  all: try (simpl in E, E'; inversion E; inversion E'; subst; eauto).
  all: try (apply eval_len in H; simpl in H; lia).
Qed.

Lemma nat_compare : forall (a b : nat), a < b \/ a = b \/ a > b. lia. Qed.

Lemma nat_compare2 : forall a b, a < b \/ a = b \/ a = S b \/ a > S b. lia. Qed.

Lemma destruct_list_eq :
  forall {A : Type} (l l' r r' hd tl tl' : list A) a b c,
    (l ++ a :: r = hd ++ b :: tl) ->
    (l' ++ a :: r' = hd ++ c :: tl') ->
    length l = length l' ->
    b <> c ->
    (length l < length hd /\
      r = skipn (S (length l)) hd ++ b :: tl /\
      r' = skipn (S (length l)) hd ++ c :: tl') \/
    (length l > length hd /\
      l = hd ++ b :: (firstn (length l - length hd - 1) tl) /\
      l' = hd ++ c :: (firstn (length l - length hd - 1) tl')).
Proof.
  intros.
  destruct (nat_compare (length l) (length hd)) as [Hlt | [Heq | Hgt]].
  - left. split; auto. split; [|
      rewrite H1 in Hlt; rewrite H1; clear H H1 l r;
      rename H0 into H; rename l' into l; rename r' into r
    ].
    all: apply (f_equal (skipn (length (l ++ [a])))) in H.
    all: replace (l ++ a :: r) with ((l ++ [a]) ++ r) in H
           by (rewrite <-app_assoc; auto).
    all: rewrite skipn_app, skipn_all, Nat.sub_diag, skipn_0, last_length, skipn_app in H.
    all: replace (S (length l) - length hd) with 0 in H by lia.
    all: rewrite skipn_0 in H; auto.
  - apply (f_equal (skipn (length l))) in H.
    rewrite !skipn_app in H.
    rewrite Nat.sub_diag in H.
    rewrite skipn_all, skipn_0 in H.
    rewrite Heq, skipn_all, Nat.sub_diag, skipn_0 in H.
    apply (f_equal (skipn (length l'))) in H0.
    rewrite !skipn_app in H0.
    rewrite Nat.sub_diag in H0.
    rewrite skipn_all, skipn_0 in H0.
    rewrite <-H1, Heq in H0.
    rewrite skipn_all, Nat.sub_diag, skipn_0 in H0.
    inversion H. inversion H0. congruence.
  - right. split; auto. split; [|
      rewrite H1 in Hgt; rewrite H1; clear H H1 l tl;
      rename H0 into H; rename l' into l; rename tl' into tl
    ].
    all: apply (f_equal (firstn (length l))) in H.
    all: rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_0, app_nil_r in H.
    all: rewrite firstn_app, firstn_all2 in H; try lia.
    all: replace (length l - length hd) with (S (length l - length hd - 1)) in H by lia.
    all: rewrite firstn_cons in H; auto.
Qed.

Lemma last_nth :
  forall {A : Type} (l : list A) (d : A),
    l <> [] ->
    last l d = nth (length l - 1) l d.
Proof with auto.
  intros A l. induction l as [| h t IH]; intros; simpl...
  clear H.
  destruct t; simpl...
  specialize IH with d.
  simpl in IH. rewrite IH; try discriminate.
  rewrite Nat.sub_0_r. reflexivity.
Qed.

Theorem eval_diff_N :
  forall l l' hd a tl tl',
    eval l l' ->
    l = hd ++ a :: tl ->
    l' = hd ++ neg a :: tl' ->
    last hd P = N.
Proof with auto.
  intros l l' hd a tl tl' H.
  revert hd a tl tl'.
  induction H; intros.
  - destruct hd; inversion H.
  - specialize eval_len with (1:=H) as Hlen.
    assert (Hneq: a <> neg a).
    { destruct a; simpl; congruence. }
    specialize @destruct_list_eq with (A:=sign) (1:=H1) (2:=H2) (3:=Hlen) (4:=Hneq) as Hdestruct.
    destruct Hdestruct as [[Hlt [Hr Hr']] | [Hgt [Hl Hl']]].
    + specialize IHeval2 with (1:=Hr) (2:=Hr') as IH.
      clear -IH Hlt.
      assert (skipn (S (length l)) hd <> []).
      { intros contra.
        rewrite contra in IH. discriminate. }
      rewrite last_nth in IH...
      rewrite nth_skipn, length_skipn in IH.
      (* length hd > S (length l)*)
      destruct (Nat.leb_spec (length hd) (S (length l))).
      apply skipn_all_iff in H0. congruence.
      assert (hd <> []).
      { intros contra. subst. discriminate.  }
      assert (length hd <> 0).
      { 
        intros contra. rewrite length_zero_iff_nil in contra. congruence.
      }
      rewrite last_nth...
      replace (length hd - 1) with (S (length l) + (length hd - S (length l) - 1)) by lia.
      assumption.
    + eauto.
  - specialize eval_len with (1:=H) as Hlen.
    assert (Hneq: a <> neg a). { destruct a; simpl; congruence. }
    specialize @destruct_list_eq with
      (A:=sign) (1:=H2) (2:=H3) (3:=Hlen) (4:=Hneq) as ?H.
    destruct H4 as [[Hlt [Hr Hr']] | [Hgt [Hl Hl']]]; eauto.
    clear -Hr Hr' H2 H0 H1 Hlt.
    destruct (Nat.leb_spec (length hd) (S (length l))).
    + assert (length hd = S (length l)) by lia.
      clear -H2 H3.
      rewrite last_nth.
      replace (length hd - 1) with (length l) by lia.
      erewrite <- app_nth1, <- H2.
      apply nth_middle.
      lia. intros contra. subst. discriminate.
    + destruct (skipn (S (length l)) hd) eqn:skipn_nil.
      apply skipn_all_iff in skipn_nil. lia.
      simpl in Hr, Hr'. subst. destruct r'.
      apply (eval_len) in H0. simpl in H0. lia.
      apply eval_hd_eq in H0. simpl in Hr'. inversion Hr'.
      subst. destruct s0; discriminate.
Qed.

Proposition last_removelast :
  forall l, last l P = N -> l = removelast l ++ [N].
Proof.
  intros. rewrite <- H. apply app_removelast_last.
  intros contra. subst. discriminate.
Qed.

Lemma eval_firstn :
  forall l l' n,
    eval l l' ->
    eval (firstn n l) (firstn n l').
Proof with auto.
  intros. revert n.
  induction H; intros...
  - specialize eval_len with (1:=H) as Hlen.
    rewrite !firstn_app, <-Hlen.
    destruct (nat_compare n (S (length l))) as [Hlt | [Heq | Hgt]].
    + replace (n - length l) with 0 by lia. rewrite !firstn_0, !app_nil_r...
    + replace (n - length l) with 1 by lia. simpl.
      apply eval_P...
    + replace (n - length l) with (S (n - S (length l))) by lia. simpl.
      apply eval_P...
  - specialize eval_len with (1:=H) as Hlen.
    rewrite !firstn_app, <-Hlen.
    destruct (nat_compare n (S (length l))) as [Hlt | [Heq | Hgt]].
    + replace (n - length l) with 0 by lia. rewrite !firstn_0, !app_nil_r...
    + replace (n - length l) with 1 by lia. simpl.
      apply eval_N with (r':=[])...
    + replace (n - length l) with (S (n - S (length l))) by lia. simpl.
      apply eval_N with (r':=firstn (n - S (length l)) r')...
      rewrite <-firstn_map. rewrite H1...
Qed.

Lemma length_app_tail:
  forall A l (a : A), S (length l) = length (l ++ [a]).
Proof.
  intros. rewrite length_app. simpl. lia.
Qed.

Lemma map_neg_neg :
  forall l,
    map neg (map neg l) = l.
Proof.
  induction l; simpl; auto.
  rewrite IHl. destruct a; simpl; auto.
Qed.

Theorem pp_forward_aux :
  forall hd tl hd' tl' a,
    length hd = length hd' ->
    eval (hd ++ P :: P :: tl) (hd' ++ neg a :: a :: tl') ->
    eval (hd ++ P :: P :: tl) (hd' ++ a :: a :: tl').
Proof with auto.
  intros hd tl hd' tl' a Heqlen H.
  remember (hd ++ P :: P :: tl) as L eqn:E.
  remember (hd' ++ neg a :: a :: tl') as L' eqn:E'.

  revert hd tl hd' tl' a E E' Heqlen.
  induction H; intros.
  - destruct hd; discriminate.
  - specialize (eval_len _ _ H) as Hlen.
    destruct (nat_compare2 (length l) (length hd)) as [Hlt | [Heq | [Hss | Hgt]]].
    + replace (hd') with (l' ++ P :: (skipn (S (length l)) hd')).
        rewrite <- app_assoc. apply eval_P with (r':=skipn (S (length l)) hd' ++ a :: a :: tl')...
        apply (f_equal (skipn (S (length l)))) in E.
        apply (f_equal (skipn (S (length l')))) in E'.
        rewrite app_assoc with (m:=[P]) (n:=r) in E.
        rewrite app_assoc with (m:=[P]) (n:=r') in E'.
        rewrite skipn_app in E, E'.
        rewrite length_app_tail with (a:=P) in E at 1 2.
        rewrite length_app_tail with (a:=P) in E' at 1 2.
        rewrite skipn_all, Nat.sub_diag, skipn_0 in E, E'.
        rewrite skipn_app in E, E'.
        rewrite <-Hlen, <-Heqlen in E'.
        replace (S (length l) - length hd) with 0 in E, E' by lia.
        apply IHeval2 with (hd:=skipn (S (length l)) hd) (tl:=tl)...
        rewrite !length_skipn. lia.
      apply (f_equal (firstn (S (length l')))) in E'.
      rewrite app_assoc with (m:=[P]) (n:=r') in E'.
      rewrite firstn_app in E'.
      rewrite firstn_app with (l1:=hd') in E'.
      rewrite length_app_tail with (a:=P) in E' at 1 2.
      replace (S (length l') - length hd') with 0 in E' by lia.
      rewrite firstn_all, Nat.sub_diag, !firstn_0, !app_nil_r in E'.
      rewrite <- firstn_skipn with (n:=S (length l')).
      rewrite <- E', <-app_assoc, Hlen...
    + apply (f_equal (skipn (length l))) in E, E'.
      apply eval_len in H.
      rewrite Heq in E at 2.
      rewrite H in E' at 1.
      rewrite Heq, Heqlen in E'.
      rewrite !skipn_app, !skipn_all, !Nat.sub_diag, !skipn_0 in E, E'.
      inv E. inv E'. apply eval_hd_eq in H0. rewrite <- H0 in H2. inv H2.
    + (* show
        a = P - done
        l = hd ++ [P] - done
        l' = hd' ++ [N] -done
        r' = tl' - done
        ---
        eval (hd ++ P :: P :: r) (hd' ++ P :: P :: r')
          eval hd hd'
            eval (firstn (length hd) l) (firstn (length hd) l')
      *)
      pose proof (f_equal (skipn (length l')) E').
      rewrite <-Hlen in H1 at 2. rewrite Hss, Heqlen in H1.
      assert (Hsub: hd' ++ neg a :: a :: tl' = (hd' ++ [neg a]) ++ a :: tl').
      { rewrite <- app_assoc. reflexivity. }
      rewrite Hsub in H1.
      rewrite skipn_app in H1. rewrite skipn_app in H1.
      rewrite length_app_tail with (a:=neg a), !skipn_all, !Nat.sub_diag, !skipn_0 in H1.
      inv H1.
      apply (f_equal (firstn (length l))) in E.
      apply (f_equal (firstn (length l'))) in E'.
      rewrite !firstn_app in E, E'.
      rewrite !firstn_all, Nat.sub_diag, firstn_0, app_nil_r in E, E'.
      rewrite firstn_all2 in E, E' by lia.
      rewrite Hss in E. rewrite <-Hlen, Hss, <-Heqlen in E'.
      rewrite Nat.sub_succ_l, Nat.sub_diag in E, E'... simpl in E, E'.
      subst. rewrite <-app_assoc. apply eval_P with (l:=hd) (l':=hd').
      2: apply eval_P with (l:=[]) (l':=[])...
      apply eval_firstn with (n:=length hd) in H.
      rewrite Heqlen in H at 2.
      rewrite !firstn_app, !firstn_all, !Nat.sub_diag, !firstn_0, !app_nil_r in H...
    + pose proof E' as E1.
      apply (f_equal (firstn (length l))) in E.
      apply (f_equal (firstn (length l'))) in E'.
      rewrite !firstn_app, firstn_all, Nat.sub_diag, firstn_0, app_nil_r in E, E'.
      rewrite firstn_all2 in E, E' by lia.
      rewrite <-Heqlen, <-Hlen in E'.
      replace (length l - length hd) with (S (S (length l - length hd - 2))) in E, E' by lia.
      rewrite !firstn_cons in E, E'.
      specialize IHeval1 with (1:=E) (2:=E') (3:=Heqlen).
      apply (f_equal (skipn (length l'))) in E1.
      rewrite !skipn_app, skipn_all, Nat.sub_diag, skipn_0 in E1.
      (* Check skipn_all_iff. *)
      destruct skipn_all_iff with (n:=length l') (l:=hd') as [? _].
      rewrite H1 in E1 by lia. clear H1.
      remember (hd' ++ a :: a :: firstn (length l - length hd - 2) tl') as L.
      replace (length l' - length hd') with (S (S (length l - length hd - 2))) in E1 by lia.
      rewrite !skipn_cons in E1. simpl in E1.
      replace (hd' ++ a :: a :: tl') with (
        L ++ P :: skipn (length l - length hd - 1) tl').
      apply eval_P...
      * apply (f_equal (skipn 1)) in E1. rewrite skipn_skipn in E1.
        replace (1 + (length l - length hd - 2)) with (length l - length hd - 1) in E1 by lia.
        simpl in E1. rewrite <- E1...
      * subst. rewrite <- app_assoc. simpl. repeat f_equal.
        (* Check firstn_skipn. *)
        rewrite <- (firstn_skipn) with (n:=length l - length hd - 2).
        f_equal.
        rewrite <- (firstn_skipn) with (n:=1).
        rewrite skipn_skipn, <-E1.
        replace (1 + (length l - length hd - 2)) with (length l - length hd - 1) by lia.
        simpl. reflexivity.
  - specialize (eval_len _ _ H) as Hlen.
    destruct (nat_compare2 (length l) (length hd)) as [Hlt | [Heq | [Hss | Hgt]]].
    + (* show that
        r'' = skipn (S (length l)) hd' ++ neg a :: a :: tl'
        r' = map neg r''
          = (map neg (skipn (S (length l)) hd') ++ neg (neg a) :: neg a :: map neg tl')
        eval r (map neg (skipn (S (length l)) hd') ++ neg a :: neg a :: map neg tl')
        ---
        eval (l ++ N :: r) (l' ++ N :: (skipn (S (length l)) hd' ++ a :: a :: tl'))
          eval l l'
          eval r ?r'
          map neg ?r' = (skipn (S (length l)) hd' ++ a :: a :: tl')
      *)
      clear IHeval1.
      pose proof E' as E1.
      apply (f_equal (skipn (S (length l)))) in E.
      apply (f_equal (skipn (S (length l')))) in E'.
      rewrite length_app_tail with (a:=N) in E at 1.
      rewrite length_app_tail with (a:=N) in E' at 1.
      rewrite app_assoc with (m:=[N]) (n:=r) in E.
      rewrite app_assoc with (m:=[N]) (n:=r'') in E'.
      rewrite skipn_app in E, E'. rewrite skipn_all in E, E'.
      rewrite skipn_app, Nat.sub_diag in E, E'.
      rewrite <-Hlen in E' at 2. rewrite <-Heqlen in E'.
      replace (S (length l) - length hd) with 0 in E, E' by lia.
      rewrite !skipn_0 in E, E'.
      remember (skipn (S (length l')) hd') as L. simpl in E'.
      apply (f_equal (firstn (length hd'))) in E1.
      rewrite !firstn_app, firstn_all, Nat.sub_diag, firstn_0, app_nil_r in E1.
      rewrite firstn_all2 in E1 by lia.
      replace (length hd' - length l') with (S (length hd' - length l' - 1)) in E1 by lia.
      simpl in E1.
      assert (length hd' - length l' - 1 = length L) as HlenL.
      { subst. rewrite length_skipn. lia. }
      rewrite HlenL, E', firstn_app, firstn_all, Nat.sub_diag, firstn_0, app_nil_r in E1.
      rewrite <-E1, <-app_assoc; clear E1. simpl.
      apply eval_N with (r':=map neg (L ++ a :: a :: tl'))...
      2: apply map_neg_neg.
      rewrite map_app. simpl. apply IHeval2 with (hd:=skipn (S (length l)) hd) (tl:=tl)...
      * apply (f_equal (map neg)) in H1. rewrite map_neg_neg, E', map_app in H1...
      * rewrite length_map, <-HlenL, length_skipn. lia.
    + apply (f_equal (skipn (length l))) in E.
      rewrite Heq in E at 2.
      rewrite !skipn_app, !skipn_all, !Nat.sub_diag, !skipn_0 in E.
      inv E.
    + apply (f_equal (skipn (length l))) in E.
      rewrite app_assoc with (m:=[P]) (n:=P::tl) in E.
      rewrite Hss in E at 2. rewrite length_app_tail with (a:=P) in E.
      rewrite skipn_app in E. rewrite skipn_app in E.
      rewrite !skipn_all, !Nat.sub_diag, !skipn_0 in E.
      inv E.
    + (* A mature proof stategy
        Coclude tactics to reduce copy?
        1. l = hd ++ P :: P :: firstn ?n tl
        2. l' =  hd' ++ neg a :: a :: firstn ?n tl'
        3. eval l (hd' ++ a :: a :: firstn ?n tl')
        4. tl' = firstn ?n tl' ++ N :: r''
      *)
      (* first we always copy E' for 4 *)
      pose proof E' as E1.
      (* proving 1 and 2 requires lots of rewriting *)
      (* always start with firstn (length ?shorter_list)*)
      apply (f_equal (firstn (length l))) in E.
      apply (f_equal (firstn (length l'))) in E'.
      (* this is the most compact way. in other branches we may take a variance chain *)
      rewrite !firstn_app, firstn_all, Nat.sub_diag, firstn_0, app_nil_r, firstn_all2 in E, E' by lia.
      rewrite <- Hlen, <- Heqlen in E'.
      (* We may destruct to get this equation dirrectly? *)
      replace (length l - length hd) with (S (S (length l - length hd - 2))) in E, E' by lia.
      simpl in E, E'.
      (* 1 and 2 is done, goto 3, use induction hypothesis *)
      specialize IHeval1 with (1:=E) (2:=E') (3:=Heqlen).
      (* now prove 4 *)
      rewrite E', <-app_assoc in E1. simpl in E1.
      apply app_inv_head in E1. inv E1.
      rewrite app_assoc with
        (m:=a :: a :: firstn (length l - length hd - 2) tl')(n:=N::map neg r').
      (* finally we can construct the eval *)
      apply eval_N with (r':=r')...
Qed.

Theorem pp_forward :
  forall l l' n,
    eval l l' ->
    nth n l N = P ->
    nth (S n) l N = P ->
    nth (S n) l' N = P ->
    eval l (firstn n l' ++ P :: skipn (S n) l').
Proof with auto.
  assert (nth_skipn:
    forall l n x,
      nth n l (neg x) = x -> skipn n l = x :: skipn (S n) l).
  {
    induction l; intros; destruct n, x; simpl in *; try discriminate; subst...
  }
  intros.
  destruct (nth_error l' n) eqn:?H; [destruct s|].
  - apply nth_error_nth with (d:=N) in H3.
    rewrite <-!nth_skipn...
    rewrite firstn_skipn...
  - apply nth_error_nth with (d:=P) in H3.
    assert (length (firstn n l) = length (firstn n l')).
    { rewrite !firstn_length_le...
      - destruct (Nat.leb_spec0 (length l') n); try lia.
        apply nth_overflow with (d:=P) in l0. congruence.
      - destruct (Nat.leb_spec0 (length l) n); try lia.
        apply nth_overflow with (d:=N) in l0. congruence.
    }
    specialize pp_forward_aux with
      (hd:=firstn n l) (tl:=skipn (S (S n)) l)
      (hd':=firstn n l') (tl':=skipn (S (S n)) l') (a:=P)
    as Haux.
    repeat (rewrite <-nth_skipn in Haux; [|assumption]).
    rewrite !firstn_skipn in Haux...
  - apply nth_error_None in H3.
    rewrite nth_overflow in H2. discriminate. lia.
Qed.

Inductive greedy_eval : list sign -> list sign -> Prop :=
| greedy_eval_refl : forall l, greedy_eval l l
| greedy_eval_flip : forall l1 l2 n,
    greedy_eval
      (l1 ++ N :: repeat P n ++ N :: l2)
      (l1 ++ N :: repeat N n ++ P :: repeat P (length l2)).

Lemma eval_Ncons_aux :
  forall n L L' a,
    length L < n ->
    eval (N :: L) (N :: L') ->
    eval (N :: a :: L) (N :: N :: L').
Proof.
  induction n; [lia|]. intros.
  inversion H0.
  - destruct l, l'; try discriminate.
    inv H1; inv H2.
    apply eval_P with (l:=N::a::l) (l':=N::N::l'); auto.
    apply IHn; auto. rewrite length_app in H. simpl in H. lia.
  - destruct l, l'; simpl.
    {
      inv H1; inv H2.
      clear - H4.
      destruct a.
      * apply eval_N with (l:=[]) (l':=[]) (r':= P::r'); auto.
        apply eval_P with (l:=[]) (l':=[]); auto.
      * apply eval_N with (l:=[N]) (l':=[N]) (r':=r'); auto.
    }
    1, 2: apply eval_len in H3; discriminate.
    {
      inv H1; inv H2.
      apply eval_N with (l:=N::a::l) (l':=N::N::l') (r':=r'); auto.
      apply IHn; auto. rewrite length_app in H. simpl in H. lia.
    }
Qed.

Lemma eval_Ncons :
  forall L L' a,
    eval (N :: L) (N :: L') ->
    eval (N :: a :: L) (N :: N :: L').
Proof.
  intros.
  apply eval_Ncons_aux with (n:=S (length L)); auto.
Qed.

Theorem eval_repeat_N :
  forall l,
    eval (N :: l) (N :: repeat N (length l)).
Proof.
  induction l as [| a L IHl0].
  - simpl. apply eval_refl.
  - simpl. apply eval_Ncons. auto.
Qed.

Theorem greedy_eval_flip_eval :
  forall l1 l2 n,
    eval
      (l1 ++ N :: repeat P n ++ N :: l2)
      (l1 ++ N :: repeat N n ++ P :: repeat P (length l2)).
Proof.
  intros.
  eapply eval_N.
    apply eval_refl.
  2: {
    erewrite map_app.
    f_equal.
    change N with (neg P).
    rewrite map_repeat; reflexivity.
    change P with (neg N).
    rewrite map_cons, map_repeat; reflexivity.
  }
  destruct n.
  - simpl. apply eval_repeat_N.
  - replace (repeat P (S n)) with (repeat P n ++ [P]) by (rewrite <- repeat_cons; auto).
    rewrite <- !app_assoc. simpl.
    apply eval_P. apply eval_refl. apply eval_repeat_N.
Qed.

Theorem greedy_eval_sound :
  forall l l',
    greedy_eval l l' ->
    eval l l'.
Proof.
  intros l l' H.
  destruct H; auto using eval_refl, greedy_eval_flip_eval.
Qed.

Definition weaker l l' := forall values,
  (value (combine l values) <= value (combine l' values))%Z.

Theorem weaker_trans :
  forall l1 l2 l3,
    weaker l1 l2 ->
    weaker l2 l3 ->
    weaker l1 l3.
Proof.
  unfold weaker.
  intros.
  specialize (H values).
  specialize (H0 values).
  lia.
Qed.

Theorem weaker_refl :
  forall l, weaker l l.
Proof.
  unfold weaker.
  lia.
Qed.

Theorem weaker_cons1 :
  forall a l l', weaker l l' -> weaker (a :: l) (a :: l').
Proof.
  unfold weaker.
  intros. simpl. destruct values. lia.
  specialize H with values.
  destruct a; simpl; lia.
Qed.

Theorem weaker_cons2 :
  forall l l', weaker l l' -> weaker (N :: l) (P :: l').
Proof.
  unfold weaker. intros. simpl.
  destruct values. lia. simpl.
  specialize H with values. lia.
Qed.

Hint Resolve weaker_trans weaker_refl weaker_cons1 weaker_cons2 : core. 

Theorem value_app :
  forall l1 l2,
    value (l1 ++ l2) =
    (value l1 + value l2)%Z.
Proof.
  induction l1; intros; simpl. lia.
  destruct a; destruct s;
    rewrite IHl1; lia.
Qed.

Lemma combine_app :
  forall {A B : Type} (l1 l2 : list A) (v : list B),
    combine (l1 ++ l2) v =
    combine l1 v ++ combine l2 (skipn (length l1) v).
Proof.
  induction l1; intros; simpl; auto.
  destruct v.
  - destruct l2; auto.
  - rewrite IHl1. auto.
Qed.

Theorem weaker_app :
  forall l1 l1' l2 l2',
    length l1 = length l1' ->
    weaker l1 l1' ->
    weaker l2 l2' ->
    weaker (l1 ++ l2) (l1' ++ l2').
Proof.
  unfold weaker.
  intros.
  rewrite !combine_app, !value_app.
  pose proof (H0 values).
  pose proof (H1 (skipn (length l1) values)).
  rewrite <- H. lia.
Qed.

Hint Resolve weaker_app : core.

Theorem weaker_repeat :
  forall l, weaker l (repeat P (length l)).
Proof.
  unfold weaker.
  induction l; simpl; intros; try lia.
  destruct values; try lia.
  specialize IHl with values.
  destruct a; simpl; lia.
Qed.

Hint Resolve weaker_repeat : core.

Definition eqb (x y : sign) : {x = y} + {x <> y}.
  destruct x, y.
  - left. auto.
  - right. discriminate.
  - right. discriminate.
  - left. auto.
Defined.

(* Search count_occ. *)

Theorem repeat_or_split :
  forall l a,
    l = repeat a (length l) \/
    exists n, l = repeat a n ++ neg a :: skipn (S n) l.
Proof.
  induction l; intros.
  - left. auto.
  - destruct (IHl a0) as [Heq | [n Heq]].
    + destruct a, a0.
      * left. simpl. f_equal. auto.
      * right. exists 0. simpl. auto.
      * right. exists 0. simpl. auto.
      * left. simpl. f_equal. auto.
    + right.
      destruct a, a0.
      * exists (S n). simpl. f_equal. auto.
      * exists 0. simpl. auto.
      * exists 0. simpl. auto.
      * exists (S n). simpl. f_equal. auto.
Qed.

Lemma signs_bifurcate :
  forall (l l' : list sign),
    length l = length l' ->
    l = l' \/ (exists hd a tl tl',
      l = hd ++ a :: tl /\
      l' = hd ++ neg a :: tl' /\
      length tl = length tl').
Proof with auto.
  induction l; intros.
  - destruct l'...
    discriminate.
  - destruct l' as [|b l']. discriminate.
    inv H. destruct (IHl _ H1)
      as [Heq | [hd [a' [tL [tL' [? []]]]]]].
    + destruct a, b.
      * left. f_equal...
      * right. exists [], P, l, l'...
      * right. exists [], N, l, l'...
      * left. f_equal...
    + destruct a, b; right.
      * exists (P :: hd), a', tL, tL'. repeat split...
          all: simpl; f_equal...
      * exists [], P, l, l'...
      * exists [], N, l, l'...
      * exists (N :: hd), a', tL, tL'. repeat split...
          all: simpl; f_equal...
Qed.

Lemma weaker_substitute : forall l n,
  weaker l (firstn n l ++ P :: skipn (S n) l).
Proof.
  intros.
  rewrite <- firstn_skipn with (n:=n) at 1.
  apply weaker_app; auto.
  rewrite <- skipn_skipn with (x:=1).
  destruct (skipn n l).
  - unfold weaker. intros. destruct values; simpl; lia.
  - destruct s; auto.
Qed.

Lemma count_occ_lt_substitute :
  forall l n,
    nth n l P = N ->
    count_occ eqb (firstn n l ++ P :: skipn (S n) l) N <
    count_occ eqb l N.
Proof.
  intros.
  rewrite <- firstn_skipn with (n:=n) (l:=l) at 3.
  rewrite !count_occ_app.
  apply add_lt_mono_l_proj_l2r.
  rewrite plus_n_O with (n:=n) in H.
  rewrite <-nth_skipn with (i:=0) (n:=n) in H.
  rewrite <-skipn_skipn with (x:=1).
  destruct (skipn n l).
  - simpl in H. discriminate.
  - simpl in H. subst. simpl. lia.
Qed.

Lemma greedy_eval_progress_case_P :
  forall l l' hd' tl tl',
    eval l l' ->
    l = hd' ++ N :: P :: tl ->
    l' = hd' ++ N :: N :: tl' ->
    length tl = length tl' ->
    greedy_eval l l' \/ exists L,
      (weaker l' L) /\
      count_occ eqb L N < count_occ eqb l' N /\
      eval l L.
Proof with auto.
  intros l l' hd' tl tl' H H0 H1 H2.
  destruct (repeat_or_split tl P) as [HallP|[n Heq]].
  - right. exists l. subst. rewrite HallP, H2. repeat split...
    rewrite !count_occ_app.
    apply add_lt_mono_l_proj_l2r. simpl.
    rewrite count_occ_repeat_neq; try discriminate. lia.
  - assert (n < length tl').
    { rewrite <- H2. apply (f_equal (@length sign)) in Heq.
      rewrite length_app, repeat_length in Heq.
      simpl in Heq. lia. }
    specialize firstn_skipn with (l:=tl') (n:=n) as Hsplit.
    destruct (repeat_or_split (firstn n tl') N) as [HallN|[m Hpref]].
    { rewrite firstn_length_le in HallN; try lia.
      assert (Hlen:
        length (skipn n tl') = S (length (skipn (S n) tl)))
      by (rewrite !length_skipn; lia).
      destruct (repeat_or_split (skipn n tl') P) as [HallTailP|[k Htail]].
      - left. subst. rewrite Heq, <- Hsplit, HallN, HallTailP, Hlen.
        apply greedy_eval_flip with (n:=S n).
      - right.
        subst. rewrite Heq, <- Hsplit, HallN.
        exists (hd' ++ N :: repeat N (S n) ++ repeat P (length (skipn n tl'))).
        repeat split.
        + simpl...
        + rewrite !count_occ_app. simpl.
          apply add_lt_mono_l_proj_l2r. simpl.
          repeat apply add_lt_mono_l_proj_l2r with (p:=1).
          rewrite !count_occ_app.
          apply add_lt_mono_l_proj_l2r.
          rewrite count_occ_repeat_neq; try discriminate.
            rewrite Htail. rewrite count_occ_app. simpl. lia.
        + rewrite Hlen.
          apply greedy_eval_sound, greedy_eval_flip with (n:=S n).
    }
    assert (Hmn: m < n).
    { apply (f_equal (@length sign)) in Hpref.
      rewrite firstn_length_le in Hpref; try lia.
      rewrite length_app in Hpref. simpl in Hpref.
      rewrite repeat_length in Hpref. simpl in Hpref. lia.
    }
    subst. rewrite Heq, <- Hsplit, Hpref in H |-*.
    right. eexists. repeat split.
    3: {
      apply pp_forward with (1:=H) (n:=length hd' + (S m)).
      - rewrite app_nth2_plus with (l:=hd').
        simpl. destruct m...
        rewrite app_nth1.
        1: apply nth_repeat_lt.
        2: rewrite repeat_length.
        all: lia.
      - replace (S (length hd' + S m)) with (length hd' + S (S m)) by lia.
        rewrite app_nth2_plus with (l:=hd').
        simpl.
        rewrite app_nth1.
        1: apply nth_repeat_lt.
        2: rewrite repeat_length.
        all: lia.
      - replace (S (length hd' + S m)) with (length hd' + S (S m)) by lia.
        rewrite app_nth2_plus with (l:=hd').
        rewrite <- app_assoc. simpl.
        Hint Resolve repeat_length : core.
        replace m with (length (repeat N m)) at 1...
        rewrite nth_middle...
    }
    { apply weaker_substitute. }
    apply count_occ_lt_substitute.
    rewrite app_nth2_plus. simpl. destruct m...
    rewrite <- app_assoc.
    rewrite app_nth1. apply nth_repeat_lt. lia.
    rewrite repeat_length. lia.
Qed.

Lemma greedy_eval_progress_case_N :
  forall l l' hd' tl tl',
    eval l l' ->
    l = hd' ++ N :: N :: tl ->
    l' = hd' ++ N :: P :: tl' ->
    length tl = length tl' ->
    greedy_eval l l' \/ exists L,
      (weaker l' L) /\
      count_occ eqb L N < count_occ eqb l' N /\
      eval l L.
Proof with auto.
  intros l l' hd' tl tl' H H0 H1 H2.
  destruct (repeat_or_split tl' P) as [HallP|[n Heq]].
  - left.
    rewrite H0, H1.
    assert (Htail: tl' = repeat P (length tl)).
    { rewrite HallP, <- H2. reflexivity. }
    rewrite Htail.
    apply greedy_eval_flip with (n:=0).
  - right. exists (hd' ++ N :: P :: repeat P (length tl)).
    subst l l'. rewrite H2 at 1 2. repeat split...
    { rewrite !count_occ_app.
      apply add_lt_mono_l_proj_l2r. simpl.
      rewrite count_occ_repeat_neq; try discriminate.
      rewrite Heq. rewrite count_occ_app. simpl. lia. }
    { apply greedy_eval_sound.
      apply greedy_eval_flip with (n:=0). }
Qed.

Theorem greedy_eval_progress :
  forall l l',
    eval l l' ->
    greedy_eval l l' \/ exists L,
      (weaker l' L) /\
      count_occ eqb L N < count_occ eqb l' N /\
      eval l L.
Proof with auto.
  intros.
  specialize eval_len with (1:=H) as Hlen.
  destruct (signs_bifurcate l l' Hlen) as
    [Heq | [hd [a [tl [tl' [? []]]]]]].
  - left. subst. apply greedy_eval_refl.
  - assert (last hd P = N). { eapply eval_diff_N; eauto. }
    apply last_removelast in H3. remember (removelast hd) as hd'.
    rewrite H3, <- app_assoc in H0, H1. simpl in H0, H1.
    clear -H0 H1 H2 H.
    destruct a.
    + eapply greedy_eval_progress_case_P; eauto.
    + eapply greedy_eval_progress_case_N; eauto.
Qed.

Theorem greedy_eval_complete_aux :
  forall n l l',
    eval l l' ->
    count_occ eqb l' N < n ->
    exists L,
      (weaker l' L) /\
      greedy_eval l L.
Proof with eauto using greedy_eval_sound.
  induction n as [|n IH]; intros l l' Heval Hcount.
  - lia.
  - destruct (greedy_eval_progress _ _ Heval) as [Hgreedy|[L [Hweaker [Hcount' Heval']]]].
    + exists l'. split...
    + destruct (IH _ _ Heval' ltac:(lia)) as [L' [Hweaker' Hgreedy']].
      exists L'. split...
Qed.

(* main theorem *)
Definition greedy_eval_complete_spec :=
  forall l l',
    eval l l' ->
    exists L,
      (weaker l' L) /\
      greedy_eval l L.

Theorem greedy_eval_complete :
  greedy_eval_complete_spec.
Proof.
  intros l l' Heval.
  eapply greedy_eval_complete_aux with (n:=S (count_occ eqb l' N)); eauto with arith.
Qed.

(* generate the definition dependence graph *)
(*
Require dpdgraph.dpdgraph.
Print DependGraph sign_eval.greedy_eval_complete_spec.

Print sign_eval.
*)

Module Negative.

Theorem eval_N_any : forall n l, length l = n -> eval (N :: repeat N n) (N :: l).
  induction n; intros.
  - apply length_zero_iff_nil in H. subst. auto.
  - destruct l. inv H.
    destruct s.
    + apply eval_N with (l:=[]) (l':=[]) (r':=N::map neg l); auto.
      apply IHn. injection H as H. rewrite <- H. apply length_map. simpl. f_equal. apply map_neg_neg.
    + simpl. apply eval_Ncons. apply IHn. auto.
Qed.

End Negative.