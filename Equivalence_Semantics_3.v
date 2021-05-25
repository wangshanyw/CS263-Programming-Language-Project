Require Import PL.Imp PL.ImpExt PL.RTClosure.
Local Open Scope imp.

Require Import PL.Denotational_Semantics_3.


(* ################################################################# *)
(** * From Denotations To Multi-step Relations *)

Lemma semantic_equiv_iter_loop1: forall st1 st2 n b c, 
  (forall st1 st2, (exists t: Z, ceval c st1 t st2) -> multi_cstep (c, st1) (Skip, st2)) ->
  (exists n0 : nat, iter_loop_body b (ceval c) n0 st1 n st2) ->
  multi_cstep (While b Do c EndWhile, st1) (Skip, st2).
Proof.
  intros. destruct H0.
  revert st1 st2 n H0; induction x; intros.
  + simpl in H0.
    unfold BinRel.test_rel in H0.
    destruct H0.
    subst st2.
    etransitivity_1n; [apply CS_While |].
    etransitivity; [apply multi_congr_CIf, semantic_equiv_bexp1_false, H1 |].
    etransitivity_1n; [apply CS_IfFalse |].
    reflexivity.
  + simpl in H0.
    unfold seq_sem at 1,
           test_sem in H0.
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
    unfold seq_sem in H1. destruct H1. destruct H1. destruct H1. 
    etransitivity_1n; [apply CS_While |].
    etransitivity; [apply multi_congr_CIf, semantic_equiv_bexp1_true, H0 |].
    etransitivity_1n; [apply CS_IfTrue |]. destruct H0. destruct H0. destruct H1. destruct H1.
    etransitivity. apply multi_congr_CSeq. apply H. exists x3. apply H0. 
    etransitivity_1n; [apply CS_Seq |].
    apply IHx with x4.
    tauto.
Qed.



Theorem semantic_equiv_com1: forall st1 st2 c,
  (exists t : Z, ceval c st1 t st2) -> multi_cstep (c, st1) (Skip, st2).
Proof.
  intros.
  revert st1 st2 H. induction c; intros.
  + simpl in H.
    unfold skip_sem in H.
    destruct H. destruct H.
    rewrite H.
    reflexivity.
  + simpl in H.
    unfold asgn_sem in H.
    destruct H.
    etransitivity_n1.
    - apply multi_congr_CAss, semantic_equiv_aexp1.
      reflexivity.
    - apply CS_Ass. tauto. destruct H. 
      apply H0.
  + simpl in H.
    unfold seq_sem in H.
    destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0.
    etransitivity. apply multi_congr_CSeq. 
    pose proof IHc1 st1 x2. apply H2. exists x0. tauto.
    etransitivity_1n; [ apply CS_Seq |].
    pose proof IHc2 x2 st2. apply H2. exists x1. tauto.
  + simpl in H.
    unfold if_sem in H.
    unfold union_sem,seq_sem,test_sem in H.
    pose proof semantic_equiv_bexp1 st1 b.
    destruct H0. destruct H. destruct H as [H | H]. destruct H. destruct H. destruct H.
    destruct H. destruct H. destruct H3. destruct H2. 
    - etransitivity. apply multi_congr_CIf. apply H0. tauto.
      etransitivity_1n; [apply CS_IfTrue |].
      pose proof IHc1 st1 st2. apply H6. exists x1. rewrite H. tauto.
    - etransitivity. apply multi_congr_CIf. apply H1.
      destruct H. destruct H. destruct H. destruct H. destruct H.
      destruct H3. destruct H2. simpl in H3. 
      unfold Sets.complement in H3. tauto.
      etransitivity_1n; [apply CS_IfFalse |].
      destruct H. destruct H. destruct H. destruct H. destruct H.
      destruct H3. destruct H2. 
      pose proof IHc2 x2 st2. rewrite H. apply H6. exists x1. tauto.
  + simpl in H.
    unfold loop_sem in H.
    unfold omega_union_sem in H.
    destruct H as [n ?].
    apply semantic_equiv_iter_loop1 with n.
    - exact IHc.
    - exact H.
Qed.

    
(* ################################################################# *)
(** * From Multi-step Relations To Denotations*)
Lemma loop_unrolling: forall b c (a b0: state) (t:Z),
    ceval (While b Do c EndWhile) a t b0 <->
    ceval (If b Then c;; While b Do c EndWhile Else Skip EndIf) a t b0.
Proof.
  intros. simpl.
    unfold iff; split; intros.
  + unfold loop_sem, omega_union_sem in H.
    destruct H as [n ?].
    destruct n.
    - simpl in H.
      unfold if_sem, union_sem.
      right; simpl.
      unfold seq_sem, skip_sem.
      exists t. exists 0. exists b0; split; [exact H | ]. 
      split. tauto. lia.
    - simpl in H.
      unfold if_sem, union_sem.
      left.
      unfold seq_sem in H.
      unfold seq_sem.
      destruct H as [t1 [t2 [st1' [? ?]]]].
      destruct H0.
      destruct H0 as [t0 [t3 [st2' [? ?]]]].
      exists t1. exists t2. exists st1'; split; [exact H |].
      split. exists t0. exists t3. exists st2';split; [exact H0 |].
      unfold loop_sem, omega_union_sem. split.
      exists n. destruct H2.
      exact H2. lia. lia.
  + unfold if_sem, union_sem in H.
    unfold loop_sem, omega_union_sem.
    destruct H.
    2: {
      exists 0%nat.
      simpl.
      unfold seq_sem, skip_sem in H.
      destruct H as [t1 [t2 [st2' [? ?]]]]. destruct H0. destruct H0.
      rewrite H0 in H. rewrite H2 in H1.
      assert (t = t1). rewrite H1. lia.
      rewrite <- H3 in H. tauto.
    }
    unfold seq_sem at 1 in H.
    destruct H as [t1 [t2 [st1' [? ?]]]].
    unfold seq_sem in H0. destruct H0.
    destruct H0 as [t0 [t3 [st0 [? ?]]]].
    destruct H2.
    unfold loop_sem, omega_union_sem in H2.
    destruct H2 as [n ?].
    exists (S n).
    simpl.
    unfold seq_sem at 1.
    exists t1. exists t2.
    exists st1'; split; [exact H |].
    unfold seq_sem. split. exists t0. exists t3.
    exists st0; split; [exact H0 |]. split. tauto. tauto. tauto.
Qed.


Lemma ceval_preserve_1: forall c1 c2 st1 st2, 
  cstep (c1, st1) (c2, st2) ->
  forall st3 t1, ceval c2 st2 t1 st3 -> (ceval c1 st1 t1 st3 \/ ceval c1 st1 (t1+1)%Z st3).
Proof.
  intros. revert t1 st3 H0.
  induction_cstep H; simpl; intros.
  + apply aeval_preserve in H.
    unfold asgn_sem in H0. unfold asgn_sem.
    rewrite H. destruct H0. left. tauto.
  + unfold skip_sem in H1.
    unfold asgn_sem.
    destruct H1. destruct H1. right. split.
    unfold aeval. unfold constant_func. tauto.
    intros. pose proof H0 Y. apply H3 in H1. rewrite H2. tauto.
  + unfold seq_sem in H0. destruct H0 as [t2 [t3 [st2' [? ?]]]].
    pose proof IHcstep t2 st2'.
    destruct H2. tauto.
    unfold seq_sem. left. exists t2. exists t3. exists st2'. tauto.
    unfold seq_sem. right. exists (t2+1)%Z. exists t3. exists st2'. 
    destruct H1. split. tauto. split. tauto. rewrite H3. lia.
  + left. unfold seq_sem, skip_sem.
    exists 0. exists t1. exists st. tauto.
  + left.
    unfold if_sem in H0.
    unfold if_sem.
    unfold union_sem, seq_sem, test_sem in H0.
    unfold union_sem, seq_sem, test_sem.
    apply beval_preserve in H.
    simpl in H0.
    simpl.
    unfold Sets.complement in H0.
    unfold Sets.complement.
    destruct H0 as [[t2 [t3 [st2' ?]]] | [t2 [t3 [st2' ?]]]].
    destruct H0. left. exists t2. exists t3. exists st2'. tauto.
    right. exists t2. exists t3. exists st2'. tauto.
  + right. unfold if_sem.
    unfold union_sem, seq_sem, test_sem.
    left. exists 1. exists t1. exists st; split.
    simpl. unfold Sets.full. tauto. split. tauto. lia.
  + right. unfold if_sem.
    unfold union_sem, seq_sem, test_sem.
    right. exists 1. exists t1. exists st; split.
    simpl. unfold Sets.complement, Sets.empty. tauto. split. tauto. lia.
  + pose proof loop_unrolling b c st st3 t1.
    simpl in H.
    left. tauto.
Qed.
    
    
Lemma ceval_preserve: forall c1 c2 st1 st2, 
  cstep (c1, st1) (c2, st2) ->
  forall st3, (exists t1, ceval c2 st2 t1 st3) -> (exists t2, ceval c1 st1 t2 st3).
Proof.
  intros.
  pose proof ceval_preserve_1 c1 c2 st1 st2.
  assert (forall (st3 : state) (t1 : Z),
     ceval c2 st2 t1 st3 -> ceval c1 st1 t1 st3 \/ ceval c1 st1 (t1 + 1) st3).
  apply H1. tauto. clear H1.
  pose proof H2 st3. clear H2.
  destruct H0.
  pose proof H1 x.
  apply H2 in H0.
  destruct H0.
  + exists x. tauto.
  + exists (x+1)%Z. tauto.
Qed.


Theorem semantic_equiv_com2: forall c st1 st2,
  multi_cstep (c, st1) (Skip, st2) -> (exists t : Z, ceval c st1 t st2).
Proof.
  intros.
  remember (CSkip) as c' eqn:H0.
  induction_1n H.
  simpl; intros; subst.
  + simpl.
    unfold skip_sem. exists 0.
    split. reflexivity.
    reflexivity.
  + pose proof ceval_preserve _ _ _ _ H st2.
    tauto.
Qed.


(* ################################################################# *)
(** * Final Theorem of semantic equivalence between the second Denotational Semantics and Small Step Semantics. *)
Theorem semantic_equiv: forall c st1 st2, 
  (exists t: Z, ceval c st1 t st2) <-> multi_cstep (c, st1) (CSkip, st2).
Proof.
  intros.
  split.
  + apply semantic_equiv_com1.
  + apply semantic_equiv_com2.
Qed.
