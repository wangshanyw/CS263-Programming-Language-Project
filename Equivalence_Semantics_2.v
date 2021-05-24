Require Import PL.Imp PL.ImpExt PL.RTClosure.
Local Open Scope imp.

Require Import PL.Denotational_Semantics_2.
Require Import PL.Equivalence_Semantics_1.

Print ceval.




(* ################################################################# *)
(** * From Denotations To Multi-step Relations *)

Lemma semantic_equiv_iter_loop1: forall st1 st2 n b c, 
  (forall st1 st2, (exists t: Z, ceval c st1 t st2) -> multi_cstep (c, st1) (Skip, st2)) ->
  (exists n0 : nat, iter_loop_body b (ceval c) n0 st1 n st2) ->
  multi_cstep (While b Do c EndWhile, st1) (Skip, st2).
Proof.
Admitted.
(*   intros.
  revert st1 st2 H0; induction n; intros.
  + destruct H0.
    induction x.
    - simpl in H0.
      unfold test_sem, Sets.complement in H0.
      destruct H0. destruct H1. discriminate H2.
    - simpl in H0.
      apply IHx. clear IHx.
      unfold test_sem, seq_sem at 1 in H0.
      destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H2.
      unfold seq_sem in H1.
      destruct H1. destruct H1. destruct H1. destruct H1. destruct H1. destruct H5.
      rewrite H0. 
      
      destruct H5. rewrite H3 in H4. 
      destruct H0. destruct H1. discriminate H2.
      
      etransitivity_1n; [apply CS_While |].
      
      
      etransitivity. apply multi_congr_CIf. apply semantic_equiv_bexp1_false.
      discriminate H1.
    multi_congr_CIf, semantic_equiv_bexp1_false.
     H0 |].
    etransitivity_1n; [apply CS_IfFalse |].
    rewrite H0. reflexivity.
  + simpl in H0.
    unfold seq_sem at 1, test_sem in H0.
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. 
    destruct H1.
    unfold seq_sem in H1.
    destruct H1. destruct H1. destruct H1. destruct H1. destruct H3.
    etransitivity_1n; [apply CS_While |]. destruct H0. destruct H5.
    etransitivity; [apply multi_congr_CIf, semantic_equiv_bexp1_true, H5 |].
    etransitivity_1n; [apply CS_IfTrue |].
    etransitivity. apply multi_congr_CSeq.
    pose proof H st1 x5. apply H7. exists x3. rewrite H0. tauto.
    etransitivity_1n; [apply CS_Seq |].
    pose proof IHn x5 st2.
    apply H7. exists x4. tauto.
Qed. *)

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

Print cstep.

Lemma ceval_preserve: forall c1 c2 st1 st2,
  cstep (c1, st1) (c2, st2) ->
  forall st3, ((exists t1, ceval c2 st2 t1 st3) -> (exists t2, ceval c1 st1 t2 st3)).
  
Proof.
  intros.
  revert st3 H0.
  induction_cstep H; simpl; intros.
  + apply aeval_preserve in H.
    unfold asgn_sem in H0.
    unfold asgn_sem.
    rewrite H.
    tauto.
  + unfold skip_sem in H1.
    unfold asgn_sem.
    destruct H1. destruct H1. exists 1. split.
    rewrite H1 in H. unfold aeval. unfold constant_func. tauto.
    rewrite <- H1. intros. pose proof H0 Y. apply H4 in H3. tauto.
  + unfold seq_sem in H0.
    unfold seq_sem.
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. 
    destruct H1.
    pose proof IHcstep x2.
    assert (exists t2 : Z, ceval c1 st t2 x2). apply H3. exists x0. tauto.
    exists x. exists x0. exists x1. exists x2. split.
    2: { tauto. }
    
    
    
    
    destruct H3. exists x0. tauto.
      
    
Admitted.

  + rewrite ceval_CSeq in H0.
    rewrite ceval_CSeq.
    unfold BinRel.concat in H0.
    unfold BinRel.concat.
    destruct H0 as [st2' [? ?]].
    exists st2'.
    specialize (IHcstep _ H0).
    tauto.
  + rewrite ceval_CSeq.
    unfold BinRel.concat, BinRel.id.
    exists st.
    split.
    - reflexivity.
    - exact H0.
  + rewrite ceval_CIf in H0.
    rewrite ceval_CIf.
    unfold if_sem in H0.
    unfold if_sem.
    unfold BinRel.union,
           BinRel.concat,
           BinRel.test_rel in H0.
    unfold BinRel.union,
           BinRel.concat,
           BinRel.test_rel.
    apply beval_preserve in H.
    simpl in H0.
    simpl.
    unfold Sets.complement in H0.
    unfold Sets.complement.
    destruct H0 as [[st2' ?] | [st2' ?]]; [left | right];
      exists st2'; tauto.
  + rewrite ceval_CIf.
    unfold if_sem.
    unfold BinRel.union,
           BinRel.concat,
           BinRel.test_rel.
    left; exists st; simpl.
    unfold Sets.full; tauto.
  + rewrite ceval_CIf.
    unfold if_sem.
    unfold BinRel.union,
           BinRel.concat,
           BinRel.test_rel.
    right; exists st; simpl.
    unfold Sets.complement, Sets.empty; tauto.
  + pose proof loop_unrolling b c.
    unfold com_equiv, BinRel.equiv in H.
    specialize (H st st3).
    tauto.
Qed. *)

Theorem semantic_equiv_com2: forall c st1 st2,
  multi_cstep (c, st1) (Skip, st2) -> exists t : Z, ceval c st1 t st2.
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

Theorem semantic_equiv: forall c st1 st2, 
  (exists t: Z, ceval c st1 t st2) <-> multi_cstep (c, st1) (CSkip, st2).
Proof.
  intros.
  split.
  + apply semantic_equiv_com1.
  + apply semantic_equiv_com2.
Qed.

(* Print semantic_equiv_aexp1. *)

(* ################################################################# *)
(** * From Denotations To Multi-step Relations *)
(** Recall theorems proved in Equivalence_Semantics_1.
    Theorem semantic_equiv_aexp1: 
    forall st a n, aeval a st = n -> multi_astep st a (ANum n).
    
    Theorem semantic_equiv_bexp1: 
    forall st b,
    (beval b st -> multi_bstep st b BTrue) /\
    (~ beval b st -> multi_bstep st b BFalse).
    
    Corollary semantic_equiv_bexp1_true: 
    forall st b, beval b st -> multi_bstep st b BTrue.
    
    Corollary semantic_equiv_bexp1_false: 
    forall st b, (Sets.complement (beval b) st -> multi_bstep st b BFalse).


