Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import PL.RTClosure.
Require Import PL.Imp.


Print clos_refl_trans.
Print Sets.

(** Third Denotational Semantics with traces **)

Module T3.

Definition skip_sem: state -> list state -> state -> Prop :=
  fun st1 sts st2 =>
    st1 = st2 /\ sts = [].

Definition asgn_sem (X: var) (E: aexp): state -> list state -> state -> Prop :=
  fun st1 sts st2 =>
    st2 X = aeval E st1 /\
    forall Y, X <> Y -> st1 Y = st2 Y /\
    sts = [st2].

Definition seq_sem (d1 d2: state -> list state -> state -> Prop)
  : state -> list state -> state -> Prop
:=
  fun st1 sts st3 =>
    exists sts_1 sts_2 st2,
      d1 st1 sts_1 st2 /\ d2 st2 sts_2 st3 /\ sts = sts_1 ++ sts_2.
      
Definition test_sem (X: state -> Prop): state -> list state -> state -> Prop :=
  fun st1 sts st2 =>
    st1 = st2 /\ X st1 /\ sts = [st2].

Definition union_sem (d d': state -> list state -> state -> Prop)
  : state -> list state -> state -> Prop
:=
  fun st1 sts st2 =>
    d st1 sts st2 \/ d' st1 sts st2.
    
Definition if_sem (b: bexp) (d1 d2: state -> list state -> state -> Prop)
  : state -> list state -> state -> Prop
:=
  union_sem
    (seq_sem (test_sem (beval b)) d1)
    (seq_sem (test_sem (beval (! b))) d2).

Fixpoint iter_loop_body
  (b: bexp)
  (loop_body: state -> list state -> state -> Prop)
  (n: nat)
  : state -> list state -> state -> Prop
:=
  match n with
  | O => test_sem (beval (! b))
  | S n' => seq_sem
              (test_sem (beval b))
              (seq_sem loop_body (iter_loop_body b loop_body n'))
  end.

Definition omega_union_sem (d: nat -> state -> list state -> state -> Prop)
  : state -> list state -> state -> Prop
:=
  fun st1 sts st2 => exists n, d n st1 sts st2.

Definition loop_sem (b: bexp) (loop_body: state -> list state -> state -> Prop)
  : state -> list state -> state -> Prop
:=
  omega_union_sem (iter_loop_body b loop_body).

Fixpoint ceval (c: com): state -> list state -> state -> Prop :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  end.
  
End T3.  

(* here we will prove that the first and the third denotational semantics are equivalent*)


Module Equivalence.

Print ceval.
Print T3.ceval.

Theorem Equivalence_bewteen_T1_T3:
forall c st1 st2,
ceval c st1 st2 ->
(exists sts: list state, T3.ceval c st1 sts st2).
Proof.
  intros.
  revert st1 st2 H. 
  induction c; subst; intros.
  + unfold ceval,BinRel.id in H.
    exists []. 
    unfold T3.ceval,T3.skip_sem.
    split. exact H. reflexivity.
  + unfold ceval in H. 
    destruct H.
    exists [st2].
    unfold T3.ceval,T3.asgn_sem. split.
    exact H. split.
    pose proof H0 Y. apply H2 in H1. exact H1. reflexivity.
  + simpl. unfold T3.seq_sem. unfold ceval, BinRel.concat in H. 
    destruct H. destruct H. 
    pose proof IHc1 st1 x. apply H1 in H. clear H1. destruct H.
    pose proof IHc2 x st2. apply H1 in H0. clear H1. destruct H0.
    exists (x0++x1). exists x0. exists x1. exists x. tauto.
  + unfold ceval, if_sem, BinRel.union in H. destruct H.
    simpl. unfold T3.if_sem, T3.union_sem.
    - unfold BinRel.concat in H.
      unfold BinRel.test_rel in H.
      destruct H. destruct H.
      pose proof IHc1 x st2. apply H1 in H0. clear H1.
      destruct H0. exists ([st1]++x0). left.
      unfold T3.seq_sem. exists [st1]. exists x0. exists st1.
      split.
      * unfold T3.test_sem. split. 
        tauto. split. destruct H.
        exact H1. reflexivity.
      * split. destruct H. rewrite H. tauto. tauto.
    - unfold BinRel.concat in H.
      unfold BinRel.test_rel in H.
      destruct H. destruct H.
      pose proof IHc2 x st2. apply H1 in H0. clear H1.
      destruct H0. exists ([st1]++x0). right.
      unfold T3.seq_sem. exists [st1]. exists x0. exists st1.
      split.
      * unfold T3.test_sem. split. 
        tauto. split. destruct H.
        exact H1. reflexivity.
      * split. destruct H. rewrite H. tauto. tauto.
  + unfold ceval, loop_sem, BinRel.omega_union in H.
    destruct H. revert x st1 st2 H. induction x.
    - intros. unfold iter_loop_body, BinRel.test_rel in H.
      simpl. unfold T3.loop_sem, T3.omega_union_sem.
      exists [st2]. unfold T3.iter_loop_body. exists 0%nat.
      unfold T3.test_sem. tauto.
    - intros. unfold iter_loop_body, BinRel.test_rel in IHx.
      unfold iter_loop_body,BinRel.concat in H.
      destruct H. destruct H.
      destruct H0. destruct H0.
      pose proof IHc x0 x1. apply H2 in H0. clear H2.
      pose proof IHx x1 st2.
      apply H2 in H1. clear H2.
      destruct H0. destruct H1.
      unfold BinRel.test_rel in H.
      destruct H.
      simpl. exists ([st1]++x2++x3). unfold T3.loop_sem.
      unfold T3.omega_union_sem.
      unfold T3.ceval,T3.loop_sem,T3.omega_union_sem in H1.
      destruct H1. exists (S x4). 
      unfold T3.iter_loop_body.
      unfold T3.seq_sem, T3.test_sem. 
      exists [st1]. exists (x2 ++ x3). exists st1.
      split.
      * split. reflexivity. split. exact H2. reflexivity.
      * split. 
        ++ exists x2. exists x3. exists x1.
           split. rewrite H. exact H0.
           unfold T3.iter_loop_body in H1.
           split. 2:{tauto. }
           exact H1.
        ++ tauto.
Qed.
    
   

