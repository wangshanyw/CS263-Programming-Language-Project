Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import PL.RTClosure.
Require Import PL.Imp. Import Assertion_D. Import Abstract_Pretty_Printing.

(** Second denotational semantics for our simple imperative language. This time, a program's denotation is defined as a ternary relation. Specifically, [st1, t, st2] belongs to the denotation of program [c] if and only if executing [c] from [st1] may take time [t] and stop at state [st2]. Assume every assignment command takes one unit of time, every
testing (for either if-command, or loop condition testing) takes one unit of time and the [Skip] command does not take any time. *)

Module T2.

Definition skip_sem: state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st1 = st2 /\ t = 0.

Definition asgn_sem (X: var) (E: aexp): state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st2 X = aeval E st1 /\
    forall Y, X <> Y -> st1 Y = st2 Y /\
    t = 1.

Definition seq_sem (d1 d2: state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  fun st1 t st3 =>
    exists t1 t2 st2,
      d1 st1 t1 st2 /\ d2 st2 t2 st3 /\ t = t1 + t2.

Definition test_sem (X: state -> Prop): state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st1 = st2 /\ X st1 /\ t = 1.

Definition union_sem (d d': state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  fun st1 t st2 =>
    d st1 t st2 \/ d' st1 t st2.

Definition if_sem (b: bexp) (d1 d2: state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  union_sem
    (seq_sem (test_sem (beval b)) d1)
    (seq_sem (test_sem (beval (! b))) d2).

Fixpoint iter_loop_body
  (b: bexp)
  (loop_body: state -> Z -> state -> Prop)
  (n: nat)
  : state -> Z -> state -> Prop
:=
  match n with
  | O => test_sem (beval (! b))
  | S n' => seq_sem
              (test_sem (beval b))
              (seq_sem loop_body (iter_loop_body b loop_body n'))
  end.

Definition omega_union_sem (d: nat -> state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  fun st1 t st2 => exists n, d n st1 t st2.

Definition loop_sem (b: bexp) (loop_body: state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  omega_union_sem (iter_loop_body b loop_body).

Fixpoint ceval (c: com): state -> Z -> state -> Prop :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  end.

End T2.

(* here is the proof of the equivalence bewteen T1 and T2 *)

Module Equivalence.

Print ceval.
Print T2.ceval.

Theorem Equivalence_bewteen_T1_T2:
forall c st1 st2,
ceval c st1 st2 ->
(exists t: Z, T2.ceval c st1 t st2).
Proof.
  intros. revert st1 st2 H. 
  induction c; subst; intros.
  + unfold ceval, BinRel.id in H. unfold T2.ceval,T2.skip_sem. 
    rewrite H. exists 0. tauto.
  + unfold ceval in H. unfold T2.ceval, T2.asgn_sem.
    exists 1. destruct H. split. exact H. split. 
    pose proof H0 Y. apply H2 in H1. clear H2. tauto. lia.
  + simpl. unfold T2.seq_sem. unfold ceval, BinRel.concat in H. 
    destruct H. destruct H. 
    pose proof IHc1 st1 x. apply H1 in H. clear H1. destruct H.
    pose proof IHc2 x st2. apply H1 in H0. clear H1. destruct H0.
    exists (x0+x1). exists x0. exists x1. exists x. tauto.
  + unfold ceval, if_sem, BinRel.union in H. destruct H.
    simpl. unfold T2.if_sem, T2.union_sem.
    - unfold BinRel.concat in H.
      unfold BinRel.test_rel in H.
      destruct H. destruct H.
      pose proof IHc1 x st2. apply H1 in H0. clear H1.
      destruct H0. exists (x0+1). left.
      unfold T2.seq_sem. exists 1. exists x0. exists st1.
      split.
      * unfold T2.test_sem. split. 
        tauto. split. destruct H.
        exact H1. lia.
      * split. destruct H. rewrite H. tauto. lia.
    - unfold BinRel.concat in H.
      unfold BinRel.test_rel in H.
      destruct H. destruct H.
      pose proof IHc2 x st2. apply H1 in H0. clear H1.
      destruct H0. exists (x0+1). right.
      unfold T2.seq_sem. exists 1. exists x0. exists st1.
      split.
      * unfold T2.test_sem. split. 
        tauto. split. destruct H.
        exact H1. lia.
      * split. destruct H. rewrite H. tauto. lia.
  + unfold ceval, loop_sem, BinRel.omega_union in H.
    destruct H. revert x st1 st2 H. induction x.
    - intros. unfold iter_loop_body, BinRel.test_rel in H.
      simpl. unfold T2.loop_sem, T2.omega_union_sem.
      exists 1. unfold T2.iter_loop_body. exists 0%nat.
      unfold T2.test_sem. tauto.
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
      simpl. exists (x3+x2+1). unfold T2.loop_sem.
      unfold T2.omega_union_sem.
      unfold T2.ceval,T2.loop_sem,T2.omega_union_sem in H1.
      destruct H1. exists (S x4). 
      unfold T2.iter_loop_body.
      unfold T2.seq_sem, T2.test_sem. 
      exists 1. exists (x3 + x2). exists st1.
      split.
      * split. reflexivity. split. exact H2. lia.
      * split. 
        ++ exists x2. exists x3. exists x1.
           split. rewrite H. exact H0.
           unfold T2.iter_loop_body in H1.
           split. 2:{lia. }
           exact H1.
        ++ lia.
Qed.



           