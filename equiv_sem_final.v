Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import PL.RTClosure.
Require Import PL.Imp. Import Assertion_D. Import Abstract_Pretty_Printing.

Module T1.

Definition skip_sem: state -> state -> Prop :=
  fun st1 st2 =>
    st1 = st2.

Definition asgn_sem (X: var) (E: aexp): state -> state -> Prop :=
  fun st1 st2 =>
    st2 X = aeval E st1 /\
    forall Y, X <> Y -> st1 Y = st2 Y.

Definition seq_sem (d1 d2: state -> state -> Prop)
  : state -> state -> Prop
:= 
  fun st1 st3 =>
    exists st2,
      d1 st1 st2 /\ d2 st2 st3.

Definition if_sem
  (b: bexp)
  (then_branch else_branch: state -> state -> Prop)
  : state -> state -> Prop
:=
  BinRel.union
    (BinRel.concat (BinRel.test_rel (beval b)) then_branch)
    (BinRel.concat (BinRel.test_rel (beval (BNot b))) else_branch).

Fixpoint iter_loop_body (b: bexp)
                        (loop_body: state -> state -> Prop)
                        (n: nat): state -> state -> Prop :=
  match n with
  | O =>
         BinRel.test_rel (beval (BNot b))
  | S n' =>
         BinRel.concat
           (BinRel.test_rel (beval b))
           (BinRel.concat
              loop_body
              (iter_loop_body b loop_body n'))
  end.

Definition loop_sem (b: bexp) (loop_body: state -> state -> Prop):
  state -> state -> Prop :=
  BinRel.omega_union (iter_loop_body b loop_body).

Fixpoint ceval (c: com): state -> state -> Prop :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  end.
  
End T1.

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

Inductive sem (denotation: Type):=
  | Sem (skip_sem : denotation)
        (ass_sem : var -> aexp -> denotation)
        (seq_sem : denotation -> denotation -> denotation)
        (if_sem : bexp -> denotation -> denotation -> denotation)
        (loop_sem: bexp -> denotation ->denotation).
        
Arguments Sem {denotation} skip_sem ass_sem seq_sem if_sem loop_sem.

Definition semantic_skip {denotation: Type} (S: sem denotation) :=
  match S with
  | Sem skip_sem _ _ _ _ => skip_sem
  end.
  
Definition semantic_ass {denotation: Type} (S: sem denotation) :=
  match S with
  | Sem _ ass_sem _ _ _ => ass_sem
  end.
  
Definition semantic_seq {denotation: Type} (S: sem denotation) :=
  match S with
  | Sem _ _ seq_sem _ _ => seq_sem
  end.
  
Definition semantic_if {denotation: Type} (S: sem denotation) :=
  match S with
  | Sem _ _ _ if_sem _ => if_sem
  end.
  
Definition semantic_while {denotation: Type} (S: sem denotation) :=
  match S with
  | Sem _ _ _ _ loop_sem => loop_sem
  end.  
  
Fixpoint ceval_by_sem {denotation: Type} (S: sem denotation)
  (c : com) : denotation :=
  match c with
  | CSkip => semantic_skip S
  | CAss X E => semantic_ass S X E
  | CSeq c1 c2 => semantic_seq S (ceval_by_sem S c1) (ceval_by_sem S c2)
  | CIf b c1 c2 => semantic_if S b (ceval_by_sem S c1) (ceval_by_sem S c2)
  | CWhile b c => semantic_while S b (ceval_by_sem S c)
  end.  
  
Definition general_equiv {denotation1: Type}{denotation2: Type} (X : denotation1) (Y : denotation2)(R : denotation1 -> denotation2 -> Prop): Prop :=
  R X Y.  
  
Definition CSkip_equiv {denotation1: Type}{denotation2: Type} (d1 : sem denotation1)(d2 : sem denotation2)(R : denotation1 -> denotation2 -> Prop): Prop :=
  general_equiv(semantic_skip d1)(semantic_skip d2) R.
  
Definition CAss_equiv {denotation1: Type}{denotation2: Type} (d1 : sem denotation1)(d2 : sem denotation2)(R : denotation1 -> denotation2 -> Prop): Prop :=
  forall (X:var) (E:aexp), general_equiv(semantic_ass d1 X E)(semantic_ass d2 X E) R.
  
Definition CSeq_equiv {denotation1: Type}{denotation2: Type} (d1 : sem denotation1)(d2 : sem denotation2)(R : denotation1 -> denotation2 -> Prop): Prop :=
  forall c1 c2: com, 
  general_equiv(ceval_by_sem d1 c1)(ceval_by_sem d2 c1)R ->
  general_equiv(ceval_by_sem d1 c2)(ceval_by_sem d2 c2) R -> general_equiv(semantic_seq d1 (ceval_by_sem d1 c1) (ceval_by_sem d1 c2))(semantic_seq d2 (ceval_by_sem d2 c1) (ceval_by_sem d2 c2)) R.
  
Definition CIf_equiv {denotation1: Type}{denotation2: Type} (d1 : sem denotation1)(d2 : sem denotation2)(R : denotation1 -> denotation2 -> Prop): Prop :=
  forall (b:bexp) (c1 c2: com),
  general_equiv(ceval_by_sem d1 c1)(ceval_by_sem d2 c1)R ->
  general_equiv(ceval_by_sem d1 c2)(ceval_by_sem d2 c2) R -> 
  general_equiv(semantic_if d1 b (ceval_by_sem d1 c1) (ceval_by_sem d1 c2))(semantic_if d2 b (ceval_by_sem d2 c1) (ceval_by_sem d2 c2)) R.
  
Definition CWhile_equiv {denotation1: Type}{denotation2: Type} (d1 : sem denotation1)(d2 : sem denotation2)(R : denotation1 -> denotation2 -> Prop): Prop :=
  forall (b:bexp)(c:com), 
  general_equiv(ceval_by_sem d1 c)(ceval_by_sem d2 c)R ->
  general_equiv(semantic_while d1 b (ceval_by_sem d1 c))(semantic_while d2 b (ceval_by_sem d2 c)) R.
  
Theorem final_proof_of_equiv{denotation1: Type}{denotation2: Type}:
  forall (d1: sem denotation1) (d2: sem denotation2),
  forall c,
  forall (R : denotation1 -> denotation2 -> Prop),
  CSkip_equiv d1 d2 R->
  CAss_equiv d1 d2 R->
  CSeq_equiv d1 d2 R->
  CIf_equiv d1 d2 R->
  CWhile_equiv d1 d2 R->
  general_equiv(ceval_by_sem d1 c)(ceval_by_sem d2 c) R.
Proof.
  intros.
  unfold general_equiv.
  unfold CSkip_equiv in H.
  unfold CAss_equiv in H0.
  unfold CSeq_equiv in H1.
  unfold CIf_equiv in H2.
  unfold CWhile_equiv in H.
  induction c; unfold ceval_by_sem; try tauto.
  pose proof H0 X a. tauto. 
  pose proof H1 c1 c2. tauto.
  pose proof H2 b c1 c2. tauto.
  pose proof H3 b c. tauto.
Qed.

Lemma sem_equiv_t2:
forall c st1 st2 t,
ceval_by_sem (Sem T2.skip_sem T2.asgn_sem T2.seq_sem T2.if_sem T2.loop_sem) c st1 t st2 <-> T2.ceval c st1 t st2.
Proof.
  induction c; simpl; try tauto.
  + unfold T2.seq_sem. intros. split. 
    ++ intros. destruct H. destruct H. destruct H. destruct H. pose proof IHc1 st1 x1 x. apply H1 in H. clear H1. destruct H0. pose proof IHc2 x1 st2 x0. apply H2 in H0. clear H2. exists x. exists x0. exists x1. tauto.
    ++ intros. destruct H. destruct H. destruct H. destruct H. pose proof IHc1 st1 x1 x. apply H1 in H. clear H1. destruct H0. pose proof IHc2 x1 st2 x0. apply H2 in H0. clear H2. exists x. exists x0. exists x1. tauto.
  + unfold T2.if_sem. unfold T2.union_sem. unfold T2.seq_sem. intros. split.
    ++ intros. destruct H.
      +++ destruct H. destruct H. destruct H. destruct H. unfold T2.test_sem in H. destruct H. destruct H0. pose proof IHc1 x1 st2 x0. apply H3 in H0. clear H3. left. exists 1. exists x0. exists st1. unfold T2.test_sem. split. tauto. rewrite H. destruct H1. split. tauto. rewrite H3 in H2. tauto.
      +++ destruct H. destruct H. destruct H. destruct H. unfold T2.test_sem in H. destruct H. destruct H0. pose proof IHc2 x1 st2 x0. apply H3 in H0. clear H3. right. exists 1. exists x0. exists st1. unfold T2.test_sem. split. tauto. rewrite H. destruct H1. split. tauto. rewrite H3 in H2. tauto.
    ++ intros. destruct H.
      +++ destruct H. destruct H. destruct H. destruct H. unfold T2.test_sem in H. destruct H. destruct H0. pose proof IHc1 x1 st2 x0. apply H3 in H0. clear H3. left. exists 1. exists x0. exists st1. unfold T2.test_sem. split. tauto. rewrite H. destruct H1. split. tauto. rewrite H3 in H2. tauto.
      +++ destruct H. destruct H. destruct H. destruct H. unfold T2.test_sem in H. destruct H. destruct H0. pose proof IHc2 x1 st2 x0. apply H3 in H0. clear H3. right. exists 1. exists x0. exists st1. unfold T2.test_sem. split. tauto. rewrite H. destruct H1. split. tauto. rewrite H3 in H2. tauto.
  + unfold T2.loop_sem. unfold T2.omega_union_sem. intros. split.
    ++ intros. destruct H. revert x st1 st2 t H. induction x; intros.
      +++ exists 0%nat. unfold T2.iter_loop_body in H. unfold T2.iter_loop_body. tauto.
      +++ unfold T2.iter_loop_body in H. unfold T2.seq_sem in H. destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. pose proof IHc x2 x5 x3. apply H3 in H0. clear H3. destruct H2. pose proof IHx x5 st2 x4. apply H4 in H2. clear H4. destruct H2. exists(S x6). unfold T2.iter_loop_body. unfold T2.seq_sem. exists 1. exists x1. unfold T2.test_sem in H. destruct H. destruct H4. rewrite H5 in H1. unfold T2.test_sem. exists st1. split. tauto. split. exists x3. exists x4. exists x5. split. rewrite H. tauto. tauto. tauto.
    ++ intros. destruct H. revert x st1 st2 t H. induction x; intros.
      +++ exists 0%nat. unfold T2.iter_loop_body in H. unfold T2.iter_loop_body. tauto.
      +++ unfold T2.iter_loop_body in H. unfold T2.seq_sem in H. destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. pose proof IHc x2 x5 x3. apply H3 in H0. clear H3. destruct H2. pose proof IHx x5 st2 x4. apply H4 in H2. clear H4. destruct H2. exists(S x6). unfold T2.iter_loop_body. unfold T2.seq_sem. exists 1. exists x1. unfold T2.test_sem in H. destruct H. destruct H4. rewrite H5 in H1. unfold T2.test_sem. exists st1. split. tauto. split. exists x3. exists x4. exists x5. split. rewrite H. tauto. tauto. tauto.
Qed.

Lemma sem_equiv_t1:
forall c st1 st2,
ceval_by_sem (Sem T1.skip_sem T1.asgn_sem T1.seq_sem T1.if_sem T1.loop_sem) c st1 st2 <-> T1.ceval c st1 st2.
Proof.
  induction c; simpl; try tauto.
  + unfold T1.seq_sem. intros. split. 
    ++ intros. destruct H. destruct H. pose proof IHc1 st1 x. apply H1 in H. clear H1. pose proof IHc2 x st2. apply H1 in H0. clear H1. exists x. tauto.
    ++ intros. destruct H. destruct H. pose proof IHc1 st1 x. apply H1 in H. clear H1. pose proof IHc2 x st2. apply H1 in H0. clear H1. exists x. tauto.
  + unfold T1.if_sem. unfold BinRel.union. unfold BinRel.concat. intros. split.
    ++ intros. destruct H.
      +++ destruct H. destruct H. destruct H. destruct H. pose proof IHc1 st1 st2. apply H in H0. clear H. left. exists st1. unfold BinRel.test_rel. split. tauto. tauto. 
      +++ destruct H. destruct H. destruct H. destruct H. pose proof IHc2 st1 st2. apply H in H0. clear H. right. exists st1. unfold BinRel.test_rel. split. tauto. tauto. 
    ++ intros. destruct H.
      +++ destruct H. destruct H. destruct H. destruct H. pose proof IHc1 st1 st2. apply H in H0. clear H. left. exists st1. unfold BinRel.test_rel. split. tauto. tauto. 
      +++ destruct H. destruct H. destruct H. destruct H. pose proof IHc2 st1 st2. apply H in H0. clear H. right. exists st1. unfold BinRel.test_rel. split. tauto. tauto. 
  + unfold T1.loop_sem. unfold BinRel.omega_union. intros. split.
    ++ intros. destruct H. revert x st1 st2 H. induction x; intros.
      +++ exists 0%nat. unfold T1.iter_loop_body in H. unfold T1.iter_loop_body. tauto.
      +++ unfold T1.iter_loop_body in H. unfold T1.seq_sem in H. destruct H. destruct H. destruct H. destruct H. unfold BinRel.concat in H0. destruct H0. destruct H. pose proof IHc st1 x0. apply H2 in H. clear H2. pose proof IHx  x0 st2. apply H2 in H0. clear H2. destruct H0. exists(S x1). unfold T1.iter_loop_body. unfold BinRel.concat. unfold BinRel.test_rel. exists st1. split. tauto. exists x0. split. tauto. tauto. 
    ++ intros. destruct H. revert x st1 st2 H. induction x; intros.
      +++ exists 0%nat. unfold T1.iter_loop_body in H. unfold T1.iter_loop_body. tauto.
      +++ unfold T1.iter_loop_body in H. unfold T1.seq_sem in H. destruct H. destruct H. destruct H. destruct H. unfold BinRel.concat in H0. destruct H0. destruct H. pose proof IHc st1 x0. apply H2 in H. clear H2. pose proof IHx  x0 st2. apply H2 in H0. clear H2. destruct H0. exists(S x1). unfold T1.iter_loop_body. unfold BinRel.concat. unfold BinRel.test_rel. exists st1. split. tauto. exists x0. split. tauto. tauto. 
Qed.

Lemma sem_equiv_t3:
forall c st1 st2 sts,
ceval_by_sem (Sem T3.skip_sem T3.asgn_sem T3.seq_sem T3.if_sem T3.loop_sem) c st1 sts st2 <-> T3.ceval c st1 sts st2.
Proof.
  induction c; simpl; try tauto.
  + unfold T3.seq_sem. intros. split. 
    ++ intros. destruct H. destruct H. destruct H. destruct H. pose proof IHc1 st1 x1 x. apply H1 in H. clear H1. destruct H0. pose proof IHc2 x1 st2 x0. apply H2 in H0. clear H2. exists x. exists x0. exists x1. tauto.
    ++ intros. destruct H. destruct H. destruct H. destruct H. pose proof IHc1 st1 x1 x. apply H1 in H. clear H1. destruct H0. pose proof IHc2 x1 st2 x0. apply H2 in H0. clear H2. exists x. exists x0. exists x1. tauto.
  + unfold T3.if_sem. unfold T3.union_sem. unfold T3.seq_sem. intros. split.
    ++ intros. destruct H.
      +++ destruct H. destruct H. destruct H. destruct H. unfold T3.test_sem in H. destruct H. destruct H0. pose proof IHc1 x1 st2 x0. apply H3 in H0. clear H3. left. exists [st1]. exists x0. exists st1. unfold T3.test_sem. split. tauto. rewrite H. destruct H1. split. tauto. rewrite H3 in H2. tauto.
      +++ destruct H. destruct H. destruct H. destruct H. unfold T3.test_sem in H. destruct H. destruct H0. pose proof IHc2 x1 st2 x0. apply H3 in H0. clear H3. right. exists [st1]. exists x0. exists st1. unfold T3.test_sem. split. tauto. rewrite H. destruct H1. split. tauto. rewrite H3 in H2. tauto.
    ++ intros. destruct H.
      +++ destruct H. destruct H. destruct H. destruct H. unfold T3.test_sem in H. destruct H. destruct H0. pose proof IHc1 x1 st2 x0. apply H3 in H0. clear H3. left. exists [st1]. exists x0. exists st1. unfold T3.test_sem. split. tauto. rewrite H. destruct H1. split. tauto. rewrite H3 in H2. tauto.
      +++ destruct H. destruct H. destruct H. destruct H. unfold T3.test_sem in H. destruct H. destruct H0. pose proof IHc2 x1 st2 x0. apply H3 in H0. clear H3. right. exists [st1]. exists x0. exists st1. unfold T3.test_sem. split. tauto. rewrite H. destruct H1. split. tauto. rewrite H3 in H2. tauto.
  + unfold T3.loop_sem. unfold T3.omega_union_sem. intros. split.
    ++ intros. destruct H. revert x st1 st2 sts H. induction x; intros.
      +++ exists 0%nat. unfold T3.iter_loop_body in H. unfold T3.iter_loop_body. tauto.
      +++ unfold T3.iter_loop_body in H. unfold T3.seq_sem in H. destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. pose proof IHc x2 x5 x3. apply H3 in H0. clear H3. destruct H2. pose proof IHx x5 st2 x4. apply H4 in H2. clear H4. destruct H2. exists(S x6). unfold T2.iter_loop_body. unfold T2.seq_sem. exists x0. exists x1. unfold T3.test_sem in H. destruct H. destruct H4. rewrite H5 in H1. unfold T3.test_sem. exists st1. split. split. tauto. split. tauto. rewrite H. tauto. split. exists x3. exists x4. exists x5. split. rewrite H. tauto. tauto. rewrite H5. tauto.
    ++ intros. destruct H. revert x st1 st2 sts H. induction x; intros.
      +++ exists 0%nat. unfold T3.iter_loop_body in H. unfold T3.iter_loop_body. tauto.
      +++ unfold T3.iter_loop_body in H. unfold T3.seq_sem in H. destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. pose proof IHc x2 x5 x3. apply H3 in H0. clear H3. destruct H2. pose proof IHx x5 st2 x4. apply H4 in H2. clear H4. destruct H2. exists(S x6). unfold T2.iter_loop_body. unfold T2.seq_sem. exists x0. exists x1. unfold T3.test_sem in H. destruct H. destruct H4. rewrite H5 in H1. unfold T3.test_sem. exists st1. split. split. tauto. split. tauto. rewrite H. tauto. split. exists x3. exists x4. exists x5. split. rewrite H. tauto. tauto. rewrite H5. tauto.
Qed.


Definition sem_r(d1:state -> state -> Prop)(d2:state -> Z -> state -> Prop): Prop :=
 forall st1 st2, d1 st1 st2 -> exists t,d2 st1 t st2.
 
Definition sem_r1(d1:state -> state -> Prop)(d2:state -> list state -> state -> Prop): Prop :=
 forall st1 st2, d1 st1 st2 -> exists sts,d2 st1 sts st2.
 
Definition sem_r2(d1:state -> Z -> state -> Prop)(d2:state -> list state -> state -> Prop): Prop :=
 forall st1 st2 t, d1 st1 t st2 -> exists sts ,d2 st1 sts st2.
(*
Definition skip_r(st1:state)(st2:state): Prop :=
 T1.skip_sem st1 st2 -> exists t, T2.skip_sem st1 t st2.
 
Definition skip_r(st1:state)(st2:state): Prop :=
 T1.skip_sem st1 st2 -> exists t, T2.skip_sem st1 t st2.
 
Definition skip_r(st1:state)(st2:state): Prop :=
 T1.skip_sem st1 st2 -> exists t, T2.skip_sem st1 t st2.
 
Definition skip_r(st1:state)(st2:state): Prop :=
 T1.skip_sem st1 st2 -> exists t, T2.skip_sem st1 t st2.
*)
Theorem Equivalence_bewteen_T1_T2:
forall c st1 st2,
T1.ceval c st1 st2 ->
(exists t: Z, T2.ceval c st1 t st2).
Proof.
  intros.
  pose proof final_proof_of_equiv (Sem T1.skip_sem T1.asgn_sem T1.seq_sem T1.if_sem T1.loop_sem) (Sem T2.skip_sem T2.asgn_sem T2.seq_sem T2.if_sem T2.loop_sem) c sem_r.
  assert(CSkip_equiv (Sem T1.skip_sem T1.asgn_sem T1.seq_sem T1.if_sem T1.loop_sem)(Sem T2.skip_sem T2.asgn_sem T2.seq_sem T2.if_sem T2.loop_sem) sem_r).
  clear H0. unfold CSkip_equiv. unfold general_equiv. unfold semantic_skip. unfold sem_r. intros. unfold T1.skip_sem, BinRel.id in H0. unfold T2.skip_sem. rewrite H0. exists 0. tauto.
  assert(CAss_equiv (Sem T1.skip_sem T1.asgn_sem T1.seq_sem T1.if_sem T1.loop_sem)(Sem T2.skip_sem T2.asgn_sem T2.seq_sem T2.if_sem T2.loop_sem) sem_r).
  clear H0. unfold CAss_equiv. unfold general_equiv. unfold semantic_ass.   unfold sem_r. intros. unfold T1.asgn_sem in H0. unfold T2.asgn_sem. exists 1. destruct H0. split. tauto. split. destruct H0. pose proof H2 Y. apply H0 in H3. tauto. tauto.
  assert(CSeq_equiv (Sem T1.skip_sem T1.asgn_sem T1.seq_sem T1.if_sem T1.loop_sem)(Sem T2.skip_sem T2.asgn_sem T2.seq_sem T2.if_sem T2.loop_sem) sem_r ).
  clear H0 H1 H2. unfold CSeq_equiv. unfold general_equiv. unfold sem_r. intros. unfold semantic_seq. unfold semantic_seq in H2. unfold T1.seq_sem in H2. destruct H2. destruct H2. pose proof H0 st0 x. apply H4 in H2. clear H4. pose proof H1 x st3. apply H4 in H3. clear H4. unfold T2.seq_sem. destruct H2. destruct H3. exists (x0+x1). exists x0. exists x1. exists x. split. tauto. tauto.
  assert(CIf_equiv (Sem T1.skip_sem T1.asgn_sem T1.seq_sem T1.if_sem T1.loop_sem)(Sem T2.skip_sem T2.asgn_sem T2.seq_sem T2.if_sem T2.loop_sem) sem_r).
  clear H0 H1 H2 H3. unfold CIf_equiv. unfold general_equiv. unfold sem_r. intros. unfold semantic_if. unfold semantic_if in H2. unfold T1.if_sem in H2. unfold BinRel.union, BinRel.concat in H2. destruct H2. destruct H2. destruct H2. unfold BinRel.test_rel in H2. destruct H2. unfold T2.if_sem. unfold T2.union_sem. unfold T2.seq_sem. pose proof H0 x st3. apply H5 in H3. clear H5. destruct H3. exists (x0+1). left. exists 1. exists x0. unfold T2.test_sem. exists x. split. tauto. split. tauto. lia. destruct H2. destruct H2. destruct H2. unfold BinRel.test_rel in H2. destruct H2. unfold T2.if_sem. unfold T2.union_sem. unfold T2.seq_sem. pose proof H1 st0 st3. apply H2 in H3. clear H2. destruct H3. exists (x+1). right. exists 1. exists x. unfold T2.test_sem. exists st0. split. tauto. split. tauto. lia.
   assert(CWhile_equiv (Sem T1.skip_sem T1.asgn_sem T1.seq_sem T1.if_sem T1.loop_sem)(Sem T2.skip_sem T2.asgn_sem T2.seq_sem T2.if_sem T2.loop_sem) sem_r).
   clear H0 H1 H2 H3 H4. unfold CWhile_equiv. unfold general_equiv. unfold sem_r. intros. unfold semantic_while. unfold semantic_while in H1. unfold T1.loop_sem in H1. unfold BinRel.omega_union, T1.iter_loop_body in H1. destruct H1. revert x st0 st3 H1. induction x.
   + unfold BinRel.test_rel. intros. destruct H1. unfold T2.loop_sem. unfold T2.omega_union_sem, T2.iter_loop_body. exists 1. exists 0%nat. unfold T2.test_sem. tauto.
   + unfold BinRel.concat. intros. unfold T2.loop_sem. unfold T2.omega_union_sem. destruct H1. unfold BinRel.test_rel in H1. destruct H1. destruct H2. destruct H2. pose proof H0 x0 x1. apply H4 in H2. clear H4. destruct H2. pose proof IHx x1 st3. apply H4 in H3. clear H4. destruct H3. unfold T2.loop_sem in H3. unfold T2.omega_union_sem, T2.iter_loop_body in H3. destruct H3. destruct H1. exists(x2+x3+1). exists(S x4). unfold T2.iter_loop_body. unfold T2.seq_sem. exists 1. exists(x2+x3). unfold T2.test_sem. exists x0. split. tauto. split. exists x2. exists x3. exists x1. split. tauto. tauto. lia.
 + apply H0 in H1. unfold general_equiv in H1. unfold sem_r in H1. pose proof H1 st1 st2. pose proof sem_equiv_t1 c st1 st2. destruct H7. apply H8 in H. apply H6 in H. destruct H. pose proof sem_equiv_t2 c st1 st2 x. destruct H9. apply H9 in H. exists x. tauto. tauto. tauto. tauto. tauto.
Qed.

Theorem Equivalence_bewteen_T1_T3:
forall c st1 st2,
T1.ceval c st1 st2 ->
(exists sts: list state, T3.ceval c st1 sts st2).
Proof.
  intros.
  pose proof final_proof_of_equiv (Sem T1.skip_sem T1.asgn_sem T1.seq_sem T1.if_sem T1.loop_sem) (Sem T3.skip_sem T3.asgn_sem T3.seq_sem T3.if_sem T3.loop_sem) c sem_r1.
  assert(CSkip_equiv (Sem T1.skip_sem T1.asgn_sem T1.seq_sem T1.if_sem T1.loop_sem)(Sem T3.skip_sem T3.asgn_sem T3.seq_sem T3.if_sem T3.loop_sem) sem_r1).
  clear H0. unfold CSkip_equiv. unfold general_equiv. unfold semantic_skip. unfold sem_r1. intros. unfold T1.skip_sem, BinRel.id in H0. unfold T3.skip_sem. rewrite H0. exists []. tauto.
  assert(CAss_equiv (Sem T1.skip_sem T1.asgn_sem T1.seq_sem T1.if_sem T1.loop_sem)(Sem T3.skip_sem T3.asgn_sem T3.seq_sem T3.if_sem T3.loop_sem) sem_r1).
  clear H0. unfold CAss_equiv. unfold general_equiv. unfold semantic_ass.   unfold sem_r1. intros. unfold T1.asgn_sem in H1. unfold T3.asgn_sem. exists [st3]. destruct H0. split. tauto. split. destruct H0. pose proof H2 Y. apply H0 in H3. tauto. tauto.
  assert(CSeq_equiv (Sem T1.skip_sem T1.asgn_sem T1.seq_sem T1.if_sem T1.loop_sem)(Sem T3.skip_sem T3.asgn_sem T3.seq_sem T3.if_sem T3.loop_sem) sem_r1 ).
  clear H0 H1 H2. unfold CSeq_equiv. unfold general_equiv. unfold sem_r1. intros. unfold semantic_seq. unfold semantic_seq in H2. unfold T1.seq_sem in H2. destruct H2. destruct H2. pose proof H0 st0 x. apply H4 in H2. clear H4. pose proof H1 x st3. apply H4 in H3. clear H4. unfold T3.seq_sem. destruct H2. destruct H3. exists (x0 ++ x1). exists x0. exists x1. exists x. split. tauto. tauto.
  assert(CIf_equiv (Sem T1.skip_sem T1.asgn_sem T1.seq_sem T1.if_sem T1.loop_sem)(Sem T3.skip_sem T3.asgn_sem T3.seq_sem T3.if_sem T3.loop_sem) sem_r1).
  clear H0 H1 H2 H3. unfold CIf_equiv. unfold general_equiv. unfold sem_r1. intros. unfold semantic_if. unfold semantic_if in H2. unfold T1.if_sem in H2. unfold BinRel.union, BinRel.concat in H2. destruct H2. destruct H2. destruct H2. unfold BinRel.test_rel in H2. destruct H2. unfold T3.if_sem. unfold T3.union_sem. unfold T3.seq_sem. pose proof H0 x st3. apply H5 in H3. clear H5. destruct H3. exists ([st0]++x0). left. exists [st0]. exists x0. unfold T3.test_sem. exists x. split. split. tauto. split. tauto. rewrite H2. tauto. split. exact H3. tauto. destruct H2. destruct H2. destruct H2. unfold BinRel.test_rel in H2. destruct H2. unfold T3.if_sem. unfold T3.union_sem. unfold T3.seq_sem. pose proof H1 st0 st3. apply H2 in H3. clear H2. destruct H3. exists ([st0]++x). right. exists [st0]. exists x. unfold T3.test_sem. exists st0. split. split. tauto. split. tauto. tauto. split. exact H2. tauto. 
   assert(CWhile_equiv (Sem T1.skip_sem T1.asgn_sem T1.seq_sem T1.if_sem T1.loop_sem)(Sem T3.skip_sem T3.asgn_sem T3.seq_sem T3.if_sem T3.loop_sem) sem_r1).
   clear H0 H1 H2 H3 H4. unfold CWhile_equiv. unfold general_equiv. unfold sem_r1. intros. unfold semantic_while. unfold semantic_while in H1. unfold T1.loop_sem in H1. unfold BinRel.omega_union, T1.iter_loop_body in H1. destruct H1. revert x st0 st3 H1. induction x.
   + unfold BinRel.test_rel. intros. destruct H1. unfold T3.loop_sem. unfold T3.omega_union_sem, T3.iter_loop_body. exists [st0]. exists 0%nat. unfold T3.test_sem. split. tauto. split. tauto. rewrite H1. tauto.
   + unfold BinRel.concat. intros. unfold T3.loop_sem. unfold T3.omega_union_sem. destruct H1. unfold BinRel.test_rel in H1. destruct H1. destruct H2. destruct H2. pose proof H0 x0 x1. apply H4 in H2. clear H4. destruct H2. pose proof IHx x1 st3. apply H4 in H3. clear H4. destruct H3. unfold T3.loop_sem in H3. unfold T3.omega_union_sem, T2.iter_loop_body in H3. destruct H3. destruct H1. exists([st0] ++ x2 ++ x3). exists(S x4). unfold T3.iter_loop_body. unfold T3.seq_sem. exists [st0]. exists(x2++x3). unfold T3.test_sem. exists x0. split. split. tauto. split. tauto. rewrite H1. tauto. split. exists x2. exists x3. exists x1. split. tauto. tauto. tauto.
 + apply H0 in H1. unfold general_equiv in H1. unfold sem_r1 in H1. pose proof H1 st1 st2. pose proof sem_equiv_t1 c st1 st2. destruct H7. apply H8 in H. apply H6 in H. destruct H. pose proof sem_equiv_t3 c st1 st2 x. destruct H9. apply H9 in H. exists x. tauto. tauto. tauto. tauto. tauto.
Qed.

Theorem Equivalence_bewteen_T2_T3:
forall c st1 st2 t,
T2.ceval c st1 t st2 ->
(exists sts: list state, T3.ceval c st1 sts st2).
Proof.
  intros.
  pose proof final_proof_of_equiv (Sem T2.skip_sem T2.asgn_sem T2.seq_sem T2.if_sem T2.loop_sem) (Sem T3.skip_sem T3.asgn_sem T3.seq_sem T3.if_sem T3.loop_sem) c sem_r2.
  assert(CSkip_equiv (Sem T2.skip_sem T2.asgn_sem T2.seq_sem T2.if_sem T2.loop_sem)(Sem T3.skip_sem T3.asgn_sem T3.seq_sem T3.if_sem T3.loop_sem) sem_r2).
  clear H0. unfold CSkip_equiv. unfold general_equiv. unfold semantic_skip. unfold sem_r2. intros. unfold T2.skip_sem in H0. unfold T3.skip_sem. destruct H0. exists []. tauto.
  assert(CAss_equiv (Sem T2.skip_sem T2.asgn_sem T2.seq_sem T2.if_sem T2.loop_sem)(Sem T3.skip_sem T3.asgn_sem T3.seq_sem T3.if_sem T3.loop_sem) sem_r2).
  clear H0. unfold CAss_equiv. unfold general_equiv. unfold semantic_ass.   unfold sem_r2. intros. unfold T2.asgn_sem in H1. unfold T3.asgn_sem. exists [st3]. destruct H0. split. tauto. split. destruct H0. pose proof H2 Y. apply H0 in H3. tauto. tauto.
  assert(CSeq_equiv (Sem T2.skip_sem T2.asgn_sem T2.seq_sem T2.if_sem T2.loop_sem)(Sem T3.skip_sem T3.asgn_sem T3.seq_sem T3.if_sem T3.loop_sem) sem_r2 ).
  clear H0 H1 H2. unfold CSeq_equiv. unfold general_equiv. unfold sem_r2. intros. unfold semantic_seq. unfold semantic_seq in H2. unfold T2.seq_sem in H2. destruct H2. destruct H2. destruct H2. destruct H2. pose proof H0 st0 x1. apply H4 in H2. clear H4. pose proof H1 x1 st3. destruct H3. apply H4 in H3. clear H4. unfold T3.seq_sem. destruct H2. destruct H3. exists (x2 ++ x3). exists x2. exists x3. exists x1. split. tauto. tauto.
  assert(CIf_equiv (Sem T2.skip_sem T2.asgn_sem T2.seq_sem T2.if_sem T2.loop_sem)(Sem T3.skip_sem T3.asgn_sem T3.seq_sem T3.if_sem T3.loop_sem) sem_r2).
  clear H0 H1 H2 H3. unfold CIf_equiv. unfold general_equiv. unfold sem_r2. intros. unfold semantic_if. unfold semantic_if in H2. unfold T2.if_sem in H2. unfold T2.union_sem in H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H3. unfold T2.test_sem in H2. destruct H2. unfold T3.if_sem. unfold T3.union_sem. unfold T3.seq_sem. pose proof H0 x1 st3 x0. apply H6 in H3. clear H6. destruct H3. exists ([st0]++x2). left. exists [st0]. exists x2. unfold T3.test_sem. exists st0. split. split. tauto. split. tauto. rewrite H2. tauto. split. rewrite H2. exact H3. tauto. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H3. unfold T2.test_sem in H2. destruct H2. unfold T3.if_sem. unfold T3.union_sem. unfold T3.seq_sem. pose proof H1 st0 st3 x0. apply H2 in H3. clear H2. destruct H3. exists ([st0]++x1). right. exists [st0]. exists x1. unfold T3.test_sem. exists st0. split. split. tauto. split. tauto. tauto. split. exact H2. tauto.
   assert(CWhile_equiv (Sem T2.skip_sem T2.asgn_sem T2.seq_sem T2.if_sem T2.loop_sem)(Sem T3.skip_sem T3.asgn_sem T3.seq_sem T3.if_sem T3.loop_sem) sem_r2).
   clear H0 H1 H2 H3 H4. unfold CWhile_equiv. unfold general_equiv. unfold sem_r2. intros. unfold semantic_while. unfold semantic_while in H1. unfold T2.loop_sem in H1. unfold T2.omega_union_sem, T2.iter_loop_body in H1. destruct H1. revert x st0 st3 t0 H1. induction x.
   + unfold T2.test_sem. intros. destruct H1. unfold T3.loop_sem. unfold T3.omega_union_sem, T3.iter_loop_body. exists [st0]. exists 0%nat. unfold T3.test_sem. split. tauto. split. tauto. rewrite H1. tauto.
   + unfold T2.seq_sem. intros. unfold T3.loop_sem. unfold T3.omega_union_sem. destruct H1. unfold T2.test_sem in H1. destruct H1. destruct H1. destruct H1. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. pose proof H0 x2 x5 x3. apply H5 in H2. clear H5. destruct H2. destruct H4. pose proof IHx x5 st3 x4. apply H6 in H4. clear H6. destruct H4. unfold T3.loop_sem in H4. unfold T3.omega_union_sem, T2.iter_loop_body in H4. destruct H4. destruct H1. exists([st0] ++ x6 ++ x7). exists(S x8). unfold T3.iter_loop_body. unfold T3.seq_sem. exists [st0]. exists(x6++x7). unfold T3.test_sem. exists st0. split. split. tauto. split. tauto. rewrite H1. tauto. split. exists x6. exists x7. exists x5. split. rewrite H1. tauto. tauto. tauto.
 + apply H0 in H1. unfold general_equiv in H1. unfold sem_r1 in H1. pose proof H1 st1 st2. pose proof sem_equiv_t2 c st1 st2 t. destruct H7. apply H8 in H. apply H6 in H. destruct H. pose proof sem_equiv_t3 c st1 st2 x. destruct H9. apply H9 in H. exists x. tauto. tauto. tauto. tauto. tauto.
Qed.

 
  