Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import PL.RTClosure.
Require Import PL.Imp.


(** Third Denotational Semantics with traces **)

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