Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import PL.RTClosure.
Require Import PL.Imp. Import Assertion_D. Import Abstract_Pretty_Printing.
  
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