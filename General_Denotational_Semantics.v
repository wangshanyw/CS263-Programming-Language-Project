Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import PL.RTClosure.
Require Import PL.Imp. Import Assertion_D. Import Abstract_Pretty_Printing.


(* Here, we will demonstrate that once two kind of Denotational Semantics has some particular properties, they are definitely equvalent. *)

(* Actually, it is not hard to find that each kind of definition has similair or even the same structure in the following form:

Fixpoint ceval (c: com): state -> Z -> state -> Prop :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  end.
  
*)

(* Thus it hits me that if every fixpoint matches some equivalence-condition, then the final destination could be easy to reach.*)


(* step 1. In the first point, I will define a TriRel just as BinRel. *)

Print BinRel.

(*
Module Sets.

Definition full {A: Type}: A -> Prop := fun _ => True.

Definition empty {A: Type}: A -> Prop := fun _ => False.

Definition intersect {A: Type} (X Y: A -> Prop) := fun a => X a /\ Y a.

Definition complement {A: Type} (X: A -> Prop) := fun a => ~ X a.

Definition equiv {A: Type} (X Y: A -> Prop): Prop :=
  forall a, X a <-> Y a.

End Sets.
*)

(* 
Module
BinRel
:= Struct
     Definition id : forall A : Type, A -> A -> Prop.
     Definition empty : forall A B : Type, A -> B -> Prop.
     Definition concat :
       forall A B C : Type, (A -> B -> Prop) -> (B -> C -> Prop) -> A -> C -> Prop.
     Definition filter1 : forall A B : Type, (A -> Prop) -> A -> B -> Prop.
     Definition filter2 : forall A B : Type, (B -> Prop) -> A -> B -> Prop.
     Definition union :
       forall A B : Type, (A -> B -> Prop) -> (A -> B -> Prop) -> A -> B -> Prop.
     Definition intersection :
       forall A B : Type, (A -> B -> Prop) -> (A -> B -> Prop) -> A -> B -> Prop.
     Definition omega_union : forall A B : Type, (nat -> A -> B -> Prop) -> A -> B -> Prop.
     Definition test_rel : forall A : Type, (A -> Prop) -> A -> A -> Prop.
     Definition equiv : forall A B : Type, (A -> B -> Prop) -> (A -> B -> Prop) -> Prop.
     Definition le : forall A B : Type, (A -> B -> Prop) -> (A -> B -> Prop) -> Prop.
   End
*)


Module TriRel.

Definition id {A B: Type}: A -> B -> A -> Prop := fun a b c => a = c.

Definition empty {A B C: Type}: A -> B -> C -> Prop := fun a b c=> False.

Definition concat {A B C D E F: Type} (r1: A -> B -> C -> Prop) (r2: C -> D -> E -> Prop): A -> F -> E -> Prop :=
  fun a f e => exists b d c, r1 a b c /\ r2 c d e.
  
Definition union {A B C: Type} (r1 r2: A -> B -> C -> Prop): A -> B -> C -> Prop :=
  fun a b c => r1 a b c \/ r2 a b c.
  
Definition omega_union {A B C: Type} (rs: nat -> A -> B -> C -> Prop): A -> B -> C -> Prop :=
  fun st1 b st2 => exists n, rs n st1 b st2.
  
Definition test_rel {A B} (X: A -> B -> Prop): A -> B -> A -> Prop :=
  fun st1 b st2 => st1 = st2 /\ X st1.

End TriRel.