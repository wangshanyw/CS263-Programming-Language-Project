## Equivalence among 3 denotational semantics and small step semantics
---
### 1 Tasks and Progression
- [x] A general theorem for proving equivalence between two recursively defined semantics
- [x] Equivalence among three recursively defined denotational semantics: the normal one, the one with time, and the one with traces 
- [x] Equivalence between small step semantics and each of denotational semantics
### 2 Compilation for our work
- Compile `Imp.v`, `RTClosure.v`, `ImpExt.v`, `ImpCF.v` to found the environment
- Compile `Denotational_Semantics_2.v`,`Denotational_Semantics_3.v`,`Equivalence_Semantics_1.v` for further proof
### 3 Proof corresponding to files
- 3 definitions of denotational semantics
  - `Imp.v`contains the normal one
  - `Denotational_Semantics_1.v`: the normal one denoted by `skip_sem` and so on
  - `Denotational_Semantics_2.v`: the one with time
  - `Denotational_Semantics_3.v`: the one with traces
- General Theorem and Proof on equivalence between each 2 Denotational Semantics with General Theorem
  - `equiv_sem_final.v`
- Proof on equivalence between each 2 Denotational Semantics
  - `Equivalence_Denotational_Semantics_1_2.v`
  - `Equivalence_Denotational_Semantics_1_3.v`
- Proof on equivalence between Small Steps Semantics and each of Denotational Semantics
  - `Equivalence_Semantics_1.v`: normal one
  - `Equivalence_Semantics_2.v`: the one with time
  - `Equivalence_Semantics_3.v`: the one with traces
### 4 Construction of General Theorem
In our proof, we view the abstract `denotation` as Type instead of each of the concrete denotational semantics.
- First, we suppose that our final goal is based on building the relation between `denotation1` and `denotation2`
  We want to construct a general theorem that given a `relation R`, if all corresponding statement pairs satisfy such a relation, the `denotation1` and `denotation2` satisfy `relation R`.
- Second, we induct 5 types of sem: `skip_sem, asgn_sem, seq_sem, if_sem, loop_sem`as `sem`.
- Third, we define the `denotation` by `sem`.
- Fourth, we define the condition that means `CSkip, CAss, CSeq, CIf, CWhile` statements of 2 different denotations have `relation R` respectively. 
- Finaly, we work out our general theorem:
  ```
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
  ```
  Note that the `relation R` given in our proof is equivalence relation, so we can finally achieve the equivalence of two denotational semantics through this theorem.
### 5 Proof on the equivalence between 2 denotational semantics based on the general theorem
- First, we give the definition of equivalence relation between 2 concrete denotational semantics.
  For example, 
  ```
  Definition sem_r(d1:state -> state -> Prop)(d2:state -> list state -> state -> Prop): Prop :=
  forall st1 st2, d1 st1 st2 -> exists sts,d2 st1 sts st2.
  ```
- Then, we can use the general theorem to prove the equivalence between 2 denotational semantics.
### 6 Proof on the equivalence between denotational semantics and small step semantics
- First, we work out the definition of `equivalence` between denotational semantics and small step semantics.
  Take the second denotational semantics as an example.
  ```
  Theorem semantic_equiv: forall c st1 st2, 
  (exists t: Z, ceval c st1 t st2) <-> multi_cstep (c, st1) (CSkip, st2).
  ```
- Then we prove it from two directions through induction method.

### 7 Contributors
F1903003 易文龙 @[yiwenlong2001](https://github.com/yiwenlong2001)

F1903002 张若涵 @[wangshanyw](https://github.com/wangshanyw)
