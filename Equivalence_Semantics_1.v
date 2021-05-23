Require Import PL.Imp PL.ImpExt PL.RTClosure.
Local Open Scope imp.

(* ################################################################# *)
(** The equivalence between the first-defined denotational semantics and small step semantics**)

(* ################################################################# *)
(** * From Denotations To Multi-step Relations *)
Theorem semantic_equiv_aexp1: forall st a n,
  aeval a st = n -> multi_astep st a (ANum n).
Proof.
  intros.
  revert n H; induction a; intros; simpl in H.
  + unfold constant_func in H.
    rewrite H.
    reflexivity.
  + rewrite <- H.
    etransitivity_n1; [reflexivity |].
    apply AS_Id.
  + etransitivity.
    { apply multi_congr_APlus1, IHa1. reflexivity. }
    etransitivity_n1.
    { apply multi_congr_APlus2; [apply AH_num |]. apply IHa2. reflexivity. }
    rewrite <- H.
    apply AS_Plus.
  + etransitivity.
    { apply multi_congr_AMinus1, IHa1. reflexivity. }
    etransitivity_n1.
    { apply multi_congr_AMinus2; [apply AH_num |]. apply IHa2. reflexivity. }
    rewrite <- H.
    apply AS_Minus.
  + etransitivity.
    { apply multi_congr_AMult1, IHa1. reflexivity. }
    etransitivity_n1.
    { apply multi_congr_AMult2; [apply AH_num |]. apply IHa2. reflexivity. }
    rewrite <- H.
    apply AS_Mult.
Qed.

Theorem semantic_equiv_bexp1: forall st b,
  (beval b st -> multi_bstep st b BTrue) /\
  (~ beval b st -> multi_bstep st b BFalse).
Proof.
  intros.
  induction b; simpl.
  + split.
    - intros.
      reflexivity.
    - unfold Sets.full.
      tauto.
  + split.
    - unfold Sets.empty.
      tauto.
    - intros.
      reflexivity.
  + assert (multi_bstep st (a1 == a2) (aeval a1 st == aeval a2 st)).
    {
      etransitivity.
      - apply multi_congr_BEq1, semantic_equiv_aexp1.
        reflexivity.
      - apply multi_congr_BEq2; [apply AH_num |].
        apply semantic_equiv_aexp1.
        reflexivity.
    }
    split; unfold Func.test_eq; intros;
    (etransitivity_n1; [exact H |]).
    - apply BS_Eq_True, H0.
    - apply BS_Eq_False, H0.
  + assert (multi_bstep st (a1 <= a2) (aeval a1 st <= aeval a2 st)).
    {
      etransitivity.
      - apply multi_congr_BLe1, semantic_equiv_aexp1.
        reflexivity.
      - apply multi_congr_BLe2; [apply AH_num |].
        apply semantic_equiv_aexp1.
        reflexivity.
    }
    split; unfold Func.test_le; intros;
    (etransitivity_n1; [exact H |]).
    - apply BS_Le_True, H0.
    - apply BS_Le_False.
      lia.
  + destruct IHb as [IH1 IH2].
    split; intros.
    - etransitivity_n1.
      * apply multi_congr_BNot, IH2.
        unfold Sets.complement in H; exact H.
      * apply BS_NotFalse.
    - etransitivity_n1.
      * apply multi_congr_BNot, IH1.
        unfold Sets.complement in H; tauto.
      * apply BS_NotTrue.
  + destruct IHb1 as [IHb11 IHb12].
    destruct IHb2 as [IHb21 IHb22].
    pose proof classic (beval b1 st).
    destruct H.
    - assert (multi_bstep st (b1 && b2) b2).
      {
        etransitivity_n1.
        * apply multi_congr_BAnd, IHb11, H.
        * apply BS_AndTrue.
      }
      split; unfold Sets.intersect; intros;
      (etransitivity; [exact H0 |]).
      * apply IHb21; tauto.
      * apply IHb22; tauto.
    - split; unfold Sets.intersect; intros; [ tauto |].
      etransitivity_n1.
      * apply multi_congr_BAnd, IHb12, H.
      * apply BS_AndFalse.
Qed.

Corollary semantic_equiv_bexp1_true: forall st b,
  beval b st -> multi_bstep st b BTrue.
Proof. intros. pose proof semantic_equiv_bexp1 st b. tauto. Qed.
  
Corollary semantic_equiv_bexp1_false: forall st b,
  (Sets.complement (beval b) st -> multi_bstep st b BFalse).
Proof. intros. pose proof semantic_equiv_bexp1 st b. tauto. Qed.

Lemma semantic_equiv_iter_loop1: forall st1 st2 n b c,
  (forall st1 st2, ceval c st1 st2 -> multi_cstep (c, st1) (Skip, st2)) ->
  iter_loop_body b (ceval c) n st1 st2 ->
  multi_cstep (While b Do c EndWhile, st1) (Skip, st2).
Proof.
  intros.
  revert st1 st2 H0; induction n; intros.
  + simpl in H0.
    unfold BinRel.test_rel in H0.
    destruct H0.
    subst st2.
    etransitivity_1n; [apply CS_While |].
    etransitivity; [apply multi_congr_CIf, semantic_equiv_bexp1_false, H1 |].
    etransitivity_1n; [apply CS_IfFalse |].
    reflexivity.
  + simpl in H0.
    unfold BinRel.concat at 1,
           BinRel.test_rel in H0.
    destruct H0 as [st [[? H0] ?]]; subst st.
    unfold BinRel.concat in H2.
    destruct H2 as [st1' [? ?]].
    etransitivity_1n; [apply CS_While |].
    etransitivity; [apply multi_congr_CIf, semantic_equiv_bexp1_true, H0 |].
    etransitivity_1n; [apply CS_IfTrue |].
    etransitivity; [apply multi_congr_CSeq, H, H1 |].
    etransitivity_1n; [apply CS_Seq |].
    apply IHn, H2.
Qed.

Theorem semantic_equiv_com1: forall st1 st2 c,
  ceval c st1 st2 -> multi_cstep (c, st1) (Skip, st2).
Proof.
  intros.
  revert st1 st2 H; induction c; intros.
  + rewrite ceval_CSkip in H.
    unfold BinRel.id in H.
    rewrite H.
    reflexivity.
  + rewrite ceval_CAss in H.
    destruct H.
    etransitivity_n1.
    - apply multi_congr_CAss, semantic_equiv_aexp1.
      reflexivity.
    - apply CS_Ass; tauto.
  + Print ceval.
    rewrite ceval_CSeq in H.
    unfold BinRel.concat in H.
    destruct H as [st' [? ?]].
    etransitivity; [apply multi_congr_CSeq, IHc1, H |].
    etransitivity_1n; [ apply CS_Seq |].
    apply IHc2, H0.
  + rewrite ceval_CIf in H.
    unfold if_sem in H.
    unfold BinRel.union,
           BinRel.concat,
           BinRel.test_rel in H.
    pose proof semantic_equiv_bexp1 st1 b.
    destruct H0.
    destruct H as [H | H]; destruct H as [st [[? ?] ?]]; subst st.
    - etransitivity; [apply multi_congr_CIf, H0, H2 |].
      etransitivity_1n; [apply CS_IfTrue |].
      apply IHc1, H3.
    - etransitivity; [apply multi_congr_CIf, H1, H2 |].
      etransitivity_1n; [apply CS_IfFalse |].
      apply IHc2, H3.
  + rewrite ceval_CWhile in H.
    unfold loop_sem in H.
    unfold BinRel.omega_union in H.
    destruct H as [n ?].
    apply semantic_equiv_iter_loop1 with n.
    - exact IHc.
    - exact H.
Qed.

(* ################################################################# *)
(** * From Multi-step Relations To Denotations *)

Lemma aeval_preserve: forall st a1 a2,
  astep st a1 a2 ->
  aeval a1 st  = aeval a2 st.
Proof.
  intros.
  induction H.
  + simpl.
    reflexivity.
  + simpl.
    unfold Func.add.
    lia.
  + simpl.
    unfold Func.add.
    lia.
  + simpl.
    unfold Func.add, constant_func.
    reflexivity.
  + simpl.
    unfold Func.sub.
    lia.
  + simpl.
    unfold Func.sub.
    lia.
  + simpl.
    unfold Func.sub, constant_func.
    reflexivity.
  + simpl.
    unfold Func.mul.
    nia.
  + simpl.
    unfold Func.mul.
    nia.
  + simpl.
    unfold Func.mul, constant_func.
    reflexivity.
Qed.

Theorem semantic_equiv_aexp2: forall st a n,
  multi_astep st a (ANum n) -> aeval a st = n.
Proof.
  intros.
  induction_1n H.
  + simpl.
    reflexivity.
  + pose proof aeval_preserve _ _ _ H.
    lia.
Qed.

Lemma beval_preserve: forall st b1 b2,
  bstep st b1 b2 ->
  (beval b1 st  <-> beval b2 st).
Proof.
  intros.
  induction H.
  + apply aeval_preserve in H.
    simpl.
    unfold Func.test_eq.
    lia.
  + apply aeval_preserve in H0.
    simpl.
    unfold Func.test_eq.
    lia.
  + simpl.
    unfold Func.test_eq, Sets.full.
    tauto.
  + simpl.
    unfold Func.test_eq, Sets.empty.
    tauto.
  + apply aeval_preserve in H.
    simpl.
    unfold Func.test_le.
    lia.
  + apply aeval_preserve in H0.
    simpl.
    unfold Func.test_le.
    lia.
  + simpl.
    unfold Func.test_le, Sets.full.
    tauto.
  + simpl.
    unfold Func.test_le, constant_func, Sets.empty.
    lia.
  + simpl.
    unfold Sets.complement.
    tauto.
  + simpl.
    unfold Sets.complement, Sets.full, Sets.empty.
    tauto.
  + simpl.
    unfold Sets.complement, Sets.full, Sets.empty.
    tauto.
  + simpl.
    unfold Sets.intersect.
    tauto.
  + simpl.
    unfold Sets.intersect, Sets.full.
    tauto.
  + simpl.
    unfold Sets.intersect, Sets.empty.
    tauto.
Qed.

Theorem semantic_equiv_bexp2: forall st b TF,
  multi_bstep st b TF ->
  (TF = BTrue -> beval b st) /\
  (TF = BFalse -> ~ beval b st).
Proof.
  intros.
  induction_1n H; simpl; intros.
  + split; intros; subst; simpl; unfold Sets.full, Sets.empty; tauto.
  + pose proof beval_preserve _ _ _ H.
    tauto.
Qed.

Lemma ceval_preserve: forall c1 c2 st1 st2,
  cstep (c1, st1) (c2, st2) ->
  forall st3, ceval c2 st2 st3 -> ceval c1 st1 st3.
Proof.
(** We could prove a stronger conclusion:

    forall st3, ceval c1 st1 st3 <-> ceval c2 st2 st3.

But this single direction version is enough to use. *)
  intros.
  revert st3 H0.
  induction_cstep H; simpl; intros.
  + apply aeval_preserve in H.
    rewrite ceval_CAss in H0.
    rewrite ceval_CAss.
    rewrite H.
    tauto.
  + rewrite ceval_CSkip in H1.
    rewrite ceval_CAss.
    unfold BinRel.id in H1.
    subst.
    tauto.
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
Qed.

Theorem semantic_equiv_com2: forall c st1 st2,
  multi_cstep (c, st1) (CSkip, st2) -> ceval c st1 st2.
Proof.
  intros.
  remember (CSkip) as c' eqn:H0.
  revert H0; induction_1n H; simpl; intros; subst.
  + simpl.
    unfold BinRel.id.
    reflexivity.
  + pose proof ceval_preserve _ _ _ _ H st2.
    tauto.
Qed.

(* ################################################################# *)
(** * Final Theorem *)

Theorem semantic_equiv: forall c st1 st2,
  ceval c st1 st2 <-> multi_cstep (c, st1) (CSkip, st2).
Proof.
  intros.
  split.
  + apply semantic_equiv_com1.
  + apply semantic_equiv_com2.
Qed.