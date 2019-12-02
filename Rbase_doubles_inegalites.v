(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import Reals.
Require Import Lra.
Require Import Tactiques.
Require Import Rbase_operations.
Require Import Rbase_inegalites.


Lemma penible : forall r r1 : R, r < r1 /\ - r1 < r -> - r1 < r < r1.
Proof.
intros.
split; elim H; intros; auto.
Qed.
Hint Resolve penible: real. 


Lemma Rlt_2_Ropp : forall r r1 r2 : R, - r2 < - r < - r1 -> r1 < r < r2.
Proof.
intros.
elim H; intros.
split; apply Ropp_lt_cancel; auto.
Qed.
Hint Resolve Rlt_2_Ropp: real.


Lemma Rlt_2_Ropp_r : forall r r1 r2 : R, r2 < r < r1 -> - r1 < - r < - r2.
Proof.
intros.
elim H; intros.
split; apply Ropp_lt_contravar; auto.
Qed.
Hint Resolve Rlt_2_Ropp_r: real.


Lemma Rlt_2_le_lt_and :
 forall r r1 r2 r3 r4 : R, r1 < r < r2 -> r3 <= r1 /\ r2 < r4 -> r3 < r < r4.
Proof.
intros.
elim H; intros.
elim H0; intros.
split.
apply Rle_lt_trans with r1; auto.
apply Rlt_trans with r2; auto.
Qed.
Hint Resolve Rlt_2_le_lt_and: real.


Lemma Rlt_2_le_lt :
 forall r r1 r2 r3 r4 : R, r1 < r < r2 -> r3 <= r1 -> r2 < r4 -> r3 < r < r4.
Proof.
intros.
generalize (Rlt_2_le_lt_and r r1 r2 r3 r4); tauto.
Qed.
Hint Resolve Rlt_2_le_lt: real.


Lemma Rlt_le_2_gauss :
 forall r r1 : R,
 r1 - 1 * / 2 < r <= r1 + 1 * / 2 ->
 r - 1 <= r1 - 1 * / 2 /\ r1 + 1 * / 2 < r + 1.
Proof.
intros.
split.
apply Rle_sub_compatibility.
rewrite Rplus_comm; rewrite Rsub_sym; rewrite <- Rplus_assoc.
replace (1 + - (1 * / 2)) with (1 * / 2);
 [ idtac | field; apply Rgt_not_eq; lra ].
elim H; intros.
rewrite Rplus_comm; auto.

apply Rlt_add_compatibility2.
rewrite Rplus_comm; rewrite Rsub_sym; rewrite <- Rplus_assoc.
replace (-(1) + 1 * / 2) with (- (1 * / 2)) by
 ( field; apply Rgt_not_eq; lra).
rewrite <- Rsub_sym.
elim H; intros; assumption.
Qed.
Hint Resolve Rlt_le_2_gauss: real.


Lemma Rlt_2_Rmult_Rinv :
 forall r r1 r2 r3 : R, 0 < r -> r1 < r2 * r < r3 -> r1 * / r < r2 < r3 * / r.
Proof.
intros.
elim H0; intros; clear H0; split.
apply mega_nul; auto; rewrite Rmult_comm; auto.
apply Rmult_lt_reg_l with r; auto.
rewrite Rmult_comm; apply Rgt_lt; rewrite Rmult_comm;
 rewrite Rmult_assoc. 
rewrite <- Rinv_l_sym;
 [ rewrite RIneq.Rmult_1_r; apply Rlt_gt; auto
 | apply Rgt_not_eq; apply Rlt_gt; auto ].
Qed.
Hint Resolve Rlt_2_Rmult_Rinv: real.


Lemma Rlt_2_monotony :
 forall r1 r2 r3 r4 r5 r6 : R,
 r1 < r2 < r3 -> r4 < r5 < r6 -> r1 + r4 < r2 + r5 < r3 + r6.
Proof.
intros.
elim H; intros; clear H.
elim H0; intros; clear H0.
split; auto with real.
Qed.
Hint Resolve Rlt_2_monotony: real.


Lemma Rlt_2_monotony_rev :
 forall r r1 r2 r3 : R, 0 < r -> r1 * r < r2 * r < r3 * r -> r1 < r2 < r3.
Proof.
intros.
elim H0; intros; clear H0.
split.
apply Rmult_lt_reg_l with r; auto.
rewrite Rmult_comm; apply Rgt_lt; rewrite Rmult_comm; apply Rlt_gt;
 auto.
apply Rmult_lt_reg_l with r; auto.
rewrite Rmult_comm; apply Rgt_lt; rewrite Rmult_comm; apply Rlt_gt;
 auto.
Qed.
Hint Resolve Rlt_2_monotony_rev: real.


Lemma Rabsolu_def3 : forall r r1 : R, Rabs r < r1 -> - r1 < r < r1.
Proof.
intros.
apply penible.
generalize H; apply Rabs_def2.
Qed.
Hint Resolve Rabsolu_def3: real.


Lemma Rle_lt_2_lt :
 forall r1 r2 r3 r4 r5 : R,
 r1 < r2 <= r3 -> r4 < r1 -> r3 < r5 -> r4 < r2 < r5.
Proof.
intros.
split.
apply Rlt_trans with r1; auto.
elim H; intros; auto.
apply Rle_lt_trans with r3; auto.
elim H; intros; auto.
Qed.
Hint Resolve Rle_lt_2_lt: real.


Lemma Rlt_2_monotony_contra :
 forall r r1 r2 r3 : R, r < 0 -> r * r3 < r * r2 < r * r1 -> r1 < r2 < r3.  
Proof.
intros.
elim H0; intros.
split.
apply Rmult_lt_reg_l with (- r); auto with real.
do 2 rewrite Ropp_mult_distr_l_reverse; apply Ropp_lt_contravar; auto.
apply Rmult_lt_reg_l with (- r); auto with real.
do 2 rewrite Ropp_mult_distr_l_reverse; apply Ropp_lt_contravar; auto.
Qed.
Hint Resolve Rlt_2_monotony_contra: real.


Lemma Rle_2_Rlt_2 :
 forall r r1 r2 r3 r4 : R, r2 < r < r3 -> r1 <= r2 -> r3 <= r4 -> r1 < r < r4. 
Proof.
intros.
elim H; intros; split.
apply Rle_lt_trans with r2; auto.
apply Rlt_le_trans with r3; auto.
Qed.
Hint Resolve Rle_2_Rlt_2: real. 


Lemma Rle_mult_lt :
 forall r1 r2 r3 r4 r5 r6 : R,
 r1 < r2 < r5 ->
 r3 < r4 < r6 ->
 0 < r2 -> 0 <= r3 -> 0 <= r4 -> 0 < r5 -> r1 * r3 < r2 * r4 < r5 * r6.
Proof.
intros.
elim H; intros; clear H.
elim H0; intros; clear H0.
split; apply Rmult_le; auto with real.
Qed.
Hint Resolve Rle_mult_lt : real.


Lemma Rlt_2_trans :
 forall r1 r2 r3 r4 r5 : R,
 r1 < r2 < r3 -> r4 < r1 -> r3 < r5 -> r4 < r2 < r5.
Proof.
intros.
split.
apply Rlt_trans with r1; auto.
elim H; intros; auto.
apply Rlt_trans with r3; auto.
elim H; intros; auto.
Qed.
Hint Resolve Rlt_2_trans: real.


Lemma Rlt_2_minus_r :
 forall r r1 r2 r3 : R, r1 - r < r2 - r < r3 - r -> r1 < r2 < r3.
Proof.
intros.
elim H; intros.
split; apply Rplus_lt_reg_r with (- r); repeat rewrite <- Rsub_sym; auto.
Qed.
Hint Resolve Rlt_2_minus_r: real. 


Lemma Rlt_2_Rinv :
 forall r1 r2 r3 : R,
 r1 > 0 -> r2 > 0 -> r3 > 0 -> r3 < r2 < r1 -> 1 * / r1 < 1 * / r2 < 1 * / r3.
Proof.
intros.
split; repeat rewrite Rmult_1l; apply Rinv_lt_contravar;
 [ apply Rmult_lt_0_compat; auto
 | elim H2; auto
 | apply Rmult_lt_0_compat; auto
 | elim H2; auto ].
Qed.
Hint Resolve Rlt_2_Rinv: real.


Lemma Rlt_2_to_Rlt : forall r1 r2 r3 : R, r1 < r2 < r3 -> r2 < r3.
Proof.
intros.
elim H; auto.
Qed.
Hint Resolve Rlt_2_to_Rlt: real.


Lemma Rlt_2_sqrt :
 forall r1 r2 r3 : R,
 0 <= r1 -> 0 <= r2 -> 0 <= r3 -> r1 < r2 < r3 -> sqrt r1 < sqrt r2 < sqrt r3.
Proof.
intros.
intuition; apply sqrt_lt_1; auto.
Qed.
Hint Resolve Rlt_2_sqrt: real.
