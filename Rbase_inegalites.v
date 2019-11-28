(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import Reals.
Require Import Psatz.
Require Import Tactiques.
Require Import Rbase_operations.

Open Scope R_scope.

Lemma Rlt_gt : forall x y : R, x < y -> y > x.
Proof.
auto with *.
Qed.
Hint Resolve Rlt_gt: real.


Lemma Rge_minus : forall x y z : R, y <= z -> x - y >= x - z.
Proof.
intros; lra.
Qed.
Hint Resolve Rge_minus: real.


Lemma Rlt_add_compatibility : forall x y z : R, x < y + z -> x - y < z. 
Proof.
intros; lra.
Qed.
Hint Resolve Rlt_add_compatibility: real.


Lemma Rlt_add_compatibility2 : forall x y z : R, x - z < y -> x < y + z.
Proof.
intros; lra.
Qed.
Hint Resolve Rlt_add_compatibility2: real.


Lemma Rle_add_compatibility : forall x y z : R, x + y <= z -> x <= z - y.
Proof.
intros; lra.
Qed.
Hint Resolve Rle_add_compatibility: real.


Lemma Rle_sub_compatibility : forall x y z : R, x <= z + y -> x - y <= z.
Proof.
intros; lra.
Qed.
Hint Resolve Rle_sub_compatibility: real. 


Lemma Rle_sub_compatibility2 : forall x y z : R, x - y <= z -> x <= z + y.
Proof.
intros; lra.
Qed.
Hint Resolve Rle_sub_compatibility2: real.


Lemma Rlt_add_compatibility3 : forall x y z : R, x < z - y -> x + y < z.
Proof.
intros; lra.
Qed.
Hint Resolve Rlt_add_compatibility3: real.


Lemma Rlt_sub_compatibility : forall x y z : R, x + y < z -> x < z - y.
Proof.
intros; lra.
Qed.
Hint Resolve Rlt_sub_compatibility: real.


Lemma Rlt_add_compatibility4 : forall x y z : R, x - y < z -> x < y + z.
Proof.
intros; lra.
Qed.
Hint Resolve Rlt_add_compatibility4: real.


Lemma Rle_sub_r : forall r r1 r2 : R, r2 <= r1 -> r - r1 <= r - r2.
Proof.
intros; lra.
Qed.
Hint Resolve Rle_sub_r: real.


Lemma Rmult_le :
 forall r1 r2 r3 r4 : R,
 r3 >= 0 -> r2 > 0 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.
intros.
apply Rle_lt_trans with (r2 * r3);
 [ apply Rmult_le_compat_r; [ apply Rge_le; auto | auto ]
 | apply Rmult_lt_compat_l; auto ].
apply Rlt_le; auto.
Qed.
Hint Resolve Rmult_le: real.


Lemma Rlt_r_O : forall r1 r2 r : R, r = 0 -> r1 < r2 + r -> r1 < r2.
Proof.
intros.
generalize H0; rewrite H; rewrite Rplus_0_r; auto.
Qed.
Hint Resolve Rlt_r_O: real. 


Lemma Rlt_sub_O : forall r1 r2 : R, 0 < r1 - r2 -> r2 < r1.
Proof.
intros; lra.
Qed.
Hint Resolve Rlt_sub_O: real.


Lemma mega_nul : forall r r1 r2 : R, 0 < r -> r1 < r * r2 -> r1 * / r < r2.
Proof.
intros.
apply Rmult_lt_reg_l with r; [ assumption | idtac ].
rewrite Rmult_comm; rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
rewrite RIneq.Rmult_1_r; assumption.
apply Rgt_not_eq; apply Rlt_gt; assumption.
Qed.
Hint Resolve mega_nul: real.


Lemma Rle_Rinv_monotony :
 forall r r1 r2 : R, 0 < r -> r1 <= r * r2 -> / r * r1 <= r2.
Proof.
intros.
apply Rmult_le_reg_l with r; auto.
rewrite <- Rmult_assoc; replace (r * / r) with 1.
rewrite Rmult_comm; rewrite RIneq.Rmult_1_r; auto.
rewrite Rmult_comm; apply Rinv_l_sym; apply Rgt_not_eq; apply Rlt_gt; auto.
Qed.
Hint Resolve Rle_Rinv_monotony: real. 


Lemma Rlt_Rinv_l_to_r :
 forall r r1 r2 : R, 0 < r -> r1 * r < r2 -> r1 < r2 * / r.
Proof.
intros.
apply Rmult_lt_reg_l with r; auto.
rewrite Rmult_comm.
apply Rgt_lt.
rewrite <- Rmult_assoc; rewrite Rmult_comm; rewrite <- Rmult_assoc;
 rewrite <- Rinv_l_sym.
rewrite Rmult_comm; rewrite RIneq.Rmult_1_r; apply Rlt_gt; auto.
apply Rgt_not_eq; apply Rlt_gt; auto.
Qed.
Hint Resolve Rlt_Rinv_l_to_r: real.


Lemma Rmult_lt_pos_bis : forall x y : R, 0 > x -> 0 > y -> 0 < x * y.
Proof.
intros.
RingReplace (x * y) (- x * - y); auto with real.
apply Rmult_lt_0_compat; auto with real.
Qed.
Hint Resolve Rmult_lt_pos_bis: real.


Lemma Rinv_le : forall r r1 : R, 0 < r -> 0 < r1 -> r1 <= r -> / r <= / r1.
Proof.
intros.
apply Rmult_le_reg_l with r1; auto.
apply Rmult_le_reg_l with r; auto.
rewrite Rmult_comm; rewrite Rmult_assoc.
replace (/ r * r) with 1;
 [ idtac | apply Rinv_l_sym; apply Rgt_not_eq; apply Rlt_gt; auto ].
replace (r1 * / r1) with 1;
 [ idtac | apply Rinv_r_sym; apply Rgt_not_eq; apply Rlt_gt; auto ].
do 2 rewrite RIneq.Rmult_1_r; auto.
Qed.
Hint Resolve Rinv_le: real.


Lemma Rle_mult_inv :
 forall r r1 r2 : R, r > 0 -> r1 * r <= r2 -> r1 <= r2 * / r.
Proof.
intros.
apply Rmult_le_reg_l with r; auto.
rewrite <- Rmult_assoc.
replace (r * r2 * / r) with r2;
 [ rewrite Rmult_comm; auto
 | symmetry  in |- *; apply Rinv_r_simpl_m; apply Rgt_not_eq; auto ].
Qed.
Hint Resolve Rle_mult_inv: real.



