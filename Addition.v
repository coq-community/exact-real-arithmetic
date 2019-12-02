(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import definition.
Require Import Tactiques.
Require Import Axiomes.
Require Export Lemmes_generaux.
Require Import Lemmes.
Require Import Psatz.
Require Import powerRZ_complements.
Require Import Rbase_operations.
Require Import Rbase_doubles_inegalites.
Require Import Rbase_inegalites.

Lemma addition_correct :
 forall (x y : R) (xc yc : Reelc),
 encadrement xc x ->
 encadrement yc y -> encadrement (addition_reelc xc yc) (x + y). 

Proof.
unfold encadrement in |- *.
intros x y xc yc H H1 n.
unfold addition_reelc in |- *.
generalize gauss_correct.
intros z; generalize (z (xc (n + 1) + yc (n + 1))%Z); clear z; intros.
elim H0; intros; clear H0.
apply
 Rlt_2_le_lt
  with
    (IZR (xc (n + 1)%Z - 1 + (yc (n + 1)%Z - 1)) * / INR B)
    (IZR (xc (n + 1)%Z + 1 + (yc (n + 1)%Z + 1)) * / INR B).
apply Rlt_2_Rmult_Rinv.
apply INR_B_non_nul.
do 2 rewrite plus_IZR.
unfold B_powerRZ in |- *.
rewrite Rmult_assoc;
 replace (powerRZ (INR B) n * INR B) with (powerRZ (INR B) (Z.succ n)). 
2: apply powerRZ_Zs; apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
generalize (H (Z.succ n)) (H1 (Z.succ n)); unfold B_powerRZ in |- *; intros;
 clear H H1. 
rewrite Rmult_plus_distr_r.
apply Rlt_2_monotony.
rewrite <- Z_R_minus; rewrite plus_IZR; auto.
rewrite <- Z_R_minus; rewrite plus_IZR; auto.
replace (IZR (xc (n + 1)%Z - 1 + (yc (n + 1)%Z - 1)))
 with (IZR (xc (n + 1)%Z + yc (n + 1)%Z) - 2).
rewrite Rmult_comm; rewrite Rmult_minus_distr_l.
apply Rle_trans with (/ INR B * IZR (xc (n + 1)%Z + yc (n + 1)%Z) - 1 * / 2).
rewrite Rmult_comm; apply Rle_sub_compatibility.
rewrite Rplus_comm; rewrite Rsub_sym; rewrite <- Rplus_assoc.
replace (1 + - (1 * / 2)) with (1 * / 2).
rewrite Rplus_comm; auto.
field; apply Rgt_not_eq; lra.
apply Rle_sub_r.
apply Rle_mult_inv.
lra.
rewrite Rmult_assoc; apply Rle_Rinv_monotony.
apply INR_B_non_nul.
rewrite RIneq.Rmult_1_r.
replace (2*2) with (INR 4) by (simpl; ring).
generalize B_sup_4; apply le_INR.
do 2 rewrite plus_IZR; do 2 rewrite <- Z_R_minus; simpl; ring.
apply
 Rle_lt_trans with (/ INR B * IZR (xc (n + 1)%Z + yc (n + 1)%Z) + 1 * / 2).
RingReplace (xc (n + 1) + 1 + (yc (n + 1) + 1))%Z
 (xc (n + 1) + yc (n + 1) + (1 + 1))%Z.
rewrite plus_IZR; rewrite Rmult_plus_distr_r; rewrite Rmult_comm.
rewrite Rplus_comm; apply Rge_le; rewrite Rplus_comm; apply Rle_ge;
 apply Rplus_le_compat_r.
RingReplace (IZR (1 + 1)) 2.
apply Rle_mult_inv.
lra.
rewrite Rmult_comm; rewrite <- Rmult_assoc.
apply Rmult_le_reg_l with (INR B).
apply INR_B_non_nul.
rewrite <- Rmult_assoc; rewrite RIneq.Rmult_1_r. 
rewrite Rmult_comm; rewrite <- Rmult_assoc.
replace (/ INR B * INR B) with 1.
rewrite Rmult_comm; rewrite RIneq.Rmult_1_r.
replace (2*2) with (INR 4) by (simpl; ring).
generalize B_sup_4; apply le_INR.
apply Rinv_l_sym.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
rewrite Rmult_comm; apply Rlt_add_compatibility3.
rewrite Rsub_sym; rewrite Rplus_comm; rewrite Rplus_assoc.
replace (1 + - (1 * / 2)) with (1 * / 2).
apply Rlt_add_compatibility2; auto.
field; apply Rgt_not_eq; apply Rlt_gt; lra.
Qed.
