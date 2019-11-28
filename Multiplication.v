(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Export definition. 
Require Import Addition.
Require Import Psatz.
Require Export Lemmes_generaux.
Require Import Axiomes.
Require Import Tactiques.
Require Import Lemmes.
Require Import Absolue.
Require Import Zabs_complements.
Require Import Rind_complements.
Require Import Zind_complements.
Require Import Rabsolu_complements.
Require Import Rbase_doubles_inegalites.
Require Import Rbase_operations.
Require Import Rbase_inegalites.
Require Import powerRZ_complements.
Require Import sg.

Lemma multiplication_correct :
 forall (X Y : R) (XC YC : Reelc),
 encadrement XC X ->
 encadrement YC Y -> encadrement (multiplication_reelc XC YC) (X * Y).   

Proof.
unfold encadrement in |- *.
intros.
unfold multiplication_reelc in |- *.
pattern X, Y in |- *.
apply Rind_eq_or.
intro.
elim H1.
intro.
rewrite H2.
do 2 rewrite Rmult_0_l.
replace (XC (p_max YC n)) with 0%Z;
 [ simpl in |- * | symmetry  in |- *; apply xc_nul with X; auto ].
split; lra.
intro.
rewrite H2.
rewrite Rmult_0_r; rewrite Rmult_0_l.
replace (YC (p_max XC n)) with 0%Z;
 [ idtac | symmetry  in |- *; apply xc_nul with Y; auto ].
rewrite <- Zmult_0_r_reverse.
rewrite Zmult_comm.
rewrite <- Zmult_0_r_reverse.
simpl in |- *.
split; lra.
intro H00.
elim H00; clear H00.
intros H01 H02.
pattern (YC (p_max XC n)), (XC (p_max YC n)) in |- *.
apply Zabs_ind_bis.
intros; elim H1; intros; clear H1.
rewrite H2; rewrite H3; simpl in |- *.
RingReplace (0 - 1) (-1); RingReplace (0 + 1) 1.
apply Rbase_doubles_inegalites.Rabsolu_def3.
apply Rmult_lt_reg_l with (B_powerRZ (p_max YC n + p_max XC n - n)).
unfold B_powerRZ in |- *.
apply powerRZ_lt.
apply INR_B_non_nul.
apply Rlt_trans with 1.
rewrite Rabs_mult; replace (Rabs (B_powerRZ n)) with (B_powerRZ n).
rewrite Rmult_comm; rewrite Rmult_assoc; unfold B_powerRZ in |- *.
replace (powerRZ (INR B) n * powerRZ (INR B) (p_max YC n + p_max XC n - n))
 with (powerRZ (INR B) (p_max YC n + p_max XC n)).
replace (powerRZ (INR B) (p_max YC n + p_max XC n)) with
 (powerRZ (INR B) (p_max YC n) * powerRZ (INR B) (p_max XC n)).
rewrite Rabs_mult.
cut (encadrement (absolue_reelc XC) (Rabs X)).
cut (encadrement (absolue_reelc YC) (Rabs Y)).
intros.
generalize (H4 (p_max YC n)); unfold absolue_reelc in |- *; rewrite H3;
 simpl in |- *.
RingReplace (0 - 1) (-1); RingReplace (0 + 1) 1; intros.
decompose [and] H5; clear H5.
generalize (H1 (p_max XC n)); unfold absolue_reelc in |- *; rewrite H2;
 simpl in |- *.
RingReplace (0 - 1) (-1); RingReplace (0 + 1) 1; intros.
decompose [and] H5; clear H5.
RingReplace 1 (1 * 1); rewrite Rmult_mult_mult.
apply Rmult_le.
apply Rle_ge; apply Rmult_le_pos.
apply powerRZ_le.
apply INR_B_non_nul.
apply Rabs_pos.
lra.
rewrite Rmult_comm; auto.
rewrite Rmult_comm; auto.
apply absolue_correct; auto.
apply absolue_correct; auto.
symmetry  in |- *; apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
pattern (p_max YC n + p_max XC n)%Z at 1 in |- *. 
replace (p_max YC n + p_max XC n)%Z with (p_max YC n + p_max XC n - n + n)%Z. 
rewrite Rmult_comm; apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
ring.
symmetry  in |- *; apply Rabs_right; apply Rgt_ge; unfold B_powerRZ in |- *;
 apply Rlt_gt; apply powerRZ_lt; apply INR_B_non_nul.
unfold B_powerRZ in |- *;
 RingReplace (powerRZ (INR B) (p_max YC n + p_max XC n - n) * 1)
  (powerRZ (INR B) (p_max YC n + p_max XC n - n)).
apply powerRZ_lt_1.
apply INR_lt_1.
generalize B_sup_4.
omega.
apply Z.lt_le_trans with 1%Z.
omega.
apply le_pmax_n.

(*2eme partie*)

intro.
generalize H H0 H01 H02; clear H H0 H01 H02.
pattern X, Y, XC, YC in |- *.
apply
 Zabs_ind_ter
  with (P1 := fun zc wc : Reelc => (0 < Z.abs (zc (p_max wc n)))%Z).
3: tauto.
intros.
generalize (H H2 H0).
intro; clear H H2 H0 H1.
RingReplace (Z.sgn (XC (p_max YC n)) * Z.sgn (YC (p_max XC n)))%Z
 (Z.sgn (YC (p_max XC n)) * Z.sgn (XC (p_max YC n)))%Z.
RingReplace (X * Y) (Y * X).
replace (Z.abs (XC (p_max YC n) * YC (p_max XC n)))
 with (Z.abs (YC (p_max XC n) * XC (p_max YC n))).
RingReplace (p_max YC n + p_max XC n)%Z (p_max XC n + p_max YC n)%Z.
auto.
rewrite Zmult_comm; auto.

(*3eme partie*)

intros.
cut
 (IZR (Z.abs (xc (p_max yc n)) + Z.abs (yc (p_max xc n))) *
  / B_powerRZ (p_max yc n + p_max xc n - n) <= 1 * / 2).  
intro a.
clear X Y XC YC H1.
pattern (yc (p_max xc n)) in |- *.
apply Zabs_ind_4.
intro.
rewrite H1; rewrite <- Zmult_0_r_reverse; rewrite Zmult_comm;
 rewrite <- Zmult_0_r_reverse; simpl in |- *.
RingReplace (0 - 1) (-1); RingReplace (0 + 1) 1. 
apply Rbase_doubles_inegalites.Rabsolu_def3.
do 2 rewrite Rabs_mult.
(**)
apply
 Rlt_trans
  with
    ((1 + IZR (Z.abs (xc (p_max yc n) * yc (p_max xc n)))) *
     / B_powerRZ (p_max yc n + p_max xc n - n) + 1 * / 2). 
apply
 Rlt_le_trans
  with
    ((1 + IZR (Z.abs (xc (p_max yc n) * yc (p_max xc n))) +
      IZR (Z.abs (xc (p_max yc n)) + Z.abs (yc (p_max xc n)))) *
     / B_powerRZ (p_max yc n + p_max xc n - n)).
apply Rlt_Rinv_l_to_r.
unfold B_powerRZ in |- *.
apply powerRZ_lt.
apply INR_B_non_nul.
replace (Rabs (B_powerRZ n)) with (B_powerRZ n); unfold B_powerRZ in |- *.
rewrite Rmult_assoc.
replace (powerRZ (INR B) n * powerRZ (INR B) (p_max yc n + p_max xc n - n))
 with (powerRZ (INR B) (p_max yc n + p_max xc n)). 
replace (powerRZ (INR B) (p_max yc n + p_max xc n)) with
 (powerRZ (INR B) (p_max yc n) * powerRZ (INR B) (p_max xc n)). 
rewrite Rmult_mult_mult.
replace
 (1 + IZR (Z.abs (xc (p_max yc n) * yc (p_max xc n))) +
  IZR (Z.abs (xc (p_max yc n)) + Z.abs (yc (p_max xc n))))
 with
  ((IZR (Z.abs (xc (p_max yc n))) + 1) * (IZR (Z.abs (yc (p_max xc n))) + 1)). 
apply Rmult_le.
apply Rle_ge.
apply Rmult_le_pos.
apply Rlt_le; apply powerRZ_lt; apply INR_B_non_nul.
apply Rabs_pos.
apply Rlt_gt; apply Rle_lt_0_plus_1.
RingReplace 0 (IZR 0); apply IZR_le; apply Zabs_pos.
cut (encadrement (absolue_reelc xc) (Rabs x)).
unfold encadrement in |- *; intro.
generalize (H3 (p_max yc n)); clear H3.
unfold absolue_reelc in |- *.
intro.
elim H3; intros; clear H3.
rewrite Rmult_comm; auto.
apply absolue_correct; auto.
cut (encadrement (absolue_reelc yc) (Rabs y)).
unfold encadrement in |- *; intro.
generalize (H3 (p_max xc n)); clear H3.
unfold absolue_reelc in |- *.
intro.
elim H3; intros; clear H3.
rewrite Rmult_comm; auto.
apply absolue_correct; auto.
rewrite Zabs_mult; rewrite plus_IZR; rewrite mult_IZR; ring.
replace (powerRZ (INR B) (p_max yc n) * powerRZ (INR B) (p_max xc n)) with
 (powerRZ (INR B) (p_max yc n + p_max xc n)); auto.
apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
replace (powerRZ (INR B) n * powerRZ (INR B) (p_max yc n + p_max xc n - n))
 with (powerRZ (INR B) (n + (p_max yc n + p_max xc n - n))). 
apply powerRZ_trivial.
ring.
apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
symmetry  in |- *; apply Rabs_right.
apply Rle_ge.
apply Rlt_le; apply powerRZ_lt; apply INR_B_non_nul.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat_l.
auto.
rewrite H1.
rewrite <- Zmult_0_r_reverse; simpl in |- *.
RingReplace (1 + 0) 1.
apply Rlt_add_compatibility3.
replace (1 - 1 * / 2) with (1 * / 2).
rewrite Rmult_comm; rewrite RIneq.Rmult_1_r. 
rewrite Rmult_comm; rewrite RIneq.Rmult_1_r. 
apply Rinv_1_lt_contravar.
lra.
apply Rlt_le_trans with (INR B).
replace 2 with (INR 2).
apply lt_INR.
generalize B_sup_4; omega.
do 2 rewrite S_INR; simpl in |- *; ring.
unfold B_powerRZ in |- *; apply powerRZ_lt_r_bis.
replace 1 with (INR 1).
apply le_INR.
generalize B_sup_4; omega.
rewrite S_INR; simpl in |- *; ring.
apply le_pmax_n.
field; apply Rgt_not_eq; lra.
intro.
replace (Z.sgn (xc (p_max yc n))) with (sg x).
2: symmetry  in |- *; apply Zsgn_sg; auto; auto.
replace (Z.sgn (yc (p_max xc n))) with (sg y).
2: symmetry  in |- *; apply Zsgn_sg; auto; auto.
pattern (x * y) in |- *.
rewrite sg.Rabsolu_sg_bis.
rewrite Rabs_mult.
rewrite sg_mult; rewrite mult_IZR.
pattern x, y in |- *.
apply sg_ind_bis.
apply sg_Zsgn_abs with xc (p_max yc n).
apply absolue_correct.
auto.
auto.
apply sg_Zsgn_abs with yc (p_max xc n).
apply absolue_correct.
auto.
auto.
intro.
rewrite H3; RingReplace (IZR (-1)) (-1).
apply Rlt_2_monotony_contra with (-1).
lra.
rewrite Rmult_comm; rewrite Rmult_plus_distr_r.
rewrite Rmult_comm; rewrite <- Rmult_assoc. 
RingReplace (-1 * -1) 1; RingReplace (1 * -1) (-1).
rewrite Rmult_comm; rewrite RIneq.Rmult_1_r.
replace (-1)%R with (-(1))%R at 1 by auto.
rewrite Rplus_comm; rewrite <- Rsub_sym.
do 2 rewrite <- Rmult_assoc.
RingReplace (-1 * -1) 1.
rewrite Rmult_assoc; rewrite Rmult_comm; rewrite RIneq.Rmult_1_r.
rewrite Rmult_minus_distr_l; rewrite <- Rmult_assoc; RingReplace (-1 * -1) 1.
RingReplace
 (1 *
  IZR
    (gauss_z_sur_B_pow (1 + Z.abs (xc (p_max yc n) * yc (p_max xc n)))
       (p_max yc n + p_max xc n - n)) - -1 * 1)
 (IZR
    (gauss_z_sur_B_pow (1 + Z.abs (xc (p_max yc n) * yc (p_max xc n)))
       (p_max yc n + p_max xc n - n)) + 1).
apply
 Rlt_2_le_lt_and
  with
    (IZR (1 + Z.abs (xc (p_max yc n) * yc (p_max xc n))) *
     / B_powerRZ (p_max yc n + p_max xc n - n) - 1 * / 2)
    (IZR (1 + Z.abs (xc (p_max yc n) * yc (p_max xc n))) *
     / B_powerRZ (p_max yc n + p_max xc n - n) + 1 * / 2).
2: apply Rlt_le_2_gauss.
2: generalize
    (gauss_correct_pow (1 + Z.abs (xc (p_max yc n) * yc (p_max xc n)))
       (p_max yc n + p_max xc n - n)).
2: tauto.
apply
 Rle_2_Rlt_2
  with
    ((1 + IZR (Z.abs (xc (p_max yc n) * yc (p_max xc n))) -
      IZR (Z.abs (xc (p_max yc n)) + Z.abs (yc (p_max xc n)))) *
     / B_powerRZ (p_max yc n + p_max xc n - n))
    ((1 + IZR (Z.abs (xc (p_max yc n) * yc (p_max xc n))) +
      IZR (Z.abs (xc (p_max yc n)) + Z.abs (yc (p_max xc n)))) *
     / B_powerRZ (p_max yc n + p_max xc n - n)).
apply Rlt_2_Rmult_Rinv.
unfold B_powerRZ in |- *.
apply powerRZ_lt.
apply INR_B_non_nul.
unfold B_powerRZ in |- *.
rewrite Rmult_assoc.
replace (powerRZ (INR B) n * powerRZ (INR B) (p_max yc n + p_max xc n - n))
 with (powerRZ (INR B) (p_max yc n + p_max xc n)). 
replace (powerRZ (INR B) (p_max yc n + p_max xc n)) with
 (powerRZ (INR B) (p_max yc n) * powerRZ (INR B) (p_max xc n)). 
rewrite Rmult_mult_mult.
replace
 (1 + IZR (Z.abs (xc (p_max yc n) * yc (p_max xc n))) +
  IZR (Z.abs (xc (p_max yc n)) + Z.abs (yc (p_max xc n))))
 with
  ((IZR (Z.abs (xc (p_max yc n))) + 1) * (IZR (Z.abs (yc (p_max xc n))) + 1)). 
replace
 (1 + IZR (Z.abs (xc (p_max yc n) * yc (p_max xc n))) -
  IZR (Z.abs (xc (p_max yc n)) + Z.abs (yc (p_max xc n))))
 with
  ((IZR (Z.abs (xc (p_max yc n))) - 1) * (IZR (Z.abs (yc (p_max xc n))) - 1)). 
apply Rle_mult_lt.
cut (encadrement (absolue_reelc xc) (Rabs x)).
unfold encadrement in |- *; intro.
generalize (H4 (p_max yc n)); clear H4.
unfold absolue_reelc in |- *.
intro.
rewrite Rmult_comm; auto.
apply absolue_correct; auto.
cut (encadrement (absolue_reelc yc) (Rabs y)).
unfold encadrement in |- *; intro.
generalize (H4 (p_max xc n)); clear H4.
unfold absolue_reelc in |- *.
rewrite Rmult_comm; auto.
apply absolue_correct; auto.
apply Rmult_lt_0_compat.
apply powerRZ_lt; apply INR_B_non_nul.
apply sg_Zsgn_abs with xc (p_max yc n).
apply absolue_correct; auto.
auto.
apply Rle_add_compatibility.
RingReplace (0 + 1) 1; RingReplace 1 (IZR (Z.succ 0)).
apply IZR_le.
apply Zlt_le_succ; auto.
apply Rmult_le_pos.
apply Rlt_le; apply powerRZ_lt; apply INR_B_non_nul.
apply Rabs_pos.
apply Rle_lt_0_plus_1.
RingReplace 0 (IZR 0).
apply Rlt_le; apply IZR_lt.
auto.
rewrite Zabs_mult; rewrite mult_IZR; rewrite plus_IZR; ring.
rewrite Zabs_mult; rewrite mult_IZR; rewrite plus_IZR; ring.
replace (powerRZ (INR B) (p_max yc n) * powerRZ (INR B) (p_max xc n)) with
 (powerRZ (INR B) (p_max yc n + p_max xc n)); auto.
apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
replace (powerRZ (INR B) n * powerRZ (INR B) (p_max yc n + p_max xc n - n))
 with (powerRZ (INR B) (n + (p_max yc n + p_max xc n - n))). 
apply powerRZ_trivial.
ring.
apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
apply Rge_le; rewrite Rmult_comm; rewrite Rmult_minus_distr_l.
rewrite Rmult_comm; apply Rle_ge.
rewrite plus_IZR; RingReplace (IZR 1) 1.
apply Rle_sub_r.
rewrite Rmult_comm; auto.
rewrite Rmult_plus_distr_r.
do 2 rewrite plus_IZR; RingReplace (IZR 1) 1.
apply Rplus_le_compat_l.
rewrite <- plus_IZR; auto.
intro.
rewrite H3.
RingReplace (IZR 1) 1.
rewrite Rmult_assoc; rewrite Rmult_1l.
apply
 Rlt_2_le_lt_and
  with
    (IZR (1 + Z.abs (xc (p_max yc n) * yc (p_max xc n))) *
     / B_powerRZ (p_max yc n + p_max xc n - n) - 1 * / 2)
    (IZR (1 + Z.abs (xc (p_max yc n) * yc (p_max xc n))) *
     / B_powerRZ (p_max yc n + p_max xc n - n) + 1 * / 2).
2: apply Rlt_le_2_gauss.
2: generalize
    (gauss_correct_pow (1 + Z.abs (xc (p_max yc n) * yc (p_max xc n)))
       (p_max yc n + p_max xc n - n)).
2: tauto.
apply
 Rle_2_Rlt_2
  with
    ((1 + IZR (Z.abs (xc (p_max yc n) * yc (p_max xc n))) -
      IZR (Z.abs (xc (p_max yc n)) + Z.abs (yc (p_max xc n)))) *
     / B_powerRZ (p_max yc n + p_max xc n - n))
    ((1 + IZR (Z.abs (xc (p_max yc n) * yc (p_max xc n))) +
      IZR (Z.abs (xc (p_max yc n)) + Z.abs (yc (p_max xc n)))) *
     / B_powerRZ (p_max yc n + p_max xc n - n)).
apply Rlt_2_Rmult_Rinv.
unfold B_powerRZ in |- *.
apply powerRZ_lt.
apply INR_B_non_nul.
rewrite <- Rmult_assoc.
unfold B_powerRZ in |- *.
rewrite Rmult_assoc.
rewrite Rmult_1l.
replace (powerRZ (INR B) n * powerRZ (INR B) (p_max yc n + p_max xc n - n))
 with (powerRZ (INR B) (p_max yc n + p_max xc n)). 
replace (powerRZ (INR B) (p_max yc n + p_max xc n)) with
 (powerRZ (INR B) (p_max yc n) * powerRZ (INR B) (p_max xc n)). 
rewrite Rmult_mult_mult.
replace
 (1 + IZR (Z.abs (xc (p_max yc n) * yc (p_max xc n))) +
  IZR (Z.abs (xc (p_max yc n)) + Z.abs (yc (p_max xc n))))
 with
  ((IZR (Z.abs (xc (p_max yc n))) + 1) * (IZR (Z.abs (yc (p_max xc n))) + 1)). 
replace
 (1 + IZR (Z.abs (xc (p_max yc n) * yc (p_max xc n))) -
  IZR (Z.abs (xc (p_max yc n)) + Z.abs (yc (p_max xc n))))
 with
  ((IZR (Z.abs (xc (p_max yc n))) - 1) * (IZR (Z.abs (yc (p_max xc n))) - 1)). 

apply Rle_mult_lt.
cut (encadrement (absolue_reelc xc) (Rabs x)).
unfold encadrement in |- *; intro.
generalize (H4 (p_max yc n)); clear H4.
unfold absolue_reelc in |- *.
intro.
rewrite Rmult_comm; auto.
apply absolue_correct; auto.
cut (encadrement (absolue_reelc yc) (Rabs y)).
unfold encadrement in |- *; intro.
generalize (H4 (p_max xc n)); clear H4.
unfold absolue_reelc in |- *.
rewrite Rmult_comm; auto.
apply absolue_correct; auto.
apply Rmult_lt_0_compat.
apply powerRZ_lt; apply INR_B_non_nul.
apply sg_Zsgn_abs with xc (p_max yc n).
apply absolue_correct; auto.
auto.
apply Rle_add_compatibility.
RingReplace (0 + 1) 1; RingReplace 1 (IZR (Z.succ 0)).
apply IZR_le.
apply Zlt_le_succ; auto.
apply Rmult_le_pos.
apply Rlt_le; apply powerRZ_lt; apply INR_B_non_nul.
apply Rabs_pos.
apply Rle_lt_0_plus_1.
RingReplace 0 (IZR 0).
apply Rlt_le; apply IZR_lt.
auto.
rewrite Zabs_mult; rewrite mult_IZR; rewrite plus_IZR; ring.
rewrite Zabs_mult; rewrite mult_IZR; rewrite plus_IZR; ring.
replace (powerRZ (INR B) (p_max yc n) * powerRZ (INR B) (p_max xc n)) with
 (powerRZ (INR B) (p_max yc n + p_max xc n)); auto.
apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
replace (powerRZ (INR B) n * powerRZ (INR B) (p_max yc n + p_max xc n - n))
 with (powerRZ (INR B) (n + (p_max yc n + p_max xc n - n))). 
apply powerRZ_trivial.
ring.
apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
apply Rge_le; rewrite Rmult_comm; rewrite Rmult_minus_distr_l.
rewrite Rmult_comm; apply Rle_ge.
rewrite plus_IZR; RingReplace (IZR 1) 1.
apply Rle_sub_r.
rewrite Rmult_comm; auto.
rewrite Rmult_plus_distr_r.
do 2 rewrite plus_IZR; RingReplace (IZR 1) 1.
apply Rplus_le_compat_l.
rewrite <- plus_IZR; auto.

(* 4eme partie *)

clear X Y XC YC H1.
pattern (xc (p_max yc n)) in |- *.
apply Zabs_ind_lt_O.
3: auto.
intros.
pattern (yc (p_max xc n)) in |- *.
apply Zabs_ind_le_1.
intro.
replace (1 * / 2) with (2 * / 4).
apply Rmult_le_compat.
RingReplace 0 (IZR 0); apply IZR_le.
rewrite H1.
apply Zplus_le_0_compat.
RingReplace 1%Z (Z.succ 0); apply Zle_succ.
apply Zabs_pos.
apply Rlt_le; apply Rinv_0_lt_compat; unfold B_powerRZ in |- *;
 apply powerRZ_lt; apply INR_B_non_nul.
rewrite plus_IZR; rewrite H1.
RingReplace (IZR 1) 1.
apply Rplus_le_reg_l with (-1).
rewrite <- Rplus_assoc; RingReplace (-1 + 1) 0; rewrite Rplus_comm;
 rewrite Rplus_0_r; replace (-1 + 2) with (IZR (Z.succ 0)) by (simpl;ring).
apply IZR_le; auto.
apply Rinv_le.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
lra.
apply Rle_trans with (INR B).
replace 4 with (INR 4).
apply le_INR.
generalize B_sup_4; omega.
do 4 rewrite S_INR; simpl in |- *; ring.
unfold B_powerRZ in |- *; apply powerRZ_lt_r_bis.
replace 1 with (INR 1).
apply le_INR.
generalize B_sup_4; omega.
rewrite S_INR; simpl in |- *; ring.
apply le_pmax_n.
field; apply Rgt_not_eq; lra.
intro.
clear H1.
pattern (p_max yc n) in |- *.
apply ind_gt_le with (msd xc).
intro.
apply Rle_trans with (4 * / B_powerRZ (Z.succ (Z.succ 0))).
replace (4 * / B_powerRZ (Z.succ (Z.succ 0))) with
 (4 * INR B * / B_powerRZ (Z.succ (Z.succ (Z.succ 0)))).
apply
 Rle_trans
  with
    (2 * INR B *
     (B_powerRZ n * / B_powerRZ (p_max xc n + msd xc) +
      B_powerRZ n * / B_powerRZ (p_max yc n + msd yc))).
replace
 (2 * INR B *
  (B_powerRZ n * / B_powerRZ (p_max xc n + msd xc) +
   B_powerRZ n * / B_powerRZ (p_max yc n + msd yc))) with
 (2 * INR B *
  (B_powerRZ (p_max yc n - msd xc) + B_powerRZ (p_max xc n - msd yc)) *
  / B_powerRZ (p_max yc n + p_max xc n - n)). 
apply Rmult_le_compat_r.
apply Rlt_le; apply Rinv_0_lt_compat; unfold B_powerRZ in |- *;
 apply powerRZ_lt; apply INR_B_non_nul.
rewrite plus_IZR.
rewrite Rmult_comm; rewrite Rmult_plus_distr_r.
apply Rplus_le_compat.
rewrite Rmult_comm; apply msd_ax2 with x; auto.
rewrite Rmult_comm; apply msd_ax2 with y; auto.
apply msd_ax1; auto.
rewrite Rmult_assoc; apply Rmult_eq_compat_l.
rewrite Rmult_plus_distr_r.
apply Rplus_plus_plus.
apply Rinv_Rmult_bis.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
replace (B_powerRZ (p_max yc n - msd xc) * B_powerRZ (p_max xc n + msd xc))
 with (B_powerRZ (p_max yc n - msd xc + (p_max xc n + msd xc))).
replace (B_powerRZ (p_max yc n + p_max xc n - n) * B_powerRZ n) with
 (B_powerRZ (p_max yc n + p_max xc n - n + n)).
unfold B_powerRZ in |- *; apply powerRZ_trivial.
ring.
unfold B_powerRZ in |- *; apply powerRZ_add. 
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
apply Rinv_Rmult_bis.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
replace (B_powerRZ (p_max xc n - msd yc) * B_powerRZ (p_max yc n + msd yc))
 with (B_powerRZ (p_max xc n - msd yc + (p_max yc n + msd yc))).
replace (B_powerRZ (p_max yc n + p_max xc n - n) * B_powerRZ n) with
 (B_powerRZ (p_max yc n + p_max xc n - n + n)).
unfold B_powerRZ in |- *; apply powerRZ_trivial.
ring.
unfold B_powerRZ in |- *; apply powerRZ_add. 
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
RingReplace (4 * INR B) (2 * INR B * 2).
do 2 rewrite Rmult_assoc; rewrite <- Rmult_assoc.
apply Rmult_le_compat_l.
apply Rmult_le_pos.
lra.
apply Rlt_le; apply INR_B_non_nul.
replace (/ B_powerRZ (p_max xc n + msd xc)) with
 (B_powerRZ (- (p_max xc n + msd xc))).
replace (/ B_powerRZ (p_max yc n + msd yc)) with
 (B_powerRZ (- (p_max yc n + msd yc))).
replace (/ B_powerRZ (Z.succ (Z.succ (Z.succ 0)))) with
 (B_powerRZ (- Z.succ (Z.succ (Z.succ 0)))).
replace (B_powerRZ n * B_powerRZ (- (p_max xc n + msd xc))) with
 (B_powerRZ (n + - (p_max xc n + msd xc))).
replace (B_powerRZ n * B_powerRZ (- (p_max yc n + msd yc))) with
 (B_powerRZ (n + - (p_max yc n + msd yc))).
RingReplace (2 * B_powerRZ (- Z.succ (Z.succ (Z.succ 0))))
 (B_powerRZ (- Z.succ (Z.succ (Z.succ 0))) +
  B_powerRZ (- Z.succ (Z.succ (Z.succ 0)))).
apply Rplus_le_compat.
unfold B_powerRZ in |- *; apply Rle_powerRZ.
apply Rlt_le; apply Rlt_le_trans with (INR 4).
do 4 rewrite S_INR. 
simpl in |- *; lra.
apply le_INR; generalize B_sup_4; omega.
rewrite Zplus_comm.
apply Zplus_le_reg_r with (Z.succ (Z.succ (Z.succ 0))).
simpl in |- *.
rewrite Zopp_plus_distr.
apply Zplus_le_reg_l with (p_max xc n).
RingReplace (p_max xc n + (- p_max xc n + - msd xc + n + 3))%Z
 (n - msd xc + 3)%Z.
rewrite <- Zplus_0_r_reverse.
unfold p_max in |- *.
apply Zle_max_l. 
unfold B_powerRZ in |- *; apply Rle_powerRZ.
apply Rlt_le; apply Rlt_le_trans with (INR 4).
do 4 rewrite S_INR. 
simpl in |- *; lra.
apply le_INR; generalize B_sup_4; omega.
rewrite Zplus_comm.
apply Zplus_le_reg_r with (Z.succ (Z.succ (Z.succ 0))).
simpl in |- *.
rewrite Zopp_plus_distr.
apply Zplus_le_reg_l with (p_max yc n).
RingReplace (p_max yc n + (- p_max yc n + - msd yc + n + 3))%Z
 (n - msd yc + 3)%Z.
rewrite <- Zplus_0_r_reverse.
unfold p_max in |- *.
apply Zle_max_l. 
unfold B_powerRZ in |- *; apply powerRZ_add; apply Rgt_not_eq; apply Rlt_gt;
 apply INR_B_non_nul.
unfold B_powerRZ in |- *; apply powerRZ_add; apply Rgt_not_eq; apply Rlt_gt;
 apply INR_B_non_nul.
unfold B_powerRZ in |- *; symmetry  in |- *; apply Rinv_powerRZ.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; symmetry  in |- *; apply Rinv_powerRZ.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; symmetry  in |- *; apply Rinv_powerRZ.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
rewrite Rmult_assoc; apply Rmult_eq_compat_l.
unfold B_powerRZ in |- *.
replace (powerRZ (INR B) (Z.succ (Z.succ (Z.succ 0)))) with
 (powerRZ (INR B) (Z.succ (Z.succ 0)) * INR B).
replace (/ (powerRZ (INR B) (Z.succ (Z.succ 0)) * INR B)) with
 (/ powerRZ (INR B) (Z.succ (Z.succ 0)) * / INR B).
rewrite Rmult_comm; rewrite Rmult_assoc.
replace (/ INR B * INR B) with 1.
rewrite RIneq.Rmult_1_r; auto.
apply Rinv_l_sym.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
symmetry  in |- *; apply Rinv_mult_distr.
apply Rgt_not_eq; apply Rlt_gt; apply powerRZ_lt; apply INR_B_non_nul.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
symmetry  in |- *; apply powerRZ_Zs.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
rewrite Rmult_comm; apply Rle_Rinv_monotony.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
rewrite Rmult_1l.
apply Rle_mult_inv.
lra.
unfold B_powerRZ in |- *.
replace (powerRZ (INR B) (Z.succ (Z.succ 0))) with (INR B * INR B).
apply Rmult_le_compat.
lra.
lra.
replace 4 with (INR 4).
apply le_INR; generalize B_sup_4; omega.
do 4 rewrite S_INR; simpl in |- *; ring. 
apply Rle_trans with 4.
lra.
replace 4 with (INR 4).
apply le_INR; generalize B_sup_4; omega.
do 4 rewrite S_INR; simpl in |- *; ring.
RingReplace (Z.succ (Z.succ 0)) (Z.succ 0 + Z.succ 0)%Z.
replace (powerRZ (INR B) (Z.succ 0 + Z.succ 0)) with
 (powerRZ (INR B) (Z.succ 0) * powerRZ (INR B) (Z.succ 0)).
rewrite powerRZ_1; auto.
symmetry  in |- *; apply powerRZ_add. 
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.

intro.
apply Rle_trans with (3 * / 8).
2: lra.
apply
 Rle_trans
  with (1 * / INR B + 2 * INR B * / B_powerRZ (Z.succ (Z.succ (Z.succ 0)))). 
apply
 Rle_trans
  with
    (/ B_powerRZ (p_max yc n + p_max xc n - n) +
     2 * INR B * B_powerRZ n * / B_powerRZ (p_max yc n + msd yc)).
rewrite plus_IZR.
replace
 (/ B_powerRZ (p_max yc n + p_max xc n - n) +
  2 * INR B * B_powerRZ n * / B_powerRZ (p_max yc n + msd yc)) with
 ((1 + 2 * INR B * B_powerRZ (p_max xc n - msd yc)) *
  / B_powerRZ (p_max yc n + p_max xc n - n)).
apply Rmult_le_compat_r.
apply Rlt_le; apply Rinv_0_lt_compat; unfold B_powerRZ in |- *;
 apply powerRZ_lt; apply INR_B_non_nul.
apply Rplus_le_compat.
RingReplace 1 (IZR (Z.succ 0)).
apply IZR_le.
apply msd_ax3.
auto.
apply msd_ax2 with y; auto.
apply msd_ax1; auto.
rewrite Rmult_plus_distr_r; rewrite Rmult_1l; apply Rplus_eq_compat_l. 
rewrite Rmult_assoc; symmetry  in |- *; rewrite Rmult_assoc;
 apply Rmult_eq_compat_l.
apply Rinv_Rmult_bis.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
replace (B_powerRZ n * B_powerRZ (p_max yc n + p_max xc n - n)) with
 (B_powerRZ (n + (p_max yc n + p_max xc n - n))).
replace (B_powerRZ (p_max yc n + msd yc) * B_powerRZ (p_max xc n - msd yc))
 with (B_powerRZ (p_max yc n + msd yc + (p_max xc n - msd yc))).
unfold B_powerRZ in |- *; apply powerRZ_trivial; ring.
unfold B_powerRZ in |- *; apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
apply Rplus_le_compat.
rewrite Rmult_1l; apply Rinv_le.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
apply INR_B_non_nul.
unfold B_powerRZ in |- *.
pattern (INR B) at 1 in |- *.
replace (INR B) with (powerRZ (INR B) (Z.succ 0)).
apply Rle_powerRZ.
apply Rlt_le; apply Rlt_le_trans with 4.
lra.
replace 4 with (INR 4).
apply le_INR; generalize B_sup_4; omega.
do 4 rewrite S_INR; simpl in |- *; ring. 
apply le_pmax_n.
apply powerRZ_1.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rmult_le_pos.
lra.
apply Rlt_le; apply INR_B_non_nul.
rewrite Rmult_comm; apply Rle_Rinv_monotony.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
apply Rle_mult_inv.
apply Rlt_gt; unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
replace (B_powerRZ n * B_powerRZ (Z.succ (Z.succ (Z.succ 0)))) with
 (B_powerRZ (n + Z.succ (Z.succ (Z.succ 0)))).
unfold B_powerRZ in |- *; apply Rle_powerRZ.
apply Rlt_le; apply Rlt_le_trans with 4.
lra.
replace 4 with (INR 4).
apply le_INR; generalize B_sup_4; omega.
do 4 rewrite S_INR; simpl in |- *; ring. 
apply Zplus_le_reg_r with (- msd yc)%Z.
simpl in |- *.
RingReplace (n + 3 + - msd yc)%Z (n - msd yc + 3)%Z.
RingReplace (p_max yc n + msd yc + - msd yc)%Z (p_max yc n).
unfold p_max in |- *.
apply Zle_max_l. 
unfold B_powerRZ in |- *; apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
unfold B_powerRZ in |- *.
apply Rle_trans with (1 * / 4 + 2 * / powerRZ 4 (Z.succ (Z.succ 0))).
apply Rplus_le_compat.
do 2 rewrite Rmult_1l; apply Rinv_le.
apply INR_B_non_nul.
lra.
replace 4 with (INR 4).
apply le_INR; generalize B_sup_4; omega.
do 4 rewrite S_INR; simpl in |- *; ring. 
rewrite Rmult_assoc; apply Rmult_le_compat_l.
lra.
replace (/ powerRZ (INR B) (Z.succ (Z.succ (Z.succ 0)))) with
 (powerRZ (INR B) (- Z.succ (Z.succ (Z.succ 0)))).
replace (/ powerRZ 4 (Z.succ (Z.succ 0))) with (powerRZ 4 (- Z.succ (Z.succ 0))).
replace (INR B * powerRZ (INR B) (- Z.succ (Z.succ (Z.succ 0)))) with
 (powerRZ (INR B) (Z.succ 0 + - Z.succ (Z.succ (Z.succ 0)))).
simpl in |- *.
do 2 rewrite RIneq.Rmult_1_r.
apply Rinv_le.
apply Rmult_lt_0_compat.
apply INR_B_non_nul.
apply INR_B_non_nul.
lra.
generalize (Rsqr_incr_1 4 (INR B)).
unfold Rsqr in |- *.
intros.
apply H4.
replace 4 with (INR 4).
apply le_INR; generalize B_sup_4; omega.
do 4 rewrite S_INR; simpl in |- *; ring. 
lra.
apply Rle_trans with 4.
lra.
replace 4 with (INR 4).
apply le_INR; generalize B_sup_4; omega.
do 4 rewrite S_INR; simpl in |- *; ring. 
simpl in |- *.
rewrite RIneq.Rmult_1_r.
symmetry  in |- *; rewrite Rinv_mult_distr.
rewrite <- Rmult_assoc.
symmetry  in |- *; apply Rbase_operations.Rmult_1_r.
apply Rinv_r_sym.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
apply Rgt_not_eq; apply Rlt_gt; apply Rmult_lt_0_compat.
apply INR_B_non_nul.
apply INR_B_non_nul.
simpl in |- *.
field.
auto.
simpl in |- *.
lra.

(*derniere partie*)

intro.
pattern (p_max xc n) in |- *.
apply ind_gt_le with (msd yc).
intro.
apply Rle_trans with (4 * / B_powerRZ (Z.succ (Z.succ 0))).
replace (4 * / B_powerRZ (Z.succ (Z.succ 0))) with
 (4 * INR B * / B_powerRZ (Z.succ (Z.succ (Z.succ 0)))).
apply
 Rle_trans
  with
    (2 * INR B *
     (B_powerRZ n * / B_powerRZ (p_max xc n + msd xc) +
      B_powerRZ n * / B_powerRZ (p_max yc n + msd yc))).
replace
 (2 * INR B *
  (B_powerRZ n * / B_powerRZ (p_max xc n + msd xc) +
   B_powerRZ n * / B_powerRZ (p_max yc n + msd yc))) with
 (2 * INR B *
  (B_powerRZ (p_max yc n - msd xc) + B_powerRZ (p_max xc n - msd yc)) *
  / B_powerRZ (p_max yc n + p_max xc n - n)). 
apply Rmult_le_compat_r.
apply Rlt_le; apply Rinv_0_lt_compat; unfold B_powerRZ in |- *;
 apply powerRZ_lt; apply INR_B_non_nul.
rewrite plus_IZR.
rewrite Rmult_comm; rewrite Rmult_plus_distr_r.
apply Rplus_le_compat.
rewrite Rmult_comm; apply msd_ax2 with x; auto.
apply msd_ax1; auto.
rewrite Rmult_comm; apply msd_ax2 with y; auto.
rewrite Rmult_assoc; apply Rmult_eq_compat_l.
rewrite Rmult_plus_distr_r.
apply Rplus_plus_plus.
apply Rinv_Rmult_bis.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
replace (B_powerRZ (p_max yc n - msd xc) * B_powerRZ (p_max xc n + msd xc))
 with (B_powerRZ (p_max yc n - msd xc + (p_max xc n + msd xc))).
replace (B_powerRZ (p_max yc n + p_max xc n - n) * B_powerRZ n) with
 (B_powerRZ (p_max yc n + p_max xc n - n + n)).
unfold B_powerRZ in |- *; apply powerRZ_trivial.
ring.
unfold B_powerRZ in |- *; apply powerRZ_add. 
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
apply Rinv_Rmult_bis.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
replace (B_powerRZ (p_max xc n - msd yc) * B_powerRZ (p_max yc n + msd yc))
 with (B_powerRZ (p_max xc n - msd yc + (p_max yc n + msd yc))).
replace (B_powerRZ (p_max yc n + p_max xc n - n) * B_powerRZ n) with
 (B_powerRZ (p_max yc n + p_max xc n - n + n)).
unfold B_powerRZ in |- *; apply powerRZ_trivial.
ring.
unfold B_powerRZ in |- *; apply powerRZ_add. 
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
RingReplace (4 * INR B) (2 * INR B * 2).
do 2 rewrite Rmult_assoc; rewrite <- Rmult_assoc.
apply Rmult_le_compat_l.
apply Rmult_le_pos.
lra.
apply Rlt_le; apply INR_B_non_nul.
replace (/ B_powerRZ (p_max xc n + msd xc)) with
 (B_powerRZ (- (p_max xc n + msd xc))).
replace (/ B_powerRZ (p_max yc n + msd yc)) with
 (B_powerRZ (- (p_max yc n + msd yc))).
replace (/ B_powerRZ (Z.succ (Z.succ (Z.succ 0)))) with
 (B_powerRZ (- Z.succ (Z.succ (Z.succ 0)))).
replace (B_powerRZ n * B_powerRZ (- (p_max xc n + msd xc))) with
 (B_powerRZ (n + - (p_max xc n + msd xc))).
replace (B_powerRZ n * B_powerRZ (- (p_max yc n + msd yc))) with
 (B_powerRZ (n + - (p_max yc n + msd yc))).
RingReplace (2 * B_powerRZ (- Z.succ (Z.succ (Z.succ 0))))
 (B_powerRZ (- Z.succ (Z.succ (Z.succ 0))) +
  B_powerRZ (- Z.succ (Z.succ (Z.succ 0)))).
apply Rplus_le_compat.
unfold B_powerRZ in |- *; apply Rle_powerRZ.
apply Rlt_le; apply Rlt_le_trans with (INR 4).
do 4 rewrite S_INR. 
simpl in |- *; lra.
apply le_INR; generalize B_sup_4; omega.
rewrite Zplus_comm.
apply Zplus_le_reg_r with (Z.succ (Z.succ (Z.succ 0))).
simpl in |- *.
rewrite Zopp_plus_distr.
apply Zplus_le_reg_l with (p_max xc n).
RingReplace (p_max xc n + (- p_max xc n + - msd xc + n + 3))%Z
 (n - msd xc + 3)%Z.
rewrite <- Zplus_0_r_reverse.
unfold p_max in |- *.
apply Zle_max_l. 
unfold B_powerRZ in |- *; apply Rle_powerRZ.
apply Rlt_le; apply Rlt_le_trans with (INR 4).
do 4 rewrite S_INR. 
simpl in |- *; lra.
apply le_INR; generalize B_sup_4; omega.
rewrite Zplus_comm.
apply Zplus_le_reg_r with (Z.succ (Z.succ (Z.succ 0))).
simpl in |- *.
rewrite Zopp_plus_distr.
apply Zplus_le_reg_l with (p_max yc n).
RingReplace (p_max yc n + (- p_max yc n + - msd yc + n + 3))%Z
 (n - msd yc + 3)%Z.
rewrite <- Zplus_0_r_reverse.
unfold p_max in |- *.
apply Zle_max_l. 
unfold B_powerRZ in |- *; apply powerRZ_add; apply Rgt_not_eq; apply Rlt_gt;
 apply INR_B_non_nul.
unfold B_powerRZ in |- *; apply powerRZ_add; apply Rgt_not_eq; apply Rlt_gt;
 apply INR_B_non_nul.
unfold B_powerRZ in |- *; symmetry  in |- *; apply Rinv_powerRZ.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; symmetry  in |- *; apply Rinv_powerRZ.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; symmetry  in |- *; apply Rinv_powerRZ.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
rewrite Rmult_assoc; apply Rmult_eq_compat_l.
unfold B_powerRZ in |- *.
replace (powerRZ (INR B) (Z.succ (Z.succ (Z.succ 0)))) with
 (powerRZ (INR B) (Z.succ (Z.succ 0)) * INR B).
replace (/ (powerRZ (INR B) (Z.succ (Z.succ 0)) * INR B)) with
 (/ powerRZ (INR B) (Z.succ (Z.succ 0)) * / INR B).
rewrite Rmult_comm; rewrite Rmult_assoc.
replace (/ INR B * INR B) with 1.
rewrite RIneq.Rmult_1_r; auto.
apply Rinv_l_sym.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
symmetry  in |- *; apply Rinv_mult_distr.
apply Rgt_not_eq; apply Rlt_gt; apply powerRZ_lt; apply INR_B_non_nul.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
symmetry  in |- *; apply powerRZ_Zs.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
rewrite Rmult_comm; apply Rle_Rinv_monotony.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
rewrite Rmult_1l.
apply Rle_mult_inv.
lra.
unfold B_powerRZ in |- *.
replace (powerRZ (INR B) (Z.succ (Z.succ 0))) with (INR B * INR B).
apply Rmult_le_compat.
lra.
lra.
replace 4 with (INR 4).
apply le_INR; generalize B_sup_4; omega.
do 4 rewrite S_INR; simpl in |- *; ring. 
apply Rle_trans with 4.
lra.
replace 4 with (INR 4).
apply le_INR; generalize B_sup_4; omega.
do 4 rewrite S_INR; simpl in |- *; ring.
RingReplace (Z.succ (Z.succ 0)) (Z.succ 0 + Z.succ 0)%Z.
replace (powerRZ (INR B) (Z.succ 0 + Z.succ 0)) with
 (powerRZ (INR B) (Z.succ 0) * powerRZ (INR B) (Z.succ 0)).
rewrite powerRZ_1; auto.
symmetry  in |- *; apply powerRZ_add. 
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.

intro.
apply Rle_trans with (3 * / 8).
2: lra.
apply
 Rle_trans
  with (1 * / INR B + 2 * INR B * / B_powerRZ (Z.succ (Z.succ (Z.succ 0)))). 
apply
 Rle_trans
  with
    (2 * INR B * B_powerRZ n * / B_powerRZ (p_max xc n + msd xc) +
     / B_powerRZ (p_max yc n + p_max xc n - n)).
rewrite plus_IZR.
replace
 (2 * INR B * B_powerRZ n * / B_powerRZ (p_max xc n + msd xc) +
  / B_powerRZ (p_max yc n + p_max xc n - n)) with
 ((2 * INR B * B_powerRZ (p_max yc n - msd xc) + 1) *
  / B_powerRZ (p_max yc n + p_max xc n - n)).
apply Rmult_le_compat_r.
apply Rlt_le; apply Rinv_0_lt_compat; unfold B_powerRZ in |- *;
 apply powerRZ_lt; apply INR_B_non_nul.
apply Rplus_le_compat.
apply msd_ax2 with x; auto.
apply msd_ax1.
auto.
RingReplace 1 (IZR (Z.succ 0)).
apply IZR_le.
apply msd_ax3.
auto.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1l.
rewrite Rplus_comm; symmetry  in |- *; rewrite Rplus_comm;
 apply Rplus_eq_compat_l. 
rewrite Rmult_assoc; symmetry  in |- *; rewrite Rmult_assoc;
 apply Rmult_eq_compat_l.
apply Rinv_Rmult_bis.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
replace (B_powerRZ (p_max yc n + p_max xc n - n) * B_powerRZ n) with
 (B_powerRZ (p_max yc n + p_max xc n - n + n)).
replace (B_powerRZ (p_max yc n - msd xc) * B_powerRZ (p_max xc n + msd xc))
 with (B_powerRZ (p_max yc n - msd xc + (p_max xc n + msd xc))).
unfold B_powerRZ in |- *; apply powerRZ_trivial; ring.
unfold B_powerRZ in |- *; apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
unfold B_powerRZ in |- *; apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
rewrite Rplus_comm.
apply Rplus_le_compat.
rewrite Rmult_1l; apply Rinv_le.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
apply INR_B_non_nul.
unfold B_powerRZ in |- *.
pattern (INR B) at 1 in |- *.
replace (INR B) with (powerRZ (INR B) (Z.succ 0)).
apply Rle_powerRZ.
apply Rlt_le; apply Rlt_le_trans with 4.
lra.
replace 4 with (INR 4).
apply le_INR; generalize B_sup_4; omega.
do 4 rewrite S_INR; simpl in |- *; ring. 
apply le_pmax_n.
apply powerRZ_1.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rmult_le_pos.
lra.
apply Rlt_le; apply INR_B_non_nul.
rewrite Rmult_comm; apply Rle_Rinv_monotony.
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
apply Rle_mult_inv.
apply Rlt_gt; unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
replace (B_powerRZ n * B_powerRZ (Z.succ (Z.succ (Z.succ 0)))) with
 (B_powerRZ (n + Z.succ (Z.succ (Z.succ 0)))).
unfold B_powerRZ in |- *; apply Rle_powerRZ.
apply Rlt_le; apply Rlt_le_trans with 4.
lra.
replace 4 with (INR 4).
apply le_INR; generalize B_sup_4; omega.
do 4 rewrite S_INR; simpl in |- *; ring. 
apply Zplus_le_reg_r with (- msd xc)%Z.
simpl in |- *.
RingReplace (n + 3 + - msd xc)%Z (n - msd xc + 3)%Z.
RingReplace (p_max xc n + msd xc + - msd xc)%Z (p_max xc n).
unfold p_max in |- *.
apply Zle_max_l. 
unfold B_powerRZ in |- *; apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
unfold B_powerRZ in |- *.
apply Rle_trans with (1 * / 4 + 2 * / powerRZ 4 (Z.succ (Z.succ 0))).
apply Rplus_le_compat.
do 2 rewrite Rmult_1l; apply Rinv_le.
apply INR_B_non_nul.
lra.
replace 4 with (INR 4).
apply le_INR; generalize B_sup_4; omega.
do 4 rewrite S_INR; simpl in |- *; ring. 
rewrite Rmult_assoc; apply Rmult_le_compat_l.
lra.
replace (/ powerRZ (INR B) (Z.succ (Z.succ (Z.succ 0)))) with
 (powerRZ (INR B) (- Z.succ (Z.succ (Z.succ 0)))).
replace (/ powerRZ 4 (Z.succ (Z.succ 0))) with (powerRZ 4 (- Z.succ (Z.succ 0))).
replace (INR B * powerRZ (INR B) (- Z.succ (Z.succ (Z.succ 0)))) with
 (powerRZ (INR B) (Z.succ 0 + - Z.succ (Z.succ (Z.succ 0)))).
simpl in |- *.
do 2 rewrite RIneq.Rmult_1_r.
apply Rinv_le.
apply Rmult_lt_0_compat.
apply INR_B_non_nul.
apply INR_B_non_nul.
lra.
generalize (Rsqr_incr_1 4 (INR B)).
unfold Rsqr in |- *.
intros.
apply H4.
replace 4 with (INR 4).
apply le_INR; generalize B_sup_4; omega.
do 4 rewrite S_INR; simpl in |- *; ring. 
lra.
apply Rle_trans with 4.
lra.
replace 4 with (INR 4).
apply le_INR; generalize B_sup_4; omega.
do 4 rewrite S_INR; simpl in |- *; ring. 
simpl in |- *.
rewrite RIneq.Rmult_1_r.
symmetry  in |- *; rewrite Rinv_mult_distr.
rewrite <- Rmult_assoc.
symmetry  in |- *; apply Rbase_operations.Rmult_1_r.
apply Rinv_r_sym.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
apply Rgt_not_eq; apply Rlt_gt; apply Rmult_lt_0_compat.
apply INR_B_non_nul.
apply INR_B_non_nul.
simpl in |- *.
field.
auto.
simpl in |- *.
lra.
Qed.

Hint Resolve multiplication_correct: reals.
