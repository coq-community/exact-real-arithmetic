(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import Reals.
Require Export definition.
Require Import Tactiques.
Require Import Rbase_inegalites.
Require Import Rbase_doubles_inegalites.
Require Import Rabsolu_complements.
Require Import powerRZ_complements.
Require Import Axiomes.
Require Import Lemmes.
Require Import Absolue.
Require Import sg.
Require Import Rind_complements.
Require Import Lemmes_generaux.
Require Import Zabs_complements.
Require Import Zpower_complements.
Require Import Fourier.
Require Import Zarith_operations.
Require Import Rbase_operations.

Axiom
  Zdiv_sup_opp :
    forall b c : Z, (c < 0)%Z -> (Zsgn c * Zdiv_sup b (Zabs c))%Z = (b / c)%Z.

Lemma inverse_correct :
 forall (x : R) (xc : Reelc),
 x <> 0 -> encadrement xc x -> encadrement (inverse_reelc xc) (1 * / x).   
Proof.
intros.
unfold encadrement in |- *; intro.
unfold inverse_reelc in |- *. 
case (Z_le_gt_dec n (- msd xc)).
intros; simpl in |- *.
RingReplace (0 - 1) (-1); RingReplace (0 + 1) 1.
apply Rbase_doubles_inegalites.Rabsolu_def3.
rewrite Rabs_mult.
apply Rle_lt_trans with (Rabs (1 * / x) * Rabs (B_powerRZ (- msd xc))).
apply Rmult_le_compat_l.
apply Rabs_pos.
unfold B_powerRZ in |- *.
apply Rsqr_le_abs_0.
apply Rsqr_incr_1;
 [ idtac
 | apply Rlt_le; apply powerRZ_lt; apply INR_B_non_nul
 | apply Rlt_le; apply powerRZ_lt; apply INR_B_non_nul ].
apply Rle_powerRZ; [ idtac | auto ].
RingReplace 1 (INR 1); apply le_INR; generalize B_sup_4; omega.
rewrite <- Rabs_mult.
apply Rlt_le_trans with (1 * / (IZR (Zabs (xc (msd xc))) - 1)).
apply Rlt_2_to_Rlt with (1 * / (IZR (Zabs (xc (msd xc))) + 1)).
rewrite Rmult_assoc; rewrite Rabs_mult.
rewrite Rabs_R1.
rewrite Rabs_mult.
replace (Rabs (/ x)) with (/ Rabs x);
 [ idtac | symmetry  in |- *; apply Rabs_Rinv; auto ].
unfold B_powerRZ in |- *.
replace (Rabs (powerRZ (INR B) (- msd xc))) with (/ powerRZ (INR B) (msd xc)). 
replace (/ Rabs x * / powerRZ (INR B) (msd xc)) with
 (/ (Rabs x * powerRZ (INR B) (msd xc))).
apply Rlt_2_Rinv.
RingReplace 1 (IZR (Zsucc 0)); RingReplace 0 (IZR 0).
rewrite <- plus_IZR; apply Rlt_gt.
apply IZR_lt.
apply Zlt_trans with (Zsucc 0).
auto with zarith.
apply Zlt_O_minus_lt.
RingReplace (Zabs (xc (msd xc)) + Zsucc 0 - Zsucc 0)%Z (Zabs (xc (msd xc))).
apply Zlt_trans with 1%Z; [ omega | apply msd_c_ter ].
apply Rmult_gt_0_compat.
apply Rlt_gt; apply Rabs_pos_lt; auto.
apply Rlt_gt; apply powerRZ_lt; apply INR_B_non_nul.
apply Rlt_gt; apply Rlt_sub_compatibility.
RingReplace (0 + 1) 1.
RingReplace 1 (IZR (Zsucc 0)); apply IZR_lt; apply msd_c_ter.
cut (encadrement (absolue_reelc xc) (Rabs x)).
unfold encadrement in |- *.
intro.
generalize (H1 (msd xc)).
unfold absolue_reelc in |- *; unfold B_powerRZ in |- *; auto.
apply absolue_correct; auto.
apply Rinv_mult_distr.
apply Rabs_no_R0; auto.
apply powerRZ_INR_B_non_nul.
transitivity (powerRZ (INR B) (- msd xc)).
apply Rinv_powerRZ.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
symmetry  in |- *; apply Rabs_pos_eq.
apply Rlt_le; apply powerRZ_lt; apply INR_B_non_nul.
rewrite Rmult_comm; apply Rle_Rinv_monotony.
apply Rlt_sub_compatibility.
RingReplace (0 + 1) 1.
RingReplace 1 (IZR (Zsucc 0)); apply IZR_lt; apply msd_c_ter.
rewrite RIneq.Rmult_1_r.
apply Rle_add_compatibility.
RingReplace (1+1) (IZR (Zsucc (Zsucc 0))); apply IZR_le.
apply Zlt_le_succ; apply msd_c_ter.

intro.
cut (Zabs (xc (n + 2 * msd xc + 1)) > 1)%Z.
intros.
cut
 (encadrement_bis
    (Zdiv_sup (B_powerZ (2 * n + 2 * msd xc + 1))
       (Zabs (xc (n + 2 * msd xc + 1)%Z))) n (/ Rabs x)).
intros.
case (Z_gt_le_dec (xc (n + 2 * msd xc + 1)%Z) 1); intros.
cut
 (encadrement_bis
    (Zdiv_sup (B_powerZ (2 * n + 2 * msd xc + 1)) (xc (n + 2 * msd xc + 1)%Z))
    n (1 * / x)); auto. 
replace (xc (n + 2 * msd xc + 1)%Z) with (Zabs (xc (n + 2 * msd xc + 1)%Z)).
replace
 (Zdiv_sup (B_powerZ (2 * n + 2 * msd xc + 1))
    (Zabs (xc (n + 2 * msd xc + 1)%Z))) with
 (sg x *
  Zdiv_sup (B_powerZ (2 * n + 2 * msd xc + 1))
    (Zabs (xc (n + 2 * msd xc + 1))))%Z.
rewrite Rmult_1l.
apply encadrement_bis_prop2; auto.
unfold Zdiv_sup in |- *.
case
 (Z_zerop
    (B_powerZ (2 * n + 2 * msd xc + 1) mod Zabs (xc (n + 2 * msd xc + 1)%Z)));
 intro.
apply Zge_le.
apply Z_div_ge0.
apply Zabs_lt_0.
apply Compare.not_eq_sym.
apply Zorder.Zlt_not_eq.
apply Zlt_trans with 1%Z.
omega.
auto with zarith.
unfold B_powerZ in |- *.
apply Zle_ge.
apply Zpower_le_0.
apply lt_O_IZR.
rewrite <- INR_IZR_INZ.
apply INR_B_non_nul.
apply Zle_le_succ.
apply Zge_le.
apply Z_div_ge0.
apply Zabs_lt_0.
apply Compare.not_eq_sym.
apply Zorder.Zlt_not_eq.
apply Zlt_trans with 1%Z.
omega.
auto with zarith.
unfold B_powerZ in |- *.
apply Zle_ge.
apply Zpower_le_0.
apply lt_O_IZR.
rewrite <- INR_IZR_INZ.
apply INR_B_non_nul.
replace (sg x) with 1%Z.
ring.
symmetry  in |- *; apply sg_pos.
apply sg_Zsgn with xc (n + 2 * msd xc + 1)%Z.
auto.
apply Zlt_trans with 1%Z.
omega.
auto with zarith.
apply Zabs_eq.
apply Zlt_le_weak.
apply Zlt_trans with 1%Z.
omega.
auto with zarith.

replace (B_powerZ (2 * n + 2 * msd xc + 1) / xc (n + 2 * msd xc + 1))%Z with
 (sg x *
  Zdiv_sup (B_powerZ (2 * n + 2 * msd xc + 1))
    (Zabs (xc (n + 2 * msd xc + 1))))%Z.
rewrite Rmult_1l.
apply encadrement_bis_prop2; auto.
unfold Zdiv_sup in |- *.
case
 (Z_zerop
    (B_powerZ (2 * n + 2 * msd xc + 1) mod Zabs (xc (n + 2 * msd xc + 1)%Z)));
 intro.
apply Zge_le.
apply Z_div_ge0.
apply Zabs_lt_0.
apply Zabs_not_eq.
apply Zgt_trans with 1%Z.
auto.
omega.
unfold B_powerZ in |- *.
apply Zle_ge.
apply Zpower_le_0.
apply lt_O_IZR.
rewrite <- INR_IZR_INZ.
apply INR_B_non_nul.
apply Zle_le_succ.
apply Zge_le.
apply Z_div_ge0.
apply Zgt_trans with 1%Z.
auto.
omega.
unfold B_powerZ in |- *.
apply Zle_ge.
apply Zpower_le_0.
apply lt_O_IZR.
rewrite <- INR_IZR_INZ.
apply INR_B_non_nul.
unfold B_powerZ in |- *.

replace (sg x) with (Zsgn (xc (n + 2 * msd xc + 1)%Z)).
apply Zdiv_sup_opp.
apply Zabs_01 with 1%Z.
omega.
auto.
auto with zarith.
apply Zsgn_sg_bis.
auto.
apply Zlt_trans with 1%Z.
omega.
auto with zarith.




cut
 (IZR
    (Z_of_nat B ^ (Zsucc (Zsucc 0) * n + Zsucc (Zsucc 0) * msd xc + Zsucc 0) /
     (Zabs (xc (n + Zsucc (Zsucc 0) * msd xc + Zsucc 0)%Z) + Zsucc 0)) <
  / Rabs x * B_powerRZ n <
  IZR
    (Zdiv_sup
       (B_powerZ (Zsucc (Zsucc 0) * n + Zsucc (Zsucc 0) * msd xc + Zsucc 0))
       (Zabs (xc (n + Zsucc (Zsucc 0) * msd xc + Zsucc 0)%Z) - Zsucc 0))).
set
 (alpha :=
  (Z_of_nat B ^ (Zsucc (Zsucc 0) * n + Zsucc (Zsucc 0) * msd xc + Zsucc 0) /
   (Zabs (xc (n + Zsucc (Zsucc 0) * msd xc + Zsucc 0)) + Zsucc 0))%Z) 
 in *.
set
 (beta :=
  Zdiv_sup
    (B_powerZ (Zsucc (Zsucc 0) * n + Zsucc (Zsucc 0) * msd xc + Zsucc 0))
    (Zabs (xc (n + Zsucc (Zsucc 0) * msd xc + Zsucc 0)%Z) - Zsucc 0)) 
 in *.
set
 (lambda :=
  Zdiv_sup (B_powerZ (2 * n + 2 * msd xc + 1))
    (Zabs (xc (n + 2 * msd xc + 1)%Z))) in *.
intro.
cut (1 <= beta - alpha <= 2)%Z. 
intro.
cut (alpha <= lambda <= beta)%Z. 
intro.
unfold encadrement_bis in |- *.
cut (beta = (alpha + 1)%Z \/ beta = (alpha + 2)%Z).
intro.
elim H5; intro.
cut (lambda = alpha \/ lambda = (alpha + 1)%Z).
intro.
elim H7; intro.
rewrite H8.
replace (IZR alpha + 1) with (IZR (alpha + Zsucc 0)). 
RingReplace (alpha + Zsucc 0)%Z (alpha + 1)%Z.
rewrite <- H6.
split.
apply Rlt_trans with (IZR alpha).
auto with real.
elim H2; auto.
elim H2; auto.
RingReplace 1 (IZR (Zsucc 0)).
rewrite plus_IZR; auto.
rewrite H8.
replace (IZR (alpha + 1) - 1) with (IZR alpha).
split.
elim H2; auto.
apply Rlt_trans with (IZR (alpha + 1)).
rewrite <- H6; elim H2; auto.
auto with real.
RingReplace 1 (IZR (Zsucc 0)).
rewrite Z_R_minus.
RingReplace (alpha + 1 - Zsucc 0)%Z alpha; auto.
omega.
RingReplace (alpha + 1)%Z (Zsucc alpha).

cut (lambda = (alpha + 1)%Z).
intro.
rewrite H7.
replace (IZR (alpha + 1) - 1) with (IZR alpha).
replace (IZR (alpha + 1) + 1) with (IZR (alpha + Zsucc (Zsucc 0))).
replace (alpha + Zsucc (Zsucc 0))%Z with (alpha + 2)%Z.
rewrite <- H6.
auto.
omega.
change 1 with (IZR (Zsucc 0)).
rewrite <- plus_IZR.
apply IZR_trivial.
omega.
change 1 with (IZR (Zsucc 0)).
rewrite Z_R_minus.
apply IZR_trivial.
omega.
unfold alpha, lambda in |- *.
unfold Zdiv_sup in |- *.
case
 (Z_zerop
    (B_powerZ (2 * n + 2 * msd xc + 1) mod Zabs (xc (n + 2 * msd xc + 1)%Z)));
 unfold B_powerZ in |- *; intros.
unfold Zdiv in |- *.
Abort.
