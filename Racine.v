(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import definition.
Require Import Reals.
Require Import Zind_complements.
Require Import Tactiques.
Require Import Fourier.
Require Import Lemmes.
Require Import Zsqrt_complements.
Require Import Rbase_inegalites.
Require Import Lemmes_generaux.
Require Import Rbase_doubles_inegalites.
Require Import Zarith_inegalites.
Require Import Zarith_operations.


Axiom Int_part_sqrt : forall z : Z, Zsqrt_plain z = Int_part (sqrt (IZR z)).


Axiom
  Int_part_interval :
    forall r1 r2 : R,
    (exists z : Z, IZR z <= r1 < IZR z + 1 /\ IZR z <= r2 < IZR z + 1) ->
    Int_part r1 = Int_part r2.

Lemma racine_correct :
 forall (x : R) (xc : Reelc),
 0 <= x -> encadrement xc x -> encadrement (racine_reelc xc) (sqrt x). 

Proof.
intros x xc H0.
unfold encadrement in |- *.
unfold racine_reelc in |- *.
intros.
pattern (xc (2 * n)%Z) in |- *. 
apply Zind_le_ZERO; intros.
generalize (H (2 * n)%Z).
rewrite <- H1.
replace (xc (Zsucc (Zsucc 0) * n)%Z) with 0%Z.
RingReplace (IZR 0) 0.
rewrite Zsqrt_0.
replace (Int_part 0) with 0%Z.
RingReplace (IZR 0) 0.
RingReplace (0 - 1) (-1); RingReplace (0 + 1) 1.
clear H; intros.
intuition.
apply Rlt_le_trans with 0.
fourier.
apply Rmult_le_pos.
rewrite <- sqrt_0.
apply sqrt_le_1; auto.
fourier.
unfold B_powerRZ in |- *.
apply powerRZ_le.
apply INR_B_non_nul.
rewrite <- sqrt_1.
replace (B_powerRZ n) with (sqrt (B_powerRZ (2 * n))). 
replace (sqrt x * sqrt (B_powerRZ (2 * n))) with
 (sqrt (x * B_powerRZ (2 * n))).
apply sqrt_lt_1.
apply Rmult_le_pos.
auto.
unfold B_powerRZ in |- *.
apply powerRZ_le.
apply INR_B_non_nul.
fourier.
auto.
apply sqrt_mult.
auto.
unfold B_powerRZ in |- *.
apply powerRZ_le.
apply INR_B_non_nul.
unfold B_powerRZ in |- *.
replace (powerRZ (INR B) (2 * n)) with
 (powerRZ (INR B) n * powerRZ (INR B) n).
apply sqrt_square.
unfold B_powerRZ in |- *.
apply powerRZ_le.
apply INR_B_non_nul.
symmetry  in |- *.
RingReplace (2 * n)%Z (n + n)%Z.
apply powerRZ_add.
apply Rgt_not_eq.
apply Rlt_gt.
apply INR_B_non_nul.
unfold Int_part in |- *.
apply Zplus_minus_eq.
rewrite Zplus_comm; symmetry  in |- *.
apply up_tech; simpl in |- *; fourier.


(*2eme partie*)

generalize (Zsqr_cond (xc (2 * n)%Z)).
intros.
elim H2; clear H2; try omega.
intros.
decompose [or] H2; clear H2.

(*a revoir a partir de la*)

replace (IZR (Zsqrt_plain (xc (Zsucc (Zsucc 0) * n)%Z)) - 1) with
 (IZR (Zsqrt_plain (xc (Zsucc (Zsucc 0) * n)%Z - Zsucc 0))).
replace (IZR (Zsqrt_plain (xc (Zsucc (Zsucc 0) * n)%Z))) with
 (IZR (Zsqrt_plain (xc (Zsucc (Zsucc 0) * n)%Z + Zsucc 0))).
apply
 Rlt_2_le_lt
  with
    (sqrt (IZR (xc (Zsucc (Zsucc 0) * n)%Z - Zsucc 0)))
    (sqrt (IZR (xc (Zsucc (Zsucc 0) * n)%Z + Zsucc 0))).
replace (B_powerRZ n) with (sqrt (B_powerRZ (2 * n))). 
replace (sqrt x * sqrt (B_powerRZ (2 * n))) with
 (sqrt (x * B_powerRZ (2 * n))).
apply Rlt_2_sqrt.
RingReplace 0 (IZR 0).
apply IZR_le.
apply Zle_add_compatibility.
RingReplace (0 + Zsucc 0)%Z (Zsucc 0).
apply Zlt_le_succ; auto.
apply Rmult_le_pos.
auto.
unfold B_powerRZ in |- *.
apply powerRZ_le.
apply INR_B_non_nul.
RingReplace 0 (IZR 0).
apply IZR_le.
apply Zle_trans with (xc (Zsucc (Zsucc 0) * n)%Z).
apply Zlt_le_weak.
auto.
omega.
rewrite <- Z_R_minus.
rewrite plus_IZR.
RingReplace (IZR (Zsucc 0)) 1.
generalize (H (Zsucc (Zsucc 0) * n)%Z); auto.
apply sqrt_mult.
auto.
unfold B_powerRZ in |- *.
apply powerRZ_le.
apply INR_B_non_nul.
unfold B_powerRZ in |- *.
replace (powerRZ (INR B) (2 * n)) with
 (powerRZ (INR B) n * powerRZ (INR B) n).
apply sqrt_square.
apply powerRZ_le.
apply INR_B_non_nul.
symmetry  in |- *.
RingReplace (2 * n)%Z (n + n)%Z.
apply powerRZ_add.
apply Rgt_not_eq.
apply Rlt_gt.
apply INR_B_non_nul.
apply Zsqrt_sqrt.
apply Zle_add_compatibility.
rewrite Zplus_comm.
rewrite <- Zplus_0_r_reverse.
apply Zgt_le_succ.
apply Zlt_gt.
auto.
apply Zsqrt_sqrt_bis.
replace (xc (Zsucc (Zsucc 0) * n) + Zsucc 0)%Z with
 (Zsucc (xc (Zsucc (Zsucc 0) * n)%Z)); [ idtac | omega ].
apply Zle_le_succ.
apply Zlt_le_weak; auto.
apply IZR_trivial.
RingReplace (Zsucc (Zsucc 0)) 2%Z.
rewrite H4.
do 2 rewrite Int_part_sqrt.
apply Int_part_interval.
exists x0.
intuition.
elim x0; intros.
simpl in |- *.
rewrite sqrt_1; fourier.
replace (IZR (Zpos p)) with (sqrt (Rsqr (IZR (Zpos p)))).
apply sqrt_le_1.
apply Rle_0_sqr.
RingReplace 0 (IZR 0).
apply IZR_le.
intuition.
rewrite plus_IZR; rewrite mult_IZR.
unfold Rsqr in |- *.
intuition.
apply sqrt_Rsqr.
RingReplace 0 (IZR 0); apply IZR_le.
intuition.
apply Rle_trans with 0.
RingReplace 0 (IZR 0); apply IZR_le.
apply Zlt_le_weak.
apply Zorder.Zlt_neg_0.
apply sqrt_positivity.
RingReplace 0 (IZR 0).
apply IZR_le.
replace (Zneg p * Zneg p + Zsucc 0)%Z with (Zsucc (Zneg p * Zneg p));
 [ idtac | omega ].
apply Zle_le_succ.
apply Zge_le; apply sqr_pos.
RingReplace (IZR x0 + 1) (IZR (x0 + Zsucc 0)).
replace (IZR (x0 + Zsucc 0)) with (sqrt (Rsqr (IZR (x0 + Zsucc 0)))).
apply sqrt_lt_1.
RingReplace 0 (IZR 0); apply IZR_le.
omega.
apply Rle_0_sqr.
unfold Rsqr in |- *.
rewrite <- mult_IZR; apply IZR_lt.
RingReplace ((x0 + Zsucc 0) * (x0 + Zsucc 0))%Z
 (x0 * x0 + Zsucc 0 + 2 * Zsucc 0 * x0)%Z.

(*faux*) 

Abort.