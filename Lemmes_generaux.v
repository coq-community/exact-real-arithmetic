(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import definition. 
Require Import Psatz.
Require Import Tactiques.
Require Import Axiomes.
Require Import Rbase_doubles_inegalites.
Require Import Rlog.
Require Import Zind_complements.
Require Import Rbase_inegalites.
Require Import powerRZ_complements.
Require Import Absolue.
Require Import Zpower.
Require Import Zarith_operations.
Require Import sg.
Require Import Lemmes.
Require Import Rind_complements.
Require Import Classical_Prop.

Lemma gauss_sur_B_O :
 forall z n : Z,
 0 < IZR (gauss_z_sur_B_pow z n) < 1 * / 2 -> gauss_z_sur_B_pow z n = 0%Z.

Proof.
intros.
apply one_IZR_lt1.
apply Rlt_2_trans with 0 (1 * / 2).
auto.
lra.
lra.
Qed.

Hint Resolve gauss_sur_B_O: real.


Lemma msd_ax1 :
 forall (xc yc : Reelc) (n : Z),
 (1 < Z.abs (xc (p_max yc n)))%Z -> (msd xc <= p_max yc n)%Z.

Proof.
intros.
apply Z.ge_le.
apply Znot_lt_ge.
cut
 (~ ((Z.abs (xc (p_max yc n)) <= 1)%Z /\ (Z.abs (xc (msd xc)) > 1)%Z) ->
  ~ (p_max yc n < msd xc)%Z).
intros.
apply H0.
apply or_not_and.
left.
apply Zlt_not_le; auto.
generalize (msd_c xc); intuition.
Qed.


Lemma msd_ax3 :
 forall (xc yc : Reelc) (n : Z),
 (p_max yc n < msd xc)%Z -> (Z.abs (xc (p_max yc n)) <= 1)%Z.

Proof.
intros.
apply Z.ge_le.
apply Znot_lt_ge.
cut (~ (msd xc <= p_max yc n)%Z -> ~ (1 < Z.abs (xc (p_max yc n)))%Z).
intro.
apply H0.
apply Zlt_not_le; auto.
cut ((1 < Z.abs (xc (p_max yc n)))%Z -> (msd xc <= p_max yc n)%Z);
 [ tauto | apply msd_ax1 ].
Qed.


Lemma B_INR_1 : forall B, (4<=B)%nat -> 1 <= INR B.
Proof.
  intros.
  replace 1 with (INR 1).
  apply le_INR; omega.
  reflexivity.
Qed.

Lemma B_INR_1' : forall B, (4<=B)%nat -> 1 < INR B.
Proof.
  intros.
  replace 1 with (INR 1).
  apply lt_INR; omega.
  reflexivity.
Qed.

Lemma powerRZ_Int_part_Rabs : forall x:R,
    x<>0 ->
    powerRZ (INR B) (Int_part (Rlog (Rabs x) (INR B))) <= Rabs x.
Proof.
  intros.
  rewrite powerRZ_Rpower.
  apply Rle_trans with (Rpower (INR B) ( (Rlog (Rabs x) (INR B)))).
  apply Rle_Rpower.
  apply B_INR_1; apply B_sup_4.
  destruct (base_Int_part (Rlog (Rabs x) (INR B))) as [b1 b2]; assumption.
  unfold Rpower, Rlog.
  replace (ln (Rabs x) / ln (INR B) * ln (INR B)) with (ln (Rabs x)).
  rewrite exp_ln.
  apply Rle_refl.
  apply Rabs_pos_lt; assumption.
  field.
  rewrite <- ln_1.
  apply Rgt_not_eq.
  apply ln_increasing.
  apply Rlt_0_1.
  apply B_INR_1'; apply B_sup_4.
  apply INR_B_non_nul.
Qed.

Lemma powerRZ_Int_part_Rabs2 : forall x:R,
    x<>0 ->
    Rabs x < powerRZ (INR B) (Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0).
Proof.
  intros.
  rewrite powerRZ_Rpower.
  apply Rle_lt_trans with (Rpower (INR B) ( (Rlog (Rabs x) (INR B)))).
  unfold Rpower, Rlog.
  replace (ln (Rabs x) / ln (INR B) * ln (INR B)) with (ln (Rabs x)).
  rewrite exp_ln.
  apply Rle_refl.
  apply Rabs_pos_lt; assumption.
  field.
  rewrite <- ln_1.
  apply Rgt_not_eq.
  apply ln_increasing.
  apply Rlt_0_1.
  apply B_INR_1'; apply B_sup_4.
  apply Rpower_lt.
  apply B_INR_1'; apply B_sup_4.
  destruct (base_Int_part (Rlog (Rabs x) (INR B))) as [b1 b2].
  rewrite plus_IZR.
  apply Rgt_lt in b2.
  apply Rplus_lt_reg_l with (- 1 - Rlog (Rabs x) (INR B)).
  simpl;ring_simplify.
  rewrite Rplus_comm.
  assumption.
  apply INR_B_non_nul.
Qed.

(*Probleme :reecrire toutes les ingalites dans R *)

Lemma msd_prop1 :
 forall (x : R) (xc : Reelc),
 x <> 0 ->
 encadrement xc x ->
 {msd xc = (- Int_part (Rlog (Rabs x) (INR B)))%Z} +
 {msd xc = (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z}.  

Proof.
intros.
cut
 (forall n : Z,
  (n < - Int_part (Rlog (Rabs x) (INR B)))%Z -> (Z.abs (xc n) <= 1)%Z).
intro.
cut
 ({(1 < Z.abs (xc (- Int_part (Rlog (Rabs x) (INR B)))))%Z} +
  {1%Z = Z.abs (xc (- Int_part (Rlog (Rabs x) (INR B)))%Z)}).
intro.
elim H2.
intro.
left.
eapply (msd_c_bis xc (- Int_part (Rlog (Rabs x) (INR B)))).
split.
apply H1.
auto with zarith.
intros.
right.
eapply (msd_c_bis xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)).
split.
intros.
pattern n in |- *.
apply Zind_plus_1 with (- Int_part (Rlog (Rabs x) (INR B)))%Z; auto.
intro.
rewrite H4; auto.
rewrite b; auto with zarith.
apply Z.lt_gt; apply Z.lt_le_trans with (Z_of_nat B).
idtac.
RingReplace 1%Z (Z_of_nat 1); apply Znat.inj_lt.
generalize B_sup_4; omega.
apply Zlt_succ_le.
apply lt_IZR; rewrite <- INR_IZR_INZ.
unfold Z.succ in |- *; rewrite plus_IZR; simpl in |- *.
apply
 Rle_lt_trans
  with
    (Rabs x * powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0)).
rewrite Rmult_comm;
 apply
  Rmult_le_reg_l
   with (/ powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0)).
apply Rinv_0_lt_compat; apply powerRZ_lt.
apply lt_INR_0; generalize B_sup_4; omega.
rewrite <- Rmult_assoc.
replace
 (/ powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0) *
  powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0)) with 1;
 [ rewrite Rmult_1_l
 | apply Rinv_l_sym; apply Rgt_not_eq; apply Rlt_gt; apply powerRZ_lt;
    apply lt_INR_0; generalize B_sup_4; omega ].
replace (/ powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0))
 with (powerRZ (INR B) (- (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0)));
 [ idtac
 | symmetry  in |- *; apply Rinv_powerRZ; apply Rgt_not_eq; apply Rlt_gt;
    apply lt_INR_0; generalize B_sup_4; omega ].
replace
 (powerRZ (INR B) (- (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0)) * INR B)
 with
 (powerRZ (INR B) (Z.succ (- (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0))));
 [ idtac
 | apply powerRZ_Zs; apply Rgt_not_eq; apply Rlt_gt; apply lt_INR_0;
    generalize B_sup_4; omega ].
rewrite Zopp_plus_distr; rewrite Zplus_comm; rewrite <- Zplus_succ_l;
 rewrite Z.opp_involutive; simpl in |- *.
apply powerRZ_Int_part_Rabs; assumption.
cut (encadrement (absolue_reelc xc) (Rabs x)).
unfold encadrement in |- *.
intro.
generalize (H3 (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0)%Z).
intro.
elim H4.
unfold B_powerRZ in |- *; intros; auto.
apply absolue_correct; auto.
apply Z_le_lt_eq_dec.
apply Zlt_succ_le.
apply lt_IZR.
apply
 Rle_lt_trans
  with (Rabs x * powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)))).
rewrite Rmult_comm;
 apply
  Rmult_le_reg_l
   with (/ powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)))).
apply Rinv_0_lt_compat; apply powerRZ_lt.
apply lt_INR_0; generalize B_sup_4; omega.
rewrite <- Rmult_assoc.
replace
 (/ powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B))) *
  powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)))) with 1;
 [ rewrite Rmult_1_l
 | apply Rinv_l_sym; apply Rgt_not_eq; apply Rlt_gt; apply powerRZ_lt;
    apply lt_INR_0; generalize B_sup_4; omega ].
replace (/ powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)))) with
 (powerRZ (INR B) (- - Int_part (Rlog (Rabs x) (INR B))));
 [ idtac
 | symmetry  in |- *; apply Rinv_powerRZ; apply Rgt_not_eq; apply Rlt_gt;
    apply lt_INR_0; generalize B_sup_4; omega ].
rewrite Z.opp_involutive; simpl in |- *; rewrite Rmult_1_r.
apply powerRZ_Int_part_Rabs; assumption.
unfold Z.succ in |- *; rewrite plus_IZR.
cut (encadrement (absolue_reelc xc) (Rabs x)).
unfold encadrement in |- *.
intro.
generalize (H2 (- Int_part (Rlog (Rabs x) (INR B)))%Z); clear H2. 
intro.
elim H2.
unfold B_powerRZ in |- *; intros; auto.
apply absolue_correct; auto.
intros.
replace (Z.abs (xc n)) with (Z.succ (Z.abs (xc n) - 1));
 [ apply Zlt_le_succ | unfold Z.succ in |- *; simpl in |- *; ring ].
apply lt_IZR.
rewrite <- Z_R_minus.
apply
 Rlt_le_trans
  with (powerRZ (INR B) (n + Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0)).
apply Rlt_trans with (Rabs x * powerRZ (INR B) n). 
cut (encadrement (absolue_reelc xc) (Rabs x));
 [ unfold encadrement in |- *; unfold B_powerRZ in |- *; intro
 | apply absolue_correct; auto ].
generalize (H2 n); clear H2.
intros.
elim H2; intro; auto.
replace (powerRZ (INR B) (n + Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0))
 with
 (powerRZ (INR B) (Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0) *
  powerRZ (INR B) n).
apply Rmult_lt_compat_r;
 [ apply powerRZ_lt; apply lt_INR_0; generalize B_sup_4; omega | idtac ].
apply powerRZ_Int_part_Rabs2; assumption.
rewrite <- Zplus_assoc; rewrite Rmult_comm; symmetry  in |- *;
 apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply lt_INR_0; generalize B_sup_4; omega.
replace (IZR 1) with (powerRZ (INR B) 0).
apply Rle_powerRZ.
apply Rlt_le.
RingReplace 1 (INR 1).
apply lt_INR; generalize B_sup_4; omega.
rewrite <- Zplus_succ_r; apply Zgt_le_succ; rewrite <- Zplus_0_r_reverse.
apply Z.lt_gt; auto with zarith.
apply powerRZ_O.
Qed.

Lemma msd_ax2 :
 forall (x : R) (xc yc : Reelc) (n : Z),
 x <> 0 ->
 encadrement xc x ->
 (msd xc <= p_max yc n)%Z ->
 IZR (Z.abs (xc (p_max yc n))) <= 2 * INR B * B_powerRZ (p_max yc n - msd xc).

Proof.
intros.
replace (2 * INR B * B_powerRZ (p_max yc n - msd xc)) with
 (IZR (Z.succ (Z.succ 0) * Z_of_nat B * Z_of_nat B ^ (p_max yc n - msd xc))).
apply IZR_le.
apply Zlt_succ_le.
apply lt_IZR.
unfold Z.succ in |- *; rewrite plus_IZR; rewrite mult_IZR.
replace (IZR (Z_of_nat B ^ (p_max yc n - msd xc))) with
 (B_powerRZ (p_max yc n - msd xc)).
unfold B_powerRZ in |- *.
rewrite mult_IZR.
rewrite <- INR_IZR_INZ; auto.
RingReplace (IZR (0 + 1 + 1)) 2.
RingReplace (IZR 1) 1.
rewrite Rmult_assoc.
replace (INR B * powerRZ (INR B) (p_max yc n - msd xc)) with
 (powerRZ (INR B) (Z.succ (p_max yc n - msd xc)));
 [ idtac
 | rewrite Rmult_comm; apply powerRZ_Zs; apply Rgt_not_eq; apply Rlt_gt;
    apply lt_INR_0; generalize B_sup_4; omega ].
apply Rlt_add_compatibility2.
apply Rmult_lt_reg_l with (powerRZ (INR B) (- Z.succ (p_max yc n - msd xc))).
apply powerRZ_lt; apply lt_INR_0; generalize B_sup_4; omega.
apply Rgt_lt; rewrite Rmult_comm; rewrite Rmult_assoc;
 apply Rlt_gt.
replace
 (powerRZ (INR B) (Z.succ (p_max yc n - msd xc)) *
  powerRZ (INR B) (- Z.succ (p_max yc n - msd xc))) with 1;
 [ rewrite Rmult_1_r | idtac ].
rewrite Rmult_comm;
 apply Rlt_le_trans with (Rabs x * powerRZ (INR B) (Z.pred (msd xc))).
replace (powerRZ (INR B) (- Z.succ (p_max yc n - msd xc))) with
 (powerRZ (INR B) (- p_max yc n) * powerRZ (INR B) (Z.pred (msd xc)));
 [ rewrite <- Rmult_assoc; apply Rmult_lt_compat_r | idtac ].
apply powerRZ_lt; apply lt_INR_0; generalize B_sup_4; omega.
apply Rmult_lt_reg_l with (powerRZ (INR B) (p_max yc n)).
apply powerRZ_lt; apply lt_INR_0; generalize B_sup_4; omega.
rewrite Rmult_comm; rewrite Rmult_assoc.
replace (powerRZ (INR B) (- p_max yc n) * powerRZ (INR B) (p_max yc n)) with
 1.
rewrite Rmult_1_r.
cut (encadrement (absolue_reelc xc) (Rabs x));
 [ intro | apply absolue_correct; auto ].
generalize H2.
unfold encadrement in |- *.
intro.
generalize (H3 (p_max yc n)).
intro.
elim H4.
unfold B_powerRZ in |- *; intros; rewrite Rmult_comm; auto.
rewrite Rmult_comm; apply powerRZ_Zopp.
apply Rgt_not_eq; apply Rlt_gt; apply lt_INR_0; generalize B_sup_4; omega.
unfold Z.pred in |- *.
unfold Z.succ in |- *.
rewrite Zopp_plus_distr.
transitivity (powerRZ (INR B) (- p_max yc n + (msd xc + -1))).
symmetry  in |- *; apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply lt_INR_0; generalize B_sup_4; omega.
apply powerRZ_trivial.
ring.
apply Rle_trans with (IZR (Z.abs (xc (Z.pred (msd xc)))) + 1).
apply Rlt_le.
cut (encadrement (absolue_reelc xc) (Rabs x));
 [ intro | apply absolue_correct; auto ].
generalize H2.
unfold encadrement in |- *.
intro.
generalize (H3 (Z.pred (msd xc))).
intro.
elim H4.
unfold B_powerRZ in |- *; intros; auto.
RingReplace 2 2; apply Rplus_le_compat_r.
apply msd_c_4.
apply powerRZ_Zopp.
apply Rgt_not_eq; apply Rlt_gt; apply lt_INR_0; generalize B_sup_4; omega.
unfold B_powerRZ in |- *.
transitivity (IZR (Zpower_nat (Z_of_nat B) (Z.abs_nat (p_max yc n - msd xc)))).
rewrite INR_IZR_INZ.
symmetry  in |- *; apply Zpower_nat_powerRZ_absolu.
auto with zarith.
apply IZR_trivial.
unfold Z.abs_nat in |- *.
cut (p_max yc n - msd xc >= 0)%Z.
case (p_max yc n - msd xc)%Z; intro.
simpl in |- *.
auto with zarith.
simpl in |- *.
intro.
symmetry  in |- *; apply Zpower_pos_nat.
intro; absurd (Zneg p >= 0)%Z; auto with *.
omega.
do 2 rewrite mult_IZR.
unfold B_powerRZ in |- *.
rewrite INR_IZR_INZ.
RingReplace (IZR (Z.succ (Z.succ 0))) 2.
apply Rmult_eq_compat_l.
transitivity (IZR (Zpower_nat (Z_of_nat B) (Z.abs_nat (p_max yc n - msd xc)))).
2: apply Zpower_nat_powerRZ_absolu; auto with zarith.
apply IZR_trivial.
unfold Z.abs_nat in |- *.
cut (p_max yc n - msd xc >= 0)%Z.
case (p_max yc n - msd xc)%Z; intro.
simpl in |- *.
auto with zarith.
simpl in |- *.
intro.
apply Zpower_pos_nat.
intro; absurd (Zneg p >= 0)%Z; auto with *.
omega.
Qed.


Lemma encadrement_bis_prop1 :
 forall (p n : Z) (x : R),
 encadrement_bis p n (Rabs x) -> (0 <= p)%Z -> encadrement_bis (sg x * p) n x.

Proof.
intros.
pattern p in |- *.
apply Zind_le_ZERO; auto; intros.
generalize H.
rewrite <- H1; rewrite <- Zmult_0_r_reverse. 
unfold encadrement_bis in |- *.
simpl in |- *.
RingReplace (0 - 1) (-1); RingReplace (0 + 1) 1.
intro.
apply Rbase_doubles_inegalites.Rabsolu_def3.
rewrite Rabs_mult.
replace (Rabs (B_powerRZ n)) with (B_powerRZ n).
elim H2; auto.
symmetry  in |- *; apply Rabs_pos_eq.
unfold B_powerRZ in |- *.
apply powerRZ_le.
apply INR_B_non_nul.

unfold encadrement_bis in |- *.
pattern x in |- *.
apply Rind_complements.Rabsolu_not_0_ind; intros.
replace (sg x) with 1%Z; [ idtac | symmetry  in |- *; apply sg_pos; auto ].
rewrite Zmult_comm; rewrite Zmult_1_r.
replace x with (Rabs x).
auto.
apply Rabs_right.
apply Rgt_ge; auto.
replace (sg x) with (-1)%Z; [ idtac | symmetry  in |- *; apply sg_neg; auto ].
replace x with (- Rabs x).
rewrite Zmult_comm; rewrite <- Zopp_eq_mult_neg_1.
rewrite Ropp_Ropp_IZR.
RingReplace (- IZR p - 1) (- (IZR p + 1)).
RingReplace (- IZR p + 1) (- (IZR p - 1)).
rewrite Ropp_mult_distr_l_reverse.
apply Rlt_2_Ropp_r.
auto.
apply Rmult_eq_reg_l with (-1).
RingReplace (-1 * - Rabs x) (Rabs x).
RingReplace (-1 * x) (- x).
apply Rabs_left; auto.
apply Rlt_not_eq.
lra.
apply Rlt_gt.
apply Rmult_lt_reg_l with (B_powerRZ n).
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
rewrite Rmult_0_r.
apply Rle_lt_trans with (IZR p - 1).
apply Rle_add_compatibility.
RingReplace (0 + 1) 1.
RingReplace 1 (IZR (Z.succ 0)).
apply IZR_le.
apply Zlt_le_succ.
auto.
unfold encadrement_bis in H.
rewrite Rmult_comm.
elim H.
auto.
Qed.



Lemma encadrement_bis_prop2 :
 forall (p n : Z) (x : R),
 x <> 0 ->
 encadrement_bis p n (/ Rabs x) ->
 (0 <= p)%Z -> encadrement_bis (sg x * p) n (/ x).

Proof.
intros.
pattern p in |- *.
apply Zind_le_ZERO; auto; intros.
generalize H0.
rewrite <- H2; rewrite <- Zmult_0_r_reverse. 
unfold encadrement_bis in |- *.
simpl in |- *.
RingReplace (0 - 1) (-1); RingReplace (0 + 1) 1.
intro.
apply Rbase_doubles_inegalites.Rabsolu_def3.
rewrite Rabs_mult.
replace (Rabs (B_powerRZ n)) with (B_powerRZ n).
replace (Rabs (/ x)) with (/ Rabs x).
elim H3; auto.
symmetry  in |- *; apply Rabs_Rinv.
auto.
symmetry  in |- *; apply Rabs_pos_eq.
unfold B_powerRZ in |- *.
apply powerRZ_le.
apply INR_B_non_nul.

unfold encadrement_bis in |- *.
pattern x in |- *.
apply Rind_complements.Rabsolu_not_0_ind; intros.
replace (sg x) with 1%Z; [ idtac | symmetry  in |- *; apply sg_pos; auto ].
rewrite Zmult_comm; rewrite Zmult_1_r.
replace x with (Rabs x).
auto.
apply Rabs_right.
apply Rgt_ge; auto.
replace (sg x) with (-1)%Z; [ idtac | symmetry  in |- *; apply sg_neg; auto ].
replace x with (- Rabs x).
rewrite Zmult_comm; rewrite <- Zopp_eq_mult_neg_1.
rewrite Ropp_Ropp_IZR.
RingReplace (- IZR p - 1) (- (IZR p + 1)).
RingReplace (- IZR p + 1) (- (IZR p - 1)).
rewrite <- Ropp_inv_permute.
rewrite Ropp_mult_distr_l_reverse.
apply Rlt_2_Ropp_r.
auto.
apply Rabs_no_R0.
auto.
apply Rmult_eq_reg_l with (-1).
RingReplace (-1 * - Rabs x) (Rabs x).
RingReplace (-1 * x) (- x).
apply Rabs_left; auto.
apply Rlt_not_eq.
lra.
apply Rlt_gt.
apply Rabs_pos_lt.
auto.
Qed.


Lemma Rabsolu_01 : forall x a : R, x <= a -> a < Rabs x -> x < 0.
Proof.
intros x a H.
unfold Rabs in |- *.
case (Rcase_abs x); intros.
auto.
lra.
Qed.

Hint Resolve Rabsolu_01: real.

Lemma Zsqrt_non_negative : forall z : Z, (0 <= z)%Z -> (0 <= Z.sqrt z)%Z.
Proof.
intros. apply Z.sqrt_nonneg.
Qed.

Lemma Zsqr_cond :
 forall z : Z,
 (0 <= z)%Z ->
 exists p : Z,
   (z = (p * p)%Z \/ z = (p * p + 1)%Z \/ z = (p * p - 1)%Z) \/
   (p * p < z < (p + 1) * (p + 1))%Z /\
   (p * p < z - 1 < (p + 1) * (p + 1))%Z /\
   (p * p < z + 1 < (p + 1) * (p + 1))%Z. 
Proof.
intros.
cut (z = 0%Z \/ z = 1%Z \/ (2 <= z)%Z); [ intuition | omega ].
exists 0%Z; omega.
exists 1%Z; omega.
generalize (Z.sqrt_spec z H); cbv zeta; intro.
generalize (Zsqrt_non_negative z H); intro.
set (r := Z.sqrt z) in *. unfold Z.succ in *.
cut
 ((z < r * r - 1)%Z \/
  z = (r * r - 1)%Z \/
  z = (r * r)%Z \/ z = (r * r + 1)%Z \/ (r * r + 1 < z)%Z);
 [ intuition | omega ].
exists (r - 1)%Z; right.
intuition; omega.
exists r; omega.
exists r; omega.
exists r; omega.
cut (z = ((r + 1) * (r + 1) - 1)%Z \/ (z < (r + 1) * (r + 1) - 1)%Z);
 [ intuition | omega ]. 
exists (r + 1)%Z; omega.
exists r; omega.
Qed.
