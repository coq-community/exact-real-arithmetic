(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Export definition.
Require Import Tactiques.
Require Import Psatz.
Require Import Axiomes.
Require Import sg.
Require Import Zarith_operations.
Require Import Rbase_inegalites.
Require Import Zind_complements.
Require Import Zsgn_complemnts.
Require Import Rbase_doubles_inegalites.
Require Import Zarith_inegalites.
Require Import Zdec_complements.
Require Import Zdiv2_complements.
Require Import powerRZ_complements.

Lemma INR_B_non_nul : 0 < INR B.

Proof.
intros.
apply lt_INR_0.
generalize B_sup_4.
omega.
Qed.

Hint Resolve INR_B_non_nul: real.

Lemma powerRZ_INR_B_non_nul : forall z : Z, powerRZ (INR B) z <> 0.

Proof.
intros.
apply Rgt_not_eq.
apply Rlt_gt.
apply powerRZ_lt.
apply INR_B_non_nul.
Qed.

Hint Resolve powerRZ_INR_B_non_nul : real.

Lemma sg_Zsgn :
 forall (x : R) (xc : Reelc) (n : Z),
 encadrement xc x -> (0 < xc n)%Z -> 0 < x.  

Proof.
intros.
generalize (H n).
intros.
decompose [and] H1.
apply Rmult_lt_reg_l with (B_powerRZ n).
unfold B_powerRZ in |- *.
apply powerRZ_lt.
apply lt_INR_0.
generalize B_sup_4.
omega.
rewrite Rmult_0_r.
RingReplace 0 (1 - 1).
apply Rle_lt_trans with (IZR (xc n) - 1).
apply Rle_add_compatibility.
rewrite Rplus_comm.
RingReplace (1 + (1 - 1)) 1.
replace 1 with (IZR (Z.succ 0)).
apply IZR_le.
apply Zgt_le_succ.
apply Z.lt_gt.
auto.
trivial.
rewrite Rmult_comm.
auto.
Qed.

Hint Resolve sg_Zsgn: real. 


Lemma sg_Zsgn_abs :
 forall (x : R) (xc : Reelc) (n : Z),
 encadrement (absolue_reelc xc) (Rabs x) -> (0 < Z.abs (xc n))%Z -> 0 < Rabs x.  

Proof.
intros.
generalize (H n).
intros.
decompose [and] H1.
apply Rmult_lt_reg_l with (B_powerRZ n).
unfold B_powerRZ in |- *.
apply powerRZ_lt.
apply lt_INR_0.
generalize B_sup_4.
omega.
rewrite Rmult_0_r.
RingReplace 0 (1 - 1).
apply Rle_lt_trans with (IZR (absolue_reelc xc n) - 1).
apply Rle_add_compatibility.
rewrite Rplus_comm.
RingReplace (1 + (1 - 1)) 1.
replace 1 with (IZR (Z.succ 0)).
apply IZR_le.
apply Zgt_le_succ.
apply Z.lt_gt.
auto.
trivial.
rewrite Rmult_comm.
auto.
Qed.

Hint Resolve sg_Zsgn_abs: real. 


Lemma sg_Zsgn_2 :
 forall (x : R) (xc : Reelc) (n : Z),
 encadrement xc x -> (0 > xc n)%Z -> 0 > x.  

Proof.
intros.
generalize (H n); intros.
decompose [and] H1.
apply Rlt_gt; apply Rmult_lt_reg_l with (B_powerRZ n);
 [ unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul | idtac ].
rewrite Rmult_0_r.
apply Rlt_le_trans with (IZR (xc n) + 1).
rewrite Rmult_comm; auto.
rewrite Rplus_comm; apply Rplus_le_reg_l with (-1).
RingReplace (-1 + (1 + IZR (xc n))) (IZR (xc n)); RingReplace (-1 + 0) (-1).
replace (-1) with (IZR (Z.pred 0)).
apply IZR_le.
apply Zlt_succ_le.
simpl in |- *.
apply Z.gt_lt; auto.
trivial.
Qed.

Hint Resolve sg_Zsgn_2: real. 

Lemma le_pmax_n :
 forall (xc yc : Reelc) (n : Z), (1 <= p_max yc n + p_max xc n - n)%Z.

Proof.
intros.
apply Zle_add_compatibility.
unfold p_max in |- *.
apply Z.le_trans with (Z.quot2 (n + 2) + Z.quot2 (n + 2))%Z;
 [ idtac | apply Zplus_le_compat; apply Zle_max_r ].
RingReplace (Z.quot2 (n + 2) + Z.quot2 (n + 2))%Z
 (2 * Z.quot2 (n + 2))%Z.
cut ({Zeven.Zeven (n + 2)} + {Zeven.Zodd (n + 2)});
 [ idtac | apply Zeven.Zeven_odd_dec ].
intros.
elim H; clear H.
intro; replace (2 * Z.quot2 (n + 2))%Z with (n + 2)%Z;
 [ idtac | apply Zeven.Zeven_quot2; auto ]. 
rewrite Zplus_comm; apply Zplus_le_compat_l.
omega.
cut ((n + 2 <= 0)%Z \/ (0 <= n + 2)%Z); [ idtac | apply Zlt_le_ind ].
intro; elim H; clear H.
intros; rewrite Zplus_comm; apply Zplus_le_reg_r with (-1)%Z.
RingReplace (2 * Z.quot2 (n + 2) + -1)%Z (2 * Z.quot2 (n + 2) - 1)%Z;
 RingReplace (n + 1 + -1)%Z n.
replace (2 * Z.quot2 (n + 2) - 1)%Z with (n + 2)%Z;
 [ idtac | apply Zodd_quot2_bis; auto ]. 
pattern n at 1 in |- *; RingReplace n (n + 0)%Z.
apply Zplus_le_compat_l.
omega.
intros; rewrite Zplus_comm; apply Zplus_le_reg_r with 1%Z.
replace (2 * Z.quot2 (n + 2) + 1)%Z with (n + 2)%Z;
 [ idtac | apply Zeven.Zodd_quot2; auto ]. 
rewrite <- Zplus_assoc.
apply Zplus_le_compat_l.
omega.
apply Z.le_ge; auto.
Qed.



Lemma Zsgn_sg :
 forall (X : R) (XC YC : Reelc) (n : Z),
 encadrement XC X ->
 (0 < Z.abs (XC (p_max YC n)))%Z -> Z.sgn (XC (p_max YC n)) = sg X.
intros X XC YC n H.
intro.
pattern (XC (p_max YC n)) in |- *.
apply Zabs_pos_ind.
intros; replace (Z.sgn (XC (p_max YC n))) with 1%Z;
 [ symmetry  in |- *; apply sg_pos; apply sg_Zsgn with XC (p_max YC n);
    [ auto | auto ]
 | symmetry  in |- *; apply Zsgn_pos; auto ].
intros; replace (Z.sgn (XC (p_max YC n))) with (-1)%Z;
 [ symmetry  in |- *; apply sg_neg; apply sg_Zsgn_2 with XC (p_max YC n);
    [ auto | apply Z.lt_gt; auto ]
 | symmetry  in |- *; apply Zsgn_neg; auto ].
auto.
Qed.

Hint Resolve Zsgn_sg: real.


Lemma Zsgn_sg_bis :
 forall (x : R) (xc : Reelc) (n : Z),
 encadrement xc x -> (0 < Z.abs (xc n))%Z -> Z.sgn (xc n) = sg x.
intros x xc n H.
intro.
pattern (xc n) in |- *.
apply Zabs_pos_ind.
intros; replace (Z.sgn (xc n)) with 1%Z;
 [ symmetry  in |- *; apply sg_pos; apply sg_Zsgn with xc n; [ auto | auto ]
 | symmetry  in |- *; apply Zsgn_pos; auto ].
intros; replace (Z.sgn (xc n)) with (-1)%Z;
 [ symmetry  in |- *; apply sg_neg; apply sg_Zsgn_2 with xc n;
    [ auto | apply Z.lt_gt; auto ]
 | symmetry  in |- *; apply Zsgn_neg; auto ].
auto.
Qed.

Hint Resolve Zsgn_sg_bis: real.


Lemma Zsgn_to_sg :
 forall (xc yc : Reelc) (x y : R) (n : Z),
 encadrement xc x ->
 encadrement yc y ->
 (0 < Z.abs (xc (p_max yc n)))%Z ->
 IZR
   (Z.sgn (xc (p_max yc n)) * Z.sgn (yc (p_max xc n)) *
    gauss_z_sur_B_pow (1 + Z.abs (xc (p_max yc n) * yc (p_max xc n)))
      (p_max yc n + p_max xc n - n)) =
 IZR
   (sg x * sg y *
    gauss_z_sur_B_pow (1 + Z.abs (xc (p_max yc n) * yc (p_max xc n)))
      (p_max yc n + p_max xc n - n)).

Proof.
intros.
apply IZR_trivial.
pattern (yc (p_max xc n)).
apply Zabs_ind_4.
intro.
rewrite H2; rewrite <- Zmult_0_r_reverse; rewrite Zmult_comm;
 do 2 rewrite <- Zmult_0_r_reverse.
simpl in |- *.
set (U := gauss_z_sur_B_pow _ _); replace U with 0%Z; try ring.
symmetry.
apply one_IZR_lt1.
apply
 Rle_lt_2_lt
  with
    (IZR 1 * / B_powerRZ (p_max yc n + p_max xc n - n) - 1 * / 2)
    (IZR 1 * / B_powerRZ (p_max yc n + p_max xc n - n) + 1 * / 2).                       
generalize (gauss_correct_pow 1 (p_max yc n + p_max xc n - n)).
tauto.
RingReplace (IZR 1) 1.
rewrite Rmult_comm; rewrite Rmult_1_r.
apply Rlt_sub_compatibility.
replace (-1 + 1 * / 2) with (-1 * / 2).
apply Rlt_trans with 0.
lra.
apply Rinv_0_lt_compat; unfold B_powerRZ in |- *; apply powerRZ_lt;
 apply INR_B_non_nul.
field; apply Rgt_not_eq; lra.
RingReplace (IZR 1) 1.
rewrite Rmult_comm; rewrite Rmult_1_r.
apply Rlt_add_compatibility3.
replace (1 - 1 * / 2) with (1 * / 2).
rewrite Rmult_comm; rewrite Rmult_1_r.
apply Rinv_1_lt_contravar.
lra.
unfold B_powerRZ in |- *.
apply Rlt_le_trans with (INR B).
RingReplace 2 (INR 2).
apply lt_INR.
generalize B_sup_4.
omega.
apply powerRZ_lt_r_bis.
RingReplace 1 (INR 1).
apply le_INR.
generalize B_sup_4.
omega.
apply le_pmax_n. 
field; apply Rgt_not_eq; lra.
intro.
replace (Z.sgn (xc (p_max yc n))) with (sg x).
replace (Z.sgn (yc (p_max xc n))) with (sg y).
auto.
symmetry; apply Zsgn_sg; auto; auto.
symmetry; apply Zsgn_sg; auto; auto.
Qed.

Hint Resolve Zsgn_to_sg: real. 




