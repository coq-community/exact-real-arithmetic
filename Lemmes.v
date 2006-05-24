(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Export definition.
Require Import Tactiques.
Require Import Fourier.
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

Hint Resolve powerRZ_INR_B_non_nul.

Lemma super_lemme : forall z z1 : Z, z = 0%Z -> 0%Z = (z1 * z)%Z.

Proof.
intros.
rewrite H; rewrite <- Zmult_0_r_reverse; auto.
Qed.

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
replace 1 with (IZR (Zsucc 0)).
apply IZR_le.
apply Zgt_le_succ.
apply Zlt_gt.
auto.
trivial.
rewrite Rmult_comm.
auto.
Qed.

Hint Resolve sg_Zsgn: real. 


Lemma sg_Zsgn_abs :
 forall (x : R) (xc : Reelc) (n : Z),
 encadrement (absolue_reelc xc) (Rabs x) -> (0 < Zabs (xc n))%Z -> 0 < Rabs x.  

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
replace 1 with (IZR (Zsucc 0)).
apply IZR_le.
apply Zgt_le_succ.
apply Zlt_gt.
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
replace (-1) with (IZR (Zpred 0)).
apply IZR_le.
apply Zlt_succ_le.
simpl in |- *.
apply Zgt_lt; auto.
trivial.
Qed.

Hint Resolve sg_Zsgn_2: real. 

Lemma le_pmax_n :
 forall (xc yc : Reelc) (n : Z), (1 <= p_max yc n + p_max xc n - n)%Z.

Proof.
intros.
apply Zle_add_compatibility.
unfold p_max in |- *.
apply Zle_trans with (Zeven.Zdiv2 (n + 2) + Zeven.Zdiv2 (n + 2))%Z;
 [ idtac | apply Zplus_le_compat; apply Zle_max_r ].
RingReplace (Zeven.Zdiv2 (n + 2) + Zeven.Zdiv2 (n + 2))%Z
 (2 * Zeven.Zdiv2 (n + 2))%Z.
cut ({Zeven.Zeven (n + 2)} + {Zeven.Zodd (n + 2)});
 [ idtac | apply Zeven.Zeven_odd_dec ].
intros.
elim H; clear H.
intro; replace (2 * Zeven.Zdiv2 (n + 2))%Z with (n + 2)%Z;
 [ idtac | apply Zeven.Zeven_div2; auto ]. 
rewrite Zplus_comm; apply Zplus_le_compat_l.
omega.
cut ((n + 2 <= 0)%Z \/ (0 <= n + 2)%Z); [ idtac | apply Zlt_le_ind ].
intro; elim H; clear H.
intros; rewrite Zplus_comm; apply Zplus_le_reg_r with (-1)%Z.
RingReplace (2 * Zeven.Zdiv2 (n + 2) + -1)%Z (2 * Zeven.Zdiv2 (n + 2) - 1)%Z;
 RingReplace (n + 1 + -1)%Z n.
replace (2 * Zeven.Zdiv2 (n + 2) - 1)%Z with (n + 2)%Z;
 [ idtac | apply Zodd_div2_bis; auto ]. 
pattern n at 1 in |- *; RingReplace n (n + 0)%Z.
apply Zplus_le_compat_l.
omega.
intros; rewrite Zplus_comm; apply Zplus_le_reg_r with 1%Z.
replace (2 * Zeven.Zdiv2 (n + 2) + 1)%Z with (n + 2)%Z;
 [ idtac | apply Zeven.Zodd_div2; auto ]. 
rewrite <- Zplus_assoc.
apply Zplus_le_compat_l.
omega.
apply Zle_ge; auto.
Qed.



Lemma Zsgn_sg :
 forall (X : R) (XC YC : Reelc) (n : Z),
 encadrement XC X ->
 (0 < Zabs (XC (p_max YC n)))%Z -> Zsgn (XC (p_max YC n)) = sg X.
intros X XC YC n H.
intro.
pattern (XC (p_max YC n)) in |- *.
apply Zabs_pos_ind.
intros; replace (Zsgn (XC (p_max YC n))) with 1%Z;
 [ symmetry  in |- *; apply sg_pos; apply sg_Zsgn with XC (p_max YC n);
    [ auto | auto ]
 | symmetry  in |- *; apply Zsgn_pos; auto ].
intros; replace (Zsgn (XC (p_max YC n))) with (-1)%Z;
 [ symmetry  in |- *; apply sg_neg; apply sg_Zsgn_2 with XC (p_max YC n);
    [ auto | apply Zlt_gt; auto ]
 | symmetry  in |- *; apply Zsgn_neg; auto ].
auto.
Qed.

Hint Resolve Zsgn_sg: real.


Lemma Zsgn_sg_bis :
 forall (x : R) (xc : Reelc) (n : Z),
 encadrement xc x -> (0 < Zabs (xc n))%Z -> Zsgn (xc n) = sg x.
intros x xc n H.
intro.
pattern (xc n) in |- *.
apply Zabs_pos_ind.
intros; replace (Zsgn (xc n)) with 1%Z;
 [ symmetry  in |- *; apply sg_pos; apply sg_Zsgn with xc n; [ auto | auto ]
 | symmetry  in |- *; apply Zsgn_pos; auto ].
intros; replace (Zsgn (xc n)) with (-1)%Z;
 [ symmetry  in |- *; apply sg_neg; apply sg_Zsgn_2 with xc n;
    [ auto | apply Zlt_gt; auto ]
 | symmetry  in |- *; apply Zsgn_neg; auto ].
auto.
Qed.

Hint Resolve Zsgn_sg_bis: real.


Lemma Zsgn_to_sg :
 forall (xc yc : Reelc) (x y : R) (n : Z),
 encadrement xc x ->
 encadrement yc y ->
 (0 < Zabs (xc (p_max yc n)))%Z ->
 IZR
   (Zsgn (xc (p_max yc n)) * Zsgn (yc (p_max xc n)) *
    gauss_z_sur_B_pow (1 + Zabs (xc (p_max yc n) * yc (p_max xc n)))
      (p_max yc n + p_max xc n - n)) =
 IZR
   (sg x * sg y *
    gauss_z_sur_B_pow (1 + Zabs (xc (p_max yc n) * yc (p_max xc n)))
      (p_max yc n + p_max xc n - n)).

Proof.
intros.
apply IZR_trivial.
pattern (yc (p_max xc n)) in |- *.
apply Zabs_ind_4.
intro.
rewrite H2; rewrite <- Zmult_0_r_reverse; rewrite Zmult_comm;
 do 2 rewrite <- Zmult_0_r_reverse.
simpl in |- *.
apply super_lemme.
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
fourier.
apply Rinv_0_lt_compat; unfold B_powerRZ in |- *; apply powerRZ_lt;
 apply INR_B_non_nul.
field; apply Rgt_not_eq; fourier.
RingReplace (IZR 1) 1.
rewrite Rmult_comm; rewrite Rmult_1_r.
apply Rlt_add_compatibility3.
replace (1 - 1 * / 2) with (1 * / 2).
rewrite Rmult_comm; rewrite Rmult_1_r.
apply Rinv_1_lt_contravar.
fourier.
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
field; apply Rgt_not_eq; fourier.
intro.
replace (Zsgn (xc (p_max yc n))) with (sg x).
replace (Zsgn (yc (p_max xc n))) with (sg y).
auto.
symmetry  in |- *; apply Zsgn_sg; auto; auto.
symmetry  in |- *; apply Zsgn_sg; auto; auto.
Qed.

Hint Resolve Zsgn_to_sg: real. 




