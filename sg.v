(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import Reals.
Require Import Psatz.
Require Import Rbase_inegalites.
Require Import Rabsolu_complements.
Require Import Tactiques.


Definition sg (x : R) : Z :=
  match total_order_T x 0 with
  | inleft (left _) => (-1)%Z
  | inleft (right _) => 0%Z
  | inright _ => 1%Z
  end.



Lemma sg_neg : forall r : R, r < 0 -> sg r = (-1)%Z.
Proof.
intros.
unfold sg in |- *.
case (total_order_T r 0).
simple destruct s; intro.
auto.
lra.
intro; lra.
Qed.
Hint Resolve sg_neg: real.


Lemma sg_pos : forall r : R, 0 < r -> sg r = 1%Z.
Proof.
intros.
unfold sg in |- *.
case (total_order_T r 0).
simple destruct s; intro.
lra.
lra.
intro; auto.
Qed.
Hint Resolve sg_pos: real. 


Lemma sg_nul : forall r : R, 0 = r -> sg r = 0%Z.
Proof.
intros.
unfold sg in |- *.
case (total_order_T r 0).
simple destruct s; intro.
lra.
auto.
intro; lra.
Qed.
Hint Resolve sg_nul: real. 


Lemma sg_mult : forall x y : R, sg (x * y) = (sg x * sg y)%Z.
Proof.
intros.
cut (0 < x \/ 0 = x \/ 0 > x); [ intro | apply Rtotal_order ].
elim H; clear H.
intro; replace (sg x) with 1%Z;
 [ rewrite Zmult_comm; rewrite Zmult_1_r
 | symmetry  in |- *; apply sg_pos; auto ]. 
cut (0 < y \/ 0 = y \/ 0 > y); [ intro | apply Rtotal_order ].
elim H0; clear H0.
intro; replace (sg y) with 1%Z;
 [ apply sg_pos | symmetry  in |- *; apply sg_pos; auto ].
apply Rmult_lt_0_compat; [ auto | auto ].
intro.
elim H0.
intro; replace (sg y) with 0%Z;
 [ apply sg_nul; symmetry  in |- *; apply Rmult_eq_0_compat; right; auto
 | symmetry  in |- *; apply sg_nul; auto ].
intro; replace (sg y) with (-1)%Z;
 [ apply sg_neg | symmetry  in |- *; apply sg_neg; auto ].
rewrite Rmult_comm; apply Rlt_sub_O; rewrite Rminus_0_l;
 rewrite <- Ropp_mult_distr_l_reverse; apply Rmult_lt_0_compat;
 [ auto with real | auto ].
intro.
elim H; clear H.
intro; replace (sg x) with 0%Z;
 [ rewrite Zmult_comm; rewrite <- Zmult_0_r_reverse; apply sg_nul;
    rewrite <- H; auto with real
 | symmetry  in |- *; apply sg_nul; auto ]. 
intro; replace (sg x) with (- (1))%Z;
 [ rewrite <- Zopp_mult_distr_l; rewrite Zmult_comm; rewrite Zmult_1_r
 | symmetry  in |- *; apply sg_neg; auto ].
cut (0 < y \/ 0 = y \/ 0 > y); [ intro | apply Rtotal_order ].
elim H0; clear H0.
intro; replace (sg y) with 1%Z;
 [ apply sg_neg | symmetry  in |- *; apply sg_pos; auto ].
apply Rlt_sub_O; rewrite Rminus_0_l; rewrite <- Ropp_mult_distr_l_reverse;
 apply Rmult_lt_0_compat; [ auto with real | auto ].
intro.
elim H0.
intro; replace (sg y) with 0%Z;
 [ apply sg_nul; symmetry  in |- *; apply Rmult_eq_0_compat; right; auto
 | symmetry  in |- *; apply sg_nul; auto ].
intro; replace (sg y) with (-1)%Z;
 [ apply sg_pos | symmetry  in |- *; apply sg_neg; auto ].
apply Rmult_lt_pos_bis; [ auto | auto ].
Qed.
Hint Resolve sg_mult: real. 


Lemma sg_mult_neg :
 forall x y : R, 0 < x /\ y < 0 \/ 0 < y /\ x < 0 -> (sg x * sg y)%Z = (-1)%Z.
Proof.
intros.
rewrite <- sg_mult.
elim H; intro.
apply sg_neg.
elim H0; intros.
apply Rmult_lt_reg_l with (/ x).
apply Rinv_0_lt_compat; auto.
rewrite <- Rmult_assoc.
replace (/ x * x) with 1.
rewrite Rmult_comm; rewrite Rmult_1_r.
rewrite Rmult_0_r; auto.
apply Rinv_l_sym; apply Rgt_not_eq; auto.
apply sg_neg.
elim H0.
intros.
rewrite Rmult_comm; apply Rmult_lt_reg_l with (/ y).
apply Rinv_0_lt_compat.
auto.
rewrite <- Rmult_assoc.
replace (/ y * y) with 1.
rewrite Rmult_comm; rewrite Rmult_1_r.
rewrite Rmult_0_r; auto.
apply Rinv_l_sym; apply Rgt_not_eq; auto.
Qed.
Hint Resolve sg_mult_neg: real.


Lemma plus_tard :
 forall x y : R,
 0 < Rabs x ->
 0 < Rabs y -> (sg x * sg y)%Z = (-1)%Z \/ (sg x * sg y)%Z = 1%Z.
Proof.
intros.
cut
 (0 < x * y \/ 0 > x * y -> (sg x * sg y)%Z = (-1)%Z \/ (sg x * sg y)%Z = 1%Z). 
intro; apply H1.
apply Rdichotomy.
apply Rabsolu_complements.Rabsolu_not_eq.
rewrite Rabs_mult.
apply Rmult_integral_contrapositive.
split;
 [ apply Rgt_not_eq; auto with real | apply Rgt_not_eq; auto with real ].
intros.
elim H1.
intro.
right.
rewrite <- sg_mult.
apply sg_pos; auto.
intro.
left.
rewrite <- sg_mult.
apply sg_neg; auto.
Qed.
Hint Resolve plus_tard: real.


Lemma sg_sqr : forall r : R, r <> 0 -> (sg r * sg r)%Z = 1%Z.
Proof.
intros.
cut (r <> 0 -> r < 0 \/ r > 0); [ intros | apply Rdichotomy ]. 
elim H0; clear H0.
intro; replace (sg r) with (-1)%Z;
 [ ring | symmetry  in |- *; apply sg_neg; auto ].
intro; replace (sg r) with 1%Z;
 [ ring | symmetry  in |- *; apply sg_pos; auto ].
auto.
Qed.
Hint Resolve sg_sqr: real.


Lemma Rabsolu_sg : forall r : R, IZR (sg r) * r = Rabs r.
Proof.
intro.
cut (0 < r \/ 0 = r \/ 0 > r); [ intro | apply Rtotal_order ].
elim H.
intro; replace (sg r) with 1%Z;
 [ idtac | symmetry  in |- *; apply sg_pos; auto ].
simpl in |- *; rewrite Rmult_1_l.
symmetry  in |- *; apply Rabs_right.
apply Rgt_ge; auto with real.
intro.
elim H0.
intro.
rewrite <- H1.
rewrite Rabs_R0.
apply Rmult_0_r.
intro; replace (sg r) with (-(1))%Z;
 [ idtac | symmetry; apply sg_neg; auto ].
rewrite Ropp_Ropp_IZR.
rewrite Ropp_mult_distr_l_reverse; rewrite Rmult_1_l.
symmetry; apply Rabs_left.
auto.
Qed.
Hint Resolve Rabsolu_sg: real.


Lemma Rabsolu_sg_bis : forall r : R, r = IZR (sg r) * Rabs r.
Proof.
intros.
cut (0 < r \/ 0 = r \/ 0 > r); [ intro | apply Rtotal_order ].
elim H.
intro; replace (sg r) with 1%Z;
 [ idtac | symmetry  in |- *; apply sg_pos; auto ].
simpl in |- *; rewrite Rmult_1_l.
symmetry  in |- *; apply Rabs_right.
apply Rgt_ge; auto with real.
intro.
elim H0.
intro.
rewrite <- H1.
rewrite Rabs_R0.
symmetry  in |- *; apply Rmult_0_r.
intro; replace (sg r) with (-(1))%Z;
 [ idtac | symmetry; apply sg_neg; auto ].
rewrite Ropp_Ropp_IZR.
rewrite Ropp_mult_distr_l_reverse; rewrite Rmult_1_l.
pattern r at 1 in |- *; RingReplace r (- - r).
apply Ropp_eq_compat; symmetry  in |- *; apply Rabs_left.
auto.
Qed.
Hint Resolve Rabsolu_sg_bis: real.
