(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import Reals.

Lemma Rsub_sym : forall x y : R, (x - y)%R = (- y + x)%R.
Proof.
intros; ring.
Qed.
Hint Resolve Rsub_sym: real.


Lemma Rmult_1_r : forall r x : R, 1%R = x -> r = (x * r)%R.
Proof.
intros; rewrite <- H; ring.
Qed.
Hint Resolve Rbase_operations.Rmult_1_r: real.


Lemma Rmult_1_r2 : forall r x : R, 1%R = x -> r = (r * x)%R.
Proof.
intros; rewrite <- H; ring.
Qed.
Hint Resolve Rmult_1_r2: real.


Lemma Rplus_plus_r1 : forall r r1 r2 : R, r1 = r2 -> (r1 + r)%R = (r2 + r)%R.
Proof.
intros; auto with real.
Qed.
Hint Resolve Rplus_plus_r1: real.


Lemma Rplus_plus_plus :
 forall r1 r2 r3 r4 : R, r1 = r3 -> r2 = r4 -> (r1 + r2)%R = (r3 + r4)%R.
Proof.
intros; rewrite H; rewrite H0; auto.
Qed.
Hint Resolve Rplus_plus_plus: real.


Lemma Rplus_Rsub_distr : forall x y z : R, (x + y - z)%R = (y + (x - z))%R.
Proof.
intros; ring.
Qed.
Hint Resolve Rplus_Rsub_distr: real.


Lemma eq_2_minus : forall r r1 : R, r = (- r1 * 2)%R -> (- r1)%R = (r + r1)%R.
Proof.
intros; rewrite H; ring.
Qed.
Hint Resolve eq_2_minus: real.


Lemma Rmult_mult_mult :
 forall r1 r2 r3 r4 : R, (r1 * r2 * (r3 * r4))%R = (r3 * r1 * (r4 * r2))%R.
Proof.
intros; ring.
Qed.
Hint Resolve Rmult_mult_mult: real.


Lemma Rmult_5 :
 forall r1 r2 r3 r4 r5 : R,
 (r1 * r2 * (r3 * r4 * r5))%R = (r1 * r3 * (r2 * r4) * r5)%R.
Proof.
intros; ring.
Qed.
Hint Resolve Rmult_5: real.


Lemma Rplus_plus_2 :
 forall r1 r2 r3 r4 : R, (r1 + r2 + r3 + r4)%R = (r1 + r3 + (r2 + r4))%R.
Proof.
intros; ring.
Qed.
Hint Resolve Rplus_plus_2: real. 


Lemma Rmult_1l : forall r : R, (1 * r)%R = r.
Proof.
intro; ring.
Qed.
Hint Resolve Rmult_1l: real.


Lemma Rinv_Rmult_bis :
 forall r1 r2 r3 r4 : R,
 (0 < r1)%R ->
 (0 < r2)%R -> (r3 * r2)%R = (r1 * r4)%R -> (r3 * / r1)%R = (r4 * / r2)%R.
Proof.
intros.
apply Rmult_eq_reg_l with r1;
 [ rewrite Rmult_comm; rewrite Rmult_assoc
 | apply Rgt_not_eq; auto with real ].
replace (/ r1 * r1)%R with 1%R;
 [ rewrite RIneq.Rmult_1_r
 | apply Rinv_l_sym; apply Rgt_not_eq; auto with real ].
rewrite <- Rmult_assoc.
apply Rmult_eq_reg_l with r2;
 [ rewrite Rmult_comm; symmetry  in |- *; rewrite Rmult_comm;
    rewrite Rmult_assoc
 | apply Rgt_not_eq; auto with real ].
replace (/ r2 * r2)%R with 1%R;
 [ rewrite RIneq.Rmult_1_r
 | apply Rinv_l_sym; apply Rgt_not_eq; auto with real ].
auto.
Qed.
Hint Resolve Rinv_Rmult_bis: real.



