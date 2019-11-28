(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import Reals.
Require Import Rbase_inegalites.
Require Import Tactiques.
Require Import Psatz.

Lemma powerRZ_Zs :
 forall (r : R) (z : Z), r <> 0 -> powerRZ r (Z.succ z) = powerRZ r z * r. 
Proof.
intros.
unfold Z.succ in |- *.
replace (powerRZ r z * r) with (powerRZ r z * powerRZ r 1).
apply powerRZ_add.
auto.
apply Rmult_eq_compat_l.
simpl in |- *.
auto with real.
Qed.

Hint Resolve powerRZ_Zs: real. 


Lemma powerRZ_lt_1 :
 forall (r : R) (z : Z), 1 < r -> (0 < z)%Z -> 1 < powerRZ r z. 

Proof.
intros r z.
elim z.
intros.
inversion H0. 
2: intros; inversion H0.
unfold powerRZ in |- *.
intros.
apply Rlt_pow_R1.
auto.
apply lt_O_nat_of_P.
Qed.

Hint Resolve powerRZ_lt_1: real.


Lemma powerRZ_croissance :
 forall (r : R) (z z1 : Z), 1 < r -> (z < z1)%Z -> powerRZ r z < powerRZ r z1.

Proof.
intros.
RingReplace z1 (z1 - z + z)%Z. 
replace (powerRZ r (z1 - z + z)) with (powerRZ r (z1 - z) * powerRZ r z).
apply Rmult_lt_reg_l with (/ powerRZ r z).
apply Rinv_0_lt_compat.
apply powerRZ_lt.
apply Rlt_trans with 1.
lra.
exact H.
apply Rgt_lt.
rewrite Rmult_comm.
rewrite Rmult_assoc.
apply Rlt_gt.
rewrite Rmult_comm.
replace (powerRZ r z * / powerRZ r z) with 1.
rewrite Rmult_1_r.
apply powerRZ_lt_1.
exact H.
RingReplace (z1 - z)%Z (z1 + - z)%Z.
apply Zlt_left_lt.
exact H0.
apply Rinv_r_sym.
apply powerRZ_NOR. 
apply Rgt_not_eq.
apply Rlt_gt.
apply Rlt_trans with 1.
lra.
exact H.
symmetry  in |- *.
apply powerRZ_add.
apply Rgt_not_eq.
apply Rlt_gt.
apply Rlt_trans with 1.
lra.
exact H.

Qed.


Hint Resolve powerRZ_croissance: real.

Lemma powerRZ_lt_r :
 forall (r : R) (z : Z), 1 < r -> (1 < z)%Z -> r < powerRZ r z.  

Proof.
intros r z.
elim z.
intros.
inversion H0. 
2: intros; inversion H0.
intros.
pattern r at 1 in |- *.
replace r with (powerRZ r (Z.succ 0)). 
apply powerRZ_croissance.
exact H.
exact H0.
apply powerRZ_1.
Qed.

Hint Resolve powerRZ_lt_r: real.


Lemma powerRZ_trivial :
 forall (r : R) (z z1 : Z), z = z1 -> powerRZ r z = powerRZ r z1.

Proof.
intros.
rewrite H; auto.
Qed.

Hint Resolve powerRZ_trivial: real.


Lemma Rinv_powerRZ :
 forall (r : R) (z : Z), r <> 0 -> / powerRZ r z = powerRZ r (- z).

Proof.
intros.
apply Rmult_eq_reg_l with (powerRZ r z).
replace (powerRZ r z * / powerRZ r z) with 1.
replace (powerRZ r z * powerRZ r (- z)) with (powerRZ r (z + - z)).
rewrite Zplus_opp_r.
symmetry  in |- *; apply powerRZ_O.
apply powerRZ_add.
auto.
apply Rinv_r_sym.
apply powerRZ_NOR; auto.
apply powerRZ_NOR; auto.
Qed.

Hint Resolve Rinv_powerRZ: real.


Lemma derniere_chance : forall (r : R) (n : nat), 1 <= r -> 1 <= r ^ n.

Proof.
intros.
elim n.
simpl in |- *.
lra.
intros; simpl in |- *.
RingReplace 1 (1 * 1).
apply Rmult_le_compat; [ lra | lra | auto | auto ].
Qed.

Hint Resolve derniere_chance: real.


Lemma Rle_powerRZ :
 forall (r : R) (z z1 : Z),
 1 <= r -> (z <= z1)%Z -> powerRZ r z <= powerRZ r z1.

Proof.
intros.
apply Rmult_le_reg_l with (powerRZ r (- z)).
apply powerRZ_lt; apply Rlt_le_trans with 1.
lra.
auto.
replace (powerRZ r (- z) * powerRZ r z) with (powerRZ r (- z + z)).
replace (powerRZ r (- z) * powerRZ r z1) with (powerRZ r (- z + z1)).
rewrite Zplus_opp_l; rewrite powerRZ_O.
2: apply powerRZ_add; apply Rgt_not_eq; apply Rlt_gt; auto.
3: apply powerRZ_add; apply Rgt_not_eq; apply Rlt_gt; auto.
2: apply Rlt_le_trans with 1; lra; auto.
2: apply Rlt_le_trans with 1; lra; auto.
cut (0 <= - z + z1)%Z; [ idtac | rewrite Zplus_comm; apply Zle_left; auto ].
intro.
generalize H1.
case (- z + z1)%Z; clear H1; intros.
simpl in |- *; lra.
unfold powerRZ in |- *; apply derniere_chance; auto.
absurd (0 <= Zneg p)%Z; auto with zarith.
Qed.

Hint Resolve Rle_powerRZ: real.

Lemma powerRZ_lt_r_bis :
 forall (r : R) (z : Z), 1 <= r -> (1 <= z)%Z -> r <= powerRZ r z.  

Proof.
intros r z. 
case z.
intros.
absurd (1 <= 0)%Z; lia.
intros.
pattern r at 1 in |- *.
replace r with (powerRZ r (Z.succ 0)); [ idtac | apply powerRZ_1 ].
apply Rle_powerRZ. 
auto.
auto.
intros.
absurd (1 <= Zneg p)%Z.
auto with arith.
auto.
Qed.

Hint Resolve powerRZ_lt_r_bis: real.


Lemma powerRZ_Zopp :
 forall (r : R) (z : Z), r <> 0 -> 1 = powerRZ r z * powerRZ r (- z).

Proof.
intros.
replace (powerRZ r z * powerRZ r (- z)) with (powerRZ r (z + - z)).
rewrite Zplus_comm; rewrite Zplus_opp_l.
symmetry  in |- *; apply powerRZ_O.
apply powerRZ_add.
auto.
Qed.

Hint Resolve powerRZ_Zopp: real.


Lemma powerRZ_Rabsolu :
 forall (r : R) (z : Z), r <> 0 -> Rabs (powerRZ r z) = powerRZ (Rabs r) z.
Proof.
intros.
unfold powerRZ in |- *.
case z; intros.
apply Rabs_R1.
symmetry  in |- *; apply RPow_abs.
replace (Rabs (/ r ^ nat_of_P p)) with (/ Rabs (r ^ nat_of_P p)).
replace (Rabs (r ^ nat_of_P p)) with (Rabs r ^ nat_of_P p); auto.
apply RPow_abs.
symmetry  in |- *; apply Rabs_Rinv.
apply pow_nonzero; auto.
Qed.
Hint Resolve powerRZ_Rabsolu: real.
