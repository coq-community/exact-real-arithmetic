(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import ZArith.
Require Import Reals.

Lemma Zplus_INZ :
 forall n m : nat, (Z_of_nat n + Z_of_nat m)%Z = Z_of_nat (n + m).
Proof.
intros.
case n; case m; simpl in |- *; trivial.
intro n0; rewrite <- plus_n_O; trivial.
simple induction n1; simpl in |- *; intros.
rewrite Pplus_one_succ_l; trivial.
rewrite Pplus_comm.
rewrite Pplus_succ_permute_r.
rewrite Pplus_comm.
injection H.
intro eq; rewrite eq; trivial.
Qed.
Hint Resolve Zplus_INZ: zarith.


Lemma IZR_eq_O : forall z : Z, z = 0%Z -> IZR z = 0%R.
Proof.
intros.
rewrite H; simpl in |- *; auto.
Qed.
Hint Resolve IZR_eq_O: real.
 

Lemma IZR_trivial : forall z z1 : Z, z = z1 -> IZR z = IZR z1. 
Proof.
intros.
rewrite H; auto.
Qed.
Hint Resolve IZR_trivial: real. 


Lemma Zle_not_lt : forall z z1 : Z, (z1 <= z)%Z -> z <> z1 -> (z1 < z)%Z.
Proof.
intros z z1.
auto with zarith.
Qed.
Hint Resolve Zle_not_lt: zarith.


Lemma Zle_2_Zs :
 forall z z1 : Z, (z1 <= z <= Z.succ z1)%Z -> z = z1 \/ z = Z.succ z1.
Proof.
intros z z1 h. omega.
Qed.
Hint Resolve Zle_2_Zs: zarith.


Lemma Zle_2_Zs_dec :
 forall z z1 : Z, (z1 <= z <= Z.succ z1)%Z -> {z = z1} + {z = Z.succ z1}.
Proof.
intros z z1 h. 
elim (Z_lt_ge_dec z (Z.succ z1)); intro.
left; omega.
right; omega.
Qed.
Hint Resolve Zle_2_Zs_dec: zarith.