(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import ZArith.
Require Import Reals.
Require Import Tactiques.
Require Import Zarith_operations.

Lemma Zsqrt_nul : forall z : Z, z = 0%Z -> Z.sqrt z = 0%Z.
Proof.
intros.
rewrite H.
simpl in |- *.
auto.
Qed.

Hint Resolve Zsqrt_nul: zarith.


Lemma Zsqrt_0 : Z.sqrt 0 = 0%Z.
Proof.
auto.
Qed.

Hint Resolve Zsqrt_0: zarith.


Lemma Zsqrt_pos : forall z : Z, (0 <= Z.sqrt z)%Z.
Proof.
intros.
unfold Z.sqrt in |- *.
case z; auto with zarith.
Qed.

Hint Resolve Zsqrt_pos: reals.


Lemma Zsqrt_sqrt :
 forall z : Z, (0 <= z)%Z -> (IZR (Z.sqrt z) <= sqrt (IZR z))%R.
Proof.
intros.
apply Rsqr_incr_0_var.
rewrite Rsqr_sqrt.
unfold Rsqr in |- *.
rewrite <- mult_IZR.
apply IZR_le.
cut
 (Z.sqrt z * Z.sqrt z <= z <
  (Z.sqrt z + 1) * (Z.sqrt z + 1))%Z.
auto with zarith.
apply Z.sqrt_spec.
auto.
RingReplace 0%R (IZR 0).
apply IZR_le; auto.
apply sqrt_positivity.
RingReplace 0%R (IZR 0).
apply IZR_le; auto.
Qed.

Hint Resolve Zsqrt_sqrt: reals.


Lemma Zsqrt_sqrt_bis :
 forall z : Z, (0 <= z)%Z -> (sqrt (IZR z) < IZR (Z.sqrt z) + 1)%R.
Proof.
intros.
apply Rsqr_incrst_0.
rewrite Rsqr_sqrt.
unfold Rsqr in |- *.
replace (IZR (Z.sqrt z) + 1)%R with (IZR (Z.sqrt z + Z.succ 0)).
rewrite <- mult_IZR.
apply IZR_lt.
cut
 (Z.sqrt z * Z.sqrt z <= z <
  (Z.sqrt z + 1) * (Z.sqrt z + 1))%Z.
intuition.
apply Z.sqrt_spec.
auto.
change 1%R with (IZR (Z.succ 0)).
rewrite <- plus_IZR.
trivial.
change 0%R with (IZR 0).
apply IZR_le; auto.
apply sqrt_positivity.
change 0%R with (IZR 0).
apply IZR_le; auto.
change 0%R with (IZR 0); change 1%R with (IZR (Z.succ 0)).
rewrite <- plus_IZR; apply IZR_le.
replace (Z.sqrt z + Z.succ 0)%Z with (Z.succ (Z.sqrt z));
 [ idtac | omega ].
apply Zle_le_succ; apply Zsqrt_pos.
Qed.

Hint Resolve Zsqrt_sqrt_bis: reals.

