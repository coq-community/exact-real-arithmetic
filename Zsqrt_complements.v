(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import Zsqrt.
Require Import Reals.
Require Import Tactiques.
Require Import Zarith_operations.

Lemma Zsqrt_nul : forall z : Z, z = 0%Z -> Zsqrt_plain z = 0%Z.
Proof.
intros.
rewrite H.
simpl in |- *.
auto.
Qed.

Hint Resolve Zsqrt_nul: zarith.


Lemma Zsqrt_0 : Zsqrt_plain 0 = 0%Z.
Proof.
auto.
Qed.

Hint Resolve Zsqrt_0: zarith.


Lemma Zsqrt_plain_pos : forall z : Z, (0 <= Zsqrt_plain z)%Z.
Proof.
intros.
unfold Zsqrt_plain in |- *.
case z; intros; try omega.
unfold Zsqrt in |- *.
case (sqrtrempos p).
intros.
omega.
Qed.

Hint Resolve Zsqrt_plain_pos: reals.


Lemma Zsqrt_sqrt :
 forall z : Z, (0 <= z)%Z -> (IZR (Zsqrt_plain z) <= sqrt (IZR z))%R.
Proof.
intros.
apply Rsqr_incr_0_var.
rewrite Rsqr_sqrt.
unfold Rsqr in |- *.
rewrite <- mult_IZR.
apply IZR_le.
cut
 (Zsqrt_plain z * Zsqrt_plain z <= z <
  (Zsqrt_plain z + 1) * (Zsqrt_plain z + 1))%Z.
auto with zarith.
apply Zsqrt_interval.
auto.
RingReplace 0%R (IZR 0).
apply IZR_le; auto.
apply sqrt_positivity.
RingReplace 0%R (IZR 0).
apply IZR_le; auto.
Qed.

Hint Resolve Zsqrt_sqrt: reals.


Lemma Zsqrt_sqrt_bis :
 forall z : Z, (0 <= z)%Z -> (sqrt (IZR z) < IZR (Zsqrt_plain z) + 1)%R.
Proof.
intros.
apply Rsqr_incrst_0.
rewrite Rsqr_sqrt.
unfold Rsqr in |- *.
replace (IZR (Zsqrt_plain z) + 1)%R with (IZR (Zsqrt_plain z + Zsucc 0)).
rewrite <- mult_IZR.
apply IZR_lt.
cut
 (Zsqrt_plain z * Zsqrt_plain z <= z <
  (Zsqrt_plain z + 1) * (Zsqrt_plain z + 1))%Z.
intuition.
apply Zsqrt_interval.
auto.
change 1%R with (IZR (Zsucc 0)).
rewrite <- plus_IZR.
trivial.
change 0%R with (IZR 0).
apply IZR_le; auto.
apply sqrt_positivity.
change 0%R with (IZR 0).
apply IZR_le; auto.
change 0%R with (IZR 0); change 1%R with (IZR (Zsucc 0)).
rewrite <- plus_IZR; apply IZR_le.
replace (Zsqrt_plain z + Zsucc 0)%Z with (Zsucc (Zsqrt_plain z));
 [ idtac | omega ].
apply Zle_le_succ; apply Zsqrt_plain_pos.
Qed.

Hint Resolve Zsqrt_sqrt_bis: reals.

