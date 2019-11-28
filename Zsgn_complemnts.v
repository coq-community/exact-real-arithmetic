(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import ZArith.
Require Import Reals.

Lemma Zsgn_mult : forall z z1 : Z, (Z.sgn z * Z.sgn z1)%Z = Z.sgn (z * z1). 

Proof.
intros.
case z; case z1; auto with real.
Qed.

Hint Resolve Zsgn_mult: real.



Lemma Zsgn_trivial : forall z z1 : Z, z = z1 -> Z.sgn z = Z.sgn z1.

Proof.
intros.
rewrite H; auto.
Qed.

Hint Resolve Zsgn_trivial: real.

Lemma Zsgn_neg : forall z : Z, (z < 0)%Z -> Z.sgn z = (-1)%Z.

Proof.
intro.
case z.
intro.
inversion H.
intros.
inversion H.
auto with zarith.
Qed.

Hint Resolve Zsgn_neg: real.


Lemma Zsgn_pos : forall z : Z, (0 < z)%Z -> Z.sgn z = 1%Z.

Proof.
intro.
case z.
intro.
inversion H.
auto with zarith.
intros.
inversion H.
Qed.

Hint Resolve Zsgn_pos: real. 


Lemma Zsgn_nul : forall z : Z, 0%Z = z -> Z.sgn z = 0%Z.

Proof.
intros.
rewrite <- H; auto with zarith.
Qed.

Hint Resolve Zsgn_nul: real. 


