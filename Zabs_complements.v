(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import ZArith.
Require Import Reals.


Lemma Zabs_mult : forall z1 z2 : Z, Z.abs (z1 * z2) = (Z.abs z1 * Z.abs z2)%Z.

Proof.
intros.
case z1.
simpl in |- *.
auto.
case z2.
simpl in |- *; auto.
simpl in |- *; auto.
simpl in |- *; auto.
simpl in |- *.
intros.
case z2.
auto with real. 
auto with real. 
auto with real.
Qed.

Hint Resolve Zabs_mult: real.


Lemma Zabs_O : forall z : Z, Z.abs z = 0%Z -> z = 0%Z.

Proof.
intro z.
case z; simpl in |- *; auto.
intros.
inversion H.
Qed.


Hint Resolve Zabs_O: real.


Lemma Zabs_lt_0 : forall z : Z, z <> 0%Z -> (Z.abs z > 0)%Z.

Proof.
intro.
unfold Z.abs in |- *.
case z.
intuition.
auto with zarith.
auto with zarith.
Qed.

Hint Resolve Zabs_lt_0: zarith.


Lemma Zabs_not_eq : forall z : Z, (Z.abs z > 0)%Z -> z <> 0%Z.
Proof.
intro.
unfold Z.abs in |- *.
case z; intro.
inversion H.
auto with zarith.
intro.
intuition.
inversion H0.
Qed.

Hint Resolve Zabs_not_eq: zarith.


Lemma Zabs_01 :
 forall x a : Z, (0 <= a)%Z -> (x <= a)%Z -> (a < Z.abs x)%Z -> (x < 0)%Z.
Proof.
intros x a H.
unfold Z.abs in |- *.
case x; intros.
omega.
omega.
red in |- *.
auto with zarith.
Qed.

Hint Resolve Zabs_01: zarith.