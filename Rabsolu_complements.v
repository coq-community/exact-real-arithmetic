(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import Reals.
Require Import Tactiques.
Require Import Rbase_doubles_inegalites.

Lemma Rabsolu_def2_moins : forall r r1 : R, (Rabs r < r1)%R -> (- r1 < r)%R.
Proof.
intros.
apply proj1 with (r < r1)%R.
apply penible; apply Rabs_def2; auto.
Qed.
Hint Resolve Rabsolu_complements.Rabsolu_def2_moins: real.


Lemma Rabsolu_not_eq : forall x : R, Rabs x <> 0%R -> 0%R <> x.
Proof.
intros.
elim (Req_dec x 0); intro.
rewrite H0 in H.
rewrite Rabs_R0 in H.
rewrite H0; auto.
auto with real.
Qed.
Hint Resolve Rabsolu_complements.Rabsolu_not_eq: real.


Lemma Rabsolu_def4 : forall x a : R, (- a < x < a)%R -> (Rabs x < a)%R.
Proof.
intros.
apply Rabs_def1; elim H; auto.
Qed.
Hint Resolve Rabsolu_complements.Rabsolu_def4: real.




