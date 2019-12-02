(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import definition.
Require Import Tactiques.
Require Import Axiomes.
Require Import Lemmes_generaux.
Require Import Lemmes.
Require Import Rbase_doubles_inegalites.


Lemma lemme_oppose :
 forall (x : R) (xc : Reelc),
 encadrement xc x -> encadrement (oppose_reelc xc) (- x).

Proof.
intros x xc.
unfold encadrement in |- *.
unfold oppose_reelc in |- *.
intros.
generalize (H n); clear H; intro H.
rewrite Ropp_mult_distr_l_reverse.
rewrite <- Ropp_minus_distr'.
rewrite Ropp_Ropp_IZR.
RingReplace (1 - - IZR (xc n))%R (IZR (xc n) + 1)%R.
RingReplace (- IZR (xc n) + 1)%R (- (IZR (xc n) - 1))%R.
apply Rlt_2_Ropp_r.
assumption.
Qed.
