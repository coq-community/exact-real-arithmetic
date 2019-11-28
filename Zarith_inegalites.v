(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import ZArith.

Lemma Zlt_le_Zs : forall z z1 : Z, (Z.succ z <= z1)%Z -> (z < z1)%Z.

Proof. 
intros.
apply Z.lt_le_trans with (Z.succ z).
apply Zlt_succ.
auto.
Qed.

Hint Resolve Zlt_le_Zs: real.


Lemma Zle_add_compatibility :
 forall z z1 z2 : Z, (z + z1 <= z2)%Z -> (z <= z2 - z1)%Z.

Proof.
intros.
apply Zplus_le_reg_l with z1. 
rewrite Zplus_minus.
rewrite Zplus_comm; auto.
Qed.

Hint Resolve Zle_add_compatibility: real.



