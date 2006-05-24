(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import Reals.
Require Import sg.

Lemma sg_ind :
 forall (P : R -> Prop) (r : R),
 (r = 0%R -> P r) -> ((0 < r)%R -> P r) -> ((r < 0)%R -> P r) -> P r. 

Proof.
intros.
cut ((0 < r)%R \/ 0%R = r \/ (0 > r)%R).
intros.
elim H2.
auto.
intros.
elim H3.
auto.
auto.
apply Rtotal_order.
Qed.


Lemma sg_ind_bis :
 forall (P : R -> R -> Prop) (x y : R),
 (0 < Rabs x)%R ->
 (0 < Rabs y)%R ->
 ((sg x * sg y)%Z = (-1)%Z -> P x y) ->
 ((sg x * sg y)%Z = 1%Z -> P x y) -> P x y.

Proof.
intros.
cut
 ((0 < Rabs x)%R ->
  (0 < Rabs y)%R -> (sg x * sg y)%Z = (-1)%Z \/ (sg x * sg y)%Z = 1%Z).
intros.
elim H3.
auto.
auto.
auto.
auto.
apply plus_tard.
Qed.


Lemma Rind_eq_or :
 forall (P : R -> R -> Prop) (x y : R),
 (x = 0%R \/ y = 0%R -> P x y) -> (x <> 0%R /\ y <> 0%R -> P x y) -> P x y.

Proof.
intros.
cut ((x = 0%R \/ y = 0%R) \/ x <> 0%R /\ y <> 0%R).
intro.
elim H1.
auto.
intro.
elim H2; auto.
case (Req_dec x 0); case (Req_dec y 0); auto.  
Qed.


Lemma Rabsolu_not_0_ind :
 forall (P : R -> Prop) (r : R),
 ((r > 0)%R -> P r) -> ((0 > r)%R -> P r) -> (Rabs r > 0)%R -> P r.
Proof.                      
intros.
cut ((Rabs r > 0)%R -> (r < 0)%R \/ (r > 0)%R).
intros.
elim H2; auto.
unfold Rabs in |- *.
case (Rcase_abs r); auto.
Qed.
