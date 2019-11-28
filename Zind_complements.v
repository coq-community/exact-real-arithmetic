(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import Reals.
Require Import Zdec_complements.
Require Import definition.
Require Import Zabs_complements.
Require Import Tactiques.

Lemma Zabs_ind_bis :
 forall (P : Z -> Z -> Prop) (x y : Z),
 (x = 0%Z /\ y = 0%Z -> P x y) ->
 ((0 < Z.abs x)%Z \/ (0 < Z.abs y)%Z -> P x y) -> P x y. 

Proof.
intros.
cut ({x = 0%Z /\ y = 0%Z} + {(0 < Z.abs x)%Z \/ (0 < Z.abs y)%Z}).
intros.
elim H1.
auto.
auto.
apply Zabs_Zle_2.
Qed.


Lemma Zabs_ind_ter :
 forall (P1 : Reelc -> Reelc -> Prop) (P : R -> R -> Reelc -> Reelc -> Prop)
   (x y : R) (xc yc : Reelc),
 (P y x yc xc -> P x y xc yc) ->
 (forall (x y : R) (xc yc : Reelc), P1 xc yc -> P x y xc yc) ->
 P1 xc yc \/ P1 yc xc -> P x y xc yc. 

Proof.
intros.
elim H1.
generalize (H0 x y xc yc).
auto.
intro.
apply H.
generalize H2.
generalize (H0 y x yc xc).
auto.
Qed.

Lemma Zabs_ind_4 :
 forall (P : Z -> Prop) (x : Z),
 (x = 0%Z -> P x) -> ((0 < Z.abs x)%Z -> P x) -> P x. 

Proof.
intros.
cut ({x = 0%Z} + {(0 < Z.abs x)%Z}). 
intros.
elim H1.
auto.
auto.
cut ({Z.abs x = 0%Z} + {(0 < Z.abs x)%Z}).
intro.
elim H1.
intro.
left.
apply Zabs_O.
auto.
intro; right; auto.
apply Zabs_Zle_1.
Qed.


Lemma Zabs_ind_lt_O :
 forall (P : Z -> Prop) (z : Z),
 (Z.abs z = 1%Z -> P z) -> ((1 < Z.abs z)%Z -> P z) -> (0 < Z.abs z)%Z -> P z.

Proof.
intros.
cut ((0 < Z.abs z)%Z -> (1 < Z.abs z)%Z \/ 1%Z = Z.abs z).
intros.
elim H2.
auto.
auto.
auto.
intro.
apply Zle_lt_or_eq.
RingReplace 1%Z (Z.succ 0).
apply Zlt_le_succ.
auto.
Qed.


Lemma Zabs_ind_le_1 :
 forall (P : Z -> Prop) (z : Z),
 ((Z.abs z <= 1)%Z -> P z) -> ((1 < Z.abs z)%Z -> P z) -> P z.

Proof.
intros.
cut ((Z.abs z <= 1)%Z \/ (1 < Z.abs z)%Z).
intros.
elim H1.
auto.
auto.
apply Zle_or_lt.
Qed.


Lemma ind_gt_le :
 forall (P : Z -> Prop) (z a : Z),
 ((a <= z)%Z -> P z) -> ((z < a)%Z -> P z) -> P z.

Proof.
intros.
cut ((a <= z)%Z \/ (z < a)%Z).
intro.
elim H1.
auto.
auto.
apply Zle_or_lt.
Qed.


Lemma Zabs_pos_ind :
 forall (P : Z -> Prop) (z : Z),
 ((0 < z)%Z -> P z) -> ((z < 0)%Z -> P z) -> (0 < Z.abs z)%Z -> P z.

Proof.
intros.
cut ({z = Z.abs z} + {z = (- Z.abs z)%Z}); [ idtac | apply Zabs_dec ].
intro.
elim H2.
intro; apply H.
rewrite a; auto.
intro; apply H0.
rewrite b.
apply Zplus_lt_reg_l with (Z.abs z).
rewrite Zplus_comm; rewrite Zplus_opp_l; rewrite <- Zplus_0_r_reverse; auto.
Qed.


Lemma Zind_plus_1 :
 forall (z a : Z) (P : Z -> Prop),
 (z = a -> P z) -> ((z < a)%Z -> P z) -> (z < a + 1)%Z -> P z.

Proof.
intros.
cut ((z < a + 1)%Z -> {(z < a)%Z} + {z = a}). 
intros.
elim H2; auto.
intro.
apply Z_le_lt_eq_dec.
apply Zlt_succ_le; auto.
Qed.


Lemma Zind_le :
 forall (z a : Z) (P : Z -> Prop),
 (z = a -> P z) -> ((z < a)%Z -> P z) -> (z <= a)%Z -> P z.

Proof.
intros.
cut ((z <= a)%Z -> {(z < a)%Z} + {z = a}). 
intros.
elim H2; auto.
intro.
apply Z_le_lt_eq_dec.
auto.
Qed.


Lemma Zind_le_ZERO :
 forall (z : Z) (P : Z -> Prop),
 (0%Z = z -> P z) -> ((0 < z)%Z -> P z) -> (0 <= z)%Z -> P z.

Proof.
intros.
cut ((0 <= z)%Z -> {(0 < z)%Z} + {0%Z = z}). 
intros.
elim H2; auto.
intro.
apply Z_le_lt_eq_dec.
auto.
Qed.