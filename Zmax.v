Require Import ZArith.

Definition Zmax (n m : Z) :=
  match (n ?= m)%Z return Z with
  | Datatypes.Eq => n
  | Datatypes.Gt => n
  | Datatypes.Lt => m
  end. 

Lemma Zmax_SS : forall n m : Z, Zsucc (Zmax n m) = Zmax (Zsucc n) (Zsucc m). 
Proof.
intros n m; unfold Zmax in |- *; rewrite (Zcompare_succ_compat n m);
 elim_compare n m; intros E; rewrite E; auto with arith.
Qed. 

Lemma Zle_max_l : forall n m : Z, (n <= Zmax n m)%Z. 
Proof.
intros n m; unfold Zmax in |- *; elim_compare n m; intros E; rewrite E;
 [ apply Zle_refl | apply Zlt_le_weak; exact E | apply Zle_refl ].
Qed. 

Lemma Zle_max_r : forall n m : Z, (m <= Zmax n m)%Z. 
Proof.
intros n m; unfold Zmax in |- *; elim_compare n m; intros E; rewrite E;
 [ apply Zge_le; unfold Zge in |- *; rewrite E; discriminate
 | apply Zle_refl
 | apply Zge_le; unfold Zge in |- *; rewrite E; discriminate ].
Qed. 

Lemma Zmax_case : forall (n m : Z) (P : Z -> Set), P n -> P m -> P (Zmax n m).
intros n m P H1 H2; unfold Zmax in |- *; case (n ?= m)%Z; auto with arith.
Qed. 

Lemma Zmax_or : forall n m : Z, Zmax n m = n \/ Zmax n m = m.
unfold Zmax in |- *; intros; elim (n ?= m)%Z; auto.
Qed. 

Lemma Zmax_n_n : forall n : Z, Zmax n n = n.
unfold Zmax in |- *; intros; elim (n ?= n)%Z; auto.
Qed. 