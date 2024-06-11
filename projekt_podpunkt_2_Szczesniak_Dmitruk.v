Require Import ZArith.
Require Import ZArithRing.
Require Import Zdiv.
Require Import Lia.
Require Import Wellfounded.

Open Scope Z_scope.
(* 2 Implementacja algorytmu Euklidesa i dowód jego poprawności *)

Inductive gcd (a b d : Z) : Prop :=
  | gcd_intro : 
      (d | a)%Z ->
      (d | b)%Z ->
      (forall x : Z, (x | a)%Z -> (x | b)%Z -> (x | d)%Z) -> gcd a b d.

Lemma gcd_sym : forall a b d : Z, gcd a b d -> gcd b a d.
Proof.
  intros a b d H.
  destruct H as [H1 H2 H3].
  constructor; auto.
Qed.

Lemma gcd_0 : forall a : Z, gcd a 0 a.
Proof.
  intros a.
  constructor.
  - apply Z.divide_refl.
  - apply Z.divide_0_r.
  - intros x H1 H2. assumption.
Qed.

Lemma gcd_minus : forall a b d : Z, gcd a (- b) d -> gcd b a d.
Proof.
  intros a b d H.
  destruct H as [H1 H2 H3].
  constructor.
  - apply Z.divide_opp_r. assumption.
  - assumption.
  - intros x H4 H5.
    assert (H4_neg : (x | - b)%Z).
    {
      apply Z.divide_opp_r. assumption.
    }
    apply H3; assumption.
Qed.

Lemma gcd_opp : forall a b d : Z, gcd a b d -> gcd b a (- d).
Proof.
  intros a b d H.
  destruct H as [H1 H2 H3].
  constructor.
  - apply Z.divide_opp_l. assumption.
  - apply Z.divide_opp_l. assumption.
  - intros x H4 H5.
    assert (H6 : (x | d)%Z).
    {
      apply H3; assumption.
    }
    apply Z.divide_opp_r. assumption.
Qed.

Lemma gcd_div : forall a b d q : Z,
  (d | a) -> (d | b) -> (d | a - q * b).
Proof.
  intros a b d q H1 H2.
  destruct H1 as [k1 Hk1].
  destruct H2 as [k2 Hk2].
  unfold Z.divide.
  exists (k1 - q * k2).
  rewrite Hk1.
  rewrite Hk2.
  ring.
Qed.

(* 
Theorem gcd_Euc_correct : forall a b : Z, gcd_rel a b (gcd_Euc a b).
Proof.
(*nie udalo sie niestety udowodnic *) *)




