(* push *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Div2.
Require Import Coq.Init.Nat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Lia.
Require Import Coq.Arith.Mult.




(* Definiujemy predicate 'divides', aby sprawdzić, czy jedna liczba dzieli drugą *)
Definition divides (d n : nat) : Prop :=
  exists k, n = k * d.






(* Definiujemy relację gcd_rel jako trójargumentową relację na liczbach naturalnych *)
Definition gcd_rel (a b d : nat) : Prop :=
  (forall k : nat, divides k a -> divides k b -> divides k d) /\
  divides d a /\
  divides d b.

(* push *)

(* Twierdzenie o liniowej kombinacji *)
Theorem lin_comb : forall (a b c d x y : nat), gcd_rel a b d /\ c = x*a + y*b -> divides d c.
Proof.
  intros.
  unfold gcd_rel in H.
  destruct H.
  unfold divides in *.
  destruct H.
  destruct H1.
  rewrite -> H0.
  destruct H1 as [k1 H1].
  destruct H2 as [k2 H2].
  rewrite H1.
  rewrite H2.
  exists (x * k1 + y * k2).
  ring.
Qed.

(* push *)

(* Rekurencyjna definicja algorytmu Euklidesa *)
Fixpoint gcd_Euc (a b : nat) {struct a} : nat :=
  match a with
  | 0 => b
  | S a' => gcd_Euc (b mod S a') (S a')
  end.


(* Dowód poprawności algorytmu *)
(* DO POPRAWY !!! *)
(*Lemma krok : forall (a b d : nat), gcd_rel a b d <-> gcd_rel b (a mod b) d.
Proof.
  intros a b d.
  split.
  - intros H_gcd.
    unfold gcd_rel in *.
    destruct H_gcd as [H_divides_ab [H_divides_a H_divides_b]].
    split.
    + intros k H_divides_k_b H_divides_k_amodb.
      apply H_divides_ab.
      unfold divides in *.
      * destruct H_divides_a.
        destruct H_divides_b.
        destruct H_divides_k_b.
        destruct H_divides_k_amodb.
        unfold mod.
        exists d.
        
        trivial.
      * apply H_divides_k_b.
    + split.
      * apply H_divides_b.
      * apply H_divides_a.
  - intros H_gcd.
    unfold gcd_rel in *.
    destruct H_gcd as [H_divides_b [H_divides_amodb H_divides_d]].
    split.
    + intros k H_divides_k_a H_divides_k_b.
      apply H_divides_b.
      * apply H_divides_k_b.
      * apply H_divides_k_a.
    + split.
      * apply H_divides_d.
      * apply H_divides_amodb.
Qed.
*)

(* push *)

(* Definicja algorytmu Euklidesa jako relacji *)
Inductive euclid : nat -> nat -> nat -> Prop :=
| base : forall a : nat, euclid a a a
| step_a : forall (a b z : nat), a < b -> euclid a (b - a) z -> euclid a b z
| step_b : forall (a b z : nat), b < a -> euclid (a - b) b z -> euclid a b z.

(* push *) 

Require Import Arith.


(* Dowód terminacji *)
Lemma euclid_terminates : forall (a b : nat), a > 0 -> b > 0 -> exists (z : nat), euclid a b z.
(* DO POPRAWY !!! *)
Proof.
  intros a b Ha Hb.
  destruct (lt_eq_lt_dec a b) as [[Hlt | Heq] | Hgt].
  - (* a < b *)
    induction a.
    exists b.
    apply (step_a 0 b b).
    trivial.
    trivial.
    exists (gcd_Euc a (b-a)).
    apply (step_a a b (gcd_Euc a (b-a))).
    trivial.
    destruct (H a) as [z Hz].
    + assumption.
    + assumption.
    + exists .
      apply (step_a a b z); assumption.
  - (* a = b *)
    exists a.
    apply base.
  - (* a > b *)
    induction a using lt_wf_ind.
    destruct (H b) as [z Hz].
    + assumption.
    + assumption.
    + exists z.
      apply (step_b a b z); assumption.
Qed. 


(* push *)
(*Bonus*)
Lemma gcd_div : forall a b d,
  divides d a -> divides d b-> divides d (a - b).
Proof.
  intros a b d H1 H2.
  destruct H1 as [k1 Hk1].
  destruct H2 as [k2 Hk2].
  rewrite Hk1.
  rewrite Hk2.
  unfold divides.
  exists (k1 - k2).
  symmetry.
  apply (Nat.mul_sub_distr_r k1 k2 d).
Qed.







 