Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Div2.
Require Import Coq.Init.Nat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Lia.
Require Import Coq.Arith.Mult.

(*1 Definicja NWD i dowód podzielności dla liniowej kombinacji*)
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


(* 2 Implementacja algorytmu Euklidesa i dowód jego poprawności *)


(* Rekurencyjna definicja algorytmu Euklidesa *)
Fixpoint gcd_Euc (a b : nat) {struct a} : nat :=
  match a with
  | 0 => b
  | S a' => gcd_Euc (b mod S a') (S a')
  end.


(* Dowód poprawności algorytmu *)
(* Próbowaliśmy, ale nie wyszło !!! *)
(*Lemma krok : forall (a b d : nat), gcd_rel a b d <-> gcd_rel b (a mod b) d. *)



(* 3 Wyrażenie algorytmu Euklidesa w semantyce relacyjnej i dowód termiancji*)

(* Definicja algorytmu Euklidesa jako relacji *)
Inductive euclid : nat -> nat -> nat -> Prop :=
| base : forall a : nat, euclid a a a
| step_a : forall (a b z : nat), a < b -> euclid a (b - a) z -> euclid a b z
| step_b : forall (a b z : nat), b < a -> euclid (a - b) b z -> euclid a b z.



(* Dowód terminacji *)
Lemma euclid_terminates : forall (a b : nat), a > 0 -> b > 0 -> exists (z : nat), euclid a b z.
(* Próbowaliśmy ale sie nie udało *)










 