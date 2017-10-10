(* ---------------------------------------------------------------------

   This file is part of a repository containing the definitions and 
   proof scripts related to the formalization of context-free language
   theory in Coq. Specifically, the following results were obtained:
   
   (i) languages square, prime and anbncn are not context-free; 
   (ii) context-free languages are not closed under intersection.
   
   More information can be found in the paper "Some Applications of the 
   Formalization of the Pumping Lemma for Context-Free Languages", 
   submitted to CPP 2018 by Marcus Vinícius Midena Ramos, Ruy J. G. B. 
   de Queiroz, Nelma Moreira and José Carlos Bacelar Almeida. 
   Also, in the thesis "Formalization of 
   Context-Free Language Theory", submitted to the Informatics
   Center of the Pernambuco Federal University (CIn/UFPE) in
   Brazil.
   
   The file README.md describes the contents of each file and 
   provides instructions on how to compile them.
   
   Marcus Vinícius Midena Ramos
   mvmramos@gmail.com
   --------------------------------------------------------------------- *)

Require Import List.
Require Import Ring.
Require Import Omega.
Require Import NPeano.
Require Import NZPow.

Require Import misc_arith.
Require Import misc_list.
Require Import cfg.
Require Import cfl.
Require Import pumping.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

(* --------------------------------------------------------------------- *)
(* PUMPING LEMMA EXAMPLE                                                 *)
(* --------------------------------------------------------------------- *)

Section Pumping_Square.

Inductive terminal: Type:=
| a.

Definition square: lang terminal:=
fun (s: list terminal) =>
exists i: nat,
length s = i*i.

Fixpoint build (k: nat): list terminal:=
match k with
| 0 => []
| S k => a :: build k
end.

Lemma build_length:
forall k: nat,
length (build k) = k.
Proof.
induction k.
- simpl.
  reflexivity.
- simpl.
  rewrite IHk.
  reflexivity.
Qed.

Lemma not_square:
forall n i: nat,
n > i*i ->
n < (i+1)*(i+1) ->
~ exists j: nat,
  n = j*j.
Proof.
intros n i H1 H2 H3.
destruct H3 as [j H3].
rewrite H3 in H1, H2.
clear H3.
destruct j.
- simpl in H1.
  apply lt_n_0 in H1. 
  contradiction.
- rewrite <- Nat.pow_2_r in H1.
  rewrite <- Nat.pow_2_r in H1. 
  apply Nat.pow_lt_mono_l_iff in H1.
  + assert (H3: i<=j) by omega.
    clear H1. 
    replace (S j) with (j+1) in H2.
    * rewrite <- Nat.pow_2_r in H2.
      rewrite <- Nat.pow_2_r in H2.
      {
      apply Nat.pow_lt_mono_l_iff in H2.
      - assert (H4: j<i) by omega.
        clear H2. 
        omega.
      - auto.
      }
    * omega. 
  + auto.
Qed.

Lemma square_plus_not_square:
forall i j k,
j>=1 ->
j<=i ->
~ i*i+j=k*k.
Proof.
intros i j k H1 H2 H3.
assert (H4: i*i+j > i*i) by omega.
assert (H5: i*i+j < (i+1)*(i+1)).
  {
  replace ((i + 1) * (i + 1)) with (S i * S i).
  - simpl.
    rewrite <- mult_n_Sm.
    omega.
  - replace (S i) with (i+1). 
    + reflexivity.
    + omega.
  }
apply not_square in H4. 
- apply H4.
  exists k.
  exact H3. 
- exact H5.
Qed.

Lemma sentence_exists:
forall n: nat,
exists w: list terminal,
length w = n*n /\ square w.
Proof.
destruct n.
- exists [].
  split.
  + simpl.
    reflexivity.
  + unfold square.
    exists 0.
    simpl.
    reflexivity.
- exists (build (n*n+n+n+1)).
  split.
  + rewrite build_length.
    apply prod_eq.
  + unfold square. 
    exists (S n).
    rewrite build_length.
    apply prod_eq.
Qed.  

Lemma not_cfl_square: ~ cfl square.
Proof.
intros H1.
assert (H2: contains_empty square).
  {
  unfold contains_empty.
  unfold square.
  exists 0.
  simpl.
  reflexivity.
  }
assert (H3: contains_non_empty square).
  {
  unfold contains_non_empty.
  exists [a].
  unfold square.
  split.
  - exists 1.
    simpl. 
    reflexivity.
  - intros H3.
    inversion H3.
  }
apply pumping_lemma in H1. 
- destruct H1 as [n H1]. 
  assert (H4: exists (s: list terminal), (length s = n*n) /\ square s).
    {
    apply sentence_exists.
    }
  destruct H4 as [s [H4 H5]].
  assert (H98: n*n >= n).
    {
    apply mult_ge.
    }
  assert (H6: length s >= n) by omega.
  specialize (H1 s H5 H6).
  destruct H1 as [u [v [w [x [y [H11 [H12 [H13 [H14 H15]]]]]]]]].
  clear H2 H3 H6 H98.
  specialize (H15 2).
  simpl in H15.
  repeat rewrite app_nil_r in H15.
  unfold square in H15.
  rewrite H11 in H4.
  destruct H15 as [i H15].
  repeat rewrite app_length in H15.
  repeat rewrite app_length in H4.
  replace (length u + (length v + length v + (length w + (length x + length x + length y)))) with
          ((length u + length v + length w + length x + length y) + length v + length x) in H15.
  + replace (length u + length v + length w + length x + length y + length v + length x) with
            (length u + (length v + (length w + (length x + length y))) + (length v + length x)) in H15.
    * rewrite H4 in H15.
      clear H4.
      {
      replace (length v + length x) with (length (v++x)) in H15.
      - apply square_plus_not_square in H15. 
        + contradiction. 
        + exact H12.
        + rewrite app_length.
          repeat rewrite app_length in H14.
          omega.
      - rewrite app_length.
        reflexivity.
      }
    * omega.
  + omega.
- split.
  + left.
    exact H2.
  + left.
    exact H3.
Qed.

End Pumping_Square.
