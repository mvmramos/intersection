(* ---------------------------------------------------------------------

   This file is part of a repository containing the definitions and 
   proof scripts related to the formalization of context-free language
   theory in Coq. Specifically, the following results were obtained:
   
   (i) languages square, prime and anbncn are not context-free; 
   (ii) context-free languages are not closed under intersection.
   
   More information can be found in the article "Applications of the 
   Formalization of the Pumping Lemma for Context-Free Languages, 
   submitted to ITP 2017". Also, in the thesis "Formalization of 
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

Require misc_ssrprime.
Notation is_prime n := (is_true (prime.prime n)).

Section Pumping_Prime.

Inductive terminal: Type:=
| a.

Definition prime_lang: lang terminal:=
fun (s: list terminal) =>
exists i: nat,
is_prime i /\
length s = i.

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

Lemma sentence_exists:
forall n: nat,
exists w: list terminal,
length w >= n /\ prime_lang w.
Proof.
intros n.
destruct n.
- exists [a;a].
  split.
  + simpl.
    omega.
  + unfold prime_lang.
    exists 2.
    split.
    * simpl.
      auto.
    * simpl.
      reflexivity.
- assert (H1: exists m: nat, m >= S n /\ is_prime m).
    {
    apply (misc_ssrprime.prime_exists n).
    }
  destruct H1 as [m [H1 H2]].
  exists (build m).
  split.
  + rewrite build_length.
    exact H1.
  + unfold prime_lang. 
    exists m.
    split.
    * exact H2. 
    * rewrite build_length.
      reflexivity.
Qed.  

Lemma not_cfl_prime: ~ cfl prime_lang.
Proof.
intros H1.
assert (H2: ~ contains_empty prime_lang).
  {
  unfold contains_empty.
  unfold prime_lang.
  intros H2.
  destruct H2 as [i [H2 H3]].
  simpl in H3.
  rewrite <- H3 in H2.
  simpl in H2.
  generalize (misc_ssrprime.prime_gt0 0 H2); auto.
  }
assert (H3: contains_non_empty prime_lang).
  {
  unfold contains_non_empty.
  exists [a;a].
  unfold prime_lang.
  split.
  - exists 2.
    simpl. auto. 
  - intros H3.
    inversion H3.
  }
apply pumping_lemma in H1. 
- destruct H1 as [n H1]. 
  assert (H4: exists (s: list terminal), (length s >= n+2) /\ prime_lang s).
    {
    apply sentence_exists.
    }
  destruct H4 as [s [H4 H5]].
  assert (H6: length s >= n) by omega.
  specialize (H1 s H5 H6).
  destruct H1 as [u [v [w [x [y [H11 [H12 [H13 [H14 H15]]]]]]]]].
  clear H2 H3 H6.
  specialize (H15 (length (u++w++y))).
  unfold prime_lang in H15.  
  destruct H15 as [i [H15 H16]].
  rewrite <- H16  in H15.
  clear H16.
  repeat rewrite app_length in H15.
  repeat rewrite iter_length in H15.
  replace (length u + ((length u + (length w + length y)) * length v + (length w + ((length u + (length w + length y)) * length x + length y)))) with
          ((length u + length w + length y) * (1 + (length v + length x))) in H15.
  + rewrite H11 in H4.
    repeat rewrite app_length in H12, H13.
    repeat rewrite app_length in H14.
    repeat rewrite app_length in H4.
    assert (H6: length v + length x <= n) by omega.
    assert (H7: 1 + (length v + length x) >= 2) by omega.
    assert (H8: length u + length w + length y >= 2) by omega.
    apply (misc_ssrprime.mult_primeN _ _ H8 H7); assumption. 
  + replace (length u + (length w + length y)) with (length (u++w++y)).
    * rewrite mult_plus_distr_l.
      rewrite mult_1_r.
      {
      replace (length u + length w + length y) with (length (u++w++y)).
      - rewrite mult_plus_distr_l.
        replace (length (u ++ w ++ y)) with (length u + length w + length y) at 1.
        + omega.
        + repeat rewrite app_length.
          rewrite plus_assoc. 
          reflexivity.
      - repeat rewrite app_length.
          rewrite plus_assoc. 
          reflexivity.
      }
    * repeat rewrite app_length.
      reflexivity.
- split.
  + right.
    exact H2.
  + left.
    exact H3.
Qed.

End Pumping_Prime.