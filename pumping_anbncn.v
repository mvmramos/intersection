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

Section Pumping_Example.

Inductive terminal: Type:=
| a
| b
| c.

Fixpoint na (s: list terminal): nat:=
match s with
| [] => 0
| a :: s => 1 + na s
| _ :: s => na s
end.

Fixpoint nb (s: list terminal): nat:=
match s with
| [] => 0
| b :: s => 1 + nb s
| _ :: s => nb s
end.

Fixpoint nc (s: list terminal): nat:=
match s with
| [] => 0
| c :: s => 1 + nc s
| _ :: s => nc s
end.

Fixpoint only_a (w: list terminal): Prop:=
match w with
| [] => True
| a :: w' => only_a w'
| _ :: w' => False
end.

Fixpoint only_b (w: list terminal): Prop:=
match w with
| [] => True
| b :: w' => only_b w'
| _ :: w' => False
end.

Fixpoint only_c (w: list terminal): Prop:=
match w with
| [] => True
| c :: w' => only_c w'
| _ :: w' => False
end.

Definition only_a_b (w: list terminal): Prop:=
exists p q: list terminal,
w=p++q /\ only_a p /\ only_b q.

Lemma only_a_only_a_b:
forall w: list terminal,
only_a w ->
only_a_b w.
Proof.
induction w.
- intros _.
  exists [], [].
  simpl.
  split.
  + reflexivity.
  + auto.
- intros H.
  destruct a0.
  + simpl in H.
    specialize (IHw H).
    exists (a::w), [].
    split.
    * rewrite app_nil_r. 
      reflexivity.
    * {
      simpl.
      split.
      - exact H.
      - auto.
      }
  + simpl in H.
    contradiction.
  + simpl in H.
    contradiction.
Qed.

Lemma only_b_only_a_b:
forall w: list terminal,
only_b w ->
only_a_b w.
Proof.
induction w.
- intros _.
  exists [], [].
  simpl.
  split.
  + reflexivity.
  + auto.
- intros H.
  destruct a0.
  + simpl in H.
    contradiction.
  + simpl in H.
    specialize (IHw H).
    exists [],(b::w).
    split.
    * rewrite app_nil_l. 
      reflexivity.
    * {
      simpl.
      split.
      - auto.
      - exact H.
      }
  + simpl in H.
    contradiction.
Qed.

Definition only_b_c (w: list terminal): Prop:=
exists p q: list terminal,
w=p++q /\ only_b p /\ only_c q.

Lemma only_b_only_b_c:
forall w: list terminal,
only_b w ->
only_b_c w.
Proof.
induction w.
- intros _.
  exists [], [].
  simpl.
  split.
  + reflexivity.
  + auto.
- intros H.
  destruct a0.
  + simpl in H.
    contradiction.
  + simpl in H.
    specialize (IHw H).
    exists (b::w), [].
    split.
    * rewrite app_nil_r. 
      reflexivity.
    * {
      simpl.
      split.
      - exact H.
      - auto.
      }
  + simpl in H.
    contradiction.
Qed.

Lemma only_c_only_b_c:
forall w: list terminal,
only_c w ->
only_b_c w.
Proof.
induction w.
- intros _.
  exists [], [].
  simpl.
  split.
  + reflexivity.
  + auto.
- intros H.
  destruct a0.
  + simpl in H.
    contradiction.
  + simpl in H.
    contradiction.
  + simpl in H.
    specialize (IHw H).
    exists [],(c::w).
    split.
    * rewrite app_nil_l. 
      reflexivity.
    * {
      simpl.
      split.
      - auto.
      - exact H.
      }
Qed.

Lemma length_na:
forall w: list terminal,
length w >= na w.
Proof.
induction w.
- simpl.
  omega.
- simpl. 
  destruct a0.
  + omega. 
  + omega. 
  + omega. 
Qed.

Lemma length_nb:
forall w: list terminal,
length w >= nb w.
Proof.
induction w.
- simpl.
  omega.
- simpl. 
  destruct a0.
  + omega. 
  + omega. 
  + omega. 
Qed.

Lemma length_nc:
forall w: list terminal,
length w >= nc w.
Proof.
induction w.
- simpl.
  omega.
- simpl. 
  destruct a0.
  + omega. 
  + omega. 
  + omega. 
Qed.

Lemma length_eq_na_0:
forall w: list terminal,
length w = na w -> nb w = 0 /\ nc w = 0.
Proof.
induction w.
- simpl. 
  auto. 
- intros H.
  destruct a0. 
  + simpl in H.
    assert (H2: length w = na w) by omega.
    specialize (IHw H2).
    simpl.
    exact IHw.
  + simpl in H.
    assert (H3: na w <= length w).
      {
      apply length_na.
      }
    omega.
  + simpl in H.
    assert (H3: na w <= length w).
      {
      apply length_na.
      }
    omega.
Qed.
      
Lemma length_eq_nb_0:
forall w: list terminal,
length w = nb w -> na w = 0 /\ nc w = 0.
Proof.
induction w.
- simpl. 
  auto. 
- intros H.
  destruct a0. 
  + simpl in H.
    assert (H2: nb w <= length w).
      {
      apply length_nb.
      }
    omega.
  + simpl in H.
    assert (H2: length w = nb w) by omega.
    specialize (IHw H2).
    simpl.
    exact IHw.
  + simpl in H.
    assert (H2: nb w <= length w).
      {
      apply length_nb.
      }
    omega.
Qed.

Lemma length_eq_nc_0:
forall w: list terminal,
length w = nc w -> na w = 0 /\ nb w = 0.
Proof.
induction w.
- simpl. 
  auto. 
- intros H.
  destruct a0. 
  + simpl in H.
    assert (H2: nc w <= length w).
      {
      apply length_nc.
      }
    omega.
  + simpl in H.
    assert (H2: nc w <= length w).
      {
      apply length_nc.
      }
    omega.
  + simpl in H.
    assert (H2: length w = nc w) by omega.
    specialize (IHw H2).
    simpl.
    exact IHw.
Qed.

Lemma only_a_length_na:
forall w: list terminal,
only_a w -> length w = na w.
Proof.
induction w.
- intros _.
  simpl.
  reflexivity.
- intros H.
  destruct a0.
  + simpl in H.
    simpl.
    specialize (IHw H).
    omega.
  + simpl in H.
    contradiction.
  + simpl in H.
    contradiction.
Qed.

Lemma only_b_length_nb:
forall w: list terminal,
only_b w -> length w = nb w.
Proof.
induction w.
- intros _.
  simpl.
  reflexivity.
- intros H.
  destruct a0.
  + simpl in H.
    contradiction.
  + simpl in H.
    simpl.
    specialize (IHw H).
    omega.
  + simpl in H.
    contradiction.
Qed.

Lemma only_c_length_nc:
forall w: list terminal,
only_c w -> length w = nc w.
Proof.
induction w.
- intros _.
  simpl.
  reflexivity.
- intros H.
  destruct a0.
  + simpl in H.
    contradiction.
  + simpl in H.
    contradiction.
  + simpl in H.
    simpl.
    specialize (IHw H).
    omega.
Qed.

Lemma length_na_only_a:
forall w: list terminal,
length w = na w ->
only_a w.
Proof.
induction w.
- intros _.
  simpl.
  auto.
- intros H.
  destruct a0.
  + simpl.
    apply IHw.
    simpl in H.
    omega.
  + simpl in H.
    assert (H2: length w >= na w).
      {
      apply length_na.
      }
    omega.
  + simpl in H.
    assert (H2: length w >= na w).
      {
      apply length_na.
      }
    omega.
Qed.

Lemma length_nb_only_b:
forall w: list terminal,
length w = nb w ->
only_b w.
Proof.
induction w.
- intros _.
  simpl.
  auto.
- intros H.
  destruct a0.
  + simpl in H.
    assert (H2: length w >= nb w).
      {
      apply length_nb.
      }
    omega.
  + simpl.
    apply IHw.
    simpl in H.
    omega.
  + simpl in H.
    assert (H2: length w >= nb w).
      {
      apply length_nb.
      }
    omega.
Qed.

Lemma length_nc_only_c:
forall w: list terminal,
length w = nc w ->
only_c w.
Proof.
induction w.
- intros _.
  simpl.
  auto.
- intros H.
  destruct a0.
  + simpl in H.
    assert (H2: length w >= nc w).
      {
      apply length_nc.
      }
    omega.
  + simpl in H.
    assert (H2: length w >= nc w).
      {
      apply length_nc.
      }
    omega.
  + simpl.
    apply IHw.
    simpl in H.
    omega.
Qed.

Lemma na_cat:
forall l1 l2: list terminal,
na (l1 ++ l2) = na l1 + na l2.
Proof.
induction l1.
- intros l2.
  simpl.
  reflexivity.
- intros l2.
  simpl. 
  destruct a0. 
  + rewrite IHl1.
    simpl.
    reflexivity.
  + rewrite IHl1.
    reflexivity.
  + rewrite IHl1.
    reflexivity.
Qed.

Lemma nb_cat:
forall l1 l2: list terminal,
nb (l1 ++ l2) = nb l1 + nb l2.
Proof.
induction l1.
- intros l2.
  simpl.
  reflexivity.
- intros l2.
  simpl. 
  destruct a0. 
  + rewrite IHl1.
    simpl.
    reflexivity.
  + rewrite IHl1.
    reflexivity.
  + rewrite IHl1.
    reflexivity.
Qed.

Lemma nc_cat:
forall l1 l2: list terminal,
nc (l1 ++ l2) = nc l1 + nc l2.
Proof.
induction l1.
- intros l2.
  simpl.
  reflexivity.
- intros l2.
  simpl. 
  destruct a0. 
  + rewrite IHl1.
    simpl.
    reflexivity.
  + rewrite IHl1.
    reflexivity.
  + rewrite IHl1.
    reflexivity.
Qed.

Lemma only_a_cat:
forall p q: list terminal,
only_a (p++q) -> only_a p /\ only_a q.
Proof.
induction p.
- intros q H.
  split.
  + simpl.
    auto.
  + exact H.
- intros q H.
  destruct a0.
  + split.
    * simpl in H.
      specialize (IHp q H).
      simpl.
      destruct IHp as [IHp _].
      exact IHp.
    * simpl in H.
      specialize (IHp q H).
      simpl.
      destruct IHp as [_ IHp].
      exact IHp.
  + simpl in H.
    contradiction.
  + simpl in H.
    contradiction.
Qed.

Lemma only_b_cat:
forall p q: list terminal,
only_b (p++q) -> only_b p /\ only_b q.
Proof.
induction p.
- intros q H.
  split.
  + simpl.
    auto.
  + exact H.
- intros q H.
  destruct a0.
  + simpl in H.
    contradiction.
  + split.
    * simpl in H.
      specialize (IHp q H).
      simpl.
      destruct IHp as [IHp _].
      exact IHp.
    * simpl in H.
      specialize (IHp q H).
      simpl.
      destruct IHp as [_ IHp].
      exact IHp.
  + simpl in H.
    contradiction.
Qed.

Lemma only_c_cat:
forall p q: list terminal,
only_c (p++q) -> only_c p /\ only_c q.
Proof.
induction p.
- intros q H.
  split.
  + simpl.
    auto.
  + exact H.
- intros q H.
  destruct a0.
  + simpl in H.
    contradiction.
  + simpl in H.
    contradiction.
  + split.
    * simpl in H.
      specialize (IHp q H).
      simpl.
      destruct IHp as [IHp _].
      exact IHp.
    * simpl in H.
      specialize (IHp q H).
      simpl.
      destruct IHp as [_ IHp].
      exact IHp.
Qed.

Lemma only_a_b_nc:
forall w: list terminal,
only_a_b w -> nc w = 0.
Proof.
destruct w.
- intros _.
  simpl.
  auto.
- intros H.
  destruct t.
  + unfold only_a_b in H.
    destruct H as [p [q [H1 [H2 H3]]]].
    destruct p, q.
    * inversion H1. 
    * inversion H1.
      rewrite <- H0 in H3.
      simpl in H3.
      contradiction.
    * simpl.
      inversion H1.
      rewrite <- H0 in H2.
      simpl in H2.
      apply only_a_length_na in H2.
      apply length_eq_na_0 in H2.
      rewrite app_nil_r.
      apply H2.
    * inversion H1.
      rewrite <- H0 in H2.
      simpl in H2.
      simpl.
      rewrite nc_cat. 
      apply only_a_length_na in H2.
      apply length_eq_na_0 in H2.
      destruct H2 as [_ H2].
      apply only_b_length_nb in H3.
      apply length_eq_nb_0 in H3.
      destruct H3 as [_ H3].
      omega.
  + unfold only_a_b in H.
    destruct H as [p [q [H1 [H2 H3]]]].
    destruct p, q.
    * inversion H1.
    * inversion H1.
      rewrite <- H0 in H3.
      simpl in H3.
      simpl.
      apply only_b_length_nb in H3.
      apply length_eq_nb_0 in H3.
      destruct H3 as [_ H3].
      exact H3.
    * inversion H1.
      rewrite <- H0 in H2.
      simpl in H2.
      contradiction.
    * inversion H1.
      rewrite <- H0 in H2.
      simpl in H2.
      contradiction.
  + unfold only_a_b in H.
    destruct H as [p [q [H1 [H2 H3]]]].
    destruct p, q.
    * inversion H1.
    * inversion H1.
      rewrite <- H0 in H3.
      simpl in H3.
      contradiction.
    * inversion H1.
      rewrite <- H0 in H2.
      simpl in H2.
      contradiction.
    * inversion H1.
      rewrite <- H0 in H2.
      simpl in H2.
      contradiction.
Qed.

Lemma only_a_b_cat_l:
forall p q: list terminal,
only_a_b (p++q) ->
p <> [] ->
na p > 0 \/ nb p > 0.
Proof.
intros p q H1 H2.
destruct p.
- destruct H2.
  reflexivity.
- destruct t.
  + left.
    simpl.
    omega.
  + right.
    simpl.
    omega.
  + unfold only_a_b in H1.
    destruct H1 as [p0 [q0 [H3 [H4 H5]]]].
    destruct p0, q0.
    * inversion H3.
    * inversion H3.
      rewrite <- H0 in H5.
      simpl in H5.
      contradiction.
    * inversion H3.
      rewrite <- H0 in H4.
      simpl in H4.
      contradiction.
    * inversion H3.
      rewrite <- H0 in H4.
      simpl in H4.
      contradiction.
Qed.

Lemma only_a_b_cat_r:
forall p q: list terminal,
only_a_b (p++q) ->
q <> [] ->
na q > 0 \/ nb q > 0.
Proof.
intros p q H1 H2.
destruct p, q.
- destruct H2.
  reflexivity.
- destruct t.
  + left.
    simpl.
    omega.
  + right.
    simpl.
    omega.
  + unfold only_a_b in H1.
    destruct H1 as [p0 [q0 [H3 [H4 H5]]]].
    destruct p0, q0.
    * inversion H3.
    * inversion H3.
      rewrite <- H0 in H5.
      simpl in H5.
      contradiction.
    * inversion H3.
      rewrite <- H0 in H4.
      simpl in H4.
      contradiction.
    * inversion H3.
      rewrite <- H0 in H4.
      simpl in H4.
      contradiction.
- destruct H2.
  reflexivity.
- destruct t0.
  + left.
    simpl.
    omega.
  + right.
    simpl.
    omega.
  + unfold only_a_b in H1. 
    destruct H1 as [p0 [q0 [H3 [H4 H5]]]].
    apply equal_app in H3.
    destruct H3 as [H3 | H3].
    * destruct H3 as [l [H3 H3']].
      {
      destruct l.
      - rewrite app_nil_l in H3'.
        rewrite <- H3' in H5.
        simpl in H5.
        contradiction.
      - inversion H3'.
        rewrite <- H0 in H3.
        rewrite H3 in H4.
        apply only_a_cat in H4.
        destruct H4 as [_ H4].
        simpl in H4.
        contradiction.
      }
    * destruct H3 as [l [H3 H3']].
      {
      rewrite H3' in H5.
      apply only_b_cat in H5.
      destruct H5 as [_ H5].
      simpl in H5.
      contradiction.
      }
Qed.

Lemma only_b_c_na:
forall w: list terminal,
only_b_c w -> na w = 0.
Proof.
destruct w.
- intros _.
  simpl.
  auto.
- intros H.
  destruct t.
  + unfold only_b_c in H.
    destruct H as [p [q [H1 [H2 H3]]]].
    destruct p, q.
    * inversion H1.
    * inversion H1.
      rewrite <- H0 in H3.
      simpl in H3.
      contradiction.
    * inversion H1. 
      rewrite <- H0 in H2. 
      simpl in H2.
      contradiction.
    * inversion H1.
      rewrite <- H0 in H2.
      simpl in H2.
      contradiction.
  + unfold only_b_c in H.
    destruct H as [p [q [H1 [H2 H3]]]].
    destruct p, q.
    * inversion H1.
    * inversion H1. 
      rewrite <- H0 in H3.
      simpl in H3.
      contradiction.
    * inversion H1. 
      rewrite app_nil_r in H4. 
      rewrite <- H0, <- H4 in H2.
      simpl in H2.
      simpl.
      rewrite app_nil_r.
      apply only_b_length_nb in H2.
      apply length_eq_nb_0 in H2.
      destruct H2 as [H2 _].
      rewrite H4 in H2.
      exact H2.
    * inversion H1.
      rewrite <- H0 in H2.
      simpl in H2.
      simpl.
      apply only_c_length_nc in H3.
      apply length_eq_nc_0 in H3.
      destruct H3 as [H3 _].
      apply only_b_length_nb in H2.
      apply length_eq_nb_0 in H2.
      destruct H2 as [H2 _].
      rewrite na_cat.
      omega.
  + unfold only_b_c in H.
    destruct H as [p [q [H1 [H2 H3]]]].
    destruct p, q.
    * inversion H1. 
    * inversion H1.
      rewrite <- H0 in H3.
      simpl in H3.
      simpl.
      apply only_c_length_nc in H3.
      apply length_eq_nc_0 in H3.
      apply H3.
    * inversion H1.
      rewrite <- H0 in H2.
      simpl in H2.
      contradiction.
    * inversion H1.
      rewrite <- H0 in H2.
      simpl in H2.
      contradiction.
Qed.

Lemma only_b_c_cat_l:
forall p q: list terminal,
only_b_c (p++q) ->
p <> [] ->
nb p > 0 \/ nc p > 0.
Proof.
intros p q H1 H2.
destruct p.
- destruct H2.
  reflexivity.
- destruct t.
  + unfold only_b_c in H1.
    destruct H1 as [p0 [q0 [H3 [H4 H5]]]].
    destruct p0, q0.
    * inversion H3. 
    * inversion H3.
      rewrite <- H0 in H5.
      simpl in H5.
      contradiction.
    * inversion H3.
      rewrite <- H0 in H4.
      simpl in H4.
      contradiction.
    * inversion H3.
      rewrite <- H0 in H4.
      simpl in H4.
      contradiction.      
  + left.
    simpl.
    omega.
  + right.
    simpl.
    omega.
Qed.

Lemma only_b_c_cat_r:
forall p q: list terminal,
only_b_c (p++q) ->
q <> [] ->
nb q > 0 \/ nc q > 0.
Proof.
intros p q H1 H2.
destruct p, q.
- destruct H2.
  reflexivity.
- destruct t.
  + unfold only_b_c in H1.
    destruct H1 as [p0 [q0 [H3 [H4 H5]]]].
    destruct p0, q0.
    * inversion H3. 
    * inversion H3.
      rewrite <- H0 in H5.
      simpl in H5. 
      contradiction.
    * inversion H3. 
      rewrite <- H0 in H4.
      simpl in H4. 
      contradiction.
    * inversion H3.
      rewrite <- H0 in H4.
      simpl in H4.
      contradiction.
  + left.
    simpl.
    omega.
  + right.
    simpl.
    omega.
- destruct H2.
  reflexivity.
- destruct t0.
  + unfold only_b_c in H1. 
    destruct H1 as [p0 [q0 [H3 [H4 H5]]]].
    apply equal_app in H3.
    destruct H3 as [H3 | H3].
    * destruct H3 as [l [H3 H3']].
      {
      destruct l.
      - rewrite app_nil_l in H3'.
        rewrite <- H3' in H5.
        simpl in H5.
        contradiction.
      - inversion H3'.
        rewrite <- H0 in H3.
        rewrite H3 in H4.
        apply only_b_cat in H4.
        destruct H4 as [_ H4].
        simpl in H4.
        contradiction.
      }
    * destruct H3 as [l [H3 H3']].
      {
      rewrite H3' in H5.
      apply only_c_cat in H5.
      destruct H5 as [_ H5].
      simpl in H5.
      contradiction.
      }
  + left.
    simpl.
    omega.
  + right.
    simpl.
    omega.
Qed.

Definition anbncn: lang terminal:=
fun (s: list terminal) =>
exists x y z: list terminal,
exists i: nat,
s = x ++ y ++ z /\ length x = i /\ na x = i /\ length y = i /\ nb y = i /\ length z = i /\ nc z = i.

Lemma na_eq_nb_eq_nc:
forall w: list terminal,
anbncn w -> na w = nb w /\ nb w = nc w.
Proof.
intros w H. 
unfold anbncn in H.
destruct H as [x [y [z [i [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]]]]].
split.
- rewrite H1.
  repeat rewrite na_cat.
  repeat rewrite nb_cat.
  rewrite <- H3 in H2.
  apply length_eq_na_0 in H2.
  destruct H2 as [H2 H8].
  rewrite <- H5 in H4.
  apply length_eq_nb_0 in H4.
  destruct H4 as [H4 H9].
  rewrite <- H7 in H6.
  apply length_eq_nc_0 in H6.
  destruct H6 as [H6 H10].
  omega.
- rewrite H1.
  repeat rewrite nb_cat.
  repeat rewrite nc_cat.
  rewrite <- H3 in H2.
  apply length_eq_na_0 in H2.
  destruct H2 as [H2 H8].
  rewrite <- H5 in H4.
  apply length_eq_nb_0 in H4.
  destruct H4 as [H4 H9].
  rewrite <- H7 in H6.
  apply length_eq_nc_0 in H6.
  destruct H6 as [H6 H10].
  omega.
Qed.

Lemma sentence_exists:
forall n: nat,
exists w: list terminal,
length w = 3*n /\ anbncn w.
Proof.
induction n.
- exists [].
  split.
  + simpl.
    auto.
  + exists [], [], [], 0.
    simpl.
    split.
    * reflexivity.
    * omega.
- destruct IHn as [w [H1 H2]].
  unfold anbncn in H2.
  destruct H2 as [x [y [z [i [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]]]].
  exists ((a::x)++(b::y)++(c::z)).
  split.
  + repeat rewrite app_length.
    simpl.
    rewrite H4, H6, H8.
    apply length_split_3 with (n:=n) (i:=i) in H3.
    * rewrite H3.
      omega.
    * exact H1.
    * exact H4.
    * exact H6.
    * exact H8.
  + exists (a::x), (b::y), (c::z), (i+1).
    split.
    * reflexivity.
    * {
      split.
      - simpl.
        rewrite H4.
        omega. 
      - split.
        + simpl.
          rewrite H5.
          omega.
        + split.
          * simpl.
            rewrite H6.
            omega.
          * {
            split. 
            - simpl.
              rewrite H7.
              omega.
            - split.
              + simpl.
                rewrite H8.
                omega.
              + simpl.
                rewrite H9.
                omega.
            }
      }
Qed.

Lemma sublist_or:
forall x y z m: list terminal,
forall i: nat,
length x = i ->
na x = i ->
length y = i ->
nb y = i ->
length z = i ->
nc z = i ->
sublist (x++y++z) m ->
length m >= 1 ->
length m <= i ->
sublist (x++y) m \/ sublist (y++z) m.
Proof.
intros x y z m i H1 H2 H3 H4 H5 H6 H7 H8 H9.
destruct m.
- simpl in H8.
  omega.
- destruct t.
  + left.
    unfold sublist in H7.
    destruct H7 as [p [s H7]].
    apply equal_app in H7.
    destruct H7 as [H7 | H7].
    * destruct H7 as [l [H10 H11]].
      apply equal_app in H11.
      {
      destruct H11 as [H11 | H11].
      - destruct H11 as [l0 [H11 H12]].
        rewrite <- H6 in H5.
        apply length_nc_only_c in H5.
        rewrite H12 in H5.
        apply only_c_cat in H5.
        destruct H5 as [_ H5].
        simpl in H5.
        contradiction.
      - destruct H11 as [l0 [H11 H12]].
        apply equal_app in H12.
        destruct H12 as [H12 | H12].
        + destruct H12 as [l1 [H12 H13]].
          rewrite H12 in H11.
          rewrite <- H4 in H3.
          apply length_nb_only_b in H3.
          rewrite H11 in H3.
          apply only_b_cat in H3.
          destruct H3 as [_ H3].
          simpl in H3.
          contradiction.
        + destruct H12 as [l1 [H12 H13]].
          destruct l0,l1.
          * inversion H12.
          * inversion H12.
            rewrite <- H0 in H13.
            rewrite <- H6 in H5.
            apply length_nc_only_c in H5.
            rewrite H13 in H5.
            simpl in H5.
            contradiction.
          * inversion H12.
            rewrite <- H0 in H11.
            rewrite <- H4 in H3.
            apply length_nb_only_b in H3.
            rewrite H11 in H3.
            apply only_b_cat in H3.
            destruct H3 as [_ H3].
            simpl in H3.
            contradiction.
          * inversion H12.
            rewrite <- H0 in H11.
            rewrite <- H4 in H3.
            apply length_nb_only_b in H3.
            rewrite H11 in H3.
            apply only_b_cat in H3.
            destruct H3 as [_ H3].
            simpl in H3.
            contradiction.
      }
    * destruct H7 as [l [H10 H11]].
      apply equal_app in H11.
      {
      destruct H11 as [H11 | H11].
      - destruct H11 as [l0 [H11 H12]].
        rewrite H10, H11.
        exists p,(l0 ++ y).
        repeat rewrite <- app_assoc.
        reflexivity.
      - destruct H11 as [l0 [H11 H12]].
        apply equal_app in H12.
        destruct H12 as [H12 | H12].
        + destruct H12 as [l1 [H12 H13]].
          destruct l,l0.
          * inversion H11.
          * inversion H11.
            {
            destruct y,l1.
            - inversion H12.
            - inversion H12.
              rewrite <- H14 in H13.
              rewrite <- H0 in H13.
              rewrite <- H6 in H5.
              apply length_nc_only_c in H5.
              rewrite H13 in H5.
              simpl in H5.
              contradiction.
            - inversion H12.
              rewrite <- H14.
              rewrite <- H0.
              exists x,[].
              repeat rewrite app_nil_r.
              reflexivity.
            - inversion H12.
              simpl in H9.
              assert (H97: length m < i) by omega.
              assert (H98: length m >= i).
                {
                simpl in H3.
                assert (H99: length y = i-1) by omega.
                rewrite H7, H15.
                repeat rewrite app_length.
                simpl.
                omega.
                }
              omega.
            }
          * inversion H11. 
            rewrite H10.
            rewrite <- H0.
            exists p,y.
            rewrite app_nil_r.
            repeat rewrite <- app_assoc. 
            reflexivity.
          * inversion H11.
            { 
            destruct y,l1. 
            - inversion H12. 
            - inversion H12.
              rewrite H10 in H1. 
              rewrite app_length in H1.
              simpl in H1.
              assert (H: i > 0) by omega.
              simpl in H3.
              omega.
            - inversion H12.
              rewrite H10.
              rewrite <- H0.
              exists p,[].
              repeat rewrite app_nil_r.
              rewrite <- app_assoc. 
              reflexivity.
            - inversion H12.
              simpl in H9.
              assert (H97: length m < i) by omega.
              rewrite H15 in H7.
              simpl in H3.
              assert (H98: length m > i).
                {
                assert (H99: length y = i-1) by omega.
                rewrite H7.
                repeat rewrite app_length.
                simpl.
                repeat rewrite app_length.
                simpl.
                omega.
                }
              omega.
            }      
        + destruct H12 as [l1 [H12 H13]].
          destruct l,l0.
          * inversion H11.
          * inversion H11.
            rewrite <- H0 in H12.
            rewrite <- H4 in H3.
            apply length_nb_only_b in H3.
            rewrite H12 in H3.
            simpl in H3.
            contradiction.
          * inversion H11.
            rewrite H10.
            rewrite <- H0.
            exists p,y.
            rewrite app_nil_r.
            repeat rewrite <- app_assoc.
            reflexivity.
          * inversion H11.
            rewrite H10, H0, H12.
            exists p,l1.
            rewrite <- app_assoc.
            assert (H99: (t :: l ++ t0 :: l0) = (t :: l) ++ (t0 :: l0)).
              {
              reflexivity.
              }
            rewrite H99.
            rewrite <- app_assoc.
            reflexivity.
      }     
  + right.
    unfold sublist in H7.
    destruct H7 as [p [s H7]].
    apply equal_app in H7.
    destruct H7 as [H7 | H7].
    * destruct H7 as [l [H10 H11]].
      apply equal_app in H11.
      {
      destruct H11 as [H11 | H11].
      - destruct H11 as [l0 [H11 H12]].
        rewrite H12.
        exists (y ++ l0),s.
        repeat rewrite <- app_assoc.
        reflexivity.
      - destruct H11 as [l0 [H11 H12]].
        apply equal_app in H12.
        destruct H12 as [H12 | H12].
        + destruct H12 as [l1 [H12 H13]].
          rewrite H12 in H11.
          rewrite H11.
          exists l,(l1++z).
          repeat rewrite <- app_assoc.
          reflexivity.
        + destruct H12 as [l1 [H12 H13]].
          destruct l0,l1.
          * inversion H12.
          * inversion H12.
            rewrite H13.
            rewrite <- H0.
            exists y,s.
            reflexivity.
          * inversion H12.
            rewrite H11.
            rewrite <- H0.
            exists l,z.
            rewrite app_nil_r.
            repeat rewrite app_assoc.
            reflexivity.
          * inversion H12.
            rewrite H11, H13.
            rewrite <- H0.
            exists l,s.
            change (l ++ (b :: l0 ++ t0 :: l1) ++ s) with (l ++ ((b :: l0) ++ (t0 :: l1)) ++ s).
            repeat rewrite <- app_assoc. 
            reflexivity.
      }
    * destruct H7 as [l [H10 H11]].
      apply equal_app in H11.
      {
      destruct H11 as [H11 | H11].
      - destruct H11 as [l0 [H11 H12]].
        rewrite H11 in H10.
        rewrite <- H2 in H1.
        apply length_na_only_a in H1.
        rewrite H10 in H1.
        apply only_a_cat in H1.
        destruct H1 as [_ H1].
        simpl in H1.
        contradiction.
      - destruct H11 as [l0 [H11 H12]].
        destruct l,l0.
        + inversion H11.
        + inversion H11.
          rewrite H12.
          rewrite <- H0.
          exists [],s.
          simpl.
          reflexivity.
        + inversion H11.
          rewrite <- H0 in H10.
          rewrite <- H2 in H1.
          apply length_na_only_a in H1.
          rewrite H10 in H1.
          apply only_a_cat in H1.
          destruct H1 as [_ H1].
          simpl in H1.
          contradiction.
        + inversion H11.
          rewrite <- H0 in H10.
          rewrite <- H2 in H1.
          apply length_na_only_a in H1.
          rewrite H10 in H1.
          apply only_a_cat in H1.
          destruct H1 as [_ H1].
          simpl in H1.
          contradiction.
      }
  + right.
    unfold sublist in H7.
    destruct H7 as [p [s H7]].
    apply equal_app in H7.
    destruct H7 as [H7 | H7].
    * destruct H7 as [l [H10 H11]].
      apply equal_app in H11.
      {
      destruct H11 as [H11 | H11].
      - destruct H11 as [l0 [H11 H12]].
        apply sublist_cat_l.
        exists l0, s.
        exact H12.
      - destruct H11 as [l0 [H11 H12]].
        apply equal_app in H12.
        destruct H12 as [H12 | H12].
        + destruct H12 as [l1 [H12 H13]].
          rewrite <- H4 in H3.
          apply length_nb_only_b in H3.
          rewrite H12 in H11.
          rewrite H11 in H3.
          apply only_b_cat in H3.
          destruct H3 as [_ H3].
          simpl in H3.
          contradiction.
        + destruct H12 as [l1 [H12 H13]].
          destruct l0,l1.
          * inversion H12.
          * inversion H12.
            apply sublist_cat_l.
            exists [],s.
            rewrite H0, H13.
            reflexivity.
          * inversion H12.
            rewrite <- H0 in H11.
            rewrite <- H4 in H3.
            apply length_nb_only_b in H3.
            rewrite H11 in H3.
            apply only_b_cat in H3.
            destruct H3 as [_ H3].
            simpl in H3.
            contradiction.
          * inversion H12.
            rewrite <- H0 in H11.
            rewrite <- H4 in H3.
            apply length_nb_only_b in H3.
            rewrite H11 in H3.
            apply only_b_cat in H3.
            destruct H3 as [_ H3].
            simpl in H3.
            contradiction.
      }  
    * destruct H7 as [l [H10 H11]].
      apply equal_app in H11.
      {
      destruct H11 as [H11 | H11].
      - destruct H11 as [l0 [H11 H12]].
        rewrite <- H2 in H1.
        apply length_na_only_a in H1.
        rewrite H10 in H1.
        apply only_a_cat in H1.
        destruct H1 as [_ H1].
        rewrite H11 in H1.
        simpl in H1.
        contradiction.
      - destruct H11 as [l0 [H11 H12]].
        apply equal_app in H12.
        destruct H12 as [H12 | H12].
        + destruct H12 as [l1 [H12 H13]].
          destruct l,l0.
          * inversion H11.
          * inversion H11.
            {
            destruct y,l1.
            - inversion H12.
            - inversion H12.
              rewrite <- H14 in H13.
              rewrite <- H0 in H13.
              rewrite H13.
              exists [],s.
              reflexivity.
            - inversion H12.
              rewrite <- H14.
              rewrite <- H0.
              exists [],z.
              simpl.
              rewrite app_nil_r.
              reflexivity.
            - inversion H12.
              rewrite H13.
              rewrite <- H14.
              rewrite <- H0.
              exists [],s.
              simpl. 
              repeat rewrite <- app_assoc. 
              reflexivity.
            }
          * inversion H11.
            rewrite <- H2 in H1.
            apply length_na_only_a in H1.
            rewrite H10 in H1.
            rewrite <- H0 in H1.
            apply only_a_cat in H1.
            destruct H1 as [_ H1].
            simpl in H1.
            contradiction.
          * inversion H11.
            rewrite <- H2 in H1.
            apply length_na_only_a in H1.
            rewrite H10 in H1.
            rewrite <- H0 in H1.
            apply only_a_cat in H1.
            destruct H1 as [_ H1].
            simpl in H1.
            contradiction.
        + destruct H12 as [l1 [H12 H13]].
          destruct l,l0.
          * inversion H11.
          * inversion H11.
            rewrite <- H0 in H12.
            rewrite <- H4 in H3.
            apply length_nb_only_b in H3.
            rewrite H12 in H3.
            simpl in H3.
            contradiction.
          * inversion H11.
            rewrite <- H0 in H10.
            rewrite <- H2 in H1.
            apply length_na_only_a in H1.
            rewrite H10 in H1.
            apply only_a_cat in H1.
            destruct H1 as [_ H1].
            simpl in H1.
            contradiction.
          * inversion H11.
            rewrite <- H0 in H10.
            rewrite <- H2 in H1.
            apply length_na_only_a in H1.
            rewrite H10 in H1.
            apply only_a_cat in H1.
            destruct H1 as [_ H1].
            simpl in H1.
            contradiction.
      }   
Qed.

Lemma sublist_only_a_b:
forall s1 s2 m: list terminal,
only_a s1 ->
only_b s2 ->
sublist (s1 ++ s2) m ->
only_a_b m.
Proof.
intros s1 s2 m H1 H2 H3.
destruct m.
- exists [],[].
  simpl.
  auto.
- destruct t.
  + destruct H3 as [w1 [w2 H3]].
    apply equal_app in H3.
    destruct H3 as [H3 | H3].
    * destruct H3 as [l [H3 H4]].
      rewrite H4 in H2.
      apply only_b_cat in H2.
      destruct H2 as [_ H2].
      simpl in H2.
      contradiction.
    * destruct H3 as [l [H3 H4]].
      {
      apply equal_app in H4.
      destruct H4 as [H4 | H4].
      - destruct H4 as [l0 [H4 H5]].
        exists (a :: m),[].
        split.
        + rewrite app_nil_r.
          reflexivity.
        + split.
          * simpl.
            rewrite H4 in H3.
            rewrite H3 in H1.
            apply only_a_cat in H1.
            destruct H1 as [_ H1].
            apply only_a_cat in H1.
            destruct H1 as [H1 _].
            simpl in H1.
            exact H1.
          * simpl.
            auto.
      - destruct H4 as [l0 [H4 H5]].
        destruct l,l0.
        + inversion H4.
        + inversion H4.
          rewrite <- H0 in H5.
          rewrite H5 in H2.
          simpl in H2.
          contradiction.
        + inversion H4.
          rewrite app_nil_r.
          exists (a :: l),[].
          split.
          * rewrite app_nil_r.
            reflexivity.
          * {
            split.
            - rewrite <- H0 in H3.
              rewrite H3 in H1.
              apply only_a_cat in H1.
              apply H1.
            - simpl.
              auto.
            }
        + inversion H4.
          exists (a :: l),(t0 :: l0).
          split.
          * reflexivity.
          * {
            split.
            - rewrite <- H0 in H3.
              rewrite H3 in H1.
              apply only_a_cat in H1.
              apply H1.
            - rewrite H5 in H2.
              apply only_b_cat in H2.
              apply H2.
            }
      }  
  + destruct H3 as [w1 [w2 H3]].
    apply equal_app in H3.
    destruct H3 as [H3 | H3].
    * destruct H3 as [l [H3 H4]].
      exists [],(b :: m).
      {
      split.
      - simpl.
        reflexivity.
      - split.
        + simpl.
          auto.
        + simpl.
          rewrite H4 in H2.
          apply only_b_cat in H2.
          destruct H2 as [_ H2].
          apply only_b_cat in H2.
          destruct H2 as [H2 _].
          simpl in H2.
          exact H2.
      }
    * destruct H3 as [l [H3 H4]].
      apply equal_app in H4.
      {
      destruct H4 as [H4 | H4].
      - destruct H4 as [l0 [H4 H5]].
        rewrite H4 in H3.
        rewrite H3 in H1.
        apply only_a_cat in H1.
        destruct H1 as [_ H1].
        simpl in H1.
        contradiction.
      - destruct H4 as [l0 [H4 H5]].
        destruct l,l0.
        + inversion H4.
        + inversion H4.
          rewrite <- H0 in H5.
          rewrite H5 in H2.
          apply only_b_cat in H2.
          destruct H2 as [H2 _].
          apply only_b_only_a_b.
          exact H2.
        + inversion H4.
          rewrite <- H0 in H3.
          rewrite H3 in H1.
          apply only_a_cat in H1.
          destruct H1 as [_ H1].
          simpl in H1.
          contradiction.
        + inversion H4.
          rewrite <- H0 in H3.
          rewrite H3 in H1.
          apply only_a_cat in H1.
          destruct H1 as [_ H1].
          simpl in H1.
          contradiction.
      }
  + destruct H3 as [w1 [w2 H3]].
    apply equal_app in H3.
    destruct H3 as [H3 | H3].
    * destruct H3 as [l [H3 H4]].
      rewrite H4 in H2.
      apply only_b_cat in H2.
      destruct H2 as [_ H2].
      simpl in H2.
      contradiction.
    * destruct H3 as [l [H3 H4]].
      apply equal_app in H4.
      {
      destruct H4 as [H4 | H4].
      - destruct H4 as [l0 [H4 H5]].
        rewrite H4 in H3.
        rewrite H3 in H1.
        apply only_a_cat in H1.
        destruct H1 as [_ H1].
        simpl in H1.
        contradiction.
      - destruct H4 as [l0 [H4 H5]].
        destruct l,l0.
        + inversion H4.
        + inversion H4.
          rewrite <- H0 in H5.
          rewrite H5 in H2.
          apply only_b_cat in H2.
          destruct H2 as [H2 _].
          simpl in H2.
          contradiction.
        + inversion H4.
          rewrite <- H0 in H3.
          rewrite H3 in H1.
          apply only_a_cat in H1.
          destruct H1 as [_ H1].
          simpl in H1.
          contradiction.
        + inversion H4.
          rewrite <- H0 in H3.
          rewrite H3 in H1.
          apply only_a_cat in H1.
          destruct H1 as [_ H1].
          simpl in H1.
          contradiction.
      }
Qed.

Lemma sublist_only_b_c:
forall s1 s2 m: list terminal,
only_b s1 ->
only_c s2 ->
sublist (s1 ++ s2) m ->
only_b_c m.
Proof.
intros s1 s2 m H1 H2 H3.
destruct m.
- exists [],[].
  simpl.
  auto.
- destruct t.
  + destruct H3 as [w1 [w2 H3]].
    apply equal_app in H3.
    destruct H3 as [H3 | H3].
    * destruct H3 as [l [H3 H4]].
      rewrite H4 in H2.
      apply only_c_cat in H2.
      destruct H2 as [_ H2].
      simpl in H2.
      contradiction.
    * destruct H3 as [l [H3 H4]].
      apply equal_app in H4.
      {
      destruct H4 as [H4 | H4].
      - destruct H4 as [l0 [H4 H5]].
        rewrite H4 in H3.
        rewrite H3 in H1.
        apply only_b_cat in H1.
        destruct H1 as [_ H1].
        simpl in H1.
        contradiction.
      - destruct H4 as [l0 [H4 H5]].
        destruct l,l0.
        + inversion H4.
        + inversion H4.
          rewrite <- H0 in H5.
          rewrite H5 in H2.
          apply only_c_cat in H2.
          destruct H2 as [H2 _].
          simpl in H2.
          contradiction.
        + inversion H4.
          rewrite <- H0 in H3.
          rewrite H3 in H1.
          apply only_b_cat in H1.
          destruct H1 as [_ H1].
          simpl in H1.
          contradiction.
        + inversion H4.
          rewrite <- H0 in H3.
          rewrite H3 in H1.
          apply only_b_cat in H1.
          destruct H1 as [_ H1].
          simpl in H1.
          contradiction.
      }
  + destruct H3 as [w1 [w2 H3]].
    apply equal_app in H3.
    destruct H3 as [H3 | H3].
    * destruct H3 as [l [H3 H4]].
      rewrite H4 in H2.
      apply only_c_cat in H2.
      destruct H2 as [_ H2].
      simpl in H2.
      contradiction.
    * destruct H3 as [l [H3 H4]].
      {
      apply equal_app in H4.
      destruct H4 as [H4 | H4].
      - destruct H4 as [l0 [H4 H5]].
        exists (b :: m),[].
        split.
        + rewrite app_nil_r.
          reflexivity.
        + split.
          * simpl.
            rewrite H4 in H3.
            rewrite H3 in H1.
            apply only_b_cat in H1.
            destruct H1 as [_ H1].
            apply only_b_cat in H1.
            destruct H1 as [H1 _].
            simpl in H1.
            exact H1.
          * simpl.
            auto.
      - destruct H4 as [l0 [H4 H5]].
        destruct l,l0.
        + inversion H4.
        + inversion H4.
          rewrite <- H0 in H5.
          rewrite H5 in H2.
          simpl in H2.
          contradiction.
        + inversion H4.
          rewrite app_nil_r.
          exists (b :: l),[].
          split.
          * rewrite app_nil_r.
            reflexivity.
          * {
            split.
            - rewrite <- H0 in H3.
              rewrite H3 in H1.
              apply only_b_cat in H1.
              apply H1.
            - simpl.
              auto.
            }
        + inversion H4.
          exists (b :: l),(t0 :: l0).
          split.
          * reflexivity.
          * {
            split.
            - rewrite <- H0 in H3.
              rewrite H3 in H1.
              apply only_b_cat in H1.
              apply H1.
            - rewrite H5 in H2.
              apply only_c_cat in H2.
              apply H2.
            }
      }  
  + destruct H3 as [w1 [w2 H3]].
    apply equal_app in H3.
    destruct H3 as [H3 | H3].
    * destruct H3 as [l [H3 H4]].
      exists [],(c :: m).
      {
      split.
      - simpl.
        reflexivity.
      - split.
        + simpl.
          auto.
        + simpl.
          rewrite H4 in H2.
          apply only_c_cat in H2.
          destruct H2 as [_ H2].
          apply only_c_cat in H2.
          destruct H2 as [H2 _].
          simpl in H2.
          exact H2.
      }
    * destruct H3 as [l [H3 H4]].
      apply equal_app in H4.
      {
      destruct H4 as [H4 | H4].
      - destruct H4 as [l0 [H4 H5]].
        rewrite H4 in H3.
        rewrite H3 in H1.
        apply only_b_cat in H1.
        destruct H1 as [_ H1].
        simpl in H1.
        contradiction.
      - destruct H4 as [l0 [H4 H5]].
        destruct l,l0.
        + inversion H4.
        + inversion H4.
          rewrite <- H0 in H5.
          rewrite H5 in H2.
          apply only_c_cat in H2.
          destruct H2 as [H2 _].
          apply only_c_only_b_c.
          exact H2.
        + inversion H4.
          rewrite <- H0 in H3.
          rewrite H3 in H1.
          apply only_b_cat in H1.
          destruct H1 as [_ H1].
          simpl in H1.
          contradiction.
        + inversion H4.
          rewrite <- H0 in H3.
          rewrite H3 in H1.
          apply only_b_cat in H1.
          destruct H1 as [_ H1].
          simpl in H1.
          contradiction.
      }
Qed.

Lemma not_cfl_anbncn: ~ cfl anbncn.
Proof.
intros H1.
assert (H2: contains_empty anbncn).
  {
  unfold contains_empty.
  unfold anbncn.
  exists [], [], [], 0.
  simpl.
  split.
  - reflexivity.
  - omega.
  }
assert (H3: contains_non_empty anbncn).
  {
  unfold contains_non_empty.
  exists [a;b;c].
  unfold anbncn.
  split.
  - exists [a], [b], [c], 1.
    split.
    + reflexivity.
    + split.
      * simpl.
        reflexivity.
      * {
        split.
        - simpl.
          reflexivity.
        - split.
          + simpl.
            reflexivity. 
          + split.
            * simpl.
              reflexivity.
            * {
              split.
              - simpl.
                reflexivity.
              - simpl.
                reflexivity.
              }
        }
  - intros H3. 
    inversion H3.
  }
apply pumping_lemma in H1. 
- destruct H1 as [n H1]. 
  assert (H4: exists (s: list terminal), (length s = 3*n) /\ anbncn s).
    {
    apply sentence_exists.
    }
  destruct H4 as [s [H4 H5]].
  assert (H6: length s >= n) by omega.
  specialize (H1 s H5 H6).
  destruct H1 as [u [v [w [x [y [H11 [H12 [H13 [H14 H15]]]]]]]]].
  clear H2 H3 H6.
  assert (H5':= H5).
  unfold anbncn in H5.
  destruct H5 as [s1 [s2 [s3 [i [H21 [H22 [H23 [H24 [H25 [H26 H27]]]]]]]]]].
  assert (H28:= H21). 
  apply length_split_3 with (n:=n) (i:=i) in H21.
  + rewrite <- H21 in H22, H23, H24, H25, H26, H27.
    clear H21.
    assert (H30: only_a_b (v++w++x) \/ only_b_c (v++w++x)).
      {
      replace (u++v++w++x++y) with (u++(v++w++x)++y) in H11.
      - remember (v++w++x) as m.
        assert (H99: sublist (s1++s2++s3) m).
          {
          rewrite <- H28.
          rewrite H11.
          exists u,y.
          reflexivity.
          }
        apply sublist_or with (i:=n) in H99.
        + destruct H99 as [H99 | H99].
          * left.
            {
            apply sublist_only_a_b in H99.
            - exact H99.
            - apply length_na_only_a.
              rewrite H22, H23.
              reflexivity.
            - apply length_nb_only_b.
              rewrite H24, H25.
              reflexivity.
            }
          * right.
            {
            apply sublist_only_b_c in H99.
            - exact H99.
            - apply length_nb_only_b.
              rewrite H24, H25.
              reflexivity.
            - apply length_nc_only_c.
              rewrite H26, H27.
              reflexivity.
            }
        + exact H22.
        + exact H23.
        + exact H24.
        + exact H25.
        + exact H26.
        + exact H27.
        + rewrite Heqm. 
          repeat rewrite app_length. 
          repeat rewrite app_length in H12.
          omega.
        + exact H14.
      - repeat rewrite <- app_assoc.
        reflexivity.
      }
    assert (H40: v++x<>[]).
      {
      apply length_not_zero in H12. 
      apply not_eq_sym. 
      exact H12. 
      }
    assert (H41: v<>[] \/ x<>[]).
      {
      apply app_not_nil in H40. 
      exact H40. 
      }
    destruct H30 as [H30 | H30].
    * (* only_a_b (v++w++x) *)
      {
      destruct H41 as [H41 | H41].
      - (* v <> [] *)
        assert (H30':= H30).
        apply only_a_b_cat_l in H30.
        + specialize (H15 2).
          simpl in H15.
          repeat rewrite app_nil_r in H15.
          rewrite H11 in H5'.
          apply na_eq_nb_eq_nc in H15. 
          apply na_eq_nb_eq_nc in H5'. 
          destruct H15 as [H15 H15'].
          destruct H5' as [H5' H5''].    
          assert (H31: nc v = 0 /\ nc w = 0 /\ nc x = 0).
            {
            apply only_a_b_nc in H30'. 
            repeat rewrite nc_cat in H30'.
            omega. 
            }
          destruct H31 as [H31 [H32 H33]].
          destruct H30 as [H30 | H30].
          * (* na v > 0 *)
            rewrite H15' in H15.
            repeat rewrite na_cat in H15.
            repeat rewrite nc_cat in H15.
            rewrite H5'' in H5'.
            repeat rewrite na_cat in H5'.
            repeat rewrite nc_cat in H5'.
            clear H15' H5''.
            rewrite H31, H32, H33 in H15.
            simpl in H15.
            rewrite H31, H32, H33 in H5'.
            simpl in H5'.
            rewrite <- H5' in H15.
            omega.
          * (* nb v > 0 *)
            repeat rewrite nb_cat in H15'.
            repeat rewrite nc_cat in H15'.
            repeat rewrite nb_cat in H5''.
            repeat rewrite nc_cat in H5''.
            rewrite H31, H32, H33 in H15'.
            simpl in H15'.
            rewrite H31, H32, H33 in H5''.
            simpl in H5''.
            rewrite <- H5'' in H15'.
            omega.
        + exact H41.
      - (* x <> [] *)
        assert (H30':= H30).
        rewrite app_assoc in H30.
        apply only_a_b_cat_r in H30.
        + specialize (H15 2).
          simpl in H15.
          repeat rewrite app_nil_r in H15.
          rewrite H11 in H5'.
          apply na_eq_nb_eq_nc in H15. 
          apply na_eq_nb_eq_nc in H5'. 
          destruct H15 as [H15 H15'].
          destruct H5' as [H5' H5''].    
          assert (H31: nc v = 0 /\ nc w = 0 /\ nc x = 0).
            {
            apply only_a_b_nc in H30'. 
            repeat rewrite nc_cat in H30'.
            omega. 
            }
          destruct H31 as [H31 [H32 H33]].
          destruct H30 as [H30 | H30].
          * (* na x > 0 *)
            rewrite H15' in H15.
            repeat rewrite na_cat in H15.
            repeat rewrite nc_cat in H15.
            rewrite H5'' in H5'.
            repeat rewrite na_cat in H5'.
            repeat rewrite nc_cat in H5'.
            rewrite H31, H32, H33 in H15.
            simpl in H15.
            rewrite H31, H32, H33 in H5'.
            simpl in H5'.
            rewrite <- H5' in H15.
            omega.
          * (* nb x > 0 *)
            repeat rewrite nb_cat in H15'.
            repeat rewrite nc_cat in H15'.
            repeat rewrite nb_cat in H5''.
            repeat rewrite nc_cat in H5''.
            rewrite H31, H32, H33 in H15'.
            simpl in H15'.
            rewrite H31, H32, H33 in H5''.
            simpl in H5''.
            rewrite <- H5'' in H15'.
            omega.
        + exact H41.
      }
    * (* only_b_c (v++w++x) *)
      {
      destruct H41 as [H41 | H41].
      - (* v <> [] *)
        assert (H30':= H30).
        apply only_b_c_cat_l in H30.
        + specialize (H15 2).
          simpl in H15.
          repeat rewrite app_nil_r in H15.
          rewrite H11 in H5'.
          apply na_eq_nb_eq_nc in H15. 
          apply na_eq_nb_eq_nc in H5'. 
          destruct H15 as [H15 H15'].
          destruct H5' as [H5' H5''].    
          assert (H31: na v = 0 /\ na w = 0 /\ na x = 0).
            {
            apply only_b_c_na in H30'. 
            repeat rewrite na_cat in H30'.
            omega. 
            }
          destruct H31 as [H31 [H32 H33]].
          destruct H30 as [H30 | H30].
          * (* nb v > 0 *)
            repeat rewrite na_cat in H15.
            repeat rewrite nb_cat in H15.
            rewrite H31, H32, H33 in H15.
            simpl in H15.
            repeat rewrite na_cat in H5'.
            repeat rewrite nb_cat in H5'.
            rewrite H31, H32, H33 in H5'.
            simpl in H5'.
            rewrite H5' in H15.
            omega.
          * (* nc v > 0 *)
            rewrite H15' in H15. 
            rewrite H5'' in H5'.
            repeat rewrite na_cat in H15.
            repeat rewrite nc_cat in H15.
            rewrite H31, H32, H33 in H15.
            simpl in H15.
            repeat rewrite na_cat in H5'.
            repeat rewrite nc_cat in H5'.
            rewrite H31, H32, H33 in H5'.
            simpl in H5'.
            rewrite H5' in H15.
            omega.
        + exact H41.
      - (* x <> [] *)
        assert (H30':= H30).
        rewrite app_assoc in H30.
        apply only_b_c_cat_r in H30.
        + specialize (H15 2).
          simpl in H15.
          repeat rewrite app_nil_r in H15.
          rewrite H11 in H5'.
          apply na_eq_nb_eq_nc in H15. 
          apply na_eq_nb_eq_nc in H5'. 
          destruct H15 as [H15 H15'].
          destruct H5' as [H5' H5''].    
          assert (H31: na v = 0 /\ na w = 0 /\ na x = 0).
            {
            apply only_b_c_na in H30'. 
            repeat rewrite na_cat in H30'.
            omega. 
            }
          destruct H31 as [H31 [H32 H33]].
          destruct H30 as [H30 | H30].
          * (* nb x > 0 *)
            repeat rewrite na_cat in H15.
            repeat rewrite nb_cat in H15.
            rewrite H31, H32, H33 in H15.
            simpl in H15.
            repeat rewrite na_cat in H5'.
            repeat rewrite nb_cat in H5'.
            rewrite H31, H32, H33 in H5'.
            simpl in H5'.
            rewrite H5' in H15.
            omega.
          * (* nc x > 0 *)
            rewrite H15' in H15.
            repeat rewrite na_cat in H15.
            repeat rewrite nc_cat in H15.
            rewrite H31, H32, H33 in H15.
            simpl in H15.
            rewrite H5'' in H5'.
            repeat rewrite na_cat in H5'.
            repeat rewrite nc_cat in H5'.
            rewrite H31, H32, H33 in H5'.
            simpl in H5'.
            rewrite H5' in H15.
            omega.
        + exact H41.
      } 
  + exact H4.
  + exact H22.
  + exact H24.
  + exact H26.
- split.
  + left.
    exact H2.
  + left.
    exact H3.
Qed.

End Pumping_Example.