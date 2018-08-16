(* ---------------------------------------------------------------------

   This file is part of a repository containing the definitions and 
   proof scripts related to the formalization of context-free language
   theory in Coq. Specifically, the following results were obtained:
   
   (i) languages square, prime and anbncn are not context-free; 
   (ii) context-free languages are not closed under intersection.
   
   More information can be found in the paper "Some Applications of the 
   Formalization of the Pumping Lemma for Context-Free Languages", 
   submitted to LSFA 2018 by Marcus Vinícius Midena Ramos, Ruy J. G. B. 
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

Require Import misc_arith.
Require Import misc_list.
Require Import cfg.
Require Import cfl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

(* --------------------------------------------------------------------- *)
(* INJECTION                                                             *)
(* --------------------------------------------------------------------- *)

Definition injective {A B: Type} (f: A->B) :=
forall x y: A, f x = f y -> x = y.

Definition bijective {A B: Type} (f: A->B) :=
{g: B->A | (forall x: A, g (f x) = x) /\ (forall y: B, f (g y) = y)}.

Definition decidable (t: Type): Type:=
(forall x y: t, {x=y}+{x<>y}).

Lemma bijective_to_injective:
forall t1 t2: Type,
forall f: t1 -> t2,
bijective f -> injective f.
Proof.
intros t1 t2 f H1.
destruct H1 as [g [H1 H2]].
intros x y H3.
rewrite <- H1.
rewrite <- H1 at 1.
rewrite H3.
reflexivity.
Qed.

Lemma bijective_dec:
forall t1 t2: Type,
forall f: t1 -> t2,
bijective f ->
decidable t1 ->
decidable t2.
Proof.
intros t1 t2 f H1 H2 x y.
assert (H1':= H1).
apply bijective_to_injective in H1'.
destruct H1 as [g [H1 H3]].
rewrite <- (H3 x).
rewrite <- (H3 y).
unfold injective in H1'.
specialize (H2 (g x) (g y)).
destruct H2 as [H2 | H2].
- rewrite H2.
  left.
  reflexivity.
- right.
  intros H4.
  specialize (H1' (g x) (g y) H4).
  contradiction. 
Qed.

Definition change_alphabet_in_language (t1 t2: Type) (l1: lang t1) (f: t1 -> t2): lang t2:=
fun (w2: list t2) =>
exists w1: list t1,
l1 w1 /\ w2 = map f w1.

Lemma change_alphabet_in_rs:
forall t1 t2 nt: Type,
forall f: (nt+t1) -> (nt+t2),
injective f ->
forall rs1: nt -> list (nt+t1) -> Prop,
exists rs2: nt -> list (nt+t2) -> Prop,
forall left: nt,
(forall right1: list (nt+t1), rs1 left right1 -> rs2 left (map f right1)) /\
(forall right2: list (nt+t2), rs2 left right2 -> exists right1: list (nt+t1), rs1 left right1 /\ right2 = (map f right1)).
Proof.
intros t1 t2 nt f H1 rs1.
unfold injective in H1. 
exists (fun (left: nt) (right: list (nt+t2)) => exists right': list (nt+t1), rs1 left right' /\ right=(map f right')).
intros left.
split.
- intros right1 H2. 
  exists right1. 
  split. 
  + exact H2.
  + reflexivity.
- intros right2 H2. 
  destruct H2 as [right' [H2 H3]]. 
  exists right'.
  split.
  + exact H2.
  + exact H3.
Qed.

Lemma f_to_f':
forall t1 t2 nt: Type,
forall f: t1 -> t2,
injective f ->
exists f': (nt+t1)->(nt+t2), 
(forall x: nt, f' (inl x) = inl x) /\ (forall y: t1, f' (inr y) = inr (f y)) /\ injective f'.
Proof.
intros t1 t2 nt f H1.
exists (fun w: (nt+t1) => match w with
                          | inl x => inl x
                          | inr y => inr (f y)
                          end).
split.
- reflexivity.
- split. 
  + intros y0.
    reflexivity.
  + unfold injective.
    intros x0 y0.
    destruct x0, y0.
    * intros H2.
      inversion H2.
      reflexivity.
    * intros H2.
      inversion H2.
    * intros H2.
      inversion H2.
    * intros H2.
      inversion H2.
      specialize (H1 t t0 H0).
      rewrite H1.
      reflexivity.
Qed.

Lemma g_to_g':
forall t1 t2 nt: Type,
forall g: t2 -> t1,
injective g ->
exists g': (nt+t2)->(nt+t1), 
(forall x: nt, g' (inl x) = inl x) /\ (forall y: t2, g' (inr y) = inr (g y)) /\ injective g'.
Proof.
intros t1 t2 nt g H1.
exists (fun w: (nt+t2) => match w with
                          | inl x => inl x
                          | inr y => inr (g y)
                          end).
split.
- reflexivity.
- split. 
  + intros y0.
    reflexivity.
  + unfold injective.
    intros x0 y0.
    destruct x0, y0.
    * intros H2.
      inversion H2.
      reflexivity.
    * intros H2.
      inversion H2.
    * intros H2.
      inversion H2.
    * intros H2.
      inversion H2.
      specialize (H1 t t0 H0).
      rewrite H1.
      reflexivity.
Qed.

Lemma change_alphabet_in_grammar:
forall t1 t2 nt: Type,
forall g1: cfg nt t1,
forall f: t1 -> t2,
bijective f ->
exists g2: cfg nt t2,
lang_of_g g2 == change_alphabet_in_language (lang_of_g g1) f.
Proof.
intros t1 t2 nt g1 f H1'.
assert (H1: injective f).
  {
  apply bijective_to_injective.
  exact H1'.
  }
assert (t1_dec: decidable t1).
  {
  exact (t_eqdec g1). 
  }
assert (nt_dec: decidable nt).
  {
  exact (nt_eqdec g1). 
  }
assert (t2_dec: decidable t2).
  {
  apply bijective_dec with (t1:=t1) (f:=f).
  - exact H1'.
  - exact t1_dec.
  }
assert (H2: exists f': (nt+t1)->(nt+t2), (forall x: nt, f' (inl x) = inl x) /\ (forall y: t1, f' (inr y) = inr (f y)) /\ injective f').
  {
  apply f_to_f'.
  exact H1.
  }
destruct H2 as [f' [H2 [H3 H4]]].
destruct H1' as [g [H1' H1'']].
assert (H2': injective g).
  {
  unfold injective.
  intros x y H.
  rewrite <- H1''.
  rewrite <- H1'' at 1.
  rewrite H.
  reflexivity.
  }
assert (H3': exists g': (nt+t2)->(nt+t1), (forall x: nt, g' (inl x) = inl x) /\ (forall y: t2, g' (inr y) = inr (g y)) /\ injective g').
  {
  apply g_to_g'.
  exact H2'.
  }
destruct H3' as [g' [H5' [H6' H7']]].
apply change_alphabet_in_rs with (rs1:=(rules g1)) in H4.
destruct H4 as [rs2 H4]. 
assert (H5: exists n: nat,
            exists ntl: list nt,
            exists tl: list t2,
            In (start_symbol g1) ntl /\
            forall left: nt,
            forall right: list (nt+t2),
            rs2 left right ->
            (length right <= n) /\
            (In left ntl) /\
            (forall s: nt, In (inl s) right -> In s ntl) /\
            (forall s: t2, In (inr s) right -> In s tl)).
  {
  destruct (rules_finite g1) as [n [ntl [tl H5]]].
  exists n, ntl.
  exists (map f tl).
  destruct H5 as [H5 H6].
  split.
  - exact H5.
  - intros left right2 H7.
    specialize (H4 left).
    destruct H4 as [_ H4].
    specialize (H4 right2 H7).
    destruct H4 as [right1 [H4 H9]].
    specialize (H6 left right1 H4).
    destruct H6 as [H10 [H11 [H12 H13]]].
    split.
    + rewrite H9.
      rewrite map_length.
      exact H10.
    + split.
      * exact H11. 
      * {
        split.
        - intros s H20.
          rewrite H9 in H20.
          apply in_split in H20.
          destruct H20 as [l1 [l2 H20]].
          symmetry in H20.
          apply map_expand in H20.
          destruct H20 as [s1' [s2' [H20 [H21 H22]]]].
          destruct s2'.
          + simpl in H22.
            inversion H22.
          + simpl in H22.
            inversion H22.
            destruct s0.
            * specialize (H2 n0).
              rewrite H2 in H0.
              inversion H0.
              apply H12.
              rewrite <- H8, H20.
              apply in_or_app.
              right.
              simpl.
              left.
              reflexivity.
            * specialize (H3 t).
              rewrite H3 in H0.
              inversion H0.
        - intros s H20.
          rewrite H9 in H20.
          apply in_split in H20.
          destruct H20 as [l1 [l2 H20]].
          symmetry in H20.
          apply map_expand in H20.
          destruct H20 as [s1' [s2' [H20 [H21 H22]]]].
          destruct s2'.
          + simpl in H22.
            inversion H22.
          + simpl in H22.
            inversion H22.
            destruct s0.
            * specialize (H2 n0).
              rewrite H2 in H0.
              inversion H0.
            * specialize (H3 t).
              rewrite H3 in H0.
              inversion H0.
              specialize (H13 t).
              assert (H23: In (inr t) right1).
                {
                rewrite H20.
                apply in_or_app.
                right.
                simpl.
                left.
                reflexivity.
                }
              specialize (H13 H23).
              apply in_map.
              exact H13.
        }
  }
exists ({|
        start_symbol:= start_symbol g1; 
        rules:= rs2; 
        t_eqdec:= t2_dec;
        nt_eqdec:= nt_dec;
        rules_finite:= H5
        |}).
unfold lang_eq.
intros w2.
unfold lang_of_g, produces, generates.
unfold change_alphabet_in_language.
simpl.
remember {|
     start_symbol := start_symbol g1;
     rules := rs2;
     t_eqdec := t2_dec;
     nt_eqdec := nt_dec;
     rules_finite := H5 |} as g2.
split.
- intros H6.
  exists (map g w2).
  assert (HH: forall s1 s2: list (nt+t2),
              derives g2 s1 s2 -> derives g1 (map g' s1) (map g' s2)).
    {
    intros s1 s2 HH.
    induction HH.
    - apply derives_refl.
    - repeat rewrite map_app.
      apply derives_trans with (s2:=map g' s2 ++ map g' [inl left] ++ map g' s3).
      + repeat rewrite map_app in IHHH.
        exact IHHH.
      + apply derives_context_free_add.
        simpl.
        rewrite H5'. 
        specialize (H4 left).
        destruct H4 as [_ H4].
        rewrite Heqg2 in H.
        simpl in H.
        specialize (H4 right H).
        destruct H4 as [right1 [H4 H4']].
        change ([inl left]) with ([]++[@inl nt t1 left]++[]).
        replace (map g' right) with ([]++(map g' right)++[]).
        * apply derives_rule.
          rewrite H4'.
          assert (H8: (map g' (map f' right1) = right1)).
            {
            clear H4 H4'.
            induction right1.
            - simpl.
              reflexivity.
            - simpl.
              rewrite IHright1.
              destruct a.
              + rewrite H2.
                rewrite H5'.
                reflexivity.
              + rewrite H3.
                rewrite H6'.
                rewrite H1'.
                reflexivity.
            }
          rewrite H8.
          exact H4.
        * simpl. 
          rewrite app_nil_r. 
          reflexivity. 
    }
  specialize (HH [inl (start_symbol g1)] (map (terminal_lift nt (terminal:=t2)) w2) H6).
  simpl in HH.
  assert (H8: g' (inl (start_symbol g1)) = inl (start_symbol g1)).
    {
    apply H5'.
    }
  rewrite H8 in HH.
  assert (H9:  (map g' (map (terminal_lift nt (terminal:=t2)) w2)) =  (map (terminal_lift nt (terminal:=t1)) (map g w2))).
    {
    clear H6 HH.
    induction w2.
    - simpl.
      reflexivity.
    - simpl.
      rewrite IHw2.
      unfold terminal_lift.
      rewrite H6'.
      reflexivity.
    }
  split.
  + rewrite H9 in HH.
    exact HH.
  + clear H6 H9 HH. 
    induction w2.
    * simpl.
      reflexivity.
    * simpl.
      rewrite H1''.
      rewrite <- IHw2.
      reflexivity.
- intros H6.
  destruct H6 as [w1 [H6 H7]].
  assert (HH: forall s1 s2: list (nt+t1),
              derives g1 s1 s2 -> derives g2 (map f' s1) (map f' s2)).
    {
    intros s1 s2 HH. 
    induction HH.
    - apply derives_refl.
    - repeat rewrite map_app.
      apply derives_trans with (s2:=map f' s2 ++ map f' [inl left] ++ map f' s3).
      + repeat rewrite map_app in IHHH.
        exact IHHH.
      + apply derives_context_free_add.
        simpl.
        rewrite H2. 
        specialize (H4 left).
        destruct H4 as [H4 _].
        specialize (H4 right H).
        change ([inl left]) with ([]++[@inl nt t2 left]++[]).
        replace (map f' right) with ([]++(map f' right)++[]).
        * apply derives_rule.
          rewrite Heqg2.
          simpl. 
          exact H4. 
        * simpl. 
          rewrite app_nil_r. 
          reflexivity. 
    }
  specialize (HH [inl (start_symbol g1)] (map (terminal_lift nt (terminal:=t1)) w1) H6).
  simpl in HH.
  assert (H8: f' (inl (start_symbol g1)) = inl (start_symbol g1)).
    {
    apply H2.
    }
  rewrite H8 in HH.
  assert (H9:  (map f' (map (terminal_lift nt (terminal:=t1)) w1)) =  (map (terminal_lift nt (terminal:=t2)) (map f w1))).
    {
    clear H6 H7 HH.
    induction w1.
    - simpl.
      reflexivity.
    - simpl.
      rewrite IHw1.
      unfold terminal_lift.
      rewrite H3.
      reflexivity.
    }
  rewrite H7.
  rewrite H9 in HH.
  exact HH.
Qed.

Lemma change_alphabet_aux:
forall t1 t2 nt: Type,
forall f: t1 -> t2,
forall g1: cfg nt t1,
forall g2: cfg nt t2,
forall l1: lang t1,
l1 == lang_of_g g1 ->
lang_of_g g2 == change_alphabet_in_language (lang_of_g g1) f ->
lang_of_g g2 == change_alphabet_in_language l1 f.
Proof.
intros t1 t2 nt f g1 g2 l1 H1 H2.
unfold lang_eq.
unfold lang_eq in H2.
intros w.
split.
- intros H3.
  specialize (H2 w).
  destruct H2 as [H2 _].
  specialize (H2 H3).
  unfold change_alphabet_in_language in H2.
  unfold change_alphabet_in_language.
  destruct H2 as [w1 [H2 H4]].
  exists w1.
  split.
  + unfold lang_eq in H1. 
    specialize (H1 w1). 
    destruct H1 as [_ H1]. 
    specialize (H1 H2). 
    exact H1. 
  + exact H4.
- intros H3.
  specialize (H2 w).
  destruct H2 as [_ H2].
  apply H2.
  unfold change_alphabet_in_language in H3.
  unfold change_alphabet_in_language.
  destruct H3 as [w1 [H3 H4]].
  exists w1.
  split.
  + unfold lang_eq in H1.
    specialize (H1 w1). 
    destruct H1 as [H1 _]. 
    specialize (H1 H3). 
    exact H1.
  + exact H4.
Qed.

Lemma change_alphabet_in_language_is_cfl:
forall t1 t2: Type,
forall l1: lang t1,
forall f: t1 -> t2,
cfl l1 ->
bijective f ->
cfl (change_alphabet_in_language l1 f).
Proof.
intros t1 t2 l1 f H1 H2'.
destruct H1 as [nt [g1 H1]].
assert (H2: injective f).
  {
  apply bijective_to_injective.
  exact H2'.
  }
assert (H3: decidable t2).
  {
  apply bijective_dec with (t1:=t1) (f:=f). 
  - exact H2'.
  - unfold decidable. 
    apply (t_eqdec g1).
  }
unfold cfl.
unfold injective in H2.
exists nt.
assert (H4: exists g2: cfg nt t2,
            lang_of_g g2 == change_alphabet_in_language (lang_of_g g1) f).
  {
  apply change_alphabet_in_grammar.
  exact H2'.
  }
destruct H4 as [g2 H4].
exists g2. 
apply lang_eq_sym.
apply change_alphabet_aux with (g1:= g1).
- exact H1.
- exact H4.
Qed.
