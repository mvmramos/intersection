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
Require Import concatenation.
Require Import cfg.
Require Import cfl.
Require Import pumping.
Require Import pumping_anbncn.
Require Import bijection.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

(* --------------------------------------------------------------------- *)
(* INTERSECTION                                                          *)
(* --------------------------------------------------------------------- *)

Lemma in_a:
forall t: terminal,
forall w: list terminal,
In t w ->
only_a w ->
t=a.
Proof.
intros t w H1 H2.
apply in_split in H1.
destruct H1 as [l1 [l2 H1]].
rewrite H1 in H2.
apply only_a_cat in H2.
destruct H2 as [_ H2].
destruct t.
- reflexivity.
- simpl in H2.
  contradiction.
- simpl in H2.
  contradiction.
Qed.

Lemma in_b:
forall t: terminal,
forall w: list terminal,
In t w ->
only_b w ->
t=b.
Proof.
intros t w H1 H2.
apply in_split in H1.
destruct H1 as [l1 [l2 H1]].
rewrite H1 in H2.
apply only_b_cat in H2.
destruct H2 as [_ H2].
destruct t.
- simpl in H2.
  contradiction.
- reflexivity.
- simpl in H2.
  contradiction.
Qed.

Lemma in_c:
forall t: terminal,
forall w: list terminal,
In t w ->
only_c w ->
t=c.
Proof.
intros t w H1 H2.
apply in_split in H1.
destruct H1 as [l1 [l2 H1]].
rewrite H1 in H2.
apply only_c_cat in H2.
destruct H2 as [_ H2].
destruct t.
- simpl in H2.
  contradiction.
- simpl in H2.
  contradiction.
- reflexivity.
Qed.

Lemma length_nc_eq:
forall z1 z2: list terminal,
length z1 = nc z1 ->
length z2 = nc z2 ->
length z1 = length z2 ->
z1 = z2.
Proof.
induction z1.
- intros z2 _ H1 H2.
  simpl in H2.
  symmetry in H2.
  apply length_zero in H2.
  symmetry.
  exact H2.
- intros z2 H1 H2 H3.
  destruct a.
  + simpl in H1.
    assert (H4: length z1 >= nc z1).
      { 
      apply length_nc.
      }
    omega.
  + simpl in H1.
    assert (H4: length z1 >= nc z1).
      { 
      apply length_nc.
      }
    omega.
  + destruct z2. 
    * simpl in H3. 
      omega. 
    * {
      destruct t.
      - simpl in H2. 
        assert (H4: length z2 >= nc z2). 
          {
          apply length_nc.
          }
        omega.
      - simpl in H2. 
        assert (H4: length z2 >= nc z2). 
          {
          apply length_nc.
          }
        omega.
      - specialize (IHz1 z2).
        simpl in H1, H2, H3.
        assert (H4: length z1 = nc z1) by omega.
        assert (H5: length z2 = nc z2) by omega.
        assert (H6: length z1 = length z2) by omega.
        specialize (IHz1 H4 H5 H6).
        rewrite IHz1.
        reflexivity.
      } 
Qed.

Section Intersection.

Inductive l_int (l1 l2: lang terminal): lang terminal:=
| l_int_c: forall s: list terminal, l1 s -> l2 s -> l_int l1 l2 s.

Lemma t_ed:
forall x y : terminal, {x = y} + {x <> y}.
Proof.
intros x y.
destruct x, y. 
- left; reflexivity. 
- right; intros H; inversion H.
- right; intros H; inversion H.
- right; intros H; inversion H.
- left; reflexivity. 
- right; intros H; inversion H.
- right; intros H; inversion H.
- right; intros H; inversion H.
- left; reflexivity. 
Qed.

Inductive non_terminal: Type:=
| S
| A
| X
| Y.

Lemma nt_ed:
forall x y : non_terminal, {x = y} + {x <> y}.
Proof.
intros x y.
destruct x, y.
- left; reflexivity. 
- right; intros H; inversion H.
- right; intros H; inversion H.
- right; intros H; inversion H.
- right; intros H; inversion H.
- left; reflexivity. 
- right; intros H; inversion H.
- right; intros H; inversion H.
- right; intros H; inversion H.
- right; intros H; inversion H.
- left; reflexivity. 
- right; intros H; inversion H.
- right; intros H; inversion H.
- right; intros H; inversion H.
- right; intros H; inversion H.
- left; reflexivity. 
Qed.

Notation sf := (list (non_terminal + terminal)).
Notation sentence := (list terminal).
Notation nlist:= (list non_terminal).
Notation tlist:= (list terminal).

Inductive rs_ambm: non_terminal -> sf -> Prop:=
  r11: rs_ambm S [inr a; inl S; inr b]
| r12: rs_ambm S [].

Lemma rs_ambm_finite:
exists n: nat,
exists ntl: nlist,
exists tl: tlist,
In S ntl /\
forall left: non_terminal,
forall right: sf,
rs_ambm left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: non_terminal, In (inl s) right -> In s ntl) /\
(forall s: terminal, In (inr s) right -> In s tl).
Proof.
exists 3.
exists [S; A; X; Y].
exists [a; b; c].
split.
- simpl.
  left.
  reflexivity.
- intros left right H1.
  split.
  + inversion H1.
    * simpl.
      omega.
    * simpl.
      omega.
  + inversion H1.
    * {
      split.
      - simpl.
        left.
        reflexivity.
      - split.
        + intros s H2.
          destruct s.
          * simpl. 
            left.
            reflexivity.
          * simpl. 
            right.
            left.
            reflexivity.
          * simpl. 
            right.
            right.
            left.
            reflexivity.
          * simpl. 
            right.
            right.
            right.
            left.
            reflexivity.
        + intros s H2.
          destruct s.
          * simpl. 
            left.
            reflexivity.
          * simpl.
            right.
            left.
            reflexivity.
          * simpl.
            right.
            right.
            left.
            reflexivity.
      }
    * {
      split.
      - simpl.
        left.
        reflexivity.
      - split.
        + intros s H2.
          simpl in H2.
          contradiction. 
        + intros s H2.
          simpl in H2.
          contradiction. 
      }
Qed.

Definition g_ambm: cfg _ _:= {|
start_symbol:= S; 
rules:= rs_ambm;
t_eqdec:= t_ed;
nt_eqdec:= nt_ed;
rules_finite:= rs_ambm_finite
|}.

Inductive rs_cn: non_terminal -> sf -> Prop:=
  r21: rs_cn S [inr c; inl S]
| r22: rs_cn S [].

Lemma rs_cn_finite:
exists n: nat,
exists ntl: nlist,
exists tl: tlist,
In S ntl /\
forall left: non_terminal,
forall right: sf,
rs_cn left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: non_terminal, In (inl s) right -> In s ntl) /\
(forall s: terminal, In (inr s) right -> In s tl).
Proof.
exists 2.
exists [S; A; X; Y].
exists [a; b; c].
split.
- simpl.
  left.
  reflexivity.
- intros left right H1.
  split.
  + inversion H1.
    * simpl.
      omega.
    * simpl.
      omega.
  + inversion H1.
    * {
      split.
      - simpl.
        left.
        reflexivity.
      - split.
        + intros s H2.
          destruct s.
          * simpl. 
            left.
            reflexivity.
          * simpl. 
            right.
            left.
            reflexivity.
          * simpl. 
            right.
            right.
            left.
            reflexivity.
          * simpl. 
            right.
            right.
            right.
            left.
            reflexivity.
        + intros s H2.
          destruct s.
          * simpl. 
            left.
            reflexivity.
          * simpl.
            right.
            left.
            reflexivity.
          * simpl.
            right.
            right.
            left.
            reflexivity.
      }
    * {
      split.
      - simpl.
        left.
        reflexivity.
      - split.
        + intros s H2.
          simpl in H2.
          contradiction. 
        + intros s H2.
          simpl in H2.
          contradiction. 
      }
Qed.

Definition g_cn: cfg _ _:= {|
start_symbol:= S; 
rules:= rs_cn;
t_eqdec:= t_ed;
nt_eqdec:= nt_ed;
rules_finite:= rs_cn_finite
|}.

Inductive ambm: list terminal -> Prop:=
| ambm_1: ambm []
| ambm_2: forall w: list terminal, ambm w -> ambm ([a]++w++[b]).

Inductive cn: list terminal -> Prop:=
| cn_1: cn []
| cn_2: forall w: list terminal, cn w -> cn ([c]++w).

Lemma app_cn:
forall s1 s2: list terminal,
cn (s1 ++ s2) ->
cn s1 /\ cn s2.
Proof.
intros s1 s2 H1.
remember (s1 ++ s2) as s.
revert s1 s2 Heqs.
induction H1.
- intros s1 s2 H1. 
  symmetry in H1. 
  apply app_eq_nil in H1.
  destruct H1 as [H1 H2].  
  rewrite H1, H2. 
  split.
  + apply cn_1.
  + apply cn_1.
- intros s1 s2 H2.
  destruct s1, s2.
  + inversion H2.
  + inversion H2.
    specialize (IHcn [] s2 H3).
    split.
    * apply IHcn.
    * apply cn_2.
      apply IHcn.
  + inversion H2.
    specialize (IHcn s1 [] H3).
    split.
    * apply cn_2.
      apply IHcn.
    * apply cn_1.
  + inversion H2.
    specialize (IHcn s1 (t0::s2) H3).
    split.
    * apply cn_2.
      apply IHcn.
    * apply IHcn.
Qed.

Definition f (t1: terminal): terminal:=
match t1 with
| a => b
| b => c
| c => a
end.

Lemma injective_f:
injective f.
Proof.
unfold injective.
intros x y H1.
destruct x, y.
- reflexivity.
- simpl in H1; inversion H1.
- simpl in H1; inversion H1.
- simpl in H1; inversion H1.
- reflexivity.
- simpl in H1; inversion H1.
- simpl in H1; inversion H1.
- simpl in H1; inversion H1.
- reflexivity.
Qed.

Definition g (t1: terminal): terminal:=
match t1 with
| b => a
| c => b
| a => c
end.

Lemma bijective_f:
bijective f.
Proof.
unfold bijective.
exists g.
split.
- destruct x.
  + simpl; reflexivity.
  + simpl; reflexivity.
  + simpl; reflexivity.
- destruct y.
  + simpl; reflexivity.
  + simpl; reflexivity.
  + simpl; reflexivity.
Qed.

Inductive an: list terminal -> Prop:=
| an_1: an []
| an_2: forall w: list terminal, an w -> an ([a]++w).

Definition an':= change_alphabet_in_language cn f.

Lemma an_equiv_an':
an == an'.
Proof.
unfold lang_eq.
intros w.
split.
- intros H1.
  induction H1.
  + unfold an'.
    exists [].
    split.
    * apply cn_1.
    * simpl.
      reflexivity.
  + unfold an'.
    unfold an' in IHan.
    destruct IHan as [w1 [H2 H3]].
    exists ([c]++w1).
    split.
    * apply cn_2.
      exact H2.
    * rewrite H3.
      simpl.
      reflexivity.
- intros H1.
  destruct H1 as [w1 [H2 H3]].
  rewrite H3.
  clear w H3.
  induction H2.
  + simpl.
    apply an_1.
  + rewrite map_app.
    simpl.
    apply an_2.
    exact IHcn.
Qed.

Inductive bmcm: list terminal -> Prop:=
| bmcm_1: bmcm []
| bmcm_2: forall w: list terminal, bmcm w -> bmcm ([b]++w++[c]).

Definition bmcm':= change_alphabet_in_language ambm f.

Lemma bmcm_equiv_bmcm':
bmcm == bmcm'.
Proof.
intros w.
split.
- intros H1.
  induction H1.
  + exists [].
    split.
    * apply ambm_1.
    * simpl.
      reflexivity.
  + destruct IHbmcm as [w1 [H2 H3]].
    exists ([a]++w1++[b]).
    split.
    * apply ambm_2.
      exact H2.
    * rewrite H3. 
      repeat rewrite map_app.
      simpl.
      reflexivity.
- intros H1.
  destruct H1 as [w1 [H2 H3]].
  rewrite H3.
  clear w H3.
  induction H2.
  + simpl.
    apply bmcm_1.
  + repeat rewrite map_app.
    simpl.
    change (b :: map f w ++ [c]) with ([b] ++ map f w ++ [c]).
    apply bmcm_2.
    repeat rewrite map_app in H3.
    apply IHambm.
Qed.

Definition ambmcn: lang terminal:=
fun (s: list terminal) =>
exists x y z: list terminal,
exists i: nat,
s = x ++ y ++ z /\ length x = i /\ na x = i /\ length y = i /\ nb y = i /\ length z = nc z.

Definition anbmcm: lang terminal:=
fun (s: list terminal) =>
exists x y z: list terminal,
exists i: nat,
s = x ++ y ++ z /\ length x = na x /\ length y = i /\ nb y = i /\ length z = i /\ nc z = i.

Lemma ambm_exists:
forall w: list terminal,
ambm w -> exists x: list terminal, exists y: list terminal,
w=x++y /\ length x = na x /\ length y = nb y /\ length x = length y.
Proof.
intros w H1.
induction H1.
- exists [], [].
  simpl.
  auto.
- destruct IHambm as [x [y [H2 [H3 [H4 H5]]]]].
  exists ([a]++x).
  exists (y++[b]).
  split.
  + rewrite H2.
    repeat rewrite <- app_assoc.
    reflexivity.
  + split.
    * simpl.
      omega.
    * {
      split. 
      - simpl.
        rewrite app_length.
        rewrite nb_cat.
        simpl.
        omega.
      - simpl.
        rewrite app_length.
        simpl.
        omega.
      } 
Qed.

Lemma cn_exists:
forall w: list terminal,
cn w -> length w = nc w.
Proof.
induction w.
- intros _.
  simpl.
  reflexivity.
- intros H1.
  destruct a.
  + inversion H1.
  + inversion H1.
  + inversion H1.
    specialize (IHw H0).
    simpl.
    omega.
Qed.

Lemma an_exists:
forall w: list terminal,
an w -> length w = na w.
Proof.
induction w.
- intros _.
  simpl.
  reflexivity.
- intros H1.
  destruct a.
  + inversion H1.
    specialize (IHw H0).
    simpl.
    omega.
  + inversion H1.
  + inversion H1.
Qed.

Lemma bmcm_exists:
forall w: list terminal,
bmcm w -> exists x: list terminal, exists y: list terminal,
w=x++y /\ length x = nb x /\ length y = nc y /\ length x = length y.
Proof.
intros w H1.
induction H1.
- exists [], [].
  simpl.
  auto.
- destruct IHbmcm as [x [y [H2 [H3 [H4 H5]]]]].
  exists ([b]++x).
  exists (y++[c]).
  split.
  + rewrite H2.
    repeat rewrite <- app_assoc.
    reflexivity.
  + split.
    * simpl.
      omega.
    * {
      split. 
      - simpl.
        rewrite app_length.
        rewrite nc_cat.
        simpl.
        omega.
      - simpl.
        rewrite app_length.
        simpl.
        omega.
      } 
Qed.

Lemma cfl_ambm:
cfl ambm.
Proof.
unfold cfl.
exists non_terminal, g_ambm.
unfold lang_eq.
intros w.
split.
- intros H1.
  unfold lang_of_g.
  unfold produces.
  unfold generates.
  induction H1.
  + simpl.
    apply derives_rule with (s1:=[]) (s2:=[]) (left:=S) (right:=[]).
    apply r12.
  + apply derives_trans with (s2:=[inr a; inl S; inr b]).
    * apply derives_rule with (s1:=[]) (s2:=[]) (left:=S) (right:=[inr a; inl S; inr b]).
      apply r11.
    * change [inr a; inl S; inr b] with ([inr a]++[inl S]++[inr b]).
      repeat rewrite map_app.
      change (map (terminal_lift non_terminal (terminal:=terminal)) [a]) with [@inr non_terminal terminal a].
      change (map (terminal_lift non_terminal (terminal:=terminal)) [b]) with [@inr non_terminal terminal b].
      apply derives_context_free_add_left.
      apply derives_context_free_add_right.
      exact IHambm.
- intros H1.
  unfold lang_of_g, produces, generates in H1.
  apply derives_equiv_derives6 in H1.
  destruct H1 as [n H1].
  destruct n.
  + inversion H1.
    destruct w.
    * inversion H.
    * simpl in H.
      inversion H.
  + revert w H1.
    induction n.
    * intros w H1.
      simpl.
      inversion H1.
      inversion H3.
      {
      inversion H2.
      - rewrite <- H8 in H5. 
        apply map_expand in H5. 
        destruct H5 as [_ [s2' [_ [_ H5]]]].
        symmetry in H5.
        apply map_expand in H5.
        destruct H5 as [s1' [_ [_ [H5 _]]]].
        symmetry in H5.
        change [inr a; inl S; inr b] with ([inr a] ++ [inl S; inr b]) in H5.
        apply map_expand in H5. 
        destruct H5 as [_ [s2'0 [_ [_ H5]]]].
        destruct s2'0.
        + simpl in H5.
          inversion H5.
        + simpl in H5.
          inversion H5.
      - change (s1 ++ inl left :: s2) with (s1 ++ [inl left] ++ s2) in H0.
        apply app_single_v2 in H0.
        destruct H0 as [H9 [H10 _]].
        rewrite <- H8, H9, H10 in H5.
        simpl in H5.
        symmetry in H5.
        apply map_eq_nil in H5.
        rewrite H5.
        apply ambm_1.
      }
    * intros w H1.
      inversion H1.
      change (s1 ++ inl left :: s2) with (s1 ++ [inl left] ++ s2) in H0.
      apply app_single_v2 in H0.
      destruct H0 as [H5 [H6 H7]].
      rewrite H5, H6 in H3.
      simpl in H3.
      rewrite app_nil_r in H3.
      {
      inversion H2.
      - rewrite <- H8 in H3.
         change ([inr a; inl S; inr b]) with ([inr a] ++ [inl S]++[inr b]) in H3.
         apply derives6_terminal_left_right in H3.
         destruct H3 as [w' [H9 H10]].
         specialize (IHn w' H10).
         rewrite H9.
         apply ambm_2.
         exact IHn.
      - rewrite <- H8 in H3.
        inversion H3.
        apply app_eq_nil in H10.
        destruct H10 as [_ H10].
        inversion H10. 
      }
Qed.

Lemma cfl_cn:
cfl cn.
Proof.
unfold cfl.
exists non_terminal, g_cn.
unfold lang_eq.
intros w.
split.
- intros H1.
  unfold lang_of_g.
  unfold produces.
  unfold generates.
  induction H1.
  + simpl.
    apply derives_rule with (s1:=[]) (s2:=[]) (left:=S) (right:=[]).
    apply r22.
  + apply derives_trans with (s2:=[inr c; inl S]).
    * apply derives_rule with (s1:=[]) (s2:=[]) (left:=S) (right:=[inr c; inl S]).
      apply r21.
    * change [inr c; inl S] with ([inr c]++[inl S]).
      repeat rewrite map_app.
      change (map (terminal_lift non_terminal (terminal:=terminal)) [c]) with [@inr non_terminal terminal c].
      apply derives_context_free_add_left.
      exact IHcn.
- intros H1. 
  unfold lang_of_g, produces, generates in H1.
  simpl in H1.
  apply derives_equiv_derives6 in H1.
  destruct H1 as [n H1].
  revert n w H1.
  destruct n.
  + intros w H1. 
    inversion H1.
    destruct w.
    * inversion H.
    * inversion H.
  + induction n.
    * intros w H1.
      inversion H1.
      {
      inversion H2.
      - inversion H3.
        apply map_expand in H7.
        destruct H7 as [_ [s2' [_ [_ H7]]]].
        symmetry in H7.
        apply map_expand in H7.
        destruct H7 as [s1' [_ [_ [H7 _]]]].
        rewrite <- H6 in H7.
        symmetry in H7.
        change ([inr c; inl S]) with ([inr c]++[inl S]) in H7.
        apply map_expand in H7.
        destruct H7 as [_ [s2'0 [_ [_ H7]]]].
        destruct s2'0.
        + inversion H7.
        + inversion H7.
      - change (inl left :: s2) with ([inl left]++s2) in H0.
        apply app_single_v2 in H0.
        destruct H0 as [H7 [H8 H9]].
        rewrite <- H6, H7, H8 in H3.
        inversion H3.
        symmetry in H0.
        apply map_eq_nil in H0.
        rewrite H0.
        apply cn_1.
      }
    * intros w H1.
      inversion H1.
        change (s1 ++ inl left :: s2) with (s1 ++ [inl left] ++ s2) in H0.
        apply app_single_v2 in H0.
        destruct H0 as [H5 [H6 H7]].
        rewrite H5, H6 in H3.
        simpl in H3.
        rewrite app_nil_r in H3.
        {
        inversion H2.
        - rewrite <- H8 in H3.
          change ([inr c; inl S]) with ([inr c] ++ [inl S]) in H3.
          apply derives6_terminal_left in H3.
          destruct H3 as [w' [H9 H10]].
          specialize (IHn w' H10).
          rewrite H9.
          apply cn_2.
          exact IHn.
        - rewrite <- H8 in H3.
          inversion H3.
          apply app_eq_nil in H10.
          destruct H10 as [_ H10].
          inversion H10.
        }
Qed.

Lemma cfl_an:
cfl an.
Proof.
apply cfl_lang_eq with (l1:=an').
- apply change_alphabet_in_language_is_cfl.
  + apply cfl_cn.
  + apply bijective_f. 
- apply lang_eq_sym. 
  apply an_equiv_an'.
Qed.

Lemma cfl_bmcm:
cfl bmcm.
Proof.
apply cfl_lang_eq with (l1:=bmcm').
- apply change_alphabet_in_language_is_cfl.
  + apply cfl_ambm.
  + apply bijective_f.
- apply lang_eq_sym. 
  apply bmcm_equiv_bmcm'.
Qed.

Lemma cat_ambm_cn_eq_ambmcn:
l_cat ambm cn == ambmcn.
Proof.
unfold lang_eq.
intros w.
split.
- intros H1.
  inversion H1.
  clear w H1 H2.
  revert s2 H0.
  induction H.
  + intros s2 H1. 
    exists [], [], s2, 0.
    simpl.
    split.
    * reflexivity.
    * {
      split.
      - reflexivity.
      - split.
        + reflexivity.
        + split. 
          * reflexivity.
          * {
            split. 
            - reflexivity. 
            - revert H1.
              induction s2.
              + intros _.
                simpl.
                reflexivity.
              + intros H1.
                destruct a.
                * inversion H1.
                * inversion H1.
                * inversion H1.
                  specialize (IHs2 H0).
                  simpl.
                  omega.
            }
      }
    + intros s2 H1.
      specialize (IHambm s2 H1).
      apply ambm_exists in H.
      destruct H as [x [y H]].
      destruct H as [H2 [H3 [H4 H5]]].
      exists ([a]++x), (y++[b]), s2, ((length x)+1).
      split.
      * rewrite H2. 
        repeat rewrite <- app_assoc.
        reflexivity.
      * {
        split.   
        - simpl.
          omega.
        - split.
          + rewrite na_cat.
            simpl. 
            omega. 
          + split.
            * rewrite app_length. 
              simpl. 
              omega.
            * {
              split.
              - rewrite nb_cat. 
                simpl. 
                omega. 
              - revert H1. 
                induction s2.
                + intros _. 
                  simpl.
                  reflexivity.
                + intros H1.
                  destruct a.
                  * inversion H1.
                  * inversion H1.
                  * inversion H1.
                    simpl.
                    assert (H6: ambmcn (w ++ s2)).
                      {
                      exists x, y, s2, (length x).
                      split.
                      - rewrite H2.
                        rewrite <- app_assoc.
                        reflexivity.
                      - split.
                        + reflexivity.
                        + split.
                          * omega.
                          * {
                            split.
                            - omega.
                            - split.
                              + omega.
                              + apply cn_exists in H0.
                                exact H0.
                            }
                      }
                    specialize (IHs2 H6 H0).
                    omega.
              }
        }   
- intros H1.
  unfold ambmcn in H1.
  destruct H1 as [x [y [z [i [H2 [H3 [H4 [H5 [H6 H7]]]]]]]]].
  rewrite H2.
  rewrite app_assoc.
  apply l_cat_app.
  + clear w H2 H7. 
    revert x y H3 H4 H5 H6. 
    induction i.
    * intros x y H1 _ H2 _.
      apply length_eq_0 in H1.
      apply length_eq_0 in H2.
      rewrite H1, H2.
      simpl.
      apply ambm_1.
    * intros x y H1 H2 H3 H4.
      assert (H5: length x > 0) by omega.
      assert (H6: length y > 0) by omega.
      apply length_gt_0 in H5.
      apply length_gt_0 in H6.
      destruct H5 as [[w' [t1 H5]] _].
      destruct H6 as [_ [w'' [t2 H6]]].
      assert (H8: t1=a).
        {
        apply in_a with (w:=x).
        - rewrite H5.
          simpl.
          left.
          reflexivity.
        - apply length_na_only_a.
          rewrite H1, H2.
          reflexivity.
        }
      assert (H9: t2=b).
        {
        apply in_b with (w:=y).
        - rewrite H6.
          apply in_or_app.
          right.
          simpl.
          left.
          reflexivity.
        - apply length_nb_only_b.
          rewrite H3, H4.
          reflexivity.
        }
    rewrite H5, H6, H8, H9.
    rewrite <- app_assoc.
    {
    replace ([a] ++ w' ++ w'' ++ [b]) with ([a] ++ (w' ++ w'') ++ [b]).
    - apply ambm_2.
      apply IHi.
      + rewrite H5 in H1.
        simpl in H1.
        omega.
      + rewrite H5, H8 in H2.
        simpl in H2.
        omega.
      + rewrite H6 in H3.
        rewrite app_length in H3.
        simpl in H3.
        omega.
      + rewrite H6, H9 in H4.
        rewrite nb_cat in H4.
        simpl in H4.
        omega.
    - rewrite <- app_assoc. 
      reflexivity.
    }
  + clear w x y i H2 H3 H4 H5 H6.
    revert H7.
    induction z.
    * intros _.
      apply cn_1.
    * intros H1.
      {
      destruct a.
      - simpl in H1.
        assert (H2: length z >= nc z).
          {
          apply length_nc.
          }
        omega.
      - simpl in H1.
        assert (H2: length z >= nc z).
          {
          apply length_nc.
          }
        omega.
      - simpl in H1.
        apply cn_2.
        apply IHz.
        omega.
      }
Qed.

Lemma cat_an_bmcm_eq_anbmcm:
l_cat an bmcm == anbmcm.
Proof.
unfold lang_eq.
intros w.
split.
- intros H1.
  inversion H1.
  clear w H1 H2.
  revert s1 H.
  induction H0.
  + intros s1 H1.
    exists s1, [], [], 0.
    simpl.
    split.
    * reflexivity.
    * {
      split.
      - revert H1.
        induction s1.
        + intros _.
          simpl.
          reflexivity.
        + intros H1.
          destruct a.
          * inversion H1.
            specialize (IHs1 H0).
            simpl.
            omega.
          * inversion H1.
          * inversion H1.
      - auto. 
      }
  + intros s1 H1.
    specialize (IHbmcm s1 H1).
    apply bmcm_exists in H0.
    destruct H0 as [x [y H]].
    destruct H as [H2 [H3 [H4 H5]]].
    exists s1, ([b]++x), (y++[c]), ((length x)+1).
    split.
    * rewrite H2. 
      repeat rewrite <- app_assoc.
      reflexivity.
    * {
      split.   
      - revert H1. 
        induction s1.
        + intros _. 
          simpl.
          reflexivity.
        + intros H1.
          destruct a.
          * inversion H1.
            simpl.
            assert (H6: anbmcm (s1 ++ w)).
              {
              exists s1, x, y, (length x).
              split.
               - rewrite H2.
                reflexivity.
              - split.
                + apply an_exists in H0.
                  exact H0.
                + split.
                  reflexivity.
                  split.
                  * symmetry.
                    exact H3.
                  * {
                    split.
                    - symmetry.
                      exact H5.
                    - omega.
                    }
              } 
            specialize (IHs1 H6 H0).
            omega.
          * inversion H1.
          * inversion H1.
      - split.
        + simpl. 
          omega.
        + split.
          * rewrite nb_cat.
            simpl.
            omega. 
          * {
            split.
            - simpl.
              rewrite app_length.
              simpl.
              omega.
            - rewrite nc_cat. 
              simpl. 
              omega. 
            }
      }
- intros H1.
  unfold anbmcm in H1.
  destruct H1 as [x [y [z [i [H2 [H3 [H4 [H5 [H6 H7]]]]]]]]].
  rewrite H2.
  apply l_cat_app.
  + clear w y z i H2 H4 H5 H6 H7.
    revert H3.
    induction x.
    * intros _.
      apply an_1.
    * intros H1.
      {
      destruct a.
      - simpl in H1.
        apply an_2.
        apply IHx.
        omega.
      - simpl in H1.
        assert (H2: length x >= na x).
          {
          apply length_na.
          }
        omega.
      - simpl in H1.
        assert (H2: length x >= na x).
          {
          apply length_na.
          }
        omega.
      }
  + clear w x H2 H3. 
    revert y z H4 H5 H6 H7. 
    induction i.
    * intros y z H1 _ H2 _.
      apply length_eq_0 in H1.
      apply length_eq_0 in H2.
      rewrite H1, H2.
      simpl.
      apply bmcm_1.
    * intros y z H1 H2 H3 H4.
      assert (H5: length y > 0) by omega.
      assert (H6: length z > 0) by omega.
      apply length_gt_0 in H5.
      apply length_gt_0 in H6.
      destruct H5 as [[w' [t1 H5]] _].
      destruct H6 as [_ [w'' [t2 H6]]].
      assert (H8: t1=b).
        {
        apply in_b with (w:=y).
        - rewrite H5.
          simpl.
          left.
          reflexivity.
        - apply length_nb_only_b.
          rewrite H1, H2.
          reflexivity.
        } 
      assert (H9: t2=c).
        {
        apply in_c with (w:=z).
        - rewrite H6.
          apply in_or_app.
          right.
          simpl.
          left.
          reflexivity.
        - apply length_nc_only_c.
          rewrite H3, H4.
          reflexivity.
        }
    rewrite H5, H6, H8, H9.
    rewrite <- app_assoc.
    {
    replace ([b] ++ w' ++ w'' ++ [c]) with ([b] ++ (w' ++ w'') ++ [c]).
    - apply bmcm_2.
      apply IHi.
      + rewrite H5 in H1.
        simpl in H1.
        omega.
      + rewrite H5, H8 in H2.
        simpl in H2.
        omega.
      + rewrite H6 in H3.
        rewrite app_length in H3.
        simpl in H3.
        omega.
      + rewrite H6, H9 in H4.
        rewrite nc_cat in H4.
        simpl in H4.
        omega.
    - rewrite <- app_assoc. 
      reflexivity.
    }
Qed.

Lemma cfl_ambmcn:
cfl ambmcn.
Proof.
apply cfl_lang_eq with (l1:=l_cat ambm cn).
- apply l_cat_is_cfl.
  + apply cfl_ambm.
  + apply cfl_cn.
- apply cat_ambm_cn_eq_ambmcn.
Qed.

Lemma cfl_anbmcm:
cfl anbmcm.
Proof.
apply cfl_lang_eq with (l1:=l_cat an bmcm).
- apply l_cat_is_cfl.
  + apply cfl_an.
  + apply cfl_bmcm.
- apply cat_an_bmcm_eq_anbmcm.
Qed.

Lemma int_eq_anbncn:
l_int ambmcn anbmcm == anbncn.
Proof.
unfold lang_eq.
intros w.
split.
- intros H1.
  inversion H1.
  unfold anbncn.
  unfold ambmcn in H.
  unfold anbmcm in H0.
  destruct H as [x1 [y1 [z1 [i1 [H11 [H12 [H13 [H14 [H15 H16]]]]]]]]].
  destruct H0 as [x2 [y2 [z2 [i2 [H21 [H22 [H23 [H24 [H25 H26]]]]]]]]].
  exists x1, y1, z2, i1.
  split.
  + assert (H41: nc x1 = 0).
      {
      rewrite <- H13 in H12.
      apply length_eq_na_0 in H12. 
      destruct H12 as [_ H12].
      exact H12. 
      }
    assert (H42: nc y1 = 0).
      {
      rewrite <- H15 in H14.
      apply length_eq_nb_0 in H14. 
      destruct H14 as [_ H14].
      exact H14. 
      }
    assert (H43: nc x2 = 0).
      {
      apply length_eq_na_0 in H22. 
      destruct H22 as [_ H22].
      exact H22. 
      }
    assert (H44: nc y2 = 0).
      {
      rewrite <- H24 in H23.
      apply length_eq_nb_0 in H23. 
      destruct H23 as [_ H23].
      exact H23. 
      }
    rewrite H11 in H21.
    assert (H50: nc (x1++y1++z1)=nc (x2++y2++z2)).
      {
      rewrite H21.
      reflexivity.
      }
    repeat rewrite nc_cat in H50.
    rewrite H41, H42, H43, H44 in H50.
    simpl in H50.
    assert (H30: z2 = z1).
      {
      apply length_nc_eq.
      - rewrite H25, H26.
        reflexivity.
      - exact H16.
      - rewrite H16.
        rewrite H50. 
        rewrite H25, H26.
        reflexivity.
      }
    rewrite H30.
    exact H11.
  + split.
    * exact H12.
    * {
      split.
      - exact H13.
      - split.
        + exact H14.
        + split.
          * exact H15.
          * clear s H1 H2. 
            assert (H30: i2=i1).
              {
              rewrite H11 in H21.
              assert (H31: nb (x1++y1++z1)=nb (x2++y2++z2)).
                {
                rewrite H21.
                reflexivity.
                }
              assert (H32: nb x1 = 0).
                {
                rewrite <- H13 in H12.
                apply length_eq_na_0 in H12.
                destruct H12 as [H12 _].
                exact H12.
                }
              assert (H33: nb z1 = 0).
                {
                apply length_eq_nc_0 in H16.
                destruct H16 as [_ H16].
                exact H16.
                }
              assert (H34: nb x2 = 0).
                {
                apply length_eq_na_0 in H22.
                destruct H22 as [H22 _].
                exact H22.
                }
              assert (H35: nb z2 = 0).
                {
                rewrite <- H26 in H25.
                apply length_eq_nc_0 in H25.
                destruct H25 as [_ H25].
                exact H25.
                }
              repeat rewrite nb_cat in H31.
              rewrite H32, H33, H34, H35 in H31.
              simpl in H31.
              rewrite H15, H24 in H31.
              omega.
              }
            {
            split.
            - rewrite H25. 
              exact H30. 
            - rewrite H26.
              exact H30.
            }
      }
- intros H1.
  unfold anbncn in H1.
  destruct H1 as [x [y [z [i [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]]]]].
  apply l_int_c.
  + unfold ambmcn.
    exists x, y, z, i.
    split.
    * exact H2.
    * {
      split.
      - exact H3.
      - split.
        + exact H4.
        + split.
          * exact H5.
          * {
            split.
            - exact H6.
            - rewrite H7, H8.
              reflexivity.
            }
      }
  + unfold anbmcm.
    exists x, y, z, i.
    split.
    * exact H2.
    * {
      split.
      - rewrite H3, H4. 
        reflexivity. 
      - split.
        + exact H5.
        + split.
          * exact H6.
          * {
            split.
            - exact H7.
            - exact H8. 
            }
      }
Qed.

Theorem cfl_not_closed_intersection:
~ forall l1 l2: lang terminal, cfl l1 -> cfl l2 -> cfl (l_int l1 l2).
Proof.
intros H1.
specialize (H1 ambmcn anbmcm).
specialize (H1 cfl_ambmcn).
specialize (H1 cfl_anbmcm).
apply cfl_lang_eq with (l2:=anbncn) in H1.
- apply not_cfl_anbncn.
  exact H1.
- apply int_eq_anbncn.
Qed.

End Intersection.
