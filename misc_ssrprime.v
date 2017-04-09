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

Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Require Import div prime.

Lemma dvdn_factmn m n: 0<m<=n -> m %| n`!.
Proof.
case: m => //= m; elim: n => //= n IHn; rewrite ltnS leq_eqVlt.
by case/orP=> [/eqP-> | /IHn]; [apply: dvdn_mulr | apply: dvdn_mull].
Qed.

Lemma prime_above m : exists2 p, m < p & prime p.
Proof.
have /pdivP[p pr_p p_dv_m1]: 1 < m`! + 1 by rewrite addn1 ltnS fact_gt0.
exists p => //; rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m.
by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.

(* Some lemas to use in plain coq (without resorting to ssreflect) *)

Lemma prime_gt0 p: prime p -> (p > 0)%coq_nat.
Proof. by move=> Hp; apply/ltP; apply prime_gt0. Qed.

Lemma prime_exists m : exists p, 
    (p >= m.+1)%coq_nat /\ prime p.
Proof.
by move: (prime_above m) => [p Hlt Hp]; exists p; split; first by apply/leP.
Qed.

Lemma mult_primeN p q:
 (p>=2 -> q>=2 -> ~ prime (p*q)%coq_nat)%coq_nat.
Proof.
move=> /leP Hp /leP Hq.
rewrite -/muln_rec -mulnE.
have lt_p_n: p < (p*q).
  apply ltn_Pmulr => //.
  by apply ltn_trans with 1.
have div_p_n: p %| (p*q) by apply dvdn_mulr.
apply/negP; apply/primePn.
right; exists p => //.
by apply/andP; split.
Qed.

