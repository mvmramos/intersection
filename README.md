These files contain definitions and proof scripts related to the correctness of:

- languages square, prime and anbncn are not context-free;
- context-free languages are closed under alphabet substitution;
- context-free languages are not closed under intersection.

File list:

- allrules.v: generates all rules over a given alphabet;
- bijection.v: context-free languages are closed under alphabet substitution;
- cfg.v: definitions and basic lemmas regarding context-free grammars and derivations;
- cfl.v: definitions and basic lemmas regarding context-free languages;
- chomsky.v: Chomsky grammar normalization;
- concatenation.v: closure of context-free languages over concatenation;
- emptyrules.v: elimination of empty rules in a context-free grammar;
- inaccessible.v: elimination of inaccessible symbols in a context-free grammar;
- intersection.v: context-free languages are not closed under intersection;
- misc_arith.v: generic arithmetic related lemmas;
- misc_list.v: generic list lemmas;
- misc_logic: generic logic lemmas;
- misc_ssrprime: generic results about prime numbers;
- pigeon.v: pigeonhole principle;
- pumping: pumipng lemma for context-free languages;
- pumping_anbncn: language anbncn is not context-free;
- pumping_prime: language prime is not context-free;
- pumping_square: language square is not context-free;
- simplification.v: unification of all previous results.
- trees.v: binary trees and their relation to Chomsky grammars;
- unitrules.v: elimination of unit rules in a context-free grammar;
- useless.v: elimination of useless symbols in a context-free grammar;

To compile, download all files and:
- coq_makefile *.v > _makefile
- make -f _makefile

These files have been created and compiled with the Coq Proof Assistant, version 8.4pl4 (June 2014).

More information can be found in the paper "Some Applications of the Formalization of the Pumping Lemma for Context-Free Languages", submitted to ITP 2017 by Marcus Vinícius Midena Ramos, Ruy J. G. B. de Queiroz, Nelma Moreira and José Carlos Bacelar Almeida.

mvmramos@gmail.com
