=TEX
\ignore{
=VDUMP t050i.tex
\hypersetup{pdfkeywords=RogerBishopJones}

Last Change $ $Date: 2013/01/10 16:35:58 $ $

$ $Id: t050.doc,v 1.3 2013/01/10 16:35:58 rbj Exp $ $
=TEX
}%ignore

This is first a rough transcription into ProofPower of the simple HOL4 proof of the Church Rosser theorem for the pure combinatory logic, eventually perhaps to be upgraded to an illative combinatory logic.

Beause I am exploring this approach with a view to extending it in certain ways, I will be making some changes along the way, above and beyond those arising from recasting the material to work in ProofPower HOL.

The two principal extensions to this work which are of interest to me are firstly to go from pure combinatory logic to illative combinatory logics, which one could do with essentially the same term structure (but more combinators), and secondly to move to infinitary combinators.

I therefore aim to maximise the applicability of each part of the development so that as little as possible will need to be reworked as I undertake those extensions.

This may eventually result in the material being split across multiple theories and multiple documents, but initially, apart from the placement in t005 \cite{rbjt005} of general results on reflexive transitive closure I will stick to one theory.
The strategy in this respect is firstly to separate out materials which do not depend on term structure (and present this first), then to adopt a structure for finitary terms which is extensible in the number of primitive combinators.


Since we don't have a datatype package I will follow my own usual practice of using a set theoretic approach to the syntax.


=SML
open_theory "misc3";
force_new_theory "⦏icl⦎";
force_new_pc ⦏"'icl"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'icl";
=IGN
new_parent "equiv";
=SML
set_merge_pcs ["misc31", "'icl"];
=TEX

\section{Reduction}

In this section I deal with matters which do not in the hol4 treatment depend upon the type of combinatory terms, and some matters which in the hol4 treatment do but need not.
The latter requires some restructuring of the proof strategy

\subsection{Diamond Preserved by RTC}

In this section we obtain the result that the recursive transitive closure of a relation satisfying the diamond property also satisfies that property.

The proof in the hol4 version is slick because RTC is redefined using a package for defining relations which delivers some nice induction principles.

ⓈHOLCONST
│ ⦏confluent⦎: ('a → 'a  → BOOL) → BOOL
├───────────
│ ∀R⦁ confluent R ⇔ ∀x y z⦁ rtc R x y ∧ rtc R x z ⇒
│             ∃u⦁ rtc R y u ∧ rtc R z u
■

ⓈHOLCONST
│ ⦏normform⦎: ('a → 'a  → BOOL) → 'a →BOOL
├───────────
│ ∀R x⦁ normform R x ⇔ ∀y⦁ ¬ R x y
■

=GFT
⦏confluent_normforms_unique⦎ =
	⊢ ∀ R⦁ confluent R ⇒
		(∀ x y z⦁ rtc R x y ∧ normform R y ∧ rtc R x z ∧ normform R z
		⇒ y = z)
=TEX

\ignore{
=SML
val confluent_def = get_spec ⌜confluent⌝;
val normform_def = get_spec ⌜normform⌝;

set_goal([], ⌜∀R⦁ confluent R ⇒
        ∀x y z⦁ rtc R x y ∧ normform R y ∧ rtc R x z ∧ normform R z
                  ⇒ (y = z)⌝);
a (rewrite_tac[confluent_def, normform_def]
	THEN REPEAT strip_tac);
a (LIST_SPEC_NTH_ASM_T 5 [⌜x⌝, ⌜y⌝, ⌜z⌝] strip_asm_tac);
a (REPEAT_N 2 (POP_ASM_T ante_tac)
	THEN once_rewrite_tac[rtc_cases]
	THEN REPEAT strip_tac
	THEN_TRY all_asm_ufc_tac[]
	THEN (SYM_ASMS_T rewrite_tac));
val confluent_normforms_unique = save_pop_thm "confluent_normforms_unique";
=TEX
}%ignore


ⓈHOLCONST
│ ⦏diamond⦎: ('a → 'a  → BOOL) → BOOL
├───────────
│ ∀R⦁ diamond R = ∀x y z⦁ R x y ∧ R x z ⇒ ∃u⦁ R y u ∧ R z u
■

=GFT
⦏confluent_diamond_rtc⦎ =
	⊢ ∀ R⦁ confluent R ⇔ diamond (rtc R)

⦏R_rtc_diamond⦎ =
	⊢ ∀ R⦁ diamond R ⇒ (∀ x p⦁ rtc R x p ⇒
		(∀ z⦁ R x z ⇒ (∃ u⦁ rtc R p u ∧ rtc R z u)))
=TEX

\ignore{
=SML
val diamond_def = get_spec ⌜diamond⌝;

set_goal([], ⌜∀R⦁ confluent R = diamond (rtc R)⌝);
a (rewrite_tac[confluent_def, diamond_def]);
val confluent_diamond_rtc = save_pop_thm "confluent_diamond_rtc";

set_goal([], ⌜∀R⦁ diamond R ⇒
         ∀x p⦁ rtc R x p ⇒
               ∀z⦁ R x z ⇒
                   ∃u⦁ rtc R p u ∧ rtc R z u⌝);
a (∀_tac THEN strip_tac);
a (rtc_ind_tac THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac[diamond_def]);
a (fc_tac [rtc_incr_thm]);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[rtc_def]);
(* *** Goal "2" *** *)
a (fc_tac[diamond_def]);
a (all_asm_fc_tac[]);
a (spec_nth_asm_tac 9 ⌜u'⌝);
a (all_fc_tac [rtc_incr_thm]);
a (all_fc_tac [tran_rtc_thm2]);
a (∃_tac ⌜u''''⌝ THEN asm_rewrite_tac[]);
val R_rtc_diamond = save_pop_thm "R_rtc_diamond";
=TEX
}%ignore

$RTC\_RTC$ is the transitivity of reflexive transitive closure, which we have as $tran\_rtc\_thm2$.

=GFT
⦏diamond_RTC_lemma⦎ =
	⊢ ∀ R⦁ diamond R ⇒ (∀ x y⦁ rtc R x y
		⇒ (∀ z⦁ rtc R x z ⇒ (∃ u⦁ rtc R y u ∧ rtc R z u)))

⦏diamond_RTC⦎ =
	⊢ ∀ R⦁ diamond R ⇒ diamond (rtc R)
=TEX

\ignore{
=SML
set_goal([], ⌜∀R⦁ diamond R ⇒
       ∀x y⦁ rtc R x y ⇒ ∀z⦁ rtc R x z ⇒
                               ∃u⦁ rtc R y u ∧ rtc R z u⌝);
a (strip_tac THEN strip_tac);
a (rtc_strongind_tac THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac [rtc_rules]);
(* *** Goal "2" *** *)
a (all_ufc_tac[R_rtc_diamond]);
a (all_asm_ufc_tac[]);
a (all_ufc_tac[tran_rtc_thm2]);
a (∃_tac ⌜u'⌝ THEN contr_tac);
val diamond_RTC_lemma = save_pop_thm "diamond_RTC_lemma";

set_goal([], ⌜∀R⦁ diamond R ⇒ diamond (rtc R)⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [diamond_def]
	THEN REPEAT strip_tac
	THEN all_fc_tac [diamond_RTC_lemma]);
a (∃_tac ⌜u'⌝ THEN contr_tac);
val diamond_RTC = save_pop_thm "diamond_RTC";
=TEX
}%ignore

=IGN

stop;


=TEX


=IGN
⊥└⊆	∀
⊥Γ▷	⇒
⊥└𝕌	∃
⊥└⟨	∧
.	⦁
=TEX

\subsection{Further Results about Reduction Relations}

In the hol4 proof reduction is defined over combinatory terms using a relation definition package which results in the following definition (this is the result of a modified notion admitting more combinatory constants):

=GFT
    redn_def
    |- $--> =
       (λa0 a1.
          ∀-->' .
            (∀a0 a1.
               (∃x y f. (a0 = f # x) ∧ (a1 = f # y) ∧ -->' x y) ∨
               (∃f g x. (a0 = f # x) ∧ (a1 = g # x) ∧ -->' f g) ∨
               (∃y. a0 = C 0 # a1 # y) ∨
               (∃f g x.
                  (a0 = C 1 # f # g # x) ∧ (a1 = f # x # (g # x))) ∨
               (∃x. (a0 = C 2 # x # x) ∧ (a1 = C 0)) ⇒
               -->' a0 a1) ⇒
            -->' a0 a1)
=TEX

Of the various parts in this definition, the first two make this a congruence relation, i.e. reductions on parts yeild reductions on the whole, the third is the primitive reduction for K, the fourth for S, the fifth for Q.
These are wrapped up to assert that the defined relation is the intersection of all relations closed under these rules.

The


So the natural way to proceed in the absence of the rule-based relation definition facility in hol4 is to define the primitive relations for each combinator, combine them (take the union or disjunction), form the congruence and take the transitive closure.


\section{Combinatory Terms}

\subsection{Introduction}

In hol4 the syntax of combinatory logic is give as a single line definition of a recursive datatype.
We can't do this in ProofPower, datatypes have to be manually cranked.
This section replicates that process, and aims to replicate pretty closely what hol4 produces for that datatype.

I did first of all modify the type to allow any number of combinatory constants after which the definition read:

=GFT hol4
val _ = Hol_datatype `CT = C of num | # of CT => CT`;
=TEX

The theory resulting from that datatype definition is as follows:

=GFT hol4
Theory: cl

Parents:
    list

Type constants:
    CT 0

Term constants:
    #    :CT -> CT -> CT
    C    :num -> CT
    CT_case    :(num -> α) -> (CT -> CT -> α) -> CT -> α
    CT_size    :CT -> num

Definitions:
    CT_TY_DEF
    |- ∃rep.
         TYPE_DEFINITION
           (λa0'.
              ∀'CT' .
                (∀a0'.
                   (∃a.
                      a0' =
                      (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                        a) ∨
                   (∃a0 a1.
                      (a0' =
                       (λa0 a1.
                          ind_type$CONSTR (SUC 0) ARB
                            (ind_type$FCONS a0
                               (ind_type$FCONS a1
                                  (λn. ind_type$BOTTOM)))) a0 a1) ∧
                      'CT' a0 ∧ 'CT' a1) ⇒
                   'CT' a0') ⇒
                'CT' a0') rep
    CT_case_def
    |- (∀f f1 a. CT_case f f1 (C a) = f a) ∧
       ∀f f1 a0 a1. CT_case f f1 (# a0 a1) = f1 a0 a1
    CT_size_def
    |- (∀a. CT_size (C a) = 1 + a) ∧
       ∀a0 a1. CT_size (# a0 a1) = 1 + (CT_size a0 + CT_size a1)

Theorems:
    datatype_CT  |- DATATYPE (CT C #)
    CT_11
    |- (∀a a'. (C a = C a') ⇔ (a = a')) ∧
       ∀a0 a1 a0' a1'. (# a0 a1 = # a0' a1') ⇔ (a0 = a0') ∧ (a1 = a1')
    CT_distinct  |- ∀a1 a0 a. C a ≠ # a0 a1
    CT_case_cong
    |- ∀M M' f f1.
         (M = M') ∧ (∀a. (M' = C a) ⇒ (f a = f' a)) ∧
         (∀a0 a1. (M' = # a0 a1) ⇒ (f1 a0 a1 = f1' a0 a1)) ⇒
         (CT_case f f1 M = CT_case f' f1' M')
    CT_nchotomy  |- ∀CC. (∃n. CC = C n) ∨ ∃C C0. CC = # C C0
    CT_Axiom
    |- ∀f0 f1.
         ∃fn.
           (∀a. fn (C a) = f0 a) ∧
           ∀a0 a1. fn (# a0 a1) = f1 a0 a1 (fn a0) (fn a1)
    CT_induction
    |- ∀P. (∀n. P (C n)) ∧ (∀C C0. P C ∧ P C0 ⇒ P (# C C0)) ⇒ ∀C. P C
=TEX

In this section I aim to replicate this quite closely, though using a different representation.
I am assuming that once this is done here, there will be no further need to refer to the representing type.

\subsection{Introducing the type CT}

The natural way to hand crank such a datatype in ProofPower HOL would be to use the theory of trees in Arthan's mathematical examples as a representation type.
However, I am more familiar with using the domain of an axiomatic set theory so it will be slightly easier for me to do that.

I don't define the constructors over the representation type since they are simple enough to write out, instead I go straight to defining the closure conditions on the set of representatives.

There are two constructors, a constant constructor and an application constructor.
There are countably many constants named by natural numbers, and tagged by zero to distinguish them from applications.
An application is constructed from two combinators and is tagged by 1.

The closure condition is:

ⓈHOLCONST
│ ⦏CTrepClosed⦎: (ONE GSU → BOOL) → BOOL
├───────────
│ ∀ s⦁ CTrepClosed s ⇔ (∀n⦁ s (Nat⋎u 0 ↦⋎u Nat⋎u n))
│	∧ (∀f a⦁ s f ∧ s a ⇒ s (Nat⋎u 1 ↦⋎u (f ↦⋎u a)))
■

The property of being a combinatory term is then the smallest property which is \emph{CTrepClosed}.

ⓈHOLCONST
│ ⦏CTsyntax⦎ : ONE GSU → BOOL
├───────────
│ ∀s⦁ CTsyntax s = ∀t ⦁ CTrepClosed t ⇒ t s
■

The following theorems about the representation are helpful in proving related result for the new type:

=GFT
⦏CTrepclosed_CTsyntax_lemma1⦎ =
	⊢ CTrepClosed CTsyntax

⦏CTrepclosed_CTsyntax_thm⦎ =
	⊢ (∀n⦁ CTsyntax (Nat⋎u 0 ↦⋎u Nat⋎u n))
       ∧ (∀f a⦁ CTsyntax f ∧ CTsyntax a ⇒ CTsyntax (Nat⋎u 1 ↦⋎u f ↦⋎u a))
=TEX
=GFT
⦏CTrepclosed_CTsyntax_lemma2⦎ =
	⊢ ∀s⦁ CTrepClosed s ⇒ (∀ t⦁ CTsyntax t ⇒ s t)
=TEX

\ignore{
=SML
val CTrepClosed_def = get_spec ⌜CTrepClosed⌝;
val CTsyntax_def = get_spec ⌜CTsyntax⌝;

set_goal([], ⌜CTrepClosed CTsyntax⌝);
val _ = a (rewrite_tac [CTsyntax_def, CTrepClosed_def]
	THEN REPEAT strip_tac
	THEN REPEAT_N 3 (asm_ufc_tac[])
	THEN asm_rewrite_tac[]);
val CTrepclosed_CTsyntax_lemma1 = save_pop_thm "CTrepclosed_CTsyntax_lemma1";

val CTrepclosed_CTsyntax_thm = save_thm ("CTrepclosed_CTsyntax_thm",
	pure_rewrite_rule [get_spec ⌜CTrepClosed⌝] CTrepclosed_CTsyntax_lemma1);

local val _ = set_goal([], ⌜∀ s⦁ CTrepClosed s ⇒ ∀t⦁ CTsyntax t ⇒ s t⌝);
val _ = a (rewrite_tac [CTsyntax_def]
	THEN prove_tac[]);
in val CTrepclosed_CTsyntax_lemma2 = save_pop_thm "CTrepclosed_CTsyntax_lemma2";
end;
=TEX
}%ignore

=GFT
⦏CTsyntax_cases_thm⦎ =
	⊢ ∀c⦁ CTsyntax c
		⇒ (∃ n⦁ c = Nat⋎u 0 ↦⋎u Nat⋎u n)
		∨ (∃ f a⦁ CTsyntax f ∧ CTsyntax a ∧ c = Nat⋎u 1 ↦⋎u f ↦⋎u a)
=TEX

\ignore{
=SML
set_goal([], ⌜∀c⦁ CTsyntax c ⇒
		(∃n⦁ c = Nat⋎u 0 ↦⋎u Nat⋎u n)
	∨	(∃f a⦁ CTsyntax f ∧ CTsyntax a ∧ c = (Nat⋎u 1 ↦⋎u f ↦⋎u a))⌝);
a (lemma_tac ⌜CTrepClosed (λc⦁ (∃n⦁ c = Nat⋎u 0 ↦⋎u Nat⋎u n)
	∨	(∃f a⦁ CTsyntax f ∧ CTsyntax a ∧ c = (Nat⋎u 1 ↦⋎u f ↦⋎u a)))⌝
	THEN1 (rewrite_tac[CTrepClosed_def]
		THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (prove_∃_tac);
(* *** Goal "2" *** *)
a (asm_prove_∃_tac THEN asm_rewrite_tac[CTrepclosed_CTsyntax_thm]);
(* *** Goal "3" *** *)
a (asm_prove_∃_tac
	THEN asm_rewrite_tac[]
	THEN ALL_FC_T rewrite_tac [CTrepclosed_CTsyntax_thm]
	THEN rewrite_tac[CTrepclosed_CTsyntax_thm]);
(* *** Goal "4" *** *)
a (asm_prove_∃_tac
	THEN asm_rewrite_tac[]
	THEN ALL_FC_T rewrite_tac [CTrepclosed_CTsyntax_thm]
	THEN rewrite_tac[CTrepclosed_CTsyntax_thm]);
(* *** Goal "5" *** *)
a (asm_prove_∃_tac
	THEN asm_rewrite_tac[]
	THEN ALL_FC_T rewrite_tac [CTrepclosed_CTsyntax_thm]
	THEN rewrite_tac[CTrepclosed_CTsyntax_thm]);
(* *** Goal "6" *** *)
a (REPEAT_N 2 strip_tac);
a (fc_tac [CTsyntax_def]);
a (all_asm_fc_tac[]);
a (POP_ASM_T ante_tac THEN rewrite_tac[]);
val CTsyntax_cases_thm = save_pop_thm "CTsyntax_cases_thm";

set_goal([], ⌜∃c⦁ CTsyntax c⌝);
a (∃_tac ⌜Nat⋎u 0 ↦⋎u Nat⋎u 0⌝
	THEN rewrite_tac [CTsyntax_def, CTrepClosed_def]
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[]);
val CTsyntax_nonempty = pop_thm();
=TEX
}%ignore

To introduce the new type we must prove that \emph{CTsyntax} is inhabited: 

=GFT
⦏CTsyntax_nonempty⦎ = 
	⊢ ∃c⦁ CTsyntax c
=TEX

The type \emph{CT} is then introduced as follows:

=SML
val CT_type_defn_thm = new_type_defn(["CT"], "CT", [], CTsyntax_nonempty);
=TEX

Which gives the following result:
=GFT
⦏CT_type_defn_thm⦎ = ⊢ ∃ f⦁ TypeDefn CTsyntax f
=TEX

From which we can derive:

=GFT
⦏CT_type_lemma2⦎ =
	⊢ ∃ abs rep⦁ (∀ a⦁ abs (rep a) = a)
         ∧ (∀ r⦁ CTsyntax r ⇔ rep (abs r) = r)
         ∧ OneOne rep
         ∧ (∀ a⦁ CTsyntax (rep a))
=TEX

\ignore{
=SML
val [CT_type_lemma2] = fc_rule [type_defn_lemma4] [CT_type_defn_thm];
=TEX
}%ignore

\subsection{Primitive Constructors over CT}

I could manage without defining the following mappings between the new type and its representations , but its easier to define them.

\ignore{
=SML
set_goal([], ⌜∃(CTabs:ONE GSU → CT) (CTrep:CT → ONE GSU)⦁
	(∀ a⦁ CTabs (CTrep a) = a)
     ∧ (∀ r⦁ CTsyntax r ⇔ CTrep (CTabs r) = r)
     ∧ OneOne CTrep
     ∧ (∀ a⦁ CTsyntax (CTrep a))⌝);
a (strip_asm_tac CT_type_lemma2);
a (∃_tac ⌜abs⌝ THEN ∃_tac ⌜rep⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm(pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏CTabs⦎: ONE GSU → CT;
│ ⦏CTrep⦎: CT → ONE GSU
├───────────
│	(∀ a⦁ CTabs (CTrep a) = a)
│     ∧ (∀ r⦁ CTsyntax r ⇔ CTrep (CTabs r) = r)
│     ∧ OneOne CTrep
│     ∧ (∀ a⦁ CTsyntax (CTrep a))
■


There will be two constructors one for constants and one for applications.
Applications are infix.

=SML
declare_infix(1000, "⋎c");
=TEX

ⓈHOLCONST
│ ⦏$⋎c⦎: CT → CT → CT
├───────────
│ ∀s t⦁ s ⋎c t = CTabs (Nat⋎u 1 ↦⋎u (CTrep s) ↦⋎u (CTrep t))
■

ⓈHOLCONST
│ ⦏C⦎: ℕ → CT
├───────────
│ ∀s⦁ C s = CTabs(Nat⋎u 0 ↦⋎u (Nat⋎u s))
■

=GFT
⦏CT_cases⦎ =
	⊢ ∀ t⦁ (∃ n⦁ t = C n) ∨ (∃ c1 c2⦁ t = c1 ⋎c c2)
=TEX

\ignore{
=SML
val CTrep_def = get_spec ⌜CTrep⌝;
val ⋎c_def = get_spec ⌜$⋎c⌝;
val C_def = get_spec ⌜C⌝;

set_goal([], ⌜∀t⦁ (∃n⦁ t = C n) ∨ (∃c1 c2⦁ t = c1 ⋎c c2)⌝);
a (strip_tac);
a (strip_asm_tac (∀_elim ⌜CTrep t⌝ CTsyntax_cases_thm));
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac [CTrep_def]);
(* *** Goal "2" *** *)
a (∨_left_tac THEN ∃_tac ⌜n⌝ THEN asm_rewrite_tac[C_def]);
a (LEMMA_T ⌜CTabs(Nat⋎u 0 ↦⋎u Nat⋎u n) = CTabs(CTrep t)⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a (rewrite_tac[CTrep_def]);
(* *** Goal "3" *** *)
a (∨_right_tac THEN ∃_tac ⌜CTabs f⌝ THEN ∃_tac ⌜CTabs a⌝
	THEN asm_rewrite_tac[⋎c_def]);
a (LEMMA_T ⌜CTabs(Nat⋎u 1 ↦⋎u CTrep (CTabs f) ↦⋎u CTrep (CTabs a)) = CTabs(CTrep t)⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a (FC_T rewrite_tac [CTrep_def]);
(* *** Goal "3.2" *** *)
a (rewrite_tac [CTrep_def]);
val CT_cases = save_pop_thm "CT_cases";
=TEX
}%ignore

\subsection{Induction and Recursion}

Now we obtain a principle of induction for reasoning about these combinatory terms and a recursion theorem to justify definitions over the terms by pattern matching recursion.

We can derive a well-founded ordering for combinatory terms from the well-foundedness of membership over the sets used to represent the terms.
This provides a first method of proof by induction over the combinatory terms which is used to prove the induction principle produced by hol4.

=GFT
⦏wf_CT_thm⦎ =
	⊢ well_founded (λ x y⦁ CTrep x ∈⋎u CTrep y)
⦏tc∈⋎u_rep_⋎c_lemma⦎ =
	⊢ ∀ c1 c2⦁ CTrep c1 ∈⋎u⋏+ CTrep (c1 ⋎c c2)
		∧ CTrep c2 ∈⋎u⋏+ CTrep (c1 ⋎c c2)
⦏CT_induction⦎ =
	⊢ ∀ P⦁ (∀ n⦁ P (C n)) ∧ (∀ c c0⦁ P c ∧ P c0 ⇒ P (c ⋎c c0))
		⇒ (∀ c⦁ P c)
⦏CT_axiom⦎ =
	⊢ ∀ f0 f1⦁ ∃ fn⦁
		(∀ a⦁ fn (C a) = f0 a)
           ∧	(∀ a0 a1⦁ fn (a0 ⋎c a1) = f1 a0 a1 (fn a0) (fn a1))
=TEX

\ignore{
=SML
set_goal([], ⌜well_founded(DerivedOrder CTrep ($∈⋎u⋏+:ONE GSU → ONE GSU → BOOL))⌝);
a (rewrite_tac [∀_elim ⌜CTrep⌝ (⇒_elim (∀_elim ⌜$∈⋎u⋏+:ONE GSU → ONE GSU → BOOL⌝ wf_derived_order_thm) (inst_type_rule [(ⓣONE⌝, ⓣ'a⌝)] gsu_wftc_thm2))]);
val wf_CT_lemma = pop_thm ();

val wf_CT_thm = save_thm ("wf_CT_thm", rewrite_rule [get_spec ⌜DerivedOrder⌝] wf_CT_lemma);

set_goal([], ⌜∀c1 c2⦁ CTrep c1 ∈⋎u⋏+ CTrep (c1 ⋎c c2)
		∧ CTrep c2 ∈⋎u⋏+ CTrep (c1 ⋎c c2)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[⋎c_def]);
a (lemma_tac ⌜CTsyntax (Nat⋎u 1 ↦⋎u CTrep c1 ↦⋎u CTrep c2)⌝ 
	THEN1 (bc_tac [∧_right_elim CTrepclosed_CTsyntax_thm]
		THEN rewrite_tac [CTrep_def]));
a (lemma_tac ⌜CTrep c1 ↦⋎u CTrep c2 ∈⋎u⋏+ Nat⋎u 1 ↦⋎u CTrep c1 ↦⋎u CTrep c2⌝
	THEN1 rewrite_tac[]);
a (lemma_tac ⌜CTrep c1 ∈⋎u⋏+ CTrep c1 ↦⋎u CTrep c2 ∧ CTrep c2 ∈⋎u⋏+ CTrep c1 ↦⋎u CTrep c2⌝
	THEN1 rewrite_tac[]);
a (all_asm_fc_tac [tc∈⋎u_trans_thm]);
a (ALL_FC_T asm_rewrite_tac[CTrep_def]);
val tc∈⋎u_rep_⋎c_lemma = save_pop_thm "tc∈⋎u_rep_⋎c_lemma";

set_goal([], ⌜∀P⦁ (∀n⦁ P (C n)) ∧ (∀c c0⦁ P c ∧ P c0 ⇒ P (c ⋎c c0)) ⇒ ∀c⦁ P c⌝);
a (REPEAT strip_tac);
a (wf_induction_tac wf_CT_thm ⌜c⌝);
a (strip_asm_tac (∀_elim ⌜t⌝ CT_cases)
	THEN asm_rewrite_tac[]);
a (var_elim_asm_tac ⌜t = c1 ⋎c c2⌝);
a (POP_ASM_T (asm_tac o (rewrite_rule[])));
a (lemma_tac ⌜CTrep c1 ∈⋎u⋏+ CTrep (c1 ⋎c c2) ∧ CTrep c2 ∈⋎u⋏+ CTrep (c1 ⋎c c2)⌝
	THEN1 rewrite_tac [tc∈⋎u_rep_⋎c_lemma]);
a (all_asm_fc_tac[]);
a (all_asm_fc_tac[]);
val CT_induction = save_pop_thm "CT_induction";

set_goal([], ⌜∀f0 f1⦁ ∃fn:ONE GSU → 'a⦁
	(∀n⦁ fn (Nat⋎u 0 ↦⋎u Nat⋎u n:ONE GSU) = f0 (Nat⋎u n:ONE GSU))
	∧ (∀a0 a1⦁ fn (Nat⋎u 1 ↦⋎u (a0 ↦⋎u a1)) = f1 a0 a1 (fn a0) (fn a1))⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜∃g⦁ g = λfn (x:ONE GSU)⦁
  if (∃n⦁ x = (Nat⋎u 0 ↦⋎u (Nat⋎u n:ONE GSU))) ∨ ∃a0 a1⦁ x = (Nat⋎u 1 ↦⋎u a0 ↦⋎u a1)
  then
	if Fst⋎u x = Nat⋎u 0
	then f0 (Snd⋎u x)
	else	let a0 = Fst⋎u (Snd⋎u x)
		and a1 = Snd⋎u (Snd⋎u x)
		in f1 a0 a1 (fn a0) (fn a1)
  else εx⦁ T⌝
	THEN1 prove_∃_tac);
a (lemma_tac ⌜g respects $∈⋎u⌝
	THEN1 (rewrite_tac [get_spec ⌜$respects⌝]
		THEN REPEAT strip_tac
		THEN asm_rewrite_tac[]));
(* *** Goal "1" *** *)
a (cond_cases_tac ⌜Fst⋎u x = Nat⋎u 0⌝);
a (CASES_T ⌜(∃n⦁ x = (Nat⋎u 0 ↦⋎u (Nat⋎u n:ONE GSU))) ∨ ∃a0 a1⦁ x = (Nat⋎u 1 ↦⋎u a0 ↦⋎u a1)⌝
	(fn x => rewrite_thm_tac x THEN asm_tac x));
a (POP_ASM_T strip_asm_tac);
(* *** Goal "1.1" *** *)
a (var_elim_asm_tac ⌜x = Nat⋎u 0 ↦⋎u Nat⋎u n⌝);
a (POP_ASM_T (strip_asm_tac o (rewrite_rule[])));
(* *** Goal "1.2" *** *)
a (lemma_tac ⌜tc $∈⋎u a0 x ∧ tc $∈⋎u a1 x⌝
	THEN1 asm_rewrite_tac[]);
(* *** Goal "1.2.1" *** *)
a (lemma_tac ⌜a0 ∈⋎u⋏+ (a0 ↦⋎u a1)⌝ THEN1 asm_rewrite_tac[tc∈⋎u_↦⋎u_left_thm]);
a (lemma_tac ⌜(a0 ↦⋎u a1) ∈⋎u⋏+ (Nat⋎u 1 ↦⋎u (a0 ↦⋎u a1))⌝
	THEN1 asm_rewrite_tac[tc∈⋎u_↦⋎u_right_thm]);
a (LEMMA_T ⌜a0 ∈⋎u⋏+ (Nat⋎u 1 ↦⋎u a0 ↦⋎u a1)⌝
	(asm_tac o (rewrite_rule[get_spec ⌜$∈⋎u⋏+⌝]))
	THEN1 all_fc_tac [tc∈⋎u_trans_thm]);
a (asm_rewrite_tac[]);
a (lemma_tac ⌜a1 ∈⋎u⋏+ (a0 ↦⋎u a1)⌝ THEN1 asm_rewrite_tac[tc∈⋎u_↦⋎u_left_thm]);
a (LEMMA_T ⌜a1 ∈⋎u⋏+ (Nat⋎u 1 ↦⋎u a0 ↦⋎u a1)⌝
	(rewrite_thm_tac o (rewrite_rule[get_spec ⌜$∈⋎u⋏+⌝]))
	THEN1 all_fc_tac [tc∈⋎u_trans_thm]);
(* *** Goal "1.2.2" *** *)
a (all_asm_fc_tac []);
a (REPEAT_N 2 (POP_ASM_T ante_tac) THEN asm_rewrite_tac[let_def]);
a (REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (strip_asm_tac (inst_type_rule [(ⓣONE⌝, ⓣ'a⌝)] gsu_wf_thm1));
a (all_fc_tac [fixp_thm1]);
a (∃_tac ⌜g'⌝);
a (POP_ASM_T ante_tac
	THEN once_asm_rewrite_tac[]
	THEN rewrite_tac[]
	THEN strip_tac);
a (strip_tac THEN REPEAT ∀_tac);
(* *** Goal "2.1" *** *)
a (SPEC_NTH_ASM_T 1 ⌜Nat⋎u 0 ↦⋎u (Nat⋎u n):ONE GSU⌝ ante_tac);
a (LEMMA_T ⌜∃ n'⦁ Nat⋎u 0 ↦⋎u Nat⋎u n = Nat⋎u 0 ↦⋎u Nat⋎u n'⌝ rewrite_thm_tac
	THEN1 (∃_tac ⌜n⌝ THEN rewrite_tac[]));
a (LEMMA_T ⌜∃ n'⦁ n = n'⌝ rewrite_thm_tac
	THEN1 (∃_tac ⌜n⌝ THEN rewrite_tac[]));
a (STRIP_T (rewrite_thm_tac o (eq_sym_rule)));
(* *** Goal "2.2" *** *)
a (SPEC_NTH_ASM_T 1 ⌜Nat⋎u 1 ↦⋎u a0 ↦⋎u a1:ONE GSU⌝ ante_tac);
a (LEMMA_T ⌜∃ a0' a1'⦁ Nat⋎u 1 ↦⋎u a0 ↦⋎u a1 = Nat⋎u 1 ↦⋎u a0' ↦⋎u a1'⌝ rewrite_thm_tac
	THEN1 (∃_tac ⌜a0⌝ THEN ∃_tac ⌜a1⌝ THEN rewrite_tac[]));
a (rewrite_tac[let_def]);
a (STRIP_T (rewrite_thm_tac o (eq_sym_rule)));
val rec_lemma1 = pop_thm ();

set_goal([], ⌜∀f0 f1⦁
         ∃fn: CT → 'a⦁
           (∀a⦁ fn (C a) = f0 a) ∧
           ∀a0 a1:CT⦁ (fn (a0 ⋎c a1):'a) = (f1 a0 a1 (fn a0) (fn a1))⌝);
a (REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim
	[⌜λc:ONE GSU⦁ f0 (εn⦁ Nat⋎u n = c)⌝,
	⌜λa0 a1 fa0 fa1⦁ f1 (CTabs a0) (CTabs a1) fa0 fa1⌝]
 rec_lemma1));
a (∃_tac ⌜λc⦁ fn (CTrep c)⌝
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[CTrep_def, C_def, ⋎c_def]);
(* *** Goal "1" *** *)
a (lemma_tac ⌜CTsyntax (Nat⋎u 0 ↦⋎u Nat⋎u a)⌝
	THEN1 rewrite_tac[CTrepclosed_CTsyntax_thm]);
a (FC_T asm_rewrite_tac [CTrep_def]);
a (ε_tac ⌜ε n⦁ n = a⌝ THEN1 prove_∃_tac);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜CTsyntax(CTrep a0) ∧ CTsyntax(CTrep a1)⌝
	THEN1 rewrite_tac [CTrep_def]);
a (lemma_tac ⌜CTsyntax(Nat⋎u 1 ↦⋎u CTrep a0 ↦⋎u CTrep a1)⌝
	THEN1 all_fc_tac [CTrepclosed_CTsyntax_thm]);
a (ALL_FC_T asm_rewrite_tac [CTrep_def]);
a (rewrite_tac[CTrep_def]);
val CT_axiom = save_pop_thm "CT_axiom";

add_∃_cd_thms [CT_axiom] "'icl";
set_merge_pcs ["misc31", "'icl"];
=TEX
}%ignore

\subsection{Further Definitions}

We can now define constants over $CT$ by pattern matching primitive recursion.

I would normally obtain a `course of values' induction by defining a well-founded relation over the terms, which is easily done thus:

=SML
declare_infix(200, "in⋎c");
=TEX

ⓈHOLCONST
│ $⦏in⋎c⦎: CT → CT → BOOL
├───────────
│ ∀x y⦁ x in⋎c y ⇔ ∃z⦁ y = x ⋎c z ∨ y = z ⋎c x
■


=GFT
=TEX

\ignore{
=SML
val in⋎c_def = get_spec ⌜$in⋎c⌝;

=IGN
set_goal([], ⌜well_founded $in⋎c⌝);
a (rewrite_tac [get_spec ⌜well_founded⌝, in⋎c_def, ⋎c_def]
	THEN REPEAT strip_tac);
a (gsu_induction_tac ⌜x⌝);

=TEX
}%ignore

However, the method used in the hol4 datatype system is to define a numeric `size' for combinatory terms as follows:

ⓈHOLCONST
│ ⦏CT_size⦎: CT → ℕ
├───────────
│	(∀a⦁		CT_size (C a)		= 1 + a)
│ ∧	∀a0 a1⦁	CT_size (a0 ⋎c a1)	= 1 + CT_size a0 + CT_size a1
■

Course of values induction can then be obtained by induction over the size of combinatory terms.

ⓈHOLCONST
│ ⦏CT_case⦎: (ℕ → CT) → (CT → CT → CT) → (CT → CT)
├───────────
│ ∀f g x y n⦁	CT_case f g (C n) = f n
│		∧	CT_case f g (x ⋎c y) = g x y
■

\ignore{
=SML
val CT_case_def = get_spec ⌜CT_case⌝;

set_goal([], ⌜∃CT_size2⦁ (∀a⦁	CT_size2 (C a)	= 1 + a)
│ ∧	∀a0 a1⦁	CT_size2 (a0 ⋎c a1)	= 1 + CT_size2 a0 + CT_size2 a1⌝);
a (strip_asm_tac (list_∀_elim
	[⌜λa:ℕ⦁ 1 + a⌝, ⌜λ(a0:CT) (a1:CT) fa0 fa1⦁ 1 + fa0 + fa1⌝] CT_axiom));

set_flag("pp_show_HOL_types", false);
=TEX
}%ignore

We now prove the rest of the theorems which are derived automatically for the datatype in hol4.

=GFT
⦏CT_11⦎ =
	⊢ (∀ a a'⦁ C a = C a' ⇒ a = a')
	∧ (∀ a0 a1 a0' a1'⦁ a0 ⋎c a1 = a0' ⋎c a1' ⇒ a0 = a0' ∧ a1 = a1')
⦏CT_distinct⦎ =
	⊢ ∀ a a0 a1⦁ ¬ C a = a0 ⋎c a1
⦏CT_nchotomy⦎ =
	⊢ ∀ cc⦁ ¬ ((∃ n⦁ cc = C n) ⇔ (∃ c c0⦁ cc = c ⋎c c0))
=TEX


\ignore{
=SML
set_goal([], ⌜
	(∀a a'⦁ (C a = C a') ⇒ (a = a')) ∧
        (∀a0 a1 a0' a1'⦁ (a0 ⋎c a1 = a0' ⋎c a1') ⇒ (a0 = a0') ∧ (a1 = a1'))
⌝);
a (rewrite_tac [C_def, ⋎c_def] THEN REPEAT_N 2 strip_tac
	THEN REPEAT ∀_tac THEN strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜CTsyntax(Nat⋎u 0 ↦⋎u Nat⋎u a)⌝ THEN1 rewrite_tac [CTrepclosed_CTsyntax_thm]);
a (lemma_tac ⌜CTsyntax(Nat⋎u 0 ↦⋎u Nat⋎u a')⌝ THEN1 rewrite_tac [CTrepclosed_CTsyntax_thm]);
a (LEMMA_T ⌜CTrep(CTabs (Nat⋎u 0 ↦⋎u Nat⋎u a)) = CTrep(CTabs (Nat⋎u 0 ↦⋎u Nat⋎u a'))⌝ (fn y => ALL_FC_T (fn x => (asm_tac o (rewrite_rule x)) y) [CTrep_def])
	THEN1 asm_rewrite_tac[]);
a (strip_tac);
(* *** Goal "2" *** *)
a (lemma_tac ⌜CTsyntax(CTrep a0) ∧ CTsyntax(CTrep a1)⌝
	THEN1 rewrite_tac [CTrep_def]);
a ((lemma_tac ⌜CTsyntax (Nat⋎u 1 ↦⋎u CTrep a0 ↦⋎u CTrep a1)⌝
	THEN1 (bc_tac [∧_right_elim CTrepclosed_CTsyntax_thm]))
		THEN_TRY ALL_FC_T asm_rewrite_tac [CTrep_def]);
a (lemma_tac ⌜CTsyntax(CTrep a0') ∧ CTsyntax(CTrep a1')⌝
	THEN1 rewrite_tac [CTrep_def]);
a ((lemma_tac ⌜CTsyntax (Nat⋎u 1 ↦⋎u CTrep a0' ↦⋎u CTrep a1')⌝
	THEN1 (bc_tac [∧_right_elim CTrepclosed_CTsyntax_thm]))
		THEN_TRY ALL_FC_T asm_rewrite_tac [CTrep_def]);
a (LEMMA_T ⌜CTrep(CTabs (Nat⋎u 1 ↦⋎u CTrep a0 ↦⋎u CTrep a1))
             = CTrep(CTabs (Nat⋎u 1 ↦⋎u CTrep a0' ↦⋎u CTrep a1'))⌝
	(fn y => ALL_FC_T (fn x => (ante_tac o (try(rewrite_rule x))) y) [CTrep_def])
	THEN1 asm_rewrite_tac[]);
a (strip_tac THEN LEMMA_T
	⌜CTabs(CTrep a0) = CTabs(CTrep a0')
	∧ CTabs(CTrep a1) = CTabs(CTrep a1')⌝
	(rewrite_thm_tac o (rewrite_rule [CTrep_def]))
	THEN1 asm_rewrite_tac[]);
val CT_11 = save_pop_thm "CT_11";

set_goal([], ⌜∀a a0 a1⦁ ¬ C a = a0 ⋎c a1⌝);
a (rewrite_tac [C_def, ⋎c_def] THEN contr_tac);
a (lemma_tac ⌜CTsyntax(CTrep a0) ∧ CTsyntax(CTrep a1)⌝
	THEN1 rewrite_tac [CTrep_def]);
a ((lemma_tac ⌜CTsyntax (Nat⋎u 1 ↦⋎u CTrep a0 ↦⋎u CTrep a1)⌝
	THEN1 (bc_tac [∧_right_elim CTrepclosed_CTsyntax_thm]))
		THEN_TRY ALL_FC_T asm_rewrite_tac [CTrep_def]);
a (lemma_tac ⌜CTsyntax(Nat⋎u 0 ↦⋎u Nat⋎u a)⌝
	THEN1 (rewrite_tac [CTrepclosed_CTsyntax_thm]));
a (LEMMA_T ⌜CTrep(CTabs (Nat⋎u 0 ↦⋎u Nat⋎u a))
	= CTrep(CTabs (Nat⋎u 1 ↦⋎u CTrep a0 ↦⋎u CTrep a1))⌝
	ante_tac
	THEN1 asm_rewrite_tac[]);
a (FC_T rewrite_tac [CTrep_def]);
val CT_distinct = save_pop_thm "CT_distinct";

set_goal([], ⌜∀M M' f f1⦁
         (M = M') ∧ (∀a⦁ (M' = C a) ⇒ (f a = f' a)) ∧
         (∀a0 a1⦁ (M' = a0 ⋎c a1) ⇒ (f1 a0 a1 = f1' a0 a1)) ⇒
         (CT_case f f1 M = CT_case f' f1' M')⌝);
a (REPEAT ∀_tac
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[]);
a (strip_asm_tac (∀_elim ⌜M'⌝ CT_cases)
	THEN asm_rewrite_tac[CT_case_def]
	THEN GET_NTH_ASM_T 1 (var_elim_asm_tac o concl));
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 2 ⌜n⌝);
(* *** Goal "2" *** *)
a (var_elim_asm_tac ⌜M = c1 ⋎c c2⌝);
a (list_spec_nth_asm_tac 1 [⌜c1⌝, ⌜c2⌝]);
val CT_case_cong = save_pop_thm "CT_case_cong";

set_goal([], ⌜∀cc⦁ ¬ (∃n⦁ cc = C n) = (∃c c0⦁ cc = c ⋎c c0)⌝);
a (REPEAT ∀_tac);
a (strip_asm_tac (∀_elim ⌜cc⌝ CT_cases) THEN asm_rewrite_tac [CT_distinct]);
(* *** Goal "1" *** *)
a (∃_tac ⌜n⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (LEMMA_T ⌜∀ a a0 a1⦁ ¬ a0 ⋎c a1 = C a⌝ rewrite_thm_tac
	THEN1 (REPEAT strip_tac THEN_TRY rewrite_tac[CT_distinct]));
(* *** Goal "2.1" *** *)
a (rewrite_tac [map_eq_sym_rule (all_∀_elim CT_distinct)]);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜c1⌝ THEN ∃_tac ⌜c2⌝ THEN asm_rewrite_tac[]);
val CT_nchotomy = save_pop_thm "CT_nchotomy";
=TEX
}%ignore

\subsection{Combinator Names}

In the original hol4 treatment the combinators K and S were constructors of the abstract datatype.
In this quasi replica I made the minor generalisation of allowing countably many constants using a constructor taking a natural number parameter.

To make the material more legible I now define constants to give the conventional names to the S and K constructors as follows.

ⓈHOLCONST
│ ⦏K⋎c⦎: CT
├───────────
│	K⋎c = C 0
■

ⓈHOLCONST
│ ⦏S⋎c⦎: CT
├───────────
│	S⋎c = C 1
■

Once I have replicated essentially the same Church Rosser proof for this pure combinatory logic I will then attempt a proof for an illative system with one illative combinatory.
This will be called `Q'.

ⓈHOLCONST
│ ⦏Q⋎c⦎: CT
├───────────
│	Q⋎c = C 2
■

Since `Q' is intended to be a close approximation to equality, it might be nice to have the following way of writing equations:

=SML
declare_infix(300, "=⋎c");
=TEX


ⓈHOLCONST
│ $⦏=⋎c⦎: CT → CT → CT
├───────────
│ ∀a0 a1⦁ a0 =⋎c a1 = (Q⋎c ⋎c a0) ⋎c a1
■

This kind of equality delivers a combinatory term rather than a BOOL.
True and false will probably be coded as left and right projections, i.e. K and KI (where I is the identity, which is SKK).

These definitions really only give names to the combinators, to know what they mean you have to look at the reduction relations over the combinators.

=SML
set_flag ("subgoal_package_quiet", false);
set_flag ("pp_use_alias", true);
=TEX


