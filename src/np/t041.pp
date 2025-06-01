=TEX
\ignore{
=VDUMP t041i.tex
\hypersetup{pdfkeywords=RogerBishopJones}

Last Change $ $Date: 2013/01/03 17:12:44 $ $

$ $Id: t041.doc,v 1.18 2013/01/03 17:12:44 rbj Exp $ $
=TEX
}%ignore

The idea is to obtain an exotic model for illative lambda-calculi by methods analogous to those employed for set theory in \cite{rbjt027}, and then to use that as a semantic foundation for the definition of one or more finitary illative lambda-calculi with systems of type assignment.

The work is conducted by conservative extension in the context of a higher order set theory established axiomatically in HOL, which I will refer to as HOL/GSU, or just GSU\cite{rbjt042}.
The end result is intended to be a semantic embedding of an illative lambda-calculus into HOL/GSU.
This end is to be realised in stages as follows:

\begin{itemize}
\item Establish an infinitary illative combinatory logic.
\begin{itemize}
\item Define the infinitary syntax by transfinite recursion in GSU.
\item Define the semantics, by determining a partial equivalence relation from a notion of reducibility over the syntax.
This involves taking a least fixed point of a recursive definition of the relation and proving a result analogous to the Church-Rosser theorem to establish coherence and non-triviality of the results.
\end{itemize}
\item Using this as a semantic domain, a new type is then introduced, which will be the domain over which the operations in the illative lambda-calculus will be defined. 
The theory is then developed by defining further operations as necessary and proving results which establish the required type assignment and inference rules for the embedded calculus.
\end{itemize}

\subsection{Type Assignments}

The systems of type assignments I am interested in have the following features:

\begin{itemize}
\item A universal type.
\item Dependent product and sum (function and pair) types.
\item A heirarchy of `Universes' (but since we have an absolute universe I will probably follow GSU in calling them galaxies), not all well-founded, each closed under dependent type constructions (this has the effect of power set and replacement).
\item A well-founded part in which classical mathematics can be conducted in the normal way (i.e. getting the theories isomorphic to the standard classical versions), and which admits arbitrarily risky axiomatic extensions analogous to (possibly even identical to) large cardinal axioms (with no greater risk here than in ZFC).
The well founded part is the union of iterated galaxy construction over the empty set.
\end{itemize}

The difficult question with such a shopping list, is whether it can be consistently fulfilled, and the principal purpose of this document is to explore an idea about how to construct an interpretation which might allow the equiconsistency of the systems considered here with ZFC (plus large cardinals where appropriate) to be established.
Having said that, the procedure is \emph{semantics first}, so I aim to construct the interpretation first, and then to derive logical systems of which it is an interpretation.
This method guarantees that the resulting system is consistent relative to my set theory (which is `A Higher Order Theory of Well-Founded Sets (with Urelements)' (GSU\index{GSU}), see \cite{rbjt042}).
\footnote{This is a modification of the pure set theory GS to admit urelements, which are irrelevant to the theory here, but may improve the smoothness of its integration into HOL.
GS actually started with urlements, but then I removed them, and now I have put them back in.
They don't make it significantly more complicated, at least not in the areas I have covered.}

In the talk which follows about syntax and semantics there are two levels involved, that of the infinitary calculus (which is the interpretation constructed in GSU) and that of the finitary calculus which will be based on it.

\subsection{Consistency}

A few more words about consistency may be in order.

The approach here is to ensure consistency in the desired logic by working from semantics to proof rules.
The logic determined by proof rules is bound to be consistent because the proof rules are either theorems proven about the chosen semantic domain or else derived rules implemented in our metalanguage for reasoning in the new language.
This is a natural outcome of the method which consists in implementing the desired language using a `shallow embedding' in a higher-order set theory.

Adoption of this method does not in itself solve the consistency problem, the problem appears in the necessary semantic preliminaries for the embedding.
To succeed it is necessary to understand how the consistency problem appears and have some idea of how it can be resolved.

In this case, the consistency problem for an illative lambda-calculus is to be resolved by providing a syntactic model in an infinitary illative combinatory logic.
The problem is then to obtain a satisfactory account of the infinitary combinatory system.
Ideally the elements of the model would be equivalence classes of terms under convertibility, but one of the primitive combinators is to be read as that very equivalence relation and the effect is that the relation of convertability cannot be a total relation over the combinators (this is how the consistency problem reappears).
This effect arises because the combinator must be defined by recursion, and the higher order equation of which a fixed point is obtained from the definition will not have a total fixed point (this is the manifestation of the various paradoxes such as Russell's or more directly relevant here, Curry's paradox).
Consistency is obtained by accepting a partial fixed point, this is equivalent on the one hand to regarding the Russell set as a "partial set", of which some things (including itself) are neither members nor non-members, neither definitely in nor out.
In the case of the Curry paradox, we find that implication does not always have a truth value (it is total over the truth values, just not over lambda terms in general).
So we have to find a way of working with a partial equivalence relation, which will be the primitive illative combinator in terms of which all the others are defined.

In the context of a combinatory logic this can be realised by limiting the possible reductions of equivalence terms, which is not a pure combinator.
Such an equivalence will always reduce to `T' if its two arguments are convertible, but in the case that they are not, it may not always be reduced to `F', in some cases it will not reduce.
It therefore is not `on the nail', it is in effect an \emph{approximation} to convertability.
The key point in the semantics is therefore the definition of this relation of convertibility.

The definition of this is recursive and is not well-founded so the definition involves taking a fixed point of a monotone functor over partial relations which approximate to convertability.
A total equality combinator would reduce to T or F (suitably chose combinators) when applied to any two combinatory terms, according to whether the two terms are convertible.
A partial equality combinator will not always reduce, there will be some pairs of terms for which one cannot have a definite view as to their convertibility.
One reason for this might be that if no reduction of the equation were possible then they would not be convertible, but once the reduction of the equation to F is added it then becomes possible to convert the two terms.
Such a pair of terms could be constructed corresponding to the liar paradox, and making the equality combinator partial protects against the derivation of contradiction in that way, by allowing that the liar sentence be neither true nor false.

Allowing this equivalence to be partially defined, in particular taking it to be the least fixed point of the defining equations under an appropriate ordering, is what gets us out of the paradox and should yield a good semantics.
This device is to be combined with steps intended to make this semantics as rich as a strong first order set theory (one in which inaccessible cardinals can be proven to exist).
Whether this will also support a system of type assignments along the lines desired remains to be seen, I have not articulated in this context my reasons for hoping that will be the case.
The rationale is more fully thought through for the analogous methods which I was previously applying to models of non-well-founded set theories, and for the preceeding work on `polysets'(see \cite{rbjt026,rbjt024,rbjt021,rbjt020,rbjp011}.

The equivalence relation is compounded from several components of which only one is `illative' and contentious (though the two combinators which handle infinitely many arguments may also be thought contentious!).
There is a question how to organise these separate components and how much to do prior to devising the functor of which the least fixed point gives the semantics of equivalence.

The proposed method, thus outlined, requires no further fundamental innovations to deliver a model, though there will be many opportunities to get details wrong.
There is however, no guarantee that the resulting system will support the kind of type-assignment system which I have in mind, this is highly speculative.
The greatest difficulty is in the complexity of the formal derivations required, which may prove beyond me.

\section{The Infinitary Interpretation}

I have had quite a few (lost count) iterations in my conception of the syntax of the infinitary system which I use for the semantics of the target illative lambda-calculus.

My first attempt was an infinitary illative lambda calculus in which there was infinitary abstraction (abstraction over infinitely many variables at once) and application (application of an infinitary abstraction to an infinite collection of arguments).
There was something unsatisfactory about this approach (a muddle about the scope of the variables, which I used to tag the arguments in an application) and by the time I had sorted it out the infinitary abstraction had been dumped (in favour of infinitary function displays).
Unfortunately the new version left me with five syntactic constructors, and, because the (infinitary) abstract syntax is hand cranked, I have a strong incentive to keep its complexity to an absolute minimum.
So I decided to ditch abstraction, and with it, variables.

Several attempts on I now have an infinitary illative combinatory logic with just one syntactic constructor.

I call this syntax infinitary because the syntax has large (inaccessible) cardinality.
It isn't actually a deductive system, but it is a language, for which we have syntax and semantics.
We have a notion of truth and can prove the truth of expressions of our infinitary language in the metalanguage (which is HOL/GSU, a higher order set theory).

The semantic intent explains the infinitary nature of the system considered, this is so that we have underlying our ultimate language (which will be a finitary untyped illative lambda-calculus with a system of type assignments) a basis for the development of exactly the same (``classical'') applicable mathematics as is more often considered in the context of ZFC or HOL.
For this purpose there are intended to be, within the ontology, structures which mirror or mimic the hierarchy of well-founded sets, and particularly, full function spaces over well founded subsets of the universe.

The idea is to define a kind of syntactic interpretation for the lambda-calculus and to give a semantics to it.
Lambda terms in the target language will denote equivalence classes of infinitary combinators in the underlying language.
The equivalence classes over the combinators are generated by the defining equations for the combinators except for the sole illative combinator, which will be equivalence (aka convertibility).
The tricky bit is to determine the semantics of this equivalence relation, since the formal definition follows the previous sentence in being recursive, and the recursion will probably not be well-founded.
This is done by treating it as a partial equivalence, giving the recursive definition in the form of a functor over partial approximations to convertibility, and then taking the least fixed point of this functor, and praying that there will be enough in there.

An important departure from the method adopted for non-well-founded set theory in \cite{rbjt027} is the acceptance that the domain of discourse will be full of junk (e.g. non-normalising terms), and that the application of a lambda-calculus based on this interpretation will depend on reasoning almost exlusively within the confines of well-behaved subdomains which are delimited by an appropriate system of type-assignment (even though the terms themselves will be un-typed).
This is intended to yield something which will look a bit like a typed lambda-calculus with subtyping and a universal type (plus some other exotic features to make it at least as strong as ZFC) but which differs from it in a manner similar to the difference between the simply-typed lambda-calculus and a system of type assignments to the pure lambda-calculus.

=SML
open_theory "misc3";
force_new_theory "⦏icomb⦎";
force_new_pc ⦏"'icomb"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'icomb";
new_parent "equiv";
set_merge_pcs ["misc31", "'icomb"];
=TEX

\subsection{Infinitary Syntax}

The syntax of an infinitary illative combinatory logic is to be encoded as sets in a higher order set theory.

Since I will probably have to prove something like the Church-Rosser theorem and the syntax can be made very simple, this will be a bare bones treatment of the syntax, by contrast with my previous similar enterprise for non-well-founded set theory in \cite{rbjt027}.

There will be just one constructor, which is the ordered pair constructor constrained to apply a single constant name to sequences of combinators of any cardinality.
We can therefore go immediately to specification of the required closure condition for the syntax.

The closure condition is:

ⓈHOLCONST
│ ⦏CrepClosed⦎: 'a GSU SET → BOOL
├───────────
│ ∀ s⦁ CrepClosed s ⇔
│	(∀c i⦁ Fun⋎u i ∧ Ordinal⋎u (Dom⋎u i) ∧ X⋎u (Ran⋎u i) ⊆ s ⇒ c ↦⋎u i ∈ s)
■

The well-formed syntax is then the smallest set which is \emph{CrepClosed}.

ⓈHOLCONST
│ ⦏Csyntax⦎ : 'a GSU SET
├───────────
│ Csyntax = ⋂{x | CrepClosed x}
■

=GFT
⦏crepclosed_csyntax_lemma⦎ =
	⊢ CrepClosed Csyntax
=TEX
=GFT
⦏crepclosed_csyntax_thm⦎ =
	⊢ ∀ c i⦁ Fun⋎u i
		∧ Ordinal⋎u (Dom⋎u i)
		∧ (∀ x⦁ x ∈ X⋎u (Ran⋎u i) ⇒ x ∈ Csyntax)
         ⇒ c ↦⋎u i ∈ Csyntax
=TEX

=GFT
⦏crepclosed_csyntax_thm2⦎ =
   ⊢ ∀ c i⦁ Fun⋎u i
		∧ Ordinal⋎u (Dom⋎u i)
		∧ (∀ x⦁ x ∈⋎u Ran⋎u i ⇒ x ∈ Csyntax)
	⇒ c ↦⋎u i ∈ Csyntax

⦏crepclosed_csyntax_thm3⦎ =
   ⊢ ∀ c i⦁ Seq⋎u i ∧ (∀ x⦁ x ∈⋎u Ran⋎u i ⇒ x ∈ Csyntax)
	⇒ c ↦⋎u i ∈ Csyntax
=TEX
=GFT
⦏crepclosed_csyntax_lemma1⦎ =
	⊢ ∀ s⦁ CrepClosed s ⇒ Csyntax ⊆ s
=TEX
=GFT
⦏crepclosed_csyntax_lemma2⦎ =
	⊢ ∀ p⦁ CrepClosed {x|p x} ⇒ (∀ x⦁ x ∈ Csyntax ⇒ p x)
=TEX

\ignore{
=SML
val CrepClosed_def = get_spec ⌜CrepClosed⌝;
val Csyntax_def = get_spec ⌜Csyntax⌝;

set_goal([], ⌜CrepClosed Csyntax⌝);
val _ = a (rewrite_tac [CrepClosed_def] THEN strip_tac);
val _ = a (rewrite_tac [Csyntax_def, CrepClosed_def]
	THEN REPEAT strip_tac
	THEN REPEAT (asm_ufc_tac[]));
val _ = a (lemma_tac ⌜(∀ x'⦁ x' ∈ X⋎u (Ran⋎u i) ⇒ x' ∈ s)⌝
		THEN1 (REPEAT strip_tac THEN REPEAT (asm_ufc_tac[])));
val _ = a (asm_ufc_tac[] THEN asm_rewrite_tac []);
val crepclosed_csyntax_lemma = pop_thm();

val crepclosed_csyntax_thm = save_thm ("crepclosed_csyntax_thm",
	pure_rewrite_rule [get_spec ⌜CrepClosed⌝,
		get_spec ⌜$⊆:('a SET→('a SET →BOOL))⌝] crepclosed_csyntax_lemma);

val crepclosed_csyntax_thm2 = save_thm ("crepclosed_csyntax_thm2",
	rewrite_rule [get_spec ⌜X⋎u⌝] crepclosed_csyntax_thm);

set_goal([],⌜∀ c i⦁ Seq⋎u i
		∧ (∀ x⦁ x ∈⋎u Ran⋎u i ⇒ x ∈ Csyntax)
	⇒ c ↦⋎u i ∈ Csyntax⌝);
a (rewrite_tac[Seq⋎u_def]);
a (rewrite_tac[prove_rule [] ⌜∀A B C⦁ (A ∧ B) ∧ C ⇔ A ∧ B ∧ C⌝]);
a (accept_tac crepclosed_csyntax_thm2);
val crepclosed_csyntax_thm3 = save_pop_thm "crepclosed_csyntax_thm3";

local val _ = set_goal([], ⌜∀s⦁ CrepClosed s ⇒ Csyntax ⊆ s⌝);
val _ = a (rewrite_tac [get_spec ⌜Csyntax⌝]
	THEN prove_tac[]);
in val crepclosed_csyntax_lemma1 = save_pop_thm "crepclosed_csyntax_lemma1";
end;

local val _ = set_goal([], ⌜∀p⦁ CrepClosed {x | p x} ⇒ ∀x⦁ x ∈ Csyntax ⇒ p x⌝);
val _ = a (rewrite_tac [get_spec ⌜Csyntax⌝] THEN REPEAT strip_tac);
val _ = a (asm_fc_tac[]);
in val crepclosed_csyntax_lemma2 = save_pop_thm "crepclosed_csyntax_lemma2";
end;
=TEX
}%ignore

\subsubsection{Recursion and Induction Principles and Rules}\label{Induction}

We need to be able to define functions by recursion over this syntax.
To do that we need to prove that the syntax is well-founded.
This is the case relative to the transitive closure of the membership relation, but to get a convenient basis for reasoning inductively over the syntax and for defining functions by recursion over the syntax it is best to define an ordering in terms of the syntactic constructors for the syntax.

This could be done strictly over the well-formed syntactic constructs, but this would involve more complexity both in the definitions and in subsequent proofs than by defining it in terms of the syntactic constructors whatever they are applied to.

ⓈHOLCONST
│ ⦏CscPrec⦎ : 'a GSU REL
├───────────
│ ∀α γ⦁ CscPrec α γ ⇔ ∃c i⦁ α ∈⋎u (Ran⋎u i) ∧ γ = c ↦⋎u i
■

=GFT
⦏CscPrec_tc_∈_thm⦎ =
	⊢ ∀ x y⦁ CscPrec x y ⇒ tc $∈⋎u x y

⦏well_founded_CscPrec_thm⦎ =
	⊢ well_founded CscPrec
=TEX

\ignore{
=SML
val CscPrec_def = get_spec ⌜CscPrec⌝;

local val _ = set_goal([], ⌜∀x y⦁ CscPrec x y ⇒ tc $∈⋎u x y⌝);
val _ = a (rewrite_tac (map get_spec [⌜CscPrec⌝]));
val _ = a (REPEAT strip_tac THEN asm_rewrite_tac [↦⋎u_tc_thm]);
val _ = a (all_fc_tac [tc∈⋎u_incr_thm]);
val _ = a (fc_tac [tc∈⋎u_Ran⋎u_thm]);
val _ = a (lemma_tac ⌜$∈⋎u⋏+ i (c ↦⋎u i)⌝
	THEN1 rewrite_tac [tc∈⋎u_↦⋎u_right_thm]);
val _ = a (all_fc_tac [tc∈⋎u_trans_thm]);
val _ = a (POP_ASM_T ante_tac THEN rewrite_tac[get_spec ⌜$∈⋎u⋏+⌝]);
in val CscPrec_tc_∈_thm = pop_thm();
end;

local val _ = set_goal ([], ⌜well_founded CscPrec⌝);
val _ = a (rewrite_tac [get_spec ⌜well_founded⌝]);
val _ = a (REPEAT strip_tac);
val _ = a (asm_tac (∀_elim ⌜s⌝ gsu_cv_ind_thm));
val _ = a (lemma_tac ⌜∀ x⦁ (∀ y⦁ tc $∈⋎u y x ⇒ s y) ⇒ s x⌝
	THEN1 REPEAT strip_tac);
(* *** Goal "1" *** *)
val _ = a (lemma_tac ⌜∀ y⦁ CscPrec y x ⇒ s y⌝
	THEN1 (REPEAT strip_tac THEN all_fc_tac [CscPrec_tc_∈_thm]
		THEN asm_fc_tac []));
val _ = a (asm_fc_tac[]);
(* *** Goal "2" *** *)
val _ = a (asm_fc_tac[]);
val _ = a (asm_rewrite_tac[]);
in val well_founded_CscPrec_thm =  save_pop_thm "well_founded_CscPrec_thm";
end;
=TEX
}%ignore

=GFT
⦏well_founded_tcCscPrec_thm⦎ =
	⊢ well_founded (tc CscPrec)
=TEX

\ignore{
=SML
set_goal([], ⌜well_founded (tc CscPrec)⌝);
val _ = a (asm_tac well_founded_CscPrec_thm);
val _ = a (fc_tac [wf_tc_wf_thm]);
val well_founded_tcCscPrec_thm = save_pop_thm ("well_founded_tcCscPrec_thm");
=TEX
}%ignore

Using the well-foundedness theorems we can define tactics for inductive proofs.

=SML
val ⦏CSC_INDUCTION_T⦎ = WFCV_INDUCTION_T well_founded_CscPrec_thm;
val ⦏csc_induction_tac⦎ = wfcv_induction_tac well_founded_CscPrec_thm;
=TEX

=GFT
⦏csc_fc_thm⦎ =
   ⊢ ∀ x⦁ x ∈ Csyntax ⇒
	(∃c i⦁ Fun⋎u i ∧ Ordinal⋎u(Dom⋎u i)
	∧ (∀ y⦁ y ∈⋎u Ran⋎u i ⇒ y ∈ Csyntax)
	∧ x = c ↦⋎u i)
=TEX
=GFT
⦏¬∅⋎u_∈_csyntax_lemma⦎ =
   ⊢ ¬ ∅⋎u ∈ Csyntax

⦏¬∅⋎u_∈_csyntax_lemma2⦎ =
   ⊢ ∀ x⦁ x ∈ Csyntax ⇒ ¬ x = ∅⋎u

⦏¬∅⋎u_∈_csyntax_lemma3⦎ =
   ⊢ ∀ V x⦁ x ∈ V ∧ V ⊆ Csyntax ⇒ ¬ x = ∅⋎u
=TEX

\ignore{
=SML
local val _ = set_goal([], ⌜∀ x⦁ x ∈ Csyntax ⇒ (∃c i⦁ Fun⋎u i ∧ Ordinal⋎u(Dom⋎u i) ∧ (∀ y⦁ y ∈⋎u (Ran⋎u i) ⇒ y ∈ Csyntax) ∧ x = c ↦⋎u i)
⌝);
val _ = a (contr_tac);
val _ = a (lemma_tac ⌜CrepClosed (Csyntax \ {x})⌝
	THEN1 (rewrite_tac [get_spec ⌜CrepClosed⌝] THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
val _ = a (lemma_tac ⌜(∀y⦁ y ∈ X⋎u (Ran⋎u i) ⇒ y ∈ Csyntax)⌝
	THEN1 (REPEAT strip_tac));
(* *** Goal "1.1" *** *)
val _ = a (all_asm_fc_tac []);
(* *** Goal "1.2" *** *)
val _ = a (ALL_FC_T rewrite_tac [crepclosed_csyntax_thm]);
(* *** Goal "2" *** *)
val _ = a (lemma_tac ⌜(∀y⦁ y ∈⋎u (Ran⋎u i) ⇒ y ∈ Csyntax)⌝
	THEN1 (REPEAT strip_tac));
(* *** Goal "2.1" *** *)
val _ = a (lemma_tac ⌜y ∈ X⋎u (Ran⋎u i)⌝
	THEN1 (asm_rewrite_tac [X⋎u_def]));
val _ = a (all_asm_fc_tac []);
(* *** Goal "2.2" *** *)
val _ = a (spec_nth_asm_tac 5 ⌜c⌝);
val _ = a (spec_nth_asm_tac 1 ⌜i⌝ THEN all_asm_fc_tac []);
val _ = a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
val _ = a (asm_tac crepclosed_csyntax_lemma1);
val _ = a (spec_nth_asm_tac 1 ⌜Csyntax \ {x}⌝);
val _ = a (spec_nth_asm_tac 1 ⌜x⌝);
in val csc_fc_thm = save_pop_thm "csc_fc_thm";
end;

set_goal([], ⌜¬ ∅⋎u ∈ Csyntax⌝);
a (contr_tac);
a (fc_tac [csc_fc_thm] THEN POP_ASM_T ante_tac THEN rewrite_tac[]);
val ¬∅⋎u_∈_csyntax_lemma = save_pop_thm "¬∅⋎u_∈_csyntax_lemma";

set_goal([], ⌜∀x⦁ x ∈ Csyntax ⇒ ¬ x = ∅⋎u⌝);
a (contr_tac THEN var_elim_nth_asm_tac 1
	THEN POP_ASM_T ante_tac
	THEN rewrite_tac [¬∅⋎u_∈_csyntax_lemma]);
val ¬∅⋎u_∈_csyntax_lemma2 = save_pop_thm "¬∅⋎u_∈_csyntax_lemma2";
 
set_goal([], ⌜∀V x⦁ x ∈ V ∧ V ⊆ Csyntax ⇒ ¬ x = ∅⋎u⌝);
a (REPEAT strip_tac
	THEN lemma_tac ⌜x ∈ Csyntax⌝ THEN1 PC_T1 "hol1" asm_prove_tac[]
	THEN fc_tac [¬∅⋎u_∈_csyntax_lemma2]);
val ¬∅⋎u_∈_csyntax_lemma3 = save_pop_thm "¬∅⋎u_∈_csyntax_lemma3";

add_pc_thms "'icomb" [¬∅⋎u_∈_csyntax_lemma];
set_merge_pcs ["misc31", "'icomb"];
=TEX
}%ignore

=GFT
⦏csc_fc_thm2⦎ =
   ⊢ ∀c i⦁ c ↦⋎u i ∈ Csyntax ⇒ Fun⋎u i ∧ Ordinal⋎u (Dom⋎u i)
				∧ (∀ x⦁ x ∈⋎u (Ran⋎u i) ⇒ x ∈ Csyntax)

⦏cscprec_fc_thm⦎ =
   ⊢ ∀ c i x⦁ x ∈⋎u Ran⋎u i ⇒ CscPrec x (c ↦⋎u i)
=TEX

\ignore{
=SML
local val _ = set_goal([], ⌜∀c i⦁ c ↦⋎u i ∈ Csyntax ⇒ Fun⋎u i ∧ Ordinal⋎u (Dom⋎u i) ∧ (∀ x⦁ x ∈⋎u (Ran⋎u i) ⇒ x ∈ Csyntax)⌝);
val _ = a (REPEAT strip_tac THEN fc_tac[csc_fc_thm] THEN all_var_elim_asm_tac THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
in val csc_fc_thm2 = save_pop_thm "csc_fc_thm2";
end;

local val _ = set_goal([], ⌜∀c i x⦁ x ∈⋎u (Ran⋎u i) ⇒ CscPrec x (c ↦⋎u i)⌝);
val _ = a (rewrite_tac [get_spec ⌜CscPrec⌝]);
val _ = a (REPEAT strip_tac);
val _ = a (∃_tac ⌜c⌝ THEN ∃_tac ⌜i⌝ THEN asm_rewrite_tac[]);
in val cscprec_fc_thm = save_pop_thm "cscprec_fc_thm";
end;
=TEX
}%ignore

Inductive proofs using the well-foundedness of ScPrec are fiddly.
The following induction principle simplifies the proofs.

=GFT
⦏csyn_induction_thm⦎ =
   ⊢	(∀c i⦁ Fun⋎u i ∧ Ordinal⋎u(Dom⋎u i)
		∧ (∀x⦁ x ∈⋎u (Ran⋎u i) ⇒ x ∈ Csyntax ∧ p x)
		⇒ p (c ↦⋎u i))
	⇒ (∀ x⦁ x ∈ Csyntax ⇒ p x)
=TEX

\ignore{
=SML
set_goal([], ⌜(∀c i⦁ Fun⋎u i ∧ Ordinal⋎u(Dom⋎u i) ∧ (∀x⦁ x ∈⋎u (Ran⋎u i) ⇒ x ∈ Csyntax ∧ p x) ⇒ p (c ↦⋎u i))
	⇒ (∀ x⦁ x ∈ Csyntax ⇒ p x)⌝);
a (REPEAT strip_tac);
a (POP_ASM_T ante_tac THEN csc_induction_tac ⌜x⌝ THEN strip_tac);
a (fc_tac [csc_fc_thm]);
a (lemma_tac ⌜∀ x⦁ x ∈⋎u Ran⋎u i ⇒ x ∈ Csyntax ∧ p x⌝
	THEN (REPEAT strip_tac THEN all_asm_fc_tac[] THEN_TRY asm_rewrite_tac[]));
a (lemma_tac ⌜CscPrec x t⌝
	THEN1 (asm_rewrite_tac[CscPrec_def]));
(* *** Goal "1" *** *)
a (∃_tac ⌜c⌝ THEN ∃_tac ⌜i⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [tc_incr_thm] THEN all_asm_fc_tac[]);
val csyn_induction_thm = save_pop_thm "csyn_induction_thm";
=TEX
}%ignore

Using this induction principle an induction tactic is defined as follows:

=SML
fun ⦏icomb_induction_tac⦎ t (a,c) = (
	let val l1 = mk_app (mk_λ (t,c), t)
	    and l2 = mk_app (mk_app (mk_const ("∈", ⓣ'a GSU → 'a GSU SET → BOOL⌝), t),
					mk_const ("Csyntax", ⓣ'a GSU SET⌝))
	in  let val l3 = mk_∀ (t, mk_⇒ (l2, l1))
	in  LEMMA_T l1 (rewrite_thm_tac o rewrite_rule[])
	THEN DROP_ASM_T l2 ante_tac
	THEN LEMMA_T l3 (rewrite_thm_tac o rewrite_rule[])
	THEN bc_tac [csyn_induction_thm]
	THEN rewrite_tac[]
	THEN strip_tac
	end end) (a,c);
=TEX

This tactic expects an argument $t$ of type $TERM$ which is a free variable of type $ⓣ('a)GSU⌝$ whose sole occurrence in the assumptions is in an assumption $⌜ⓜt⌝ ∈ Csyntax⌝$, and results in a single subgoal.
The conclusion of the subgoal is as in the original except that free occurrences of $⌜t⌝$ have been replaced by $⌜c ↦⋎u i⌝$.
The assumption 
=INLINEFT
⌜ⓜt⌝∈Csyntax⌝
=TEX
 is replaced by three new assumptions asserting that $⌜i⌝$ is a function, that its domain is an ordinal, and that everything in its range is a member of \emph{Csyntax} for which the property expressed in the conclusion holds.

A slight variant on that is:

=GFT
⦏csyn_induction_thm2⦎ =
   ⊢	(∀c i⦁ Seq⋎u i
		∧ (∀x⦁ x ∈⋎u (Ran⋎u i) ⇒ x ∈ Csyntax ∧ p x)
		⇒ p (c ↦⋎u i))
	⇒ (∀ x⦁ x ∈ Csyntax ⇒ p x)
=TEX

\ignore{
=SML
set_goal([], ⌜(∀c i⦁ Seq⋎u i ∧ (∀x⦁ x ∈⋎u (Ran⋎u i) ⇒ x ∈ Csyntax ∧ p x) ⇒ p (c ↦⋎u i))
	⇒ (∀ x⦁ x ∈ Csyntax ⇒ p x)⌝);
a (rewrite_tac [Seq⋎u_def, prove_rule [] ⌜∀A B C⦁ ((A ∧ B) ∧ C) ⇔ (A ∧ B ∧ C)⌝]);
a (accept_tac csyn_induction_thm);
val csyn_induction_thm2 = save_pop_thm "csyn_induction_thm2";
=TEX
}%ignore


=SML
fun ⦏icomb_induction_tac2⦎ t (a,c) = (
	let val l1 = mk_app (mk_λ (t,c), t)
	    and l2 = mk_app (mk_app (mk_const ("∈", ⓣ'a GSU → 'a GSU SET → BOOL⌝), t),
					mk_const ("Csyntax", ⓣ'a GSU SET⌝))
	in  let val l3 = mk_∀ (t, mk_⇒ (l2, l1))
	in  LEMMA_T l1 (rewrite_thm_tac o rewrite_rule[])
	THEN DROP_ASM_T l2 ante_tac
	THEN LEMMA_T l3 (rewrite_thm_tac o rewrite_rule[])
	THEN bc_tac [csyn_induction_thm2]
	THEN rewrite_tac[]
	THEN strip_tac
	end end) (a,c);
=TEX

This tactic expects an argument $t$ of type $TERM$ which is a free variable of type $ⓣ('a)GSU⌝$ whose sole occurrence in the assumptions is in an assumption $⌜ⓜt⌝ ∈ Csyntax⌝$, and results in a single subgoal.
The conclusion of the subgoal is as in the original except that free occurrences of $⌜t⌝$ have been replaced by $⌜c ↦⋎u i⌝$.
The assumption 
=INLINEFT
⌜ⓜt⌝∈Csyntax⌝
=TEX
 is replaced by three new assumptions asserting that $⌜i⌝$ is a sequence, and that everything in its range is a member of \emph{Csyntax} for which the property expressed in the conclusion holds.

=GFT
⦏csyntax_pair_thm⦎ = ⊢ ∀ t⦁ t ∈ Csyntax ⇒ (∃ c ts⦁ t = c ↦⋎u ts)
=TEX

\ignore{
=SML
set_goal([], ⌜∀t⦁ t ∈ Csyntax ⇒ ∃c ts⦁ t = c ↦⋎u ts⌝);
a (strip_tac THEN strip_tac);
a (icomb_induction_tac2 ⌜t⌝);
a (∃_tac ⌜c⌝ THEN ∃_tac ⌜i⌝ THEN rewrite_tac[]);
val csyntax_pair_thm = save_pop_thm "csyntax_pair_thm";
=TEX
}%ignore

=IGN
open_theory "icomb";
set_pc "icomb";
set_goal([⌜t:('a GSU) ∈ Csyntax⌝, ⌜q:BOOL⌝], ⌜p:('a GSU→BOOL) t⌝);
a (icomb_induction_tac ⌜t⌝);
drop_main_goal();
=TEX


The following function provides domain restriction of a function over $ⓣ'a\ GSU⌝$.
Since this is an operation on total functions, the effect is achieved by delivering a function which returns the same value for all arguments outside the restricted domain.
The purpose is to constrain recursion to be well founded, so the possibility of returning a function completely unconstrained in what it does off the restricted domain does not suffice (we would not be able to prove that the domain restriction had done anything at all).
The domain is a set, but the constraint is to its transitive closure.

=SML
declare_infix(310, "◁⋎u⋎e");
=TEX

ⓈHOLCONST
│ $⦏◁⋎u⋎e⦎ : 'a GSU → ('a GSU → 'b) → ('a GSU → 'b)
├───────────
│ ∀s f⦁ s ◁⋎u⋎e f = λt⦁ if t ∈⋎u⋏+ s then f t else εx⦁T
■

A recursion lemma suitable for consistency proofs of primitive recursive definitions over our syntax can now be proven, this supports definition by primitive recursion of functions over the syntax.

=GFT
⦏csc_recursion_lemma⦎ =
   ⊢ ∀af⦁ ∃f⦁ ∀c i⦁ f (c ↦⋎u i) = af (i ◁⋎u⋎e f) c i
=TEX


\ignore{
=SML
val ◁⋎u⋎e_def = get_spec ⌜$◁⋎u⋎e⌝;

set_goal([], ⌜∀(af:('a GSU → 'b) → 'a GSU → 'a GSU → 'b)⦁ ∃(f:'a GSU → 'b)⦁
	∀c i⦁ f (c ↦⋎u i) = af (i ◁⋎u⋎e f) c i⌝);
val _ = a (REPEAT strip_tac);
val _ = a (lemma_tac ⌜∃g:((('a)GSU→'b)→('a)GSU→'b)⦁
	g = λf x⦁ if (∃c i⦁ x = c ↦⋎u i) 
		then af ((Snd⋎u x) ◁⋎u⋎e f) (Fst⋎u x) (Snd⋎u x)
		else εx⦁T⌝
	THEN1 prove_∃_tac);
val _ = a (lemma_tac ⌜g respects $∈⋎u⋏+⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜$respects⌝] THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (cond_cases_tac ⌜∃ c i⦁ x = c ↦⋎u i⌝);
a (LEMMA_T ⌜Snd⋎u x ◁⋎u⋎e g' = Snd⋎u x ◁⋎u⋎e h⌝ rewrite_thm_tac);
a (rewrite_tac [◁⋎u⋎e_def] THEN strip_tac);
a (cond_cases_tac ⌜x' ∈⋎u⋏+ Snd⋎u x⌝);
a (spec_nth_asm_tac 3 ⌜x'⌝ THEN_TRY asm_rewrite_tac[]);
a (lemma_tac ⌜Snd⋎u x ∈⋎u⋏+ x⌝ THEN1 asm_rewrite_tac[tc∈⋎u_↦⋎u_right_thm]);
a (all_fc_tac [tc∈⋎u_trans_thm]);
a (all_fc_tac [tc_incr_thm]);
(* *** Goal "2" *** *)
a (∃_tac ⌜fix g⌝);
a (asm_tac gsu_wftc_thm2);
a (all_fc_tac [get_spec ⌜fix⌝]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[] THEN strip_tac);
a (GET_NTH_ASM_T 1 (once_rewrite_thm_tac o map_eq_sym_rule));
a (rewrite_tac[] THEN REPEAT strip_tac);
a (cond_cases_tac ⌜∃ c' i'⦁ c = c' ∧ i = i'⌝);
a (spec_nth_asm_tac 1 ⌜c⌝);
a (spec_nth_asm_tac 1 ⌜i⌝);
val csc_recursion_lemma = save_pop_thm "csc_recursion_lemma";
=TEX
}%ignore

This is (when proven) plugged into proof context {\it 'icomb} for use in consistency proofs.

=SML
add_∃_cd_thms [csc_recursion_lemma] "'icomb";
set_merge_pcs ["misc31", "'icomb"];
=TEX

This is just to test the recursion theorem.

ⓈHOLCONST
│ ⦏CscRank⦎ : 'a GSU → 'a GSU
├───────────
│ ∀c i⦁ CscRank (c ↦⋎u i) =
	⋃⋎u (Imagep⋎u Suc⋎u ((Imagep⋎u (i ◁⋎u⋎e CscRank)) (Ran⋎u i)))
■


\subsubsection{More Closure Properties}

In order to prove that various expressions yield elements of Csyntax further definitions and theorems are required.

The construction of terms is accomplished primarily by the construction of sequences of terms.
For concision in expressing closure conditions of operators over such sequences we give a name for a sequence of terms in our syntax.

ⓈHOLCONST
│ ⦏CscSeq⦎ : 'a GSU → BOOL
├───────────
│ ∀s⦁ CscSeq s ⇔ Seq⋎u s ∧ ∀t⦁ t ∈⋎u Ran⋎u s ⇒ t ∈ Csyntax
■

=GFT
=TEX

\ignore{
=SML
val CscSeq_def = get_spec ⌜CscSeq⌝;

set_goal([], ⌜∀s t⦁ CscSeq s ∧ CscSeq t ⇒ CscSeq (s @⋎u t)⌝);
a (rewrite_tac[CscSeq_def]);
a (REPEAT strip_tac);

=TEX
}%ignore


\subsubsection{Finitary Constant Combinators}

Our syntax does not include the standard finitary application, to do this you have to append the argument to the sequence of arguments already present on the function.
It's handy to define a function in HOL which does this operation (i.e. which constructs the required combinatory term).
For this we will use an infix bare subscript $c$.

=SML
declare_infix (350, "⋎c");
=TEX

ⓈHOLCONST
│ $⦏⋎c⦎ : 'a GSU → 'a GSU → 'a GSU
├───────────
│ ∀f a⦁ f ⋎c a = let fc = Fst⋎u f
│		and fa = Snd⋎u f
│		in fc ↦⋎u (fa @⋎u (Unit⋎u (∅⋎u ↦⋎u a)))
■

We also define a function corresponding to a constant constructor.
This requires the constant `name' as argument and returns a combinator with that name at the head and an empty list of arguments.

ⓈHOLCONST
│ $⦏MkCcon⦎ : 'a GSU → 'a GSU
├───────────
│ ∀n⦁ MkCcon n = n ↦⋎u ∅⋎u
■

=GFT
⦏MkCcon_∈_Csyntax_thm⦎ = ⊢ ∀ x⦁ MkCcon x ∈ Csyntax
=TEX

\ignore{
=SML
val MkCcon_def = get_spec ⌜MkCcon⌝;

set_goal([], ⌜∀x:'a GSU⦁ MkCcon x ∈ Csyntax⌝);
a (strip_tac);
a (rewrite_tac [MkCcon_def]);
a (lemma_tac ⌜Fun⋎u (∅⋎u:'a GSU)
         ∧ Ordinal⋎u (Dom⋎u (∅⋎u:'a GSU))
         ∧ (∀ x:'a GSU⦁ x ∈ X⋎u (Ran⋎u ∅⋎u) ⇒ x ∈ Csyntax)⌝
	THEN1 rewrite_tac[ord⋎u_∅⋎u_thm]);
a (all_fc_tac [crepclosed_csyntax_thm]);
a (asm_rewrite_tac[]);
val MkCcon_∈_Csyntax_thm = save_pop_thm "MkCcon_∈_Csyntax_thm";

add_rw_thms [MkCcon_∈_Csyntax_thm] "'icomb";
add_sc_thms [MkCcon_∈_Csyntax_thm] "'icomb";
set_merge_pcs ["misc31", "'icomb"];
=TEX
}%ignore

Using which we name the primitive combinators.

We use an initial segment of the natural numbers as the names of combinators in the infinitary object langauge, but we give more intuitive names in our metalanguage (HOL) for the resulting combinatory term. 

First two finitary pure combinators:

ⓈHOLCONST
│ ⦏S⋎c⦎ : 'a GSU
├───────────
│ S⋎c = MkCcon (Nat⋎u 0)
■

ⓈHOLCONST
│ ⦏K⋎c⦎ : 'a GSU
├───────────
│ K⋎c = MkCcon (Nat⋎u 1)
■

Then the sole illative combinator, which is equality or equivalence.

ⓈHOLCONST
│ $⦏≡⋎c⦎ : 'a GSU
├───────────
│ $≡⋎c = MkCcon (Nat⋎u 2)
■

Various useful combinatorial expressions may now be named.

=GFT
	I = λx⦁x
=TEX

ⓈHOLCONST
│ $⦏I⋎c⦎ : 'a GSU
├───────────
│ I⋎c = (S⋎c ⋎c K⋎c) ⋎c K⋎c
■

The truth values may be represented as two projections from the argument list.

=GFT
	T = λx y⦁ x
=TEX

ⓈHOLCONST
│ $⦏T⋎c⦎ : 'a GSU
├───────────
│ T⋎c = K⋎c
■

=GFT
	F = λx y⦁ y
=TEX

ⓈHOLCONST
│ $⦏F⋎c⦎ : 'a GSU
├───────────
│ F⋎c = K⋎c ⋎c I⋎c
■

Conditionals may then be represented by applying the condition to the two alternatives:

=GFT
	if x then y else z = xyz
=TEX

ⓈHOLCONST
│ $⦏If⋎c⦎ : 'a GSU → 'a GSU → 'a GSU → 'a GSU
├───────────
│ ∀x y z⦁ If⋎c x y z = (x ⋎c y) ⋎c z
■

Natural numbers may be represented as iterators (though this is unlikely to be how they are represented in the target illative lambda calculus):

Thus, zero is the identity function.

ⓈHOLCONST
│ $⦏0⋎c⦎ : 'a GSU
├───────────
│ 0⋎c = I⋎c
■

=GFT
	Suc n = λf x⦁ f((n f)x)
	= λf⦁ λx⦁ f((n f)x)
	= λf⦁ S (K f) (n f)
	= S (λf⦁ S (K f)) n
	= S (S (K S) K) n
	= λf⦁ ((S (K S) K) f) (n f)
	= λf⦁ ((λx⦁ ((K S) x) (K x)) f) (n f)
	= λf⦁ ((λx⦁ S (K x)) f) (n f)
	= λf⦁ S (K f) (n f)
	= λf x⦁ ((K f x) ((n f) x))
	= λf x⦁ f ((n f) x)
=TEX

ⓈHOLCONST
│ $⦏Suc⋎c⦎ : 'a GSU
├───────────
│ Suc⋎c = S⋎c ⋎c (S⋎c ⋎c (K⋎c ⋎c S⋎c) ⋎c K⋎c)
■

However, we require a representation of transfinite ordinals.
It is not clear how this could be obtained as iterators. 

It is probable that arithmetic will be arrived at in a manner more similar to that adopted in a well-founded set theory.
Such a set theory could be derived within the target illative lambda-calculus as a theory of characteristic functions, provided that we have a sufficiency of such functions, which the infinitary combinators are intended to ensure.

\subsubsection{Infinitary Combinators}

The idea is to get a system which is ontologically equivalent to the standard interpretations of well-founded set theory with large cardinal axioms.
By equivalent here I mean something like mutually interpretable, but the interpretations at stake here are correspondences between the ontologies, not interpretability of theories.
However, this is the case without the infinitary combinators, so what I am looking for is a bit more.

I want to ensure that the functions available as combinators are all functions with small graphs (and a decent collection of those with large graphs, but they are not our present concern).
The infinitary combinators are introduced to permit a function to be defined in extension, so long as its graph is ``small'' (i.e. smaller than the universe of discourse).

It is not entirely straightforward to do this.
The present proposal is to use three infinitary combinators.

First an inert combinator which is used to construct lists or sequences.

ⓈHOLCONST
│ $⦏Φ⋎c⦎ : 'a GSU → 'a GSU
├───────────
│ ∀s⦁ Φ⋎c s = (Nat⋎u 3) ↦⋎u s
■

Such combinators are irreducible and injective, and it is therefore possible in principle to extract the components, for which we supply the following projection combinator.

The projection combinator takes two sequences, the first effectively determining an element of the second to be extracted.
Normally this would be supplied with two sequences of equal length and the element to be extracted from the second would be the one which corresponds to the first element of the first sequence which reduces to `T', provided that all previous values reduce to `F' (otherwise no element is selected, i.e. no reduction is possible).

ⓈHOLCONST
│ $⦏Ω⋎c⦎ : 'a GSU
├───────────
│ Ω⋎c = MkCcon (Nat⋎u 4)
■

One may think of the first sequence supplied as an argument to $Ω⋎c$ as an ordinal $α$ and of $Ω⋎c\ ⋎c\ α\ ⋎c\ β$ as selecting the $α^{th}$ element of $β$, but when we do eventually come to the theory of ordinals we will not use this representation.
Furthermore note that this way of indicating the element to be selected is determined primarily because it is convenient for constructing infinitary `case' constructions, and hence for the definition of arbitrary functions.

To achieve this effect we need one further infinitary combinator, a mapping combinator.

This combinator expects its second argument to be a sequence, and maps its first argument over the elements of the sequence, returning a sequence which consists of the elements of the original sequence transformed by the function supplied as the first argument.
Of course, the intended ``transformation'' will only take place as the combinators in the new sequence are themselves reduced, the reduction arising from this combinator is just to apply the function to each element giving a sequence of applications.

ⓈHOLCONST
│ $⦏Ψ⋎c⦎ : 'a GSU
├───────────
│ Ψ⋎c = MkCcon (Nat⋎u 5)
■

These three combinators together may be used to define a function as a graph in the following way.
Form two corresponding sequences, the first of values in the domain of the desired function, the second having at each position the value of the function at that point.
The required function takes some value $⌜x⌝$, and maps $⌜≡ ⋎c\ x⌝$ over the first argument, and then uses that list to determine which value to select from the second list.
The effect of the mapping operation is to create a sequence in which every element is the truth value of the claim that it is equal to the argument $⌜x⌝$, which, provided that all terms normalise will be the a representation of the position in the list of the argument, which can then be used to select the required value from the other sequence.

An infinitary case combinator might therefore be obtained from these three combinators as follows.

=GFT
	Gfun⋎c	= λx y z⦁ Ω ⋎c (Ψ ⋎c (≡ ⋎c z) ⋎c x) ⋎c y
=TEX

It is not expected that this will ever be done, it is important only that it \emph{could} be done (if only by some inaccessibly infinite deity), and this is intended to ensure that we can do `classical' mathematics in pretty much the normal way within our target calculus, which will probably be demonstrated by reconstructing a strong set theory within it.
The ability to represent arbitrary functions on infinite domains (e.g. over the reals) by such means depends upon the axiom of choice, which we do have at our disposal.
It is intended also that the target illative lambda calculus will benefit (or perhaps in some eyes be blighted by) a choice principle.

=GFT
⦏MkCcons_∈_Csyntax_clauses⦎ = ⊢ S⋎c ∈ Csyntax
       ∧ K⋎c ∈ Csyntax
       ∧ $≡⋎c ∈ Csyntax
       ∧ T⋎c ∈ Csyntax
       ∧ Ω⋎c ∈ Csyntax
       ∧ Ψ⋎c ∈ Csyntax
=TEX

\ignore{
=SML
val S⋎c_def = get_spec ⌜S⋎c⌝;
val K⋎c_def = get_spec ⌜K⋎c⌝;
val I⋎c_def = get_spec ⌜I⋎c⌝;
val ≡⋎c_def = get_spec ⌜$≡⋎c⌝;
val T⋎c_def = get_spec ⌜T⋎c⌝;
val F⋎c_def = get_spec ⌜F⋎c⌝;
val Φ⋎c_def = get_spec ⌜Φ⋎c⌝;
val Ω⋎c_def = get_spec ⌜Ω⋎c⌝;
val Ψ⋎c_def = get_spec ⌜Ψ⋎c⌝;
=IGN
val ⋎c_def = get_spec ⌜$⋎c⌝;
=SML
set_goal([], ⌜S⋎c ∈ Csyntax
	∧ K⋎c ∈ Csyntax
	∧ $≡⋎c ∈ Csyntax
	∧ T⋎c ∈ Csyntax
	∧ Ω⋎c ∈ Csyntax
	∧ Ψ⋎c ∈ Csyntax
(*	∧ ⋎c ∈ Csyntax
	∧ ⋎c ∈ Csyntax
*)⌝);
a (rewrite_tac[S⋎c_def, K⋎c_def, ≡⋎c_def, T⋎c_def, Ω⋎c_def, Ψ⋎c_def, MkCcon_∈_Csyntax_thm]);
val MkCcons_∈_Csyntax_clauses = pop_thm ();

add_rw_thms [MkCcons_∈_Csyntax_clauses] "'icomb";
add_sc_thms [MkCcons_∈_Csyntax_clauses] "'icomb";
set_merge_pcs ["misc31", "'icomb"];

=TEX
}%ignore

\subsection{Semantics}

The following semantics is a first crude cut.
Conceivably it might be `correct' but certainly it is not very nicely structured.
A good structure is only likely to emerge as I get a handle on the proofs I need to do with it.

The semantics which follows must be in effect a monotone functor, so that we can obtain a least fixed point.
In my previous attempts for a non well-founded set theory I used truth functions into a suitably ordered four-valued set of truth values, but in this case a simpler approach seems possible, in which we use a functor over standard bi-valent relations, ordered by inclusion (of the set of ordered pairs of which the relation is the characteristic function).
The relation in question is that of \emph{convertibility}.

To understand how this works it is best to think of it in other terms, as a \emph{partial} equivalence relation.
A \emph{partial} equivalence relation is one for which some pairs are equivalent and some pairs are not equivalent, and the status of others is unknown.
The relation we work with will be the positive part of this partial equivalence relation.
However, it will contain coded within it also the negative part.

This encoding occurs through the conversions for applications of the equivalence combinator.
The equivalence combinator is intended to be the relation of convertibility, but for reasons connected with the paradoxes it cannot be total.
This is because the notion of convertibility at stake involves the conversions for equivalence expressions, and so the dependency is recursive.
Defining convertibility as the least fixed point of our functor gives is recursive definition which will fail to be well-founded for some pairs of combinators.
For these pairs, equivalence will not reduce, and it will therefore be a partial equivalence relation.

The functor is defined in two parts, respectively for the positive and the negative parts of the convertibility relation.
The two are then put together.

The positive part is an equivalence relation which ultimately corresponds exactly to convertibility.

The negative part is an approximation to distinctness, but there will be some pairs of terms which are not convertible which never appear in the negative part (possibly because if they did, they would then appear also in the positive part engendering contradiction, this is what we would expect to happen with the assertion that the Russell set is a member of itself, if it comes out true, then it will also come out false).

The negative part plays a role in the definition of the positive part, because an application of an equivalence combinator reduces to $F⋎c$ only if the two arguments are related under this negative part of the partial equivalence relation.

Of course, the negative part is not itself an equivalence relation.
The requirement that the whole (both the positive and the negative parts) is a partial equivalence relation is simply the usual conditions (reflexive, symmetric and transitive),  on the positive part.
We also require that the two parts don't disagree!

We consider the definition in two parts, the positive part and the negative part.

The positive part of the functor is a functor which takes a convertibility relation, closes it up under all the direct conversions for combinators other than the equivalence combinator.
The negative part then computes a set of inequalities from this convertibility relation.
The postive and negative parts are then incorporated into the relation as conversions of equations.

\paragraph{positive part}

The positive part is defined in three stages.

First \emph{direct reduction} is defined for the \emph{Pure} combinators \index{combinator!pure}.
These are combined into a closure operator which obtains from any relation the smallest equivalence relation closed under direct reduction subject to a rule of extensionality (equivalent functions applied to equivalent arguments give equivalent combinators).
In this context the pure combinators are those for which direct reduction is definable independently of the other combinators.

The second stage is the definition of direct reducibility for the illative equivalence combinator, which is done \emph{relative to} some given partial equivalence relation.

The third stage is to combine the two previous definitions into a partial functor, which takes a partial equivalence relation and delivers the positive part of a partial equivalence relation.
It does this by applying the definition of direct reducibility of equivalence to the partial equivalence to get a first version of the positive part, and then closing this under the closure operator obtained from the definitions of the other combinators.

\paragraph{negative part}

There are two parts to this.

Firstly a fixed part under which all constants are known to be distinct.

Secondly we infer that two combinatorial expressions are distinct if when applied to equal arguments they yield distinct results.
To obtain such results you need to have both positive and negative results, so this part has to be defined as a function over a partial equivalence relation.

I now see that the negative part is derivable from the positive part, in which it is incorporated as reductions of equations to $F⋎c$.
Its not obvious whether it is better to extract the information in that way or to maintain it separately as I first set out to do.
I will hedge my bets a bit until I get a stronger sense of which is the best way to go.

\subsubsection{The Combinators}

We have five combinatory constants, S, K, $≡$ (convertability), $Ω$ (projection), and $Ψ$ (map), of which the last two are infinitary, the first three being much the same as you would expect in a finitary illative combinatory logic in which the illative primitive is equality.

The rationale for this is that the infinitary aspect is of marginal significance, and may be thought of as supplying strength, just as in the role of large cardinals in set theory, the strength is bound up with ontological plenitude.
It should be like an afterthough, the main features of the system should arise in the finitary case from the first three combinators, and the principle innovation is in the approach to giving meaning to $≡$.

The definitions of the pure combinators (all except $≡$) are given as conversion rules, whose reflexive symmetric transitive closure give a first approximation to the meaning of $≡$.
If we assume given some meaning for $≡$ and obtain from it a second version by combining it with the conversion rules for the other combinators, then we have a functor over possible meanings for $≡$, which will be monotone.
The least fixed point will then be used to determine the semantics of the infinitary combinatory logic.

\subsubsection{Direct Conversions for the Pure Combinators}

These are defined as relations over \emph{Csyntax}.

=SML
declare_type_abbrev("⦏RED⦎", ["'a"], ⓣ'a GSU → 'a GSU → BOOL⌝);
=TEX


ⓈHOLCONST
│ ⦏Kred⦎ : 'a RED
├───────────
│ ∀s t⦁ Kred s t ⇔ ∃x y⦁ s = (K⋎c ⋎c x) ⋎c y ∧ t = x
■

ⓈHOLCONST
│ ⦏Sred⦎ : 'a RED
├───────────
│ ∀s t⦁ Sred s t ⇔ ∃x y z⦁ s = ((S⋎c ⋎c x) ⋎c y) ⋎c z ∧ t = (x ⋎c z) ⋎c (y ⋎c z)
■

The projection combinator is more complicated.

ⓈHOLCONST
│ ⦏Ω⋎r⋎e⋎d⦎ : 'a RED
├───────────
│ ∀s t⦁ Ω⋎r⋎e⋎d s t ⇔ (∃k l m n⦁ Dom⋎u k = Dom⋎u m
		∧ Ordinal⋎u (Dom⋎u k) ∧ Ran⋎u k = Unit⋎u F⋎c
		∧ s = Ω⋎c ⋎c (Φ⋎c (k @⋎u l)) ⋎c (Φ⋎c (m @⋎u n)) 
		∧ t = Ω⋎c ⋎c (Φ⋎c l) ⋎c (Φ⋎c n))
	∨ (∃k m⦁ ∅⋎u ↦⋎u T⋎c ∈⋎u k
		∧ ∅⋎u ↦⋎u t ∈⋎u m
		∧ s = Ω⋎c ⋎c (Φ⋎c k) ⋎c (Φ⋎c m))
■ 

As is the infinitary ``map''.

ⓈHOLCONST
│ ⦏Ψ⋎r⋎e⋎d⦎ : 'a RED
├───────────
│ ∀s t⦁ Ψ⋎r⋎e⋎d s t ⇔ ∃f l m⦁ Dom⋎u l = Dom⋎u m
│		∧ Ordinal⋎u (Dom⋎u l)
│		∧ m = (λ⋎u x⦁ f ⋎c x)(Dom⋎u l)
│		∧ s = (Ψ⋎c ⋎c f) ⋎c (Φ⋎c l)
│		∧ t = Φ⋎c m
■

Direct combinatorial reducibility is the union of these relationships.
Because the infinitary combinators are so much more complex than the finitary combinators in ways which are probably not pertinent to the method of defining equivalence, I propose to separate out the two kinds of reduction, and undertake the development in the first instance using only the finitary part.

The finitary combinators yield this notion of reducibility:

ⓈHOLCONST
│ ⦏DComRed⦎ : 'a RED
├───────────
│ ∀s t⦁ DComRed s t ⇔ Kred s t ∨ Sred s t
■ 

With the following for the infinitary combinators, which we will consider no further until we have demonstrated the viability of our method using only the finitary combinators.

ⓈHOLCONST
│ ⦏DiComRed⦎ : 'a RED
├───────────
│ ∀s t⦁ DiComRed s t ⇔ Ω⋎r⋎e⋎d s t ∨ Ψ⋎r⋎e⋎d s t 
■ 

ⓈHOLCONST
│ ⦏DbComRed⦎ : 'a RED
├───────────
│ ∀s t⦁ DbComRed s t ⇔ Kred s t ∨ Sred s t ∨ Ω⋎r⋎e⋎d s t ∨ Ψ⋎r⋎e⋎d s t 
■ 

\subsubsection{Extraction of Negative Part}

Since the negative part of the partial equivalence relation (and the positive part for that matter) is encoded in the positive part through reductions of equivalences, it is possible to recover it from the positive part.

This is how it is done:

ⓈHOLCONST
│ ⦏Np⦎ : ('a RED) → ('a RED)
├───────────
│ ∀r⦁ Np r = λx y⦁ r (($≡⋎c ⋎c x) ⋎c y) F⋎c
■

This just says that two terms are distinct if the equivalence between them converts to $F⋎c$.

\subsubsection{Equality}

We now consider the question, when can we know that two combinators are equal or not equal.

The first obvious principle is that if two combinators are convertible then they are equal.
We cannot adopt the converse principle, that two combinators which are not convertible are distinct, because the equality conditions feed into the conversion rules through the equality combinator.
So we have to have some definite criteria for distinctness which we are confident will not include any combinator pairs which might ever be found to be convertible.

There are three parts to these criteria for distinctness.

The first part is that all the constants are to be considered distinct.
This is consistent with the reduction rules for those constants to which we assign a definite meaning.

This provides an initial value for the inequality relation.

ⓈHOLCONST
│ ⦏Ineq0⦎ : 'a RED
├───────────
│ Ineq0 = λx y⦁	∃v w⦁ x = MkCcon v ∧ y = MkCcon w ∧ ¬ v = w	
■ 

The second part is that if two combinators when applied to equal lists of arguments reduce to combinators which are known to be distinct, then they are themselves distinct.

We need a closure operation which will take a notion of inequality and add to it any further inequalities which are immediately apparent from that inequality relation using the second rule just cited.

ⓈHOLCONST
│ ⦏EqSeq⦎ : ('a RED) → ('a RED)
├───────────
│ ∀eq⦁ EqSeq eq = λv w⦁ Fun⋎u v ∧ Fun⋎u w ∧  Dom⋎u v = Dom⋎u w ∧ Ordinal⋎u (Dom⋎u v)
│		∧ ∀x⦁ x ∈⋎u Dom⋎u v ⇒ eq (v ⋎u x) (w ⋎u x)
■

ⓈHOLCONST
│ ⦏IneqStep⦎ : ('a RED) → ('a RED)
├───────────
│ ∀eq⦁ IneqStep eq = λx y⦁ Ineq0 x y ∨ Np eq x y
│			∨ ∃v w⦁ EqSeq eq v w ∧ Np eq (x ⋎c v) (y ⋎c w)
■

\subsubsection{Illative Reduction}

Reduction for the illative combinator $≡⋎c$ is intended to encapsulate reducibility as a whole.
We could define such a notion here in terms of closure of the reducibility relation for the pure combinators, but this would fall short of the entire reducibility relation by not recognising the reductions it introduces.
The definition needs to be recursive, reducibility needs to be defined in terms of itself.

Such a recursive definition can be realised by taking a fixed point of a functor which defines reducibility given some supposed definition of reducibility.

In constructing such a functor we need to specify the reductions which take place on applications of the equality combinator, which will be done using the supplied equivalence relation.
This will be a partial relation in the form of two disjoint relations, one positive and one negative.
If the positive relation holds over the arguments the equation reduces to $T⋎c$ if the negative relation holds the equation reduces to $F⋎c$.

ⓈHOLCONST
│ ⦏EqStep⦎ : ('a RED) → ('a RED)
├───────────
│ ∀eq⦁ EqStep eq = λv w⦁ ∃c i1 i2⦁ c ↦⋎u i1 ∈ Csyntax ∧ c ↦⋎u i2 ∈ Csyntax
│	∧ Dom⋎u i1 = Dom⋎u i2 ∧ (∀x⦁ x ∈⋎u Dom⋎u i1 ⇒ eq (i1 ⋎c x) (i2 ⋎c x))
■

ⓈHOLCONST
│ ⦏≡⋎r⋎e⋎d⦎ : ('a RED) → ('a RED)
├───────────
│ ∀eq⦁ ≡⋎r⋎e⋎d eq = λx y⦁ ∃l m⦁ x = (($≡⋎c ⋎c l) ⋎c m)
│			∧ (EqStep eq x y ∧ y = T⋎c ∨ IneqStep eq x y ∧ y = F⋎c)
■

\subsubsection{Closure}

There must be a name for this.

I have two versions, not sure yet which to use.

ⓈHOLCONST
│ ⦏RedClosed1⦎ : ('a RED) → BOOL
├───────────
│ ∀r⦁ RedClosed1 r = ∀c i1 i2⦁ c ↦⋎u i1 ∈ Csyntax ∧ c ↦⋎u i2 ∈ Csyntax
│	∧ Dom⋎u i1 = Dom⋎u i2 ∧ (∀x⦁ x ∈⋎u Dom⋎u i1 ⇒ r (i1 ⋎c x) (i2 ⋎c x))
│	⇒ r (c ↦⋎u i1) (c ↦⋎u i2)
■ 

ⓈHOLCONST
│ ⦏RedClosed2⦎ : ('a RED) → BOOL
├───────────
│ ∀r⦁ RedClosed2 r = ∀c d e f g h⦁ c ↦⋎u e ∈ Csyntax ∧ d ↦⋎u f ∈ Csyntax
│	∧ r (c ↦⋎u e) (d ↦⋎u f) ∧ EqSeq r g h 
│	⇒ r (c ↦⋎u e @⋎u g) (c ↦⋎u f @⋎u h)
■ 

I'll use them both pro-tem.

ⓈHOLCONST
│ ⦏RedClosure⦎ : ('a RED) → ('a RED)
├───────────
│ ∀r⦁ RedClosure r = Snd (EquivClosure
	(Csyntax, λx y⦁ ∀r1⦁ RedClosed1 r1 ∧ RedClosed2 r1 ∧ (Csyntax, r) ⊆ (Csyntax, r1)
			⇒ r1 x y))
■ 

\subsubsection{The Semantic Functor}

The functor with which we define equivalence must a monotone functor over partial equivalence relations.
It requires, or rather consists of a positive and a negative closure operator, each of which has access to the partial equivalence relation and delivers one half of the resulting partial equivalence relation.

ⓈHOLCONST
│ ⦏ILamFunct⦎ : ('a RED) → ('a RED)
├───────────
│ ∀r⦁ ILamFunct r = RedClosure (≡⋎r⋎e⋎d r)
■ 

To take a fixed point we define a version of this as an operator over sets.

ⓈHOLCONST
│ ⦏ILamFunctS⦎ : ('a GSU × 'a GSU)SET → ('a GSU × 'a GSU)SET
├───────────
│ ∀s⦁ ILamFunctS s = {x | ILamFunct(λx y⦁ (x,y) ∈ s) (Fst x)(Snd x)}
■ 

\subsubsection{Equivalence}

Pure infinitary combinatorial equivalence is then:

ⓈHOLCONST
│ ⦏PIComEq⦎ : 'a GSU SET × ('a GSU → 'a GSU → BOOL)
├───────────
│ PIComEq = EquivClosure(Csyntax, λx y⦁ (x,y) ∈ Lfp ILamFunctS)
■ 

=GFT
⦏Equiv_PIComEq_thm⦎ = ⊢ Equiv PIComEq
⦏Fst_PIComEq_thm⦎ = ⊢ Fst PIComEq = Csyntax
⦏CSyntax_PIComEq_thm⦎ = ⊢ ∀ x⦁ x ∈ Csyntax ⇒ x ∈ EquivClass PIComEq x
=TEX

\ignore{
=SML
val RedClosure_def = get_spec ⌜RedClosure⌝;
val ILamFunct_def = get_spec ⌜ILamFunct⌝;
val ILamFunctS_def = get_spec ⌜ILamFunctS⌝;
val PIComEq_def = get_spec ⌜PIComEq⌝;

set_goal([], ⌜Equiv PIComEq⌝);
a (rewrite_tac [PIComEq_def, Equiv_EquivClosure_thm]);
val Equiv_PIComEq_thm = save_pop_thm "Equiv_PIComEq_thm";

set_goal([], ⌜Fst PIComEq = Csyntax⌝);
a (rewrite_tac [PIComEq_def, Fst_EquivClosure_thm]);
val Fst_PIComEq_thm = pop_thm();

set_goal([], ⌜∀x⦁ x ∈ Csyntax ⇒ x ∈ EquivClass PIComEq x⌝);
a (REPEAT strip_tac THEN split_pair_rewrite_tac [⌜PIComEq⌝][Fst_PIComEq_thm]);
a (bc_tac [list_∀_elim [⌜Csyntax⌝, ⌜Snd PIComEq⌝] equiv_class_∈_thm] THEN REPEAT strip_tac);
a (LEMMA_T ⌜(Csyntax, Snd PIComEq) = PIComEq⌝ rewrite_thm_tac
	THEN_LIST [split_pair_rewrite_tac [⌜PIComEq⌝] [], accept_tac Equiv_PIComEq_thm]);
a (rewrite_tac [eq_sym_rule Fst_PIComEq_thm]);
val CSyntax_PIComEq_thm = save_pop_thm "CSyntax_PIComEq_thm";

add_pc_thms "'icomb" [Fst_PIComEq_thm, Equiv_PIComEq_thm];
set_merge_pcs ["misc31", "'icomb"];
=TEX
}%ignore

We now define a set of equivalence classes which will form a new type of combinators.

ⓈHOLCONST
│ ⦏PureInfComb⦎ : 'a GSU SET → BOOL
├───────────
│ ∀x⦁ PureInfComb x ⇔ x ∈ QuotientSet Csyntax (Snd PIComEq)
■ 

=GFT
⦏PureInfComb_∃_lemma⦎ =
   ⊢ ∀ x⦁ x ∈ Csyntax ⇒ EquivClass PIComEq x ∈ PureInfComb
⦏∃_PureInfComb_lemma⦎ =
   ⊢ ∃ x⦁ x ∈ PureInfComb
=TEX

\ignore{
=SML
val PureInfComb_def = get_spec ⌜PureInfComb⌝;

set_goal([], ⌜∀x⦁ x ∈ Csyntax ⇒ PureInfComb(EquivClass PIComEq x)⌝);
a (rewrite_tac [PureInfComb_def, PIComEq_def, get_spec ⌜EquivClass⌝, get_spec ⌜QuotientSet⌝]
	THEN REPEAT strip_tac);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[get_spec ⌜EquivClass⌝, EquivClosure_def] THEN REPEAT strip_tac);
val PureInfComb_∃_lemma = pop_thm ();

set_goal([], ⌜∃x⦁ PureInfComb x⌝);
a (∃_tac ⌜EquivClass PIComEq (MkCcon ∅⋎u)⌝);
a (lemma_tac ⌜MkCcon ∅⋎u ∈ Csyntax⌝ THEN1 rewrite_tac[MkCcon_∈_Csyntax_thm]);
a (all_fc_tac [PureInfComb_∃_lemma]);
val ∃_PureInfComb_lemma = pop_thm ();
=TEX
}%ignore

\subsection{Consistency}

At this point it is desirable to prove something like the Church-Rosser theorem for this system, so that we know that not all combinators are equivalent.
Since this is probably hard I am exploring a bit more before digging in to the proof.

The most doubtful part of the enterprise is not the infinitary combinators.
It is the illative combinator.
So its probably worth working through the handling of the illative combinator in a system with no infinitary combinators, and adding in the infinitary combinators (whose purpose is just to add strength), when the treatment of the illative combinator has been proven in the simpler context.

ⓈHOLCONST
│ ⦏ChurchRosser⦎ : ('a → 'a → BOOL) → BOOL
├───────────
│ ∀r⦁ ChurchRosser r ⇔ ∀w x y⦁ r w x ∧ r w y ⇒ ∃z⦁ r x z ∧ r y z
■ 

=IGN
 ⓈHOLCONST
│ ⦏CrUb⦎ : ('a → 'a → BOOL) → ('a → 'a → 'a)
 ├───────────
│ ∀r⦁ CrUb r = λx y⦁ εz⦁ r x z ∧ r y z
 ■ 

 ⓈHOLCONST
│ ⦏CrRectangle⦎ : ('a → 'a → BOOL) → (ℕ → 'a) × (ℕ → 'a) → (ℕ → ℕ → 'a)
 ├───────────
│ ∀r f g x y⦁
	CrRectangle r (f, g) 0 y  = f y
    ∧	CrRectangle r (f, g) (x+1) 0  = g (x+1)
    ∧	CrRectangle r (f, g) (x+1) (y+1)  = CrUb r (CrRectangle r (f, g) x (y+1)) (CrRectangle r (f, g) (x+1) y)
 ■ 

=IGN
⦏CrUb_thm⦎ = ⊢ ∀ r⦁ ChurchRosser r
	⇒ (∀ x y z⦁ r x y ∧ r x z ⇒ r y (CrUb r y z) ∧ r z (CrUb r y z))
=TEX

I approach the Church-Rosser proofs (loosely) following a method I took from Barendregt \cite{barendregtTLC} (which he attributes to W. Tait and Per Martin-L{\ouml}f).
This consists in proving that the transitive closure of a Church-Rosser relation is Church-Rosser, and then finding a Church-Rosser relation whose transitive closure is the desired relation.

The first theorem is:

=GFT
⦏CrTc_thm⦎ = ⊢ ∀ r⦁ ChurchRosser r ⇒ ChurchRosser (tc r)
=TEX

\ignore{
=SML
val ChurchRosser_def = get_spec ⌜ChurchRosser⌝;
=IGN
val CrUb_def = get_spec ⌜CrUb⌝;
val CrRectangle_def = get_spec ⌜CrRectangle⌝;

set_goal([], ⌜∀r⦁ ChurchRosser r ⇒ ∀x y z⦁ r x y ∧ r x z ⇒ r y (CrUb r y z) ∧ r z (CrUb r y z)⌝);
a (∀_tac THEN rewrite_tac[ChurchRosser_def, CrUb_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (ε_tac ⌜ε z'⦁ r y z' ∧ r z z'⌝);
a (all_asm_fc_tac[]);
a (∃_tac ⌜z''⌝ THEN contr_tac);
(* *** Goal "2" *** *)
a (ε_tac ⌜ε z'⦁ r y z' ∧ r z z'⌝);
a (all_asm_fc_tac[]);
a (∃_tac ⌜z''⌝ THEN contr_tac);
val CrUb_thm = save_pop_thm "CrUb_thm";

=SML
set_goal([], ⌜∀r⦁ ChurchRosser r ⇒ ChurchRosser (tc r)⌝);
a (strip_tac THEN rewrite_tac[ChurchRosser_def] THEN REPEAT strip_tac);
(* a (cases_tac ⌜r w x⌝ THEN cases_tac ⌜r w y⌝); *)
a (all_fc_tac [tc_decomp_thm3]);
a (lemma_tac ⌜∃ub⦁ ∀x y⦁ (∃w⦁ r w x ∧ r w y) ⇒ r x (ub x y) ∧ r y (ub x y)
	∧ ub y x = ub x y⌝);
(* *** Goal "1" *** *)
a (∃_tac ⌜λv w:'a⦁ εu:'a⦁ r v u ∧ r w u⌝ THEN rewrite_tac[]);
a (REPEAT ∀_tac THEN strip_tac);
a (ε_tac ⌜ε u⦁ r x' u ∧ r y' u⌝);
(* *** Goal "1.1" *** *)
a (all_asm_fc_tac[]);
a (∃_tac ⌜z'⌝ THEN contr_tac);
(* *** Goal "1.2" *** *)
a (all_asm_fc_tac[] THEN asm_rewrite_tac[]);
a (rewrite_tac [prove_rule [] ⌜∀u⦁ r y' u ∧ r x' u ⇔ r x' u ∧ r y' u⌝ ]);
(* *** Goal "2" *** *)
(* to get round an error in the first version with minimal impact
   I now change the usage of n and n' *)
a (rename_tac [(⌜n⌝, "no"), (⌜n'⌝, "no'")]);
a (lemma_tac ⌜∃n n'⦁ n = no+1 ∧ n' = no'+1⌝ THEN1 prove_∃_tac);
a (lemma_tac ⌜∃crr⦁ ∀x y⦁
	crr 0 y  = f' y
    ∧	crr (x+1) 0  = f (x+1)
    ∧	crr (x+1) (y+1)  = ub (crr x (y+1)) (crr (x+1) y)⌝ THEN prove_∃_tac);
a (lemma_tac ⌜∀xpy⦁ xpy + 1 < n + n' ⇒ ∀x y⦁ x < n ∧ y < n' ∧ x + y = xpy
	⇒ r (crr x (y + 1)) (crr (x + 1) (y + 1))
		∧ r (crr (x + 1) y) (crr (x + 1) (y + 1))⌝
	THEN1 ∀_tac);
(* *** Goal "2.1" *** *)
a (induction_tac ⌜xpy⌝);
(* *** Goal "2.1.1" *** *)
a (rewrite_tac[] THEN (REPEAT_N 4 strip_tac) THEN asm_rewrite_tac[]);
a (LEMMA_T ⌜crr(0+1) 0 = f 1⌝ (rewrite_thm_tac o (rewrite_rule[]))
	THEN1 asm_rewrite_tac[]);
a (lemma_tac ⌜r w (f 1) ∧ r w (f' 1)⌝ THEN strip_tac);
(* *** Goal "2.1.1.1" *** *)
a (rewrite_tac[asm_rule ⌜w = f 0⌝]);
a (spec_nth_asm_tac 13 ⌜0⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac[]);
(* *** Goal "2.1.1.2" *** *)
a (rewrite_tac[asm_rule ⌜w = f' 0⌝]);
a (spec_nth_asm_tac 10 ⌜0⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac[]);
(* *** Goal "2.1.1.3" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "2.1.1.4" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "2.1.2" *** *)
a (REPEAT_N 4 strip_tac);
a (lemma_tac ⌜xpy + 1 < n + n'⌝
	THEN1 (PC_T1 "lin_arith" prove_tac [asm_rule ⌜(xpy + 1) + 1 < n + n'⌝]));
(* *** Goal "2.1.3" *** *)
a (REPEAT_N 4 strip_tac);
a (cond_cases_tac ⌜x'=0 ∨ y'=0⌝);
(* *** Goal "2.1.3.1" *** *)
a (var_elim_asm_tac ⌜x' = 0⌝);
a (POP_ASM_T (asm_tac o (rewrite_rule[])));
a (lemma_tac ⌜xpy <n'⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a (LEMMA_T ⌜0 + xpy = xpy⌝ asm_tac THEN1 rewrite_tac[]);
a (list_spec_nth_asm_tac 7 [⌜0⌝, ⌜xpy⌝]);
a (lemma_tac ⌜xpy + 1 ≤ no'⌝ THEN1 PC_T1 "lin_arith" prove_tac[
	asm_rule ⌜y' = xpy + 1⌝,
	asm_rule ⌜y' < n'⌝,
	asm_rule ⌜n' = no' + 1⌝]);
a (spec_nth_asm_tac 15 ⌜xpy+1⌝);
a (POP_ASM_T ante_tac);
a (LEMMA_T ⌜f' (xpy + 1) = crr 0 (xpy + 1)⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a (LEMMA_T ⌜f' ((xpy + 1) + 1) = crr 0 (y' +1)⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a (strip_tac);
a (list_spec_nth_asm_tac 15 [⌜crr (0 + 1) (xpy + 1)⌝, ⌜crr 0 (y' + 1)⌝]);
(* *** Goal "2.1.3.1.1" *** *)
a (spec_nth_asm_tac 1 ⌜crr 0 (xpy + 1)⌝);
(* *** Goal "2.1.3.1.2" *** *)
a (lemma_tac ⌜crr 1 (y' + 1) = ub (crr (0 + 1) (xpy + 1)) (crr 0 (y' + 1))⌝);
(* *** Goal "2.1.3.1.2.1" *** *)
a (GET_NTH_ASM_T 1 (rewrite_thm_tac o eq_sym_rule));
a (once_rewrite_tac[prove_rule [] ⌜crr 1 (y' + 1)= crr(0+1)(y' + 1)⌝]);
a (pure_asm_rewrite_tac[]);
a (LEMMA_T ⌜crr 1 (xpy + 1) = ub (f' (xpy + 1)) (crr (0 + 1) xpy)⌝ rewrite_thm_tac);
a (pure_rewrite_tac [prove_rule [] ⌜crr 1 = crr (0+1)⌝]);
a (pure_asm_rewrite_tac[]);
a (strip_tac);
(* *** Goal "2.1.3.1.2.2" *** *)
a (GET_NTH_ASM_T 1 rewrite_thm_tac);
a (GET_NTH_ASM_T 3 (rewrite_thm_tac o (rewrite_rule[])));
a (DROP_NTH_ASM_T 4 ante_tac); 
a (rewrite_tac[asm_rule ⌜y' = xpy + 1⌝]);
(* *** Goal "2.1.3.2" *** *)
a (var_elim_asm_tac ⌜y' = 0⌝);
a (POP_ASM_T (asm_tac o (rewrite_rule[])));
a (lemma_tac ⌜xpy < n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a (LEMMA_T ⌜xpy + 0 = xpy⌝ asm_tac THEN1 rewrite_tac[]);
a (list_spec_nth_asm_tac 7 [⌜xpy⌝, ⌜0⌝]);
a (lemma_tac ⌜xpy +1 ≤ no ⌝ THEN1 PC_T1 "lin_arith" prove_tac[
	asm_rule ⌜x' = xpy + 1⌝,
	asm_rule ⌜x' < n⌝,
	asm_rule ⌜n = no + 1⌝]);
a (spec_nth_asm_tac 18 ⌜xpy+1⌝);
a (POP_ASM_T ante_tac);
a (LEMMA_T ⌜f (xpy + 1) = crr (xpy + 1) 0⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a (LEMMA_T ⌜f ((xpy + 1) + 1) = crr (x' + 1) 0⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a (strip_tac);
a (list_spec_nth_asm_tac 15 [⌜crr (xpy + 1) (0 + 1)⌝, ⌜crr (x' + 1) 0⌝]);
(* *** Goal "2.1.3.2.1" *** *)
a (spec_nth_asm_tac 1 ⌜crr (xpy + 1) 0⌝);
(* *** Goal "2.1.3.2.2" *** *)
a (lemma_tac ⌜crr (x' + 1) 1 = ub (crr (xpy + 1) (0 + 1)) (crr (x' + 1) 0)⌝);
(* *** Goal "2.1.3.2.2.1" *** *)
a (once_rewrite_tac[prove_rule [] ⌜crr (x' + 1) 1 = crr (x' + 1) (0+1)⌝]);
a (GET_NTH_ASM_T 15 (fn crrdef =>
	rewrite_tac [rewrite_conv [crrdef] ⌜crr (x' + 1) (0 + 1)⌝]));
a (pure_asm_rewrite_tac[]);
a (strip_tac);
(* *** Goal "2.1.3.2.2.2" *** *)
a (GET_NTH_ASM_T 1 rewrite_thm_tac);
a (GET_NTH_ASM_T 3 (rewrite_thm_tac o (rewrite_rule[])));
a (DROP_NTH_ASM_T 4 ante_tac); 
a (rewrite_tac[asm_rule ⌜x' = xpy + 1⌝]);
(* *** Goal "2.1.3.3" *** *)
a (strip_asm_tac (∀_elim ⌜x'⌝ ℕ_cases_thm));
a (strip_asm_tac (∀_elim ⌜y'⌝ ℕ_cases_thm));
a (lemma_tac ⌜i < n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]); 
a (lemma_tac ⌜i' < n'⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]); 
a (lemma_tac ⌜i + y' = xpy⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]); 
a (lemma_tac ⌜x' + i' = xpy⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]); 
a (list_spec_nth_asm_tac 13 [⌜i⌝, ⌜y'⌝]);
a (list_spec_nth_asm_tac 15 [⌜x'⌝, ⌜i'⌝]);
a (DROP_NTH_ASM_T 4 discard_tac THEN DROP_NTH_ASM_T 1 discard_tac);
a (REPEAT_N 2 (POP_ASM_T ante_tac));
a (rewrite_tac[eq_sym_rule (asm_rule ⌜x' = i + 1⌝),
		eq_sym_rule (asm_rule ⌜y' = i' + 1⌝)]);
a (REPEAT_N 2 strip_tac);
a (list_spec_nth_asm_tac 19 [⌜crr x' (y'+1)⌝, ⌜crr (x'+1) y'⌝]);
(* *** Goal "2.1.3.3.1" *** *)
a (spec_nth_asm_tac 1 ⌜crr x' y'⌝);
(* *** Goal "2.1.3.3.2" *** *)
a (LEMMA_T ⌜crr (x' + 1) (y' + 1) = ub (crr x' (y' + 1)) (crr (x' + 1) y')⌝ (fn x => rewrite_thm_tac x THEN LIST_GET_NTH_ASM_T [2,3] rewrite_tac));
a (GET_NTH_ASM_T 19 rewrite_thm_tac);
(* a (asm_rewrite_tac[]); *)
(* *** Goal "2.2" *** *)
a (lemma_tac ⌜∀xpy⦁ xpy + 1 < n + n' ⇒ ∀x y⦁ x < n ∧ y < n' ∧ x + y ≤ xpy ⇒
	 tc r (f' (y+1)) (crr (x + 1) (y + 1)) ∧ tc r (f (x + 1)) (crr (x + 1) (y + 1))⌝);
(* *** Goal "2.2.1" *** *)
a (strip_tac);
a (induction_tac ⌜xpy⌝);
(* *** Goal "2.2.1.1" *** base case *)
a (rewrite_tac[] THEN (REPEAT_N 4 strip_tac) THEN asm_rewrite_tac[]);
a (LEMMA_T ⌜crr(0+1) 0 = f 1⌝ (rewrite_thm_tac o (rewrite_rule[]))
	THEN1 asm_rewrite_tac[]);
a (lemma_tac ⌜r (f 0) (f 1) ∧ r (f 0) (f' 1)⌝);
(* *** Goal "2.2.1.1.1" *** *)
a (LEMMA_T ⌜r (f 0) (f' 1) ⇔ r (f' 0) (f' 1)⌝ rewrite_thm_tac
	THEN1 (SYM_ASMS_T rewrite_tac));
a (LEMMA_T ⌜0 ≤ no⌝ asm_tac THEN1 (PC_T1 "lin_arith" asm_prove_tac[]));
a (LEMMA_T ⌜0 ≤ no'⌝ asm_tac THEN1 (PC_T1 "lin_arith" asm_prove_tac[]));
a (ALL_ASM_FC_T (MAP_EVERY (asm_tac o (rewrite_rule[]))) []);
a (contr_tac);
(* *** Goal "2.2.1.1.2" *** *)
a (list_spec_nth_asm_tac 12 [⌜f' 1⌝, ⌜f 1⌝]);
(* *** Goal "2.2.1.1.2.1" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "2.2.1.1.2.2" *** *)
a (all_fc_tac[tc_incr_thm] THEN contr_tac);
(* *** Goal "2.2.1.2" *** step case condition *)
a (REPEAT_N 4 strip_tac);
a (strip_asm_tac (pc_rule1 "lin_arith" prove_rule[]
	⌜(xpy + 1) + 1 < n + n' ⇒ xpy + 1 < n + n'⌝));
(* *** Goal "2.2.1.3" *** step_case proper *)
a (REPEAT_N 4 strip_tac);
a (cond_cases_tac ⌜x' + y' < xpy + 1⌝);
(* *** Goal "2.2.1.3.1" *** *)
a (lemma_tac ⌜x' + y' ≤ xpy⌝
	THEN1 PC_T1 "lin_arith" prove_tac [asm_rule ⌜x' + y' < xpy + 1⌝]);
a (list_spec_nth_asm_tac 7 [⌜x'⌝, ⌜y'⌝] THEN contr_tac);
(* *** Goal "2.2.1.3.2" *** *)
a (lemma_tac ⌜x' + y' = xpy + 1⌝ THEN1 PC_T1 "lin_arith" prove_tac 
		[asm_rule ⌜¬ x' + y' < xpy + 1⌝,
		asm_rule ⌜x' + y' ≤ xpy + 1⌝]);
a (cond_cases_tac ⌜x'=0 ∨ y'=0⌝);
(* *** Goal "2.2.1.3.2.1" *** *)
a (lemma_tac ⌜¬ y' = 0⌝ THEN1 PC_T1 "lin_arith" prove_tac 
		[asm_rule ⌜x' + y' = xpy + 1⌝,
		asm_rule ⌜x' = 0⌝]);
a (strip_asm_tac (∀_elim ⌜y'⌝ ℕ_cases_thm));
a (lemma_tac ⌜i < n'⌝ THEN1 PC_T1 "lin_arith" prove_tac
	[asm_rule ⌜y' < n'⌝, asm_rule ⌜y' = i+1⌝]);
a (lemma_tac ⌜x'+i ≤ xpy⌝ THEN1 PC_T1 "lin_arith" prove_tac
	[asm_rule ⌜x' + y' ≤ xpy + 1⌝, asm_rule ⌜y' = i+1⌝]);
a (list_spec_nth_asm_tac 12 [⌜x'⌝, ⌜i⌝]);
a (lemma_tac ⌜(x'+y')+1 < n+n'⌝ THEN1 PC_T1 "lin_arith" prove_tac
	[asm_rule ⌜x' < n⌝, asm_rule ⌜y' < n'⌝]);
a (spec_nth_asm_tac 16 ⌜x'+y'⌝);
a (list_spec_nth_asm_tac 1 [⌜x'⌝, ⌜y'⌝]);
a (strip_asm_tac(
	list_∀_elim [⌜r⌝, ⌜crr x' (y' + 1)⌝, ⌜crr (x' + 1) (y' + 1)⌝]
	tc_incr_thm));
a (strip_asm_tac(
	list_∀_elim [⌜r⌝, ⌜crr (x' + 1) y'⌝, ⌜crr (x' + 1) (y' + 1)⌝]
	tc_incr_thm));
a (DROP_NTH_ASM_T 7 ante_tac);
a (DROP_NTH_ASM_T 7 ante_tac);
a (REPEAT_N 2 (POP_ASM_T ante_tac));
a (GET_ASM_T ⌜y' = i + 1⌝ (rewrite_thm_tac o eq_sym_rule));
a (REPEAT ⇒_tac);
a (all_fc_tac[tran_tc_thm2]);
a (REPEAT strip_tac);
a (var_elim_asm_tac ⌜x' = 0⌝);
a (DROP_NTH_ASM_T 6 ante_tac);
a (asm_rewrite_tac[]);
(* *** Goal "2.2.1.3.2.2" *** *)
a (lemma_tac ⌜¬ x' = 0⌝ THEN1 PC_T1 "lin_arith" prove_tac 
		[asm_rule ⌜x' + y' = xpy + 1⌝,
		asm_rule ⌜y' = 0⌝]);
a (strip_asm_tac (∀_elim ⌜x'⌝ ℕ_cases_thm));
a (lemma_tac ⌜i < n⌝ THEN1 PC_T1 "lin_arith" prove_tac
	[asm_rule ⌜x' < n⌝, asm_rule ⌜x' = i+1⌝]);
a (lemma_tac ⌜i + y' ≤ xpy⌝ THEN1 PC_T1 "lin_arith" prove_tac
	[asm_rule ⌜x' + y' ≤ xpy + 1⌝, asm_rule ⌜x' = i+1⌝]);
a (list_spec_nth_asm_tac 12 [⌜i⌝, ⌜y'⌝]);
a (lemma_tac ⌜(x'+y')+1 < n+n'⌝ THEN1 PC_T1 "lin_arith" prove_tac
	[asm_rule ⌜x' < n⌝, asm_rule ⌜y' < n'⌝]);
a (spec_nth_asm_tac 16 ⌜x'+y'⌝);
a (list_spec_nth_asm_tac 1 [⌜x'⌝, ⌜y'⌝]);
a (strip_asm_tac(
	list_∀_elim [⌜r⌝, ⌜crr x' (y' + 1)⌝, ⌜crr (x' + 1) (y' + 1)⌝]
	tc_incr_thm));
a (strip_asm_tac(
	list_∀_elim [⌜r⌝, ⌜crr (x' + 1) y'⌝, ⌜crr (x' + 1) (y' + 1)⌝]
	tc_incr_thm));
a (DROP_NTH_ASM_T 7 ante_tac);
a (DROP_NTH_ASM_T 7 ante_tac);
a (REPEAT_N 2 (POP_ASM_T ante_tac));
a (GET_ASM_T ⌜x' = i + 1⌝ (rewrite_thm_tac o eq_sym_rule));
a (REPEAT ⇒_tac);
a (all_fc_tac[tran_tc_thm2]);
a (REPEAT strip_tac);
a (var_elim_asm_tac ⌜y' = 0⌝);
a (DROP_NTH_ASM_T 5 ante_tac);
a (asm_rewrite_tac[]);
(* *** Goal "2.2.1.3.2.3" *** *)
a (strip_asm_tac (∀_elim ⌜x'⌝ ℕ_cases_thm));
a (strip_asm_tac (∀_elim ⌜y'⌝ ℕ_cases_thm));
a (lemma_tac ⌜i < n⌝ THEN1 PC_T1 "lin_arith" prove_tac
	[asm_rule ⌜x' < n⌝, asm_rule ⌜x' = i+1⌝]);
a (lemma_tac ⌜i' < n'⌝ THEN1 PC_T1 "lin_arith" prove_tac
	[asm_rule ⌜y' < n'⌝, asm_rule ⌜y' = i'+1⌝]);
a (lemma_tac ⌜i + y' ≤ xpy⌝ THEN1 PC_T1 "lin_arith" prove_tac
	[asm_rule ⌜x' + y' ≤ xpy + 1⌝, asm_rule ⌜x' = i+1⌝]);
a (lemma_tac ⌜x' + i' ≤ xpy⌝ THEN1 PC_T1 "lin_arith" prove_tac
	[asm_rule ⌜x' + y' ≤ xpy + 1⌝, asm_rule ⌜y' = i'+1⌝]);
a (list_spec_nth_asm_tac 15 [⌜i⌝, ⌜y'⌝]);
a (list_spec_nth_asm_tac 17 [⌜x'⌝, ⌜i'⌝]);
a (lemma_tac ⌜(x'+y')+1 < n+n'⌝ THEN1 PC_T1 "lin_arith" prove_tac
	[asm_rule ⌜x' < n⌝, asm_rule ⌜y' < n'⌝]);
a (spec_nth_asm_tac 21 ⌜x'+y'⌝);
a (list_spec_nth_asm_tac 1 [⌜x'⌝, ⌜y'⌝]);
a (strip_asm_tac(
	list_∀_elim [⌜r⌝, ⌜crr x' (y' + 1)⌝, ⌜crr (x' + 1) (y' + 1)⌝]
	tc_incr_thm));
a (strip_asm_tac(
	list_∀_elim [⌜r⌝, ⌜crr (x' + 1) y'⌝, ⌜crr (x' + 1) (y' + 1)⌝]
	tc_incr_thm));
a (REPEAT_N 4 (DROP_NTH_ASM_T 7 ante_tac));
a (REPEAT_N 2 (POP_ASM_T ante_tac));
a (GET_ASM_T ⌜x' = i + 1⌝ (rewrite_thm_tac o eq_sym_rule));
a (GET_ASM_T ⌜y' = i' + 1⌝ (rewrite_thm_tac o eq_sym_rule));
a (REPEAT ⇒_tac);
a (all_fc_tac[tran_tc_thm2]);
a (REPEAT strip_tac);
(* *** Goal "2.2.2" *** *)
a (∃_tac ⌜crr n n'⌝);
a (lemma_tac ⌜(no + no') + 1 < n + n'⌝ THEN1 PC_T1 "lin_arith" prove_tac
	[asm_rule ⌜n = no + 1⌝,
	asm_rule ⌜n' = no' + 1⌝]);
a (spec_nth_asm_tac 2 ⌜no + no'⌝);
a (lemma_tac ⌜no < n⌝ THEN1 PC_T1 "lin_arith" prove_tac
	[asm_rule ⌜n = no + 1⌝]);
a (lemma_tac ⌜no' < n'⌝ THEN1 PC_T1 "lin_arith" prove_tac
	[asm_rule ⌜n' = no' + 1⌝]);
a (list_spec_nth_asm_tac 3 [⌜no⌝, ⌜no'⌝]);
a (REPEAT_N 2 (POP_ASM_T ante_tac));
a (asm_rewrite_tac[]);
a (REPEAT strip_tac);
val CrTc_thm = save_pop_thm "CrTc_thm";
=TEX
}%ignore

Typically a relation of direct reduction (or its reflexive closure) will not be Church-Rosser.
This is because a reduction of a redex may replicate some other redex (contained within it).
To reduce that other redex after the first reduction will require more than one reduction.
To get a Church-Rosser relation we need to allow all these `residuals' to be reduced in one step.

I therefore define an operator which takes a relation of direct reduction and makes from it a parallel reduction relation which is more likely to be Church-Rosser.
The idea is that any set of redexes in the term can be reduced in a single step, but that no redex which was not in that original term can be reduced in that step.

There are (at least!) two ways of defining this relationship.

The first (which is the kind of approach used in Barendregt) is to define it as undertaking a single depth-first scan of the term reducing any of the redexes.

The second is to devise a representation of a set of redexes and to define the reduction parameterised by such a set of redexes.
The desired relation is then obtained by existentially quantifying over sets of redexes.

I started out with the second approach, but this was rapidly getting too complicated, so I am trying out the first approach.

They are presented here (so far as they go) in reverse order.

With either of these approaches it is possible to identify a maximal direct reduction of any term.
One can argue that the relation is Church-Rosser because whatever reduction is undertaken on a term it can be converted by just one more reduction to the maximal reduct of the original term.
Thus for each term, there is some other term (its maximal reduct), which could serve as the bottom of the diamond whatever two other reducts were considered.
One might hope that this observation would permit a simplification of the Church-Rosser proof, but so far I have not found a way to realise that simplification.

I shall keep my eye on this as I work through the preliminary stages of the proof.

In the following section I make some steps towards a proof based on coordinates, in the subsequent section I mentally put this aside and try an approach more closely following one presented by Barendregt.

\subsubsection{Approach based on Coordinates}

Redexes (or subterms in general) in a combinatorial term can be identified by coordinates, finite sequences of (not necessarily finite) ordinals suffice.
We do need to insist that the coordinates are coordinates of redexes.

I define first the operation of extracting from a combinator the substructure identified by a set of coordinates.
I use the type LIST for finite sequences.
When it comes to selecting a subterm, a term is an ordered pair of which the second element is a sequence of terms (the first is a constant name).
The sequence is a function whose domain is an ordinal, so we just apply this sequence to the relevant coordinate (which is here the head \emph{h} of the list of coordinates).

ⓈHOLCONST
│ ⦏SubTerm⦎ : 'a GSU LIST → 'a GSU → 'a GSU
├───────────
│ ∀h t tl⦁	SubTerm [] t = t
│ 	∧	SubTerm (Cons h tl) t = SubTerm tl ((Snd⋎u t) ⋎u h)
■ 

Since this function is total (and therefore will yield junk if there is no subterm addressed by the coordinates) I also need a test so I know whether a coordinate list does actually point to a subterm.
This test assumes that its second argument is a combinatory term, and tests whether the coordinate list points to a subterm.

ⓈHOLCONST
│ ⦏is_SubTerm⦎ : 'a GSU LIST → 'a GSU → BOOL
├───────────
│ ∀h t tl⦁	(is_SubTerm [] t ⇔ T)
│ 	∧	(is_SubTerm (Cons h tl) t ⇔
│			h ∈⋎u Dom⋎u (Snd⋎u t) ∧ is_SubTerm tl ((Snd⋎u t) ⋎u h))
■ 

=GFT
⦏SubTerm_in_Csyntax_lemma⦎ =
   ⊢ ∀ t⦁ t ∈ Csyntax ⇒ (∀ cs⦁ is_SubTerm cs t ⇒ SubTerm cs t ∈ Csyntax)
=TEX

\ignore{
=SML
val SubTerm_def = get_spec ⌜SubTerm⌝;
val is_SubTerm_def = get_spec ⌜is_SubTerm⌝;

set_goal([], ⌜∀t⦁ t ∈ Csyntax ⇒ ∀cs⦁ is_SubTerm cs t
		⇒ (SubTerm cs t) ∈ Csyntax⌝);
a (∀_tac THEN strip_tac);
a (icomb_induction_tac ⌜t⌝);
a (∀_tac);
a (strip_asm_tac (∀_elim ⌜cs⌝ list_cases_thm)
	THEN_TRY asm_rewrite_tac[is_SubTerm_def, SubTerm_def]);
(* *** Goal "1" *** *)
a (lemma_tac ⌜∀ x⦁ x ∈ X⋎u (Ran⋎u i) ⇒ x ∈ Csyntax⌝
	THEN1 (rewrite_tac [X⋎u_def] THEN REPEAT strip_tac THEN all_asm_fc_tac[]));
a (fc_tac [crepclosed_csyntax_thm]);
a (all_asm_fc_tac[]);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (REPEAT strip_tac);
a (all_fc_tac [app_in_Ran_thm]);
a (all_asm_fc_tac[]);
val SubTerm_in_Csyntax_lemma = save_pop_thm "SubTerm_in_Csyntax_lemma";
=TEX
}%ignore

This isn't quite a sufficient check.
It is important that nothing is accepted as a redex unless it really is one, particularly not if it might be turned into one by some other reduction (this is because we don't want the description of the reductions required to give different results after some other reduction than before), so the best thing is to use the direct reduction relation to test whether the identified subterms are redexes, i.e. we just check whether the subterm is in the domain of the relationship.

The parameters here are:
\begin{itemize}
\item[r] the direct reduction relation
\item[t] the combinatory term
\item[cls] a set of coordinate lists
\end{itemize}
and the value is true if all the identified subterms are in the domain of the reduction relation.

ⓈHOLCONST
│ ⦏is_redex_set⦎ : 'a RED → 'a GSU → ('a GSU LIST)SET → BOOL
├───────────
│ ∀(r:'a RED) t cls⦁ is_redex_set r t cls ⇔
│	∀cs⦁ cs ∈ cls ⇒ is_SubTerm cs t ∧ (∃y⦁ r (SubTerm cs t) y)
■ 

We now need to define the effects of applying some such set of reductions.
There are two effects of interest.
The first of course is the resulting term.

The second is a residual map, which tells us how to find the instances in the new term of the subterms of the old term.
To compute the residual map we assume that a residual map is available for the direct reduction relation, and use that in computing the residual map function for the derived parallel reduction relation.

The best way to compute the new term is with a depth first traversal.
This ensures that redexes for reduction are are not replicated until they have been reduced.

The definition is inductive over the structure of the combinatory terms.
At each stage in the recursion the set of coordinate sequences is filtered by selecting only those which point within the selected subterm and chopping the head of those sequences.
The reduction of the term takes place after the reduction of its subterms.
We assume that the second parameter is a syntactically valid combinatory term and that the set of coordinate sequences passes the $is\_redex\_set$ test.

The following function restricts a set of coordinates to the relative coordinates of subterms of a give top-level sub-term, identified by its coordinate.

ⓈHOLCONST
│ ⦏cls_restrict⦎ : ('a GSU LIST)SET → 'a GSU → ('a GSU LIST)SET
├───────────
│ ∀cls (t:'a GSU)⦁ cls_restrict cls t = {v: 'a GSU LIST | Cons t v ∈ cls}
■

We need direct reduction to be deterministic, i.e. to be a many-one relation.
Assuming that it is we can use the following function to perform a reduction.

ⓈHOLCONST
│ ⦏reduce⦎ : 'a RED → 'a GSU → 'a GSU
├───────────
│ ∀(r:'a RED) (t:'a GSU)⦁ reduce r t =
│	εnt⦁ r t nt ∨ ((¬ ∃nt2⦁ r t nt2) ∧ nt = t) 
■ 

We want to map certain operations over terms to be applied at certain locations specified by coordinates.
Some general combinators might be the best way to achieve this.

We need to obtain from a parallel reduction not only the resulting term but also a map which tells us the location of any residuals.
The function to be mapped over the term must therefore not simply be a function over combinators, but a function which transforms a combinator and delivers a residual map (which is a kind of map over coordinate lists).

The type of such a function is therefore:

=SML
declare_type_abbrev ("CT", ["'a"], ⓣ'a GSU → ('a GSU × ('a GSU LIST → 'a GSU LIST))⌝);
=TEX

We could build into the mapping function the means of composing the resulting coordinate transformers obtained in the traversal, but it is better to supply that as a parameter.
The type of such a parameter would be:

=SML
declare_type_abbrev ("CC", ["'a"], ⓣ('a GSU × ('a GSU LIST → 'a GSU LIST)) LIST
			→ 'a GSU LIST × ('a GSU LIST → 'a GSU LIST)⌝);
=TEX

ⓈHOLCONST
│ ⦏depth_map_aux⦎ : ('a GSU → 'a GSU) → 'a GSU → ('a GSU LIST) SET → 'a GSU
├───────────
│ ∀f c ts⦁ depth_map_aux f (c ↦⋎u ts) = λcls⦁ 
│	let newts =
│	Imagep⋎u (λop⦁ Fst⋎u op ↦⋎u (ts ◁⋎u⋎e depth_map_aux f)
│		   (Snd⋎u op) (cls_restrict cls (Fst⋎u op))) ts
│	in if [] ∈ cls then f (c ↦⋎u newts) else c ↦⋎u newts
■ 

=IGN
 ⓈHOLCONST
│ ⦏depth_map_aux2⦎ : ('a CT × 'a CC) → 'a GSU → ('a GSU LIST) SET
│			→ 'a GSU × ('a GSU LIST → 'a GSU LIST)
 ├───────────
│ ∀ct cc c ts⦁ depth_map_aux2 (ct, cc) (c ↦⋎u ts) = λcls⦁ 
│	let newts =
│	Imagep⋎u (λop⦁ Fst⋎u op ↦⋎u (ts ◁⋎u⋎e depth_map_aux2 (ct, cc))
│		   (Snd⋎u op) (cls_restrict cls (Fst⋎u op))) ts
│	in (if [] ∈ cls then ct (c ↦⋎u (Map Fst newts)) else c ↦⋎u (Map Fst newts),
│		cc (Map Snd newts))
 ■ 
=TEX

ⓈHOLCONST
│ ⦏depth_map⦎ : ('a GSU → 'a GSU) → ('a GSU LIST)SET → 'a GSU → 'a GSU
├───────────
│ ∀f cls t⦁ depth_map f cls t = depth_map_aux f t cls
■ 

This function defines the term which results from a parallel reduction.

ⓈHOLCONST
│ ⦏par_reduce⦎ : 'a RED → ('a GSU LIST)SET → 'a GSU → 'a GSU
├───────────
│ ∀r c ts cls⦁ par_reduce r cls (c ↦⋎u ts) =
│	depth_map (reduce r) cls (c ↦⋎u ts)
■ 

We need to be able to compute residual maps which show where to find the residuals of each redex after a (parallel) reduction.
It is probably easier just to map the movement of all combinations irrespective of whether they are redexes.
I think functions from coordinate sets to coordinate sets will probably do the trick.
We suppose that the direct reductions are specified both as a relation and as a residual map.
We can then compute a residual map for a parallel reduction by composing these maps in a manner which corresponds to the depth first traversal which defines the parallel reduction derived from some direct reducibility relation.




We then prove for each direct reduction a commutativity result, which says that performing some reduction before that direct reduction is equivalent to applying that reduction to each of the residuals after the direct reduction.
Next I prove that combining direct reductions preserves this property, and finally that lifting to parallel reduction gives a similar commutativity for the resulting parallel reduction.

From this to the diamond property should be straightforward, which then applies to the transitive closure which is close to the desired reduction relation.
This approach gives Church-Rosser for all by the equivalence combinator.

I then define a functor which takes a value for a direct equivalence reduction
satisfying the relevant commutativity property, and yields a Church-Rosser reduction relation incorporating the other combinators, and a new notion of equivalence hopefully also commutative.
The functor will be monotone, and its least fixed point will be the final reduction relation, which will be a limit of Church-Rosser relations.
So then I need to prove that the functor some relevant continuity property so that its least fixed point is also Church-Rosser.

\subsubsection{More closely following Barendregt}

The previous approach looks too complex.
Eventually I returned to Barendregt for better ideas.
My main reason for not following him more closely had been that he works with systems which contain variables, whereas I am working with a system which lacks variables.
However, it now occurs to me that I can do with ``inert'' combinators the kinds of thing which are normally done with free variables, and so it is plausible that following Barendregt more closely will be possible.
The signficance of this is that variables provide a simple way to track residuals, and the main complexity arising from my previous proof ideas arose from tracking residuals so that a deferred reduction can be completed at all the instances.


Barendregt leaves the Church-Rosser proof for combinatory logic as an exercise (exercise 7.13), so it ought to be manageable, even perhaps with the added complications here.
Before noting the complications I consider the clues available in Barendregt on how to do the exercise.

There is an earlier proof that beta reduction in the lambda-calculus is Church-Rosser in Chapter 3 (Theorem 3.2.8), which can be simplified to give the proof for combinatory logic.
The approach is to define a restricted notion of beta reduction whose transitive closure is CR and to prove that this more restrictive notion is CR.
The particular reduction used for the lambda calculus cannot be used for combinatory logic, but Barendregt suggests instead the reduction which allows parallel reduction of any disjoint set of redexes.

The plan here is to do a version of that adapted to our infinitary combinators, and follow through in the spirit of the proof for beta reduction in Chapter 3.

In addition to allowing for infinitary combinators, we have to parameterise the proof to work with any notion of direct reduction which satisfies certain conditions, so that we can then apply it to systems involving illatory combinators.
Exactly what these conditions should be is not yet clear, but I propose to start by trying something analogous to Barendregt's Lemma 3.2.4 which may be paraphrase as ``reduction commutes with substitution''.

So we start with the definition of disjoint parallel reduction, which is given as an operator over relations.

ⓈHOLCONST
│ ⦏disj_par_reduce⦎ : 'a RED → 'a RED
├───────────
│ ∀r c ts nt⦁ disj_par_reduce r (c ↦⋎u ts) nt ⇔
│		r (c ↦⋎u ts) nt
│	∨	∃ts'⦁ (∀i v⦁ i ↦⋎u v ∈⋎u ts
│			 ⇔ ∃v'⦁ i ↦⋎u v' ∈⋎u ts'
│			    ∧ ((ts ◁⋎u⋎e (disj_par_reduce r)) v v' ∨ v' = v))
│		      ∧ (∃i v v'⦁ i ↦⋎u v ∈⋎u ts ∧ i ↦⋎u v' ∈⋎u ts'
│			    ∧ ((ts ◁⋎u⋎e (disj_par_reduce r)) v v'))
│		      ∧ nt = (c ↦⋎u ts')
■ 

The first result I need to prove is that disjoint parallel reduction commutes with substitution, provided that direct reduction does.
So I need to define substitution.
We have no variables so the substitution in question is substitution for a combinator, which with these infinitary combinators is not quite as straightforward as with the traditional combinators, it invoves concatenating the list of arguments in the two expressions involved.

In the intended applications substitution is for inert combinators only, but we do not need to take that into consideration in the definition of substitution.
In the following:-

\begin{itemize}
\item the first argument is the name of the combinator for which the substitution is being made (not actually a combinatory term, just the name)
\item the second is the combinatory term which is being substituted for that combinator, and
\item the third is the combinatory term into which substitution takes place.
\end{itemize}

ⓈHOLCONST
│ ⦏subs⦎ : 'a GSU → 'a GSU → 'a GSU → 'a GSU
├───────────
│ ∀ cn c ts s⦁ subs cn s (c ↦⋎u ts) =
│	if c = cn
│	then (Fst⋎u s ↦⋎u ((Snd⋎u s) @⋎u (RanMap⋎u (ts ◁⋎u⋎e (subs cn s)) ts)))
│	else (c ↦⋎u (RanMap⋎u (ts ◁⋎u⋎e (subs cn s)) ts))
■ 


=GFT
⦏r_disj_par_thm⦎ = ⊢ ∀ r x y⦁ x ∈ Csyntax ∧ r x y ⇒ disj_par_reduce r x y
=TEX

\ignore{
=SML
val disj_par_reduce_def = get_spec ⌜disj_par_reduce⌝;
val subs_def = get_spec ⌜subs⌝;

set_goal([], ⌜∀r x y⦁ x ∈ Csyntax ∧ r x y ⇒ disj_par_reduce r x y⌝);
a (REPEAT strip_tac);
a (all_fc_tac [csyntax_pair_thm]);
a (var_elim_asm_tac ⌜x = c ↦⋎u ts⌝);
a (asm_rewrite_tac [disj_par_reduce_def]);
val r_disj_par_thm = save_pop_thm "r_disj_par_thm";

=IGN

stop;

set_goal([], ⌜∀cn s t⦁ s ∈ Csyntax ∧ t ∈ Csyntax ⇒ subs cn s t ∈ Csyntax⌝);
a (REPEAT strip_tac);
a (icomb_induction_tac2 ⌜t⌝);
a (rewrite_tac [subs_def]);
a (cond_cases_tac ⌜c = cn⌝);

=TEX
}%ignore


We do now need the notion of an inert combinator, relative to some notion of reduction.
This takes a reduction and returns a property of combinator names which is satisfied only be combinators which are never reduced by the reduction.

ⓈHOLCONST
│ ⦏inert⦎ : 'a RED → 'a GSU → BOOL
├───────────
│ ∀ r c⦁ inert r c ⇔ ¬ ∃ ts c' ts'⦁ r (c ↦⋎u ts) (c' ↦⋎u ts') ∧ ¬ c = c'
■ 

=GFT
⦏inert_disj_par_thm⦎ = ⊢ ∀ r cn⦁ inert (disj_par_reduce r) cn ⇔ inert r cn
=TEX

\ignore{
=SML
val inert_def = get_spec ⌜inert⌝;

set_goal([], ⌜∀r cn⦁ inert (disj_par_reduce r) cn ⇔ inert r cn⌝);
a (rewrite_tac [inert_def, disj_par_reduce_def] THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 2 ⌜ts⌝);
a (spec_nth_asm_tac 1 ⌜c'⌝);
a (spec_nth_asm_tac 1 ⌜ts'⌝);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜ts⌝);
a (spec_nth_asm_tac 1 ⌜c'⌝);
a (spec_nth_asm_tac 1 ⌜ts'⌝);
(* *** Goal "3" *** *)
a (var_elim_asm_tac ⌜c' = cn⌝);
val inert_disj_par_thm = save_pop_thm "inert_disj_par_thm";
=TEX
}%ignore

The property of reductions that they commute with substitution is now definable.

ⓈHOLCONST
│ ⦏comm_subs⦎ : 'a RED → BOOL
├───────────
│ ∀ r⦁ comm_subs r ⇔ ∀cn⦁ inert r cn ⇒
│		∀ s t t2⦁ s ∈ Csyntax ∧ t ∈ Csyntax
│			⇒ r t t2
│			⇒ r (subs cn s t) (subs cn s t2) 
■ 


The following theorem states that substitution commutes with disjoint parallel reduction if it commutes with direct reduction.

\ignore{
=SML
val comm_subs_def = get_spec ⌜comm_subs⌝;

=IGN

stop;

set_goal([], ⌜∀r⦁ comm_subs r ⇒ comm_subs (disj_par_reduce r)⌝);
a (rewrite_tac [disj_par_reduce_def, comm_subs_def]
	THEN REPEAT strip_tac);
a (POP_ASM_T ante_tac THEN icomb_induction_tac2 ⌜t⌝);
a (rewrite_tac [disj_par_reduce_def] THEN strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜inert r cn⌝
	THEN1 (once_rewrite_tac [map_eq_sym_rule inert_disj_par_thm]
		THEN strip_tac)); 
a (lemma_tac ⌜(c ↦⋎u i) ∈ Csyntax⌝
	THEN1 (bc_tac [crepclosed_csyntax_thm3]
		THEN strip_tac
		THEN asm_fc_tac[]));
a (lemma_tac ⌜r (subs cn s (c ↦⋎u i)) (subs cn s t2)⌝
	THEN1 all_asm_fc_tac[]);
a (all_fc_tac [r_disj_par_thm]);

a (lemma_tac ⌜disj_par_reduce r (c ↦⋎u i) t2⌝
	THEN1 (rewrite_tac [disj_par_reduce_def] THEN asm_rewrite_tac[]));
a (all_asm_fc_tac[]);

=TEX
}%ignore

\subsubsection{Proof Strategy}

The strategy is, first prove a \emph{Church/Rosser} theorem for the pure part of the infinitary combinatory logic, i.e. the bit without the equivalence combinator reductions.
Then do the rest, which we won't think about yet (much).

A Church/Rosser theorem was first proved for the $λ$-calculus by Church and Rosser\cite{churchCLC}.
The result we require here should be simpler to produce because we have only a combinatory logic.
However, the adoption of an infinitary system naturally complicates matters, though possibly not greatly.


The following proof strategem is new, so far as I am aware.
The need to completely formalise the proof forces one to be more definite about certain things, which at first glance may seem to impose additional difficulties, but ultimately may assist in finding a nice proof.

The required result is rather like a commutativity result for combinatory reduction, like saying that the order of reduction is not very significant.
To state exactly what that means in this context is not so straightforward as it is to state the commutativity of addition in arithmetic.
The result obtains not because of any peculiarities of the specific reductions under consideration, but simply because they are combinatory, or some such relatively simple characteristic which they share.
It would hold if they were purely combinatory, as S and K are, but we also have combinators which are not quite so pure, the projection combinator and the equivalence combinator.
For these, being `nearly pure combinators' in some sense to be defined, will have to suffice.

The respect in which the map and projection combinators deviate from being purely combinatory is that they are not entirely careless as to their arguments.
A pure combinator, in the sense in which S and K and anything composed from them is a pure combinator, apply irrespective of the values of their arguments, just so long as there are enough of them, and they deliver results in which their arguments are replicated whole (or not replicated at all) without being in any way modified.
The projection combinator is fussy about the value of its first argument, which serves to stipulate an element of its second arguments which is to be extracted.
The map combinator is not fussy about the values of its arguments, but it mangles the first rather than merely replicating it.
The feature which saves these is that they nevertheless `respect reducibility', but unfortunately that is a difficult characteristic to define in this context and so some simpler sufficient condition for their admissibility is desirable.
Perhaps that they are sensitive only to a part of their argumenst which is in normal form, and something else about how the map combinator forms its result.

The relevance to the Church Rosser theorem is that performing reductions on operands will have very limited effects on the permissible reductions of the whole, the same reductions will be possible and the only effect is on the copies of that operand in the resulting structure.

With the projection combinator, an initial segment of the operands must normalise before reduction can take place, and the reduction is sensitive to the value of the selector.
The sensitivity is therefore safe, insofar as the relevant values cannot possibly change if the reduction is deferred.
We could therefore stipulate that a reduction has a pattern (or more than one) which is a combinatory structure in which the only parts which are not variables are normal terms.
However, the notion of normal term depends upon all the reductions so this is not an easy thing to include in the criteria, perhaps it would be better just to allow $T$ and $F$.
That would be OK for the projection combinator, but not for equivalence.

Equivalence does not reduce without inspecting the operands, and does not look for $T$ or $F$, or for normality.
Its saving grace is that if, while reduction is deferred, one of two identical operands is reduced, then it will be possible to reduce the other to make the two operands equal again and effect the reduction of the equality at a later date.

In order to be able to express the precise sense in which these reductions commute, it is necessary to say what a reduction \emph{is}, what it operates \emph{on} and what it \emph{does} in manner which makes it possible to talk about effecting the same reduction either before or after some other transformations.
This means that we have to include sufficient information when undertaking a transformation to know how to apply the same reduction either before or after.
The most important element of this is keeping track of so called `residuals', i.e. keeping track of what happens to redexes of interest when they are moved about by some reduction.

This is achieved using a system of coordinates.
A coordinate determines a place in a combinatory term and a constituent combinator which occurs within the first combinator.
When a reduction takes place, it does so by reduction of an occurrence which may be identified by such a coordinate.
Every constituent of the combinator which is being reduced may then appear in zero, one, or more than one place in the result of the reduction.
The effect of a reduction on the location of the constituent combinators may be recorded as a map from locations (as coordinates) to sets of locations.
If coordinates are relative then this map can be rendered using relative coordinates.

\subsubsection{Representation of Reductions}

The natural choice for our calculus, both for absolute and for relative coordinates, is a sequence of ordinals.
This is such a simple notion that one is immediately tempted to go back and start again using certain maps over sequences of ordinals to represent the combinators.
Without prejudice to whether this should be done, it seems likely to be a good idea to use this representation for combinatory terms in the proof, which will then be straightforward to transfer back to the present representation.

We need representative for the following kinds of entity:

\begin{itemize}
\item Terms and Coordinates
\item Reduction Patterns and applicability
\item Reduction effects or transformations
\end{itemize}

In this calculus, give a suitable notion of coordinate, a combinatory term is determined completely by a map from coordinates to constant names (or possibly variables, for metatheoretic purposes).
A reduction pattern is a combinatory term containing some variables (and subject possibly to other constraints), and its applicability is determined by a simple matching algorithm.
The local effect of a reduction is a new term and a residual map, which maps each argument number in the original pattern to the set of relative coordinates at which it appears in the result of the transformation.
From the local effect of a reduction, we obtain its global affect, which is the application to a subterm of some larger combinatory term, and the conversion of the residual map from local to global coordinates.

The representation I propose is a map from coordinates to combinator names or variables (I'm not sure whether I need the variables yet, but we'll have them in just in case).
A combinator is just a value of type $ⓣ'a GSU⌝$, for the variables ordinals of type $ⓣ'a GSU⌝$ will do.
To code the alternative we enclose a combinator name in two singleton sets so that it cannot be mistaken for an ordinal.

So a `combinator map' may be defined as follows.

\begin{enumerate}
\item it is a function
\item values in the domain of the function are sequences of ordinals
\item all initial segments of values in the domain are also in the domain
\item if some sequence of ordinals y is in the domain and x is some other sequence of ordinalys which has the same length as y and at every point is not greater than y, then it also is in the domain.
\end{enumerate}

ⓈHOLCONST
│ ⦏is_cmap⦎ : 'a GSU → BOOL
├───────────
│ ∀m⦁ is_cmap m ⇔ Fun⋎u m
│ ∧ (∀x⦁ x ∈⋎u Dom⋎u m ⇒ Seq⋎u x ∧ ∀y⦁ y ∈⋎u Ran⋎u x ⇒ Ordinal⋎u y)
│ ∧ (∀x y⦁ y ∈⋎u Dom⋎u m ∧ Dom⋎u x ⊆⋎u Dom⋎u y ⇒ x ∈⋎u Dom⋎u m)
│ ∧ (∀x y⦁ y ∈⋎u Dom⋎u m ∧ Dom⋎u x = Dom⋎u y ∧ (∀z⦁ z ∈⋎u Dom⋎u x ⇒ x ⋎u z ⊆⋎u y ⋎u z)
│		⇒ x ∈⋎u Dom⋎u m)
■ 

\subsubsection{The Reduction Graph}

This is a fresh start, in the exposition.
Only after I have written it will I know what to do with the preceeding material.

The idea is that a combinatory term together with a set of reduction rules determines a directed graph with labelled nodes and arcs.
The nodes and the arcs are labelled by distinct ordinals, together with certain other information.

The other information on a node is a combinatory term.
The node labelled zero is special and the combinatory term is the starting point for the reductions represented by the graph.
A location is a position in one of the combinatory terms which appear on nodes of the graph.
It consists of the number of the node and a coordinate within that term.
A location map is a map which assignes to each term affected by a reduction the new locations.

The arcs are \emph{direct reductions}, the nodes are combinatory terms together with certain other information.
A direct reduction consists of a direct reduction \emph{rule} and a location.
The other information on the nodes is a location map, which shows where constituents of `earlier' terms appear in the present term, these are sometimes called `residuals'.

\subsection{Coordinate Set Equivalence}

This is a third attempt.
It has been too early to write about this, because most of the action is taking place in my head, and the evolution of ideas continually invalidates anything I may previously have written.

In this version coordinates play a larger role so I begin with discussing coordinates.

\subsubsection{Coordinates}

To refer to specific parts of an infinitary combinatory term we use coordinate systems.
Because of the infinitary nature, a set of coordinates is a sequence of ordinals.
I think that because of the way the combinatory terms are organised this will always be a finite sequence of ordinals, though the ordinals will not in general be finite.
(This reflects the well-foundedness of these terms, there could only be infinite sequences if there were infinite descending membership chains in the underlying set theoretic representation, the infinitary nature appears, as it were, horizontally.)

A sequence of ordinals may be used to refer to parts of combinatory terms in any of the following ways:

\begin{enumerate}
\item In its primary significance the coordinates refer to a sub-term which is the whole of or a part of the term within which the coordinate system is being used.
The empty sequence refers to the whole term.
Give a term $t$ referred to by some coordinates $c$, the coordinates of the $\alpha{_th}$ element in its argument list consist of the sequence obtained by appending $\alpha$ to $c$.

\item The coordinates may also be used to refer to a combinatory constant, which would be the one at the head of the sub-term which is referred to by the coordinates.

\item Coordinates may be use to refer to an application, bearing in mind that in this system the correspondence between subterms and applications is broken.
In this case you take the sub-term which is referred to by the coordinates, and the application in question is that of which the sub-term is the argument.
Bear in mind that an infinitary combinatory term is in the sense of application used here, a possibly infinite sequence of applications.

\end{enumerate}

\subsubsection{Residuals and Node Formation}

In order to be able to talk about effecting the same reduction under differing circumstances (different points in some sequence of reductions), we need a way of describing a reduction which is independent of the details which vary.
The signficant changes are changes in location of the redex, taking into account that it may be replicated or eliminated.

The replicas of some term after a reduction of sequence of reductions are called its residuals.

If we identify a reduction by the location of its redex, then to be able to talk about the same reduction being applied before and after some other sequence of reductions it is necessary to treat a redex before some sequence of reductions as equivalent to the complete set of its residuals after the reductions.
We are therefore looking for an equivalence relation between sets of sets of coordinate sets.
That's not quite right, the coordinate sets

\subsubsection{Reductions}

Given a combinatory term and a set of reduction rules, a reduction, which is a sequence of applications of the rules, could be represented by a (possibly transfinite) sequence of coordinate sequences, if the rules are deterministic (which our will be).
This will not suffice for an approach to the Church-Rosser theorem based on a conception of reduction which is commutative, because the principle way in which `the same' reduction might differ when its application is deferred is in the coordinates at which the reduction is applied.

\subsubsection{Combinatory Direct Reductions}

We now define the effects of the primitive pure combinators in two ways.
The first is as a transformation on a term represented as a \emph{cmap}.
The second is as a residual map, which shows the new locations of the subterms of a redex.

The following function assumes that the argument $cmap$ is a $K$ redex, i.e. that its head is K and its argument list has a length greater than 1.

ⓈHOLCONST
│ ⦏K_cmap⦎ : 'a GSU → 'a GSU
├───────────
│ ∀m:('a)GSU⦁ K_cmap m = (λ⋎u cs⦁
│	let h = Head⋎u cs
│	and x = m ⋎u Unit⋎u (∅⋎u ↦⋎u ∅⋎u)
│	in	m ⋎u 
│			(if (Nat⋎u 2) ≤⋎u h
│			then	let h2 =	if natural_number⋎u h
│						then h --⋎u (Nat⋎u 1)
│						else h
│				in SeqCons⋎u h2 (Tail⋎u cs)
│			else	if h = Nat⋎u 1
│				then Tail⋎u cs
│			 	else cs)) (Gx⋎u m)
■ 

ⓈHOLCONST
│ ⦏K_rmap⦎ : 'a GSU → 'a GSU → 'a GSU
├───────────
│ ∀m⦁ K_rmap m = λ cs⦁
│	let h = Head⋎u cs
│	and x = m ⋎u Unit⋎u (∅⋎u ↦⋎u ∅⋎u)
│	in	(if (Nat⋎u 2) ≤⋎u h
│		then	let h2 =	if natural_number⋎u h
│					then h --⋎u (Nat⋎u 1)
│					else h
│			in SeqCons⋎u h2 (Tail⋎u cs)
│		else	if h = Nat⋎u 1
│			then Tail⋎u cs
│		 	else cs)
■ 

\section{Primitives of Illative Lambda Calculus}

In this section we define the primitive notions of the Illative Lambda Calculus in terms of the underlying model of terms as equivalence classes of combinators (represented as sets in GSU).

In the next section the Illative Lambda Calculus will then be developed in a separate theory abstracted away from the underlying model.

At this point it is not clear what the primitives should be, so this is exploratory material.

\subsection{The Type of Lambda-Terms}

=SML
val LT_def = new_type_defn (["LT"], "LT", ["'a"], ∃_PureInfComb_lemma);
=TEX

=GFT
⦏LT_def⦎ = ⊢ ∃ f⦁ TypeDefn PureInfComb f
=TEX

We will have a new theory for the finitary system, which I will try to confine to results in the finitary system.
The definitions and proofs will involve materials in the underlying theory, which may well be quite substantial.
These materials are supplied here, before we start the new theory.

First we need to define functions to take us between the new abstract entities and their representatives as equivalence classes of combinators.

\ignore{
=SML
set_goal([], ⌜∃abs_LT rep_LT⦁ (∀ a:'a LT⦁ abs_LT (rep_LT a) = a)
│	∧ (∀ r:'a GSU SET⦁ PureInfComb r ⇔ rep_LT (abs_LT r) = r)
│	∧ OneOne rep_LT⌝);
a (strip_asm_tac (simple_⇒_match_mp_rule1 type_lemmas_thm2 LT_def));
a (∃_tac ⌜abs⌝ THEN ∃_tac ⌜rep⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏abs_LT⦎ : 'a GSU SET → 'a LT;
│ ⦏rep_LT⦎ : 'a LT → 'a GSU SET
├───────────
│ 	  (∀ a⦁ abs_LT (rep_LT a) = a)
│	∧ (∀ r⦁ PureInfComb r ⇔ rep_LT (abs_LT r) = r)
│	∧ OneOne rep_LT
■ 

=GFT
⦏LT_clauses⦎ = ⊢ (∀ a⦁ abs_LT (rep_LT a) = a) ∧ (∀ a b⦁ rep_LT a = rep_LT b ⇔ a = b)
⦏LT_fc_thm1⦎ = ⊢ ∀ r⦁ PureInfComb r ⇒ rep_LT (abs_LT r) = r
⦏LT_fc_thm2⦎ = ⊢ ∀ x y⦁ PureInfComb x ∧ PureInfComb y
			⇒ (abs_LT x = abs_LT y ⇔ x = y)
=TEX

\ignore{
=SML
val abs_LT_def = get_spec ⌜abs_LT⌝;
set_merge_pcs ["misc3", "'icomb"];

set_goal([], ⌜(∀a:'a LT⦁ abs_LT (rep_LT a) = a)⌝);
a (rewrite_tac[abs_LT_def]);
val LT_clause1 = pop_thm();

set_goal([], ⌜(∀a b:'a LT⦁ rep_LT a = rep_LT b ⇔ a = b)⌝);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (LEMMA_T ⌜abs_LT(rep_LT a) = abs_LT(rep_LT b)⌝ ante_tac
	THEN1 asm_rewrite_tac[]);
a (rewrite_tac [LT_clause1]);
val LT_clause2 = pop_thm();

val LT_clauses = ∧_intro LT_clause1 LT_clause2;

set_goal([], ⌜∀ r⦁ PureInfComb r ⇒ (rep_LT (abs_LT r) = r)⌝);
a (rewrite_tac[abs_LT_def]);
val LT_fc_thm1 = save_pop_thm "LT_fc_thm1";

set_goal([], ⌜∀x y⦁ PureInfComb x ∧ PureInfComb y ⇒ (abs_LT x = abs_LT y ⇔ x = y)⌝);
a (rewrite_tac[abs_LT_def] THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (SYM_ASMS_T once_rewrite_tac);
a (POP_ASM_T rewrite_thm_tac);
val LT_fc_thm2 = save_pop_thm "LT_fc_thm2";

add_pc_thms "'icomb" [LT_clauses];
set_merge_pcs ["misc31", "'icomb"];
=TEX
}%ignore


\subsection{Judgements}

A proposition is an object of type \emph{LT}.
There is just one true proposition, which is the equivalence class containing $T⋎c$.
We will call this $T⋎l$.
To assert a proposition is to identify it with $T⋎l$.

Something like a sequent calculus might be best.

=SML
declare_infix  (0, "Ξ⋎l");
declare_infix  (0, "Ξ");
=TEX

ⓈHOLCONST
│ $⦏Ξ⋎l⦎ : 'a LT LIST → 'a LT → BOOL
├───────────
│ ∀pl (p:'a LT)⦁ (pl Ξ⋎l p) ⇔ ∀⋎L (Map (λp⦁ T⋎c ∈ (rep_LT p)) pl) ⇒ T⋎c ∈ (rep_LT p)
■ 

=SML
declare_alias ("Ξ", ⌜$Ξ⋎l⌝);
=TEX

=GFT
=TEX

\ignore{
=SML
val Ξ⋎l_def = get_spec ⌜ $Ξ⋎l⌝;
=TEX
}%ignore

\subsection{Primitive Combinators}

ⓈHOLCONST
│ ⦏Lift2l⦎ : 'a GSU → 'a LT 
├───────────
│ ∀c⦁ Lift2l c = abs_LT (EquivClass PIComEq c)
■ 

=GFT
=TEX

\ignore{
=SML
val Lift2l_def = get_spec ⌜Lift2l⌝;

set_goal([],⌜∀x⦁ x ∈ Csyntax ⇒ x ∈ rep_LT (Lift2l x)⌝);
a (rewrite_tac [Lift2l_def] THEN REPEAT strip_tac);
a (fc_tac [PureInfComb_∃_lemma]);
a (strip_asm_tac (∀_elim ⌜EquivClass PIComEq x⌝ LT_fc_thm1));
a (asm_rewrite_tac[]);
a (ante_tac (Equiv_PIComEq_thm) THEN split_pair_rewrite_tac[⌜PIComEq⌝][] THEN strip_tac);
a (fc_tac [equiv_class_∈_thm]);
a (lemma_tac ⌜x ∈ Fst PIComEq⌝ THEN1 asm_rewrite_tac[]);
a (asm_fc_tac[]);
val Lift2l_thm = save_pop_thm "Lift2l_thm";
=TEX
}%ignore

The combinators S, K and $≡$ are required, the others may not be made visible directly.

ⓈHOLCONST
│ ⦏S⋎l⦎ : 'a LT 
├───────────
│ S⋎l = Lift2l S⋎c
■ 

ⓈHOLCONST
│ ⦏K⋎l⦎ : 'a LT 
├───────────
│ K⋎l = Lift2l K⋎c
■ 

ⓈHOLCONST
│ $⦏≡⋎l⦎ : 'a LT 
├───────────
│ $≡⋎l = Lift2l $≡⋎c
■ 

=GFT
=TEX

=SML
declare_alias ("S", ⌜S⋎l⌝);
declare_alias ("K", ⌜K⋎l⌝);
=TEX

\ignore{
=SML
val S⋎l_def = get_spec ⌜S⋎l⌝;
val K⋎l_def = get_spec ⌜K⋎l⌝;
val ≡⋎l_def = get_spec ⌜$≡⋎l⌝;
=TEX
}%ignore

\subsection{Application and Abstraction}

To reason about this we are going to need to show that choice of representative does not matter.

=SML
declare_infix (250, "⋎l");
=TEX

ⓈHOLCONST
│ $⦏⋎l⦎ : 'a LT → 'a LT → 'a LT
├───────────
│ ∀f a⦁ f ⋎l a = Lift2l ((εx⦁ x ∈ rep_LT f) ⋎c (εx⦁ x ∈ rep_LT a))
■ 

=SML
declare_alias(".", ⌜$⋎l⌝);
declare_infix (250, ".");
=TEX

=GFT
=TEX

\ignore{
=SML
val ⋎l_def = get_spec ⌜ $⋎l⌝;
=TEX
}%ignore

\ignore{
=SML
commit_pc "'icomb";

force_new_pc "⦏icomb⦎";
merge_pcs ["misc3", "'icomb"] "icomb";
commit_pc "icomb";

force_new_pc "⦏icomb1⦎";
merge_pcs ["misc31", "'icomb"] "icomb1";
commit_pc "icomb1";
=TEX
}%ignore

\section{Illative Lambda-Calculus}

=SML
open_theory "icomb";
force_new_theory "⦏ilamb⦎";
force_new_pc ⦏"'ilamb"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'ilamb";
new_parent "equiv";
set_merge_pcs ["icomb", "'ilamb"];
=TEX


=GFT
	I = λx⦁x
=TEX

ⓈHOLCONST
│ $⦏I⋎l⦎ : 'a LT
├───────────
│ I⋎l = (S⋎l ⋎l K⋎l) ⋎l K⋎l
■

=GFT
	T = λx y⦁ x
=TEX

ⓈHOLCONST
│ $⦏T⋎l⦎ : 'a LT
├───────────
│ T⋎l = K⋎l
■

=GFT
	F = λx y⦁ y
=TEX

ⓈHOLCONST
│ $⦏F⋎l⦎ : 'a LT
├───────────
│ F⋎l = K⋎l ⋎l I⋎l
■


=SML
declare_alias ("I", ⌜I⋎l⌝);
declare_alias ("T", ⌜T⋎l⌝);
declare_alias ("F", ⌜F⋎l⌝);
=TEX


=GFT
⦏T⋎l_thm⦎ = ⊢ [] Ξ⋎l T⋎l
=TEX

\ignore{
=SML
val T⋎l_def = get_spec ⌜T⋎l⌝;
val F⋎l_def = get_spec ⌜F⋎l⌝;

set_goal([], ⌜[] Ξ T⋎l⌝);
a (rewrite_tac[Ξ⋎l_def, T⋎l_def, K⋎l_def, T⋎c_def]);
a (lemma_tac ⌜K⋎c ∈ Csyntax⌝ THEN1 rewrite_tac[]);
a (fc_tac [Lift2l_thm] THEN asm_rewrite_tac[]);
val T⋎l_thm = save_pop_thm "T⋎l_thm";
=TEX
}%ignore

\subsection{Primitive Equality}

I expect that non-primitive equalities will be normally used, but these will be defined in terms of the primitive equality.

=SML
declare_infix(210, "≡⋎n");
=TEX

ⓈHOLCONST
│ $⦏≡⋎n⦎ : 'a LT → 'a LT → 'a LT
├───────────
│ ∀x y⦁ x ≡⋎n y = $≡⋎l ⋎l x ⋎l y
■

=SML
declare_alias ("≡", ⌜$≡⋎n⌝);
=TEX

=GFT
=TEX

\ignore{
=IGN
val ≡⋎n_def = get_spec ⌜$≡⋎n⌝;
set_goal([], ⌜∀x⦁ [] Ξ x ≡⋎n x⌝);
a (strip_tac THEN rewrite_tac[≡⋎l_def, ≡⋎n_def]);

=TEX
}%ignore


\subsection{The System of Type Assignment}

=SML
set_flag ("subgoal_package_quiet", false);
set_flag ("pp_use_alias", true);
=TEX


