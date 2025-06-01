=IGN
$Id: t009.doc $
=TEX
\documentclass[12pt]{article}
%\usepackage{ProofPower}
\usepackage{A4}
%\usepackage{latexsym}
\usepackage{rbj}
\usepackage{epsf}
\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Rob Arthan and Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

%\def\ZAxDesLabel{}
%\def\ZGenericLabel{}
%\def\ZOtherLabel{}
%\def\ZSchemaLabel{}
%\def\Hide#1{\relax}

\ftlinepenalty=9999

% command used for hiding proofs (omits from listing but processes formal content)
\newcommand{\ignore}[1]{}

\title{Well-orderings and Well-foundedness}
\date{$ $Date: 2019/12/07$ $}
\author{R.D. Arthan and R.B. Jones}
\vfill
\makeindex

\begin{document}
\vfill
\maketitle
\begin{abstract}
This document consists of two parts.
The first is a theory of well-orderings prepared by Rob Arthan for possible inclusion in the ProofPower theory of ordered sets.
The second is material on well-foundedness, mainly consisting in the proof of the recursion theorem which is needed for consistency proofs of definitions by transfinite recursion respecting (if that's the right term) some well founded relationship.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2004/10/03

Last Change 2019/12/07

\href{http://www.rbjones.com/rbjpub/pp/doc/t009.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t009.pdf}

\copyright\ Rob Arthan and Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize

\end{centering}

\newpage

{\parskip=0pt\tableofcontents}

%%%%

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\newpage

\subsection{RBJ's Preface}

For context and motivation see \cite{rbjt000}.

This document has been produced by Roger Jones by hacking a document written by Rob Arthan called {\it ordered\_sets}.

This preface contains my notes on what I have done to it:

\begin{enumerate}
\item Change the name of the document.
\item Make sure theory listing uses aliases.
\item Change so that the theory of orders is not incorporated by duplication.
\item Change to suppress the listing of proofs and to include instead displays of key theorems and lemmas in the narrative.
\item Messed about with the section structure.
\item Put material on relations over a whole type and the independence proofs into a separate theory.
\item Added the material on transitive closure, the well-founded part of a relationship, and the recursion theorem.
\item A variety of material leading up to the concept of initial strict well-ordering and the proof that every set has such an ordering.
\item Transfer of the independence results into a separate theory.
\end{enumerate}

Note that theory {\tt rbjmisc}\cite{rbjt006} is now a parent, so an attempt to incorporate any of this into {\Product} would need to uncouple that dependency.

\section{INTRODUCTION}\label{INTRODUCTION}

This note contains various definitions and theorems, many of which are ultimately destined for
the {\Product} theory {\it orders}, which, it is intended, will supply a generally
useful collection of definitions and results relating to ordered sets of various kinds
(including ordered sets accompanied by some finer structure, e.g., an ordered set given as the
transitive closure of  a, not necessarily transitive, well-founded, relation, representing
some pattern for defining functions by recursion).

The significant mathematical facts that this note adds to the theory
of ordered sets are: Zorn's lemma for relations viewed as propositional
functions, the well-ordering principle and some useful equivalences to do with
well-foundedness (e.g., we show that a set is well-founded iff. it has no
infinite descending chains). These results and their proofs serve to validate
the definitions.

In part, the purpose of this note is to investigate relationships between various
primitive notions that are commonly used in talking about ordered sets.  In particular,
it is common in the literature for concepts such as well-foundedness or antisymmetry
to be defined so that they entail other properties such as irreflexivity. The goal here
is to fill out the list of primitive notions offered in the theory {\it orders} to give an
adequate vocabulary to state the various definitions commonly given in the literature
in terms of primitive notions that are independent. The result is a list of six primitive notions:
reflexivity, irreflexivity, antisymmetry, transitivity, trichotomy and a notion
we call the ``weak minimal condition'' which is an analogue of well-foundedness broadened
so as not to entail reflexivity or antisymmetry.

Where useful notions, like the customary
definition of well-foundedness, entail more than one primitive notion, in this note,
the notion is expressed in terms of the chosen primitive ones and the customary definition
is proved as a theorem.

Section~\ref{Independence} contains proofs that the chosen primitive notions are
indeed independent, by proving that for each pair $P$ and $Q$ of primitive notions
their are examples where both hold, where $P$ holds and not $Q$ and where
$Q$ holds and not $P$. This material is not intended for inclusion in the theory {\it orders},
but rather to serve as a check on the chosen formalisation (as, in a different way, do
the proofs of Zorn's lemma and the well-ordering principle).
It also provides an exercise in semi-automated
bulk theorem-proving --- the challenge being to formulate and prove the desired results
without having to type in all 45 cases and all 45 witnesses.

For the convenience of anyone wanting to run this script on {\Product},
this note is a {\Product} literate script including
the code for all the proofs (most of which though present in the source is
supressed in the printed document).

The appendices include listings of the theory set up by the code in this document.
The theory (optionally) includes the existing theorems from the theory {\it orders}.
These comprise a body of results about down-sets which amount to the proof
of the Dedekind-MacNeille completion theorem and a collection of facts about
orders induced on a set equipped with a function mapping it to an ordered set.
These are all there to support the original aim of constructing the type of real numbers.

These existing theorems are followed by a couple of results that make our definition of
the minimum condition and of well-foundedness easier to work with.
Then come two lemmas leading up to Zorn's lemma (for which all the hard work
has been done elsewhere). This is then used (together with some lemmas about
subsets of ordered sets and extensions of well-ordered sets) to prove the
well-ordering principle. This material is followed by a selection of facts about
the minimum condition and well-foundedness to do with descending sequences
and induction. This is then specialised to the case where the field of the relation
in question is expected to be the universe of a type. Analogues of all the properties
are introduced for this case and the main results are specialised to it.
Finally come results that build up to the statement that our six
primitive notions are logically independent as mentioned above.

This document requires version 2.7.1 of {\Product} --- earlier versions of
the theory {\it orders} defined constants {\it PartialOrder} and {\it LinearOrder}
(now called {\it StrictPartialOrder} and {\it StrictLinearOrder}) which conflict
with constants defined here; later versions are likely to include the definitions
and many of the theorems already.

\section{SOME PROPERTIES OF RELATIONS}\label{SOME PROPERTIES OF RELATIONS}

The definitions below follow the spirit of the existing ones by not requiring
reflexivity or irreflexivity except where necessary. The intention is to make
the primitive notions logically independent of one another.

\subsection{Definitions of Primitive Properties}

The primitive notions that are there already are: irreflexivity, antisymmetry,
transitivity and trichotomy together with other notions such as density that are
more specific to the Dedekind-MacNeille completion construction and its
use in constructing the real numbers.
To these we add the notions of: reflexivity, and
the ``weak minimum condition'' (which says that every non-empty set contains a
minimal element in a certain sense).
In terms of these primitives we define derived notions such as well-foundedness.

=SML
open_theory "orders";
force_new_theory "⦏ordered_sets⦎";
new_parent "set_thms";
new_parent "rbjmisc";
val existing_defs = map get_spec (get_consts "orders");
set_merge_pcs["basic_hol", "'sets_alg", "'savedthm_cs_∃_proof"];
=TEX

Now we give definitions for the primitives not already defined.

This one, we now abstain from providing since it is in theory $equiv\_rel$ which is now a parent.

=GFTSHOW
 ⓈHOLCONST
 │ ⦏Refl⦎ : ('a SET × ('a → 'a → BOOL)) → BOOL
 ├──────
 │ ∀ (X, $<<)⦁
 │	Refl(X, $<<)
 │ ⇔	∀x⦁x ∈ X ⇒ x <<  x
 ■
=TEX

We follow Cohn's Universal Algebra in using the term ``minimum condition''
for the condition that gives
well-foundedness of the ordered set formulated so that the ordering
relation need not be irreflexive. This is intended to accommodate
the varying conventions that are typically used in the literature for
well-ordered sets on the one hand and recursion with respect to
a well-founded relation on the other. However, this condition
entails that the relation is antisymmetric, so we take as primitive the following
weaker version.

ⓈHOLCONST
│ ⦏WeakMinCond⦎ : ('a SET × ('a → 'a → BOOL)) → BOOL
├──────
│ ∀ (X, $<<)⦁
│	WeakMinCond(X, $<<)
│ ⇔	∀A⦁ A ⊆ X ∧ ¬A = {} ⇒
│	∃x⦁ x ∈ A ∧ ∀y⦁ y ∈ A ∧ y << x ∧ ¬ y = x ⇒ x << y
■

We now have our full set of primitives.

\subsection{Definitions of Derived Properties}

The following non-primitive properties are of interest.

ⓈHOLCONST
│ ⦏PartialOrder⦎ : ('a SET × ('a → 'a → BOOL)) → BOOL
├──────
│ ∀ (X, $<<)⦁
│	PartialOrder(X, $<<)
│ ⇔	Antisym(X, $<<) ∧ Trans(X, $<<)
■

ⓈHOLCONST
│ ⦏LinearOrder⦎ : ('a SET × ('a → 'a → BOOL)) → BOOL
├──────
│ ∀ (X, $<<)⦁ LinearOrder(X, $<<) ⇔ PartialOrder(X, $<<) ∧ Trich(X, $<<)
■

ⓈHOLCONST
│ ⦏MinCond⦎ : ('a SET × ('a → 'a → BOOL)) → BOOL
├──────
│ ∀ (X, $<<)⦁
│		MinCond(X, $<<)
│	⇔	Antisym(X, $<<)
│	∧	WeakMinCond(X, $<<)
■

ⓈHOLCONST
│ ⦏WellOrdering⦎ : ('a SET × ('a → 'a → BOOL)) → BOOL
├──────
│ ∀ (X, $<<)⦁
│	WellOrdering(X, $<<)
│ ⇔	LinearOrder(X, $<<)  ∧ WeakMinCond(X, $<<) 
■


The general policy heretofore has been to express properties of relations in a manner indifferent to whether the relation is reflexive or not.
The concept of well-foundedness is important for recursive definitions and inductive reasoning, but for these purposes a strict inequality is needed.

A well-founded relation is therefore an irreflexive relation which satisfies \emph{MinCond}:


ⓈHOLCONST
│ ⦏WellFounded⦎ : ('a SET × ('a → 'a → BOOL)) → BOOL
├──────
│ ∀ (X, $<<)⦁
│	WellFounded(X, $<<)
│ ⇔	Irrefl(X, $<<)  ∧ MinCond(X, $<<) 
■

The inductive applications of well founded relations depend upon the equivalence of this definition with an induction principle.
Such an induction principle is needed for reasoning about well-orderings so further results about well-orderings will be deferred until the induction principle is in place.


\subsection{Using the Definitions}

In this section we do a little preening on the definitions, including a
recasting of the definitions for the minimum condition and well-foundedness.

\ignore{
If we're making a duplicate theory, we need to rebind the ML variables for the constants
in the theory order. If we're not, it doesn't hurt to rebind them anyway.
=SML
val ⦏down_sets_def⦎ = get_spec ⌜DownSets⌝;
val ⦏down_set_def⦎ = get_spec⌜DownSet⌝;
val ⦏cuts_def⦎ = get_spec⌜Cuts⌝;
val ⦏complete_def⦎ = get_spec⌜Complete⌝;
val ⦏unbounded_below_def⦎ = get_spec⌜UnboundedBelow⌝;
val ⦏unbounded_above_def⦎ = get_spec⌜UnboundedAbove⌝;
val ⦏has_supremum_def⦎ = get_spec⌜$HasSupremum⌝;
val ⦏upper_bound_def⦎ = get_spec⌜UpperBound⌝;
val ⦏dense_def⦎ = get_spec⌜Dense⌝;
val ⦏dense_in_def⦎ = get_spec⌜$DenseIn⌝;
val ⦏strict_linear_order_def⦎ = get_spec⌜StrictLinearOrder⌝;
val ⦏trich_def⦎ = get_spec⌜Trich⌝;
val ⦏strict_partial_order_def⦎ = get_spec⌜StrictPartialOrder⌝;
val ⦏trans_def⦎ = get_spec⌜Trans⌝;
val ⦏antisym_def⦎ = get_spec⌜Antisym⌝;
val ⦏irrefl_def⦎ = get_spec⌜Irrefl⌝;

=SML
val ⦏refl_def⦎ = get_spec⌜Refl⌝;
val ⦏partial_order_def⦎ = get_spec⌜PartialOrder⌝;
val ⦏linear_order_def⦎ = get_spec⌜LinearOrder⌝;
val ⦏weak_min_cond_def⦎ = get_spec⌜WeakMinCond⌝;
val ⦏min_cond_def⦎ = get_spec⌜MinCond⌝;
val ⦏well_ordering_def⦎ = get_spec⌜WellOrdering⌝;
val ⦏well_founded_def⦎ = get_spec⌜WellFounded⌝;
=TEX
}%ignore

A relation has the minimum condition iff. every non-empty subset has a minimal
element (in the more usual sense).
We will almost invariably use this formulation in the sequel.
Well-foundedness can be rendered similarly, in this case expression of the minimality condition is simplified by the fact that well-founded relations are by definition irreflexive.

=GFT
⦏min_cond_def_thm⦎ = ⊢ ∀X $<<⦁ MinCond(X, $<<) ⇔
	(∀ A⦁	A ⊆ X ∧ ¬ A = {}
		⇒ (∃ x⦁ x ∈ A ∧ (∀ y⦁ y ∈ A ∧ ¬ y = x ⇒ ¬ y << x)))

⦏well_founded_thm⦎ = ⊢ ∀X $<<⦁ WellFounded(X, $<<) ⇔
	(∀ A⦁	A ⊆ X ∧ ¬ A = {}
		⇒ (∃ x⦁ x ∈ A ∧ (∀ y⦁ y ∈ A ⇒ ¬ y << x)))
=TEX

\ignore{
=SML
val min_cond_def_thm = (
set_goal([], ⌜∀X $<<⦁
		MinCond(X, $<<)
	⇔	(∀ A⦁	A ⊆ X ∧ ¬ A = {}
		⇒	(∃ x⦁ x ∈ A ∧ (∀ y⦁ y ∈ A ∧ ¬ y = x ⇒ ¬ y << x)))⌝);
a(rewrite_tac [min_cond_def, antisym_def, weak_min_cond_def]);
a(REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_ufc_tac[]);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(contr_tac THEN all_asm_ufc_tac[]);
a(lemma_tac⌜x ∈ X  ∧ y ∈ X⌝ THEN1
	(REPEAT strip_tac THEN PC_T1 "sets_ext1" all_asm_ufc_tac[]));
a(rename_tac[] THEN all_asm_ufc_tac[]);
(* *** Goal "2" *** *)
a(contr_tac);
a(lemma_tac⌜{x; y} ⊆ X ∧ ¬{x; y} = {}⌝ THEN1
	PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_asm_ufc_tac[] THEN all_var_elim_asm_tac);
(* *** Goal "2.1" *** *)
a(spec_nth_asm_tac 1 ⌜y⌝ THEN all_var_elim_asm_tac);
(* *** Goal "2.2" *** *)
a(spec_nth_asm_tac 1 ⌜x⌝ THEN all_var_elim_asm_tac);
(* *** Goal "3" *** *)
a(all_asm_ufc_tac[]);
a(lemma_tac⌜x ∈ X⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(lemma_tac⌜y ∈ X⌝ THEN1 PC_T1 "sets_ext1" all_asm_ufc_tac[]);
a(all_asm_ufc_tac[]);
save_pop_thm "min_cond_def_thm"
);
=TEX

=SML
val well_founded_thm = (
set_goal([], ⌜∀X $<<⦁
		WellFounded(X, $<<)
	⇔	(∀ A⦁	A ⊆ X ∧ ¬ A = {}
		⇒	(∃ x⦁ x ∈ A ∧ (∀ y⦁ y ∈ A ⇒ ¬ y << x)))⌝);
a(rewrite_tac [well_founded_def, irrefl_def, min_cond_def_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(all_asm_ufc_tac[]);
a(∃_tac ⌜x⌝ THEN REPEAT strip_tac THEN all_asm_ufc_tac[]);
a(cases_tac ⌜¬y = x⌝ THEN1 all_asm_ufc_tac[]);
a(rename_tac[(⌜x⌝, "a")] THEN lemma_tac⌜y ∈ X⌝ THEN
	PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜{x} ⊆ X ∧ ¬{x} = {}⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_asm_ufc_tac[] THEN all_var_elim_asm_tac);
a(POP_ASM_T bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "3" *** *)
a(all_asm_ufc_tac[]);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac THEN all_asm_ufc_tac[]);
save_pop_thm "well_founded_thm"
);
=TEX
}%ignore

The following is intended for use in conjunction with {\it min\_cond\_thm}.

=GFT
⦏well_ordering_def_thm⦎ = ⊢ ∀X $<<⦁ WellOrdering(X, $<<)
	⇔ LinearOrder(X, $<<) ∧ MinCond(X, $<<)
=TEX

\ignore{
=SML
val well_ordering_def_thm = (
set_goal([], ⌜∀X $<<⦁
		WellOrdering(X, $<<)
	⇔	LinearOrder(X, $<<) ∧ MinCond(X, $<<)⌝);
a(rewrite_tac [well_ordering_def, linear_order_def, min_cond_def, partial_order_def]
	THEN taut_tac);
save_pop_thm "well_ordering_def_thm"
);
=TEX

=SML
val def_thms = [
	refl_def, partial_order_def, linear_order_def,
	weak_min_cond_def, min_cond_def_thm,
	well_ordering_def_thm, well_founded_thm
	]
	@ existing_defs;
=TEX
}%

\subsection{Lemmas about Subsets of Ordered Sets}\label{Lemmas about Subsets of Ordered Sets}

These lemmas build up to the fact that a subset of a well-ordered set is
well-ordered (which we use in the proof of the well-ordering principle).

=GFT
⦏subrel_refl_thm⦎ =
	⊢ ∀ X Y $<<⦁ Y ⊆ X ∧ Refl (X, $<<) ⇒ Refl (Y, $<<)

⦏subrel_irrefl_thm⦎ =⊢ ∀ X Y $<<⦁ Y ⊆ X ∧
		    Irrefl (X, $<<) ⇒ Irrefl (Y, $<<)

⦏subrel_antisym_thm⦎ = ⊢ ∀ X Y $<<⦁ Y ⊆ X ∧
		     Antisym (X, $<<) ⇒ Antisym (Y, $<<)

⦏subrel_trans_thm⦎ = ⊢ ∀ X Y $<<⦁ Y ⊆ X ∧
		   Trans (X, $<<) ⇒ Trans (Y, $<<)

⦏subrel_trich_thm⦎ = ⊢ ∀ X Y $<<⦁ Y ⊆ X ∧
		   Trich (X, $<<) ⇒ Trich (Y, $<<)

⦏subrel_partial_order_thm⦎ = ⊢ ∀ X Y $<<⦁ Y ⊆ X ∧
			   PartialOrder (X, $<<) ⇒ PartialOrder (Y, $<<)

⦏subrel_linear_order_thm⦎ =  ⊢ ∀ X Y $<<⦁ Y ⊆ X ∧
			  LinearOrder (X, $<<) ⇒ LinearOrder (Y, $<<)

⦏subrel_min_cond_thm⦎ =  ⊢ ∀ X Y $<<⦁ Y ⊆ X ∧
		      MinCond (X, $<<) ⇒ MinCond (Y, $<<)

⦏subrel_well_ordering_thm⦎ = ⊢ ∀X Y $<<⦁ Y ⊆ X ∧
			   WellOrdering(X, $<<) ⇒ WellOrdering(Y, $<<)
=TEX

\ignore{
=SML
val _ = set_merge_pcs["basic_hol", "'sets_ext", "'savedthm_cs_∃_proof"];

val subrel_refl_thm = (
set_goal([], ⌜∀X Y $<<⦁
	Y ⊆ X ∧ Refl(X, $<<) ⇒ Refl(Y, $<<)
⌝);
a(rewrite_tac def_thms THEN PC_T "hol1" contr_tac);
a(all_asm_ufc_tac[] THEN all_asm_ufc_tac[]);
save_pop_thm "subrel_refl_thm"
);

val subrel_irrefl_thm = (
set_goal([], ⌜∀X Y $<<⦁
	Y ⊆ X ∧ Irrefl(X, $<<) ⇒ Irrefl(Y, $<<)
⌝);
a(rewrite_tac def_thms THEN contr_tac);
a(all_asm_ufc_tac[] THEN all_asm_ufc_tac[]);
save_pop_thm "subrel_irrefl_thm"
);

val ⦏subrel_antisym_thm⦎ = (
set_goal([], ⌜∀X Y $<<⦁
	Y ⊆ X ∧ Antisym(X, $<<) ⇒ Antisym(Y, $<<)
⌝);
a(rewrite_tac def_thms THEN contr_tac);
a(all_asm_ufc_tac[] THEN all_asm_ufc_tac[]);
save_pop_thm "subrel_antisym_thm"
);

val ⦏subrel_trans_thm⦎ = (
set_goal([], ⌜∀X Y $<<⦁
	Y ⊆ X ∧ Trans(X, $<<) ⇒ Trans(Y, $<<)
⌝);
a(rewrite_tac def_thms THEN contr_tac);
a(all_asm_ufc_tac[] THEN all_asm_ufc_tac[]);
save_pop_thm "subrel_trans_thm"
);

val ⦏subrel_trich_thm⦎ = (
set_goal([], ⌜∀X Y $<<⦁
	Y ⊆ X ∧ Trich(X, $<<) ⇒ Trich(Y, $<<)
⌝);
a(rewrite_tac def_thms THEN contr_tac);
a(all_asm_ufc_tac[] THEN all_asm_ufc_tac[]);
save_pop_thm "subrel_trich_thm"
);

val ⦏subrel_partial_order_thm⦎ = (
set_goal([], ⌜∀X Y $<<⦁
	Y ⊆ X ∧ PartialOrder(X, $<<) ⇒ PartialOrder(Y, $<<)
⌝);
a(rewrite_tac [partial_order_def] THEN contr_tac
	THEN all_ufc_tac[subrel_antisym_thm, subrel_trans_thm]);
save_pop_thm "subrel_partial_order_thm"
);

val ⦏subrel_linear_order_thm⦎ = (
set_goal([], ⌜∀X Y $<<⦁
	Y ⊆ X ∧ LinearOrder(X, $<<) ⇒ LinearOrder(Y, $<<)
⌝);
a(rewrite_tac [linear_order_def] THEN contr_tac
	THEN all_ufc_tac[subrel_partial_order_thm, subrel_trich_thm]);
save_pop_thm "subrel_linear_order_thm"
);

val subrel_min_cond_thm = (
set_goal([], ⌜∀X Y $<<⦁
	Y ⊆ X ∧ MinCond(X, $<<) ⇒ MinCond(Y, $<<)
⌝);
a(rewrite_tac def_thms THEN contr_tac);
a(lemma_tac⌜∀x⦁x ∈ A ⇒ x ∈ X⌝
 THEN1 (REPEAT strip_tac)
 THEN REPEAT (all_asm_ufc_tac[]));
save_pop_thm "subrel_min_cond_thm"
);

val subrel_well_ordering_thm = (
set_goal([], ⌜∀X Y $<<⦁
	Y ⊆ X ∧ WellOrdering(X, $<<) ⇒ WellOrdering(Y, $<<)
⌝);
a(rewrite_tac [well_ordering_def_thm] THEN contr_tac
	THEN all_ufc_tac[subrel_linear_order_thm, subrel_min_cond_thm]);
save_pop_thm "subrel_well_ordering_thm"
);

val _ = set_merge_pcs["'sets_alg", "basic_hol", "'savedthm_cs_∃_proof"];
=TEX

}%ignore

\subsection{Subtype Theorems}

An injection into an ordering may be used to define an ordering over the domain of the injection.
The resulting ordering inherits some properties of the target ordering.
These are the properties which are preserved by the subset relationship over ordinals (since the resulting ordering is isomorphic with the ordering over range of the injection).

In this section we formalise this.
The ultimate aim is to show that an injection into a strict well-ordering will define a strict well-ordering over its domain, which is used to prove the existence of initial strict well-orderings.


=GFT
⦏order_injection_properties_thm⦎ = ⊢ ∀P f W $<< V $<<<⦁
	(∀X Y $<<⦁ X ⊆ Y ∧ P(Y, $<<) ⇒ P(X, $<<))
	       ∧ OneOne f
               ∧ W = {w|∃ v⦁ v ∈ V ∧ w = f v}
               ∧ $<<< = (λ x y⦁ f x << f y)
	       ∧ P (W, $<<)
	       ⇒ P (V, $<<<)⌝
=TEX

\ignore{
=IGN
set_goal([], ⌜∀P f L M N $<< $<<<⦁
	(∀X Y r⦁ X ⊆ Y ∧ P(Y, r) ⇒ P(X, r))
	∧ OneOne f
	∧ M = {w | %exists%v%spot% v ∈ S ∧ w = f v}
	∧ M ⊆ N
	∧ P(N, $<<<)
	∧ $<< = (%lambda% x y %spot% (f x) <<< (f y))
	⇒ P(L, $<<)⌝);
a (REPEAT strip_tac);
a (all_asm_fc_tac[]);

=TEX
}%ignore


\subsection{Minimal Elements}

It is useful to have a function which delivers minimal elements of a set under some relation which has such elements.
The definition below is couched to deliver something even if the relationship only satisfies the weak minimum condition.

ⓈHOLCONST
│ ⦏Mins⦎ : ('a SET × ('a → 'a → BOOL)) → 'a SET → 'a SET
├──────
│ ∀ (X, $<<) Y⦁
│   Mins(X, $<<) Y =
    {x | x ∈ X ∧ x ∈ Y ∧ ∀ y⦁ y ∈ X ∧ y ∈ Y
       ⇒ x << y ∨ x = y ∨ ¬ y << x}
■

The following theorems facilitate the use of the function.

=GFT
⦏mins_thm⦎ = ⊢ ∀ X $<< Y x⦁
	x ∈ Mins (X, $<<) Y ⇔
	(x ∈ X ∧ x ∈ Y ∧ ∀ y⦁ y ∈ X ∧ y ∈ Y
	   ⇒ x << y ∨ x = y ∨ ¬ y << x)
	
⦏weak_mins_thm⦎ = ⊢ ∀ X $<< Y x⦁
	WeakMinCond (X, $<<) ⇒
	∀ Y⦁ Y ⊆ X ∧ ¬ Y = {} ⇒ ¬ Mins (X, $<<) Y  = {}
	
⦏weak_mins_thm2⦎ = ⊢ ∀ X $<< Y x⦁
	WeakMinCond (X, $<<) ⇒
	∀ Y⦁ Y ⊆ X ∧ ¬ Y = {} ⇒ ∃x⦁ x ∈ Mins (X, $<<) Y
	
⦏full_mins_thm⦎ = ⊢ ∀ X $<< Y x⦁
	MinCond (X, $<<) ⇒
	(x ∈ Mins (X, $<<) Y ⇔
	x ∈ X ∧ x ∈ Y ∧ ∀ y⦁ y ∈ X ∧ y ∈ Y ⇒ y << x ⇒ y = x)
=TEX
\ignore{
=SML
val mins_def = get_spec ⌜Mins⌝;

set_goal([], ⌜∀ X $<< Y x⦁
	x ∈ Mins (X, $<<) Y ⇔
	x ∈ X ∧ x ∈ Y ∧ ∀ y⦁ y ∈ X ∧ y ∈ Y ⇒ x << y ∨ x = y ∨ ¬ y << x⌝); 
a (rewrite_tac [weak_min_cond_def, mins_def]
  THEN REPEAT ∀_tac THEN strip_tac);
val mins_thm = save_pop_thm "mins_thm";

set_goal([], ⌜∀ X $<<⦁ WeakMinCond (X, $<<) ⇒
	     ∀ Y x⦁ Y ⊆ X ∧ ¬ Y = {} ⇒  ¬ Mins (X, $<<) Y  = {}⌝); 
a (PC_T1 "sets_ext" rewrite_tac [weak_min_cond_def, mins_def]
  THEN REPEAT strip_tac);
a (spec_nth_asm_tac 3 ⌜Y⌝);
a (asm_fc_tac[]);
a (asm_fc_tac[]);
a (∃_tac ⌜x'⌝ THEN REPEAT strip_tac);
a (asm_fc_tac[]);
a (spec_nth_asm_tac 5 ⌜y⌝);
a (asm_rewrite_tac[]);
val weak_mins_thm = save_pop_thm "weak_mins_thm";

set_goal([], ⌜∀ X $<<⦁ WeakMinCond (X, $<<) ⇒
	     ∀ Y x⦁ Y ⊆ X ∧ ¬ Y = {} ⇒  ∃x⦁ x ∈ Mins (X, $<<) Y⌝); 
a (REPEAT_N 6 strip_tac THEN all_fc_tac[weak_mins_thm]);
a (POP_ASM_T ante_tac
  THEN PC_T1 "sets_ext" rewrite_tac[]
  THEN REPEAT strip_tac);
a (∃_tac ⌜x⌝ THEN REPEAT strip_tac);
val weak_mins_thm2 = save_pop_thm "weak_mins_thm2";

set_goal([], ⌜∀ X $<< Y x⦁
	MinCond (X, $<<) ⇒
	(x ∈ Mins (X, $<<) Y ⇔
	x ∈ X ∧ x ∈ Y ∧ ∀ y⦁ y ∈ X ∧ y ∈ Y ∧ y << x ⇒ y = x)⌝); 
a (rewrite_tac [min_cond_def, mins_def]
  THEN REPEAT ∀_tac THEN strip_tac);
a (fc_tac[antisym_def]
  THEN REPEAT strip_tac
  THEN all_asm_fc_tac[]
  THEN_TRY asm_rewrite_tac[]);
a (spec_nth_asm_tac 4 ⌜y⌝);
(* *** Goal "1" *** *)
a (list_spec_nth_asm_tac 8 [⌜x⌝,⌜y⌝]);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
val full_mins_thm = save_pop_thm "full_mins_thm";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Minr⦎ : ('a SET × ('a → 'a → BOOL)) → 'a SET → 'a
├──────
│ ∀ (X, $<<) Y⦁
│   Minr(X, $<<) Y = εx⦁ x ∈ X ∧ x ∈ Y ∧
│    	    ∀ y⦁ y ∈ X ∧ y ∈ Y ⇒ x << y ∨ x = y ∨ ¬ y << x
■

=GFT
⦏weak_minr_thm⦎ = ⊢ ∀ X $<< Y x⦁
	WeakMinCond (X, $<<) ∧ Y ⊆ X ∧ ¬Y = {} ∧ x = Minr (X, $<<) Y ⇒ 
	x ∈ Y ∧ ∀ y⦁ y ∈ Y ∧ y << x ∧ ¬ y = x ⇒ x << y
=TEX

\ignore{
=SML
val minr_def = get_spec ⌜Minr⌝ ;

set_goal([], ⌜∀ X $<< Y x⦁
	WeakMinCond (X, $<<) ∧ Y ⊆ X ∧ ¬Y = {} ∧ x = Minr (X, $<<) Y ⇒ 
	x ∈ Y ∧ ∀ y⦁ y ∈ Y ∧ y << x ∧ ¬ y = x ⇒ x << y⌝); 
a (rewrite_tac [weak_min_cond_def, minr_def]
  THEN REPEAT ∀_tac THEN strip_tac);
a (spec_nth_asm_tac 4 ⌜Y⌝);
a (ε_tac ⌜ε x⦁ x ∈ X ∧ x ∈ Y ∧ ∀ y⦁ y ∈ X ∧ y ∈ Y ⇒ x << y ∨ x = y ∨ ¬ y << x⌝);
(* *** Goal "1" *** *)
a (∃_tac ⌜x'⌝ THEN asm_rewrite_tac[] THEN strip_tac);
(* *** Goal "1.1" *** *)
a (GET_ASM_T ⌜Y ⊆ X⌝ ante_tac THEN PC_T1 "sets_ext" rewrite_tac[]);
a (strip_tac THEN asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a (REPEAT strip_tac);
a (spec_nth_asm_tac 5 ⌜y⌝ );
a (POP_ASM_T rewrite_thm_tac);
(* *** Goal "2" *** *)
a (REPEAT_N 3 (POP_ASM_T ante_tac));
a (GET_NTH_ASM_T 3 (rewrite_thm_tac o eq_sym_rule));
a (REPEAT strip_tac);
a (lemma_tac ⌜¬ x = y⌝ THEN1 (contr_tac THEN all_var_elim_asm_tac));
a (lemma_tac ⌜y ∈ X⌝);
(* *** Goal "2.1" *** *)
a (GET_ASM_T ⌜Y ⊆ X⌝ ante_tac THEN PC_T1 "sets_ext" rewrite_tac[]);
a (REPEAT strip_tac THEN asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (spec_nth_asm_tac 6 ⌜y⌝);
val weak_minr_thm = save_pop_thm "weak_minr_thm";
=TEX
}%ignore

=GFT
⦏minr_thm⦎ = ⊢ ∀ X $<< Y x⦁
	MinCond (X, $<<) ∧ Y ⊆ X ∧ ¬Y = {} ∧ x = Minr (X, $<<) Y ⇒ 
	x ∈ Y ∧ ∀ y⦁ y ∈ Y ⇒ y << x ⇒ y = x
=TEX

\ignore{
=SML
set_goal([], ⌜∀ X $<< Y x⦁
	     MinCond (X, $<<) ∧ Y ⊆ X ∧ ¬Y = {} ∧ x = Minr (X, $<<) Y ⇒ 
	     x ∈ Y ∧ ∀ y⦁ y ∈ Y ⇒ y << x ⇒ y = x⌝); 
a (rewrite_tac [min_cond_def] THEN REPEAT ∀_tac THEN strip_tac);
a (all_fc_tac[weak_minr_thm] THEN REPEAT strip_tac);
a (fc_tac[weak_minr_thm]);
a (fc_tac[antisym_def]);
a (lemma_tac ⌜x ∈ X ∧ y ∈ X⌝
  THEN1 (GET_ASM_T ⌜Y ⊆ X⌝ ante_tac
  	THEN PC_T1 "sets_ext" rewrite_tac[]
  	THEN strip_tac
	THEN asm_fc_tac[]
	THEN REPEAT strip_tac));
a (list_spec_nth_asm_tac 3 [⌜x⌝,⌜y⌝]
  THEN1 asm_rewrite_tac[]);
a (list_spec_nth_asm_tac 6 [⌜Y⌝,⌜x⌝,⌜y⌝]);
val minr_thm = save_pop_thm "minr_thm";
=TEX
}%ignore


\subsection{Injections into Orderings}

=GFT
⦏irf_injection_thm⦎ = ⊢ ∀ X $<< f⦁
	Irrefl (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	Irrefl (X, λ x y⦁ f x << f y)
=TEX

\ignore{

=SML
set_goal([], ⌜∀ X $<< f⦁
	Irrefl (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	Irrefl (X, λ x y⦁ f x << f y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[irrefl_def, one_one_def]);
a (contr_tac);
a (REPEAT (all_asm_fc_tac[]));
val irf_injection_thm = save_pop_thm "irf_injection_thm";
=TEX
}%ignore


=GFT
⦏as_injection_thm⦎ = ⊢ ∀ X $<< f⦁
	Antisym (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	Antisym (X, λ x y⦁ f x << f y)
=TEX

\ignore{

=SML
set_goal([], ⌜∀ X $<< f⦁
	Antisym (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	Antisym (X, λ x y⦁ f x << f y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[antisym_def, one_one_def]);
a (contr_tac);
a (all_asm_fc_tac[]);
a (list_spec_nth_asm_tac 10 [⌜f x⌝, ⌜f y⌝]);
a (all_asm_fc_tac[]);
val as_injection_thm = save_pop_thm "as_injection_thm";
=TEX
}%ignore

=GFT
⦏tr_injection_thm⦎ = ⊢ ∀ X $<< f⦁
	Trans (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	Trans (X, λ x y⦁ f x << f y)
=TEX

\ignore{

=SML
set_goal([], ⌜∀ X $<< f⦁
	Trans (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	Trans (X, λ x y⦁ f x << f y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[trans_def, one_one_def]);
a (contr_tac);
a (all_asm_fc_tac[]);
a (list_spec_nth_asm_tac 12 [⌜f x⌝, ⌜f y⌝, ⌜f z⌝]);
val tr_injection_thm = save_pop_thm "tr_injection_thm";
=TEX
}%ignore

=GFT
⦏po_injection_thm⦎ = ⊢ ∀ X $<< f⦁
	PartialOrder (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	PartialOrder (X, λ x y⦁ f x << f y)
=TEX

\ignore{

=SML
set_goal([], ⌜∀ X $<< f⦁
	PartialOrder (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	PartialOrder (X, λ x y⦁ f x << f y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[partial_order_def]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac[as_injection_thm]);
(* *** Goal "2" *** *)
a (all_fc_tac[tr_injection_thm]);
val po_injection_thm = save_pop_thm "po_injection_thm";
=TEX
}%ignore

=GFT
⦏tri_injection_thm⦎ = ⊢ ∀ X $<< f⦁
	Trich (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	Trich (X, λ x y⦁ f x << f y)
=TEX

\ignore{

=SML
set_goal([], ⌜∀ X $<< f⦁
	Trich (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	Trich (X, λ x y⦁ f x << f y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[trich_def, one_one_def]);
a (contr_tac);
a (all_asm_fc_tac[]);
a (list_spec_nth_asm_tac 10 [⌜f x⌝, ⌜f y⌝]);
a (all_asm_fc_tac[]);
val tri_injection_thm = save_pop_thm "tri_injection_thm";
=TEX
}%ignore

=GFT
⦏lo_injection_thm⦎ = ⊢ ∀ X $<< f⦁
	LinearOrder (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	LinearOrder (X, λ x y⦁ f x << f y)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ X $<< f⦁
	LinearOrder (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	LinearOrder (X, λ x y⦁ f x << f y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[linear_order_def]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac[po_injection_thm]);
(* *** Goal "2" *** *)
a (all_fc_tac[tri_injection_thm]);
val lo_injection_thm = save_pop_thm "lo_injection_thm";
=TEX
}%ignore

=GFT
⦏wmc_injection_thm⦎ = ⊢ ∀ X $<< f⦁
	WeakMinCond (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	WeakMinCond (X, λ x y⦁ f x << f y)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ X $<< f⦁
	WeakMinCond (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	WeakMinCond (X, λ x y⦁ f x << f y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[weak_min_cond_def, one_one_def]);
a (REPEAT strip_tac);
a (list_spec_nth_asm_tac 5 [⌜{z | ∃ x⦁ x ∈ A ∧ z = f x}⌝]);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac
  THEN PC_T1 "sets_ext" rewrite_tac[]
  THEN strip_tac);
a (asm_fc_tac[]);
a (lemma_tac ⌜x' ∈ X⌝
  THEN1 (GET_ASM_T ⌜A ⊆ X⌝ ante_tac
  	THEN PC_T1 "sets_ext" rewrite_tac[]
  	THEN strip_tac
	THEN asm_fc_tac[]
	THEN REPEAT strip_tac));
a (list_spec_nth_asm_tac 9 [⌜x'⌝]);
a (var_elim_asm_tac ⌜x = f x'⌝);
(* *** Goal "2" *** *)
a (GET_ASM_T ⌜¬ A = {}⌝ ante_tac
  THEN PC_T1 "sets_ext" rewrite_tac[]
  THEN strip_tac);
a (GET_NTH_ASM_T 2 ante_tac
  THEN PC_T1 "sets_ext" rewrite_tac[]
  THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜f x⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "3" *** *)
a (∃_tac ⌜x'⌝ THEN REPEAT strip_tac);
(* *** Goal "3.2" *** *)
a (list_spec_nth_asm_tac 10 [⌜y⌝, ⌜x'⌝]);
a (var_elim_asm_tac ⌜x = f x'⌝);
a (list_spec_nth_asm_tac 5 [⌜f y⌝]);
a (list_spec_nth_asm_tac 1 [⌜y⌝]);
val wmc_injection_thm = save_pop_thm "wmc_injection_thm";
=TEX
}%ignore


=GFT
⦏wo_injection_thm⦎ = ⊢ ∀ X $<< f⦁
	WellOrdering (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	WellOrdering (X, λ x y⦁ f x << f y)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ X $<< f⦁
	WellOrdering (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	WellOrdering (X, λ x y⦁ f x << f y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[well_ordering_def]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac[lo_injection_thm]);
(* *** Goal "2" *** *)
a (all_fc_tac[wmc_injection_thm]);
val wo_injection_thm = save_pop_thm "wo_injection_thm";
=TEX
}%ignore

\section{WELL-ORDERING}\label{WELL-ORDERING}

\subsection{Minimal Elements}

=GFT
⦏antisym_minr_thm⦎ = ⊢ ∀ X $<< Y x⦁
	MinCond (X, $<<) ∧
	Antisym (X, $<<) ∧
	Y ⊆ X ∧ ¬Y = {} ∧ x = Minr (X, $<<) Y ⇒ 
	x ∈ Y ∧ ∀ y⦁ y ∈ Y ⇒ y << x ⇒ y = x
=TEX

\ignore{
=SML
set_goal([], ⌜∀ X $<< Y x⦁
	     MinCond (X, $<<) ∧
	     Antisym (X, $<<) ∧
	     Y ⊆ X ∧ ¬Y = {} ∧ x = Minr (X, $<<) Y ⇒ 
	     x ∈ Y ∧ ∀ y⦁ y ∈ Y ⇒ y << x ⇒ y = x⌝); 
a (rewrite_tac [antisym_def]
  THEN REPEAT ∀_tac THEN strip_tac);
a (all_fc_tac[minr_thm] THEN REPEAT strip_tac);
a (lemma_tac ⌜x ∈ X ∧ y ∈ X⌝
  THEN1 (GET_ASM_T ⌜Y ⊆ X⌝ ante_tac
  	THEN PC_T1 "sets_ext" rewrite_tac[]
  	THEN strip_tac
	THEN asm_fc_tac[]
	THEN REPEAT strip_tac));
a (all_fc_tac[minr_thm] THEN REPEAT strip_tac);
val antisym_minr_thm = save_pop_thm "strict_minr_thm";
=TEX
}%ignore

=GFT
⦏wo_minr_thm⦎ = ⊢ ∀ X $<< Y x⦁
	    WellOrdering (X, $<<) ∧
	    Y ⊆ X ∧ ¬Y = {} ∧ x = Minr (X, $<<) Y ⇒ 
	    x ∈ Y ∧ ∀ y⦁ y ∈ Y ⇒ x << y ∨ y = x)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ X $<< Y x⦁
	     WellOrdering (X, $<<) ∧ Y ⊆ X ∧ ¬Y = {} ∧ x = Minr (X, $<<) Y ⇒ 
	x ∈ Y ∧ ∀ y⦁ y ∈ Y ⇒ x << y ∨ y = x⌝); 
a (rewrite_tac [well_ordering_def]
  THEN REPEAT ∀_tac THEN strip_tac
  THEN fc_tac[weak_minr_thm]);
a (list_spec_nth_asm_tac 1 [⌜Y⌝,⌜x⌝]);
a (REPEAT_N 3 strip_tac);
a (fc_tac[linear_order_def]);
a (fc_tac[trich_def]);
a (REPEAT strip_tac);
a (conv_tac eq_sym_conv);
a (contr_tac);
a (lemma_tac ⌜x ∈ X ∧ y ∈ X⌝
  THEN1 (GET_ASM_T ⌜Y ⊆ X⌝ ante_tac
  	THEN PC_T1 "sets_ext" rewrite_tac[]
  	THEN strip_tac
	THEN asm_fc_tac[]
	THEN REPEAT strip_tac));
a (list_spec_nth_asm_tac 5 [⌜x⌝,⌜y⌝]);
a (list_spec_nth_asm_tac 12 [⌜Y⌝,⌜x⌝,⌜y⌝]);
a (contr_tac);
a (var_elim_asm_tac ⌜y = x⌝ );
val wo_minr_thm = save_pop_thm "wo_minr_thm";
=TEX
}%ignore

=GFT
⦏wo_minr_thm2⦎ = ⊢ ∀ X $<< Y x⦁
	WellOrdering (X, $<<) ∧
	Y ⊆ X ∧ ¬Y = {} ∧ x = Minr (X, $<<) Y ⇒ 
	x ∈ Y ∧ ∀ y⦁ y ∈ Y ⇒ y << x ⇒ y = x
=TEX

\ignore{
=SML
set_goal([], ⌜∀ X $<< Y x⦁
	WellOrdering (X, $<<) ∧
	     Y ⊆ X ∧ ¬Y = {} ∧ x = Minr (X, $<<) Y ⇒ 
	     x ∈ Y ∧ ∀ y⦁ y ∈ Y ⇒ y << x ⇒ y = x⌝);
a (REPEAT ∀_tac THEN strip_tac);
a (lemma_tac ⌜MinCond (X, $<<) ∧ Antisym (X, $<<)⌝);
(* *** Goal "1" *** *)
a (rewrite_tac [min_cond_def]);
a (fc_tac [well_ordering_def]);
a (fc_tac [linear_order_def]);
a (fc_tac [partial_order_def]);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a ( REPEAT strip_tac THEN all_fc_tac[antisym_minr_thm]);
val wo_minr_thm2 = save_pop_thm "wo_minr_thm2";
=TEX
}%ignore

\subsection{Zorn's Lemma for Properties of Relations}

We already have Zorn's lemma in the special case where the ordered
set is some subset of the lattice of subsets of a set (and the ordering
relation is inclusion). We just need to ``interface'' with that theorem
by looking at the chains contained in an arbitrary relation.

=GFT
⦏zorn_thm2⦎ = ⊢ ∀X $<<⦁
		Trans(X, $<<)
	∧	Antisym(X, $<<)
	∧	(∀C⦁	C ⊆ X ∧ Trich(C, $<<)
		⇒	∃x⦁x ∈ X ∧ UpperBound(C, $<<, x))
	⇒	∃x⦁	x ∈ X ∧ ∀y⦁ y ∈ X ∧ ¬y = x ⇒ ¬x << y

⦏chain_singleton_extension_thm⦎ = ⊢ ∀X $<< C x⦁
		Trans(X, $<<)
	∧	C ⊆ X
	∧	Trich(C, $<<)
	∧	x ∈ X
	∧	(∀y⦁y ∈ C ⇒ y << x)
	⇒	Trich(C ∪ {x}, $<<)

⦏chain_singleton_extension_thm⦎ = ⊢ ∀X $<< C x⦁
		Trans(X, $<<)
	∧	C ⊆ X
	∧	Trich(C, $<<)
	∧	x ∈ X
	∧	(∀y⦁y ∈ C ⇒ y << x)
	⇒	Trich(C ∪ {x}, $<<)
=TEX
\ignore{
=SML
val _ = set_merge_pcs["'sets_alg", "predicates", "'savedthm_cs_∃_proof"];
=TEX

=SML
val chain_extension_thm = (
set_goal([], ⌜
	∀X $<< C D⦁
		Trans(X, $<<)
	∧	C ⊆ X
	∧	Trich(C, $<<)
	∧	D ⊆ X
	∧	Trich(D, $<<)
	∧	(∀x y⦁x ∈ C ∧ y ∈ D ⇒ x << y)
	⇒	Trich(C ∪ D, $<<)
⌝);
a(rewrite_tac[get_spec⌜Trich⌝, get_spec⌜Trans⌝] THEN REPEAT strip_tac
	THEN rename_tac[] THEN all_asm_ufc_tac[]);
save_pop_thm"chain_extension_thm"
);
=TEX

=SML
val chain_singleton_thm = (
set_goal([], ⌜
	∀$<< x⦁ Trich({x}, $<<)
⌝);
a(rewrite_tac[get_spec⌜Trich⌝] THEN REPEAT strip_tac);
a(all_var_elim_asm_tac);
save_pop_thm"chain_singleton_thm"
);
=TEX

=SML
val chain_singleton_extension_thm = (
set_goal([], ⌜
	∀X $<< C x⦁
		Trans(X, $<<)
	∧	C ⊆ X
	∧	Trich(C, $<<)
	∧	x ∈ X
	∧	(∀y⦁y ∈ C ⇒ y << x)
	⇒	Trich(C ∪ {x}, $<<)
⌝);
a(REPEAT strip_tac THEN bc_thm_tac chain_extension_thm);
a(∃_tac⌜X⌝ THEN rewrite_tac[chain_singleton_thm]);
a(all_asm_ante_tac);
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN_TRY all_var_elim_asm_tac
	THEN all_asm_ufc_tac[]);
save_pop_thm "chain_singleton_extension_thm"
);
=TEX

=SML
val zorn_thm2 = (
set_goal([], ⌜
	∀X $<<⦁
		Trans(X, $<<)
	∧	Antisym(X, $<<)
	∧	(∀C⦁	C ⊆ X ∧ Trich(C, $<<)
		⇒	∃x⦁x ∈ X ∧ UpperBound(C, $<<, x))
	⇒	∃x⦁	x ∈ X ∧ ∀y⦁ y ∈ X ∧ ¬y = x ⇒ ¬x << y
⌝);
a(REPEAT strip_tac);
a(lemma_tac ⌜∃u⦁ u = {C | C ⊆ X ∧ Trich(C, $<<) }⌝ THEN1 prove_∃_tac);
a(lemma_tac⌜¬ u = {} ∧ SubsetClosed u ∧ NestClosed u⌝);
(* *** Goal "1" *** *)
a(REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(asm_rewrite_tac[] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(∃_tac⌜{}⌝ THEN rewrite_tac[get_spec⌜Trich⌝]);
(* *** Goal "1.2" *** *)
a(rewrite_tac[get_spec⌜SubsetClosed⌝]
	THEN asm_rewrite_tac[get_spec⌜Trich⌝]);
a(REPEAT strip_tac);
(* *** Goal "1.2.1" *** *)
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "1.2.2" *** *)
a(lemma_tac⌜x ∈ a ∧ y ∈ a⌝ THEN
	REPEAT strip_tac THEN PC_T1 "sets_ext1" all_asm_ufc_tac[]);
(* *** Goal "1.3" *** *)
a(rewrite_tac[get_spec⌜NestClosed⌝]
	THEN asm_rewrite_tac[get_spec⌜Trich⌝]);
a(REPEAT strip_tac);
(* *** Goal "1.3.1" *** *)
a(PC_T1 "sets_ext1" asm_prove_tac[]);
(* *** Goal "1.3.2" *** *)
a(PC_T "sets_ext1"(DROP_ASM_T ⌜Nest v⌝
	(strip_asm_tac o list_∀_elim[⌜s⌝, ⌜s'⌝] o rewrite_rule[get_spec⌜Nest⌝])));
(* *** Goal "1.3.2.1" *** *)
a(PC_T "sets_ext1" (all_asm_ufc_tac[] THEN all_asm_ufc_tac[]));
(* *** Goal "1.3.2.2" *** *)
a(PC_T "sets_ext1" (asm_ufc_tac[] THEN all_asm_ufc_tac[]));
(* *** Goal "2" *** *)
a(all_ufc_tac[zorn_thm1]);
a(POP_ASM_T ante_tac THEN  asm_rewrite_tac[get_spec⌜Maximal⋎⊆⌝]
	THEN REPEAT strip_tac);
a(all_asm_ufc_tac[]);
a(POP_ASM_T (strip_asm_tac o rewrite_rule[get_spec⌜UpperBound⌝]));
a(∃_tac ⌜x⌝ THEN contr_tac);
a(PC_T1 "sets_ext1" lemma_tac ⌜a ⊆ X⌝ THEN1
	(GET_NTH_ASM_T 7 ante_tac THEN rewrite_tac[get_spec⌜Trich⌝]
		THEN prove_tac[]));
a(lemma_tac ⌜∀z⦁z ∈ a ⇒ z << y⌝);
(* *** Goal "2.1" *** *)
a(REPEAT strip_tac);
a(GET_NTH_ASM_T 17 (bc_thm_tac o rewrite_rule[get_spec⌜Trans⌝]));
a(∃_tac⌜x⌝ THEN asm_rewrite_tac[]);
a(all_asm_ufc_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜a ∪ {y} = a⌝ THEN1 GET_NTH_ASM_T 8 bc_thm_tac);
(* *** Goal "2.2.1" *** *)
a(REPEAT strip_tac THEN_LIST
	[PC_T1 "sets_ext1" asm_prove_tac[],
	bc_thm_tac chain_singleton_extension_thm, PC_T1 "sets_ext1" prove_tac[]]);
a(∃_tac ⌜X⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a(lemma_tac⌜y ∈ a⌝ THEN1
	(POP_ASM_T ante_tac THEN PC_T1 "sets_ext1" prove_tac[]));
a(LIST_GET_NTH_ASM_T [8] all_ufc_tac);
a(GET_NTH_ASM_T 19 (strip_asm_tac o rewrite_rule[get_spec⌜Antisym⌝]));
a(rename_tac[] THEN all_asm_ufc_tac[]);
save_pop_thm "zorn_thm2"
);

=SML
val _ = set_pc "sets_ext1";
=TEX
}%ignore
\subsection{The Well-Ordering Principle}

The following lemma is needed in the proof of the well-ordering principle. It shows
that extending a well-ordering by adding an extra element above all the existing
elements gives a well-ordering.

=GFT
⦏well_ordering_extension_lemma⦎ = ⊢ ∀A x y z $<<<⦁
	WellOrdering(A, $<<<)
∧	¬x ∈ A
⇒	WellOrdering(
		A ∪ {x},
		λ a b⦁ a ∈ A ∧ b ∈ A ∧ a <<< b ∨ a ∈ A ∧ b = x ∨ a = x ∧ b = x)⌝
=TEX

\ignore{
=SML
val ⦏well_ordering_extension_lemma = (
set_goal([], ⌜∀A x y z $<<<⦁
	WellOrdering(A, $<<<)
∧	¬x ∈ A
⇒	WellOrdering(
		A ∪ {x},
		λ a b⦁ a ∈ A ∧ b ∈ A ∧ a <<< b ∨ a ∈ A ∧ b = x ∨ a = x ∧ b = x)⌝
);
a(PC_T1 "sets_ext1" rewrite_tac def_thms THEN contr_tac
	THEN_TRY all_var_elim_asm_tac THEN_TRY SOLVED_T
	(all_asm_ufc_tac[] THEN all_asm_ufc_tac[]));
a(swap_nth_asm_concl_tac 1 THEN REPEAT strip_tac THEN rewrite_tac[]);
a(cases_tac⌜∃a⦁a ∈ A ∧ a ∈ A'⌝);
(* *** Goal "1" *** *)
a(spec_nth_asm_tac 6 ⌜{b | b ∈ A'  ∧ b ∈ A ∧ (b <<< a ∨ b = a)}⌝);
(* *** Goal "1.1" *** *)
a(spec_nth_asm_tac 1 ⌜a⌝);
(* *** Goal "1.2" *** *)
a(∃_tac⌜x''⌝ THEN contr_tac);
(* *** Goal "1.2.1" *** *)
a(spec_nth_asm_tac 5 ⌜y⌝);
a(list_spec_nth_asm_tac 17 [⌜y⌝, ⌜a⌝]);
a(list_spec_nth_asm_tac 19 [⌜a⌝, ⌜y⌝, ⌜x''⌝]);
a(list_spec_nth_asm_tac 21 [⌜x''⌝, ⌜a⌝] THEN all_var_elim_asm_tac);
(* *** Goal "1.2.2" *** *)
a(all_var_elim_asm_tac);
(* *** Goal "1.2.3" *** *)
a(all_var_elim_asm_tac);
(* *** Goal "1.3" *** *)
a(all_var_elim_asm_tac);
a(∃_tac⌜a⌝ THEN contr_tac);
(* *** Goal "1.3.1" *** *)
a(spec_nth_asm_tac 5 ⌜y⌝);
(* *** Goal "1.3.2" *** *)
a(all_var_elim_asm_tac);
(* *** Goal "1.3.3" *** *)
a(all_var_elim_asm_tac);
(* *** Goal "2" *** *)
a(cases_tac⌜∀a⦁¬a ∈ A⌝);
(* *** Goal "2.1" *** *)
a(∃_tac⌜x⌝ THEN contr_tac);
(* *** Goal "2.1.1" *** *)
a(spec_nth_asm_tac 5 ⌜x'⌝ THEN1 all_asm_ufc_tac[]);
a(all_var_elim_asm_tac);
(* *** Goal "2.1.2" *** *)
a(spec_nth_asm_tac 5 ⌜y⌝ THEN1 all_asm_ufc_tac[]);
(* *** Goal "2.2" *** *)
a(spec_nth_asm_tac 4 ⌜x'⌝ THEN1 all_asm_ufc_tac[]);
a(all_var_elim_asm_tac);
a(∃_tac⌜x⌝ THEN contr_tac);
a(spec_nth_asm_tac 5 ⌜y⌝ THEN1 all_asm_ufc_tac[]);
save_pop_thm "well_ordering_extension_lemma"
);
=TEX
}%ignore

The proof of the well-ordering is much as per Halmos.
Some care is needed to get the construction right and to avoid an embarrassment of case splits.
We have to exhibit a well-ordering on some arbitrary set $X$. Since subsets of well-ordered
sets are well-ordered it suffices to well-order the universe of the type of the elements of $X$.
To do this we define $U$ to be the set of all relations that well-order their field and
are reflexive on their field:

=SML
val _ = set_merge_pcs["'sets_alg", "basic_hol", "'savedthm_cs_∃_proof"];

val u_def = ⌜∃U⦁
	U =
	{	R : 'a → 'a → BOOL
	|	WellOrdering({a | R a a}, R) ∧ ∀a b⦁ R a b ⇒ R a a ∧ R b b}⌝;
=TEX

$U$ is partial ordered by saying $R {<<<} S$ iff. $R$ is an Initial segment of $S$:

=SML
val segment_def = ⌜∃$<<<⦁ ∀R S: 'a → 'a → BOOL⦁ 
		R <<< S
	⇔	(∀a b⦁R a b ⇒ S a b)
	∧	(∀a b⦁R a a ∧ ¬R b b ∧ S b b ⇒ S a b)⌝;
=TEX

We then verify that $U$ and ${<<<}$ satisfy the hypotheses of Zorn's lemma:

=SML
val zorn_hyps =  ⌜
		Trans(U : ('a → 'a → BOOL) SET, $<<<)
	∧	Antisym(U, $<<<)
	∧	(∀ C⦁ C ⊆ U ∧ Trich (C, $<<<) ⇒
			(∃ x⦁ x ∈ U ∧ UpperBound (C, $<<<, x)))⌝;
=TEX

This verification, done naively would involve a large number of case splits in the situation
where we have two members $R$ and $S$ of a chain, so that either $R$ precedes $S$
or $S$ precedes $R$ --- one part of the formal proof would branch into 16 cases, if we proceeded
in the naive way. Instead, we use the following lemma which shows that any two elements, $R$ and $S$,
of a chain are both contained (viewed as sets of pairs) in some other element, $Q$. Of course,
$Q$ can be taken to be one or other of $R$ and $S$, but that does not matter for all but
one of the properties we have to prove.. This property is that the upper bounds
of chains satisfy the minimum condition, and the case split in question is unavoidable since the
arguments are essentially different for the two cases. 

=SML
val key_lemma =⌜∀R S : 'a → 'a → BOOL⦁
		R ∈ C ∧ S ∈ C
	⇒ 	∃Q⦁
		Q ∈ C
	∧	(∀a b⦁R a b ⇒ Q a b )
	∧	(∀a b⦁S a b ⇒ Q a b )⌝;
=TEX

Once we have the hypotheses of Zorn's lemma, we apply it to produce a maximal element for
the initial segment relation and then prove that the field of such a maximal element must be
the whole set. Most of the work for this has been done in the previous theorem about
single element extensions of well-orderings.

=GFT
⦏well_ordering_thm⦎ = ⊢ ∀X :'a SET⦁ ∃ $<<⦁ WellOrdering(X, $<<)
=TEX

\ignore{
=SML
val ⦏well_ordering_thm⦎ = ( 
set_goal([], ⌜∀X :'a SET⦁ ∃ $<<⦁ WellOrdering(X, $<<)⌝);
a(REPEAT strip_tac);
a(lemma_tac u_def THEN1 prove_∃_tac);
a(lemma_tac segment_def THEN1 prove_∃_tac);
a(lemma_tac zorn_hyps);
(* *** Goal "1" *** *)
a(REPEAT strip_tac);
(* *** Goal "1.1" *** *) (* Transitivity *)
a(asm_rewrite_tac[trans_def] THEN REPEAT strip_tac
	THEN1 (all_asm_ufc_tac[] THEN all_asm_ufc_tac[]));
a(cases_tac⌜y a a ⌝ THEN all_asm_ufc_tac[]);
a(cases_tac⌜y b b ⌝ THEN all_asm_ufc_tac[] THEN all_asm_ufc_tac[]);
(* *** Goal "1.2" *** *) (* Antisymmetry *)
a(asm_rewrite_tac[antisym_def] THEN  contr_tac);
a(LIST_GET_NTH_ASM_T [2, 4, 5] (MAP_EVERY ante_tac) THEN
	rewrite_tac[ext_thm] THEN prove_tac[]);
(* *** Goal "1.3" *** *) (* Upper bounds *)
a(POP_ASM_T (strip_asm_tac o rewrite_rule[trich_def]));
a(lemma_tac key_lemma);
(* *** Goal "1.3.1" *** *)
a(REPEAT strip_tac);
a(cases_tac⌜R = S⌝ THEN1 (∃_tac⌜R⌝ THEN asm_rewrite_tac[]));
a(lemma_tac⌜∀R S⦁
		R ∈ C ∧ S ∈ C ∧ R <<< S
	⇒ 	∃Q⦁
		Q ∈ C
	∧	(∀a b⦁R a b ⇒ Q a b )
	∧	(∀a b⦁S a b ⇒ Q a b )⌝);
(* *** Goal "1.3.1.1" *** *)
a(rename_tac [] THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜S'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.3.1.2" *** *)
a(list_spec_nth_asm_tac 5 [⌜R⌝, ⌜S⌝] THEN rename_tac[] THEN all_asm_ufc_tac[]
	THEN ∃_tac⌜Q:'a → 'a → BOOL⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.3.2" *** *)
a(lemma_tac⌜∀R⦁
	R ∈ C ⇒ WellOrdering ({a|R a a}, R) ∧ (∀ a b⦁ R a b ⇒ R a a ∧ R b b)⌝);
(* *** Goal "1.3.2.1" *** *)
a(REPEAT_N 2 strip_tac);
a(LEMMA_T ⌜R ∈ U⌝ ante_tac THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(asm_rewrite_tac[] THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "1.3.2.2" *** *)
a(rewrite_tac[upper_bound_def]);
a(∃_tac⌜λa b⦁∃R⦁ R ∈ C ∧ R a b⌝
	THEN asm_rewrite_tac[] THEN REPEAT strip_tac
	THEN_TRY (SOLVED_T 
		(contr_tac THEN all_asm_ufc_tac[] THEN all_asm_ufc_tac[])));
(* *** Goal "1.3.2.2.1" *** *) (* Union is a well-ordering *)
a(POP_ASM_T ante_tac THEN rewrite_tac def_thms THEN REPEAT strip_tac);
(* *** Goal "1.3.2.2.1.1" *** *)
(* of the 4 subgoals for the well-ordering properties and the other property for U *)
(* Antisymmetry *)
a(contr_tac);
a(list_spec_asm_tac key_lemma [⌜R⌝, ⌜R'⌝]);
a(list_spec_asm_tac key_lemma [⌜R''⌝, ⌜Q⌝]);
a(list_spec_asm_tac key_lemma [⌜R'''⌝, ⌜Q'⌝]);
a(LIST_GET_NTH_ASM_T [1, 2, 4, 5, 7, 8]
	(fn ths => REPEAT (CHANGED_T(all_ufc_tac ths))));
a(LIST_GET_NTH_ASM_T [28] all_ufc_tac);
(* *** Goal "1.3.2.2.1.2" *** *)
(* Transitivity *)
a(list_spec_asm_tac key_lemma [⌜R⌝, ⌜R'⌝]);
a(list_spec_asm_tac key_lemma [⌜R''⌝, ⌜Q⌝]);
a(list_spec_asm_tac key_lemma [⌜R'''⌝, ⌜Q'⌝]);
a(list_spec_asm_tac key_lemma [⌜R''''⌝, ⌜Q''⌝]);
a(lemma_tac⌜Q''' x y ∧ Q''' y z⌝ THEN1
	(LIST_GET_NTH_ASM_T [1, 2, 4, 5, 7, 8]
		(fn ths => REPEAT (CHANGED_T(all_ufc_tac ths))))
	THEN REPEAT strip_tac);
a(lemma_tac⌜Q'''  x z⌝ THEN1
	(LIST_GET_NTH_ASM_T [25]
		(fn ths => REPEAT (CHANGED_T(all_ufc_tac ths)))));
a(CONTR_T (fn th => all_ufc_tac[th]));
(* *** Goal "1.3.2.2.1.3" *** *)
(* the other property in U: members of U are reflexive on their field: *)
a(list_spec_asm_tac key_lemma [⌜R⌝, ⌜R'⌝]);
a(lemma_tac⌜Q x x ∧ Q y y⌝ THEN1
	(LIST_GET_NTH_ASM_T [1, 2]
		(fn ths => REPEAT (CHANGED_T(all_ufc_tac ths))))
	THEN REPEAT strip_tac);
a(spec_nth_asm_tac 6 ⌜Q⌝);
a(LIST_GET_NTH_ASM_T [13] all_ufc_tac);
a(CONTR_T (fn th => all_ufc_tac[th]));
(* *** Goal "1.3.2.2.1.4" *** *)
(* Minimum condition *)
a(POP_ASM_T ante_tac THEN POP_ASM_T ante_tac
	THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(PC_T1 "sets_ext1" all_asm_ufc_tac[]);
a(lemma_tac⌜
	¬{a | R a a ∧ a ∈ A} = {} ∧ {a | R a a ∧ a ∈ A} ⊆ {a | R a a}
⌝ THEN1
	(LIST_GET_NTH_ASM_T [1, 3] (MAP_EVERY ante_tac)
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(LIST_GET_NTH_ASM_T [7] all_ufc_tac);
a(∃_tac⌜x'⌝ THEN contr_tac);
a(lemma_tac⌜∀R S x y⦁ R ∈ C ∧ S ∈ C ∧ R x x ∧ S y x ⇒ R y x⌝);
(* *** Goal "1.3.2.2.1.4.1" *** *)
a(LIST_DROP_NTH_ASM_T (interval 1 15) discard_tac THEN REPEAT strip_tac);
a(cases_tac ⌜R = S⌝ THEN1 all_var_elim_asm_tac);
a(LIST_SPEC_NTH_ASM_T 6 [⌜R⌝, ⌜S⌝]  ante_tac);
a(LIST_GET_NTH_ASM_T [8] rewrite_tac THEN contr_tac);
(* *** Goal "1.3.2.2.1.4.1.1" *** *)
a(cases_tac⌜R y y⌝);
(* *** Goal "1.3.2.2.1.4.1.1.1" *** *)
a(LEMMA_T ⌜R ∈ U⌝ ante_tac THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(asm_rewrite_tac def_thms THEN REPEAT strip_tac);
a(cases_tac ⌜x = y⌝ THEN1 all_var_elim_asm_tac);
a(LIST_SPEC_NTH_ASM_T 3 [⌜x⌝, ⌜y⌝]  ante_tac);
a(LIST_GET_NTH_ASM_T [12, 6, 7, 1] rewrite_tac);
a(strip_tac);
a(LIST_GET_NTH_ASM_T [10] all_ufc_tac);
a(LEMMA_T ⌜S ∈ U⌝ ante_tac THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(asm_rewrite_tac def_thms THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T [5] all_ufc_tac);
(* *** Goal "1.3.2.2.1.4.1.1.2" *** *)
a(LEMMA_T ⌜S ∈ U⌝ ante_tac THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(asm_rewrite_tac def_thms THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T [4] all_ufc_tac);
a(LIST_GET_NTH_ASM_T [9] all_ufc_tac);
a(cases_tac ⌜x = y⌝ THEN1 all_var_elim_asm_tac);
a(contr_tac);
a(LIST_GET_NTH_ASM_T [1] all_ufc_tac);
(* *** Goal "1.3.2.2.1.4.1.2" *** *)
a(LIST_GET_NTH_ASM_T [3] all_ufc_tac);
(* *** Goal "1.3.2.2.1.4.2" *** *)
a(LIST_GET_NTH_ASM_T [1] all_ufc_tac);
a(LEMMA_T ⌜R ∈ U⌝ ante_tac THEN1 
	(LIST_GET_NTH_ASM_T [19, 13] (MAP_EVERY ante_tac)
		THEN PC_T1 "sets_ext1" prove_tac[]));
a(LIST_GET_NTH_ASM_T [21] rewrite_tac THEN REPEAT strip_tac);
a(LIST_GET_NTH_ASM_T [1] all_ufc_tac);
a(LIST_GET_NTH_ASM_T [9] all_ufc_tac);
(* *** Goal "1.3.2.2.2" *** *)
a(rename_tac[(⌜a⌝, "S")] THEN cases_tac ⌜R = S⌝ THEN1 all_var_elim_asm_tac);
a(LIST_SPEC_NTH_ASM_T 9 [⌜R⌝, ⌜S⌝]  ante_tac);
a(LIST_GET_NTH_ASM_T [11] rewrite_tac);
a(REPEAT strip_tac THEN1 all_asm_ufc_tac[]);
a(LIST_GET_NTH_ASM_T [1] all_ufc_tac);
a(CONTR_T (fn th => all_ufc_tac[th]));
(* *** Goal "2" *** *)
a(all_ufc_tac[zorn_thm2]);
a(LIST_DROP_NTH_ASM_T [3, 4, 5] discard_tac);
a(∃_tac ⌜x⌝ THEN rename_tac[(⌜x⌝, "<<")]);
a(bc_thm_tac subrel_well_ordering_thm);
a(∃_tac⌜Universe⌝ THEN contr_tac);
a(swap_nth_asm_concl_tac 3 THEN asm_rewrite_tac[] THEN contr_tac);
a(lemma_tac⌜¬{a | a << a} = Universe⌝ THEN1
	(swap_nth_asm_concl_tac 2 THEN asm_rewrite_tac[]));
a(POP_ASM_T (PC_T1 "sets_ext1" strip_asm_tac));
a(all_ufc_tac[∀_elim⌜{a | a << a}⌝ well_ordering_extension_lemma]);
a(lemma_tac⌜(λ a b⦁
	a ∈ {a | a << a} ∧ b ∈ {a | a << a} ∧ a << b ∨ a ∈ {a | a << a} ∧ b = x
∨	a = x ∧ b = x) ∈ U⌝);
(* *** Goal "2.1" *** *)
a(POP_ASM_T ante_tac THEN LIST_GET_NTH_ASM_T [7] rewrite_tac);
a(rewrite_tac[pc_rule1 "sets_ext1" prove_rule[]
	⌜{a|a << a ∨ a << a ∧ a = x ∨ a = x} = {a | a << a} ∪ {x}⌝]);
a(REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a(lemma_tac⌜¬(λ a b⦁
	a ∈ {a | a << a} ∧ b ∈ {a | a << a} ∧ a << b ∨ a ∈ {a | a << a} ∧ b = x
∨	a = x ∧ b = x) = $<<⌝);
(* *** Goal "2.2.1" *** *)
a(rewrite_tac[ext_thm] THEN REPEAT strip_tac);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.2" *** *)
a(lemma_tac⌜$<< <<< (λ a b⦁
	a ∈ {a | a << a} ∧ b ∈ {a | a << a} ∧ a << b ∨ a ∈ {a | a << a} ∧ b = x
∨	a = x ∧ b = x) ⌝);
(* *** Goal "2.2.2.1" *** *)
a(LIST_GET_NTH_ASM_T [9] rewrite_tac);
a(REPEAT strip_tac THEN all_asm_ufc_tac[]);
(* *** Goal "2.2.2.2" *** *)
a(all_asm_ufc_tac[]);
save_pop_thm "well_ordering_thm"
);
=TEX
}%ignore
\section{STRICT WELL-ORDERINGS}\label{STRICT WELL-ORDERINGS}

\subsection{Strictness}

The concept of well-foundedness is distinctive here in applying only to strict, i.e. irreflexive relations.
This usage is adopted because well-foundedness is used as a criterion for judging the consistency of recursive definitions, which is secured if the values referred to on the right of a recursive definition are less than the value on the left under some strictly well-founded relationship.
For this reason we require a well-founded relation to be irreflexive.

In this context the variant of the well-ordering theorem which delivers a strict (and hence well-founded) well-order may be of use, and more generally therefore the theorems which show that strict (irreflexive) versions of relations have most of the properties of interest here which are possessed by the original.


ⓈHOLCONST
│ ⦏Strict⦎ : ('a SET × ('a → 'a → BOOL))
│		→ ('a SET × ('a → 'a → BOOL))
├──────
│ ∀ (X, $<<)⦁
│	Strict (X, $<<)
│ =	(X, λx y⦁ x << y ∧ ¬ x = y)
■

[This is a bad definition, because it meddles with the relation outside its domain of relevance, and so may change a relation which is already irreflexive over its explicit domain.
It would be better to define strict over the relation only, though perhaps it would be better not to work with this concept of relation at all and just to stick with the native HOL conception of a relation as curried property of pairs.]

A few lemmas for proving properties of strict relations:

=GFT
⦏IrreflStrict_thm⦎ =
	⊢ ∀ X $<<⦁ Irrefl (Strict (X, $<<))
⦏PartialOrderStrict_thm⦎ = 
	⊢ ∀ X $<<⦁ PartialOrder (X, $<<) ⇒ PartialOrder (Strict (X, $<<))
⦏TrichStrict_thm⦎ =
	⊢ ∀ X $<<⦁ Trich (X, $<<) ⇒ Trich (Strict (X, $<<))
⦏LinearOrderStrict_thm⦎ =
	⊢ ∀ X $<<⦁ LinearOrder (X, $<<) ⇒ LinearOrder (Strict (X, $<<))
⦏AntisymStrict_thm⦎ =
	⊢ ∀ X $<<⦁ Antisym (X, $<<) ⇒ Antisym (Strict (X, $<<))
⦏WeakMinCondStrict_thm⦎ =
	⊢ ∀ X $<<⦁ WeakMinCond (X, $<<) ⇒ WeakMinCond (Strict (X, $<<))
⦏WellOrderingStrict_thm⦎ =
	⊢ ∀ X $<<⦁ WellOrdering (X, $<<) ⇒ WellOrdering (Strict (X, $<<))
⦏MinCondStrict_thm⦎ =
	⊢ ∀ X $<<⦁ LinearOrder (X, $<<) ∧ WeakMinCond (X, $<<)
		⇒ MinCond (Strict (X, $<<))
⦏WellFoundedStrict_thm⦎ =
	⊢ ∀ X $<<⦁ WellOrdering (X, $<<) ⇒ WellFounded (Strict (X, $<<))
=TEX

\ignore{
=SML
val strict_def = get_spec ⌜Strict⌝;

set_goal([], ⌜∀ (X:'a SET) ($<<:('a → 'a → BOOL))⦁ Irrefl (Strict (X, $<<))⌝);
a (rewrite_tac[irrefl_def, strict_def] THEN REPEAT strip_tac);
val IrreflStrict_thm = save_pop_thm "IrreflStrict_thm";


set_goal([], ⌜∀ (X:'a SET) $<<⦁ PartialOrder (X, $<<) ⇒ PartialOrder (Strict (X, $<<))⌝);
a (strip_tac THEN rewrite_tac[partial_order_def, trans_def, antisym_def, strict_def]
	THEN contr_tac THEN all_asm_fc_tac[]);
a (all_var_elim_asm_tac);
a (all_asm_fc_tac[]);
val PartialOrderStrict_thm = save_pop_thm "PartialOrderStrict_thm";

set_goal([], ⌜∀ (X:'a SET) ($<<:'a → 'a → BOOL)⦁ Trich (X, $<<) ⇒ Trich (Strict (X, $<<))⌝);
a (strip_tac THEN rewrite_tac[trich_def, strict_def]
	THEN contr_tac THEN all_asm_fc_tac[]);
a (all_var_elim_asm_tac);
val TrichStrict_thm = save_pop_thm "TrichStrict_thm";

set_goal([], ⌜∀ (X:'a SET) ($<<:'a → 'a → BOOL)⦁ LinearOrder (X, $<<) ⇒ LinearOrder (Strict (X, $<<))⌝);
a (REPEAT ∀_tac THEN rewrite_tac[linear_order_def]);
a (strip_tac THEN fc_tac [PartialOrderStrict_thm, TrichStrict_thm]);
a (REPEAT_N 2 (POP_ASM_T ante_tac) THEN rewrite_tac [strict_def, linear_order_def]
	THEN REPEAT strip_tac);
val LinearOrderStrict_thm = save_pop_thm "LinearOrderStrict_thm";

set_goal([], ⌜∀ (X:'a SET) ($<<:'a → 'a → BOOL)⦁ Antisym (X, $<<) ⇒ Antisym (Strict (X, $<<))⌝);
a (REPEAT ∀_tac THEN rewrite_tac[strict_def, antisym_def]);
a (contr_tac THEN all_asm_fc_tac[]);
val AntisymStrict_thm = save_pop_thm "AntisymStrict_thm";

set_goal([], ⌜∀ (X:'a SET) ($<<:'a → 'a → BOOL)⦁ WeakMinCond (X, $<<) ⇒ WeakMinCond (Strict(X, $<<))⌝);
a (REPEAT ∀_tac THEN rewrite_tac[strict_def, weak_min_cond_def]);
a (contr_tac THEN all_asm_fc_tac[]);
a (spec_nth_asm_tac 3 ⌜x⌝ THEN1 all_asm_fc_tac[]);
a (all_var_elim_asm_tac);
val WeakMinCondStrict_thm = save_pop_thm "WeakMinCondStrict_thm";

set_goal([], ⌜∀ (X:'a SET) ($<<:'a → 'a → BOOL)⦁ WellOrdering (X, $<<) ⇒ WellOrdering (Strict (X, $<<))⌝);
a (REPEAT ∀_tac THEN rewrite_tac[well_ordering_def]
	THEN strip_tac
	THEN asm_fc_tac [LinearOrderStrict_thm, WeakMinCondStrict_thm]
	THEN REPEAT_N 2 (POP_ASM_T ante_tac)
	THEN rewrite_tac [strict_def, well_ordering_def]
	THEN REPEAT strip_tac);
val WellOrderingStrict_thm = save_pop_thm "WellOrderingStrict_thm";

set_goal([], ⌜∀ (X:'a SET) ($<<:'a → 'a → BOOL)⦁
	LinearOrder (X, $<<) ∧ WeakMinCond (X, $<<)
               ⇒ MinCond (Strict (X, $<<))⌝);
a (rewrite_tac[weak_min_cond_def, min_cond_def, strict_def, antisym_def]
	THEN contr_tac);
(* *** Goal "1" *** *)
a (fc_tac [linear_order_def]);
a (fc_tac [partial_order_def]);
a (fc_tac [antisym_def]);
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (all_asm_fc_tac[]);
a (spec_nth_asm_tac 3 ⌜x⌝);
(* *** Goal "2.1" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (all_var_elim_asm_tac);
val MinCondStrict_thm = save_pop_thm "MinCondStrict_thm";

set_goal([], ⌜∀ (X:'a SET) ($<<:'a → 'a → BOOL)⦁ WellOrdering (X, $<<) ⇒ WellFounded (Strict (X, $<<))⌝);
a (rewrite_tac[
	well_ordering_def, well_founded_def,
	rewrite_rule[strict_def] IrreflStrict_thm]);
a (REPEAT strip_tac THEN asm_fc_tac[MinCondStrict_thm]);
a (POP_ASM_T ante_tac THEN rewrite_tac [well_founded_def, strict_def]
	THEN REPEAT strip_tac);
a (rewrite_tac[rewrite_rule[strict_def]IrreflStrict_thm]);
val WellFoundedStrict_thm = save_pop_thm "WellFoundedStrict_thm";
=TEX
}%ignore

Then a wrinkle on the well-ordering theorem:

=GFT
⦏wf_well_ordering_thm⦎ =
	⊢ ∀X :'a SET⦁ ∃ $<<⦁ WellOrdering(X, $<<) ∧ WellFounded(X, $<<)
=TEX

\ignore{
=SML
set_goal([], ⌜∀X :'a SET⦁ ∃ $<<⦁ WellOrdering(X, $<<) ∧ WellFounded(X, $<<)⌝);
a (strip_tac);
a (strip_asm_tac well_ordering_thm THEN spec_nth_asm_tac 1 ⌜X⌝);
a (∃_tac ⌜Snd(Strict (X, $<<))⌝);
a (fc_tac[WellOrderingStrict_thm, WellFoundedStrict_thm]);
a (REPEAT_N 2 (POP_ASM_T ante_tac)
	THEN rewrite_tac[strict_def]
	THEN REPEAT strip_tac);
val wf_well_ordering_thm = save_pop_thm "wf_well_ordering_thm";
=TEX
}%ignore

\subsection{Strict Well-Orderings}

We might as well have the concept of strict well-ordering.

ⓈHOLCONST
│ ⦏StrictWellOrdering⦎ : ('a SET × ('a → 'a → BOOL)) → BOOL
├──────
│ ∀(X, $<<)⦁ StrictWellOrdering (X, $<<)
│	⇔ Irrefl (X, $<<) ∧ WellOrdering (X, $<<)
■

=GFT
⦏StrictWellOrdering_thm1⦎ =
	⊢ ∀ X $<<⦁ WellOrdering (X, $<<) ⇒ StrictWellOrdering (Strict (X, $<<))
   
⦏SWO_WellFounded_thm⦎ =
  	⊢ ∀ X $<<⦁ StrictWellOrdering (X, $<<) ⇒ WellFounded (X, $<<)

⦏strict_well_ordering_thm⦎ =
	⊢ ∀X :'a SET⦁ ∃ $<<⦁ StrictWellOrdering(X, $<<)
=TEX

\ignore{
=SML
val strict_well_ordering_def = get_spec ⌜StrictWellOrdering⌝;

set_goal([], ⌜∀ X $<<⦁ WellOrdering (X, $<<) ⇒ StrictWellOrdering (Strict (X, $<<))⌝);
a (REPEAT strip_tac);
a (once_rewrite_tac [prove_rule [] ⌜Strict (X, $<<)=(Fst (Strict (X, $<<)):'a SET, Snd (Strict (X, $<<)))⌝, strict_well_ordering_def, IrreflStrict_thm]);
a (pure_rewrite_tac[strict_well_ordering_def]);
a (asm_rewrite_tac [IrreflStrict_thm, WellFoundedStrict_thm]);
a (fc_tac [WellOrderingStrict_thm]);
val StrictWellOrdering_thm1 = save_pop_thm "StrictWellOrdering_thm1";

set_goal([], ⌜∀ X $<<⦁ StrictWellOrdering (X, $<<) ⇒ WellFounded (X, $<<)⌝);
a (strip_tac THEN rewrite_tac[strict_well_ordering_def, well_ordering_def, well_founded_def, min_cond_def, weak_min_cond_def, linear_order_def, partial_order_def]);
a (REPEAT strip_tac THEN all_asm_fc_tac[]);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val SWO_WellFounded_thm = save_pop_thm "SWO_WellFounded_thm";

set_goal([], ⌜∀X :'a SET⦁ ∃ $<<⦁ StrictWellOrdering(X, $<<)⌝);
a (strip_tac THEN strip_asm_tac well_ordering_thm);
a (spec_asm_tac ⌜∀ X⦁ ∃ $<<⦁ WellOrdering (X, $<<)⌝ ⌜X⌝);
a (∃_tac ⌜Snd (Strict (X, $<<))⌝ THEN asm_fc_tac [StrictWellOrdering_thm1]);
a (LEMMA_T ⌜(X, Snd (Strict (X, $<<))) = Strict(X, $<<)⌝ rewrite_thm_tac
  THEN1 rewrite_tac [strict_def]);
a strip_tac;
val strict_well_ordering_thm = save_pop_thm "strict_well_ordering_thm";
=TEX
}%ignore

=GFT
⦏swo_minr_thm⦎ = ⊢ ∀ X $<< Y x⦁
	StrictWellOrdering (X, $<<) ∧
	Y ⊆ X ∧ ¬Y = {} ∧ x = Minr (X, $<<) Y ⇒ 
	x ∈ Y ∧ ∀ y⦁ y ∈ Y ⇒ (¬x = y ⇔ x << y)
=TEX

\ignore{
=SML
val StrictWellOrdering_def = get_spec ⌜StrictWellOrdering⌝;

set_goal([], ⌜∀ X $<< Y x⦁
	StrictWellOrdering (X, $<<) ∧
	     Y ⊆ X ∧ ¬Y = {} ∧ x = Minr (X, $<<) Y ⇒ 
	     x ∈ Y ∧ ∀ y⦁ y ∈ Y ⇒ (¬x = y ⇔ x << y)⌝);
a (REPEAT ∀_tac THEN strip_tac);
a (fc_tac[strict_well_ordering_def]);
a (fc_tac[irrefl_def]);
a (lemma_tac ⌜x ∈ Y⌝ THEN1 all_asm_fc_tac [wo_minr_thm]);
a (lemma_tac ⌜x ∈ X⌝
  THEN1 (GET_ASM_T ⌜Y ⊆ X⌝ ante_tac
  	THEN PC_T1 "sets_ext" rewrite_tac[]
  	THEN strip_tac
	THEN asm_fc_tac[]
	THEN REPEAT strip_tac));
a (lemma_tac ⌜¬ x << x⌝ THEN1 all_asm_fc_tac []);
a (contr_tac
  THEN all_asm_fc_tac [wo_minr_thm]
  THEN all_var_elim_asm_tac);
val swo_minr_thm = save_pop_thm "swo_minr_thm";
=TEX
}%ignore

=GFT
⦏swo_injection_thm⦎ = ⊢ ∀ X $<< f⦁
	StrictWellOrdering (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	StrictWellOrdering (X, λ x y⦁ f x << f y)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ X $<< f⦁
	StrictWellOrdering (X, $<<) ∧
	OneOne f ∧ (∀ x⦁ x ∈ X ⇒ f x ∈ X) ⇒
	StrictWellOrdering (X, λ x y⦁ f x << f y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[strict_well_ordering_def]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac[irf_injection_thm]);
(* *** Goal "1" *** *)
a (all_fc_tac[wo_injection_thm]);
val swo_injection_thm = save_pop_thm "swo_injection_thm";
=TEX
}%ignore


Unwinding the layers of definition we get down to the five primitives: irrefl, antisym, trans, trich, weak mind cond.
However, its convenient not to ignore the strengthening of the minimum condition so this gives a strict min cond instead of weak min cond.
=GFT
⦏swo_clauses⦎ = ⊢ ∀ X $<< f⦁
	StrictWellOrdering (X, $<<) ⇒
		(∀ x⦁ x ∈ X ⇒ ¬ x << x)
             ∧	(((∀ x y⦁ x ∈ X ∧ y ∈ X ∧ ¬ x = y ⇒ ¬ (x << y ∧ y << x))
             ∧	(∀ x y z⦁ x ∈ X ∧ y ∈ X ∧ z ∈ X ∧ x << y ∧ y << z ⇒ x << z))
             ∧	(∀ x y⦁ x ∈ X ∧ y ∈ X ∧ ¬ x = y ⇒ x << y ∨ y << x))
             ∧	(∀ A⦁ A ⊆ X ∧ ¬ A = {}
                 ⇒ (∃ x⦁ x ∈ A ∧ (∀ y⦁ y ∈ A ∧ ¬ y = x ⇒ x << y)))⌝);
=TEX

\ignore{
=SML
set_goal([],⌜∀ X $<<⦁ StrictWellOrdering (X, $<<) ⇒
		(∀ x⦁ x ∈ X ⇒ ¬ x << x)
             ∧	(((∀ x y⦁ x ∈ X ∧ y ∈ X ∧ ¬ x = y ⇒ ¬ (x << y ∧ y << x))
             ∧	(∀ x y z⦁ x ∈ X ∧ y ∈ X ∧ z ∈ X ∧ x << y ∧ y << z ⇒ x << z))
             ∧	(∀ x y⦁ x ∈ X ∧ y ∈ X ∧ ¬ x = y ⇒ x << y ∨ y << x))
             ∧	(∀ A⦁ A ⊆ X ∧ ¬ A = {}
                 ⇒ (∃ x⦁ x ∈ A ∧ (∀ y⦁ y ∈ A ∧ ¬ y = x ⇒ x << y)))⌝);
a (rewrite_tac[strict_well_ordering_def, irrefl_def, well_ordering_def, linear_order_def, weak_min_cond_def, partial_order_def, trich_def, antisym_def, trans_def]);
a (REPEAT_N 4 strip_tac THEN asm_rewrite_tac[]);
a (contr_tac THEN asm_fc_tac[]);
a (spec_nth_asm_tac 3 ⌜x⌝);
a (spec_nth_asm_tac 4 ⌜y⌝);
a (lemma_tac ⌜x ∈ X ∧ y ∈ X⌝ THEN1 (PC_T1 "sets_ext" all_asm_fc_tac[] THEN REPEAT strip_tac));
a (list_spec_nth_asm_tac 13 [⌜y⌝, ⌜x⌝]);
val swo_clauses = save_pop_thm "swo_clauses";
=TEX
}%ignore

\subsection{Initial Strict Well-Orderings}

\ignore{
We have the result that every set can be well-ordered.
There will be many.

There is a partial order over these well-orderings which arises from the fact that each well-prdering corresponds to an ordinal number, and the is therefore a least such ordinal and a corresponding set of well-orderings.
The least ordinal will be an {\it initial} ordinal, and we therefore call the corresponding well-orderings {\it intial well-orderings} and in this section prove that every set has an intial well-ordering.

An initial well-ordering can be obtained in the following way.
First, chose an arbitrary well-ordering of the set.
Then consider the initial segments of that well-ordering which have a cardinality the same as the whole.
Since these are well-ordered we can chose the least of this set, which will correspond to an initial ordinal.
By hypothesis there is a bijection between that intial segment and the whole, using which an initial well-ordering of the whole can be constructed.

The folllowing definition of the property {\it Initial} is intended to make sense only for well-orderings, but is expressed as a property of relations in general.
It corresponds to the notion of intial ordinal only when applied to well-orderings.
}%ignore

The concept of initial ordinal is not straightforward to defined outside the context of a theory of ordinals, but we may use arbitrary well-orderings as surrogates for ordinals and it is useful to have the result that any set has an initial well-ordering, which is then the surrogate for an initial ordinal, before we get into a theory of ordinals.

This can be expressed without explicitly defining the notion of initial ordinal in the following way:

ⓈHOLCONST
│ ⦏InitialStrictWellOrdering⦎ : ('a SET × ('a → 'a → BOOL)) → BOOL
├──────
│ ∀ (X, $<<)⦁ InitialStrictWellOrdering (X, $<<)
│	⇔ StrictWellOrdering(X, $<<) ∧
│	  ¬ ∃f y⦁ y ∈ X ∧ OneOne f ∧ ∀z⦁ z ∈ X ⇒ f z ∈ X ∧ f z << y 
■

We can then prove:

=GFT
⦏initial_strict_well_ordering_thm⦎ =
	⊢ ∀X :'a SET⦁ ∃ $<<⦁ InitialStrictWellOrdering(X, $<<)
=TEX

\ignore{
=SML
val initial_strict_well_ordering_def = get_spec ⌜InitialStrictWellOrdering⌝;

set_goal([], ⌜∀X :'a SET⦁ ∃ $<<⦁ InitialStrictWellOrdering(X, $<<)⌝);
a (strip_tac THEN rewrite_tac[initial_strict_well_ordering_def]);
a (strip_asm_tac strict_well_ordering_thm);
a (spec_asm_tac ⌜∀ X⦁ ∃ $<<⦁ StrictWellOrdering (X, $<<)⌝ ⌜X⌝);
a (cases_tac ⌜(∃ f y⦁ y ∈ X ∧ OneOne f ∧ (∀ z⦁ z ∈ X ⇒ f z ∈ X ∧ f z << y))⌝);
(* *** Goal "1" *** *)
a (lemma_tac ⌜∃ Y⦁ Y = 
  {y | y ∈ X ∧ (∃ f⦁ OneOne f ∧ (∀ z⦁ z ∈ X ⇒ f z ∈ X ∧ f z << y))}⌝
  THEN1 prove_∃_tac);
a (lemma_tac ⌜Y ⊆ X⌝ THEN1 (
  PC_T1 "sets_ext" asm_rewrite_tac[]
  THEN REPEAT strip_tac
  ));
a (lemma_tac ⌜¬ Y = {}⌝ THEN1 (
  PC_T1 "sets_ext" asm_rewrite_tac[]
  THEN REPEAT strip_tac
  THEN (∃_tac ⌜y⌝)
  THEN asm_rewrite_tac[]
  THEN REPEAT strip_tac
  THEN ∃_tac ⌜f⌝
  THEN asm_rewrite_tac[]
  ));
a (lemma_tac ⌜∃ x⦁ x = Minr(X,$<<) Y⌝
  THEN1 prove_∃_tac);
a (all_fc_tac[swo_minr_thm]);
a (POP_ASM_T ante_tac);
a (GET_NTH_ASM_T 4 rewrite_thm_tac THEN strip_tac);
a (lemma_tac ⌜∃ $<<<⦁ $<<< = (λ x y:'a⦁ f' x << f' y)⌝
  THEN prove_∃_tac);
a (∃_tac ⌜$<<<⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (fc_tac[swo_injection_thm]);
a (lemma_tac ⌜∀ x⦁ x ∈ X ⇒ f' x ∈ X⌝
  THEN1 (REPEAT strip_tac THEN asm_fc_tac[]));
a (spec_nth_asm_tac 2 ⌜f'⌝ THEN1 asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a contr_tac;
a (strip_asm_tac(list_∀_elim [⌜X⌝, ⌜$<<⌝, ⌜Y⌝, ⌜x⌝] swo_minr_thm));
a (lemma_tac ⌜f' y' ∈ Y⌝ THEN1 asm_rewrite_tac[]);
(* *** Goal "1.2.1" *** *)
a (spec_nth_asm_tac 7 ⌜y'⌝);
a (lemma_tac ⌜OneOne(f' o f'')⌝ THEN1 all_fc_tac[OneOne_o_thm]);
a (REPEAT strip_tac THEN ∃_tac ⌜f' o f''⌝ THEN asm_rewrite_tac[o_def] THEN REPEAT strip_tac);
(* *** Goal "1.2.1.1" *** *)
a (lemma_tac ⌜f'' z ∈ X⌝ THEN1 all_asm_fc_tac[]);
a (all_asm_fc_tac[]);
(* *** Goal "1.2.1.2" *** *)
a (DROP_ASM_T ⌜∀ z⦁ z ∈ X ⇒ f'' z ∈ X ∧ f'' z <<< y'⌝ ante_tac
  THEN GET_ASM_T ⌜$<<< = (λ x y⦁ f' x << f' y)⌝ rewrite_thm_tac THEN strip_tac);
a (all_asm_fc_tac[]);
(* *** Goal "1.2.2" *** *)
a (spec_nth_asm_tac 2 ⌜f' y'⌝);
(* *** Goal "1.2.2.1" *** *)
a (spec_nth_asm_tac 10 ⌜y'⌝);
a (var_elim_asm_tac ⌜x = f' y'⌝);
(* *** Goal "1.2.2.2" *** *)
a (spec_nth_asm_tac 10 ⌜y'⌝);
a (all_fc_tac [swo_clauses]);
(* *** Goal "2" *** *)
a (∃_tac ⌜$<<⌝ THEN asm_rewrite_tac[]);
val initial_strict_well_ordering_thm = save_pop_thm "initial_strict_well_ordering_thm";
=TEX
}%ignore


Unwinding the layers of definition we get down to the five primitives: irrefl, antisym, trans, trich, weak mind cond.
However, it's convenient not to ignore the strengthening of the minimum condition so this gives a strict min cond instead of weak min cond.
=GFT
⦏iswo_clauses⦎ = ⊢ ∀ X $<< f⦁
	InitialStrictWellOrdering (X, $<<) ⇒
		(∀ x⦁ x ∈ X ⇒ ¬ x << x)
             ∧	(((∀ x y⦁ x ∈ X ∧ y ∈ X ∧ ¬ x = y ⇒ ¬ (x << y ∧ y << x))
             ∧	(∀ x y z⦁ x ∈ X ∧ y ∈ X ∧ z ∈ X ∧ x << y ∧ y << z ⇒ x << z))
             ∧	(∀ x y⦁ x ∈ X ∧ y ∈ X ∧ ¬ x = y ⇒ x << y ∨ y << x))
             ∧	(∀ A⦁ A ⊆ X ∧ ¬ A = {}
                 ⇒ (∃ x⦁ x ∈ A ∧ (∀ y⦁ y ∈ A ∧ ¬ y = x ⇒ x << y)))⌝);
=TEX

\ignore{
=SML
set_goal([],⌜∀ X $<<⦁ InitialStrictWellOrdering (X, $<<) ⇒
		(∀ x⦁ x ∈ X ⇒ ¬ x << x)
             ∧	(((∀ x y⦁ x ∈ X ∧ y ∈ X ∧ ¬ x = y ⇒ ¬ (x << y ∧ y << x))
             ∧	(∀ x y z⦁ x ∈ X ∧ y ∈ X ∧ z ∈ X ∧ x << y ∧ y << z ⇒ x << z))
             ∧	(∀ x y⦁ x ∈ X ∧ y ∈ X ∧ ¬ x = y ⇒ x << y ∨ y << x))
             ∧	(∀ A⦁ A ⊆ X ∧ ¬ A = {}
                 ⇒ (∃ x⦁ x ∈ A ∧ (∀ y⦁ y ∈ A ∧ ¬ y = x ⇒ x << y)))⌝);
a (rewrite_tac[initial_strict_well_ordering_def, strict_well_ordering_def, irrefl_def, well_ordering_def, linear_order_def, weak_min_cond_def, partial_order_def, trich_def, antisym_def, trans_def]);
a (REPEAT_N 4 strip_tac THEN asm_rewrite_tac[]);
a (contr_tac THEN asm_fc_tac[]);
a (spec_nth_asm_tac 3 ⌜x⌝);
a (spec_nth_asm_tac 4 ⌜y⌝);
a (lemma_tac ⌜x ∈ X ∧ y ∈ X⌝ THEN1 (PC_T1 "sets_ext" all_asm_fc_tac[] THEN REPEAT strip_tac));
a (list_spec_nth_asm_tac 14 [⌜y⌝, ⌜x⌝]);
val iswo_clauses = save_pop_thm "iswo_clauses";
=TEX
}%ignore

=GFT
⦏iswo_clauses2⦎ = ⊢ ∀ X $<< f⦁
	InitialStrictWellOrdering (X, $<<) ⇒
		(∀ x⦁ x ∈ X ⇒ ¬ x << x)
             ∧	(((∀ x y⦁ x ∈ X ∧ y ∈ X ∧ ¬ x = y ⇒ ¬ (x << y ∧ y << x))
             ∧	(∀ x y z⦁ x ∈ X ∧ y ∈ X ∧ z ∈ X ∧ x << y ∧ y << z ⇒ x << z))
             ∧	(∀ x y⦁ x ∈ X ∧ y ∈ X ∧ ¬ x = y ⇒ x << y ∨ y << x))
             ∧	(∀ A⦁ A ⊆ X ∧ ¬ A = {}
                 ⇒ (Minr X A ∈ A ∧ (∀ y⦁ y ∈ A ∧ ¬ y = x ⇒ Minr X A << y)))⌝);
=TEX

\ignore{
=SML
set_goal([],⌜∀ X $<< f⦁
	InitialStrictWellOrdering (X, $<<) ⇒
		(∀ x⦁ x ∈ X ⇒ ¬ x << x)
             ∧	(((∀ x y⦁ x ∈ X ∧ y ∈ X ∧ ¬ x = y ⇒ ¬ (x << y ∧ y << x))
             ∧	(∀ x y z⦁ x ∈ X ∧ y ∈ X ∧ z ∈ X ∧ x << y ∧ y << z ⇒ x << z))
             ∧	(∀ x y⦁ x ∈ X ∧ y ∈ X ∧ ¬ x = y ⇒ x << y ∨ y << x))
             ∧	(∀ A⦁ A ⊆ X ∧ ¬ A = {}
                 ⇒ (Minr (X,$<<) A ∈ A ∧ (∀ y⦁ y ∈ A ⇒ y = Minr (X,$<<) A ∨ Minr (X,$<<) A << y)))⌝);
a (REPEAT_N 4 strip_tac
  THEN REPEAT (ufc_tac
       [initial_strict_well_ordering_def,strict_well_ordering_def, irrefl_def,
       well_ordering_def, linear_order_def, weak_min_cond_def, partial_order_def,
       trich_def, antisym_def, trans_def, swo_minr_thm]));
a strip_tac;
(* *** Goal "1" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (strip_tac);
(* *** Goal "2.1" *** *)
a (strip_tac);
(* *** Goal "2.1.1" *** *)
a (strip_tac);
(* *** Goal "2.1.1.1" *** *)
a (contr_tac THEN all_asm_fc_tac[]);
(* *** Goal "2.1.1.2" *** *)
a (contr_tac THEN all_asm_fc_tac[]);
(* *** Goal "2.1.2" *** *)
a (contr_tac THEN all_asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (REPEAT_N 3 strip_tac);
(* *** Goal "2.2.1" *** *)
a (list_spec_nth_asm_tac 16 [⌜Minr (X, $<<) A⌝, ⌜A⌝]);
(* *** Goal "2.2.2" *** *)
a (REPEAT_N 2 strip_tac);
a (list_spec_nth_asm_tac 18 [⌜y⌝, ⌜Minr (X, $<<) A⌝, ⌜A⌝]);
(* *** Goal "2.2.2.1" *** *)
a (POP_ASM_T rewrite_thm_tac);
(* *** Goal "2.2.2.2" *** *)
a (POP_ASM_T rewrite_thm_tac);
val iswo_clauses2 = save_pop_thm "iswo_clauses2";
=TEX
}%ignore

=GFT
⦏ISWO_WellFounded_thm⦎ =
  	⊢ ∀ X $<<⦁ InitialStrictWellOrdering (X, $<<) ⇒ WellFounded (X, $<<)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ X $<<⦁ InitialStrictWellOrdering (X, $<<) ⇒ WellFounded (X, $<<)⌝);
a (REPEAT strip_tac
  THEN fc_tac[initial_strict_well_ordering_def]
  THEN fc_tac[SWO_WellFounded_thm]);
val ISWO_WellFounded_thm = save_pop_thm "ISWO_WellFounded_thm";
=TEX
}%ignore


\subsection{The Minimum Conditions}

In this section we show the equivalence of our definitions with some other useful
conditions. This selection of equivalences is currently just a sample. We could,
for example, come up with induction principles characterising the minimum conditions.

A relation has the minimum condition iff. every descending sequence stabilises:

=GFT
⦏min_cond_descending_sequence_thm⦎ = ⊢ ∀X $<<⦁
		MinCond(X, $<<)
	⇔	∀f⦁ (∀n⦁f n ∈ X) ∧ (∀n⦁f(n+1) << f n)
			⇒ ∃m⦁∀n⦁m < n ⇒ f n = f m
=TEX

\ignore{
=SML
val ⦏min_cond_descending_sequence_thm⦎ = (
set_goal([], ⌜∀X $<<⦁
		MinCond(X, $<<)
	⇔	∀f⦁ (∀n⦁f n ∈ X) ∧ (∀n⦁f(n+1) << f n)
			⇒ ∃m⦁∀n⦁m < n ⇒ f n = f m⌝);
a(rewrite_tac [min_cond_def_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a(lemma_tac⌜{x | ∃n⦁x = f n} ⊆ X⌝ THEN1
	(PC_T1 "sets_ext1" REPEAT strip_tac THEN asm_rewrite_tac[]));
a(lemma_tac⌜¬{x | ∃n⦁x = f n} = {}⌝ THEN1
	(PC_T1 "sets_ext1" REPEAT strip_tac THEN ∃_tac⌜f m⌝ THEN prove_tac[]));
a(all_asm_ufc_tac[]);
a(∃_tac⌜n⌝ THEN ∀_tac);
a(induction_tac⌜n'⌝ THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(lemma_tac ⌜n' = n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_var_elim_asm_tac1);
a(lemma_tac⌜f(n+1) ∈ {x | ∃n⦁x = f n}⌝ THEN1
	(PC_T1 "sets_ext1" REPEAT strip_tac THEN ∃_tac⌜n+1⌝ THEN prove_tac[]));
a(contr_tac);
a(spec_nth_asm_tac 3 ⌜f(m+1)⌝ THEN_TRY (SOLVED_T(asm_prove_tac[])));
(* *** Goal "1.2" *** *)
a(DROP_NTH_ASM_T 4 ante_tac THEN
	GET_NTH_ASM_T 2 (rewrite_thm_tac o eq_sym_rule));
a(REPEAT strip_tac THEN all_var_elim_asm_tac1);
a(lemma_tac⌜f(n'+1) ∈ {x | ∃n⦁x = f n}⌝ THEN1
	(PC_T1 "sets_ext1" REPEAT strip_tac THEN
		∃_tac⌜n'+1⌝ THEN prove_tac[]));
a(contr_tac);
a(spec_nth_asm_tac 5 ⌜f(m+1)⌝ THEN_TRY (SOLVED_T(asm_prove_tac[])));
(* *** Goal "2" *** *)
a(swap_nth_asm_concl_tac 3 THEN REPEAT strip_tac);
a(lemma_tac⌜∃x⦁x ∈ A⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(lemma_tac⌜∃f⦁f 0 = x ∧ ∀m⦁f(m+1) = εy⦁ y ∈ A ∧ ¬y = f m ∧ y << f m⌝
	THEN1 prove_∃_tac);
a(lemma_tac⌜∀m⦁f m ∈ A ∧ ¬f(m+1) = f m ∧ f(m+1) << f m⌝ THEN1 ∀_tac);
(* *** Goal "2.1" *** *)
a(induction_tac⌜m⌝ THEN1 asm_rewrite_tac[]);
(* *** Goal "2.1.1" *** *)
a(ε_tac⌜ε y⦁ y ∈ A ∧ ¬y = x ∧  y << x⌝ THEN contr_tac);
a(spec_nth_asm_tac 5 ⌜x⌝ THEN all_asm_ufc_tac[]);
(* *** Goal "2.1.2" *** *)
a(ε_tac⌜ε y⦁ y ∈ A ∧ ¬y = f m ∧  y << f m⌝ THEN1 contr_tac);
(* *** Goal "2.1.2.1" *** *)
a(spec_nth_asm_tac 8  ⌜f m⌝ THEN all_asm_ufc_tac[]);
(* *** Goal "2.1.2.2" *** *)
a(ε_tac⌜ε y⦁ y ∈ A ∧ ¬y = f (m+1) ∧  y << f (m+1)⌝);
(* *** Goal "2.1.2.2.1" *** *)
a(asm_rewrite_tac[]);
a(spec_nth_asm_tac 10 ⌜ε y⦁ y ∈ A ∧ ¬y = f m ∧  y << f m⌝
	THEN  contr_tac THEN all_asm_ufc_tac[]);
(* *** Goal "2.1.2.2.2" *** *)
a(once_asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.1.2.2.2.1" *** *)
a(DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2.2.2.2" *** *)
a(POP_ASM_T ante_tac THEN
	spec_nth_asm_tac 12 ⌜ε y⦁ y ∈ A ∧ ¬y = f (m+1) ∧ y << f (m+1)⌝ );
a(asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(DROP_NTH_ASM_T 2 discard_tac THEN ∃_tac⌜f⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a(LEMMA_T ⌜f n ∈  A⌝ ante_tac THEN1 asm_rewrite_tac[]);
a(GET_NTH_ASM_T 6 ante_tac THEN PC_T1 "sets_ext1" prove_tac[]);
(* *** Goal "2.2.2" *** *)
a(asm_rewrite_tac[]);
(* *** Goal "2.2.3" *** *)
a(∃_tac⌜m+1⌝ THEN asm_rewrite_tac[]);
save_pop_thm "min_cond_descending_sequence_thm"
);
=TEX
}%ignore

A relation is a reflexive well-ordering iff. every non-empty subset has a unique lower bound:

=GFT
⦏refl_well_ordering_lower_bounds_thm⦎ = ⊢ ∀X $<<⦁
		Refl(X, $<<)
	∧	WellOrdering(X, $<<)
	⇔	∀A⦁A ⊆ X ∧ ¬A = {} ⇒ ∃⋎1 x⦁ x ∈ A ∧ ∀y⦁y ∈ A ⇒ x << y
=TEX

\ignore{
=SML
val ⦏refl_well_ordering_lower_bounds_thm⦎ = (
set_goal([], ⌜∀X $<<⦁
		Refl(X, $<<)
	∧	WellOrdering(X, $<<)
	⇔	∀A⦁A ⊆ X ∧ ¬A = {} ⇒ ∃⋎1 x⦁ x ∈ A ∧ ∀y⦁y ∈ A ⇒ x << y⌝);
a(REPEAT_UNTIL is_⇒ strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac def_thms  THEN REPEAT strip_tac THEN all_asm_ufc_tac[]);
a(∃⋎1_tac ⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a(lemma_tac⌜x ∈ X⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(cases_tac ⌜y = x⌝  THEN1 (all_var_elim_asm_tac THEN all_asm_ufc_tac[]));
a(LIST_GET_NTH_ASM_T[4] all_ufc_tac);
a(lemma_tac⌜x << y ∨ y << x⌝);
a(GET_NTH_ASM_T 10 bc_thm_tac);
a(lemma_tac⌜y ∈ X⌝ THEN1
	(LIST_GET_NTH_ASM_T [4, 8] (MAP_EVERY ante_tac) THEN
		PC_T1 "sets_ext1" prove_tac[]));
a(contr_tac THEN all_var_elim_asm_tac);
(* *** Goal "1.2" *** *)
a(contr_tac THEN all_asm_ufc_tac[]);
(* *** Goal "2" *** *)
a(⇒_tac THEN rewrite_tac[well_ordering_def_thm, linear_order_def, partial_order_def]);
a(rewrite_tac[taut_rule⌜∀p1 p2 p3 p4 p5⦁
	p1 ∧ ((p2 ∧ p3) ∧ p4) ∧ p5 ⇔
	p1 ∧ (p1 ⇒ p2) ∧ (p1 ∧ p2 ⇒ p4) ∧
	(p1 ∧ p2 ∧ p4 ⇒ p3) ∧ (p1 ∧ p2 ∧ p3 ∧ p4 ⇒ p5)⌝]);
a(rewrite_tac def_thms THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *) (* Reflexivity *)
a(lemma_tac⌜{x} ⊆ X ∧ ¬{x} = {}⌝ THEN1 PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_asm_ufc_tac[] THEN all_var_elim_asm_tac);
a(GET_NTH_ASM_T 2 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *) (* Antisymmetry *)
a(swap_nth_asm_concl_tac 2);
a(lemma_tac⌜{x; y} ⊆ X ∧ ¬{x; y} = {}⌝ THEN1
	PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_asm_ufc_tac[] THEN all_var_elim_asm_tac);
(* *** Goal "2.2.1" *** *)
a(conv_tac eq_sym_conv THEN GET_NTH_ASM_T 3 bc_thm_tac);
a(REPEAT strip_tac THEN all_var_elim_asm_tac);
(* *** Goal "2.2.2" *** *)
a(GET_NTH_ASM_T 3 bc_thm_tac);
a(REPEAT strip_tac THEN all_var_elim_asm_tac);
(* *** Goal "2.3" *** *) (* Trichotomy *)
a(lemma_tac⌜{x; y} ⊆ X ∧ ¬{x; y} = {}⌝ THEN1
	PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_asm_ufc_tac[] THEN all_var_elim_asm_tac);
(* *** Goal "2.3.1" *** *)
a(swap_nth_asm_concl_tac 7);
a(GET_NTH_ASM_T 5 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2.3.2" *** *)
a(GET_NTH_ASM_T 4 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2.4" *** *) (* Transitivity *)
a(lemma_tac⌜{x; y; z} ⊆ X ∧ ¬{x; y; z} = {}⌝ THEN1
	PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_asm_ufc_tac[] THEN all_var_elim_asm_tac);
(* *** Goal "2.4.1" *** *)
a(GET_NTH_ASM_T 5 bc_thm_tac THEN REPEAT strip_tac);
(* *** Goal "2.4.2" *** *)
a(lemma_tac ⌜y << x⌝ THEN1
	(GET_NTH_ASM_T 5 bc_thm_tac THEN REPEAT strip_tac));
a(cases_tac ⌜y = x⌝ THEN1 all_var_elim_asm_tac);
a(rename_tac[] THEN all_asm_ufc_tac[]);
(* *** Goal "2.4.3" *** *)
a(lemma_tac ⌜z << y⌝ THEN1
	(GET_NTH_ASM_T 5 bc_thm_tac THEN REPEAT strip_tac));
a(cases_tac ⌜y = z⌝ THEN1 all_var_elim_asm_tac);
a(rename_tac[] THEN all_asm_ufc_tac[]);
(* *** Goal "2.5" *** *) (* Minimum condition *)
a(all_asm_ufc_tac[]);
a(∃_tac⌜x⌝ THEN REPEAT strip_tac);
a(swap_nth_asm_concl_tac 1);
a(GET_NTH_ASM_T 3 bc_thm_tac THEN REPEAT strip_tac);
a(lemma_tac⌜x << y'⌝ THEN1
	(GET_NTH_ASM_T 5 bc_thm_tac THEN REPEAT strip_tac));
a(lemma_tac⌜x ∈ X ∧ y ∈ X ∧ y' ∈ X⌝ THEN1 
	(LIST_GET_NTH_ASM_T [2, 4, 7, 9]
		(MAP_EVERY ante_tac)THEN PC_T1 "sets_ext1" prove_tac[]));
a(rename_tac[] THEN LIST_GET_NTH_ASM_T [14] all_ufc_tac);
save_pop_thm "refl_well_ordering_lower_bounds_thm"
);
=TEX
}%ignore


A relation is well-founded iff. there are no infinite descending sequences:

=GFT
⦏well_founded_descending_sequence_thm⦎ = ⊢ ∀X $<<⦁
		WellFounded(X, $<<)
	⇔	¬∃f⦁ (∀n⦁f n ∈ X) ∧ (∀n⦁f(n+1) << f n)
=TEX

\ignore{
=SML
val ⦏well_founded_descending_sequence_thm⦎ = (
set_goal([], ⌜∀X $<<⦁
		WellFounded(X, $<<)
	⇔	¬∃f⦁ (∀n⦁f n ∈ X) ∧ (∀n⦁f(n+1) << f n)⌝);
a(REPEAT_UNTIL is_⇒ strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac [well_founded_def, irrefl_def] THEN contr_tac);
a(all_ufc_tac[min_cond_descending_sequence_thm]);
a(lemma_tac⌜f(m+1) = f m⌝ THEN1
	(POP_ASM_T bc_thm_tac THEN REPEAT strip_tac));
a(lemma_tac⌜f m∈ X ∧ f(m+1) << f m⌝ THEN1 asm_rewrite_tac[]);
a(POP_ASM_T ante_tac THEN GET_NTH_ASM_T 2 rewrite_thm_tac);
a(all_asm_ufc_tac[]);
(* *** Goal "2" *** *)
a(rewrite_tac[well_founded_def] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a(rewrite_tac[irrefl_def] THEN contr_tac);
a(swap_nth_asm_concl_tac 3 THEN REPEAT strip_tac);
a(∃_tac⌜λm:ℕ⦁x⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(POP_ASM_T ante_tac THEN rewrite_tac
	[min_cond_descending_sequence_thm]);
a(REPEAT strip_tac);
a(swap_nth_asm_concl_tac 3 THEN REPEAT strip_tac);
a(∃_tac⌜f⌝ THEN asm_rewrite_tac[]);
save_pop_thm "well_founded_descending_sequence_thm"
);
=TEX
}%ignore

A relation is well-founded iff. it enjoys the Noetherian(?) induction principle:

=GFT
⦏well_founded_induction_thm⦎ = ⊢ ∀X $<<⦁
		WellFounded(X, $<<)
	⇔	∀p⦁ (∀x⦁x ∈ X ∧ (∀y⦁y ∈ X ∧ y << x ⇒ p y) ⇒ p x)
			⇒ (∀x⦁x ∈ X ⇒ p x)
⦏ISWO_Induction_thm⦎ = ⊢ ∀ X $<<⦁
	InitialStrictWellOrdering (X, $<<) ⇒
		∀p⦁ (∀x⦁x ∈ X ∧ (∀y⦁y ∈ X ∧ y << x ⇒ p y) ⇒ p x)
		    ⇒ (∀x⦁x ∈ X ⇒ p x)
=TEX

\ignore{
=SML
val ⦏well_founded_induction_thm⦎ = (
set_goal([], ⌜∀X $<<⦁
		WellFounded(X, $<<)
	⇔	∀p⦁ (∀x⦁x ∈ X ∧ (∀y⦁y ∈ X ∧ y << x ⇒ p y) ⇒ p x)
			⇒ (∀x⦁x ∈ X ⇒ p x)⌝);
a(REPEAT_UNTIL is_⇒ strip_tac);
(* *** Goal "1" *** *)
a(rewrite_tac [well_founded_def, min_cond_def_thm, irrefl_def] THEN contr_tac);
a(lemma_tac ⌜{x | x ∈ X ∧ ¬p x} ⊆ X⌝ THEN1
	PC_T1 "sets_ext1"prove_tac[]);
a(lemma_tac ⌜¬{x | x ∈ X ∧ ¬p x} = {}⌝ THEN1
	PC_T1 "sets_ext1" asm_prove_tac[]);
a(all_asm_ufc_tac[]);
a(lemma_tac⌜∀ y⦁ y ∈ X ∧ y << x' ⇒ p y⌝ THEN contr_tac);
(* *** Goal "1.1" *** *)
a(cases_tac⌜y = x'⌝ THEN1 (all_var_elim_asm_tac THEN asm_prove_tac[]));
a(all_asm_ufc_tac[]);
(* *** Goal "1.2" *** *)
a(all_asm_ufc_tac[]);
(* *** Goal "2" *** *)
a( rewrite_tac[well_founded_descending_sequence_thm] THEN contr_tac);
a(LEMMA_T ⌜∀x⦁
	x ∈ X
⇒	(λa⦁	 a ∈ X
	∧	∀g⦁ g 0 = a
	∧	(∀y ⦁g y ∈ X)
	⇒	∃m⦁¬g(m+1)  << g m)
	x
⌝ ante_tac);
(* *** Goal "2.1" *** *)
a(DROP_NTH_ASM_T 3 bc_thm_tac);
a(rewrite_tac[] THEN contr_tac);
a(SPEC_NTH_ASM_T 1 ⌜0⌝ (strip_asm_tac o rewrite_rule[]));
a(DROP_NTH_ASM_T 5 (ante_tac o ∀_elim⌜g 1⌝) THEN 
	all_var_elim_asm_tac1 THEN asm_rewrite_tac[] THEN strip_tac);
a(∃_tac⌜λm⦁g(m+1)⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a(rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜f 0⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜f⌝ THEN asm_rewrite_tac[]);
save_pop_thm "well_founded_induction_thm"
);

set_goal([], ⌜∀ X $<<⦁
	InitialStrictWellOrdering (X, $<<) ⇒
		∀p⦁ (∀x⦁x ∈ X ∧ (∀y⦁y ∈ X ∧ y << x ⇒ p y) ⇒ p x)
		    ⇒ (∀x⦁x ∈ X ⇒ p x)⌝);
a (REPEAT_N 3 strip_tac THEN fc_tac [initial_strict_well_ordering_def]);
a (fc_tac [SWO_WellFounded_thm]);
a (fc_tac [well_founded_induction_thm]);
a (REPEAT strip_tac THEN all_asm_fc_tac[]);
val ISWO_Induction_thm = save_pop_thm "ISWO_Induction_thm";
=TEX
}%ignore
\section{TRANSITIVE CLOSURE}

First the definition:

ⓈHOLCONST
│ ⦏TranClsr⦎ : ('a SET × ('a → 'a → BOOL)) → ('a SET × ('a → 'a → BOOL))
├──────
│ ∀ (X, $<<)⦁ TranClsr (X, $<<) = (X, λx y⦁ 
│	∀r⦁ (Trans (X, r) ∧ ∀v w⦁ v ∈ X ∧ w ∈ X ∧ v << w ⇒ r v w) ⇒ r x y)
■

ⓈHOLCONST
│ ⦏RefTranClsr⦎ : ('a SET × ('a → 'a → BOOL)) → ('a SET × ('a → 'a → BOOL))
├──────
│ ∀ (X, $<<)⦁ RefTranClsr (X, $<<) = (X, λx y⦁
│	x = y ∨ Snd (TranClsr (X, $<<)) x y)
■

The following elementary facts about transitive closure prove useful:

=GFT
⦏trans_tc_thm⦎ = 	⊢ ∀ X $<<⦁ Trans (TranClsr (X, $<<))

⦏trans_tc_thm2⦎ = 	⊢ ∀ X $<< x y z⦁ x ∈ X ∧ y ∈ X ∧ z ∈ X
	∧ Snd(TranClsr (X, $<<)) x y
	∧ Snd(TranClsr (X, $<<)) y z
	⇒ Snd(TranClsr (X, $<<)) x z

⦏tc_incr_thm2⦎ =	⊢ ∀ X $<< x y⦁ x ∈ X ∧ y ∈ X
	∧ x << y
	⇒ Snd(TranClsr (X, $<<)) x y

⦏tc_decompose_thm⦎ =	⊢ ∀ X $<< x y⦁ x ∈ X ∧ y ∈ X
	∧ Snd (TranClsr (X, $<<)) x y
	∧ ¬ x << y
	⇒ ∃z⦁ z ∈ X
	∧ Snd (TranClsr (X, $<<)) x z
	∧ z << y

⦏tc_mono_thm⦎ = ⊢ ∀ (X, r1) (X, r2)⦁
	  (∀ x y⦁ x ∈ X ∧ y ∈ X
           ∧ r1 x y 
	  ⇒ r2 x y)
	⇒ (∀ x y⦁ x ∈ X ∧ y ∈ X
	  ∧ Snd (TranClsr (X, r1)) x y
	  ⇒ Snd (TranClsr (X, r2)) x y)
=TEX

\ignore{
=SML
val tran_clsr_def = get_spec ⌜TranClsr⌝;
val ref_tran_clsr_def = get_spec ⌜RefTranClsr⌝;

=SML
set_goal ([], ⌜∀ X $<<⦁ Trans (TranClsr (X, $<<))⌝);
a (rewrite_tac [tran_clsr_def, trans_def]
	THEN REPEAT strip_tac
	THEN REPEAT (all_asm_ufc_tac[]));
val trans_tc_thm = save_pop_thm "trans_tc_thm";
=TEX

=SML
set_goal ([], ⌜∀ X $<<⦁ Fst (TranClsr (X, $<<)) = X⌝);
a (rewrite_tac [tran_clsr_def]
	THEN REPEAT strip_tac);
val fst_tc_lemma = save_pop_thm "fst_tc_lemma";
=TEX

=SML
set_goal ([], ⌜∀ r⦁ TranClsr r = (Fst r, λx y⦁ 
	∀s⦁ (Trans (Fst r, s) ∧ ∀v w⦁ v ∈ Fst r ∧ w ∈ Fst r ∧ Snd r v w ⇒ s v w) ⇒ s x y)⌝);
a (strip_tac
	THEN once_rewrite_tac [prove_rule [] ⌜r = (Fst r, Snd r)⌝]
	THEN pure_rewrite_tac [tran_clsr_def]
	THEN rewrite_tac [ext_thm]);
val tran_clsr_thm = save_pop_thm "tran_clsr_thm";
=TEX

=SML
set_goal ([], ⌜∀ X $<< x y z⦁ x ∈ X ∧ y ∈ X ∧ z ∈ X
	∧ Snd(TranClsr (X, $<<)) x y ∧ Snd(TranClsr (X, $<<)) y z ⇒ Snd(TranClsr (X, $<<)) x z⌝);
a (rewrite_tac [tran_clsr_thm]
	THEN REPEAT strip_tac
	THEN all_asm_ufc_tac []
	THEN all_ufc_tac [trans_def]);
val trans_tc_thm2 = save_pop_thm "trans_tc_thm2";
=TEX

=SML
set_goal([], ⌜∀ X $<< x y⦁ x ∈ X ∧ y ∈ X
	∧ x << y ⇒ Snd(TranClsr (X, $<<)) x y⌝);
a (rewrite_tac [tran_clsr_def]
	THEN REPEAT strip_tac
	THEN REPEAT (asm_ufc_tac[]));
val tc_incr_thm2 = save_pop_thm "tc_incr_thm2";
=TEX

=SML
set_goal([],⌜∀ X $<< x y⦁ x ∈ X ∧ y ∈ X ∧ Snd (TranClsr (X, $<<)) x y ∧ ¬ x << y ⇒
	∃z⦁ z ∈ X ∧ Snd (TranClsr (X, $<<)) x z ∧ z << y⌝);
a (REPEAT strip_tac);
a (GET_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [tran_clsr_thm])));
a (lemma_tac ⌜∃r⦁ r = λv w⦁ v << w ∨ ∃u⦁ u ∈ X ∧ Snd (TranClsr (X, $<<)) v u ∧ u << w⌝
	THEN1 prove_∃_tac);
a (lemma_tac ⌜Trans (X, r)⌝);
(* *** Goal "1" *** *)
a (rewrite_tac[trans_def]
		THEN REPEAT ∀_tac
		THEN asm_rewrite_tac[]
		THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (∃_tac ⌜y'⌝ THEN asm_rewrite_tac[]);
a (rewrite_tac [tran_clsr_def]
	THEN REPEAT strip_tac);
a (all_asm_ufc_tac[]);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜u⌝ THEN asm_rewrite_tac[]);
a (all_ufc_tac [tc_incr_thm2]);
a (all_ufc_tac [trans_tc_thm2]);
(* *** Goal "1.3" *** *)
a (∃_tac ⌜y'⌝ THEN asm_rewrite_tac[]);
a (all_ufc_tac [tc_incr_thm2]);
a (all_ufc_tac [trans_tc_thm2]);
(* *** Goal "1.4" *** *)
a (∃_tac ⌜u'⌝ THEN asm_rewrite_tac[]);
a (all_ufc_tac [tc_incr_thm2]);
a (all_ufc_tac [trans_tc_thm2]);
a (all_ufc_tac [trans_tc_thm2]);
(* *** Goal "2" *** *)
a (asm_ufc_tac[]);
(* *** Goal "2.1" *** *)
a (swap_nth_asm_concl_tac 1
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
val tc_decompose_thm = save_pop_thm "tc_decompose_thm";
=TEX

=SML
set_goal([],⌜∀ (X, r1) (X, r2)⦁
	(∀ x y⦁ x ∈ X ∧ y ∈ X ∧ r1 x y ⇒ r2 x y)
	⇒ (∀ x y⦁ x ∈ X ∧ y ∈ X ∧ Snd (TranClsr (X, r1)) x y ⇒ Snd (TranClsr (X, r2)) x y)⌝);
a (rewrite_tac [tran_clsr_def]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜∀ v w⦁ v ∈ X ∧ w ∈ X ∧ r1 v w ⇒ r v w⌝
	THEN1 REPEAT strip_tac
	THEN REPEAT (all_asm_ufc_tac[]));
val tc_mono_thm = save_pop_thm "tc_mono_thm";

set_goal([], ⌜∀(X,$<<) x y⦁ Snd (TranClsr (X, $<<)) x y ⇒ x ∈ X ∧ y ∈ X⌝);
a (REPEAT ∀_tac);
a (split_pair_rewrite_tac [⌜(X, $<<)⌝] [tran_clsr_def]
	THEN rewrite_tac []
	THEN REPEAT ∀_tac THEN strip_tac);
a (SPEC_NTH_ASM_T 1 ⌜λx y⦁ x ∈ X ∧ y ∈ X ∧ Snd (TranClsr (X, $<<)) x y⌝
	(strip_asm_tac o (rewrite_rule[])));
(* *** Goal "1" *** *)
a (CONTR_T discard_tac THEN POP_ASM_T ante_tac
	THEN rewrite_tac[trans_def]
	THEN REPEAT strip_tac);
a (all_asm_ufc_tac [trans_tc_thm2]);
(* *** Goal "2" *** *)
a (CONTR_T discard_tac
	THEN POP_ASM_T ante_tac
	THEN rewrite_tac[tran_clsr_def]
	THEN REPEAT strip_tac
	THEN all_asm_ufc_tac []);
(* *** Goal "3" *** *)
a (asm_rewrite_tac[]);
val tran_clsr_lemma1 = save_pop_thm "tran_clsr_lemma1"; 
=TEX
}%ignore

When reasoning using well-founded induction a primitive induction principle can be converted into ``course of values'' induction by using the theorem which states that a relation is well-founded iff its transitive closure is well-founded.

In preparation for proving this theorem it is convenient to have a more general notion of inclusion of relations than that of section \ref{Lemmas about Subsets of Ordered Sets}.
This is helpful because a relation is a subrelation of its transitive closure, not a restriction of it to a smaller field.
This suffices to establish that it is well founded if its transitive closure is.
One might as well get it via the general result that subrelations of well-founded relation is well-founded, but it can't be done using a subrel theorem of the kind presented in section \ref{Lemmas about Subsets of Ordered Sets} earlier.

=SML
declare_infix (300, "⊆⋎r");
=TEX

ⓈHOLCONST
│ ⦏$⊆⋎r⦎: ('a SET × ('a → 'a → BOOL)) → ('a SET × ('a → 'a → BOOL)) → BOOL
├──────
│ ∀ (X, r1) (Y, r2)⦁ (X, r1) ⊆⋎r (Y, r2) ⇔
│	∀ x y⦁ x ∈ X ∧ y ∈ X ∧ r1 x y
│	⇒ x ∈ Y ∧ y ∈ Y ∧ r2 x y
■

Allowing us to state concisely (and prove) that a relation is contained in its transitive closure:

=GFT
⦏r_⊆⋎r_tcr_thm⦎ =	⊢ ∀r⦁ r ⊆⋎r TranClsr r
=TEX

And that various properties of relations also hold of their subrelations:

=GFT
⦏subrel_irrefl_thm2⦎ =		⊢ ∀r s⦁ s ⊆⋎r r ∧ Irrefl r ⇒ Irrefl s
⦏subrel_antisym_thm2⦎ =		⊢ ∀r s⦁ s ⊆⋎r r ∧ Antisym r ⇒ Antisym s
⦏subrel_min_cond_thm2⦎ =		⊢ ∀r s⦁ s ⊆⋎r r ∧ MinCond r ⇒ MinCond s
⦏subrel_well_founded_thm2⦎ =	⊢ ∀r s⦁ s ⊆⋎r r ∧ WellFounded r ⇒ WellFounded s
=TEX

\ignore{
=SML
val ⊆r_def = get_spec ⌜$⊆⋎r⌝;
set_goal([], ⌜∀ r1 r2⦁ r1 ⊆⋎r r2 ⇔
	∀ x y⦁ x ∈ Fst r1 ∧ y ∈ Fst r1 ∧ Snd r1 x y
	⇒ x ∈ Fst r2 ∧ y ∈ Fst r2 ∧ Snd r2 x y⌝);
a (REPEAT ∀_tac
	THEN pure_once_rewrite_tac (map (prove_rule [])
		[⌜r1 = (Fst r1, Snd r1)⌝,
		 ⌜r2 = (Fst r2, Snd r2)⌝])
	THEN pure_rewrite_tac [⊆r_def]
	THEN rewrite_tac[]
	THEN REPEAT strip_tac);
val ⊆r_thm = save_pop_thm "⊆r_thm";

set_goal ([], ⌜∀r⦁ r ⊆⋎r TranClsr r⌝);
a (rewrite_tac [⊆r_thm, tran_clsr_thm]
	THEN REPEAT strip_tac
	THEN all_asm_ufc_tac[]);
val r_⊆_tcr_thm = save_pop_thm "r_⊆_tcr_thm";
=TEX

=SML
set_goal ([], ⌜∀r s⦁ s ⊆⋎r r ∧ Irrefl r ⇒ Irrefl s⌝);
a (REPEAT ∀_tac
	THEN split_pair_rewrite_tac [⌜r⌝, ⌜s⌝] [irrefl_def, ⊆r_def]
	THEN contr_tac
	THEN REPEAT (all_asm_ufc_tac[]));
val subrel_irrefl_thm2 = save_pop_thm "subrel_irrefl_thm2";

set_goal ([], ⌜∀r s⦁ s ⊆⋎r r ∧ Antisym r ⇒ Antisym s⌝);
a (REPEAT ∀_tac
	THEN split_pair_rewrite_tac [⌜r⌝, ⌜s⌝] [antisym_def, ⊆r_def]
	THEN contr_tac);
a (list_spec_nth_asm_tac 7 [⌜x⌝, ⌜y⌝]);
a (list_spec_nth_asm_tac 10 [⌜y⌝, ⌜x⌝]);
a (list_spec_nth_asm_tac 10 [⌜x⌝, ⌜y⌝]);
val subrel_antisym_thm2 = save_pop_thm "subrel_antisym_thm2";
=TEX

=SML
set_goal ([], ⌜∀r s⦁ s ⊆⋎r r ∧ MinCond r ⇒ MinCond s⌝);
a (REPEAT ∀_tac
	THEN split_pair_rewrite_tac [⌜r⌝, ⌜s⌝] [min_cond_def, weak_min_cond_def]
	THEN REPEAT strip_tac
	THEN all_ufc_tac [subrel_antisym_thm2]);
a (DROP_NTH_ASM_T 6 (fn x => strip_asm_tac (rewrite_rule [⊆r_def] x)));
a (DROP_NTH_ASM_T 3 ante_tac
	THEN rewrite_tac [sets_ext_clauses]
	THEN contr_tac);
a (spec_nth_asm_tac 6 ⌜A ∩ (Fst r)⌝);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac
	THEN rewrite_tac [sets_ext_clauses, ∈_in_clauses]
	THEN contr_tac);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜x⌝);
a (lemma_tac ⌜x ∈ Fst s ∧ y ∈ Fst s⌝
	THEN1 (strip_tac THEN GET_NTH_ASM_T 10
	(fn x => (all_ufc_tac [rewrite_rule [sets_ext_clauses] x]))));
a (lemma_tac ⌜¬ x ∈ Fst r⌝
	THEN1 (GET_NTH_ASM_T 7
	(fn x => ((strip_asm_tac o (∀_elim ⌜x⌝))
	       (rewrite_rule [sets_ext_clauses, ∈_in_clauses] x)))));
a (list_spec_nth_asm_tac 11 [⌜y⌝, ⌜x⌝]);
(* *** Goal "3" *** *)
a (spec_nth_asm_tac 4 ⌜x'⌝);
a (lemma_tac ⌜x' ∈ Fst s ∧ y ∈ Fst s⌝
	THEN1 (strip_tac THEN GET_NTH_ASM_T 12
	(fn x => (all_ufc_tac [rewrite_rule [sets_ext_clauses] x]))));
a (list_spec_nth_asm_tac 12 [⌜y⌝, ⌜x'⌝]);
a (spec_nth_asm_tac 9 ⌜y⌝);
a (DROP_NTH_ASM_T 19 ante_tac
	THEN rewrite_tac [antisym_def]
	THEN contr_tac);
a (list_spec_nth_asm_tac 1 [⌜y⌝, ⌜x'⌝]);
val subrel_min_cond_thm2 = save_pop_thm "subrel_min_cond_thm2";
=TEX

=SML
set_goal ([], ⌜∀r s⦁ s ⊆⋎r r ∧ WellFounded r ⇒ WellFounded s⌝);
a (REPEAT ∀_tac
	THEN split_pair_rewrite_tac [⌜r⌝, ⌜s⌝] [well_founded_def]
	THEN REPEAT strip_tac
	THEN all_asm_ufc_tac [subrel_irrefl_thm2, subrel_min_cond_thm2]);
val subrel_well_founded_thm2 = save_pop_thm "subrel_well_founded_thm2";
=TEX

}%ignore

A relation is well-founded iff its transitive closure is well-founded.

In the right to left direction the result follows from the fact that a relation is a subrelation of its transitive closure and that a subrelation of a well-founded relation is well-founded.
In the left to right direction the proof involves showing by well-founded induction that there is no descending sequence in the transitive closure.

=GFT
⦏wf_iff_wftc_thm⦎ =	⊢ ∀ X $<<⦁
	WellFounded (X, $<<) ⇔ WellFounded (TranClsr (X, $<<))
=TEX

\ignore{
=SML
set_goal ([], ⌜∀ X $<<⦁ WellFounded (X, $<<) ⇒ WellFounded (TranClsr (X, $<<))⌝);
a (REPEAT strip_tac);
a (GET_NTH_ASM_T 1 (fn x => asm_tac (rewrite_rule [well_founded_induction_thm] x)));
a (spec_nth_asm_tac 1 ⌜λv⦁ v ∈ X ⇒ ¬ (∃ f⦁
	  (∀ n⦁ f n ∈ X ∧ Snd (TranClsr (X, $<<)) (f n) v)
	∧ (∀ n⦁ Snd (TranClsr (X, $<<)) (f (n + 1)) (f n)))⌝);
(* *** Goal "1" *** *)
a (CONTR_T discard_tac THEN POP_ASM_T (strip_asm_tac o (rewrite_rule[])));
a (spec_nth_asm_tac 2 ⌜0⌝);
a (lemma_tac ⌜∀n⦁ Snd (TranClsr (X, $<<)) (f (n + 1)) (f 0)⌝
	THEN1 strip_tac);
(* *** Goal "1.1" *** *)
a (induction_tac ⌜n⌝);
(* *** Goal "1.1.1" *** *)
a (SPEC_NTH_ASM_T 3 ⌜0⌝ rewrite_thm_tac);
(* *** Goal "1.1.2" *** *)
a (spec_nth_asm_tac 4 ⌜n + 1⌝);
a (lemma_tac ⌜f (n+1) ∈ X ∧ f ((n + 1) + 1) ∈ X⌝
	THEN1 (asm_rewrite_tac []));
a (all_ufc_tac [trans_tc_thm2]);
(* *** Goal "1.2" *** *)
a (cases_tac ⌜f 0 << x⌝); 
(* *** Goal "1.2.1" *** *)
a (SPEC_NTH_ASM_T 7 ⌜f 0⌝ (strip_asm_tac o (rewrite_rule[])));
a (SPEC_NTH_ASM_T 1 ⌜λn⦁ f (n+1)⌝ (strip_asm_tac o (rewrite_rule[])));
(* *** Goal "1.2.1.1" *** *)
a (spec_nth_asm_tac 8 ⌜n+1⌝);
(* *** Goal "1.2.1.2" *** *)
a (spec_nth_asm_tac 4 ⌜n⌝);
(* *** Goal "1.2.1.3" *** *)
a (spec_nth_asm_tac 7 ⌜n+1⌝);
(* *** Goal "1.2.2" *** *)
a (all_ufc_tac [tc_decompose_thm]);
a (SPEC_NTH_ASM_T 10 ⌜z⌝ (strip_asm_tac o (rewrite_rule[])));
a (spec_nth_asm_tac 1 ⌜f⌝);
(* *** Goal "1.2.2.1" *** *)
a (spec_nth_asm_tac 11 ⌜n⌝);
(* *** Goal "1.2.2.2" *** *)
a (POP_ASM_T ante_tac
	THEN strip_asm_tac (∀_elim ⌜n⌝ ℕ_cases_thm)
	THEN asm_rewrite_tac[]);
a (spec_nth_asm_tac 7 ⌜i⌝
	THEN spec_nth_asm_tac 12 ⌜i+1⌝
	THEN all_ufc_tac [trans_tc_thm2]);
(* *** Goal "1.2.2.3" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (split_pair_rewrite_tac [⌜TranClsr (X, $<<)⌝] [well_founded_descending_sequence_thm]);
a (contr_tac);
a (lemma_tac ⌜∀n⦁ f n ∈ X⌝
	THEN1 (GET_NTH_ASM_T 2 ante_tac
		THEN rewrite_tac [tran_clsr_def]
		THEN strip_tac));
a (spec_nth_asm_tac 1 ⌜0⌝);
a (SPEC_NTH_ASM_T 5 ⌜f 0⌝ (strip_asm_tac o (rewrite_rule[])));
a (spec_nth_asm_tac 1 ⌜λn⦁ f (n+1)⌝);
(* *** Goal "2.1" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac[]);
a (induction_tac ⌜n⌝ THEN TRY (asm_rewrite_tac[]));
a (lemma_tac ⌜f (n + 1) ∈ X ∧ f ((n + 1) + 1) ∈ X⌝ THEN1 asm_rewrite_tac []);
a (spec_nth_asm_tac 7 ⌜n+1⌝ THEN all_ufc_tac [trans_tc_thm2]);
(* *** Goal "2.3" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac[]);
a (spec_nth_asm_tac 4 ⌜n + 1⌝);
val wf_wftc_lemma = pop_thm ();
=TEX

=SML
set_goal([], ⌜∀ X $<< x y⦁ WellFounded (X, $<<) ∧ x ∈ X ⇒ ¬ Snd (TranClsr (X, $<<)) x x⌝);
a (contr_tac);
a (ALL_FC_T (MAP_EVERY ante_tac) [wf_wftc_lemma]);
a (split_pair_rewrite_tac [⌜TranClsr (X, $<<)⌝] [well_founded_descending_sequence_thm]
	THEN REPEAT strip_tac);
a (SPEC_NTH_ASM_T 1 ⌜λn:ℕ⦁x⌝ ante_tac
	THEN rewrite_tac [] THEN REPEAT strip_tac);
a (asm_rewrite_tac [tran_clsr_def]);
val tcwf_not_refl_thm = save_pop_thm "tcwf_not_refl_thm";
=TEX

=SML
set_goal ([], ⌜∀r⦁ WellFounded r ⇒ WellFounded (TranClsr r)⌝);
a (split_pair_rewrite_tac [⌜r⌝] [wf_wftc_lemma] THEN REPEAT strip_tac);
val wf_wftc_thm = save_pop_thm "wf_wftc_thm";
=TEX

=SML
set_goal ([], ⌜∀r⦁ WellFounded (TranClsr r) ⇒ WellFounded r⌝);
a (REPEAT strip_tac);
a (asm_tac (all_∀_elim r_⊆_tcr_thm)
	THEN all_ufc_tac [subrel_well_founded_thm2]);
val wftc_wf_thm = save_pop_thm "wftc_wf_thm";
=TEX

=SML
set_goal ([], ⌜∀r⦁ WellFounded r ⇔ WellFounded (TranClsr r)⌝);
a (REPEAT strip_tac
	THEN all_ufc_tac [wftc_wf_thm, wf_wftc_thm]);
val wf_iff_wftc_thm = save_pop_thm "wf_iff_wftc_thm";
=TEX
}%ignore

\subsection{The Well-Founded Part of a Relation}

Relations which are not well-founded may have useful well-founded subrelations.

The well-founded part of a relation is the restriction of the relation to the subdomain of elements which are not the first element of any infinite descending sequence.

ⓈHOLCONST
│ ⦏WfPart⦎: ('a SET × ('a → 'a → BOOL)) → ('a SET × ('a → 'a → BOOL))
├──────
│ ∀ (X, $<<)⦁ WfPart (X, $<<) = (
│	{x | x ∈ X ∧ ¬ ∃f⦁ f 0 = x ∧ ∀n⦁ (f n ∈ X ∧ (f (n+1)) << f n)},
│	$<<)
■

The well-founded part of a relation is of course, well-founded.

=GFT
⦏wf_part_wf_thm⦎ = ⊢ ∀r⦁ WellFounded (WfPart r)
=TEX

\ignore{
=SML
val wf_part_def = get_spec ⌜WfPart⌝;
set_goal([], ⌜∀r⦁ WellFounded (WfPart r)⌝);
a (split_pair_rewrite_tac [⌜r⌝]
	[wf_part_def, well_founded_descending_sequence_thm]
	THEN contr_tac);
a (spec_nth_asm_tac 2 ⌜0⌝);
a (spec_nth_asm_tac 1 ⌜f⌝);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 5 ⌜n⌝);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 4 ⌜n⌝);
val wf_part_wf_thm = save_pop_thm "wfpart_wf_thm";
=TEX
}%ignore

\section{RECURSIVE DEFINITIONS}


The recursion theorem asserts the existence of fixed points of functionals under certain circumstances.
This is helpful in establishing the consistency of inductive or recursive definitions of functions.
The basic idea is that a recursive definition will be consistent if the recursion is well-founded.

Exactly how the result is best formulated depends on how you want to use it.

In HOL a suitable version of the recursion theorem will be of general applicability in consistency proofs for recursive definitions of HOL functions, which are of course, total over some type, so this is a prime application.

A special variant on this is when a new type is being introduced, corresponding to a subset of some existing type) and one of the primitive operators on the new type is defined recursively.
Since the operator is primitive, it must be defined over a subset of the representation type and a version of the recursion theorem which yields a partial fixedpoint will be useful (a partial fixedpoint in this context is a total function which is fixed under the functional over some subset of its domain type).
Since this is a generalisation of the recursion theorem more commonly applicable, this is the version I prove here.

A third case of interest is the recursive specification of functions in Z.
In this case functions are represented as many-one relations.
Its not sensible to address this variant here because it needs to be done in a context suitable for reasoning about Z, best done in a separate document.

The existence of a fixed point of a functional depends upon the recursion embodied in the functional  being well-founded.
The following two definitions allow us to talk about this formally.

A functional ``FunctRespects'' (informally, respects) a relation over some set if it delivers a function whose value at some point in that set is dependent only on the values of the operand function at the points in the set related to x under the relation.

ⓈHOLCONST
│ ⦏FunctRespects⦎: (('a → 'b) → ('a → 'b))
│		→ ('a SET × ('a → 'a → BOOL)) → BOOL
├──────
│ ∀G (X, $<<)⦁ FunctRespects G (X, $<<) ⇔
│	∀g h x⦁ x ∈ X ⇒ (∀y⦁ y ∈ X ∧ y << x ⇒ g y = h y) ⇒ G g x = G h x
■

A functional is well-founded if it respects some well-founded relation, and in that case will have a fixed point.

It would be nice if one could obtain from a functional a relation which that functional respects.
I have unable to discover a way in which this can be done in the general case (other than the useless everywhere-true relationship, which has an empty well-founded part).

=IGN
A functional has a fixed point if its dependencies are well-founded (this is a sufficient but not a necessary condition).
A functional always has a partial fixed point which is fixed over the well-founded part of its dependency relation, which may be defined:

 ⓈHOLCONST
│ ⦏WfDomain⦎: (('a → 'b) → ('a → 'b)) → 'a SET
 ├──────
│ ∀G⦁ WfDomain G = Fst (WfPart (Universe, Dependencies G))
 ■
=TEX

To express a recursion theorem giving partial fixed points of a functional we define the notion of partial equivalence of functions.

ⓈHOLCONST
│ ⦏PartFunEquiv⦎: 'a SET → ('a → 'b) → ('a → 'b) → BOOL
├──────
│ ∀X f g⦁ PartFunEquiv X f g ⇔ ∀x⦁ x ∈ X ⇒ f x = g x
■

which has the elementary property:
=GFT
⦏part_fun_equiv_lemma1⦎ = ⊢ ∀X Y f g⦁
	PartFunEquiv X f g ∧ Y ⊆ X ⇒ PartFunEquiv Y f g
=TEX

\ignore{
=SML
val funct_respects_def = get_spec ⌜FunctRespects⌝;
val part_fun_equiv_def = get_spec ⌜PartFunEquiv⌝;
=TEX
=SML
set_goal ([], ⌜∀X Y f g⦁ PartFunEquiv X f g ∧ Y ⊆ X ⇒ PartFunEquiv Y f g⌝);
a (rewrite_tac [part_fun_equiv_def, sets_ext_clauses]
	THEN REPEAT strip_tac
	THEN REPEAT (all_asm_ufc_tac[]));
val part_fun_equiv_lemma1 = save_pop_thm "part_fun_equiv_lemma1";
=TEX
}%ignore

The following variant of reflexive transitive closure (yielding a set from an element) proves useful:

ⓈHOLCONST
│ ⦏TcUpTo⦎: ('a SET × ('a → 'a → BOOL)) → 'a → 'a SET
├──────
│ ∀(X, $<<) x⦁ TcUpTo (X, $<<) x =
│	{y |  y ∈ X ∧ x ∈ X ∧ x = y ∨ Snd (TranClsr (X, $<<)) y x}
■

=GFT
⦏tcupto_inc_lemma1⦎ = ⊢ ∀ X $<< x y⦁ x ∈ X ∧ y ∈ X ∧ y << x
	⇒ (TcUpTo (X, $<<) y) ⊆ (TcUpTo (X, $<<) x)

⦏tcupto_inc_lemma2⦎ = ⊢ ∀ X $<< x y⦁ y ∈ X ∧ x ∈ (TcUpTo (X, $<<) y)
	⇒ (TcUpTo (X, $<<) x) ⊆ (TcUpTo (X, $<<) y)
=TEX

\ignore{
=SML
val tc_up_to_def = get_spec ⌜TcUpTo⌝;
=TEX
=SML
set_goal([], ⌜∀ X $<< x⦁ x ∈ X ⇒ TcUpTo (X, $<<) x = {y | Snd (RefTranClsr (X, $<<)) y x}⌝);
a (rewrite_tac [sets_ext_clauses, tc_up_to_def, ref_tran_clsr_def]
	THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac);
val tc_up_to_eq_thm = save_pop_thm "tc_up_to_eq_thm";

set_goal ([], ⌜∀ X $<< x y⦁ x ∈ X ∧ y ∈ X ∧ y << x
	⇒ (TcUpTo (X, $<<) y) ⊆ (TcUpTo (X, $<<) x)⌝);
a (rewrite_tac [tc_up_to_def, sets_ext_clauses]
	THEN REPEAT strip_tac
	THEN TRY all_var_elim_asm_tac
	THEN all_ufc_tac [tc_incr_thm2]);
(* *** Goal "1" *** *)
a (all_ufc_tac [tran_clsr_lemma1]);
(* *** Goal "2" *** *)
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜$<<⌝, ⌜y⌝, ⌜x⌝] tc_incr_thm2));
a (all_asm_ufc_tac [tran_clsr_lemma1]);
a (all_ufc_tac [trans_tc_thm2]);
val tcupto_inc_lemma1 = save_pop_thm "tcupto_inc_lemma1";

set_goal ([], ⌜∀ X $<< x y⦁ y ∈ X ∧ x ∈ (TcUpTo (X, $<<) y)
	⇒ (TcUpTo (X, $<<) x) ⊆ (TcUpTo (X, $<<) y)⌝);
a (rewrite_tac [tc_up_to_def, sets_ext_clauses]
	THEN REPEAT strip_tac
	THEN TRY all_var_elim_asm_tac
	THEN REPEAT (all_ufc_tac [tran_clsr_lemma1, trans_tc_thm2]));
val tcupto_inc_lemma2 = save_pop_thm "tcupto_inc_lemma2";
=TEX
}%ignore

The following two lemmas about {\it PartFunEquiv} are then immediate:

=GFT
⦏part_fun_equiv_lemma2⦎ = ⊢ ∀X f g x y⦁ x ∈ X ∧ y ∈ X
	∧ PartFunEquiv (TcUpTo (X, $<<) y) f g
	∧ x << y
	⇒ PartFunEquiv (TcUpTo (X, $<<) x) f g

⦏part_fun_equiv_lemma3⦎ = ⊢ ∀X Y f g x y⦁ y ∈ X
	∧ PartFunEquiv (TcUpTo (X, $<<) y) f g
	∧ x ∈ (TcUpTo (X, $<<) y)
	⇒ PartFunEquiv (TcUpTo (X, $<<) x) f g
=TEX

\ignore{
=SML
set_goal ([], ⌜∀X f g x y⦁ x ∈ X ∧ y ∈ X
	∧ PartFunEquiv (TcUpTo (X, $<<) y) f g
	∧ x << y
	⇒ PartFunEquiv (TcUpTo (X, $<<) x) f g⌝);
a (rewrite_tac [part_fun_equiv_def, sets_ext_clauses]
	THEN REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜$<<⌝, ⌜y⌝, ⌜x⌝] tcupto_inc_lemma1));
a (POP_ASM_T (asm_tac o (rewrite_rule [sets_ext_clauses])));
a (all_asm_ufc_tac[]);
a (all_asm_ufc_tac[]);
val part_fun_equiv_lemma2 = save_pop_thm "part_fun_equiv_lemma2";

set_goal ([], ⌜∀X Y f g x y⦁ y ∈ X
	∧ PartFunEquiv (TcUpTo (X, $<<) y) f g
	∧ x ∈ (TcUpTo (X, $<<) y)
	⇒ PartFunEquiv (TcUpTo (X, $<<) x) f g⌝);
a (rewrite_tac [part_fun_equiv_def, sets_ext_clauses]
	THEN REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜$<<⌝, ⌜x⌝, ⌜y⌝] tcupto_inc_lemma2));
a (POP_ASM_T (asm_tac o (rewrite_rule [sets_ext_clauses])));
a (all_asm_ufc_tac[]);
a (all_asm_ufc_tac[]);
val part_fun_equiv_lemma3 = save_pop_thm "part_fun_equiv_lemma3";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏UniquePartFixp⦎:  'a SET → (('a → 'b) → ('a → 'b)) → BOOL
├──────
│ ∀ X  G⦁ UniquePartFixp X G ⇔ ∃ f⦁
│	PartFunEquiv X (G f) f
│	∧ ∀g⦁ PartFunEquiv X (G g) g ⇒ PartFunEquiv X f g
■

\ignore{
=SML
val unique_part_fixp_def = get_spec ⌜UniquePartFixp⌝;
=SML
set_goal([],⌜∃UniqueVal:('a SET × ('a → 'a → BOOL))
		→ (('a → 'b) → ('a → 'b)) → 'a → 'b⦁
	∀ X $<< G x⦁ x ∈ X
	∧ UniquePartFixp (TcUpTo (X, $<<) x) G
	⇒ ∀ f⦁ PartFunEquiv (TcUpTo (X, $<<) x) (G f) f
	       ⇒ UniqueVal (X, $<<) G x = f x⌝);
a (∃_tac ⌜λ(X, $<<) G x⦁ εz⦁ x ∈ X
	∧ UniquePartFixp (TcUpTo (X, $<<) x) G
	⇒ ∀ f⦁ PartFunEquiv (TcUpTo (X, $<<) x) (G f) f
	       ⇒ z = f x⌝
	THEN rewrite_tac[]
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[]);
a (ε_tac ⌜ε z⦁ ∀ f⦁ PartFunEquiv (TcUpTo (X, $<<) x) (G f) f ⇒ z = f x⌝);
(* *** Goal "1" *** *)
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [unique_part_fixp_def])));
a (∃_tac ⌜f' x⌝ THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜f''⌝);
a (GET_NTH_ASM_T 1 (strip_asm_tac o (rewrite_rule [part_fun_equiv_def])));
a (spec_nth_asm_tac 1 ⌜x⌝);
a (GET_NTH_ASM_T 1 (strip_asm_tac o (rewrite_rule [tc_up_to_def])));
(* *** Goal "2" *** *)
a (all_asm_ufc_tac[]);
val unique_val_lemma = save_pop_thm "unique_val_lemma";
=TEX
}%ignore

The proof of the recursion theorem is by well-founded induction on the transitive closure of a relation respected by the functional.
The induction hypothesis is exposed in the following lemma:

=GFT
⦏recursion_theorem_lemma1⦎ = ⊢ ∀G (X, $<<)⦁
	FunctRespects G (X, $<<) ∧ WellFounded (X, $<<)
	⇒ ∀x⦁ x ∈ X ⇒ UniquePartFixp (TcUpTo (X, $<<) x) G
=TEX

\ignore{
=SML
set_goal([], ⌜∀G (X, $<<)⦁ FunctRespects G (X, $<<) ∧ WellFounded (X, $<<) ⇒
	∀x⦁ x ∈ X ⇒ UniquePartFixp (TcUpTo (X, $<<) x) G⌝);
a (once_rewrite_tac [wf_iff_wftc_thm, funct_respects_def]
	THEN split_pair_rewrite_tac [⌜TranClsr (X, $<<)⌝]
		[well_founded_induction_thm, fst_tc_lemma]
	THEN REPEAT strip_tac);
a (SPEC_NTH_ASM_T 2 ⌜λx⦁ UniquePartFixp (TcUpTo (X, $<<) x) G⌝
	(strip_asm_tac o (rewrite_rule[]))
	THEN_LIST
	  [CONTR_T discard_tac THEN POP_ASM_T ante_tac
		THEN rewrite_tac[unique_part_fixp_def], 
	   TRY (all_asm_ufc_tac[])]);
a (strip_asm_tac unique_val_lemma);
a (∃_tac ⌜λx⦁ if Snd (TranClsr (X,$<<)) x x'
	then UniqueVal (X, $<<) G x
	else G (UniqueVal (X, $<<) G) x⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [part_fun_equiv_def, tc_up_to_def]
	THEN REPEAT ∀_tac);
a (cases_tac ⌜Snd (TranClsr (X, $<<)) x'' x'⌝
	THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a (lemma_tac ⌜x'' ∈ X⌝ THEN1 (all_ufc_tac [tran_clsr_lemma1]));
a (spec_nth_asm_tac 4 ⌜x''⌝);
a (GET_NTH_ASM_T 1 (strip_asm_tac o (rewrite_rule [unique_part_fixp_def])));
a (list_spec_nth_asm_tac 6 [⌜X⌝, ⌜$<<⌝, ⌜G⌝, ⌜x''⌝]);
a (list_spec_nth_asm_tac 1 [⌜f⌝]);
a (asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 2 discard_tac);
a (GET_NTH_ASM_T 3 (asm_tac o (rewrite_rule [part_fun_equiv_def])));
a (lemma_tac ⌜x'' ∈ TcUpTo (X, $<<) x''⌝
	THEN1 asm_rewrite_tac [tc_up_to_def]);
a (spec_nth_asm_tac 2 ⌜x''⌝);
a (GET_NTH_ASM_T 1 (rewrite_thm_tac o eq_sym_rule));
a (list_spec_nth_asm_tac 15 [
	⌜λ x⦁ if Snd (TranClsr (X, $<<)) x x'
                   then UniqueVal (X, $<<) G x
                   else G (UniqueVal (X, $<<) G) x⌝,
	⌜f⌝, ⌜x''⌝]);
a (CONTR_T discard_tac
	THEN POP_ASM_T ante_tac
	THEN rewrite_tac[]);
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜$<<⌝, ⌜y⌝, ⌜x''⌝] tc_incr_thm2));
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜$<<⌝, ⌜y⌝, ⌜x''⌝, ⌜x'⌝] trans_tc_thm2));
a (asm_rewrite_tac[]);
a (spec_nth_asm_tac 15 ⌜y⌝);
a (list_spec_nth_asm_tac 15 [⌜X⌝, ⌜$<<⌝, ⌜G⌝, ⌜y⌝]);
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜G f⌝, ⌜f⌝, ⌜y⌝, ⌜x''⌝] part_fun_equiv_lemma2));
a (spec_nth_asm_tac 2 ⌜f⌝);
(* *** Goal "1.2" *** *)
a (REPEAT strip_tac THEN all_var_elim_asm_tac);
a (list_spec_nth_asm_tac 7 [⌜λ x
                 ⦁ if Snd (TranClsr (X, $<<)) x x''
                   then UniqueVal (X, $<<) G x
                   else G (UniqueVal (X, $<<) G) x⌝, ⌜UniqueVal (X, $<<) G⌝, ⌜x''⌝]);
a (CONTR_T discard_tac THEN POP_ASM_T ante_tac THEN rewrite_tac[]);
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜$<<⌝, ⌜y⌝, ⌜x''⌝] tc_incr_thm2)
	THEN POP_ASM_T rewrite_thm_tac);
(* *** Goal "2" *** *)
a (rewrite_tac [part_fun_equiv_def] THEN REPEAT strip_tac);
a (cases_tac ⌜Snd (TranClsr (X, $<<)) x'' x'⌝
	THEN asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (ufc_tac [tran_clsr_lemma1]);
a (spec_nth_asm_tac 6 ⌜x''⌝);
a (list_spec_nth_asm_tac 6 [⌜X⌝, ⌜$<<⌝, ⌜G⌝, ⌜x''⌝]);
a (all_ufc_tac [list_∀_elim [⌜X⌝, ⌜Y⌝, ⌜f:'a → 'b⌝, ⌜g:'a → 'b⌝] part_fun_equiv_lemma3]);
a (spec_nth_asm_tac 2 ⌜g⌝);
(* *** Goal "2.2" *** *)
a (DROP_NTH_ASM_T 2 ante_tac
	THEN rewrite_tac [tc_up_to_def]
	THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac);
a (list_spec_nth_asm_tac 8 [⌜UniqueVal (X, $<<) G⌝, ⌜g⌝, ⌜x''⌝]);
(* *** Goal "2.2.1" *** *)
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜$<<⌝, ⌜y⌝, ⌜x''⌝] tc_incr_thm2));
a (spec_nth_asm_tac 8 ⌜y⌝);
a (list_spec_nth_asm_tac 8 [⌜X⌝, ⌜$<<⌝, ⌜G⌝, ⌜y⌝]);
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜G g⌝, ⌜g⌝, ⌜y⌝, ⌜x''⌝] part_fun_equiv_lemma2));
a (spec_nth_asm_tac 2 ⌜g⌝);
a (asm_rewrite_tac[]);
a (GET_NTH_ASM_T 3 ante_tac
	THEN rewrite_tac [part_fun_equiv_def, tc_up_to_def]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜x''⌝);
val recursion_theorem_lemma1 = save_pop_thm "recursion_theorem_lemma1";
=TEX
}%ignore
\ignore{
=IGN
(* evaluation of ufc tactics *)
set_goal([], ⌜∀G (X, $<<)⦁ FunctRespects G (X, $<<) ∧ WellFounded (X, $<<) ⇒
	∀x⦁ x ∈ X ⇒ UniquePartFixp (TcUpTo (X, $<<) x) G⌝);
a (once_rewrite_tac [wf_iff_wftc_thm, funct_respects_def]
	THEN split_pair_rewrite_tac [⌜TranClsr (X, $<<)⌝]
		[well_founded_induction_thm, fst_tc_lemma]
	THEN REPEAT strip_tac);
a (SPEC_NTH_ASM_T 2 ⌜λx⦁ UniquePartFixp (TcUpTo (X, $<<) x) G⌝
	(strip_asm_tac o (rewrite_rule[]))
	THEN_LIST
	  [CONTR_T discard_tac THEN POP_ASM_T ante_tac
		THEN rewrite_tac[unique_part_fixp_def], 
	   TRY (all_asm_ufc_tac[])]);
a (strip_asm_tac unique_val_lemma);
a (∃_tac ⌜λx⦁ if Snd (TranClsr (X,$<<)) x x'
	then UniqueVal (X, $<<) G x
	else G (UniqueVal (X, $<<) G) x⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [part_fun_equiv_def, tc_up_to_def]
	THEN REPEAT ∀_tac);
a (cases_tac ⌜Snd (TranClsr (X, $<<)) x'' x'⌝
	THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a (lemma_tac ⌜x'' ∈ X⌝ THEN1 (all_ufc_tac [tran_clsr_lemma1]));
a (lemma_tac ⌜UniquePartFixp (TcUpTo (X, $<<) x'') G⌝ THEN1 (all_asm_ufc_tac []));
a (ufc_tac [unique_part_fixp_def]);
a (LEMMA_T ⌜UniqueVal (X, $<<) G x'' = f x''⌝ rewrite_thm_tac
	THEN1 (REPEAT (asm_ufc_tac [])));
(*
a (list_spec_nth_asm_tac 6 [⌜X⌝, ⌜$<<⌝, ⌜G⌝, ⌜x''⌝]);
a (list_spec_nth_asm_tac 1 [⌜f⌝]);
a (asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 2 discard_tac);
*)
a (ufc_tac [part_fun_equiv_def]);
a (lemma_tac ⌜x'' ∈ TcUpTo (X, $<<) x''⌝
	THEN1 asm_rewrite_tac [tc_up_to_def]);
a (LEMMA_T ⌜G f x'' = f x''⌝ (rewrite_thm_tac o eq_sym_rule)
	THEN1 asm_fc_tac[]);
(*
a (spec_nth_asm_tac 2 ⌜x''⌝);
a (GET_NTH_ASM_T 1 (rewrite_thm_tac o eq_sym_rule));
*)
a (list_spec_nth_asm_tac 15 [
	⌜λ x⦁ if Snd (TranClsr (X, $<<)) x x'
                   then UniqueVal (X, $<<) G x
                   else G (UniqueVal (X, $<<) G) x⌝,
	⌜f⌝, ⌜x''⌝]);
a (CONTR_T discard_tac
	THEN POP_ASM_T ante_tac
	THEN rewrite_tac[]);
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜$<<⌝, ⌜y⌝, ⌜x''⌝] tc_incr_thm2));
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜$<<⌝, ⌜y⌝, ⌜x''⌝, ⌜x'⌝] trans_tc_thm2));
a (asm_rewrite_tac[]);
a (spec_nth_asm_tac 15 ⌜y⌝);
a (list_spec_nth_asm_tac 15 [⌜X⌝, ⌜$<<⌝, ⌜G⌝, ⌜y⌝]);
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜G f⌝, ⌜f⌝, ⌜y⌝, ⌜x''⌝] part_fun_equiv_lemma2));
a (spec_nth_asm_tac 2 ⌜f⌝);
(* *** Goal "1.2" *** *)
a (REPEAT strip_tac THEN all_var_elim_asm_tac);
a (list_spec_nth_asm_tac 7 [⌜λ x
                 ⦁ if Snd (TranClsr (X, $<<)) x x''
                   then UniqueVal (X, $<<) G x
                   else G (UniqueVal (X, $<<) G) x⌝, ⌜UniqueVal (X, $<<) G⌝, ⌜x''⌝]);
a (CONTR_T discard_tac THEN POP_ASM_T ante_tac THEN rewrite_tac[]);
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜$<<⌝, ⌜y⌝, ⌜x''⌝] tc_incr_thm2)
	THEN POP_ASM_T rewrite_thm_tac);
(* *** Goal "2" *** *)
a (rewrite_tac [part_fun_equiv_def] THEN REPEAT strip_tac);
a (cases_tac ⌜Snd (TranClsr (X, $<<)) x'' x'⌝
	THEN asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (ufc_tac [tran_clsr_lemma1]);
a (spec_nth_asm_tac 6 ⌜x''⌝);
a (list_spec_nth_asm_tac 6 [⌜X⌝, ⌜$<<⌝, ⌜G⌝, ⌜x''⌝]);
a (all_ufc_tac [list_∀_elim [⌜X⌝, ⌜Y⌝, ⌜f:'a → 'b⌝, ⌜g:'a → 'b⌝] part_fun_equiv_lemma3]);
a (spec_nth_asm_tac 2 ⌜g⌝);
(* *** Goal "2.2" *** *)
a (DROP_NTH_ASM_T 2 ante_tac
	THEN rewrite_tac [tc_up_to_def]
	THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac);
a (list_spec_nth_asm_tac 8 [⌜UniqueVal (X, $<<) G⌝, ⌜g⌝, ⌜x''⌝]);
(* *** Goal "2.2.1" *** *)
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜$<<⌝, ⌜y⌝, ⌜x''⌝] tc_incr_thm2));
a (spec_nth_asm_tac 8 ⌜y⌝);
a (list_spec_nth_asm_tac 8 [⌜X⌝, ⌜$<<⌝, ⌜G⌝, ⌜y⌝]);
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜G g⌝, ⌜g⌝, ⌜y⌝, ⌜x''⌝] part_fun_equiv_lemma2));
a (spec_nth_asm_tac 2 ⌜g⌝);
a (asm_rewrite_tac[]);
a (GET_NTH_ASM_T 3 ante_tac
	THEN rewrite_tac [part_fun_equiv_def, tc_up_to_def]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜x''⌝);
val recursion_theorem_lemma1 = save_pop_thm "recursion_theorem_lemma1";
=TEX
}%ignore

The recursion theorem follows:

=GFT
⦏recursion_theorem⦎ = ⊢ ∀ X $<< G⦁
	FunctRespects G (X, $<<) ∧ WellFounded (X, $<<) ⇒ UniquePartFixp X G
=TEX

\ignore{
=SML
set_goal([], ⌜∀((X, $<<):'a SET × ('a → 'a → BOOL)) (G:('a → 'b) → ('a → 'b))⦁
	FunctRespects G (X, $<<) ∧ WellFounded (X, $<<) ⇒
	UniquePartFixp X G⌝);
a (REPEAT strip_tac
	THEN ufc_tac [recursion_theorem_lemma1, funct_respects_def]);
a (rewrite_tac [unique_part_fixp_def]);
a (strip_asm_tac unique_val_lemma);
a (∃_tac ⌜UniqueVal (X, $<<) G⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [part_fun_equiv_def]
	THEN REPEAT strip_tac);
a (all_asm_ufc_tac[]);
a (all_asm_ufc_tac [unique_part_fixp_def]);
a (lemma_tac ⌜UniqueVal (X, $<<) G x = f x⌝
	THEN1 all_asm_ufc_tac[]);
a (asm_rewrite_tac[]);
a (fc_tac [part_fun_equiv_def]);
a (list_spec_nth_asm_tac 1 [⌜x⌝]);
(* *** Goal "1.1" *** *)
a (POP_ASM_T ante_tac
	THEN asm_rewrite_tac [tc_up_to_def]);
(* *** Goal "1.2" *** *)
a (DROP_NTH_ASM_T 2 discard_tac);
a (SYM_ASMS_T rewrite_tac);
a (list_spec_nth_asm_tac 9 [⌜f⌝, ⌜UniqueVal (X, $<<) G⌝, ⌜x⌝]);
a (CONTR_T discard_tac THEN POP_ASM_T ante_tac THEN rewrite_tac[]);
a (spec_nth_asm_tac 10 ⌜y⌝);
a (list_spec_nth_asm_tac 10 [⌜X⌝, ⌜$<<⌝, ⌜G⌝, ⌜y⌝]);
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜G f⌝, ⌜f⌝, ⌜y⌝, ⌜x⌝] part_fun_equiv_lemma2));
a (spec_nth_asm_tac 2 ⌜f⌝);
(* *** Goal "2" *** *)
a (rewrite_tac [part_fun_equiv_def] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 4 ⌜x⌝);
a (list_spec_nth_asm_tac 4 [⌜X⌝, ⌜$<<⌝, ⌜G⌝, ⌜x⌝]);
a (lemma_tac ⌜(TcUpTo (X, $<<) x) ⊆ X⌝
	THEN1 (rewrite_tac [sets_ext_clauses, tc_up_to_def]
		THEN REPEAT strip_tac
		THEN ufc_tac[tran_clsr_lemma1]));
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜TcUpTo (X, $<<) x⌝, ⌜G g⌝, ⌜g⌝] part_fun_equiv_lemma1));
a (spec_nth_asm_tac 3 ⌜g⌝);
val recursion_theorem = save_pop_thm "recursion_theorem";
=TEX
}%ignore

from which is readily obtained the specialisation to total functions:

=GFT
⦏tf_recursion_thm⦎ = ⊢ ∀$<< G⦁
	FunctRespects G (Universe, $<<) ∧ WellFounded (Universe, $<<)
	⇒ ∃f⦁ (G f) = f
=TEX

\ignore{
=SML
set_goal ([], ⌜∀$<< G⦁ FunctRespects G (Universe, $<<) ∧ WellFounded (Universe, $<<) ⇒
	∃⋎1 f⦁ (G f) = f⌝);
a (REPEAT strip_tac THEN all_ufc_tac [recursion_theorem]);
a (POP_ASM_T ante_tac THEN rewrite_tac [unique_part_fixp_def, part_fun_equiv_def]
	THEN REPEAT strip_tac);
a (∃⋎1_tac ⌜f⌝ THEN asm_rewrite_tac [ext_thm]
	THEN REPEAT strip_tac THEN asm_ufc_tac[]
	THEN asm_rewrite_tac[]);
val tf_recursion_thm = save_pop_thm "tf_recursion_thm";
=TEX
}%ignore

It may be helpful to have a proforma which facilitates proof that a function respects some well-founded relation.
One way of approaching this is to define a function which restricts some other function to the part of its domain strictly below some value.
These will be the values which are accessible to a function computing its value at that point which respects the relation.

Here I assume the relation is over the whole type.

=SML
declare_infix(400, "⟨◁");
=TEX

ⓈHOLCONST
│ $⦏⟨◁⦎:  ('a × ('a → 'a → BOOL)) → ('a → 'b) → ('a → 'b)
├──────
│ ∀ x $<< f⦁ (x, $<<) ⟨◁ f = λy⦁ if y << x then f y else εz⦁T
■

=GFT
⦏⟨◁_fc_thm⦎ = ⊢ ∀ y x $<< f⦁ y << x ⇒ ((x, $<<) ⟨◁ f) y = f y
=TEX

\ignore{
=SML
val ⟨◁_def = get_spec ⌜$⟨◁⌝;

set_goal([], ⌜∀ y x $<< f⦁ y << x ⇒ ((x, $<<) ⟨◁ f) y = f y⌝);
a (rewrite_tac [⟨◁_def] THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
val ⟨◁_fc_thm = save_pop_thm "⟨◁_fc_thm";

set_goal([], ⌜∀$<<⦁ WellFounded(Universe, $<<) ⇒
	∀af⦁ ∃f⦁ ∀x⦁ f x = af ((x, $<<) ⟨◁ f) x⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜FunctRespects (λg x⦁ af ((x, $<<) ⟨◁ g) x) (Universe, $<<)⌝
	THEN1 rewrite_tac[funct_respects_def, ⟨◁_def, get_spec ⌜Universe⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (LEMMA_T ⌜(λ y⦁ if y << x then g y else ε z⦁ T) 
	= (λ y⦁ if y << x then h y else ε z⦁ T)⌝ rewrite_thm_tac
	THEN1 (rewrite_tac[ext_thm]
		THEN REPEAT strip_tac));
a (cond_cases_tac ⌜x' << x⌝);
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac[tf_recursion_thm]);
a (∃_tac ⌜f⌝);
a (strip_tac);
a (DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac[ext_thm] THEN strip_tac
	THEN asm_rewrite_tac[]);
val tf_rec_thm2 = save_pop_thm "tf_rec_thm2";
=TEX
}%ignore

\section{RELATIONS OVER A TYPE}\label{RELATIONSOVERATYPE}

The material in the next two sections is placed in a new theory {\it U\_orders}.

\ignore{
=SML
new_theory "⦏U_orders⦎";
=TEX
}%ignore

All of our definitions are explicit about the ordered set $X$ on which the property of
interest is required to hold. In many applications, $X$ will be the universe of a type
and the definitions and the statements of some of the theorems simplify.
The relevant definitions may be given concisely as follows:

ⓈHOLCONST
│	UIrrefl : ('a  → 'a → BOOL) → BOOL;
│	UAntisym : ('a  → 'a → BOOL) → BOOL;
│	UTrans : ('a  → 'a → BOOL) → BOOL;
│	UStrictPartialOrder : ('a  → 'a → BOOL) → BOOL;
│	UTrich : ('a  → 'a → BOOL) → BOOL;
│	UStrictLinearOrder : ('a  → 'a → BOOL) → BOOL;
│	UComplete : ('a  → 'a → BOOL) → BOOL;
│	URefl : ('a  → 'a → BOOL) → BOOL;
│	UPartialOrder : ('a  → 'a → BOOL) → BOOL;
│	ULinearOrder : ('a  → 'a → BOOL) → BOOL;
│	UWeakMinCond : ('a  → 'a → BOOL) → BOOL;
│	UMinCond : ('a  → 'a → BOOL) → BOOL;
│	UWellOrdering : ('a  → 'a → BOOL) → BOOL;
│	UWellFounded : ('a  → 'a → BOOL) → BOOL;
│	UStrictWellOrdering : ('a  → 'a → BOOL) → BOOL;
│	UInitialStrictWellOrdering : ('a  → 'a → BOOL) → BOOL
├
│	UIrrefl = Curry Irrefl Universe 
│ ∧	UAntisym = Curry Antisym Universe
│ ∧	UTrans = Curry Trans Universe
│ ∧	UStrictPartialOrder = Curry StrictPartialOrder Universe
│ ∧	UTrich = Curry Trich Universe
│ ∧	UStrictLinearOrder = Curry StrictLinearOrder Universe
│ ∧	UComplete = Curry Complete Universe
│ ∧	URefl = Curry Refl Universe
│ ∧	UPartialOrder = Curry PartialOrder Universe
│ ∧	ULinearOrder = Curry LinearOrder Universe
│ ∧	UWeakMinCond = Curry WeakMinCond Universe
│ ∧	UMinCond = Curry MinCond Universe
│ ∧	UWellOrdering = Curry WellOrdering Universe
│ ∧	UWellFounded = Curry WellFounded Universe
│ ∧	UStrictWellOrdering = Curry StrictWellOrdering Universe
│ ∧	UInitialStrictWellOrdering = Curry InitialStrictWellOrdering Universe
■

Now we automatically derive the defining properties of all of these constants
in terms of primitive notions or other constants in the set.

\ignore{
=SML
val ext_thm_x = prove_rule[ext_thm]⌜∀ f g⦁ f = g ⇔ (∀ $<<⦁ f $<< = g $<<) ⌝;
val u_thm1 = (rewrite_rule[ext_thm_x] o get_spec)⌜UIrrefl⌝;
val u_thm2 =  (rewrite_rule[] o once_rewrite_rule
    	(def_thms@[
		strict_well_ordering_def,
		initial_strict_well_ordering_def]))
	u_thm1;
val u_thm3 = conv_rule (ONCE_MAP_C eq_sym_conv) u_thm1;
val u_thm4 = rewrite_rule [u_thm3] u_thm2;

val [
⦏u_irrefl_def_thm⦎,
⦏u_antisym_def_thm⦎,
⦏u_trans_def_thm⦎,
⦏u_strict_partial_order_def_thm⦎,
⦏u_trich_def_thm⦎,
⦏u_strict_linear_order_def_thm⦎,
⦏u_complete_def_thm⦎,
⦏u_refl_def_thm⦎,
⦏u_partial_order_def_thm⦎,
⦏u_linear_order_def_thm⦎,
⦏u_weak_min_cond_def_thm⦎,
⦏u_min_cond_def_thm⦎,
⦏u_well_ordering_def_thm⦎,
⦏u_well_founded_def_thm⦎,
⦏u_strict_well_ordering_def_thm⦎,
⦏u_initial_strict_well_ordering_def_thm⦎
] = strip_∧_rule u_thm4;
val _ = map save_thm [
	("u_irrefl_def_thm", u_irrefl_def_thm),
	("u_antisym_def_thm", u_antisym_def_thm),
	("u_trans_def_thm", u_trans_def_thm),
	("u_strict_partial_order_def_thm", u_strict_partial_order_def_thm),
	("u_trich_def_thm", u_trich_def_thm),
	("u_strict_linear_order_def_thm", u_strict_linear_order_def_thm),
	("u_complete_def_thm", u_complete_def_thm),
	("u_refl_def_thm", u_refl_def_thm),
	("u_partial_order_def_thm", u_partial_order_def_thm),
	("u_linear_order_def_thm", u_linear_order_def_thm),
	("u_weak_min_cond_def_thm", u_weak_min_cond_def_thm),
	("u_min_cond_def_thm", u_min_cond_def_thm),
	("u_well_ordering_def_thm", u_well_ordering_def_thm),
	("u_well_founded_def_thm", u_well_founded_def_thm),
	("u_strict_well_ordering_def_thm", u_strict_well_ordering_def_thm),
	("u_initial_strict_well_ordering_def_thm", u_initial_strict_well_ordering_def_thm)
	];
=TEX

The following code translates the relevant instances of the main theorems:

=SML
val ⦏u_zorn_thm2⦎ = save_thm
	("u_zorn_thm2",
	rewrite_rule[u_thm3](∀_elim⌜Universe:'a SET⌝
		zorn_thm2));
val ⦏u_well_ordering_thm⦎ = save_thm
	("u_well_ordering_thm",
	rewrite_rule[u_thm3](∀_elim⌜Universe:'a SET⌝
		well_ordering_thm));
val ⦏u_strict_well_ordering_thm⦎ = save_thm
	("u_strict_well_ordering_thm",
	rewrite_rule[u_thm3](∀_elim⌜Universe:'a SET⌝
		strict_well_ordering_thm));
val ⦏u_swo_clauses⦎ = save_thm
	("u_swo_clauses",
	rewrite_rule[u_thm3](∀_elim⌜Universe:'a SET⌝
		swo_clauses));
val ⦏u_initial_strict_well_ordering_thm⦎ = save_thm
	("u_initial_strict_well_ordering_thm",
	rewrite_rule[u_thm3](∀_elim ⌜Universe:'a SET⌝
		initial_strict_well_ordering_thm));
val ⦏u_iswo_clauses⦎ = save_thm
	("u_iswo_clauses",
	rewrite_rule[u_thm3](∀_elim⌜Universe:'a SET⌝
		iswo_clauses));
val ⦏u_iswo_clauses2⦎ = save_thm
	("u_iswo_clauses2",
	rewrite_rule[u_thm3](∀_elim⌜Universe:'a SET⌝
		iswo_clauses2));
val ⦏u_iswo_well_founded_thm⦎ = save_thm
	("u_iswo_well_founded_thm",
	rewrite_rule[u_thm3](∀_elim⌜Universe:'a SET⌝
		ISWO_WellFounded_thm));
val ⦏u_iswo_induction_thm⦎ = save_thm
	("u_iswo_induction_thm",
	rewrite_rule[u_thm3](∀_elim⌜Universe:'a SET⌝
		ISWO_Induction_thm));
val ⦏u_min_cond_descending_sequence_thm⦎ = save_thm
	("u_min_cond_descending_sequence_thm",
	rewrite_rule[u_thm3](∀_elim⌜Universe:'a SET⌝
		min_cond_descending_sequence_thm));
val ⦏u_well_founded_descending_sequence_thm⦎ = save_thm
	("u_well_founded_descending_sequence_thm",
	rewrite_rule[u_thm3](∀_elim⌜Universe:'a SET⌝
		well_founded_descending_sequence_thm));
val ⦏u_well_founded_induction_thm⦎ = save_thm
	("u_well_founded_induction_thm",
	rewrite_rule[u_thm3](∀_elim⌜Universe:'a SET⌝
		well_founded_induction_thm));
val ⦏u_refl_well_ordering_lower_bounds_thm⦎ = save_thm
	("u_refl_well_ordering_lower_bounds_thm",
	rewrite_rule[u_thm3](∀_elim⌜Universe:'a SET⌝
		refl_well_ordering_lower_bounds_thm));
=IGN
set_goal([], ⌜⌝);
=TEX
}%ignore

\subsection{Miscellanea}

I place here some results which are proven only over orders over the whole type.

\subsubsection{Properties pulled back from a map}

When a function whose codomain is well-founded is used to define an order over its domain type, then that order will be well-founded.

=GFT
u_well_founded_pullback_thm =
   ⊢ ∀ f r⦁ UWellFounded r ⇒ UWellFounded (λ x y⦁ r (f x) (f y)):
=TEX

\ignore{
=SML
set_goal([], ⌜∀(f:'a → 'b) (r:'b → 'b → BOOL)⦁ UWellFounded r
	     ⇒ UWellFounded (λx y⦁ r (f x)(f y)) ⌝);
a (REPEAT ∀_tac THEN rewrite_tac [u_well_founded_def_thm]
  THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜{y | ∃z⦁ z ∈ A ∧ y = f z} ⌝);
(* *** Goal "1" *** *)
a (GET_NTH_ASM_T 2 (fn x => strip_asm_tac (rewrite_rule[sets_ext_clauses] x)));
a (GET_NTH_ASM_T 2 ante_tac);
a (rewrite_tac[sets_ext_clauses]);
a (strip_tac);
a (spec_nth_asm_tac 1 ⌜f x⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "2" *** *)
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[] THEN strip_tac);
a (SYM_ASMS_T rewrite_tac);
a (spec_nth_asm_tac 1 ⌜f y⌝ THEN asm_rewrite_tac[]);
a (strip_tac);
a (spec_nth_asm_tac 2 ⌜y⌝);
val u_well_founded_pullback_thm = save_pop_thm "u_well_founded_pullback_thm";
=TEX
}%ignore

\subsubsection{Combining Orders}

The sum of two orders may be defined thus:

=SML
declare_infix(400, "+⋎r");
=TEX

ⓈHOLCONST
│ $⦏+⋎r⦎:  ('a → 'a → BOOL) → ('b → 'b → BOOL) → ('a + 'b → 'a + 'b → BOOL)
├──────
│ ∀ r s⦁ r +⋎r s = λx y⦁
│    (IsL x ∧ IsL y ∧ r (OutL x) (OutL y))
│ ∨   (IsR x ∧ IsR y ∧ s (OutR x) (OutR y)) 
│ ∨   (IsL x ∧ IsR y) 
■

=GFT
   
=TEX

\ignore{
=IGN
val plus⋎r_def = get_spec ⌜$+⋎r⌝;
stop;
set_goal([], ⌜∀ r s⦁UWellFounded r ∧ UWellFounded s ⇒ UWellFounded (r +⋎r s)⌝);
a (rewrite_tac[u_well_founded_def_thm, plus⋎r_def]
  THEN REPEAT strip_tac);
a (POP_ASM_T (strip_asm_tac o (rewrite_rule[sets_ext_clauses])));
a (cases_tac ⌜{v | IsL v} ∩ A = {}⌝);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 3 ⌜{ v | ∃ w⦁ w ∈ A ∧ v = OutR w}⌝);
(* *** Goal "1.1" *** *)
a (POP_ASM_T ante_tac THEN POP_ASM_T ante_tac
  THEN rewrite_tac[sets_ext_clauses]);
a (REPEAT strip_tac);
a (asm_fc_tac[]);
a (strip_asm_tac (∀_elim ⌜x⌝ sum_cases_thm2));
=TEX
}%ignore

\section{INDEPENDENCE}\label{Independence}

We want to show that for any pair of the primitive notions, $P$ and $Q$,
there are relations for which both hold, $P$ holds but not $Q$ and $Q$ holds but not $P$.
Somewhat more subtly, we want to do this without assuming that the primitive notions
are distinct. (I.e., it is not good enough to assume that reflexivity and transitivity are
distinct notions, for example, when exhibiting a relation that has one property but
not the other).

The examples will all use relations on the natural numbers. The weak minimum condition
turns out to be the hardest property to prove in the examples; the following lemma serves
in all but one case (viz. weak minimum condition and not antisymmetry, for which, happily,
the relation that relates any two natural numbers does the job).

=SML
open_theory "ordered_sets";
new_theory "⦏ordered_sets_i⦎";
=TEX

\ignore{
=SML
val weak_min_cond_≤_lemma = (
set_goal ([], ⌜∀X; $<< ⦁
	(∀i j:ℕ⦁  i << j ⇒ i ≤ j) ⇒ WeakMinCond(X, $<<)
⌝);
a(rewrite_tac[weak_min_cond_def] THEN PC_T1 "sets_ext1" REPEAT strip_tac);
a(POP_ASM_T ante_tac THEN cov_induction_tac⌜x⌝);
a(REPEAT strip_tac THEN cases_tac ⌜∀n⦁n ∈ A ⇒ x ≤ n⌝);
(* *** Goal "1" *** *)
a(∃_tac ⌜x⌝ THEN REPEAT strip_tac);
a(all_asm_ufc_tac[] THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(lemma_tac⌜n < x⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a(all_asm_ufc_tac[]);
a(∃_tac ⌜x'⌝ THEN asm_rewrite_tac[]);
save_pop_thm "weak_min_cond_≤_lemma"
);
=TEX
}%ignore

For the cases where we need to show that the primitive properties are compatible,
our example are be (with one exception), the usual order structure on the natural 
numbers in its reflexive or irreflexive guise. The exception turns out to be when
we have to exhibit a relation which is both reflexive and irreflexive.

\ignore{
=SML
val ≤_less_lemma = (
set_goal ([], ⌜
	Refl(Universe, ($≤: ℕ→(ℕ→BOOL)))
∧	Irrefl(Universe, ($<: ℕ→(ℕ→BOOL)))
∧	¬Irrefl(Universe, ($≤: ℕ→(ℕ→BOOL)))
∧	¬Refl(Universe, ($<: ℕ→(ℕ→BOOL)))
∧	Antisym(Universe, ($≤: ℕ→(ℕ→BOOL)))
∧	Antisym(Universe, ($<: ℕ→(ℕ→BOOL)))
∧	Trans(Universe, ($≤: ℕ→(ℕ→BOOL)))
∧	Trans(Universe, ($<: ℕ→(ℕ→BOOL)))
∧	Trich(Universe, ($≤: ℕ→(ℕ→BOOL)))
∧	Trich(Universe, ($<: ℕ→(ℕ→BOOL)))
∧	WeakMinCond(Universe, ($≤: ℕ→(ℕ→BOOL)))
∧	WeakMinCond(Universe, ($<: ℕ→(ℕ→BOOL)))
⌝);
a(rewrite_tac [refl_def, irrefl_def, antisym_def, trans_def, trich_def]
	THEN PC_T1 "sets_ext1" REPEAT strip_tac
	THEN_TRY PC_T1 "lin_arith" asm_prove_tac[]
	THEN bc_thm_tac weak_min_cond_≤_lemma
	THEN_TRY rewrite_tac[] THEN PC_T1 "lin_arith" asm_prove_tac[]);
save_pop_thm "≤_less_lemma"
);
=TEX

Now we embark on a short series of portmanteau lemmas that will fit together
to give the desired results. The first lemma is the one where we actually
have to provide 20 specific witnesses to show that none of reflexivity,
antisymmetry, transitivity, trichotomy or the weak minimum condition entails
another. We formulate this as follows using numeric tags to avoid accidentally
assuming that the primitive notions are pairwise distinct.

=SML
val _ = set_merge_pcs["'sets_alg", "basic_hol", "'savedthm_cs_∃_proof"];
val ⦏independence_lemma1⦎ = (
set_goal ([], ⌜
∀m n⦁ m ∈ {0; 1; 2; 3; 4} ∧ n ∈ {0; 1; 2; 3; 4} ∧ ¬m = n ⇒
let	props m =
	if	m = 0
	then	Refl
	else if	m = 1
	then	Antisym
	else if	m = 2
	then	Trans
	else if	m = 3
	then	Trich
	else	WeakMinCond
in	∃X : ℕ SET; $<< ⦁ props m (X, $<<) ∧ ¬props n (X, $<<)
⌝);
a(rewrite_tac[let_def]);
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN_TRY all_var_elim_asm_tac
	THEN conv_tac (MAP_C ℕ_eq_conv) THEN rewrite_tac[]
	THEN DROP_ASMS_T discard_tac);
(* *** Goal "1" *** *) (* Refl / Antisym *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j⦁T⌝ );
a(rewrite_tac def_thms THEN REPEAT strip_tac);
a(∃_tac⌜0⌝ THEN strip_tac THEN ∃_tac⌜1⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *) (* Refl / Trans *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j⦁i = j ∨ j = i + 1⌝ );
a(rewrite_tac def_thms THEN REPEAT strip_tac);
a(∃_tac⌜0⌝ THEN strip_tac THEN ∃_tac⌜1⌝ THEN strip_tac THEN ∃_tac⌜2⌝
	THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "3" *** *) (* Refl / Trich *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j⦁i = j⌝ );
a(rewrite_tac def_thms THEN REPEAT strip_tac);
a(∃_tac⌜0⌝ THEN strip_tac THEN ∃_tac⌜1⌝ THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "4" *** *) (* Refl / WeakMinCond *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜$≥:ℕ→(ℕ→BOOL)⌝ );
a(rewrite_tac def_thms THEN REPEAT strip_tac);
a(∃_tac⌜Universe⌝ THEN PC_T1 "sets_ext1" rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜x+1⌝ THEN REPEAT strip_tac);
(* *** Goal "5" *** *) (* Antisym / Refl *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j:ℕ⦁i < j⌝ );
a(rewrite_tac def_thms THEN PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "6" *** *) (* Antisym / Trans *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j:ℕ⦁j = i + 1⌝ );
a(rewrite_tac def_thms THEN REPEAT strip_tac THEN1
	asm_rewrite_tac[plus_assoc_thm]);
a(∃_tac⌜0⌝ THEN strip_tac THEN ∃_tac⌜1⌝ THEN strip_tac THEN ∃_tac⌜2⌝
	THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "7" *** *) (* Antisym / Trich *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j:ℕ⦁j = i + 1⌝ );
a(rewrite_tac def_thms THEN REPEAT strip_tac THEN1
	asm_rewrite_tac[plus_assoc_thm]);
a(∃_tac⌜0⌝ THEN strip_tac THEN ∃_tac⌜2⌝  THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "8" *** *) (* Antisym / WeakMinCond *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜$>:(ℕ→(ℕ→BOOL))⌝ );
a(rewrite_tac def_thms THEN REPEAT strip_tac THEN1
	PC_T1 "lin_arith" asm_prove_tac[]);
a(∃_tac⌜Universe⌝ THEN PC_T1 "sets_ext1" rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜x+1⌝ THEN REPEAT strip_tac);
(* *** Goal "9" *** *) (* Trans / Refl *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j:ℕ⦁F⌝ );
a(rewrite_tac def_thms THEN REPEAT strip_tac);
(* *** Goal "10" *** *) (* Trans / Antisym *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j:ℕ⦁T⌝ );
a(rewrite_tac def_thms THEN REPEAT strip_tac);
a(∃_tac⌜0⌝ THEN strip_tac THEN ∃_tac⌜1⌝ THEN REPEAT strip_tac);
(* *** Goal "11" *** *) (* Trans / Trich *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j:ℕ⦁F⌝ );
a(rewrite_tac def_thms THEN REPEAT strip_tac);
a(∃_tac⌜0⌝ THEN strip_tac THEN ∃_tac⌜1⌝ THEN REPEAT strip_tac);
(* *** Goal "12" *** *) (* Trans / WeakMinCond *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j:ℕ⦁i >  j⌝ );
a(rewrite_tac def_thms THEN REPEAT strip_tac THEN_TRY
	 PC_T1 "lin_arith" asm_prove_tac[]);
a(∃_tac⌜Universe⌝ THEN PC_T1 "sets_ext1" rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜x+1⌝ THEN REPEAT strip_tac);
(* *** Goal "13" *** *) (* Trich / Refl *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j:ℕ⦁i < j⌝ );
a(rewrite_tac def_thms THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "14" *** *) (* Trich / Antisym *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j:ℕ⦁T⌝ );
a(rewrite_tac def_thms THEN REPEAT strip_tac);
a(∃_tac⌜0⌝ THEN strip_tac THEN ∃_tac⌜1⌝ THEN REPEAT strip_tac);
(* *** Goal "15" *** *) (* Trich / Trans *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j⦁¬j = 0 ∨ ¬i = 0 ∧ j = 0 ⌝ );
a(rewrite_tac def_thms THEN REPEAT strip_tac THEN1
	PC_T1 "lin_arith" asm_prove_tac[]);
a(∃_tac⌜0⌝ THEN strip_tac THEN ∃_tac⌜1⌝ THEN strip_tac THEN ∃_tac⌜0⌝
	THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "16" *** *) (* Trich / WeakMinCond *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j:ℕ⦁i >  j⌝ );
a(rewrite_tac def_thms THEN REPEAT strip_tac THEN_TRY
	 PC_T1 "lin_arith" asm_prove_tac[]);
a(∃_tac⌜Universe⌝ THEN PC_T1 "sets_ext1" rewrite_tac[] THEN REPEAT strip_tac);
a(∃_tac⌜x+1⌝ THEN REPEAT strip_tac);
(* *** Goal "17" *** *) (* WeakMinCond / Refl *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j:ℕ⦁i <  j⌝ );
a(strip_tac THEN1
	(bc_thm_tac weak_min_cond_≤_lemma
	THEN rewrite_tac[] THEN PC_T1 "lin_arith" prove_tac[]));
a(rewrite_tac def_thms THEN REPEAT strip_tac);
(* *** Goal "18" *** *) (* WeakMinCond / Antisym *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j:ℕ⦁ T⌝ );
a(rewrite_tac def_thms THEN PC_T1 "sets_ext1" prove_tac[]);
a(∃_tac⌜0⌝ THEN strip_tac THEN ∃_tac⌜1⌝ THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "19" *** *) (* WeakMinCond / Trans *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j:ℕ⦁j = i + 1⌝ );
a(strip_tac THEN1
	(bc_thm_tac weak_min_cond_≤_lemma
	THEN rewrite_tac[] THEN PC_T1 "lin_arith" prove_tac[]));
a(rewrite_tac def_thms THEN REPEAT strip_tac);
a(∃_tac⌜0⌝ THEN strip_tac THEN ∃_tac⌜1⌝ THEN strip_tac THEN ∃_tac⌜2⌝
	THEN PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "20" *** *)
a(∃_tac⌜Universe⌝ THEN ∃_tac⌜λi j:ℕ⦁j = i + 1⌝ );
a(strip_tac THEN1
	(bc_thm_tac weak_min_cond_≤_lemma
	THEN rewrite_tac[] THEN PC_T1 "lin_arith" prove_tac[]));
a(rewrite_tac def_thms THEN REPEAT strip_tac);
a(∃_tac⌜0⌝ THEN strip_tac THEN ∃_tac⌜2⌝ THEN PC_T1 "lin_arith" prove_tac[]);
save_pop_thm"independence_lemma1"
);
=TEX

We deal with irreflexive (resp. non-irreflexive) relations by reducing the required examples to a
reflexive (resp. non-reflexive) case. This occupies the next two lemmas, the proofs of which
show that this may be done by one construction in each case.
In the next lemma, we derive an irreflexive relation from a reflexive one by removing
the diagonal:

=SML
val ⦏independence_lemma2⦎ = (
set_goal ([], ⌜
∀m⦁ m ∈ {1; 2; 3; 4} ⇒
let	props m =
	if	m = 1
	then	Antisym
	else if	m = 2
	then	Trans
	else if	m = 3
	then	Trich
	else	WeakMinCond
in	(∃X : ℕ SET; $<< ⦁  Refl (X, $<<) ∧ ¬props m (X, $<<))
⇒	(∃X : ℕ SET; $<< ⦁ Irrefl (X, $<<) ∧ ¬props m (X, $<<))
⌝);
a(rewrite_tac[let_def]);
a(PC_T "sets_ext1"  (∀_tac THEN ⇒_tac) THEN_TRY all_var_elim_asm_tac
	THEN conv_tac (MAP_C ℕ_eq_conv) THEN rewrite_tac[]
	THEN DROP_ASMS_T discard_tac
	THEN rewrite_tac def_thms THEN REPEAT strip_tac
	THEN ∃_tac⌜X⌝ THEN ∃_tac⌜λi j:ℕ⦁¬i = j ∧ i << j⌝
	THEN rewrite_tac[] THEN contr_tac 
	THEN_TRY SOLVED_T
		(rename_tac[] THEN all_asm_ufc_tac[] THEN_TRY all_var_elim_asm_tac));
(* *** Goal "1" *** *) (* Trans *)
a(cases_tac⌜x = y⌝ THEN1 all_var_elim_asm_tac);
a(cases_tac⌜y = z⌝ THEN1 all_var_elim_asm_tac);
a(rename_tac[] THEN all_asm_ufc_tac[] THEN_TRY all_var_elim_asm_tac);
(* *** Goal "2" *** *) (* WeakMinCond *)
a(rename_tac[] THEN all_asm_ufc_tac[]);
a(spec_nth_asm_tac 4 ⌜x⌝ THEN all_asm_ufc_tac[]);
save_pop_thm"independence_lemma2"
);
=TEX

And in the proof of the next lemma, we make a non-irreflexive relation by adding
in the diagonal (a.k.a., forming the reflexive closure). The hypothesis of non-reflexivity
is not necessary, but makes the result easier to user later on.

=SML
val ⦏independence_lemma3⦎ = (
set_goal ([], ⌜
∀m⦁ m ∈ {1; 2; 3; 4} ⇒
let	props m =
	if	m = 1
	then	Antisym
	else if	m = 2
	then	Trans
	else if	m = 3
	then	Trich
	else	WeakMinCond
in	(∃X : ℕ SET; $<< ⦁  props m (X, $<<) ∧ ¬Refl(X, $<<))
⇒	(∃X : ℕ SET; $<< ⦁ props m (X, $<<) ∧ ¬Irrefl(X, $<<))
⌝);
a(rewrite_tac[let_def]);
a(PC_T "sets_ext1"  (∀_tac THEN ⇒_tac) THEN_TRY all_var_elim_asm_tac
	THEN conv_tac (MAP_C ℕ_eq_conv) THEN rewrite_tac[]
	THEN DROP_ASMS_T discard_tac
	THEN rewrite_tac def_thms THEN REPEAT strip_tac
	THEN ∃_tac⌜X⌝ THEN ∃_tac⌜λi j⦁i = j ∨ i << j⌝
	THEN rewrite_tac[] THEN contr_tac
	THEN_TRY SOLVED_T
		(rename_tac[] THEN TRY (all_asm_ufc_tac[]) THEN_TRY all_var_elim_asm_tac));
(* *** Goal "" *** *) (* WeakMinCond *)
a(rename_tac[] THEN all_asm_ufc_tac[]);
a(spec_nth_asm_tac 3 ⌜x'⌝ THEN  all_asm_ufc_tac[]);
save_pop_thm"independence_lemma3"
);
=TEX

We now do some {\it ad hoc} forward proof that sucks the various cases out of the lemmas.
Step through this interactively to see what is going on here (roughly, specialise the
$m$ and $n$ in the lemmas to each numeric value for which the lemma says something
useful and then simplify the results to give the existential assertion saying that
an ordered set  of a particular kind exists).

=SML
val l1 = pc_rule1  "sets_ext1" rewrite_rule[let_def] independence_lemma1;
val l2 = pc_rule1  "sets_ext1" rewrite_rule[let_def] independence_lemma2;
val l3 = pc_rule1  "sets_ext1" rewrite_rule[let_def] independence_lemma3;

fun spec_lit th = rewrite_rule[] o conv_rule (MAP_C ℕ_eq_conv) o switch ∀_elim  th;

val ns0_4 = dest_enum_set ⌜{0; 1; 2; 3; 4}⌝;
val ns1_4 = dest_enum_set ⌜{1; 2; 3; 4}⌝;

val ths1 = flat (map (fn t => map (spec_lit t) ns0_4) (map (spec_lit  l1) ns0_4));
val ths2 = map (spec_lit l2) ns1_4;
val ths3 = map (spec_lit l3) ns1_4;
=TEX

Now the independence theorem can be stated and proved.
The above lemmas give 44 of the 45 cases.
The only case we have not dealt with is the compatibility of reflexivity and
irreflexivity (for which the witness is the empty ordered set).
=SML
val ⦏independence_thm⦎ = (
set_goal ([], ⌜
∀m n⦁ m ∈ {0; 1; 2; 3; 4; 5} ∧ n ∈ {0; 1; 2; 3; 4; 5} ⇒
let	props m =
	if	m = 0
	then	Refl
	else if	m = 1
	then	Antisym
	else if	m = 2
	then	Trans
	else if	m = 3
	then	Trich
	else if	m = 4
	then	WeakMinCond
	else	Irrefl
in	(¬m = n  ⇒ ∃X : ℕ SET; $<<⦁ props m (X, $<<) ∧ ¬props n (X, $<<))
∧	(m < n ⇒ ∃X : ℕ SET; $<< ⦁ props m (X, $<<) ∧ props n (X, $<<))
⌝);
a(rewrite_tac[let_def]);
a(PC_T1 "sets_ext1" REPEAT strip_tac THEN_TRY all_var_elim_asm_tac
	THEN conv_tac (MAP_C ℕ_eq_conv) THEN rewrite_tac[]
	THEN bc_tac (ths2 @ ths3)
	THEN_TRY MAP_EVERY (TRY o accept_tac) ths1
	THEN_TRY (
	SOLVED_T (∃_tac⌜Universe⌝ THEN
		∃_tac⌜$≤:(ℕ→(ℕ→BOOL))⌝ THEN rewrite_tac[≤_less_lemma])
ORELSE
	SOLVED_T (∃_tac⌜Universe⌝ THEN
		∃_tac⌜$<:(ℕ→(ℕ→BOOL))⌝ THEN rewrite_tac[≤_less_lemma]))
	THEN ∃_tac⌜{}⌝ THEN rewrite_tac def_thms);
save_pop_thm"independence_thm"
);
=TEX

Finally, we do some forward proof to suck out a theorem that explicitly states
the 45 cases --- consult the theory listing or run through this interactively to
see the result. 

=SML
val i_th = pc_rule1  "sets_ext1" rewrite_rule[let_def] independence_thm;

val ns0_5 = dest_enum_set ⌜{0; 1; 2; 3; 4; 5}⌝;

val i_ths = flat (map (fn t => map (spec_lit t) ns0_5) (map (spec_lit  i_th) ns0_5));

val i_clauses = (pc_rule1"lin_arith" rewrite_rule[]) (list_∧_intro ( i_ths));

val ⦏independence_clauses⦎ = save_thm
	("independence_clauses",  conv_rule cnf_conv i_clauses);
=TEX
}%ignore

\newpage
\appendix
{%\HOLindexOff
\small
\include{ordered_sets.th}
}

\newpage
{%\HOLindexOff
\small
\include{ordered_sets_i.th}
}

\newpage
{%\HOLindexOff
\small
\include{U_orders.th}
}

\twocolumn[\section{INDEX}\label{INDEX}]
{\small\printindex}

=TEX

\end{document}
=SML
val use_alias_flag_value = set_flag ("pp_use_alias", true);
val was_line_len = set_int_control("thl_line_width", 14);
output_theory{out_file="ordered_sets.th.pp", theory="ordered_sets"};
open_theory "U_orders";
output_theory{out_file="U_orders.th.pp", theory="U_orders"};
open_theory "ordered_sets_i";
output_theory{out_file="ordered_sets_i.th.pp", theory="ordered_sets_i"};
val _ = set_int_control("thl_line_width", was_line_len);
val _ = set_flag ("pp_use_alias", use_alias_flag_value);
=TEX


