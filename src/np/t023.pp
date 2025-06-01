get_spec ⌜ManyOne⌝;
=IGN
$Id: t023.doc,v 1.18 2012/11/24 20:22:24 rbj Exp $
open_theory "GS";
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-ord", "'savedthm_cs_∃_proof"];
set_merge_pcs ["hol", "'wf_relp", "'wf_recp", "'GS1", "'savedthm_cs_∃_proof"];
set_merge_pcs ["hol1", "'gst-ax", "'gst-ord", "'savedthm_cs_∃_proof"];
=TEX
\documentclass[11pt,a4paper]{article}
%\usepackage{latexsym}
%\usepackage{ProofPower}
\usepackage{rbj}
\ftlinepenalty=9999
\usepackage{A4}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}
\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{A Higher Order Theory of Well-Founded Sets}
\makeindex
\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

\author{Roger Bishop Jones}
\date{\ }

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
An axiomatic development in ProofPower-HOL of a higher order theory of well-founded sets.
This is similar to a higher order ZFC strengthened by the assertion that every set is a member of some other set which is a (standard) model of ZFC.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2007/09/25

Last Change $ $Date: 2012/11/24 20:22:24 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t023.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t023.pdf}

$ $Id: t023.doc,v 1.18 2012/11/24 20:22:24 rbj Exp $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize

\end{centering}

\thispagestyle{empty}
\end{titlepage}
\newpage
\addtocounter{page}{1}
{\parskip=0pt\tableofcontents}

\newpage

\section{Introduction}

This document provides a theory which is used in various foundational studies, for example in my investigations into non well-founded set theories.
So its primary purpose has been pragmatic (in the context of some rather bizzarre objectives).

However, central to my philosophy of {\it metaphysical positivism} is an analytic method and the necessary philosophical and technical material necessary to explain and underpin, possibly to justify, the method and its applications.
This has lead me to begin an attempt at explaining this theory as part of that method, which has not progressed far enough as yet to be of much value.
This follows.

This document forms a part of a foundational architecture.

In this introduction I will say a few words about the architecture and how this document fits into it, sufficient to give some motivation for the choices I have made here,

The architecture addresses descriptive languages and their use in deductive reasoning.
Such languages and methods are seen as enabling, especially when appropriately supported by digital information processing, advances in the ways in which various important objectives may be realised.

To reason deductively using some language, it is important that the language has a definite abstract semantics, and this is best realised by defining suitable languages using a formal semantics.
Unfortunately, a semantic regress results.

Multiple strategems are advocated for the termination of semantic regress.
We are concerned here with just one of these.
This involves termination of formal semantic regress in an informal semantics, which is itself primarily vested in an abstract ontology.

We therefore present:

\begin{itemize}
\item an informal description of an abstract ontology
\item an inforaml account of the truth conditions of languages suitable for talking and reasoning about this ontology
\item an approximation to this language as a computer supported formalised axiomatic theory
\end{itemize}

\section{Ontology}

The aim is for a universal abstract ontology.
That is, one to which any other kind of abstract ontology may be reduced.
This is to provide the subject matter for languages which may be universal in senses to be discussed.

It is seems natural, for many involved in formal semantics, to regard set theory as a metalanguage of last resort, in which the formal semantics of any other language might be given.
To be sure negative results on definability are interpreted as forcing us to consider set theories as languages which come in a heirarchy of strengths, and only the family of languages rather than any particular member of that family has any hope of being universal.
This does not exhaust the objections which can be raised against the possibility that set theory (or any other language) can be universal.

\subsection{Semantic Universality}

The practical utility of a foundation for abstract semantics does not rest on its being universal, but it is nevertheless an interesting possibility.

The kind of universality concerned here is universality for defining abstract semantics.
A universal language in this sense would be one in which the semantics of any other language could be rendered.
To make this notion of unversality precise you would have to make precise the relevant notion of ``language'' concerned and that of ``semantics''.
I know of no single contender for this.

It may be worth mentioning a couple of examples.

It is conventional wisdom that the truth predicate of a language cannot be defined in that language.
This is certainly demonstrable for first order arithmetic, via formalisation of epeminides' paradox.
If this could be generalised, it would yield a negative result on the possibility of a universal language for abstract semantics, and it is sometimes construed as doing so.

\subsection{Well-Founded Collections}

{\quote
A well-founded set is any definite collection of well-founded sets. 
}

This is intended as an inductive definition, and hence that only those collections whose well-foundedness follows from this definition are well-founded sets.
The term ``definite'' is important, since without some such qualification the definition would yield a contradiction, since the collection of well-founded sets which it defines would then be itself a well-founded set, and would hence not be well-founded.

This tells us that the notion of well-founded set is essentially open ended, that the formation of well-founded sets never comes to an end, that the well-founded sets do not form a definite collection.
The meaning of definite is intended here to be very weak.
We do require a set to be a definite collection in the sense that every possible member of the set either is or is not a member. 
This is what we need for membership to be encapsulated in a boolean relationship.
The concept of well-founded set could be made definite by giving a stronger meaning to definite in the above definition, e.g. by incorporating a limit on the size or rank of a definite set.
But I know of no natural and intuitively plausible strengthening, limitations of size and rank seem quite arbitrary.

\section{Axioms}

\subsection{Introduction}

Galactic set theory is a set theory with ``galaxies'' (previously known as ``universes'') axiomatised in Higher Order Logic.

\subsubsection{Scope}
This document is mainly concerned with the axioms of galactic set theory, but includes in addition some definitions and theorems which might easily have been part of the axiomatisation.
In the usual first order axiomatisations of set theory, for example, the $Pair⋎g$ constructor is introduced axiomatically.
In this axiomatisation neither the empty set nor $Pair⋎g$ are primitive, they are introduced by definition once the axioms have been presented.
Same goes for separation and intersection.
The theory {\tt gst-ax} created by this document, consists of an axiomatic development of a well-founded set theory in ProofPower HOL, and is created as a child of {\tt basic-hol}.
This version of the theory is derived from a previous version in which ``pseudo-urelements'' were available, and in which the standard set theoretic vocabulary was used (which rendered the theory unusable in combination with the usual ProofPower HOL theory of sets).
Pseudo-urelements were dropped because I don't need them, and, however slight the complication they introduce, its not necessary.
To enable this theory to be used with the standard set theory (properties in set theoretic clothing) the volcabulary has been systematically subscripted with `g' (for galactic).

\subsubsection{Why Galactic?}

This document introduces Galactic Set Theory, which is similar to what has elsewhere been called Universal Set Theory (e.g. by Paul M. Cohn in his ``Universal Algebra'', but I dare say it came from somewhere else).
The ``universes'' in Cohn, and the galaxies here are mostly models of ZFC, except the smallest in which there is no infinite set.
The other main difference is that galactic set theory is formulated in higher order logic.

\subsection{Membership}

The first thing we do is to introduce a new ProofPower theory and, in that theory, the new TYPE SET together with the membership relation and a psuedo-urelement injection.

\subsubsection{The Type GS}

The sets under consideration will be the elements of a new type {\it GS} so the first thing we do is to introduce that new type.
GS is a {\it pure} {\it well-founded} set theory.
Since the theory will not be conservative, we make no attempt to relate the membership of "GS" to any of the types already available.

=SML
open_theory "rbjmisc";
force_new_theory "⦏gst-ax⦎";
new_parent "U_orders";
new_parent "wf_relp";
new_parent "wf_recp";
force_new_pc "⦏'gst-ax⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'gst-ax";
set_merge_pcs ["basic_hol", "'gst-ax"];
new_type ("⦏GS⦎", 0);
=TEX

\subsection{Membership}

The most important constant is membership, which is a relation over the sets.
We can't define this constant (in this context) so it is introduced as a new constant (about which nothing is asserted except its name and type) and its properties are introduced axiomatically. 

=SML
new_const ("⦏∈⋎g⦎", ⓣGS→GS→BOOL⌝);
declare_infix (230,"∈⋎g");
=TEX

I will possibly be making use of two different treatments of well-foundedness (from the theories {\it U\_orders}, and {\it wf\_relp}) and it may be helpful to establish the connection between them.

The following theorem does the trick:

=GFT
⦏UWellFounded_well_founded_thm⦎ =
	⊢ ∀ $<<⦁ UWellFounded $<< ⇔ well_founded $<<
=TEX

\ignore{
=SML
set_goal ([], ⌜∀$<<⦁ UWellFounded $<< ⇔ well_founded $<<⌝);
a (rewrite_tac [get_spec ⌜well_founded⌝, u_well_founded_induction_thm]);
val UWellFounded_well_founded_thm = save_pop_thm "UWellFounded_well_founded_thm";
=TEX
}%ignore

The axioms of extensionality and well-foundedness may be thought of as telling us what kind of thing a set is (later axioms tell us how many of these sets are to be found in our domain of discourse).

\subsubsection{Extensionality}

The most fundamental property of membership (or is it of sets?) is {\it extensionality}, which tells us what kind of thing a set is.
The axiom tells us that if two sets have the same elements then they are in fact the same set.

=SML
val ⦏gs_ext_axiom⦎ = new_axiom (["gs_ext_axiom"],
	⌜∀s t:GS⦁  s = t ⇔ ∀e⦁ e ∈⋎g s ⇔ e ∈⋎g t⌝);
=TEX

It follows from the definitions of {\it IsPue} and {\it IsSet} and {\it ue\_inj\_axiom} that nothing is both a set and a urelement, and that urelements are equal iff the values from which they were obtained under Pue are equal.

It is convenient to have a function which gives the extension of a GS set as a SET of GSs.

ⓈHOLCONST
│ ⦏X⋎g⦎ : GS → GS SET
├─────────
│ ∀s⦁ X⋎g s = {t | t ∈⋎g s}
■

\subsubsection{Well-Foundedness}

Wellfoundedness is asserted using the definition in the theory ``U\_orders'', which is conventional in asserting that each non-empty set has a minimal element.

=SML
val ⦏gs_wf_axiom⦎ = new_axiom (["gs_wf_axiom"], ⌜UWellFounded $∈⋎g⌝);
=TEX

=GFT
⦏gs_wf_thm1⦎ =		⊢ well_founded $∈⋎g
⦏gs_wf_min_thm⦎ =	⊢ ∀ x⦁ (∃ y⦁ y ∈⋎g x) ⇒ (∃ z⦁ z ∈⋎g x ∧ ¬ (∃ v⦁ v ∈⋎g z ∧ v ∈⋎g x))
⦏gs_wftc_thm⦎ =		⊢ well_founded (tc $∈⋎g)
=TEX

\ignore{
=SML
val gs_wf_thm1 = save_thm ("gs_wf_thm1", rewrite_rule [UWellFounded_well_founded_thm] gs_wf_axiom);
push_pc "sets_ext";

set_goal([], ⌜well_founded (tc $∈⋎g)⌝);
a (bc_tac [wf_tc_wf_thm]);
a (accept_tac gs_wf_thm1);
val gs_wftc_thm = save_pop_thm "gs_wftc_thm";

set_goal([], ⌜∀x⦁ (∃y⦁ y ∈⋎g x) ⇒ ∃z⦁ z ∈⋎g x ∧ ¬∃v⦁ v ∈⋎g z ∧ v ∈⋎g x⌝);
a (REPEAT strip_tac);
a (asm_tac (rewrite_rule [∀_elim ⌜$∈⋎g⌝ u_well_founded_def_thm] gs_wf_axiom));
a (spec_nth_asm_tac 1 ⌜{z | z ∈⋎g x}⌝);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "2" *** *)
a (∃_tac ⌜x'⌝ THEN contr_tac);
a (asm_prove_tac[]);
val gs_wf_min_thm = save_pop_thm "gs_wf_min_thm";
pop_pc();
=TEX
}%ignore

=SML
declare_infix (230, "∈⋎g⋏+");
=TEX

ⓈHOLCONST
│ $⦏∈⋎g⋏+⦎ : GS → GS → BOOL
├────────────
│ $∈⋎g⋏+ = tc $∈⋎g
■

=GFT
⦏gs_wftc_thm2⦎ =	⊢ well_founded $∈⋎g⋏+
⦏tc∈_incr_thm⦎ =		⊢ ∀ x y⦁ x ∈⋎g y ⇒ x ∈⋎g⋏+ y
⦏tc∈_cases_thm⦎ =	⊢ ∀ x y⦁ x ∈⋎g⋏+ y ⇔ (x ∈⋎g y ∨ (∃ z⦁ x ∈⋎g⋏+ z ∧ z ∈⋎g y))
⦏tc∈_trans_thm⦎ =	⊢ ∀ s t u⦁ s ∈⋎g⋏+ t ∧ t ∈⋎g⋏+ u ⇒ s ∈⋎g⋏+ u
=TEX

\ignore{
=SML
set_goal([], ⌜well_founded $∈⋎g⋏+⌝);
a (rewrite_tac [get_spec ⌜$∈⋎g⋏+⌝, gs_wftc_thm]);
val gs_wftc_thm2 = save_pop_thm "gs_wftc_thm2";

set_goal([], ⌜∀x y⦁ x ∈⋎g y ⇒ x ∈⋎g⋏+ y⌝);
a (rewrite_tac [get_spec ⌜$∈⋎g⋏+⌝] THEN REPEAT strip_tac THEN fc_tac [tc_incr_thm]);
val tc∈_incr_thm = save_pop_thm "tc∈_incr_thm";

set_goal([], ⌜∀ x y⦁ x ∈⋎g⋏+ y ⇔ x ∈⋎g y ∨ ∃z⦁ x ∈⋎g⋏+ z ∧ z ∈⋎g y⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$∈⋎g⋏+⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [tc_decomp_thm]);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [tc_incr_thm]);
(* *** Goal "3" *** *)
a (lemma_tac ⌜tc $∈⋎g z y⌝ THEN1 fc_tac [tc_incr_thm]);
a (all_ufc_tac [tran_tc_thm2]);
val tc∈_cases_thm = save_pop_thm "tc∈_cases_thm";

set_goal([], ⌜∀s t u⦁ s ∈⋎g⋏+ t ∧ t ∈⋎g⋏+ u ⇒ s ∈⋎g⋏+ u⌝);
a(REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$∈⋎g⋏+⌝, tran_tc_thm2]);
val tc∈_trans_thm = save_pop_thm "tc∈_trans_thm";
=TEX
}%ignore

The resulting induction principle (sometimes called Neotherian induction) is useful.

=GFT
⦏gs_wf_ind_thm⦎ =	⊢ ∀ p⦁ (∀ x⦁ (∀ y⦁ y ∈⋎g x ⇒ p y) ⇒ p x) ⇒ (∀ x⦁ p x)
⦏gs_cv_ind_thm⦎ =	⊢ ∀ p⦁ (∀ x⦁ (∀ y⦁ tc $∈⋎g y x ⇒ p y) ⇒ p x) ⇒ (∀ x⦁ p x)
⦏gs_cv_ind_thm2⦎ =	⊢ ∀ p⦁ (∀ x⦁ (∀ y⦁ y ∈⋎g⋏+ x ⇒ p y) ⇒ p x) ⇒ (∀ x⦁ p x)
=TEX

But we can get induction tactics directly from the well-foundedness theorems:

=SML
val ⦏GS_INDUCTION_T⦎ = WF_INDUCTION_T gs_wf_thm1;
val ⦏gs_induction_tac⦎ = wf_induction_tac gs_wf_thm1;
val ⦏GS_INDUCTION_T2⦎ = WF_INDUCTION_T gs_wftc_thm2;
val ⦏gs_induction_tac2⦎ = wf_induction_tac gs_wftc_thm2;
=TEX

\ignore{
=SML
val gs_wf_ind_thm = save_thm ("gs_wf_ind_thm",
	(rewrite_rule  [∀_elim ⌜$∈⋎g⌝ u_well_founded_induction_thm] gs_wf_axiom));

val gs_cv_ind_thm = save_thm ("gs_cv_ind_thm",
	(rewrite_rule  [rewrite_rule [UWellFounded_well_founded_thm]
	(∀_elim ⌜tc $∈⋎g⌝ u_well_founded_induction_thm)] gs_wftc_thm));

val gs_cv_ind_thm2 = save_thm ("gs_cv_ind_thm2",
	(prove_rule  [gs_cv_ind_thm, get_spec ⌜$∈⋎g⋏+⌝]
	⌜∀ p⦁ (∀ x⦁ (∀ y⦁ y ∈⋎g⋏+ x ⇒ p y) ⇒ p x) ⇒ (∀ x⦁ p x)⌝));
=TEX
}%ignore


=GFT
⦏wf_l1⦎ =	⊢ ∀ x:GS⦁ ¬ x ∈⋎g x
⦏wf_l2⦎ =	⊢ ∀ x y:GS⦁ ¬ (x ∈⋎g y ∧ y ∈⋎g x)
⦏wf_l3⦎ =	⊢ ∀ x y z:GS⦁ ¬ (x ∈⋎g y ∧ y ∈⋎g z ∧ z ∈⋎g x)
=TEX

\ignore{
=SML
set_goal([], ⌜
	∀ x:GS⦁ ¬ x ∈⋎g x
⌝);
=TEX

The proof uses well-founded transfinite induction over the membership relation.

=SML
a (asm_tac (gs_wf_ind_thm));
a (spec_nth_asm_tac 1 ⌜λx⦁ ¬ x ∈⋎g x⌝);
=GFT
(* *** Goal "1" *** *)

(*  3 *)  ⌜∀ s⦁ (∀ x⦁ (∀ y⦁ y ∈⋎g x ⇒ s y) ⇒ s x) ⇒ (∀ x⦁ s x)⌝
(*  2 *)  ⌜∀ y⦁ y ∈⋎g x ⇒ (λ x⦁ ¬ x ∈⋎g x) y⌝
(*  1 *)  ⌜¬ (λ x⦁ ¬ x ∈⋎g x) x⌝

(* ?⊢ *)  ⌜∀ x⦁ ¬ x ∈⋎g x⌝
=SML
a (swap_nth_asm_concl_tac 1
	THEN rewrite_tac[]
	THEN swap_nth_asm_concl_tac 1
	THEN ALL_ASM_FC_T (MAP_EVERY ante_tac) []
	THEN asm_rewrite_tac[]);
=GFT
(* *** Goal "2" *** *)

(*  2 *)  ⌜∀ s⦁ (∀ x⦁ (∀ y⦁ y ∈⋎g x ⇒ s y) ⇒ s x) ⇒ (∀ x⦁ s x)⌝
(*  1 *)  ⌜∀ x⦁ (λ x⦁ ¬ x ∈⋎g x) x⌝

(* ?⊢ *)  ⌜∀ x⦁ ¬ x ∈⋎g x⌝
=SML
a (strip_tac
	THEN swap_nth_asm_concl_tac 1
	THEN rewrite_tac[]
	THEN REPEAT strip_tac
	THEN ∃_tac ⌜x⌝
	THEN asm_rewrite_tac[]);
val wf_l1 = save_pop_thm "wf_l1";
=SML
set_goal([], ⌜∀ x y:GS⦁ ¬ (x ∈⋎g y ∧ y ∈⋎g x)⌝);
=TEX

=SML
a (asm_tac gs_wf_ind_thm);
a (spec_nth_asm_tac 1 ⌜λz⦁ ∀x⦁ ¬(x ∈⋎g z ∧ z ∈⋎g x)⌝);
(* *** Goal "1" *** *)
a (swap_nth_asm_concl_tac 1
	THEN rewrite_tac[]
	THEN swap_nth_asm_concl_tac 1
	THEN ALL_ASM_FC_T (MAP_EVERY ante_tac) []
	THEN asm_rewrite_tac[]);
a (strip_tac
	THEN spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "2" *** *)
a (strip_tac
	THEN swap_nth_asm_concl_tac 1
	THEN rewrite_tac[]
	THEN REPEAT strip_tac
	THEN ∃_tac ⌜y⌝
	THEN REPEAT strip_tac
	THEN ∃_tac ⌜x⌝
	THEN REPEAT strip_tac);
val wf_l2 = save_pop_thm "wf_l2";
=TEX

=SML
set_goal([], ⌜∀ x y z:GS⦁ ¬ (x ∈⋎g y ∧ y ∈⋎g z ∧ z ∈⋎g x)⌝);
=TEX

=SML
a (asm_tac gs_wf_ind_thm);
a (spec_nth_asm_tac 1 ⌜λz⦁ ∀x y⦁ ¬(x ∈⋎g y ∧ y ∈⋎g z ∧ z ∈⋎g x)⌝);
(* *** Goal "1" *** *)
a (swap_nth_asm_concl_tac 1
	THEN rewrite_tac[]
	THEN swap_nth_asm_concl_tac 1
	THEN ALL_ASM_FC_T (MAP_EVERY ante_tac) []
	THEN asm_rewrite_tac[]);
a (strip_tac
	THEN list_spec_nth_asm_tac 1 [⌜x⌝, ⌜x''⌝]);
(* *** Goal "2" *** *)
a (REPEAT ∀_tac);
a (SPEC_NTH_ASM_T 1 ⌜z:GS⌝ ante_tac);
a (rewrite_tac[]);
a (strip_tac THEN asm_rewrite_tac[]);
val wf_l3 = save_pop_thm "wf_l3";
=TEX
}%ignore

\subsection{The Ontology Axiom}

The remaining axioms are intended to ensure that the subset is a large and well-rounded subset of the cumulative heirarchy.
This is to be accomplished by defining a Galaxy as a set satisfying certain closure properties and then asserting that every set is a member of some Galaxy.
It is convenient to introduce new constants and axioms for each of the Galactic closure properties before asserting the existence of the Galaxies.

Here we define the subset relation and assert the existence of powersets and unions.

\subsubsection{Subsets}

A subset s of t is a set all of whose members are also members of t.

=SML
declare_infix (230,"⊆⋎g");
declare_infix (230,"⊂⋎g");
=TEX

ⓈHOLCONST
│ $⦏⊆⋎g⦎ : GS → GS → BOOL
├───────────
│ ∀s t⦁ s ⊆⋎g t ⇔ ∀e⦁ e ∈⋎g s ⇒ e ∈⋎g t
■

ⓈHOLCONST
│ $⦏⊂⋎g⦎ : GS → GS → BOOL
├───────────
│ ∀s t⦁ s ⊂⋎g t ⇔ s ⊆⋎g t ∧ ¬ t ⊆⋎g s
■

=GFT
⦏⊆⋎g_thm⦎ =			⊢ ∀ s t⦁ s ⊆⋎g t ⇔ (∀ e⦁ e ∈⋎g s ⇒ e ∈⋎g t)
⦏⊆⋎g_eq_thm⦎ =		⊢ ∀ A B⦁ A = B ⇔ A ⊆⋎g B ∧ B ⊆⋎g A
⦏⊆⋎g_refl_thm⦎ =		⊢ ∀ A⦁ A ⊆⋎g A
⦏∈⋎g⊆⋎g_thm⦎ =		⊢ ∀ e A B⦁ e ∈⋎g A ∧ A ⊆⋎g B ⇒ e ∈⋎g B
⦏⊆⋎g_trans_thm⦎ =	⊢ ∀ A B C⦁ A ⊆⋎g B ∧ B ⊆⋎g C ⇒ A ⊆⋎g C
⦏not_psub_thm⦎ =	⊢ ∀ x⦁ ¬ x ⊂⋎g x
=TEX

\ignore{
=SML
val ⊆⋎g_thm = get_spec ⌜$⊆⋎g⌝;
val ⊆⋎g_eq_thm = save_thm ("⊆⋎g_eq_thm", 
	prove_rule [get_spec ⌜$⊆⋎g⌝, gs_ext_axiom]
	⌜∀A B⦁ A = B ⇔ A ⊆⋎g B ∧ B ⊆⋎g A⌝);
val ⊆⋎g_refl_thm = save_thm ("⊆⋎g_refl_thm", 
	prove_rule [get_spec ⌜$⊆⋎g⌝]
	⌜∀A⦁ A ⊆⋎g A⌝);
val ∈⋎g⊆⋎g_thm = save_thm ("∈⋎g⊆⋎g_thm",
	prove_rule [get_spec ⌜$⊆⋎g⌝]
	⌜∀e A B⦁ e ∈⋎g A ∧ A ⊆⋎g B ⇒ e ∈⋎g B⌝);
val ⊆⋎g_trans_thm = save_thm ("⊆⋎g_trans_thm",
	prove_rule [get_spec ⌜$⊆⋎g⌝]
	⌜∀A B C⦁ A ⊆⋎g B ∧ B ⊆⋎g C ⇒ A ⊆⋎g C⌝);

set_goal ([], ⌜∀x⦁ ¬ x ⊂⋎g x⌝);
a (rewrite_tac [get_spec ⌜$⊂⋎g⌝]);
a (REPEAT strip_tac);
val not_psub_thm = save_pop_thm "not_psub_thm";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏⊆⋎g_closed⦎ : GS → BOOL
├────────────
│ ∀s⦁ ⊆⋎g_closed s ⇔ ∀e f⦁ e ∈⋎g s ∧ f ⊆⋎g e ⇒ f ∈⋎g s
■


\subsubsection{The Ontology Axiom}

We now specify with a single axiom the closure requirements which ensure that our universe is adequately populated.
The ontology axiom states that every set is a member of some galaxy which is transitive and closed under formation of powersets and unions and under replacement.

The formulation of replacement only makes membership of a galaxy dependent on the range being contained in the galaxy, it asserts unconditionally the sethood of the image of a set under a functional relation.

=SML
val ⦏Ontology_axiom⦎ =
	new_axiom (["Ontology_axiom"],
⌜ ∀s⦁
	∃g⦁ s ∈⋎g g
∧
	∀t⦁ t ∈⋎g g ⇒ t ⊆⋎g g
	∧ (∃p⦁ (∀v⦁ v ∈⋎g p ⇔ v ⊆⋎g t) ∧ p ∈⋎g g)
	∧ (∃u⦁ (∀v⦁ v ∈⋎g u ⇔ ∃w⦁ v ∈⋎g w ∧ w ∈⋎g t) ∧ u ∈⋎g g)
	∧ (∀rel⦁ ManyOne rel ⇒
		(∃r⦁ (∀v⦁ v ∈⋎g r ⇔ ∃w ⦁ w ∈⋎g t ∧ rel w v) ∧
			(r ⊆⋎g g ⇒ r ∈⋎g g)))⌝
);
=TEX

\subsection{PowerSets and Union}

Here we define the powerset and union operators.

\subsubsection{PowerSets}

\ignore{
=SML
set_goal([],⌜∃ ℙ⋎g⦁ ∀s t:GS⦁ t ∈⋎g ℙ⋎g s ⇔ t ⊆⋎g s⌝);
a (prove_∃_tac THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜s'⌝ (Ontology_axiom)));
a (spec_nth_asm_tac 1 ⌜s'⌝);
a (∃_tac ⌜p⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏ℙ⋎g⦎: GS → GS
├─────────────
│ ∀s t:GS⦁ t ∈⋎g ℙ⋎g s ⇔ t ⊆⋎g s
■

=GFT
⦏s∈ℙs_thm⦎ =	⊢ ∀ s⦁ s ∈⋎g ℙ⋎g s
⦏stc∈ℙs_thm⦎ =	⊢ ∀ s⦁ s ∈⋎g⋏+ ℙ⋎g s
=TEX

\ignore{
=SML
set_goal([], ⌜∀s⦁ s ∈⋎g ℙ⋎g s⌝);
a (rewrite_tac [get_spec ⌜ℙ⋎g⌝, ⊆⋎g_thm]);
val s∈ℙs_thm = save_pop_thm "s∈ℙs_thm";

set_goal([], ⌜∀s⦁ s ∈⋎g⋏+ ℙ⋎g s⌝);
a (rewrite_tac [get_spec ⌜$∈⋎g⋏+⌝]);
a (asm_tac s∈ℙs_thm THEN ufc_tac [tc_incr_thm]);
val stc∈ℙs_thm = save_pop_thm "stc∈ℙs_thm";
=TEX
}%ignore

\subsubsection{Union}

\ignore{
=SML
set_goal([],⌜∃⋃⋎g⦁ ∀s t⦁ t ∈⋎g ⋃⋎g s ⇔ ∃e⦁ t ∈⋎g e ∧ e ∈⋎g s⌝);
a (prove_∃_tac THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜s'⌝ Ontology_axiom));
a (spec_nth_asm_tac 1 ⌜s'⌝);
a (∃_tac ⌜u⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏⋃⋎g⦎: GS → GS
├───────────
│ ∀s t⦁ t ∈⋎g ⋃⋎g s ⇔ ∃e⦁ t ∈⋎g e ∧ e ∈⋎g s
■

=GFT
⦏∈⋎g⋃⋎g_thm⦎ =	⊢ ∀s t:GS⦁ t ∈⋎g s ⇒ t ⊆⋎g ⋃⋎g s
=TEX

\ignore{
=SML
val ∈⋎g⋃⋎g_thm = save_thm ("∈⋎g⋃⋎g_thm",
	prove_rule [get_spec ⌜⋃⋎g⌝, ⊆⋎g_thm]
	⌜∀s t:GS⦁ t ∈⋎g s ⇒ t ⊆⋎g ⋃⋎g s⌝);
=TEX
}%ignore

\subsection{Relational Replacement}

The constant RelIm is defined for relational replacement.

\subsubsection{RelIm}

\ignore{
=SML
set_goal([],⌜∃RelIm⦁ ∀rel s t⦁ ManyOne rel ⇒ (t ∈⋎g RelIm rel s ⇔ ∃e⦁ e ∈⋎g s ∧ rel e t)⌝);
a (prove_∃_tac THEN REPEAT strip_tac);
a (strip_asm_tac (∀_elim ⌜s'⌝ Ontology_axiom));
a (spec_nth_asm_tac 1 ⌜s'⌝);
a (spec_nth_asm_tac 1 ⌜rel'⌝);
a (asm_rewrite_tac[]);
a (∃_tac ⌜r⌝ THEN strip_tac THEN strip_tac THEN asm_rewrite_tac[]);
a (∃_tac ⌜r⌝ THEN strip_tac THEN strip_tac THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏RelIm⦎: (GS → GS → BOOL) → GS → GS
├───────────────
│ ∀rel s t⦁ ManyOne rel ⇒ (t ∈⋎g RelIm rel s ⇔ ∃e⦁ e ∈⋎g s ∧ rel e t)
■

\subsection{Separation}

Separation is introduced by conservative extension.

The specification of {\it Sep} which follows is introduced after proving that it is satisfied by a term involving the use of $RelIm$.

\ignore{
=SML
set_goal([],⌜∃Sep⦁ ∀s p e⦁
e ∈⋎g (Sep s p) ⇔ e ∈⋎g s ∧ p e
⌝);
a (prove_∃_tac THEN REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim [⌜s'⌝] (Ontology_axiom)));
a (lemma_tac ⌜∃rel⦁ rel = λx y⦁ p' x ∧ y = x⌝
	THEN1 prove_∃_tac);
a (lemma_tac ⌜ManyOne rel⌝
	THEN1 asm_rewrite_tac [get_spec ⌜ManyOne rel⌝]);
(* *** Goal "1" *** *)
a (REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜RelIm rel s'⌝);
a (⇔_FC_T asm_rewrite_tac [get_spec ⌜RelIm⌝]);
a (prove_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

This higher order formulation of separation is accomplished by defining a new constant which takes a property of sets {\it p} and a set {\it s} and returns the subset of {\it s} consisting of those elements which satisfy {\it p}.

ⓈHOLCONST
│ ⦏Sep⦎ : GS → (GS → BOOL) → GS
├───────────
│ ∀s p e⦁ e ∈⋎g (Sep s p) ⇔ e ∈⋎g s ∧ p e
■

\ignore{
=SML
val Sep_thm = get_spec ⌜Sep⌝;
fun add_pc_thms pc thms =
		(add_rw_thms thms pc;
		add_sc_thms thms pc;
 		add_st_thms thms pc);
add_pc_thms "'gst-ax" [Sep_thm, ⊆⋎g_refl_thm];
add_rw_thms [stc∈ℙs_thm] "'gst-ax";
add_sc_thms [stc∈ℙs_thm] "'gst-ax";
set_merge_pcs ["basic_hol", "'gst-ax"];
=TEX
}%ignore

=GFT
⦏Sep_sub_thm⦎ =		⊢ ∀ s p⦁ Sep s p ⊆⋎g s
⦏Sep_sub_thm2⦎ =	⊢ ∀ s p e⦁ e ∈⋎g Sep s p ⇒ e ∈⋎g s
⦏Sep_∈_ℙ_thm⦎ =	⊢ ∀ s p⦁ Sep s p ∈⋎g ℙ⋎g s
⦏Sep_⊆_thm⦎ =		⊢ ∀ s t⦁ t ⊆⋎g s ⇒ Sep s (CombC $∈⋎g t) = t
=TEX

\ignore{
=SML
set_goal([], ⌜∀s p⦁ (Sep s p) ⊆⋎g s⌝);
a (rewrite_tac [get_spec ⌜$⊆⋎g⌝, get_spec ⌜Sep⌝]
	THEN REPEAT strip_tac);
val Sep_sub_thm = save_pop_thm "Sep_sub_thm";

val Sep_sub_thm2 = save_thm ("Sep_sub_thm2", pure_rewrite_rule [get_spec ⌜$⊆⋎g⌝] Sep_sub_thm);

set_goal([], ⌜∀s p⦁ (Sep s p) ∈⋎g ℙ⋎g s⌝);
a (rewrite_tac [get_spec ⌜ℙ⋎g⌝, Sep_sub_thm]);
val Sep_∈_ℙ_thm = save_pop_thm "Sep_∈_ℙ_thm";

set_goal([], ⌜∀s t⦁ t ⊆⋎g s ⇒ Sep s (CombC $∈⋎g t) = t⌝);
a (strip_tac THEN rewrite_tac [gs_ext_axiom, get_spec ⌜$⊆⋎g⌝, get_spec ⌜Sep⌝, get_spec ⌜CombC⌝]
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
val Sep_⊆_thm = save_pop_thm "Sep_⊆_thm";
=TEX
}%ignore

\subsection{Galaxies}

A Galaxy is a transitive set closed under powerset formation, union and replacement.
The Ontology axioms ensures that every set is a member of some galaxy.
Here we define a galaxy constructor and establish some of its properties.

\subsubsection{Definition of Galaxy}

First we define the property of being a galaxy.

ⓈHOLCONST
│ ⦏galaxy⦎: GS → BOOL
├───────────
│ ∀s⦁
│	galaxy s ⇔ (∃x⦁ x ∈⋎g s)
│	∧ ∀t⦁ t ∈⋎g s
│		⇒ t ⊆⋎g s
│		∧ ℙ⋎g t ∈⋎g s
│		∧ ⋃⋎g t ∈⋎g s
│		∧ (∀rel⦁ ManyOne rel
│			⇒ RelIm rel t ⊆⋎g s
│			⇒ RelIm rel t ∈⋎g s)
■

=GFT
⦏galaxies_∃_thm⦎ =
	⊢ ∀s⦁ ∃g⦁ s ∈⋎g g ∧ galaxy g
=TEX

\ignore{
=SML
set_goal([],⌜∀s⦁ ∃g⦁ s ∈⋎g g ∧ galaxy g⌝);
a (strip_tac THEN rewrite_tac [get_spec ⌜galaxy⌝]);
a (strip_asm_tac (∀_elim ⌜s⌝ Ontology_axiom));
a (∃_tac ⌜g⌝ THEN asm_rewrite_tac []);
a (strip_tac
	THEN1 (∃_tac ⌜s⌝ THEN strip_tac)
	THEN strip_tac THEN strip_tac);
a (spec_nth_asm_tac 2 ⌜t⌝);
a (asm_rewrite_tac[] THEN strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜ℙ⋎g t = p⌝
	THEN1 (rewrite_tac [get_spec ⌜ℙ⋎g⌝, gs_ext_axiom]
		THEN strip_tac
		THEN asm_rewrite_tac[])
	);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (strip_tac);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜⋃⋎g t = u⌝
	THEN1 (rewrite_tac [get_spec ⌜⋃⋎g⌝, gs_ext_axiom]
		THEN strip_tac
		THEN asm_rewrite_tac[])
	);
a (asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (strip_tac THEN strip_tac);
a (spec_nth_asm_tac 2 ⌜rel⌝);
(* *** Goal "2.2.1" *** *)
a (lemma_tac ⌜RelIm rel t = r⌝);
(* *** Goal "2.2.1.1" *** *)
a (rewrite_tac [gs_ext_axiom]);
a (⇔_FC_T asm_rewrite_tac [get_spec ⌜RelIm⌝]);
(* *** Goal "2.2.1.2" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a (lemma_tac ⌜RelIm rel t = r⌝);
(* *** Goal "2.2.2.1" *** *)
a (rewrite_tac [gs_ext_axiom]);
a (⇔_FC_T asm_rewrite_tac [get_spec ⌜RelIm⌝]);
(* *** Goal "2.2.2.2" *** *)
a (asm_rewrite_tac[]);
val galaxies_∃_thm = save_pop_thm "galaxies_∃_thm";
=TEX
}%ignore

\subsubsection{Definition of Gx}

{\it Gx} is a function which maps each set onto the smallest galaxy of which it is a member.

\ignore{
=SML
set_goal([],⌜∃ Gx⦁ ∀s t⦁ t ∈⋎g Gx s ⇔ ∀g⦁ galaxy g ∧ s ∈⋎g g ⇒ t ∈⋎g g⌝);
a (prove_∃_tac THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜s'⌝ galaxies_∃_thm));
a (∃_tac ⌜Sep g (λh⦁ ∀ i⦁ galaxy i ∧ s' ∈⋎g i ⇒ h ∈⋎g i)⌝);
a (rewrite_tac [get_spec ⌜Sep⌝]);
a (REPEAT strip_tac THEN_TRY all_asm_fc_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Gx⦎: GS → GS
├────────────
│ ∀s t⦁ t ∈⋎g Gx s ⇔ ∀g⦁ galaxy g ∧ s ∈⋎g g ⇒ t ∈⋎g g
■

Each set is in its smallest enclosing galaxy, which is of course a galaxy and is contained in any other galaxy of which that set is a member:

=GFT
⦏t_in_Gx_t_thm⦎ =		⊢ ∀ t⦁ t ∈⋎g Gx t
⦏tc∈_Gx_thm⦎ =			⊢ ∀ t⦁ t ∈⋎g⋏+ Gx t
⦏galaxy_Gx⦎ =			⊢ ∀s⦁ galaxy (Gx s)
⦏Gx_⊆⋎g_galaxy⦎ =		⊢ ∀s g⦁ galaxy g ∧ s ∈⋎g g  ⇒ (Gx s) ⊆⋎g g
=TEX

\ignore{
=SML
set_goal([], ⌜∀t⦁ t ∈⋎g Gx t⌝);
a (prove_tac [get_spec ⌜Gx⌝]);
val t_in_Gx_t_thm = save_pop_thm "t_in_Gx_t_thm";

val tc∈_Gx_thm = 
	let val [thm] = ufc_rule [tc∈_incr_thm] [t_in_Gx_t_thm]
	in save_thm("tc∈_Gx_thm", thm)
	end;
=TEX

Now we prove that Gx s is a subset of any galaxy containing s.

=SML
set_goal([],⌜∀s g⦁ galaxy g ∧ s ∈⋎g g  ⇒ (Gx s) ⊆⋎g g⌝);
a (rewrite_tac[get_spec ⌜$⊆⋎g⌝, get_spec ⌜Gx⌝]);
a (REPEAT strip_tac THEN all_asm_fc_tac[]);
val Gx_⊆⋎g_galaxy = save_pop_thm "Gx_⊆⋎g_galaxy";
=TEX

Now we prove that Gx always yeilds a galaxy.

=SML
set_goal([],⌜∀s⦁ galaxy (Gx s)⌝);
a (rewrite_tac (map get_spec [⌜galaxy⌝]));
a (REPEAT_N 2 strip_tac
	THEN1 (∃_tac ⌜s⌝
		THEN rewrite_tac [get_spec ⌜Gx⌝]
		THEN REPEAT strip_tac)
	THEN strip_tac
	THEN rewrite_tac [get_spec ⌜Gx⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac (map get_spec [⌜$⊆⋎g⌝,⌜Gx⌝])
	THEN REPEAT strip_tac);
a (all_asm_fc_tac [get_spec ⌜galaxy⌝]);
a (all_asm_fc_tac [get_spec ⌜galaxy⌝]);
a (asm_ante_tac ⌜t ⊆⋎g g⌝
	THEN rewrite_tac [get_spec ⌜$⊆⋎g⌝]
	THEN strip_tac
	THEN REPEAT (asm_fc_tac[]));
(* *** Goal "2" *** *)
a (all_asm_fc_tac [get_spec ⌜galaxy⌝]);
a (all_asm_fc_tac [get_spec ⌜galaxy⌝]);
(* *** Goal "3" *** *)
a (all_asm_fc_tac [get_spec ⌜galaxy⌝]);
a (all_asm_fc_tac [get_spec ⌜galaxy⌝]);
(* *** Goal "4" *** *)
a (all_asm_fc_tac[]);
a (asm_fc_tac [list_∀_elim [⌜g⌝] (get_spec ⌜galaxy⌝)]);
a (REPEAT (all_asm_fc_tac [Gx_⊆⋎g_galaxy, ⊆⋎g_trans_thm]));
val galaxy_Gx = save_pop_thm "galaxy_Gx";
=TEX
}%ignore

\subsubsection{Galaxy Closure}

The galaxy axiom asserts that a Galaxy is transitive and closed under construction of powersets, distributed union and replacement.
Galaxies are also closed under most other ways of constructing sets, and we need to demonstrate these facts systematically as the theory is developed.

ⓈHOLCONST
│ ⦏transitive⦎ : GS → BOOL
├────────────
│ ∀s⦁ transitive s ⇔ ∀e⦁ e ∈⋎g s ⇒ e ⊆⋎g s
■

=GFT
⦏GalaxiesTransitive_thm⦎ =	⊢ ∀s⦁ galaxy s ⇒ transitive s
=TEX

\ignore{
=SML
set_goal([],⌜∀s⦁ galaxy s ⇒ transitive s⌝);
a (rewrite_tac [get_spec ⌜transitive⌝]);
a (REPEAT strip_tac
	THEN fc_tac [get_spec⌜galaxy⌝]
	THEN asm_fc_tac[]);
val GalaxiesTransitive_thm = save_pop_thm "GalaxiesTransitive_thm";
=TEX
}%ignore

=GFT
⦏GCloseℙ_thm⦎ =	⊢ ∀ g⦁ galaxy g ⇒ (∀ s⦁ s ∈⋎g g ⇒ ℙ⋎g s ∈⋎g g)
⦏GClose⋃_thm⦎ =	⊢ ∀ g⦁ galaxy g ⇒ (∀ s⦁ s ∈⋎g g ⇒ ⋃⋎g s ∈⋎g g)
⦏GCloseSep_thm⦎ =	⊢ ∀ g⦁ galaxy g ⇒ (∀s⦁ s ∈⋎g g ⇒ ∀p⦁ Sep s p ∈⋎g g)
⦏GClose_⊆_thm⦎ =	⊢ ∀ g⦁ galaxy g ⇒ (∀ s⦁ s ∈⋎g g ⇒ (∀ t⦁ t ⊆⋎g s ⇒ t ∈⋎g g))
=TEX

\ignore{
=SML
set_goal([],⌜∀g⦁ galaxy g ⇒ ∀s⦁ s ∈⋎g g ⇒ ℙ⋎g s ∈⋎g g⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜galaxy⌝]);
a (asm_fc_tac[]);
val GCloseℙ_thm = pop_thm ();

set_goal([],⌜∀g⦁ galaxy g ⇒ ∀s⦁ s ∈⋎g g ⇒ ⋃⋎g s ∈⋎g g⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜galaxy⌝]);
a (asm_fc_tac[]);
val GClose⋃_thm = pop_thm ();

set_goal([],⌜∀g⦁ galaxy g ⇒ ∀s⦁ s ∈⋎g g ⇒ ∀p⦁ Sep s p ∈⋎g g⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜galaxy⌝]);
a (lemma_tac ⌜∃rel⦁ rel = λx y⦁ p x ∧ y = x⌝
	THEN1 prove_∃_tac);
a (lemma_tac ⌜ManyOne rel⌝
	THEN1 asm_rewrite_tac [get_spec ⌜ManyOne rel⌝]);
(* *** Goal "1" *** *)
a (REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜Sep s p = RelIm rel s ∧ RelIm rel s ∈⋎g g⌝);
(* *** Goal "2.1" *** *)
a (list_spec_nth_asm_tac 7 [⌜s⌝,⌜rel⌝]);
(* *** Goal "2.1.1" *** *)
a (SWAP_NTH_ASM_CONCL_T 1 discard_tac);
a (rewrite_tac[get_spec ⌜$⊆⋎g⌝]);
a (⇔_FC_T rewrite_tac [get_spec ⌜RelIm⌝]);
a (asm_rewrite_tac[]);
a (REPEAT strip_tac THEN asm_rewrite_tac[]);
a (SPEC_NTH_ASM_T 7 ⌜s⌝ ante_tac);
a (rewrite_tac[get_spec ⌜$⊆⋎g⌝]);
a (REPEAT strip_tac THEN asm_fc_tac[]);
(* *** Goal "2.1.2" *** *)
a (REPEAT strip_tac THEN rewrite_tac[gs_ext_axiom]);
a (⇔_FC_T asm_rewrite_tac [get_spec ⌜RelIm⌝]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (once_asm_rewrite_tac[] THEN strip_tac);
val GCloseSep_thm = pop_thm {};

set_goal([],⌜∀g⦁ galaxy g ⇒ ∀s⦁ s ∈⋎g g ⇒ ∀t⦁ t ⊆⋎g s ⇒ t ∈⋎g g⌝);
a (REPEAT strip_tac);
a (fc_tac [GCloseSep_thm, GCloseℙ_thm]);
a (asm_ufc_tac[]);
a (SPEC_NTH_ASM_T 1 ⌜λx⦁ x ∈⋎g t⌝ ante_tac);
a (LEMMA_T ⌜(λ x⦁ x ∈⋎g t) = CombC $∈⋎g t⌝ rewrite_thm_tac
	THEN1 rewrite_tac [get_spec ⌜CombC⌝]);
a (FC_T rewrite_tac [Sep_⊆_thm]);
val GClose_⊆_thm = pop_thm ();
=TEX
}%ignore

=GFT
⦏GClose_fc_clauses⦎ =
   ⊢ ∀ g
     ⦁ galaxy g
         ⇒ (∀ s
         ⦁ s ∈⋎g g
             ⇒ ℙ⋎g s ∈⋎g g
               ∧ ⋃⋎g s ∈⋎g g
               ∧ (∀ p⦁ Sep s p ∈⋎g g)
               ∧ (∀ t⦁ t ⊆⋎g s ⇒ t ∈⋎g g))
=TEX

\ignore{
=SML
set_goal([], ⌜∀g⦁ galaxy g ⇒ ∀s⦁ s ∈⋎g g
	⇒ ℙ⋎g s ∈⋎g g
	∧ ⋃⋎g s ∈⋎g g
	∧ (∀p⦁ Sep s p ∈⋎g g)
	∧ (∀t⦁ t ⊆⋎g s ⇒ t ∈⋎g g)⌝);
a (REPEAT strip_tac
	THEN all_fc_tac [GCloseℙ_thm, GClose⋃_thm, GCloseSep_thm, GClose_⊆_thm]
	THEN asm_rewrite_tac[]);
val GClose_fc_clauses = save_pop_thm "GClose_fc_clauses";
=TEX
}%ignore

=GFT
⦏tc∈⋎g_lemma⦎ =		⊢ ∀ s e⦁ e ∈⋎g⋏+ s ⇒ (∀ t⦁ transitive t ∧ s ⊆⋎g t ⇒ e ∈⋎g t)
⦏GClose_tc∈⋎g_thm⦎ =	⊢ ∀ s g⦁ galaxy g ⇒ s ∈⋎g⋏+ g ⇒ s ∈⋎g g
=TEX

\ignore{
=SML
set_goal([], ⌜∀s e⦁ e ∈⋎g⋏+ s ⇒ ∀t⦁ transitive t ∧ s ⊆⋎g t ⇒ e ∈⋎g t⌝);
a (strip_tac THEN rewrite_tac [get_spec ⌜transitive⌝, get_spec ⌜$∈⋎g⋏+⌝]);
a (gs_induction_tac ⌜s⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac[tc_decomp_thm, get_spec ⌜$⊆⋎g⌝]);
(* *** Goal "1.1" *** *)
a (asm_fc_tac []);
(* *** Goal "1.2" *** *)
a (lemma_tac ⌜tc $∈⋎g z t⌝ THEN1 fc_tac [tc_incr_thm]);
a (spec_nth_asm_tac 8 ⌜z⌝);
a (spec_nth_asm_tac 1 ⌜s⌝);
(* *** Goal "1.2.1" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "1.2.2" *** *)
a (lemma_tac ⌜z ⊆⋎g t'⌝ THEN1 (REPEAT (asm_fc_tac[])));
a (all_asm_fc_tac[]);
val tc∈⋎g_lemma = pop_thm();

set_goal([], ⌜∀s g⦁ galaxy g ⇒ (s ∈⋎g⋏+ g ⇒ s ∈⋎g g)⌝);
a (REPEAT strip_tac);
a (fc_tac [GalaxiesTransitive_thm]);
a (fc_tac [tc∈⋎g_lemma]);
a (asm_fc_tac []);
a (POP_ASM_T ante_tac THEN rewrite_tac[]);
val GClose_tc∈⋎g_thm = save_pop_thm "GClose_tc∈⋎g_thm";
=TEX
}%ignore

=GFT
⦏Gx_mono_thm⦎ =	⊢ ∀s t⦁ s ⊆⋎g t ⇒ Gx s ⊆⋎g Gx t
⦏Gx_mono_thm2⦎ =	⊢ ∀s t⦁ s ∈⋎g t ⇒ Gx s ⊆⋎g Gx t
=TEX

=GFT
⦏Gx_trans_thm⦎ =	⊢ ∀ s⦁ transitive (Gx s)
⦏Gx_trans_thm2⦎ =	⊢ ∀ s t⦁ s ∈⋎g t ⇒ s ∈⋎g Gx t
⦏Gx_trans_thm3⦎ =	⊢ ∀ s t u⦁ s ∈⋎g t ∧ t ∈⋎g Gx u ⇒ s ∈⋎g Gx u
⦏t_sub_Gx_t_thm⦎ =	⊢ ∀ t⦁ t ⊆⋎g Gx t
=TEX

=GFT
⦏Gx_mono_thm3⦎ =	⊢ ∀ s t⦁ s ⊆⋎g t ⇒ s ⊆⋎g Gx t
⦏Gx_mono_thm4⦎ =	⊢ ∀ s t⦁ s ⊆⋎g t ⇒ s ∈⋎g Gx t
=TEX

\ignore{
=SML
set_goal([], ⌜∀s t⦁ s ⊆⋎g t ⇒ Gx s ⊆⋎g Gx t⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜galaxy (Gx t)⌝ THEN1 rewrite_tac [galaxy_Gx]);
a (lemma_tac ⌜s ∈⋎g (Gx t)⌝);
(* *** Goal "1" *** *)
a (lemma_tac ⌜t ∈⋎g Gx t⌝
	THEN1 rewrite_tac [t_in_Gx_t_thm]);
a (fc_tac [GCloseSep_thm]);
a (LIST_SPEC_NTH_ASM_T 1 [⌜t⌝, ⌜λx⦁ x ∈⋎g s⌝] ante_tac);
a (lemma_tac ⌜Sep t (λ x⦁ x ∈⋎g s) = s⌝
	THEN1 (once_rewrite_tac[gs_ext_axiom]
		THEN rewrite_tac[get_spec ⌜Sep⌝]
		THEN REPEAT strip_tac));
(* *** Goal "1.1" *** *)
a (GET_NTH_ASM_T 5 ante_tac
	THEN once_rewrite_tac [get_spec ⌜$⊆⋎g⌝]
	THEN strip_tac
	THEN asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a (once_rewrite_tac[asm_rule ⌜Sep t (λ x⦁ x ∈⋎g s) = s⌝]);
a (strip_tac);
(* *** Goal "2" *** *)
a (fc_tac [Gx_⊆⋎g_galaxy]);
a (asm_fc_tac[]);
val Gx_mono_thm = save_pop_thm "Gx_mono_thm";

set_goal([], ⌜∀s t⦁ s ∈⋎g t ⇒ Gx s ⊆⋎g Gx t⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜galaxy (Gx t)⌝ THEN1 rewrite_tac [galaxy_Gx]);
a (fc_tac [GalaxiesTransitive_thm]);
a (fc_tac [get_spec ⌜transitive⌝]);
a (lemma_tac ⌜t ∈⋎g Gx t⌝ THEN1 rewrite_tac[t_in_Gx_t_thm]);
a (ASM_FC_T (MAP_EVERY(strip_asm_tac o (once_rewrite_rule [get_spec ⌜$⊆⋎g⌝]))) [] 
	THEN asm_fc_tac[]);
a (all_fc_tac [Gx_⊆⋎g_galaxy]);
val Gx_mono_thm2 = save_pop_thm "Gx_mono_thm2";

set_goal([], ⌜∀s⦁ transitive (Gx s)⌝);
a (strip_tac);
a (lemma_tac ⌜galaxy (Gx s)⌝ THEN1 rewrite_tac [galaxy_Gx]);
a (fc_tac [GalaxiesTransitive_thm]);
val Gx_trans_thm = save_pop_thm "Gx_trans_thm";

set_goal([], ⌜∀t⦁ t ⊆⋎g Gx t⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜t ∈⋎g Gx t⌝ THEN1 rewrite_tac [t_in_Gx_t_thm]);
a (fc_tac [rewrite_rule [get_spec ⌜transitive⌝]Gx_trans_thm]);
val t_sub_Gx_t_thm = save_pop_thm "t_sub_Gx_t_thm";

set_goal([], ⌜∀s t⦁ s ⊆⋎g t ⇒ s ⊆⋎g Gx t⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜t ⊆⋎g Gx t⌝ THEN1 rewrite_tac [t_sub_Gx_t_thm]);
a (all_fc_tac [⊆⋎g_trans_thm]);
val Gx_mono_thm3 = save_pop_thm "Gx_mono_thm3";

set_goal([], ⌜∀s t⦁ s ⊆⋎g t ⇒ s ∈⋎g Gx t⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜galaxy (Gx t)⌝ THEN1 rewrite_tac[galaxy_Gx]);
a (lemma_tac ⌜t ∈⋎g Gx t⌝ THEN1 rewrite_tac[t_in_Gx_t_thm]);
a (all_ufc_tac [GClose_fc_clauses]);
val Gx_mono_thm4 = save_pop_thm "Gx_mono_thm4";

set_goal([], ⌜∀s t⦁ s ∈⋎g t ⇒ s ∈⋎g Gx t⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜t ∈⋎g Gx t⌝ THEN1 rewrite_tac [t_in_Gx_t_thm]);
a (lemma_tac ⌜transitive (Gx t)⌝ THEN1 rewrite_tac [Gx_trans_thm]);
a (ALL_FC_T (MAP_EVERY (fn x => fc_tac [rewrite_rule [get_spec ⌜$⊆⋎g⌝] x]))
	[get_spec ⌜transitive⌝]);
val Gx_trans_thm2 = save_pop_thm "Gx_trans_thm2";

set_goal([], ⌜∀s t u⦁ s ∈⋎g t ∧ t ∈⋎g Gx u ⇒ s ∈⋎g Gx u⌝);
a (REPEAT strip_tac);
a (LEMMA_T ⌜transitive (Gx u)⌝ ante_tac THEN1 rewrite_tac [Gx_trans_thm]);
a (rewrite_tac [get_spec ⌜transitive⌝]
	THEN STRIP_T (fn x => FC_T (MAP_EVERY ante_tac) [x]));
a (rewrite_tac [get_spec ⌜$⊆⋎g⌝] THEN STRIP_T (fn x => fc_tac [x]));
val Gx_trans_thm3 = save_pop_thm "Gx_trans_thm3";

=TEX
}%ignore

\subsubsection{The Empty Set}

We can now prove that there is an empty set.

\ignore{
=SML
set_goal([], ⌜∃ ∅⋎g⦁ ∀s⦁ ¬ s ∈⋎g ∅⋎g⌝);
a (∃_tac ⌜Sep (εs:GS⦁ T) (λx:GS⦁ F)⌝
	THEN rewrite_tac [get_spec⌜Sep⌝]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

So we define $⌜∅⋎g⌝$ as the empty set:

ⓈHOLCONST
│ ⦏∅⋎g⦎ : GS
├
│ ∀s⦁ ¬ s ∈⋎g ∅⋎g
■

and the empty set is a member of every galaxy:

=GFT
⦏G∅⋎gC⦎ =		⊢ ∀ g⦁ galaxy g ⇒ ∅⋎g ∈⋎g g
⦏∅⋎g⊆⋎g_thm⦎ =	⊢ ∀ s⦁ ∅⋎g ⊆⋎g s
⦏⋃⋎g∅⋎g_thm⦎ =	⊢ ⋃⋎g ∅⋎g = ∅⋎g
=TEX
=GFT
⦏∅⋎g_spec⦎ =				⊢ ∀ s⦁ ¬ s ∈⋎g ∅⋎g
⦏mem_not_empty_thm⦎ =	⊢ ∀ m n⦁ m ∈⋎g n ⇒ ¬ n = ∅⋎g
⦏∅⋎g_∈⋎g_galaxy_thm⦎ =	⊢ ∀ x⦁ galaxy x ⇒ ∅⋎g ∈⋎g x
⦏∅⋎g_∈⋎g_Gx_thm⦎ =		⊢ ∀ x⦁ ∅⋎g ∈⋎g Gx x
=TEX

\ignore{
=SML
set_goal([],⌜∀g⦁ galaxy g ⇒ ∅⋎g ∈⋎g g⌝);
a (REPEAT strip_tac);
a (fc_tac [GCloseSep_thm, get_spec ⌜galaxy⌝]);
a (list_spec_nth_asm_tac 1 [⌜x⌝,⌜λx:GS⦁ F⌝]);
a (lemma_tac ⌜∅⋎g = Sep x (λ x⦁ F)⌝
	THEN1 (rewrite_tac [gs_ext_axiom, get_spec ⌜∅⋎g⌝, get_spec ⌜Sep⌝]));
a (asm_rewrite_tac[]);
val G∅⋎gC = save_pop_thm "G∅⋎gC";

val ∅⋎g⊆⋎g_thm = save_thm ("∅⋎g⊆⋎g_thm",
	prove_rule [get_spec ⌜∅⋎g⌝, ⊆⋎g_thm]
	⌜∀s:GS⦁ ∅⋎g ⊆⋎g s⌝);
val ⋃⋎g∅⋎g_thm = save_thm ("⋃⋎g∅⋎g_thm",
	prove_rule [get_spec ⌜∅⋎g⌝, get_spec ⌜⋃⋎g⌝, gs_ext_axiom]
	⌜⋃⋎g ∅⋎g = ∅⋎g⌝);
val ∅⋎g_spec = get_spec ⌜∅⋎g⌝;

set_goal ([], ⌜∀m n⦁ m ∈⋎g n ⇒ ¬ n = ∅⋎g⌝);
a (REPEAT strip_tac);
a (rewrite_tac [gs_ext_axiom]
	THEN REPEAT strip_tac);
a (∃_tac ⌜m⌝ THEN asm_rewrite_tac[get_spec ⌜∅⋎g⌝]);
val mem_not_empty_thm = save_pop_thm "mem_not_empty_thm";

set_goal ([], ⌜∀x⦁ galaxy x ⇒ ∅⋎g ∈⋎g x⌝);
a (REPEAT strip_tac THEN fc_tac [GClose_fc_clauses]);
a (fc_tac [get_spec ⌜galaxy⌝]);
a (asm_ufc_tac[]);
a (SPEC_NTH_ASM_T 5 ⌜λx:GS⦁F⌝ ante_tac);
a (lemma_tac ⌜∅⋎g ⊆⋎g x'⌝ THEN1 rewrite_tac [∅⋎g⊆⋎g_thm]);
a (fc_tac[Sep_⊆_thm]);
a (lemma_tac ⌜(λ x⦁ F) = (CombC $∈⋎g ∅⋎g)⌝
	THEN1 (rewrite_tac [ext_thm, get_spec ⌜CombC⌝, ∅⋎g_spec]));
a (rewrite_tac [asm_rule ⌜(λ x⦁ F) = CombC $∈⋎g ∅⋎g⌝, asm_rule ⌜Sep x' (CombC $∈⋎g ∅⋎g) = ∅⋎g⌝]);
val ∅⋎g_∈⋎g_galaxy_thm = save_pop_thm "∅⋎g_∈⋎g_galaxy_thm";

set_goal ([], ⌜∀x⦁ ∅⋎g ∈⋎g Gx x⌝);
a (asm_tac galaxy_Gx THEN ufc_tac [∅⋎g_∈⋎g_galaxy_thm]);
val ∅⋎g_∈⋎g_Gx_thm = save_pop_thm "∅⋎g_∈⋎g_Gx_thm";

add_pc_thms "'gst-ax" (map get_spec [⌜ℙ⋎g⌝, ⌜⋃⋎g⌝] @ [∅⋎g_spec, ∅⋎g⊆⋎g_thm, ⋃⋎g∅⋎g_thm]);
set_merge_pcs ["basic_hol", "'gst-ax"];
=TEX
}%ignore

\subsection{Functional Replacement}

The more convenient form of replacement which takes a function rather than a relation (and hence needs no "ManyOne" caveat) is introduced here.

\subsubsection{Introduction}

Though a functional formulation of replacement is most convenient for most applications, it has a number of small disadvantages which have persuaded me to stay closer to the traditional formulation of replacement in terms of relations.
The more convenient functional version will then be introduced by definition (so if you don't know what I'm talking about, look forward to compare the two versions).

For the record the disadvantages of the functional one (if used as an axiom) are:

\begin{enumerate}
\item It can't be used to prove the existence of the empty set.
\item When used to define separation it requires the axiom of choice.
\end{enumerate}

\subsubsection{Imagep}

Now we prove a more convenient version of replacement which takes a HOL function rather than a relation as its argument.
It states that the image of any set under a function is also a set.

\ignore{
=SML
set_goal([],⌜∃Imagep⦁ ∀f:GS → GS⦁ ∀s: GS⦁ 
	(∀x⦁ x ∈⋎g Imagep f s ⇔ ∃e⦁ e ∈⋎g s ∧ x = f e)⌝);
a (prove_∃_tac THEN REPEAT strip_tac);
a (lemma_tac ⌜∃fr⦁ fr = λx y⦁ y = f' x⌝ THEN1 prove_∃_tac);
a (lemma_tac ⌜ManyOne fr⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜ManyOne⌝]
		THEN REPEAT strip_tac
		THEN asm_rewrite_tac[]));
a (∃_tac ⌜RelIm fr s'⌝);
a (⇔_FC_T asm_rewrite_tac [get_spec ⌜RelIm⌝]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

$⌜Imagep\ f\ s⌝$ is the image of $s$ through $f$.

ⓈHOLCONST
│ ⦏Imagep⦎ : (GS → GS) → GS → GS
├───────────
│ ∀f s x⦁ x ∈⋎g Imagep f s ⇔ ∃e⦁ e ∈⋎g s ∧ x = f e
■

\ignore{
=SML
val Imagep_spec = get_spec ⌜Imagep⌝;
add_pc_thms "'gst-ax" (map get_spec [⌜Imagep⌝]);
set_merge_pcs ["basic_hol", "'gst-ax"];
=TEX
}%ignore

\subsubsection{Galaxy Closure}

We now show that galaxies are closed under {\it Imagep}.

=GFT
⦏GImagepC⦎ =	⊢ ∀g⦁ galaxy g ⇒ ∀s⦁ s ∈⋎g g
				⇒ ∀f⦁ Imagep f s ⊆⋎g g ⇒ Imagep f s ∈⋎g g
=TEX

\ignore{
=SML
set_goal([],⌜∀g⦁ galaxy g
	⇒ ∀s⦁ s ∈⋎g g
	⇒ ∀f⦁ Imagep f s ⊆⋎g g
	⇒ Imagep f s ∈⋎g g⌝);
a (REPEAT_N 5 strip_tac);
a (lemma_tac ⌜∃fr⦁ fr = λx y⦁ y = f x⌝ THEN1 prove_∃_tac);
a (lemma_tac ⌜ManyOne fr⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜ManyOne⌝]
		THEN REPEAT strip_tac
		THEN asm_rewrite_tac[]));
a (lemma_tac ⌜Imagep f s = RelIm fr s⌝);
(* *** Goal "1" *** *)
a (pure_rewrite_tac [gs_ext_axiom]);
a (⇔_FC_T pure_once_rewrite_tac [get_spec ⌜RelIm⌝]);
a (asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a (once_asm_rewrite_tac[]);
a (fc_tac[get_spec ⌜galaxy⌝]);
a (list_spec_nth_asm_tac 5 [⌜s⌝,⌜fr⌝]
	THEN asm_rewrite_tac[]);
val GImagepC = save_pop_thm "GImagepC";
=TEX
}%ignore

\subsection{Pair and Unit sets}

$Pair⋎g$ is defined using replacement, and Sing (because ``Unit'' is used elsewhere) using $Pair⋎g$.

\ignore{
=SML
set_goal([],⌜∃Pair⋎g⦁ ∀s t e:GS⦁
	e ∈⋎g Pair⋎g s t
	⇔ e = s ∨ e = t⌝);
a (∃_tac ⌜λs t⦁Imagep (λx⦁ if x = ∅⋎g then s else t) (ℙ⋎g (ℙ⋎g ∅⋎g))⌝
	THEN rewrite_tac[get_spec ⌜$⊆⋎g⌝]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (asm_ante_tac ⌜¬ e = s⌝);
a (asm_rewrite_tac[]);
a (cases_tac ⌜e'=∅⋎g⌝
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜∅⋎g⌝
	THEN prove_tac
	[get_spec ⌜$⊆⋎g⌝]);
(* *** Goal "3" *** *)
a (lemma_tac ⌜¬ ℙ⋎g ∅⋎g = ∅⋎g⌝);
a (prove_tac[
	get_spec ⌜$⊆⋎g⌝,
	gs_ext_axiom]);
a (∃_tac ⌜∅⋎g⌝
	THEN prove_tac[]);
a (∃_tac ⌜ℙ⋎g ∅⋎g⌝ THEN asm_rewrite_tac[]);
a (strip_tac THEN rewrite_tac[get_spec ⌜$⊆⋎g⌝]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

Pairs can be defined as the image of some two element set under a function defined by a conditional.
A suitable two element set can be constructed from the empty set using the powerset construction a couple of times.
However, having proven that this can be done (details omitted), we can introduce the pair constructor by conservative extension as follows.
(the ProofPower tool shows that it has accepted my proof by putting this extension into the "definitions" section of the theory listing).

ⓈHOLCONST
│ ⦏Pair⋎g⦎ : GS → GS → GS
├────────────
│ ∀s t e:GS⦁ e ∈⋎g Pair⋎g s t ⇔ e = s ∨ e = t	
■

=GFT
⦏Pair⋎g_∈_thm⦎ =		⊢ ∀ x y⦁ x ∈⋎g Pair⋎g x y ∧ y ∈⋎g Pair⋎g x y
⦏Pair⋎g_tc∈_thm⦎ =	⊢ ∀ s t⦁ s ∈⋎g⋏+ Pair⋎g s t ∧ t ∈⋎g⋏+ Pair⋎g s t
⦏Pair⋎g_eq_thm⦎ =		⊢ ∀ s t u v⦁ Pair⋎g s t = Pair⋎g u v
					⇔ s = u ∧ t = v ∨ s = v ∧ t = u
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y⦁ x ∈⋎g Pair⋎g x y ∧ y ∈⋎g Pair⋎g x y⌝);
a (rewrite_tac [get_spec ⌜Pair⋎g⌝]);
val Pair⋎g_∈_thm = save_pop_thm "Pair⋎g_∈_thm";

set_goal([], ⌜∀s t⦁ s ∈⋎g⋏+ Pair⋎g s t ∧ t ∈⋎g⋏+ Pair⋎g s t⌝);
a (REPEAT ∀_tac);
a (STRIP_THM_THEN asm_tac (list_∀_elim [⌜s⌝, ⌜t⌝] Pair⋎g_∈_thm)
	THEN ufc_tac [tc∈_incr_thm]);
a (REPEAT strip_tac);
val Pair⋎g_tc∈_thm = save_pop_thm "Pair⋎g_tc∈_thm";

set_goal([],⌜∀s t u v⦁
	Pair⋎g s t = Pair⋎g u v
	⇔ s = u ∧ t = v
	∨ s = v ∧ t = u⌝);
a (rewrite_tac[
	∀_elim ⌜Pair⋎g s t⌝ gs_ext_axiom,	
	get_spec ⌜Pair⋎g⌝]
	THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 2 ⌜s⌝
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜u⌝
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (spec_nth_asm_tac 2 ⌜v⌝
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (spec_nth_asm_tac 2 ⌜t⌝
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY asm_rewrite_tac[]);
val Pair⋎g_eq_thm =
	save_pop_thm "Pair⋎g_eq_thm";
=TEX
}%ignore

=GFT
⦏GClosePair⋎g⦎ =	⊢ ∀g⦁ galaxy g ⇒ ∀s t⦁ s ∈⋎g g ∧ t ∈⋎g g
				⇒ Pair⋎g s t ∈⋎g g
=TEX

\ignore{
=SML
set_goal([],⌜∀g⦁ galaxy g ⇒ ∀s t⦁ s ∈⋎g g ∧ t ∈⋎g g ⇒ Pair⋎g s t ∈⋎g g⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜Pair⋎g s t = Imagep (λx⦁ if x = ∅⋎g then s else t) (ℙ⋎g (ℙ⋎g ∅⋎g))⌝);
(* *** Goal "1" *** *)
a (once_rewrite_tac [gs_ext_axiom]);
a (rewrite_tac (map get_spec [⌜Pair⋎g⌝,⌜Imagep⌝]));
a (REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a (∃_tac ⌜∅⋎g⌝ THEN rewrite_tac[get_spec ⌜$⊆⋎g⌝]);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜ℙ⋎g ∅⋎g⌝ THEN rewrite_tac[get_spec ⌜$⊆⋎g⌝]);
a (lemma_tac ⌜¬ ℙ⋎g ∅⋎g = ∅⋎g⌝);
(* *** Goal "1.2.1" *** *)
a (rewrite_tac [gs_ext_axiom]
	THEN strip_tac
	THEN ∃_tac ⌜∅⋎g⌝
	THEN rewrite_tac[]);
(* *** Goal "1.2.2" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "1.3" *** *)
a (cases_tac ⌜e' = ∅⋎g⌝
	THEN asm_rewrite_tac[]);
a (asm_ante_tac ⌜e = (if e' = ∅⋎g then s else t)⌝
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
a (fc_tac [GImagepC]);
a (list_spec_nth_asm_tac 1 [⌜ℙ⋎g (ℙ⋎g ∅⋎g)⌝,⌜λ x⦁ if x = ∅⋎g then s else t⌝]);
a (fc_tac [G∅⋎gC]);
a (lemma_tac ⌜∀s⦁ s ∈⋎g g ⇒ ℙ⋎g s ∈⋎g g⌝
	THEN1 (REPEAT (fc_tac [get_spec ⌜galaxy⌝])));
a (REPEAT (asm_fc_tac []));
(* *** Goal "2.2" *** *)
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac [get_spec ⌜$⊆⋎g⌝]);
a (REPEAT strip_tac);
a (POP_ASM_T ante_tac
	THEN cases_tac ⌜e' = ∅⋎g⌝
	THEN asm_rewrite_tac[]
	THEN strip_tac
	THEN asm_rewrite_tac[]);
val GClosePair⋎g = save_pop_thm "GClosePair⋎g";
=TEX
}%ignore

\subsubsection{Unit Sets}

Since ``Unit'' is used in the theory of groups I use ``Sing'' for singleton sets.

ⓈHOLCONST
│ ⦏Sing⦎ : GS → GS
├──────────
│ ∀s⦁ Sing s = Pair⋎g s s
■

The following theorem tells you what the members of a unit sets are.

=GFT
⦏Sing_thm⦎ =	⊢ ∀s e⦁ e ∈⋎g Sing s ⇔ e = s
⦏Sing_thm2⦎ =	⊢ ∀x⦁ x ∈⋎g Sing x
⦏Sing_tc∈_thm⦎ =	⊢ ∀x⦁ x ∈⋎g⋏+ Sing x
=TEX

\ignore{
=SML
set_goal([],⌜∀s e⦁
	e ∈⋎g Sing s ⇔ e = s⌝);
a (rewrite_tac [
	get_spec⌜Sing⌝,
	get_spec⌜Pair⋎g⌝]
	THEN REPEAT strip_tac);
val Sing_thm = pop_thm ();

set_goal([], ⌜∀x⦁ x ∈⋎g Sing x⌝);
a (rewrite_tac [Sing_thm]);
val Sing_thm2 = save_pop_thm "Sing_thm2";

set_goal([], ⌜∀x⦁ x ∈⋎g⋏+ Sing x⌝);
a (strip_tac);
a (asm_tac (∀_elim ⌜x⌝ Sing_thm2) THEN fc_tac [tc∈_incr_thm]);
val Sing_tc∈_thm = save_pop_thm "Sing_tc∈_thm";

add_pc_thms "'gst-ax" [get_spec ⌜Pair⋎g⌝, Sing_thm];
add_rw_thms [Pair⋎g_∈_thm, Pair⋎g_tc∈_thm, Sing_tc∈_thm] "'gst-ax";
add_sc_thms [Pair⋎g_∈_thm, Pair⋎g_tc∈_thm, Sing_tc∈_thm] "'gst-ax";
set_merge_pcs ["basic_hol", "'gst-ax"];
=TEX
}%ignore

The following theorem tells you when two unit sets are equal.

=GFT
⦏Sing_eq_thm⦎ =	⊢ ∀s t⦁ Sing s = Sing t ⇔ s = t
=TEX

\ignore{
=SML
set_goal([],⌜∀s t⦁
	Sing s = Sing t
	⇔ s = t⌝);
a (prove_tac [
	∀_elim ⌜Sing s⌝ gs_ext_axiom]);
val Sing_eq_thm = pop_thm ();
add_pc_thms "'gst-ax" [Sing_eq_thm];
set_merge_pcs ["basic_hol", "'gst-ax"];
=TEX
}%ignore

\subsubsection{Galaxy Closure}

=GFT
⦏GCloseSing⦎ =	⊢ ∀g⦁ galaxy g ⇒ ∀s⦁ s ∈⋎g g ⇒ Sing s ∈⋎g g
=TEX

\ignore{
=SML
set_goal([],⌜∀g⦁ galaxy g ⇒ ∀s⦁ s ∈⋎g g ⇒ Sing s ∈⋎g g⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜Sing⌝]);
a (REPEAT (asm_fc_tac[GClosePair⋎g]));
val GCloseSing = save_pop_thm "GCloseSing";
=TEX
}%ignore

\subsubsection{Sing-Pair equations}

The following theorems tell you when Pairs are really Sings.

=GFT
⦏Sing_Pair⋎g_eq_thm⦎ =	⊢ ∀s t u⦁ Sing s = Pair⋎g t u ⇔ s = t ∧ s = u
⦏Pair⋎g_Sing_eq_thm⦎ =	⊢ ∀s t u⦁ Pair⋎g s t = Sing u ⇔ s = u ∧ t = u
=TEX

\ignore{
=SML
set_goal([],
	⌜∀s t u⦁
	Sing s = Pair⋎g t u
	⇔ s = t ∧ s = u⌝);
a (prove_tac [
	∀_elim ⌜Sing s⌝ gs_ext_axiom]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜s⌝
	THEN spec_nth_asm_tac 2 ⌜t⌝
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY rewrite_tac[]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 1 ⌜u⌝
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY rewrite_tac[]);
val Sing_Pair⋎g_eq_thm = pop_thm ();
=TEX

=SML
set_goal([],⌜∀s t u⦁
	Pair⋎g s t = Sing u
	⇔ s = u ∧ t = u⌝);
a (prove_tac [
	∀_elim ⌜Pair⋎g s t⌝ gs_ext_axiom]);
val Pair⋎g_Sing_eq_thm = pop_thm ();
=TEX
}%ignore

\subsection{Union and Intersection}

Binary union and distributed and binary intersection are defined.

\subsubsection{Binary Union}

\ignore{
=SML
declare_infix (240, "∪⋎g");
set_goal ([],⌜∃($∪⋎g)⦁ ∀s t e⦁
e ∈⋎g (s ∪⋎g t) ⇔ e ∈⋎g s ∨ e ∈⋎g t
⌝);
a (∃_tac ⌜λs t⦁ ⋃⋎g (Pair⋎g s t)⌝);
a (prove_tac [get_spec ⌜⋃⋎g⌝]);
save_cs_∃_thm(pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ $∪⋎g : GS → GS → GS
├─────────────
│ ∀s t e⦁ e ∈⋎g (s ∪⋎g t) ⇔ e ∈⋎g s ∨ e ∈⋎g t
■

=GFT
⦏⊆⋎g∪⋎g_thm⦎ =	⊢ ∀ A B⦁ A ⊆⋎g A ∪⋎g B ∧ B ⊆⋎g A ∪⋎g B
⦏∪⋎g⊆⋎g_thm1⦎ =	⊢ ∀ A B C⦁ A ⊆⋎g C ∧ B ⊆⋎g C ⇒ A ∪⋎g B ⊆⋎g C
⦏∪⋎g⊆⋎g_thm2⦎ =	⊢ ∀ A B C D⦁ A ⊆⋎g C ∧ B ⊆⋎g D ⇒ A ∪⋎g B ⊆⋎g C ∪⋎g D
⦏∪⋎g∅⋎g_clauses⦎ =	⊢ ∀ A⦁ A ∪⋎g ∅⋎g = A ∧ ∅⋎g ∪⋎g A = A
=TEX

\ignore{
=SML
val ⦏∪⋎g_thm⦎ = get_spec ⌜$∪⋎g⌝;
val ⦏⊆⋎g∪⋎g_thm⦎ = save_thm ("⊆⋎g∪⋎g_thm", prove_rule
	[⊆⋎g_thm, ∪⋎g_thm]
	⌜∀A B⦁ A ⊆⋎g A ∪⋎g B ∧ B ⊆⋎g A ∪⋎g B⌝);
val ⦏∪⋎g⊆⋎g_thm1⦎ = save_thm ("∪⋎g⊆⋎g_thm1", prove_rule
	[⊆⋎g_thm, ∪⋎g_thm]
	⌜∀A B C⦁ A ⊆⋎g C ∧ B ⊆⋎g C ⇒ A ∪⋎g B ⊆⋎g C⌝);
val ⦏∪⋎g⊆⋎g_thm2⦎ = save_thm ("∪⋎g⊆⋎g_thm2", prove_rule
	[⊆⋎g_thm, ∪⋎g_thm]
	⌜∀A B C D⦁ A ⊆⋎g C ∧ B ⊆⋎g D ⇒ (A ∪⋎g B) ⊆⋎g (C ∪⋎g D)⌝);
val ⦏∪⋎g∅⋎g_clauses⦎ = save_thm ("∪⋎g∅⋎g_clauses", prove_rule
	[gs_ext_axiom, ∪⋎g_thm]
	⌜∀A⦁ (A ∪⋎g ∅⋎g) = A
	∧ (∅⋎g ∪⋎g A) = A⌝);
=TEX
}%ignore

\subsubsection{Galaxy Closure}

=GFT
⦏GClose∪⋎g⦎ =	⊢ ∀g⦁ galaxy g ⇒ ∀s t⦁ s ∈⋎g g ∧ t ∈⋎g g ⇒ s ∪⋎g t ∈⋎g g
=TEX

\ignore{
=SML
set_goal([],⌜∀g⦁ galaxy g ⇒ ∀s t⦁ s ∈⋎g g ∧ t ∈⋎g g ⇒ s ∪⋎g t ∈⋎g g⌝);
a (REPEAT strip_tac THEN fc_tac [get_spec ⌜galaxy⌝]);
a (lemma_tac ⌜s ∪⋎g t = ⋃⋎g (Pair⋎g s t)⌝
	THEN1 (once_rewrite_tac [gs_ext_axiom]
		THEN rewrite_tac [get_spec ⌜⋃⋎g⌝, get_spec ⌜$∪⋎g⌝]
		THEN prove_tac[]));
a (asm_rewrite_tac []);
a (lemma_tac ⌜Pair⋎g s t ∈⋎g g⌝
	THEN1 (REPEAT (asm_fc_tac [GClosePair⋎g])));
a (REPEAT (asm_fc_tac[]));
val GClose∪⋎g = save_pop_thm "GClose∪⋎g";
=TEX
}%ignore

\subsubsection{Distributed Intersection}

Distributed intersection doesn't really make sense for the empty set, but under this definition it maps the empty set onto itself.

ⓈHOLCONST
│ ⦏⋂⋎g⦎ : GS → GS
├
│ ∀s⦁ ⋂⋎g s = Sep (⋃⋎g s) (λx⦁ ∀t⦁ t ∈⋎g s ⇒ x ∈⋎g t)
■


=GFT
⦏⋂⋎g⊆⋎g_thm⦎ =	⊢ ∀x s e⦁ x ∈⋎g s
				⇒ (e ∈⋎g ⋂⋎g s ⇔ ∀y⦁ y ∈⋎g s ⇒ e ∈⋎g y)
⦏⊆⋎g⋂⋎g_thm⦎ =	⊢  ∀A B⦁ A ∈⋎g B
				⇒ ∀C⦁ (∀D⦁ D ∈⋎g B ⇒ C ⊆⋎g D)
				⇒ C ⊆⋎g ⋂⋎g B
⦏⋂⋎g∅⋎g_thm⦎ = 	⊢ ⋂⋎g ∅⋎g = ∅⋎g
=TEX

\ignore{
=SML
set_goal ([],⌜∀x s e⦁ x ∈⋎g s ⇒
	(e ∈⋎g ⋂⋎g s ⇔ ∀y⦁ y ∈⋎g s ⇒ e ∈⋎g y)⌝);
a (prove_tac [
	get_spec ⌜⋂⋎g⌝]);
val ⋂⋎g_thm = save_pop_thm "⋂⋎g_thm";
=SML
set_goal([],⌜∀s t⦁ s ∈⋎g t ⇒ ⋂⋎g t ⊆⋎g s⌝);
a (rewrite_tac [⋂⋎g_thm, ⊆⋎g_thm]);
a (REPEAT strip_tac);
a (REPEAT (asm_fc_tac[⋂⋎g_thm]));
val ⋂⋎g⊆⋎g_thm = save_pop_thm "⋂⋎g⊆⋎g_thm";

val ⊆⋎g⋂⋎g_thm = save_thm ("⊆⋎g⋂⋎g_thm", 
	(prove_rule [⊆⋎g_thm, gs_ext_axiom,
	get_spec ⌜$⋂⋎g⌝]
	⌜∀A B⦁ A ∈⋎g B ⇒ ∀C⦁	
	(∀D⦁ D ∈⋎g B ⇒ C ⊆⋎g D)
	⇒ C ⊆⋎g ⋂⋎g B⌝));

val ⋂⋎g∅⋎g_thm = save_thm ("⋂⋎g∅⋎g_thm", 
	(prove_rule [gs_ext_axiom,	get_spec ⌜$⋂⋎g⌝]
	⌜⋂⋎g ∅⋎g = ∅⋎g⌝));
=TEX
}%ignore

\subsubsection{Binary Intersection}

Binary intersection could be defined in terms of distributed intersection, but its easier not to.

=SML
declare_infix (240, "∩⋎g");
=TEX

ⓈHOLCONST
│ $⦏∩⋎g⦎ : GS → GS → GS
├
│ ∀s t⦁ s ∩⋎g t = Sep s (λx⦁ x ∈⋎g t)
■

\subsubsection{Galaxy Closure}

=GFT
⦏GClose⋂⋎g⦎ =	⊢ ∀g⦁ galaxy g ⇒ ∀s⦁ s ∈⋎g g ⇒ ⋂⋎g s ∈⋎g g
⦏GClose∩⋎g⦎ =	⊢ ∀g⦁ galaxy g ⇒ ∀s t⦁ s ∈⋎g g ∧ t ∈⋎g g ⇒ s ∩⋎g t ∈⋎g g
=TEX

\ignore{
=SML
set_goal([],⌜∀g⦁ galaxy g ⇒ ∀s⦁ s ∈⋎g g ⇒ ⋂⋎g s ∈⋎g g⌝);
a (REPEAT strip_tac
	THEN rewrite_tac[get_spec ⌜⋂⋎g⌝]);
a (fc_tac [GCloseSep_thm, get_spec ⌜galaxy⌝]);
a (list_spec_nth_asm_tac 1 [⌜⋃⋎g s⌝, ⌜λ x⦁ ∀ t⦁ t ∈⋎g s ⇒ x ∈⋎g t⌝]);
a (asm_fc_tac[]);
val GClose⋂⋎g = save_pop_thm "GClose⋂⋎g";

set_goal([],⌜∀g⦁ galaxy g ⇒ ∀s t⦁ s ∈⋎g g ∧ t ∈⋎g g ⇒ s ∩⋎g t ∈⋎g g⌝);
a (REPEAT strip_tac
	THEN rewrite_tac[get_spec ⌜$∩⋎g⌝]);
a (fc_tac [GCloseSep_thm]);
a (list_spec_nth_asm_tac 1 [⌜s⌝, ⌜λ x⦁ x ∈⋎g t⌝]);
val GClose∩⋎g = save_pop_thm "GClose∩⋎g";
=TEX
}%ignore

=GFT
⦏∩⋎g_thm⦎ =		⊢ ∀s t e⦁ e ∈⋎g s ∩⋎g t ⇔ e ∈⋎g s ∧ e ∈⋎g t
⦏∩⋎g_thm⦎ =		⊢ ∀s t e⦁	e ∈⋎g s ∩⋎g t ⇔ e ∈⋎g s ∧ e ∈⋎g t
=TEX

=GFT
⦏⊆⋎g∩⋎g_thm⦎ =	⊢ ∀A B⦁ A ∩⋎g B ⊆⋎g A ∧ A ∩⋎g B ⊆⋎g B
⦏∩⋎g⊆⋎g_thm1⦎ =	⊢ ∀A B C⦁ A ⊆⋎g C ∧ B ⊆⋎g C ⇒ A ∩⋎g B ⊆⋎g C
⦏∩⋎g⊆⋎g_thm2⦎ =	⊢ ∀A B C D⦁ A ⊆⋎g C ∧ B ⊆⋎g D ⇒ (A ∩⋎g B) ⊆⋎g (C ∩⋎g D)
⦏∩⋎g⊆⋎g_thm3⦎ =	⊢ ∀A B C⦁ C ⊆⋎g A ∧ C ⊆⋎g B ⇒ C ⊆⋎g A ∩⋎g B
=TEX

\ignore{
=SML
set_goal ([],⌜∀s t e⦁
	e ∈⋎g s ∩⋎g t ⇔ e ∈⋎g s ∧ e ∈⋎g t⌝);
a (prove_tac [
	get_spec ⌜$∩⋎g⌝]);
val ∩⋎g_thm = save_thm ("∩⋎g_thm",
	prove_rule [get_spec ⌜$∩⋎g⌝]
	⌜∀s t e⦁	e ∈⋎g s ∩⋎g t ⇔ e ∈⋎g s ∧ e ∈⋎g t⌝);
val ⊆⋎g∩⋎g_thm = save_thm ("⊆⋎g∩⋎g_thm",
	prove_rule [⊆⋎g_thm, ∩⋎g_thm]
	⌜∀A B⦁ A ∩⋎g B ⊆⋎g A ∧ A ∩⋎g B ⊆⋎g B⌝);
val ∩⋎g⊆⋎g_thm1 = save_thm ("∩⋎g⊆⋎g_thm1",
	prove_rule [⊆⋎g_thm, ∩⋎g_thm]
	⌜∀A B C⦁ A ⊆⋎g C ∧ B ⊆⋎g C ⇒ A ∩⋎g B ⊆⋎g C⌝);
val ∩⋎g⊆⋎g_thm2 = save_thm ("∩⋎g⊆⋎g_thm2",
	prove_rule [⊆⋎g_thm, ∩⋎g_thm]
	⌜∀A B C D⦁ A ⊆⋎g C ∧ B ⊆⋎g D ⇒ (A ∩⋎g B) ⊆⋎g (C ∩⋎g D)⌝);
val ∩⋎g⊆⋎g_thm3 = save_thm ("∩⋎g⊆⋎g_thm3",
	prove_rule [⊆⋎g_thm, ∩⋎g_thm]
	⌜∀A B C⦁ C ⊆⋎g A ∧ C ⊆⋎g B ⇒ C ⊆⋎g A ∩⋎g B⌝);
=TEX
}%ignore

\subsubsection{Consequences of Well-Foundedness}

=GFT
⦏not_x_in_x_thm⦎ =	⊢ ¬ (∃ x⦁ x ∈⋎g x)
=TEX

\ignore{
=SML
set_goal([], ⌜¬ ∃x⦁ x ∈⋎g x⌝);
a contr_tac;
a (asm_tac gs_wf_min_thm);
a (spec_nth_asm_tac 1 ⌜Sep x (λy:GS⦁ y = x)⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (POP_ASM_T ante_tac
	THEN rewrite_tac[]);
a strip_tac;
a (DROP_NTH_ASM_T 2 ante_tac
	THEN rewrite_tac[]);
a (swap_nth_asm_concl_tac 1);
a (all_var_elim_asm_tac);
a (strip_tac);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val not_x_in_x_thm = save_pop_thm "not_x_in_x_thm";
=TEX
}%ignore

\subsection{Galaxy Closure Clauses}

=GFT
⦏GClose_fc_clauses2⦎ =
   ⊢ ∀ g
     ⦁ galaxy g
         ⇒ (∀ s t⦁ s ∈⋎g g ∧ t ∈⋎g g ⇒ Pair⋎g s t ∈⋎g g)
           ∧ (∀ s⦁ s ∈⋎g g ⇒ Sing s ∈⋎g g)
           ∧ (∀ s t⦁ s ∈⋎g g ∧ t ∈⋎g g ⇒ s ∪⋎g t ∈⋎g g)
           ∧ (∀ s⦁ s ∈⋎g g ⇒ ⋂⋎g s ∈⋎g g)
           ∧ (∀ s t⦁ s ∈⋎g g ∧ t ∈⋎g g ⇒ s ∩⋎g t ∈⋎g g)
=TEX

\ignore{
=SML
set_goal([], ⌜∀g⦁ galaxy g ⇒
	  (∀s t⦁ s ∈⋎g g ∧ t ∈⋎g g ⇒ Pair⋎g s t ∈⋎g g)
	∧ (∀s⦁ s ∈⋎g g ⇒ Sing s ∈⋎g g)
	∧ (∀s t⦁ s ∈⋎g g ∧ t ∈⋎g g ⇒ s ∪⋎g t ∈⋎g g)
	∧ (∀s⦁ s ∈⋎g g ⇒ ⋂⋎g s ∈⋎g g)
	∧ (∀s t⦁ s ∈⋎g g ∧ t ∈⋎g g ⇒ s ∩⋎g t ∈⋎g g)
	⌝);
a (REPEAT strip_tac
	THEN all_fc_tac [GClosePair⋎g, GCloseSing, GClose∪⋎g, GClose⋂⋎g, GClose∩⋎g]);
val GClose_fc_clauses2 = save_pop_thm "GClose_fc_clauses2";
=TEX
}%ignore

=GFT
⦏tc∈_clauses⦎ =	⊢ ∀ s⦁	s ∈⋎g⋏+ Sing s
			∧ 	s ∈⋎g⋏+ ℙ⋎g s
			∧ ∀t⦁	t ∈⋎g⋏+ Pair⋎g s t
			∧ 	s ∈⋎g⋏+ Pair⋎g s t
=TEX

\ignore{
=SML
set_goal([], ⌜∀ s⦁	s ∈⋎g⋏+ Sing s
		∧ 	s ∈⋎g⋏+ ℙ⋎g s
		∧ ∀t⦁	t ∈⋎g⋏+ Pair⋎g s t
		∧ 	s ∈⋎g⋏+ Pair⋎g s t⌝);
a (rewrite_tac[]);
val tc∈_clauses = save_pop_thm "tc∈_clauses";
=TEX
}%ignore


\subsection{Proof Context}

To simplify subsequent proofs a new "proof context" is created enabling automatic use of the results now available.

\subsubsection{Principles}

The only principle I know of which assists with elementary proofs in set theory is the principle that set theoretic conjectures can be reduced to the predicate calculus by using extensional rules for relations and for operators.

Too hasty a reduction can be overkill and may convert a simple conjecture into an unintelligible morass.
We have sometimes in the past used made available two proof contexts, an aggressive extensional one, and a milder non-extensional one.
However, the extensional rules for the operators are fairly harmless, expansion is triggered by the extensional rules for the relations (equality and subset), so a proof context containing the former together with a suitable theorem for the latter gives good control.

\subsubsection{Theorems Used Recklessly}

This is pretty much guesswork, only time will tell whether this is the best collection.

=SML
val gst_ax_thms = [
	∅⋎g_spec,
	get_spec ⌜ℙ⋎g⌝,
	get_spec ⌜⋃⋎g⌝,
	Imagep_spec,
	Pair⋎g_eq_thm,
	get_spec ⌜Pair⋎g⌝,
	Sing_eq_thm,
	Sing_thm,
	Pair⋎g_Sing_eq_thm,
	Sing_Pair⋎g_eq_thm,
	Sep_thm,
	∪⋎g_thm,
	∩⋎g_thm
];

val gst_opext_clauses =
	(all_∀_intro
	o list_∧_intro
	o (map all_∀_elim))
	gst_ax_thms;
save_thm ("gst_opext_clauses", gst_opext_clauses);
=TEX

\subsubsection{Theorems Used Cautiously}

The following theorems are too aggressive for general use in the proof context but are needed when attempting automatic proof.
When an extensional proof is appropriate it can be initiated by a cautious (i.e. a "once") rewrite using the following clauses, after which the extensional rules in the proof context will be triggered.

=SML
val gst_relext_clauses =
	(all_∀_intro
	o list_∧_intro
	o (map all_∀_elim))
	[gs_ext_axiom,
	get_spec⌜$⊆⋎g⌝];
save_thm ("gst_relext_clauses", gst_relext_clauses);
=TEX

There are a number of important theorems, such as well-foundedness and galaxy closure which have not been mentioned in this context.
The character of these theorems makes them unsuitable for the proof context, their application requires thought.

\subsubsection{Automatic Proof}

The basic proof automation is augmented by adding a preliminary rewrite with the relational extensionality clauses.

=SML
fun gst_ax_prove_conv thl =
	TRY_C (pure_rewrite_conv [gst_relext_clauses])
	THEN_C (basic_prove_conv thl);
=TEX

\subsubsection{Proof Context 'gst-ax}

=SML
val nost_thms = [galaxy_Gx, t_in_Gx_t_thm];

add_rw_thms (gst_ax_thms @ nost_thms) "'gst-ax";
add_sc_thms (gst_ax_thms @ nost_thms) "'gst-ax";
add_st_thms gst_ax_thms "'gst-ax";
set_pr_conv gst_ax_prove_conv "'gst-ax";
set_pr_tac
	(conv_tac o gst_ax_prove_conv)
	"'gst-ax";
commit_pc "'gst-ax";
=TEX

Using the proof context "'gst-ax" elementary results in gst are now provable automatically on demand.
For this reason it is not necessary to prove in advance of needing them results such as the associativity of intersection, since they can be proven when required by an expression of the form "prove rule[] term" which proves {\it term} and returns it as a theorem.
If the required proof context for doing this is not in place the form ``
=INLINEFT
merge_pcs_rule ["basic_hol", 'gst-ax"] (prove_rule []) term
=TEX
'' may be used.
Since this is a little cumbersome we define the function {\it $gst\_ax\_rule$} and illustrate its use as follows:

=SML
val gst_ax_rule =
	(merge_pcs_rule1
	["basic_hol", "'gst-ax"]
	prove_rule) [];
val gst_ax_conv = 
	MERGE_PCS_C1
	["basic_hol", "'gst-ax"]
	prove_conv;
val gst_ax_tac =
	conv_tac o gst_ax_conv;
=TEX

\subsubsection{Examples}

The following are examples of the elementary results which are now proven automatically:
=SML
gst_ax_rule ⌜
	a ∩⋎g (b ∩⋎g c)
	= (a ∩⋎g b) ∩⋎g c⌝;
gst_ax_rule ⌜a ∩⋎g b ⊆⋎g b⌝;
gst_ax_rule ⌜∅⋎g ∪⋎g b = b⌝;
gst_ax_rule ⌜
	a ⊆⋎g b ∧ c ⊆⋎g d
	⇒ a ∩⋎g c ⊆⋎g b ∩⋎g d⌝;
gst_ax_rule ⌜Sep b p ⊆⋎g b⌝;
gst_ax_rule ⌜a ⊆⋎g b ⇒
	Imagep f a ⊆⋎g Imagep f b⌝;
=IGN
Imagep_axiom;
set_goal([],⌜a ⊆⋎g b ∧ c ⊆⋎g d
	⇒ Imagep f (a ∩⋎g c)
	⊆⋎g Imagep f (b ∩⋎g d)⌝);
a (once_rewrite_tac
	[gst_relext_clauses]);
a (gst_ax_tac[]);
a (rewrite_tac[]);
a (prove_tac[]);
a contr_tac;
Sep_thm;
=TEX

\section{Products and Sums}

A new "gst-fun" theory is created as a child of "gst-ax".
The theory will contain the definitions of ordered pairs, cartesian product, relations and functions, dependent products (functions), dependent sums (disjoint unions) and related material for general use.

=SML
open_theory "gst-ax";
force_new_theory "gst-fun";
force_new_pc "'gst-fun";
merge_pcs ["'savedthm_cs_∃_proof"] "'gst-fun";
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-fun"];
=TEX

\subsection{Ordered Pairs}

=SML
declare_infix (240,"↦⋎g");
=TEX

I first attempted to define ordered pairs in a more abstract way than by explicit use of the Wiener-Kuratovski representation, but this gace me problems so I eventually switched to the explicit definition.

This influences the development of the theory, since the first thing I do is to replicate the previously used defining properties.

ⓈHOLCONST
│ $⦏↦⋎g⦎ : GS → GS → GS
├────────────
│ ∀s t⦁ (s ↦⋎g t) = Pair⋎g (Sing s) (Pair⋎g s t)
■

=GFT
⦏↦⋎g_eq_thm⦎ =			⊢ ∀ s t u v⦁ (s ↦⋎g t = u ↦⋎g v) = (s = u ∧ t = v)
⦏Pair⋎g_∈_↦⋎g_thm⦎ =		⊢ ∀s t⦁ Pair⋎g s t ∈⋎g s ↦⋎g t
⦏Pair⋎g_∈⋎g_Gx_↦⋎g_thm⦎ =	⊢ ∀ s t⦁ Pair⋎g s t ∈⋎g Gx (s ↦⋎g t)
⦏↦⋎g_spec_thm⦎ =		⊢ (∀ s t u v⦁ (s ↦⋎g t = u ↦⋎g v) = (s = u ∧ t = v))
       				∧ (∀ s t⦁ Pair⋎g s t ∈⋎g s ↦⋎g t)
       				∧ (∀ s t⦁ Pair⋎g s t ∈⋎g Gx (s ↦⋎g t))
⦏↦⋎g_∈⋎g_Gx_Pair⋎g_thm⦎ =	⊢ ∀ s t⦁ s ↦⋎g t ∈⋎g Gx (Pair⋎g s t)
=TEX

\ignore{
=SML
set_goal([], ⌜∀s t u v:GS⦁
	(s ↦⋎g t = u ↦⋎g v ⇔ s = u ∧ t = v)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜$↦⋎g⌝] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN REPEAT strip_tac);
val ↦⋎g_eq_thm = save_pop_thm "↦⋎g_eq_thm";
 
set_goal([], ⌜∀s t⦁ Pair⋎g s t ∈⋎g (s ↦⋎g t)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜$↦⋎g⌝] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN REPEAT strip_tac);
val Pair⋎g_∈_↦⋎g_thm = save_pop_thm "Pair⋎g_∈_↦⋎g_thm";

set_goal([], ⌜∀s t⦁ Pair⋎g s t ∈⋎g Gx (s ↦⋎g t)⌝);
a (rewrite_tac[get_spec ⌜$↦⋎g⌝] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN REPEAT strip_tac);
a (lemma_tac ⌜galaxy (Gx (Pair⋎g s t))⌝
	THEN1 rewrite_tac [galaxy_Gx]);
a (lemma_tac ⌜Pair⋎g s t ∈⋎g Gx (Pair⋎g s t)⌝
	THEN1 rewrite_tac [t_in_Gx_t_thm]);
a (strip_asm_tac (∀_elim ⌜Gx (Pair⋎g s t)⌝ GClosePair⋎g));
a (lemma_tac ⌜(Sing s) ∈⋎g Gx (Pair⋎g s t)⌝);
(* *** Goal "1" *** *)
a (lemma_tac ⌜s ∈⋎g Gx (Pair⋎g s t)⌝);
(* *** Goal "1.1" *** *)
a (fc_tac [GalaxiesTransitive_thm]);
a (fc_tac [get_spec ⌜transitive⌝]);
a (LEMMA_T ⌜Pair⋎g s t ⊆⋎g Gx (Pair⋎g s t)⌝ ante_tac
	THEN1 asm_fc_tac[]
	THEN once_rewrite_tac [gst_relext_clauses]
	THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜s⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜Pair⋎g⌝]);
(* *** Goal "1.2" *** *)
a (strip_asm_tac (∀_elim ⌜Gx (Pair⋎g s t)⌝ GCloseSing)
	THEN asm_fc_tac[]);
(* *** Goal "2" *** *)
a (LEMMA_T ⌜(Pair⋎g s t) ∈⋎g (Pair⋎g (Sing s) (Pair⋎g s t))⌝asm_tac 
	THEN1 (once_rewrite_tac [get_spec ⌜Pair⋎g⌝]
		THEN REPEAT strip_tac));
a (LEMMA_T ⌜Gx (Pair⋎g s t) ⊆⋎g Gx (Pair⋎g (Sing s) (Pair⋎g s t))⌝ ante_tac
	THEN1 (all_fc_tac [Gx_mono_thm2]));
a (once_rewrite_tac [get_spec ⌜$⊆⋎g⌝]
	THEN STRIP_T (fn x => all_fc_tac [x]));
val Pair⋎g_∈⋎g_Gx_↦⋎g_thm = save_pop_thm "Pair⋎g_∈⋎g_Gx_↦⋎g_thm";

set_goal([], ⌜∀s t⦁ s ↦⋎g t ∈⋎g Gx (Pair⋎g s t)⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜$↦⋎g⌝]);
a (lemma_tac ⌜galaxy (Gx (Pair⋎g s t))⌝
	THEN1 rewrite_tac [galaxy_Gx]);
a (lemma_tac ⌜Pair⋎g s t ∈⋎g Gx (Pair⋎g s t)⌝
	THEN1 rewrite_tac [t_in_Gx_t_thm]);
a (lemma_tac ⌜(Sing s) ∈⋎g Gx (Pair⋎g s t)⌝);
(* *** Goal "1" *** *)
a (lemma_tac ⌜s ∈⋎g Gx (Pair⋎g s t)⌝);
(* *** Goal "1.1" *** *)
a (fc_tac [GalaxiesTransitive_thm]);
a (fc_tac [get_spec ⌜transitive⌝]);
a (LEMMA_T ⌜Pair⋎g s t ⊆⋎g Gx (Pair⋎g s t)⌝ ante_tac
	THEN1 asm_fc_tac[]
	THEN once_rewrite_tac [gst_relext_clauses]
	THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜s⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜Pair⋎g⌝]);
(* *** Goal "1.2" *** *)
a (strip_asm_tac (∀_elim ⌜Gx (Pair⋎g s t)⌝ GCloseSing)
	THEN asm_fc_tac[]);
(* *** Goal "2" *** *)
a (strip_asm_tac (list_∀_elim [⌜Gx (Pair⋎g s t)⌝] GClosePair⋎g));
a (all_asm_fc_tac[]);
val ↦⋎g_∈⋎g_Gx_Pair⋎g_thm = save_pop_thm "↦⋎g_∈⋎g_Gx_Pair⋎g_thm";

val ↦⋎g_spec_thm = list_∧_intro [↦⋎g_eq_thm, Pair⋎g_∈_↦⋎g_thm, Pair⋎g_∈⋎g_Gx_↦⋎g_thm];
=TEX

=SML
add_pc_thms "'gst-fun" [↦⋎g_spec_thm];
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-fun"];
=TEX
}%ignore

=GFT
⦏¬↦⋎g∅⋎g_thm⦎ =	⊢ ∀ x y⦁ ¬ x ↦⋎g y = ∅⋎g
⦏¬∅⋎g↦⋎g_thm⦎ =	⊢ ∀ x y⦁ ¬ ∅⋎g = x ↦⋎g y
⦏GClose↦⋎g_thm⦎ =	⊢ ∀ g⦁ galaxy g ⇒ (∀ s t⦁ s ∈⋎g g ∧ t ∈⋎g g ⇒ s ↦⋎g t ∈⋎g g)
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y⦁ ¬ x ↦⋎g y = ∅⋎g⌝);
a (REPEAT strip_tac THEN once_rewrite_tac [gs_ext_axiom] THEN REPEAT strip_tac);
a (∃_tac ⌜Pair⋎g x y⌝ THEN rewrite_tac [↦⋎g_spec_thm]);
val ¬↦⋎g∅⋎g_thm = save_pop_thm "¬↦⋎g∅⋎g_thm";

set_goal([], ⌜∀x y⦁ ¬ ∅⋎g = x ↦⋎g y⌝);
a (REPEAT strip_tac THEN once_rewrite_tac [gs_ext_axiom] THEN REPEAT strip_tac);
a (∃_tac ⌜Pair⋎g x y⌝ THEN rewrite_tac [↦⋎g_spec_thm]);
val ¬∅⋎g↦⋎g_thm = save_pop_thm "¬∅⋎g↦⋎g_thm";

set_goal([], ⌜∀g⦁  galaxy g ⇒ (∀s t⦁ s ∈⋎g g ∧ t ∈⋎g g ⇒ s ↦⋎g t ∈⋎g g)⌝);
a (REPEAT strip_tac THEN rewrite_tac[get_spec ⌜$↦⋎g⌝]);
a (all_fc_tac [GClose_fc_clauses2]);
a (all_fc_tac [GClose_fc_clauses2]);
val GClose↦⋎g_thm = save_pop_thm "GClose↦⋎g_thm";
=TEX
}%ignore

=GFT
⦏tc∈_↦_left_thm⦎ =	⊢ ∀ s t⦁ s ∈⋎g⋏+ s ↦⋎g t
⦏tc∈_↦_right_thm⦎ =	⊢ ∀ s t⦁ t ∈⋎g⋏+ s ↦⋎g t
=TEX

\ignore{
=SML
set_goal([], ⌜∀s t:GS⦁ s ∈⋎g⋏+ s ↦⋎g t⌝);
a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜$↦⋎g⌝]);
a (lemma_tac ⌜Sing s ∈⋎g⋏+ Pair⋎g (Sing s) (Pair⋎g s t)⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜s ∈⋎g⋏+ Sing s⌝ THEN1 rewrite_tac[]);
a (all_fc_tac[tc∈_trans_thm]);
val tc∈_↦_left_thm = save_pop_thm "tc∈_↦_left_thm";

set_goal([], ⌜∀s t:GS⦁ t ∈⋎g⋏+ s ↦⋎g t⌝);
a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜$↦⋎g⌝]);
a (lemma_tac ⌜Pair⋎g s t ∈⋎g⋏+ Pair⋎g (Sing s) (Pair⋎g s t)⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜t ∈⋎g⋏+ Pair⋎g s t⌝ THEN1 rewrite_tac[]);
a (all_fc_tac[tc∈_trans_thm]);
val tc∈_↦_right_thm = save_pop_thm "tc∈_↦_right_thm";
=TEX

=SML
add_pc_thms "'gst-fun" [¬↦⋎g∅⋎g_thm, ¬∅⋎g↦⋎g_thm];
add_rw_thms [↦⋎g_∈⋎g_Gx_Pair⋎g_thm, tc∈_↦_left_thm, tc∈_↦_right_thm] "'gst-fun";
add_sc_thms [↦⋎g_∈⋎g_Gx_Pair⋎g_thm, tc∈_↦_left_thm, tc∈_↦_right_thm] "'gst-fun";
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-fun"];
=TEX
}%ignore

\subsubsection{Projections}

The following functions may be used for extracting the components of ordered pairs.

\ignore{
=SML
set_goal([], ⌜∃ fst snd⦁
∀s t⦁
	fst(s ↦⋎g t) = s
	∧ snd(s ↦⋎g t) = t⌝);
a (∃_tac ⌜λp⦁εx⦁∃y⦁p=x ↦⋎g y⌝);
a (∃_tac ⌜λp⦁εy⦁∃x⦁p=x ↦⋎g y⌝);
a (rewrite_tac[] THEN REPEAT ∀_tac);
a (all_ε_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜t⌝ THEN ∃_tac ⌜s⌝
 THEN prove_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜s⌝ THEN ∃_tac ⌜t⌝
 THEN prove_tac[]);
(* *** Goal "3" *** *)
a (∃_tac ⌜t⌝ THEN ∃_tac ⌜s⌝
 THEN prove_tac[]);
(* *** Goal "4" *** *)
a (eq_sym_nth_asm_tac 1);
a (eq_sym_nth_asm_tac 4);
a (asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏fst⦎ ⦏snd⦎ : GS → GS
├──────────
│ ∀s t⦁ fst(s ↦⋎g t) = s	∧ snd(s ↦⋎g t) = t
■

=GFT
⦏↦_tc_thm⦎ =	⊢ ∀ x y⦁ tc $∈⋎g x (x ↦⋎g y) ∧ tc $∈⋎g y (x ↦⋎g y)
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y⦁ tc $∈⋎g x (x ↦⋎g y) ∧ tc $∈⋎g y (x ↦⋎g y)⌝);
a (REPEAT ∀_tac);
a (LEMMA_T ⌜Pair⋎g x y ∈⋎g (x ↦⋎g y) ∧ x ∈⋎g Pair⋎g x y ∧ y ∈⋎g Pair⋎g x y⌝
	(REPEAT_TTCL ∧_THEN asm_tac)
	THEN1 (rewrite_tac [↦⋎g_spec_thm, Pair⋎g_∈_thm]
		THEN all_var_elim_asm_tac));
a (fc_tac [tc_incr_thm]);
a (all_fc_tac [tran_tc_thm2]
	THEN asm_rewrite_tac[]);
val ↦_tc_thm = save_pop_thm "↦_tc_thm";
=TEX

=SML
add_pc_thms "'gst-fun" [get_spec ⌜fst⌝];
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-fun"];
=TEX
}%ignore

\subsubsection{MkPair and MkTriple}

It proves convenient to have constructors which take HOL pairs and triples as parameters.

ⓈHOLCONST
│ ⦏MkPair⋎g⦎ : GS × GS → GS
├──────────
│ ∀lr⦁ MkPair⋎g lr = (Fst lr) ↦⋎g (Snd lr)
■

ⓈHOLCONST
│ ⦏MkTriple⋎g⦎ : GS × GS × GS → GS
├──────────
│ ∀t⦁ MkTriple⋎g t = (Fst t) ↦⋎g (MkPair⋎g (Snd t))
■

\ignore{
=IGN

set_goal([], ⌜∀x y⦁ x ∈⋎g⋏+ MkPair ⌝);

=TEX
}%ignore

\subsection{Relations}

ⓈHOLCONST
│ ⦏rel⦎ : GS → BOOL
├───────────
│ ∀x⦁ rel x ⇔ ∀y⦁ y ∈⋎g x ⇒ ∃s t⦁ y = s ↦⋎g t
■

\ignore{
=SML
val rel⋎g_def = get_spec ⌜rel⌝;
=TEX
}%ignore

=GFT
⦏rel_∅⋎g_thm⦎ =	⊢ rel ∅⋎g
=TEX

\ignore{
=SML
val rel_∅⋎g_thm = prove_thm (
	"rel_∅⋎g_thm",
	⌜rel ∅⋎g⌝,
	prove_tac[get_spec⌜rel⌝]);
=TEX
}%ignore

The domain is the set of elements which are related to something under the relationship.

ⓈHOLCONST
│ ⦏dom⦎ : GS → GS
├──────────
│ ∀x⦁ dom x = Sep (Gx x) (λw⦁ ∃v⦁ w ↦⋎g v ∈⋎g x)
■

=GFT
⦏dom_∅⋎g_thm⦎ =		⊢ dom ∅⋎g = ∅⋎g
⦏dom_thm⦎ =		⊢ ∀ r y⦁ y ∈⋎g dom r ⇔ (∃ x⦁ y ↦⋎g x ∈⋎g r)
⦏dom_Gx_thm⦎ =	⊢ ∀ r⦁ dom r ∈⋎g Gx r
⦏GClose_dom_thm⦎ =	⊢ ∀ g⦁ galaxy g ⇒ (∀ r⦁ r ∈⋎g g ⇒ dom r ∈⋎g g)
=TEX

\ignore{
=SML
set_goal([],⌜dom ∅⋎g = ∅⋎g⌝);
a (prove_tac[get_spec⌜dom⌝, gst_relext_clauses]);
val dom_∅⋎g_thm = save_pop_thm "dom_∅⋎g_thm";

set_goal([], ⌜∀r y⦁ y ∈⋎g dom r ⇔ ∃ x⦁ y ↦⋎g x ∈⋎g r⌝);
a (rewrite_tac [get_spec ⌜dom⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (LEMMA_T  ⌜(Pair⋎g y x) ∈⋎g Gx (y ↦⋎g x)⌝ asm_tac
	THEN1 rewrite_tac [↦⋎g_spec_thm]);
a (lemma_tac ⌜Gx (y ↦⋎g x) ⊆⋎g Gx r⌝ THEN1 fc_tac [Gx_mono_thm2]);
a (LEMMA_T ⌜y ∈⋎g Pair⋎g y x⌝ asm_tac THEN1 rewrite_tac []);
a (lemma_tac ⌜y ∈⋎g Gx (y ↦⋎g x)⌝);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜galaxy (Gx (y ↦⋎g x))⌝ THEN1 rewrite_tac[galaxy_Gx]);
a (fc_tac [GalaxiesTransitive_thm]);
a (fc_tac [get_spec ⌜transitive⌝]);
a (ASM_FC_T (MAP_EVERY ante_tac) []
	THEN once_rewrite_tac [get_spec ⌜$⊆⋎g⌝]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "2.2" *** *)
a (DROP_NTH_ASM_T 3 (asm_tac o (once_rewrite_rule [get_spec⌜$⊆⋎g⌝])));
a (spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "3" *** *)
a (∃_tac ⌜x⌝ THEN strip_tac);
val dom_thm = save_pop_thm "dom_thm";

set_goal([], ⌜∀r⦁ dom r ∈⋎g Gx r⌝);
a (strip_tac THEN rewrite_tac [get_spec ⌜dom⌝]);
a (lemma_tac ⌜galaxy (Gx r)⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜Sep (Gx r) (λ w⦁ ∃ v⦁ w ↦⋎g v ∈⋎g r) = Sep (⋃⋎g (⋃⋎g r)) (λ w⦁ ∃ v⦁ w ↦⋎g v ∈⋎g r)⌝
	THEN1 (rewrite_tac [gst_relext_clauses] THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (∃_tac ⌜Pair⋎g e v⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜e ↦⋎g v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (lemma_tac ⌜e ∈⋎g⋏+ r⌝ THEN1 (
	ufc_tac [tc∈_incr_thm]
	THEN REPEAT_N 2 (all_ufc_tac [tc∈_trans_thm])));
a (asm_tac t_in_Gx_t_thm);
a (all_ufc_tac [tc∈_incr_thm]);
a (all_ufc_tac [tc∈_trans_thm]);
a (all_fc_tac [GClose_tc∈⋎g_thm]);
(* *** Goal "4" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "5" *** *)
a (asm_rewrite_tac[]);
a (lemma_tac ⌜r ∈⋎g Gx r⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜⋃⋎g r ∈⋎g Gx r⌝ THEN1 all_fc_tac[GClose_fc_clauses]);
a (lemma_tac ⌜(⋃⋎g (⋃⋎g r)) ∈⋎g Gx r⌝ THEN1 (all_fc_tac[GClose_fc_clauses]));
a (all_fc_tac [GClose_fc_clauses]);
a (asm_rewrite_tac[]);
val dom_Gx_thm = save_pop_thm "dom_Gx_thm"; 

set_goal([], ⌜∀g⦁ galaxy g ⇒ ∀r⦁ r ∈⋎g g ⇒ dom r ∈⋎g g⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜dom⌝]);
a (lemma_tac ⌜galaxy (Gx r)⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜Sep (Gx r) (λ w⦁ ∃ v⦁ w ↦⋎g v ∈⋎g r) = Sep (⋃⋎g (⋃⋎g r)) (λ w⦁ ∃ v⦁ w ↦⋎g v ∈⋎g r)⌝
	THEN1 (rewrite_tac [gst_relext_clauses] THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (∃_tac ⌜Pair⋎g e v⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜e ↦⋎g v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (lemma_tac ⌜e ∈⋎g⋏+ r⌝ THEN1 (
	ufc_tac [tc∈_incr_thm]
	THEN REPEAT_N 2 (all_ufc_tac [tc∈_trans_thm])));
a (asm_tac t_in_Gx_t_thm);
a (all_ufc_tac [tc∈_incr_thm]);
a (all_ufc_tac [tc∈_trans_thm]);
a (all_fc_tac [GClose_tc∈⋎g_thm]);
(* *** Goal "4" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "5" *** *)
a (asm_rewrite_tac[]);
a (lemma_tac ⌜r ∈⋎g Gx r⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜⋃⋎g r ∈⋎g Gx r⌝ THEN1 all_fc_tac[GClose_fc_clauses]);
a (lemma_tac ⌜(⋃⋎g (⋃⋎g r)) ∈⋎g Gx r⌝ THEN1 (all_fc_tac[GClose_fc_clauses]));
a (lemma_tac ⌜⋃⋎g r ∈⋎g g⌝ THEN1 all_fc_tac [GClose_fc_clauses]);
a (lemma_tac ⌜⋃⋎g (⋃⋎g r) ∈⋎g g⌝ THEN1 all_fc_tac [GClose_fc_clauses]);
a (lemma_tac ⌜∀ p⦁ Sep (⋃⋎g (⋃⋎g r)) p ∈⋎g g⌝ THEN1 all_fc_tac [GClose_fc_clauses]);
a (asm_rewrite_tac[]);
val GClose_dom_thm = save_pop_thm "GClose_dom_thm";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏ran⦎ : GS → GS
├────────────
│ ∀x⦁ ran x = Sep (Gx x) (λw⦁ ∃v⦁ v ↦⋎g w ∈⋎g x)
■

=GFT
⦏ran_∅⋎g_thm⦎ =		⊢ ran ∅⋎g = ∅⋎g
⦏ran_thm⦎ =		⊢ ∀r y⦁ y ∈⋎g ran r ⇔ ∃ x⦁ x ↦⋎g y ∈⋎g r
⦏GClose_ran_thm⦎ =	⊢ ∀ g⦁ galaxy g ⇒ (∀ r⦁ r ∈⋎g g ⇒ ran r ∈⋎g g)
⦏tc∈_ran_thm⦎ = 		⊢ ∀ x y⦁ x ∈⋎g⋏+ ran y ⇒ x ∈⋎g⋏+ y
=TEX

\ignore{
=SML
set_goal([],⌜ran ∅⋎g = ∅⋎g⌝);
a (prove_tac[get_spec ⌜ran⌝, gst_relext_clauses]);
val ran_∅⋎g_thm =	save_pop_thm "ran_∅⋎g_thm";

set_goal([], ⌜∀r y⦁ y ∈⋎g ran r ⇔ ∃ x⦁ x ↦⋎g y ∈⋎g r⌝);
a (rewrite_tac [get_spec ⌜ran⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (LEMMA_T  ⌜(Pair⋎g x y) ∈⋎g Gx (x ↦⋎g y)⌝ asm_tac
	THEN1 rewrite_tac [↦⋎g_spec_thm]);
a (lemma_tac ⌜Gx (x ↦⋎g y) ⊆⋎g Gx r⌝ THEN1 fc_tac [Gx_mono_thm2]);
a (LEMMA_T ⌜y ∈⋎g Pair⋎g x y⌝ asm_tac THEN1 rewrite_tac []);
a (lemma_tac ⌜y ∈⋎g Gx (x ↦⋎g y)⌝);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜galaxy (Gx (x ↦⋎g y))⌝ THEN1 rewrite_tac[galaxy_Gx]);
a (fc_tac [GalaxiesTransitive_thm]);
a (fc_tac [get_spec ⌜transitive⌝]);
a (ASM_FC_T (MAP_EVERY ante_tac) []
	THEN once_rewrite_tac [get_spec ⌜$⊆⋎g⌝]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "2.2" *** *)
a (DROP_NTH_ASM_T 3 (asm_tac o (once_rewrite_rule [get_spec⌜$⊆⋎g⌝])));
a (spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "3" *** *)
a (∃_tac ⌜x⌝ THEN strip_tac);
val ran_thm = save_pop_thm "ran_thm";

set_goal([], ⌜∀g⦁ galaxy g ⇒ ∀r⦁ r ∈⋎g g ⇒ ran r ∈⋎g g⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜ran⌝]);
a (lemma_tac ⌜galaxy (Gx r)⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜Sep (Gx r) (λ w⦁ ∃ v⦁ v ↦⋎g w ∈⋎g r) = Sep (⋃⋎g (⋃⋎g r)) (λ w⦁ ∃ v⦁ v ↦⋎g w ∈⋎g r)⌝
	THEN1 (rewrite_tac [gst_relext_clauses] THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (∃_tac ⌜Pair⋎g v e⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜v ↦⋎g e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (lemma_tac ⌜e ∈⋎g⋏+ r⌝ THEN1 (
	ufc_tac [tc∈_incr_thm]
	THEN REPEAT_N 2 (all_ufc_tac [tc∈_trans_thm])));
a (asm_tac t_in_Gx_t_thm);
a (all_ufc_tac [tc∈_incr_thm]);
a (all_ufc_tac [tc∈_trans_thm]);
a (all_fc_tac [GClose_tc∈⋎g_thm]);
(* *** Goal "4" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "5" *** *)
a (asm_rewrite_tac[]);
a (lemma_tac ⌜r ∈⋎g Gx r⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜⋃⋎g r ∈⋎g Gx r⌝ THEN1 all_fc_tac[GClose_fc_clauses]);
a (lemma_tac ⌜(⋃⋎g (⋃⋎g r)) ∈⋎g Gx r⌝ THEN1 (all_fc_tac[GClose_fc_clauses]));
a (lemma_tac ⌜⋃⋎g r ∈⋎g g⌝ THEN1 all_fc_tac [GClose_fc_clauses]);
a (lemma_tac ⌜⋃⋎g (⋃⋎g r) ∈⋎g g⌝ THEN1 all_fc_tac [GClose_fc_clauses]);
a (lemma_tac ⌜∀ p⦁ Sep (⋃⋎g (⋃⋎g r)) p ∈⋎g g⌝ THEN1 (all_fc_tac [GClose_fc_clauses]));
a (asm_rewrite_tac[]);
val GClose_ran_thm = save_pop_thm "GClose_ran_thm";

set_goal([], ⌜∀x y⦁ $∈⋎g⋏+ x (ran y) ⇒ $∈⋎g⋏+ x y⌝);
a (REPEAT strip_tac);
a (fc_tac [tc∈_cases_thm]);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac);
a (rewrite_tac [ran_thm] THEN REPEAT strip_tac);
a (lemma_tac ⌜$∈⋎g⋏+ x (x' ↦⋎g x)⌝ THEN1 rewrite_tac [tc∈_↦_right_thm]);
a (fc_tac [tc∈_incr_thm]);
a (all_fc_tac [tc∈_trans_thm]);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac);
a (rewrite_tac [ran_thm] THEN REPEAT strip_tac);
a (lemma_tac ⌜$∈⋎g⋏+ z (x' ↦⋎g z)⌝ THEN1 rewrite_tac [tc∈_↦_right_thm]);
a (fc_tac [tc∈_incr_thm]);
a (all_ufc_tac [tc∈_trans_thm]);
a (all_ufc_tac [tc∈_trans_thm]);
val tc∈_ran_thm = save_pop_thm "tc∈_ran_thm";
=TEX
}%ignore

\ignore{
=SML
set_goal([],⌜∃field⦁ ∀s e⦁
e ∈⋎g (field s) ⇔ e ∈⋎g (dom s) ∨ e ∈⋎g (ran s)⌝);
a (∃_tac ⌜λx⦁ (dom x) ∪⋎g (ran x)⌝);
a (prove_tac[]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏field⦎: GS → GS
├─────────
│ ∀s e⦁ e ∈⋎g (field s) ⇔ e ∈⋎g (dom s) ∨ e ∈⋎g (ran s)
■

=GFT
⦏field_∅⋎g_thm⦎ =	⊢ field ∅⋎g = ∅⋎g
=TEX

\ignore{
=SML
add_pc_thms "'gst-fun" ([
	get_spec ⌜field⌝,
	rel_∅⋎g_thm,
	dom_∅⋎g_thm,
	ran_∅⋎g_thm]);
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-fun"];

set_goal([],⌜field ∅⋎g = ∅⋎g⌝);
a (prove_tac[gst_relext_clauses]);
val field_∅⋎g_thm = save_pop_thm "field_∅⋎g_thm";
add_pc_thms "'gst-fun" ([field_∅⋎g_thm]);
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-fun"];
=TEX
}%ignore

\subsection{Domain and Range Restrictions}

=SML
declare_infix (300, "◁⋎g");
declare_infix (300, "▷⋎g");
declare_infix (300, "⩤⋎g");
declare_infix (300, "⩥⋎g");
=TEX

ⓈHOLCONST
│ $⦏◁⋎g⦎: GS → GS → GS
├──────
│ ∀s r⦁ s ◁⋎g r = Sep r (λp⦁ fst p ∈⋎g s)
■

ⓈHOLCONST
│ $⦏▷⋎g⦎: GS → GS → GS
├──────
│ ∀s r⦁ r ▷⋎g s = Sep r (λp⦁ snd p ∈⋎g s)
■

ⓈHOLCONST
│ $⦏⩤⋎g⦎: GS → GS → GS
├──────
│ ∀s r⦁ s ⩤⋎g r = Sep r (λp⦁ ¬ fst p ∈⋎g s)
■

ⓈHOLCONST
│ $⦏⩥⋎g⦎: GS → GS → GS
├──────
│ ∀s r⦁ r ⩥⋎g s = Sep r (λp⦁ ¬ snd p ∈⋎g s)
■

=SML
declare_alias ("◁", ⌜$◁⋎g⌝);
declare_alias ("▷", ⌜$▷⋎g⌝);
declare_alias ("⩤", ⌜$⩤⋎g⌝);
declare_alias ("⩥", ⌜$⩥⋎g⌝);
=TEX

\subsection{Dependent Types}

Any relation may be regarded as a dependent sum type.
When so regarded, each ordered pair in the relation consist with a type-index and a value whose type is that associated with the type.

The indexed set of types, relative to which every pair in the relation is well-typed may be retrieved from the relation as follows.

ⓈHOLCONST
│ ⦏Rel2DepType⋎g⦎ : GS → GS
├─────────────
│ ∀r⦁ Rel2DepType⋎g r = Sep
│		(Gx r)
│		(λe⦁ ∃i t:GS⦁
│			e = i ↦⋎g t
│			∧ i ∈⋎g dom r
│			∧ (∀j⦁ j ∈⋎g t ⇔ i ↦⋎g j ∈⋎g r))
■

\ignore{
=IGN
stop;
set_goal([], ⌜∀r e⦁ rel r ⇒
	(e ∈⋎g Rel2DepType⋎g r
	⇔ ∃i t:GS⦁ e = i ↦⋎g t
			∧ i ∈⋎g dom r
			∧ (∀j⦁ j ∈⋎g t ⇔ i ↦⋎g j ∈⋎g r))⌝);
a (REPEAT_N 3 strip_tac THEN rewrite_tac [get_spec ⌜Rel2DepType⋎g⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜i⌝ THEN ∃_tac ⌜t⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜galaxy (Gx r)⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜r ∈⋎g Gx r⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜dom r ∈⋎g (Gx r)⌝ THEN1 (all_fc_tac [GClose_dom_thm]));
a (lemma_tac ⌜i ∈⋎g (Gx r)⌝ THEN1 (
	all_fc_tac [tc∈_incr_thm]
	THEN all_fc_tac [tc∈_trans_thm]
	THEN all_fc_tac [GClose_tc∈⋎g_thm]));
a (lemma_tac ⌜t = Sep (ran r) (λj⦁ i ↦⋎g j ∈⋎g r)⌝
	THEN1 (rewrite_tac [gst_relext_clauses] THEN REPEAT strip_tac));
(* *** Goal "2.1" *** *)
a (rewrite_tac [ran_thm]);
a (asm_ufc_tac []);
a (∃_tac ⌜i⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (asm_ufc_tac []);
(* *** Goal "2.3" *** *)
a (SYM_ASMS_T ufc_tac);
(* *** Goal "2.4" *** *)
a (lemma_tac ⌜ran r ∈⋎g Gx r⌝ THEN1 all_fc_tac [GClose_ran_thm]);
a (lemma_tac ⌜Sep (ran r) (λ j⦁ i ↦⋎g j ∈⋎g r) ∈⋎g Gx r⌝
	THEN1 (ALL_FC_T  rewrite_tac[GClose_fc_clauses]));
stop;
a (lemma_tac ⌜⌝ THEN1 fc_tac [tc∈_incr_thm]);


a (∃_tac ⌜i⌝ THEN asm_rewrite_tac[]);

a (∃_tac ⌜⌝ THEN asm_rewrite_tac[]);

a (lemma_tac ⌜∀j⦁ j ∈⋎g t ⇒ j ∈⋎g⋏+ r⌝ THEN1 REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜i ↦⋎g j ∈⋎g r⌝ THEN1 asm_fc_tac[]);
a (lemma_tac ⌜j ∈⋎g⋏+ i ↦⋎g j⌝ THEN1 rewrite_tac[]);
a (all_fc_tac [tc∈_incr_thm] THEN all_fc_tac [tc∈_trans_thm]);
(* *** Goal "2.2" *** *)
a (lemma_tac ⌜⌝ THEN1 (asm_rewrite_tac[gst_relext_clauses]));
a (lemma_tac ⌜∀j⦁ j ∈⋎g t ⇒ j ∈⋎g r⌝
	THEN1 (REPEAT strip_tac
		THEN asm_fc_tac []
		THEN fc_tac [GClose_tc∈⋎g_thm]));
GClose_fc_clauses;

a (asm_rewrite_tac[]);
a (fc_tac [GClose↦⋎g_thm]);

a (lemma_tac ⌜t ∈⋎g Gx r⌝

a (∃_tac ⌜λr⦁ Sep
		(Gx r)
		(λe⦁ ∃i t:GS⦁
			e = i ↦⋎g t
			∧ i ∈⋎g dom r
			∧ (∀j⦁ j ∈⋎g t ⇔ i ↦⋎g j ∈⋎g r))⌝
	THEN rewrite_tac[]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜i⌝ THEN ∃_tac ⌜t⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜galaxy (Gx r)⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜i ∈⋎g Gx r ∧ t ∈⋎g Gx r⌝
a (fc_tac [GClose↦⋎g_thm]);
a (list_spec_nth_asm_tac 1 [⌜i⌝, ⌜t⌝]);
=TEX
}%ignore

Any similar indexed collection of sets, determines a set of ordered pairs and a set of functions according to the following definitions.

The dependent sums are as follows:

ⓈHOLCONST
│ ⦏DepSum⋎g⦎ : GS → GS
├─────────────
│ ∀t⦁ DepSum⋎g t = Sep
│		(Gx t)
│		(λe⦁ ∃i t2 v:GS⦁
│			e = i ↦⋎g v
│			∧ v ∈⋎g t2
│			∧ i ↦⋎g t2 ∈⋎g t)
■

=GFT
=TEX

\ignore{
=IGN
stop;

set_goal([], ⌜∀r⦁ rel r ⇒ DepSum⋎g (Rel2DepType⋎g r) = r⌝);
a (REPEAT strip_tac THEN rewrite_tac (map get_spec [⌜DepSum⋎g⌝, ⌜Rel2DepType⋎g⌝]));
a (once_rewrite_tac [gst_relext_clauses] THEN_TRY (rewrite_tac []) THEN REPEAT strip_tac THEN_TRY rewrite_tac[]);
(* *** Goal "1" *** *)
a (all_var_elim_asm_tac);
a (all_asm_fc_tac[]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)

=TEX
}%ignore

\ignore{
 ⓈHOLCONST
│ ⦏DepProd⋎g⦎ : GS → GS
├─────────────
│ ∀t⦁ DepProd⋎g t = Sep
│		(Gx t)
│		(λf⦁ dom f = dom t
│			∧ ∀e⦁ e ∈⋎g f ⇒ ∃a v⦁ e = a ↦⋎g v ∈⋎g f ⇒ )
 ■
}%ignore


\subsection{Dependent Sums and Cartesian Products}

=SML
declare_binder "Σ⋎g";
=TEX

ⓈHOLCONST
│ $⦏Σ⋎g⦎ : (GS → GS) → GS → GS
├───────────
│ ∀f s⦁  $Σ⋎g f s = ⋃⋎g (
│	Imagep	(λe⦁ Imagep (λx⦁ e ↦⋎g x) (f e))
│		s
│ )
■

=SML
declare_infix(240,"×⋎g");
=TEX

ⓈHOLCONST
│ $⦏×⋎g⦎ : GS → GS → GS
├───────────
│ ∀s t⦁ s ×⋎g t = ⋃⋎g (
│	Imagep
│	(λse⦁ (Imagep (λte⦁ se ↦⋎g te) t))
│	s)
■

\ignore{
=SML
set_goal([],⌜∀s t e⦁ e ∈⋎g s ×⋎g t ⇔
	∃l r⦁l ∈⋎g s ∧ r ∈⋎g t
	∧ e = l ↦⋎g r
⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$×⋎g⌝]);
a (prove_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜e''⌝
	THEN ∃_tac ⌜snd(e)⌝
	THEN asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 1 
	(fn x=> fc_tac [
	(once_rewrite_rule
		[gst_relext_clauses] x)]));
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜Imagep (λ te⦁ l ↦⋎g te) t⌝);
a (prove_tac[]);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜r⌝
 THEN prove_tac[]);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜l⌝ THEN prove_tac[]);
val ×⋎g_spec = save_pop_thm "×⋎g_spec";
=TEX
}%ignore


=GFT
⦏f↦⋎gs_thm⦎ =
	⊢ ∀ s t p⦁ p ∈⋎g s ×⋎g t ⇒ fst p ↦⋎g snd p = p

⦏v∈⋎g×⋎g_thm⦎ =
	⊢ ∀ p s t⦁ p ∈⋎g s ×⋎g t ⇒ fst p ∈⋎g s ∧ snd p ∈⋎g t

⦏↦⋎g∈⋎g×⋎g_thm⦎ =
	⊢ ∀ l r s t⦁ l ↦⋎g r ∈⋎g s ×⋎g t ⇔ (l ∈⋎g s ∧ r ∈⋎g t)
=TEX

\ignore{
=SML
set_goal ([],⌜∀s t p⦁ p ∈⋎g s ×⋎g t
	⇒ fst(p) ↦⋎g snd(p) = p⌝);
a (prove_tac[×⋎g_spec]);
a (asm_rewrite_tac[]);
val f↦⋎gs_thm = save_pop_thm "f↦⋎gs_thm";

set_goal([],⌜∀p s t⦁
	p ∈⋎g (s ×⋎g t)
	⇒ fst p ∈⋎g s ∧ snd p ∈⋎g t⌝);
a (prove_tac[×⋎g_spec]
      THEN_TRY asm_rewrite_tac[]);
val v∈⋎g×⋎g_thm = 
	save_pop_thm "v∈⋎g×⋎g_thm";

(*
add_pc_thms "'gst-fun" [v∈⋎g×⋎g_thm];
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-fun"];
*)

set_goal([],⌜∀l r s t⦁
	(l ↦⋎g r) ∈⋎g (s ×⋎g t)
	⇔ l ∈⋎g s ∧ r ∈⋎g t⌝);
a (prove_tac[×⋎g_spec]);
a (∃_tac ⌜l⌝
	THEN ∃_tac ⌜r⌝
	THEN asm_prove_tac[]);
val ↦⋎g∈⋎g×⋎g_thm = save_pop_thm "↦⋎g∈⋎g×⋎g_thm";

add_pc_thms "'gst-fun" [↦⋎g∈⋎g×⋎g_thm];
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-fun"];
=TEX
}%ignore

=GFT
=TEX

\ignore{
=IGN
stop;

set_goal([], ⌜s ×⋎g t ∈⋎g = {z | }⌝);

set_goal([], ⌜∀g⦁ galaxy g ⇒ (∀s t⦁ s ∈⋎g g ∧ t ∈⋎g g ⇒ s ×⋎g t ∈⋎g g)⌝);
a (REPEAT strip_tac THEN fc_tac [get_spec ⌜galaxy⌝, GCloseSep_thm, ]);

=TEX
}%ignore

\subsubsection{Relation Space}

This is the set of all relations over some domain and codomain, i.e. the power set of the cartesian product.

=SML
declare_infix(240,"↔⋎g");
=TEX

ⓈHOLCONST
│ $↔⋎g : GS → GS → GS
├───────────
│ ∀s t⦁ s ↔⋎g t = ℙ⋎g(s ×⋎g t)
■

=GFT
↔⋎g⊆⋎g×⋎g_thm =	⊢ ∀s t r⦁ r ∈⋎g s ↔⋎g t ⇔ r ⊆⋎g (s ×⋎g t)
∅⋎g∈⋎g↔⋎g_thm =	⊢ ∀s t⦁ ∅⋎g ∈⋎g s ↔⋎g t
=TEX

\ignore{
=SML
set_goal ([], ⌜∀s t r⦁ r ∈⋎g s ↔⋎g t ⇔ r ⊆⋎g (s ×⋎g t)⌝);
a (prove_tac[get_spec⌜$↔⋎g⌝, gst_relext_clauses]);
val ↔⋎g⊆⋎g×⋎g_thm = save_pop_thm "↔⋎g⊆⋎g×⋎g_thm";

set_goal ([], ⌜∀s t⦁ ∅⋎g ∈⋎g s ↔⋎g t⌝);
a (prove_tac[get_spec⌜$↔⋎g⌝,
	gst_relext_clauses]);
val ∅⋎g∈⋎g↔⋎g_thm = save_pop_thm "∅⋎g∈⋎g↔⋎g_thm";
add_pc_thms "'gst-fun" [∅⋎g∈⋎g↔⋎g_thm];
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-fun"];
=TEX
}%ignore

\subsubsection{Another Pair-Projection Inverse Theorem}

Couched in terms of membership of relation spaces.

=SML
set_goal ([], ⌜∀p r s t⦁
	p ∈⋎g r ∧
	r ∈⋎g s ↔⋎g t ⇒
	fst(p) ↦⋎g snd(p) = p⌝); 
a (prove_tac[
	get_spec ⌜$↔⋎g⌝,
	⊆⋎g_thm]); 
a (REPEAT
	(asm_fc_tac[f↦⋎gs_thm])); 
val f↦⋎gs_thm1 =
	save_pop_thm "f↦⋎gs_thm1"; 
=TEX

\subsubsection{Member of Relation Theorem}

=SML
set_goal ([],⌜∀p r s t⦁
	p ∈⋎g r ∧
	r ∈⋎g s ↔⋎g t ⇒
	fst(p) ∈⋎g s ∧
	snd(p) ∈⋎g t⌝); 
a (prove_tac[
	get_spec ⌜$↔⋎g⌝,
	⊆⋎g_thm]); 
a (asm_fc_tac[]); 
a (fc_tac[v∈⋎g×⋎g_thm]); 
a (asm_fc_tac[]); 
a (fc_tac[v∈⋎g×⋎g_thm]); 
val ∈⋎g↔⋎g_thm =
	save_pop_thm "∈⋎g↔⋎g_thm";
=TEX

\subsubsection{Relational Composition}

=SML
declare_infix (250,"o⋎g");
ⓈHOLCONST
 $o⋎g : GS → GS → GS
├
∀f g⦁ f o⋎g g =
	Imagep
	(λp⦁ (fst(fst p) ↦⋎g snd(snd p)))
	(Sep (g ×⋎g f) λp⦁ ∃q r s⦁ p = (q ↦⋎g r) ↦⋎g (r ↦⋎g s))
■

=GFT
o⋎g_thm =
   ⊢ ∀f g x⦁ x ∈⋎g f o⋎g g ⇔
	∃q r s⦁ q ↦⋎g r ∈⋎g g ∧ r ↦⋎g s ∈⋎g f
		∧ x = q ↦⋎g s
o⋎g_thm2 =
   ⊢ ∀ f g x y⦁ x ↦⋎g y ∈⋎g f o⋎g g
	⇔ (∃ z⦁ x ↦⋎g z ∈⋎g g ∧ z ↦⋎g y ∈⋎g f)

o⋎g_associative_thm =
   ⊢ ∀f g h⦁ (f o⋎g g) o⋎g h = f o⋎g g o⋎g h

o⋎g_rel_thm =
   ⊢ ∀ r s⦁ rel r ∧ rel s ⇒ rel (r o⋎g s)
=TEX

\ignore{
=SML
set_goal([], ⌜∀f g x⦁ x ∈⋎g f o⋎g g ⇔
	∃q r s⦁ q ↦⋎g r ∈⋎g g
	∧ r ↦⋎g s ∈⋎g f ∧ x = q ↦⋎g s⌝);
a (rewrite_tac (map get_spec [⌜$o⋎g⌝]));
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (MAP_EVERY ∃_tac [⌜q⌝, ⌜r⌝, ⌜s⌝]);
a (DROP_NTH_ASM_T 3 ante_tac
	THEN asm_rewrite_tac []);
(* *** Goal "2" *** *)
a (∃_tac ⌜(q ↦⋎g r) ↦⋎g r ↦⋎g s⌝
	THEN asm_rewrite_tac[]);
a (prove_∃_tac);
val o⋎g_thm = save_pop_thm "o⋎g_thm";
=SML
set_goal([], ⌜∀f g x y⦁ x ↦⋎g y ∈⋎g f o⋎g g ⇔
	∃z⦁ x ↦⋎g z ∈⋎g g
	∧ z ↦⋎g y ∈⋎g f⌝);
a (REPEAT_N 4 strip_tac
	THEN rewrite_tac [o⋎g_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜r⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (MAP_EVERY ∃_tac [⌜x⌝, ⌜z⌝, ⌜y⌝]
	THEN asm_rewrite_tac[]);
val o⋎g_thm2 = save_pop_thm "o⋎g_thm2";

set_goal ([], ⌜∀r s⦁ rel r ∧ rel s ⇒  rel (r o⋎g s)⌝);
a (rewrite_tac [get_spec ⌜rel⌝, o⋎g_thm] THEN REPEAT strip_tac);
a (∃_tac ⌜q⌝ THEN ∃_tac ⌜s'⌝ THEN strip_tac);
val o⋎g_rel_thm = save_pop_thm "o⋎g_rel_thm";

set_goal([], ⌜∀f g h⦁ (f o⋎g g) o⋎g h = f o⋎g (g o⋎g h)⌝);
a (once_rewrite_tac [gs_ext_axiom]);
a (rewrite_tac [o⋎g_thm]);
a (REPEAT step_strip_tac);
(* *** Goal "1" *** *)
a (prove_∃_tac THEN all_var_elim_asm_tac);
a (MAP_EVERY ∃_tac [⌜s'⌝, ⌜r'⌝] THEN asm_rewrite_tac[]);
a (∃_tac ⌜q⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜q'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (prove_∃_tac THEN all_var_elim_asm_tac);
a (MAP_EVERY ∃_tac [⌜s⌝, ⌜r'⌝] THEN asm_rewrite_tac[] THEN strip_tac);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜q'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜s'⌝ THEN asm_rewrite_tac[]);
val o⋎g_associative_thm = save_pop_thm "o⋎g_associative_thm"; 

add_pc_thms "'gst-fun" [o⋎g_thm2];
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-fun"];
=TEX
}%ignore

\subsubsection{Relation Subset of Cartesian Product}

=GFT
rel_sub_cp_thm = 
	⊢ ∀ x⦁ rel x ⇔ (∃ s t⦁ x ⊆⋎g s ×⋎g t)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀x⦁ rel x ⇔ ∃s t⦁ x ⊆⋎g s ×⋎g t⌝);
a (once_rewrite_tac [gst_relext_clauses]);
a (rewrite_tac[get_spec⌜rel⌝, ×⋎g_spec]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜dom x⌝ THEN ∃_tac ⌜ran x⌝ THEN REPEAT strip_tac);
a (asm_fc_tac[]);
a (∃_tac ⌜s⌝ THEN ∃_tac ⌜t⌝
	THEN asm_rewrite_tac[get_spec ⌜dom⌝, get_spec ⌜ran⌝]);
a (lemma_tac ⌜Pair⋎g s t ∈⋎g Gx e⌝ THEN1 asm_rewrite_tac [↦⋎g_spec_thm]);
a (LEMMA_T ⌜s ∈⋎g Pair⋎g s t⌝ asm_tac THEN1 rewrite_tac[]);
a (LEMMA_T ⌜t ∈⋎g Pair⋎g s t⌝ asm_tac THEN1 rewrite_tac[]);
a (all_fc_tac [Gx_trans_thm3]);
a (LEMMA_T ⌜Gx e ⊆⋎g Gx x⌝ (fn x => fc_tac [rewrite_rule [get_spec ⌜$⊆⋎g⌝] x])
	THEN1 fc_tac [Gx_mono_thm2]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (DROP_NTH_ASM_T 10 ante_tac THEN asm_rewrite_tac[] THEN strip_tac);
a (∃_tac ⌜t⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (DROP_NTH_ASM_T 10 ante_tac THEN asm_rewrite_tac[] THEN strip_tac);
a (∃_tac ⌜s⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_fc_tac[]);
a (∃_tac ⌜l⌝ THEN ∃_tac ⌜r⌝ THEN asm_rewrite_tac[]);
val rel_sub_cp_thm = save_pop_thm "rel_sub_cp_thm";
=TEX
}%ignore

\subsection{Functions}

Definition of partial and total functions and the corresponding function spaces.

\subsubsection{fun}

ⓈHOLCONST
 fun : GS → BOOL
├
∀x⦁ fun x ⇔ rel x ∧
	∀s t u⦁ s ↦⋎g u ∈⋎g x
		∧ s ↦⋎g t ∈⋎g x
		⇒ u = t
■

\ignore{
=SML
val fun_def = get_spec ⌜fun⌝;
=TEX
}%ignore

\subsubsection{lemmas}

=GFT
fun_∅⋎g_thm =
	⊢ fun ∅⋎g
o⋎g_fun_thm =
	⊢ ∀ f g⦁ fun f ∧ fun g ⇒ fun (f o⋎g g)
ran_o⋎g_thm =
	⊢ ∀ f g⦁ ran (f o⋎g g) ⊆⋎g ran f
dom_o⋎g_thm =
	⊢ ∀ f g⦁ dom (f o⋎g g) ⊆⋎g dom g
dom_o⋎g_thm2 =
	⊢ ∀ f g⦁ ran g ⊆⋎g dom f ⇒ dom (f o⋎g g) = dom g
=TEX
\ignore{
=SML
val fun_∅⋎g_thm = prove_thm (
	"fun_∅⋎g_thm", ⌜fun ∅⋎g⌝,
	prove_tac[
	 get_spec ⌜fun⌝]);

set_goal([], ⌜∀f g⦁ fun f ∧ fun g ⇒ fun (f o⋎g g)⌝);
a (rewrite_tac [get_spec ⌜fun⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [o⋎g_rel_thm]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜z = z'⌝ THEN1 all_asm_fc_tac[]);
a (all_var_elim_asm_tac THEN all_asm_fc_tac[]);
val o⋎g_fun_thm = save_pop_thm "o⋎g_fun_thm";

set_goal ([], ⌜∀f g⦁ ran (f o⋎g g) ⊆⋎g ran f⌝);
a (once_rewrite_tac [gst_relext_clauses]);
a (rewrite_tac [ran_thm] THEN REPEAT strip_tac);
a (∃_tac ⌜z⌝ THEN strip_tac);
val ran_o⋎g_thm = save_pop_thm "ran_o⋎g_thm";

set_goal ([], ⌜∀f g⦁ dom (f o⋎g g) ⊆⋎g dom g⌝);
a (once_rewrite_tac [gst_relext_clauses]);
a (rewrite_tac [dom_thm] THEN REPEAT strip_tac);
a (∃_tac ⌜z⌝ THEN strip_tac);
val dom_o⋎g_thm = save_pop_thm "dom_o⋎g_thm";

set_goal([], ⌜∀ f g⦁ ran g ⊆⋎g dom f ⇒ dom (f o⋎g g) = dom g⌝);
a (once_rewrite_tac [gst_relext_clauses]
	THEN rewrite_tac [ran_thm, dom_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜x⌝);
(* *** Goal "2.1" *** *)
a (spec_nth_asm_tac 1 ⌜e⌝);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜x'⌝ THEN ∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val dom_o⋎g_thm2 = save_pop_thm "dom_o⋎g_thm2";
=TEX
}%ignore

\subsubsection{Partial Function Space}

This is the set of all partial functions (i.e. many one mapings) over some domain and codomain.
=SML
declare_infix (240, "⇸⋎g");
ⓈHOLCONST
 $⇸⋎g : GS → GS → GS
├
∀s t⦁ s ⇸⋎g t = Sep (s ↔⋎g t) fun
■
=TEX

\subsubsection{Partial Function Space Non-Empty}

First the theorem that the empty set is a partial function over any domain and codomain.
=SML
set_goal([],
	⌜∀s t⦁ ∅⋎g ∈⋎g s ⇸⋎g t⌝);
a (prove_tac[
	get_spec ⌜$⇸⋎g⌝,
	fun_∅⋎g_thm]);
val ∅⋎g∈⋎g⇸⋎g_thm =
	save_pop_thm "∅⋎g∈⋎g⇸⋎g_thm";
=TEX
And then that every partial function space is non-empty.
=SML
set_goal([],
	⌜∀s t⦁ ∃ f⦁ f ∈⋎g s ⇸⋎g t⌝);
a (REPEAT strip_tac
	THEN ∃_tac ⌜∅⋎g⌝
	THEN
	rewrite_tac [∅⋎g∈⋎g⇸⋎g_thm]);
val ∃⇸⋎g_thm =
	save_pop_thm "∃⇸⋎g_thm";
=TEX

\subsubsection{Function Space}

This is the set of all total functions over some domain and codomain.

=SML
declare_infix (240, "→⋎g");
ⓈHOLCONST
│ $→⋎g : GS → GS → GS
├
│ ∀s t⦁ s →⋎g t = Sep (s ⇸⋎g t)
│	λr⦁ dom r = s
■

\subsubsection{Function Space Non-Empty}

First, for the special case of function spaces with empty domain we prove the theorem that the empty set is a member:

=SML
set_goal([],⌜∀s t⦁ ∅⋎g ∈⋎g ∅⋎g →⋎g t⌝);
a (prove_tac[get_spec ⌜$→⋎g⌝,
	fun_∅⋎g_thm,
	∅⋎g∈⋎g⇸⋎g_thm]);
val ∅⋎g∈⋎g∅⋎g→⋎g_thm =
	save_pop_thm "∅⋎g∈⋎g∅⋎g→⋎g_thm";
=TEX

Then that whenever the codomain is non-empty the function space is non-empty.

=GFT
∃→⋎g_thm =
   ⊢ ∀ s t⦁ (∃ x⦁ x ∈⋎g t) ⇒ (∃ f⦁ f ∈⋎g s →⋎g t)
=TEX

\ignore{
=SML
set_goal([],
	⌜∀s t⦁ (∃x⦁ x ∈⋎g t)
	⇒ ∃ f⦁ f ∈⋎g s →⋎g t⌝);
a (REPEAT strip_tac
	THEN ∃_tac ⌜s ×⋎g (Sing x)⌝);
a (rewrite_tac [get_spec ⌜$→⋎g⌝,
	get_spec ⌜$⇸⋎g⌝,
	get_spec ⌜$↔⋎g⌝]);
a (once_rewrite_tac
	[gst_relext_clauses]);
a (rewrite_tac[
	get_spec ⌜dom⌝,
	get_spec ⌜fun⌝,
	get_spec ⌜rel⌝,
	×⋎g_spec, dom_thm]
	THEN REPEAT strip_tac
	THEN TRY (asm_rewrite_tac[])
	THEN TRY prove_∃_tac);
a (∃_tac ⌜x⌝ THEN REPEAT strip_tac
	THEN ∃_tac ⌜l⌝
	THEN asm_rewrite_tac[]);
val ∃→⋎g_thm = save_pop_thm "∃→⋎g_thm";
=TEX
}%ignore

ⓈHOLCONST
│ →⋎g_closed : GS → BOOL
├────────────
│ ∀s⦁ →⋎g_closed s ⇔ ∀d c⦁ d ∈⋎g s ∧ c ∈⋎g s ⇒ d →⋎g c ∈⋎g s
■

\subsection{Functional Abstraction}

Functional abstraction is defined as a new variable binding construct yeilding a functional set.

\subsubsection{Abstraction}

Because of the closeness to lambda abstraction $λ⋎g$ is used as the name of a new binder for set theoretic functional abstraction.

=SML
declare_binder "λ⋎g";
=TEX

To define a functional set we need a HOL function over sets together with a set which is to be the domain of the function.
Specification of the range is not needed.
The binding therefore yields a function which maps sets to sets (maps the domain to the function).

The following definition is a placeholder, a more abstract definition might eventually be substituted.
The function is defined as that subset of the cartesian product of the set s and its image under the function f which coincides with the graph of f over s.

ⓈHOLCONST
│ $λ⋎g: (GS → GS) → GS → GS
├─────────
│ ∀f s⦁ $λ⋎g f s = Sep (s ×⋎g (Imagep f s)) (λp⦁ snd p = f (fst p))
■

\subsection{Application and Extensionality}

In this section we define function application and show that functions are extensional.

\subsubsection{Application}

Application by juxtaposition cannot be overloaded and is used for application of HOL functions.
Application of functional sets is therefore defined as an infix operator whose name is the empty name subscripted by "g".

=SML
declare_infix (250,"⋎g");
=TEX

The particular form shown here is innovative in the value specified for applications of functions to values outside their domain.
The merit of the particular value chosen is that it makes true an extensionality theorem which quantifies over all sets as arguments to the function, which might not otherwise be the case.
Whether this form is useful I don't know.
Generally a result with fewer conditionals is harder to prove but easier to use, but in this case I'm not so sure of the benefit.

It may be noted that it may also be used to apply a non-functional relation, if what you want it some arbitrary value (selected by the choice function) to which some object relates.

ⓈHOLCONST
│ $⋎g : GS → GS → GS
├───────
│ ∀f x⦁ f ⋎g x =
│	if ∃y⦁ x ↦⋎g y ∈⋎g f
│	then εy⦁ x ↦⋎g y ∈⋎g f
│	else f
■

=GFT
app_thm1 = 
	⊢ ∀f x⦁ (∃⋎1y⦁ x ↦⋎g y ∈⋎g f)
	  ⇒ x ↦⋎g (f ⋎g x) ∈⋎g f

app_thm2 = 
	⊢ ∀f x y⦁ fun f ∧ (x ↦⋎g y ∈⋎g f)
	  ⇒ f ⋎g x = y

app_thm3 = 
	⊢ ∀f x⦁ fun f ∧ x ∈⋎g dom f
	  ⇒ x ↦⋎g f ⋎g x ∈⋎g f

o⋎g_⋎g_thm = 
	⊢ ∀f g x⦁ fun f ∧ fun g ∧ x ∈⋎g dom g ∧ ran g ⊆⋎g dom f
	  ⇒ (f o⋎g g) ⋎g x = f ⋎g g ⋎g x
=TEX
\ignore{
=SML

set_goal([],⌜∀f x⦁ (∃⋎1y⦁ x ↦⋎g y ∈⋎g f)
	⇒ x ↦⋎g (f ⋎g x) ∈⋎g f⌝);
a (prove_tac[get_spec⌜$⋎g⌝]);
a (LEMMA_T ⌜∃ y⦁ x ↦⋎g y ∈⋎g f⌝
	(fn x=> rewrite_tac[x])
	THEN1 (
		∃_tac ⌜y⌝
		THEN prove_tac[]));
a (all_ε_tac);
a (∃_tac ⌜y⌝ THEN prove_tac[]);
val app_thm1 = save_pop_thm "app_thm1";
=TEX

Note that the result is not conditional on f being a function.

The next theorem applies to functions only and obtains the necessary uniqueness of image from that assumption.

=SML
set_goal([],⌜
∀f x y⦁ fun f ∧ (x ↦⋎g y ∈⋎g f)
	⇒ f ⋎g x = y
⌝);
a (prove_tac[get_spec⌜$⋎g⌝,
	get_spec ⌜fun⌝]);
a (LEMMA_T
	⌜∃ y⦁ x ↦⋎g y ∈⋎g f⌝
	(fn x=> rewrite_tac[x])
	THEN1 (
		∃_tac ⌜y⌝
		THEN prove_tac[]));
a (all_ε_tac);
a (∃_tac ⌜y⌝
	THEN prove_tac[]);
a (REPEAT (asm_fc_tac[]));
val app_thm2 = save_pop_thm "app_thm2";

set_goal([], ⌜∀f x⦁ fun f ∧ x ∈⋎g dom f ⇒ x ↦⋎g f ⋎g x ∈⋎g f⌝);
a (rewrite_tac [get_spec ⌜fun⌝, get_spec ⌜$⋎g⌝]
	THEN REPEAT strip_tac);
a (POP_ASM_T (strip_asm_tac o (rewrite_rule [dom_thm])));
a (LEMMA_T ⌜∃y⦁ x ↦⋎g y ∈⋎g f⌝ rewrite_thm_tac
	THEN1 (∃_tac ⌜x'⌝ THEN asm_rewrite_tac[dom_thm]));
a (ε_tac ⌜ε y⦁ x ↦⋎g y ∈⋎g f⌝);
a (∃_tac ⌜x'⌝ THEN strip_tac);
val app_thm3 = save_pop_thm "app_thm3";

set_goal([], ⌜∀f g x⦁ fun f ∧ fun g ∧ x ∈⋎g dom g ∧ ran g ⊆⋎g dom f
	⇒ (f o⋎g g) ⋎g x = f ⋎g g ⋎g x⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜fun (f o⋎g g)⌝ THEN1 all_fc_tac [o⋎g_fun_thm]);
a (LEMMA_T ⌜x ∈⋎g dom (f o⋎g g)⌝ asm_tac
	THEN1 all_fc_tac [once_rewrite_rule [gst_relext_clauses] dom_o⋎g_thm]);
(* *** Goal "1" *** *)
a (all_fc_tac [dom_o⋎g_thm2]
	THEN pure_asm_rewrite_tac[]
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (PC_T "hol" (strip_asm_tac (list_∀_elim [⌜f o⋎g g⌝, ⌜x⌝] app_thm3)));
a (GET_NTH_ASM_T 1 strip_asm_tac);
a (LEMMA_T ⌜g ⋎g x = z⌝ rewrite_thm_tac THEN1 all_fc_tac [app_thm2]); 
a (LEMMA_T ⌜f ⋎g z = (f o⋎g g) ⋎g x⌝ rewrite_thm_tac THEN1 all_fc_tac [app_thm2]); 
val o⋎g_⋎g_thm = save_pop_thm "o⋎g_⋎g_thm"; 
=TEX
}%ignore

\subsubsection{The "Type" of an Application (1)}

The following theorem states that the result of applying a partial function to a value in its domain is a value in its codomain.

=SML
set_goal([],
	⌜∀f s t u⦁ f ∈⋎g s ⇸⋎g t ∧
	u ∈⋎g dom f ⇒
	f ⋎g u ∈⋎g t⌝); 
a (prove_tac[
	get_spec ⌜$⇸⋎g⌝,
	get_spec ⌜dom⌝]);
a (all_fc_tac [app_thm2] THEN asm_rewrite_tac[]);
a (all_fc_tac [f↦⋎gs_thm1]);
a (all_fc_tac [∈⋎g↔⋎g_thm]); 
a (POP_ASM_T ante_tac THEN asm_rewrite_tac []);
val ⋎g∈⋎g_thm = save_pop_thm "⋎g∈⋎g_thm";
=TEX

\subsubsection{The "Type" of an Application (2)}

The following theorem states that the result of applying a total function to a value in its domain is a value in its codomain.

=GFT
=TEX

\ignore{
=SML
set_goal([],
	⌜∀f s t u⦁ f ∈⋎g s →⋎g t ∧
	u ∈⋎g s ⇒
	f ⋎g u ∈⋎g t⌝); 
a (prove_tac[
	get_spec ⌜$→⋎g⌝]);
a (bc_thm_tac ⋎g∈⋎g_thm);
a (∃_tac ⌜s⌝
	THEN pure_asm_rewrite_tac[]
	THEN contr_tac); 
val ⋎g∈⋎g_thm1 = save_pop_thm "⋎g∈⋎g_thm1";
=TEX
}%ignore

\subsubsection{Partial functions are total}

Every partial function is total over its domain.
(there is an ambiguity in the use of the term "domain" for a partial function.
It might mean the left hand operand of some partial function space construction within which the partial function concerned may be found, or it might mean the set of values over which the function is defined.
Here we are saying that if f is a partial function over A, then its domain is some subset of A and f is a total function over that subset of A.)

=GFT
∈⋎g⇸⋎g⇒∈⋎g→⋎g_thm =
	⊢ ∀f s t u⦁ f ∈⋎g s ⇸⋎g t ⇒ f ∈⋎g dom f →⋎g t
=TEX

\ignore{
=SML
set_goal([],⌜∀f s t u⦁ f ∈⋎g s ⇸⋎g t ⇒ f ∈⋎g dom f →⋎g t⌝); 
a (rewrite_tac[
	get_spec ⌜$→⋎g⌝,
	get_spec ⌜$↔⋎g⌝,
	get_spec ⌜dom⌝,
	get_spec ⌜$⇸⋎g⌝]);
a (once_rewrite_tac[gst_relext_clauses]); 
a (REPEAT strip_tac); 
a (rewrite_tac[×⋎g_spec]); 
a (asm_fc_tac[]); 
a (all_fc_tac[
	f↦⋎gs_thm,
	v∈⋎g×⋎g_thm]); 
a (∃_tac ⌜fst e⌝
	THEN ∃_tac ⌜snd e⌝
	THEN asm_rewrite_tac[]
	THEN strip_tac); 
(* *** Goal "1" *** *)
a (LEMMA_T ⌜Pair⋎g (fst e) (snd e) ∈⋎g Gx (fst e ↦⋎g snd e)⌝ ante_tac
	THEN1 rewrite_tac [↦⋎g_spec_thm]);
a (pure_rewrite_tac[asm_rule ⌜fst e ↦⋎g snd e = e⌝]
	THEN strip_tac);
a (LEMMA_T ⌜Gx e ⊆⋎g Gx f⌝ ante_tac THEN1 fc_tac [Gx_mono_thm2]);
a (rewrite_tac [gst_relext_clauses] THEN strip_tac THEN asm_fc_tac[]);
a (LEMMA_T ⌜fst e ∈⋎g Pair⋎g (fst e) (snd e)⌝ asm_tac THEN1 rewrite_tac[]);
a (all_fc_tac [Gx_trans_thm3]);
(* *** Goal "2" *** *)
a (∃_tac ⌜snd e⌝	THEN asm_rewrite_tac[]); 
val ∈⋎g⇸⋎g⇒∈⋎g→⋎g_thm = save_pop_thm "∈⋎g⇸⋎g⇒∈⋎g→⋎g_thm";
=TEX
}%ignore

\subsection{The Identity Function}

\subsubsection{specification}

ⓈHOLCONST
│ id : GS → GS
├────────
│ ∀s⦁ id s = Sep
│	(s ×⋎g s)
│	λx⦁ fst x = snd x
■

\subsubsection{lemmas}

=GFT
id_thm1 =
	⊢ ∀s x⦁ x ∈⋎g id s	
	  ⇔ ∃y⦁ y ∈⋎g s ∧ x = y ↦⋎g y

id_ap_thm =
	⊢ ∀s x⦁ x ∈⋎g s	
	  ⇒ (id s) ⋎g x = x

id∈⋎g⇸⋎g_thm1 =
	⊢ ∀s t u⦁ s ⊆⋎g t ∩⋎g u
	  ⇒ id s ∈⋎g t ⇸⋎g u

id∈⋎g⇸⋎g_thm2 =
	⊢ ∀s t u⦁ s ⊆⋎g t
	  ⇒ id s ∈⋎g t ⇸⋎g t

id_clauses =
	⊢ ∀s⦁ rel(id s) ∧ fun (id s)
	  ∧ dom(id s) = s ∧ ran(id s) = s
=TEX

\ignore{
=SML
val idg_def = get_spec ⌜id⌝;

set_goal([],⌜∀s x⦁
	x ∈⋎g id s	
	⇔ ∃y⦁ y ∈⋎g s
	∧ x = y ↦⋎g y⌝);
a (prove_tac[get_spec ⌜id⌝]
	THEN_TRY (asm_rewrite_tac[
	get_spec⌜$↔⋎g⌝,
	×⋎g_spec]));
(* *** Goal "1" *** *)
a (fc_tac[×⋎g_spec]);
a (asm_ante_tac ⌜fst x = snd x⌝
	THEN asm_rewrite_tac[]
	THEN strip_tac
	THEN all_var_elim_asm_tac);
a (∃_tac ⌜r⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (REPEAT (∃_tac ⌜y⌝) THEN asm_rewrite_tac[]);
val id_thm1 =
	save_pop_thm "id_thm1";

set_goal([],⌜∀s x⦁
	x ∈⋎g s	
	⇒ (id s) ⋎g x = x⌝);
a (once_rewrite_tac[gst_relext_clauses]);
a (rewrite_tac[get_spec ⌜$⋎g⌝, id_thm1]);
a (REPEAT_N 4 strip_tac);
a (LEMMA_T ⌜∃ y y'⦁ y' ∈⋎g s ∧ x = y' ∧ y = y'⌝
	(fn x=> rewrite_tac[x] THEN asm_tac x)
	THEN1 (REPEAT_N 2 (∃_tac ⌜x⌝)
		THEN asm_rewrite_tac[]));
a (all_ε_tac
	THEN asm_rewrite_tac[]);
val id_ap_thm = save_pop_thm "id_ap_thm"; 

set_goal([],⌜∀s t u⦁ s ⊆⋎g t ∩⋎g u ⇒ id s ∈⋎g t ⇸⋎g u⌝);
a (rewrite_tac[gst_relext_clauses]);
a (prove_tac[get_spec ⌜$⇸⋎g⌝,
	get_spec ⌜id⌝,
	get_spec ⌜$↔⋎g⌝,
	×⋎g_spec]);
(* *** Goal "1" *** *)
a (once_rewrite_tac[gst_relext_clauses]);
a (prove_tac[×⋎g_spec]);
a (MAP_EVERY ∃_tac [⌜l⌝, ⌜r⌝] THEN REPEAT strip_tac
	THEN (REPEAT (asm_fc_tac[])));
(* *** Goal "2" *** *)
a (prove_tac[get_spec ⌜fun⌝,
	get_spec ⌜rel⌝,
	×⋎g_spec]);
val id∈⋎g⇸⋎g_thm1 = save_pop_thm "id∈⋎g⇸⋎g_thm1";

set_goal([],⌜∀s t u⦁ s ⊆⋎g t ⇒ id s ∈⋎g t ⇸⋎g t⌝);
a (prove_tac[]);
a (bc_thm_tac id∈⋎g⇸⋎g_thm1);
a (asm_rewrite_tac [
	prove_rule [gst_relext_clauses]
	⌜t ∩⋎g t = t⌝]);
val id∈⋎g⇸⋎g_thm2 = save_pop_thm "id∈⋎g⇸⋎g_thm2";

set_goal ([], ⌜∀s⦁ rel (id s)⌝);
a (rewrite_tac [get_spec ⌜rel⌝, get_spec ⌜id⌝]
	THEN REPEAT strip_tac);
a (fc_tac [×⋎g_spec]);
a (∃_tac ⌜l⌝ THEN ∃_tac ⌜r⌝
	THEN asm_rewrite_tac[]);
val rel_id_lem = pop_thm();

set_goal([], ⌜∀s⦁ rel(id s) ∧ fun (id s) ∧ dom(id s) = s ∧ ran(id s) = s⌝);
a (rewrite_tac [rel_id_lem] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [fun_def, rel_id_lem, get_spec ⌜id⌝]
	THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac
	THEN strip_tac);
(* *** Goal "2" *** *)
a (rewrite_tac[get_spec ⌜dom⌝]);
a (once_rewrite_tac [gst_relext_clauses]);
a (rewrite_tac[get_spec ⌜id⌝] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (LEMMA_T ⌜e ↦⋎g e ∈⋎g (Sep (s ×⋎g s) (λ x⦁ fst x = snd x))⌝ asm_tac
	THEN1 (rewrite_tac[] THEN strip_tac));
a (fc_tac [Gx_trans_thm2]);
a (LEMMA_T ⌜Pair⋎g e e ∈⋎g Gx (e ↦⋎g e)⌝ asm_tac THEN1 rewrite_tac []);
a (lemma_tac ⌜galaxy (Gx (Sep (s ×⋎g s) (λ x⦁ fst x = snd x)))⌝ THEN1 rewrite_tac [galaxy_Gx]);
a (all_fc_tac [get_spec ⌜Gx⌝]);
a (LEMMA_T ⌜e ∈⋎g Pair⋎g e e⌝ asm_tac THEN1 prove_tac[]);
a (all_fc_tac [Gx_trans_thm3]);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (rewrite_tac[get_spec ⌜ran⌝]);
a (once_rewrite_tac [gst_relext_clauses]);
a (rewrite_tac[get_spec ⌜id⌝] THEN REPEAT strip_tac);
(* *** Goal "3.1" *** *)
a (LEMMA_T ⌜e ↦⋎g e ∈⋎g (Sep (s ×⋎g s) (λ x⦁ fst x = snd x))⌝ asm_tac
	THEN1 (rewrite_tac[] THEN strip_tac));
a (fc_tac [Gx_trans_thm2]);
a (LEMMA_T ⌜Pair⋎g e e ∈⋎g Gx (e ↦⋎g e)⌝ asm_tac THEN1 rewrite_tac []);
a (lemma_tac ⌜galaxy (Gx (Sep (s ×⋎g s) (λ x⦁ fst x = snd x)))⌝ THEN1 rewrite_tac [galaxy_Gx]);
a (all_fc_tac [get_spec ⌜Gx⌝]);
a (LEMMA_T ⌜e ∈⋎g Pair⋎g e e⌝ asm_tac THEN1 prove_tac[]);
a (all_fc_tac [Gx_trans_thm3]);
(* *** Goal "3.2" *** *)
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
val id_clauses = save_pop_thm "id_clauses";

add_pc_thms "'gst-fun" ([id_clauses]);
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-fun"];
=TEX
}%ignore

\subsection{Override}

Override is an operator over sets which is intended primarily for use with functions.
It may be used to change the value of the function over any part of its domain by overriding it with a function which is defined only for those values.

=SML
declare_infix (250,"⊕⋎g");
=TEX

ⓈHOLCONST
│ $⦏⊕⋎g⦎ : GS → GS → GS
├─────────────
│ ∀s t⦁ s ⊕⋎g t = Sep (s ∪⋎g t)
│	λx⦁ if fst x ∈⋎g dom t then x ∈⋎g t else x ∈⋎g s 
■

=GFT
⦏∈⋎g⊕⋎g_thm⦎ =
   ⊢ ∀ s t x⦁ x ∈⋎g s ⊕⋎g t = (if fst x ∈⋎g dom t then x ∈⋎g t else x ∈⋎g s)

⦏↦⋎g∈⋎g⊕⋎g_thm⦎ =
   ⊢ ∀ s t x y
     ⦁ x ↦⋎g y ∈⋎g s ⊕⋎g t = (x ↦⋎g y ∈⋎g t ∨ ¬ x ∈⋎g dom t ∧ x ↦⋎g y ∈⋎g s)

⦏⊕⋎g_rel_thm⦎ =
   ⊢ ∀ s t⦁ rel s ∧ rel t ⇒ rel (s ⊕⋎g t)

⦏⊕⋎g_fun_thm⦎ =
   ⊢ ∀ s t⦁ fun s ∧ fun t ⇒ fun (s ⊕⋎g t)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀s t x⦁ x ∈⋎g (s ⊕⋎g t) ⇔
	   if fst x ∈⋎g dom t then x ∈⋎g t else x ∈⋎g s⌝);
a (rewrite_tac [get_spec ⌜$⊕⋎g⌝]
	THEN REPEAT strip_tac);
val ∈⋎g⊕⋎g_thm = save_pop_thm "∈⋎g⊕⋎g_thm";

set_goal ([], ⌜∀s t x y⦁ x ↦⋎g y ∈⋎g (s ⊕⋎g t) ⇔
	   x ↦⋎g y ∈⋎g t
	∨ ¬ (x ∈⋎g dom t)
	   ∧ x ↦⋎g y ∈⋎g s
⌝);
a (rewrite_tac [get_spec ⌜$⊕⋎g⌝] THEN REPEAT strip_tac);
a (POP_ASM_T ante_tac THEN rewrite_tac [dom_thm]
	THEN REPEAT strip_tac);
a (asm_fc_tac[]);
val ↦⋎g∈⋎g⊕⋎g_thm = save_pop_thm "↦⋎g∈⋎g⊕⋎g_thm";

set_goal([], ⌜∀s t⦁ rel s ∧ rel t ⇒ rel (s ⊕⋎g t)⌝);
a (rewrite_tac [get_spec ⌜rel⌝, ∈⋎g⊕⋎g_thm]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]
	THEN ∃_tac ⌜s'⌝ THEN ∃_tac ⌜t'⌝ THEN strip_tac);
val ⊕⋎g_rel_thm = save_pop_thm "⊕⋎g_rel_thm";

set_goal([], ⌜∀s t⦁ fun s ∧ fun t ⇒ fun (s ⊕⋎g t)⌝);
a (rewrite_tac [get_spec ⌜fun⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac[⊕⋎g_rel_thm]);
(* *** Goal "2" *** *)
a (REPEAT_N 2 (POP_ASM_T ante_tac)
	THEN rewrite_tac [↦⋎g∈⋎g⊕⋎g_thm, dom_thm]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
val ⊕⋎g_fun_thm = save_pop_thm "⊕⋎g_fun_thm";
=TEX
}%ignore

\subsection{Proof Contexts}

Finalisation of a proof context.

\subsubsection{Proof Context}

=SML
add_pc_thms "'gst-fun" ([
	field_∅⋎g_thm,
	fun_∅⋎g_thm,
	∅⋎g∈⋎g⇸⋎g_thm]);
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-fun"];
commit_pc "'gst-fun";
=TEX

\section{Ordinals}

A new "gst-ord" theory is created as a child of "gst-ax".
The theory will contain the definitions of ordinals and related material for general use, roughly following "Set Theory" by Frank Drake, chapter 2 section 2.
The subsections in this document correspondend to the subsections in the book.

\subsubsection{Motivation}

This is really motivated purely by interest and self-education.
Since its so fundamental I think it likely to turn out handy.
Some of the material required is not specific to set theory and is quite widely applicable (in which case I actually develop it elsewhere and then just use it here.
Well-foundedness and induction over well-founded relations is the obvious case relevant to this part of Drake.
The recursion theorem is the important more general result which appears in the next section in Drake.
"more general" means "can be developed as a polymorphic theory in HOL and applied outside the context of set theory".
In fact these things have to be developed in the more general context to be used in the ways they are required in the development of set theory, since, for example, one wants to do definitions by recursion over the set membership relation where neither the function defined nor the relevant well-founded relation are actually sets.

\subsubsection{Divergence}

I have not followed Drake slavishly.
More or less, I follow him where it works out OK and looks reasonable and doesn't trigger any of my prejudices.

Sometimes the context in which I am doing the work makes some divergence desirable or necessary.
For example, I am doing the work in the context of a slightly eccentric set theory ("Galactic Set Theory") which mainly makes no difference, but has a non-standard formulation of the axiom of foundation.
Mainly this is covered by deriving the standard formulation and its consequences and using them where this is used by Drake (in proving the trichotomy theorem).
However, the machinery for dealing with well-foundedness makes a difference to how induction principles are best formulated and derived.

Sometimes I look at what he has done and I think, "no way am I going to do that".
Not necessarily big things, for example, I couldn't use his definition of successor ordinal which he pretty much admits himself is what we nerds call a kludge.

\subsubsection{The Theory ord}

The new theory is first created, together with a proof context which we will build up as we develop the theory.

=SML
open_theory "gst-ax";
force_new_theory "gst-ord";
(* new_parent "wf_recp"; *)
force_new_pc "'gst-ord";
merge_pcs ["'savedthm_cs_∃_proof"] "'gst-ord";
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-ord"];
=TEX

\subsection{Definitions 2.1 and 2.3}

An ordinal is defined as a transitive and connected set.
The usual ordering over the ordinals is defined and also the successor function.

\subsubsection{The Definition}

The concept of transitive set has already been defined in theory {\it gst-ax}.
The concepts {\it connected} and {\it ordinal} are now defined.

ⓈHOLCONST
 ⦏connected⦎ : GS → BOOL
├
  ∀s :GS⦁ connected s ⇔
	∀t u :GS⦁ t ∈⋎g s ∧ u ∈⋎g s ⇒ t ∈⋎g u ∨ t = u ∨ u ∈⋎g t
■

ⓈHOLCONST
 ⦏ordinal⦎ : GS → BOOL
├
  ∀s :GS⦁ ordinal s ⇔ transitive s ∧ connected s
■

We now introduce infix ordering relations over ordinals.

=SML
declare_infix(240,"<⋎o");
declare_infix(240,"≤⋎o");

ⓈHOLCONST
 $⦏<⋎o⦎ : GS → GS → BOOL
├
  ∀x y:GS⦁ x <⋎o y ⇔ ordinal x ∧ ordinal y ∧ x ∈⋎g y
■

=GFT
⦏less_mem_thm⦎ =
	⊢ ∀ α β⦁ α <⋎o β ⇒ ordinal α ∧ ordinal β ∧ α ∈⋎g β

⦏mem_less_thm⦎ =
	⊢ ∀ α β⦁ ordinal α ∧ ordinal β ∧ α ∈⋎g β ⇒ α <⋎o β

⦏ord_mem_psub_thm⦎ =
	⊢ ∀ α⦁ ordinal α ⇒ (∀ β⦁ β ∈⋎g α ⇒ β ⊂⋎g α)

⦏lto_psub_thm⦎ =
	⊢ ∀ α β⦁ α <⋎o β ⇒ α ⊂⋎g β

⦏lo_trans_thm⦎ =
	⊢ ∀ α β γ⦁ α <⋎o β ∧ β <⋎o γ ⇒ α <⋎o γ
=TEX

\ignore{
=SML
set_goal([], ⌜∀α β⦁ ordinal α ∧ ordinal β ∧ α ∈⋎g β ⇒ α <⋎o β⌝);
a (REPEAT strip_tac THEN asm_rewrite_tac [get_spec ⌜$<⋎o⌝]);
val mem_less_thm = save_pop_thm "mem_less_thm";

set_goal([], ⌜∀α β⦁ α <⋎o β ⇒ ordinal α ∧ ordinal β ∧ α ∈⋎g β⌝);
a (rewrite_tac [get_spec ⌜$<⋎o⌝]
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac []);
val less_mem_thm = save_pop_thm "less_mem_thm";

set_goal([], ⌜∀α⦁ ordinal α ⇒ ∀β⦁ β ∈⋎g α ⇒ β ⊂⋎g α⌝);
a (REPEAT strip_tac
	THEN fc_tac [get_spec ⌜ordinal⌝]
	THEN fc_tac [get_spec ⌜transitive⌝]);
a (rewrite_tac [get_spec ⌜$⊂⋎g⌝]);
a (asm_fc_tac []
	THEN asm_rewrite_tac [get_spec ⌜$⊆⋎g⌝]
	THEN REPEAT strip_tac);
a (∃_tac ⌜β⌝ THEN asm_rewrite_tac[wf_l1]);
val ord_mem_psub_thm = save_pop_thm "ord_mem_psub_thm";

set_goal([], ⌜∀α β⦁ α <⋎o β ⇒ α ⊂⋎g β⌝);
a (REPEAT strip_tac THEN fc_tac [less_mem_thm]);
a (fc_tac [∀_elim ⌜β⌝ ord_mem_psub_thm]);
a (asm_fc_tac[]);
val lto_psub_thm = save_pop_thm "lto_psub_thm";

set_goal([], ⌜∀α β γ⦁ α <⋎o β ∧ β <⋎o  γ ⇒ α <⋎o γ⌝);
a (rewrite_tac [get_spec ⌜$<⋎o⌝] THEN REPEAT strip_tac);
a (lemma_tac ⌜transitive γ⌝ THEN1 fc_tac [get_spec ⌜ordinal⌝]);
a (all_fc_tac [get_spec ⌜transitive⌝]);
a (all_fc_tac [get_spec ⌜$⊆⋎g⌝]);
val lo_trans_thm = save_pop_thm "lo_trans_thm";

=TEX
}%ignore


ⓈHOLCONST
 $⦏≤⋎o⦎ : GS → GS → BOOL
├
  ∀x y:GS⦁ x ≤⋎o y ⇔ ordinal x ∧ ordinal y ∧ (x ∈⋎g y ∨ x = y)
■

=GFT
⦏leo_lo_thm⦎ =
	⊢ ∀ x y⦁ x ≤⋎o y ⇔ ordinal x ∧ ordinal y ∧ (x <⋎o y ∨ x = y)

⦏leo_sub_thm⦎ =
	⊢ ∀ α β⦁ α ≤⋎o β ⇒ α ⊆⋎g β

⦏leo_trans_thm⦎ =
	⊢ ∀ α β γ⦁ α ≤⋎o β ∧ β ≤⋎o γ ⇒ α ≤⋎o γ

⦏leo_lo_trans_thm⦎ =
	⊢ ∀ α β γ⦁ α ≤⋎o β ∧ β <⋎o γ ⇒ α <⋎o γ

⦏lo_leo_trans_thm⦎ =
	⊢ ∀ α β γ⦁ α <⋎o β ∧ β ≤⋎o γ ⇒ α <⋎o γ
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y:GS⦁ x ≤⋎o y ⇔ ordinal x ∧ ordinal y ∧ (x <⋎o y ∨ x = y)⌝);
a (rewrite_tac [get_spec ⌜$≤⋎o⌝, get_spec ⌜$<⋎o⌝]);
a (REPEAT strip_tac);
val leo_lo_thm = save_pop_thm "leo_lo_thm";

set_goal([], ⌜∀α β⦁ α ≤⋎o β ⇒ α ⊆⋎g β⌝);
a (REPEAT strip_tac);
a (fc_tac [leo_lo_thm]);
(* *** Goal "1" *** *)
a (fc_tac[lto_psub_thm]);
a (fc_tac[get_spec ⌜$⊂⋎g⌝]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac []);
val leo_sub_thm = save_pop_thm "leo_sub_thm";

set_goal([], ⌜∀α β γ⦁ α ≤⋎o β ∧ β ≤⋎o γ ⇒ α ≤⋎o γ⌝);
a (rewrite_tac [get_spec ⌜$≤⋎o⌝]
	THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY rewrite_tac[]);
a (lemma_tac ⌜transitive γ⌝ THEN1 fc_tac [get_spec ⌜ordinal⌝]);
a (all_fc_tac [get_spec ⌜transitive⌝]);
a (all_fc_tac [get_spec ⌜$⊆⋎g⌝]);
val leo_trans_thm = save_pop_thm "leo_trans_thm";

set_goal([], ⌜∀α β γ⦁ α ≤⋎o β ∧ β <⋎o γ ⇒ α <⋎o γ⌝);
a (rewrite_tac [get_spec ⌜$≤⋎o⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [mem_less_thm]);
a (all_fc_tac [lo_trans_thm]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
val leo_lo_trans_thm = save_pop_thm "leo_lo_trans_thm";

set_goal([], ⌜∀α β γ⦁ α <⋎o β ∧ β ≤⋎o γ ⇒ α <⋎o γ⌝);
a (rewrite_tac [get_spec ⌜$≤⋎o⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (strip_asm_tac (list_∀_elim [⌜β⌝, ⌜γ⌝] mem_less_thm));
a (all_fc_tac [lo_trans_thm]);
(* *** Goal "2" *** *)
a (all_var_elim_asm_tac);
val lo_leo_trans_thm = save_pop_thm "lo_leo_trans_thm";
=TEX
}%ignore

The following definition gives the successor function over the ordinals (this appears later in Drake).

ⓈHOLCONST
 ⦏suc⋎o⦎ : GS → GS
├
  ∀x:GS⦁ suc⋎o x = x ∪⋎g (Sing x)
■

\ignore{
=IGN
add_pc_thms "'gst-ord" [get_spec ⌜connected⌝, get_spec ⌜ordinal⌝];
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-ord"];
=TEX
}%ignore

\subsection{Theorem 2.2}

We prove that the empty set is an ordinal, and that the members of an ordinal and the successor of an ordinal are ordinals.

\subsubsection{The Empty Set is an Ordinal}

First we prove that the empty set is an ordinal, which requires only rewriting with the relevant definitions.

\ignore{
=SML
set_goal([],⌜	ordinal ∅⋎g	⌝);
a (rewrite_tac[get_spec ⌜ordinal⌝, get_spec ⌜transitive⌝, get_spec ⌜connected⌝]);
val ordinal_∅⋎g = save_pop_thm "ordinal_∅⋎g";
=TEX
}

\subsubsection{The Successor of an Ordinal is an Ordinal}

Next we prove that the successor of an ordinal is an ordinal.
This is done in two parts, transitivity and connectedness.

=SML
set_goal([], ⌜	∀ x:GS⦁ transitive x ⇒ transitive (suc⋎o x)	⌝);
=TEX

\ignore{
=SML
a (rewrite_tac[get_spec ⌜transitive⌝, get_spec ⌜suc⋎o⌝]
	THEN REPEAT strip_tac
	THEN once_rewrite_tac [gst_relext_clauses]
	THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 4 ⌜e⌝);
a (POP_ASM_T ante_tac);
a (once_rewrite_tac [get_spec⌜$⊆⋎g⌝]
	THEN strip_tac);
a (all_asm_fc_tac[]);
val trans_suc_trans = save_pop_thm "trans_suc_trans";
=TEX
}%ignore

=SML
set_goal([],⌜∀ x:GS⦁
	connected x ⇒ connected (suc⋎o x)
⌝);
=TEX

\ignore{
=SML
a (rewrite_tac[get_spec ⌜connected⌝, get_spec ⌜suc⋎o⌝]);
a (REPEAT strip_tac
	THEN all_asm_fc_tac[]
	THEN all_var_elim_asm_tac);
val conn_suc_conn = save_pop_thm "conn_suc_conn";
=TEX
}%ignore

These together enable us to prove:

=SML
set_goal([], ⌜∀ x:GS⦁ ordinal x ⇒ ordinal (suc⋎o x)⌝);
=TEX

The proof expands using the definition of ordinal, strips the goal and reasons forward from the resulting assumptions using the two lemmas proved above.

=SML
a (rewrite_tac[get_spec ⌜ordinal⌝]
	THEN REPEAT strip_tac
	THEN fc_tac [trans_suc_trans, conn_suc_conn]);
val ord_suc_ord_thm = save_pop_thm "ord_suc_ord_thm";
=TEX

\subsubsection{The Ordinal Zero is not a successor}

=GFT
⦏∅⋎g_not_suc⋎o_thm⦎ =
	⊢ ¬ (∃ α⦁ suc⋎o α = ∅⋎g)

⦏not_in_suco_thm⦎ =
	⊢ ∀ α⦁ ¬ α = suc⋎o α

⦏leo_suc_thm⦎ =
	⊢ ∀ α⦁ ordinal α ⇒ α ≤⋎o suc⋎o α

⦏lo_suc_thm⦎ =
	⊢ ∀ α⦁ ordinal α ⇒ α <⋎o suc⋎o α
=TEX

\ignore{
=SML
set_goal([], ⌜¬ ∃α⦁ suc⋎o α = ∅⋎g⌝);
a ( strip_tac THEN strip_tac);
a (rewrite_tac [get_spec ⌜suc⋎o⌝]);
a (once_rewrite_tac [gs_ext_axiom]);
a (rewrite_tac [get_spec ⌜$∪⋎g⌝]);
a (contr_tac);
a (spec_nth_asm_tac 1 ⌜α⌝);
val ∅⋎g_not_suc⋎o_thm = save_pop_thm "∅⋎g_not_suc⋎o_thm";

set_goal ([], ⌜∀α⦁ ¬ α = suc⋎o α⌝);
a (strip_tac
	THEN rewrite_tac [get_spec ⌜suc⋎o⌝]);
a (once_rewrite_tac [gs_ext_axiom]
	THEN REPEAT strip_tac);
a (∃_tac ⌜α⌝ THEN rewrite_tac [wf_l1]);
val not_in_suco_thm = save_pop_thm "not_in_suco_thm";

set_goal ([], ⌜∀α⦁ ordinal α ⇒ α ≤⋎o suc⋎o α⌝);
a (rewrite_tac [get_spec ⌜$≤⋎o⌝]
	THEN REPEAT strip_tac);
a (fc_tac [ord_suc_ord_thm]);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜suc⋎o⌝]);
val leo_suc_thm = save_pop_thm "leo_suc_thm";

set_goal ([], ⌜∀α⦁ ordinal α ⇒ α <⋎o suc⋎o α⌝);
a (rewrite_tac [get_spec ⌜$<⋎o⌝]
	THEN REPEAT strip_tac);
a (fc_tac [ord_suc_ord_thm]);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜suc⋎o⌝]);
val lo_suc_thm = save_pop_thm "lo_suc_thm";
=TEX
}%ignore

\subsubsection{The members of an Ordinal are Ordinals}

We now aim to prove that the members of an ordinal are ordinals.
We do this by proving first that they are connected and then that they are transitive.
First however, we show that any subset of a connected set is connected.
=SML
set_goal([],⌜
	∀ x:GS⦁ connected x ⇒ ∀ y:GS⦁ y ⊆⋎g x ⇒ connected y
⌝);
=TEX
The proof consists of expanding appropriate definitions, stripping the goal and then reasoning forward from the assumptions.
=SML
a (rewrite_tac (map get_spec [⌜connected⌝, ⌜$⊆⋎g⌝])
	THEN REPEAT_N 7 strip_tac);
=GFT
(* *** Goal "" *** *)

(*  4 *)  ⌜∀ t u⦁ t ∈⋎g x ∧ u ∈⋎g x ⇒ t ∈⋎g u ∨ t = u ∨ u ∈⋎g t⌝
(*  3 *)  ⌜∀ e⦁ e ∈⋎g y ⇒ e ∈⋎g x⌝
(*  2 *)  ⌜t ∈⋎g y⌝
(*  1 *)  ⌜u ∈⋎g y⌝

(* ?⊢ *)  ⌜t ∈⋎g u ∨ t = u ∨ u ∈⋎g t⌝
=SML
a (all_asm_fc_tac[]);
a (REPEAT_N 2 (asm_fc_tac[]) THEN REPEAT strip_tac);
val conn_sub_conn = save_pop_thm "conn_sub_conn";
=TEX
Now we show that any member of an ordinal is an ordinal.
=SML
set_goal([],⌜
	∀ x:GS⦁ ordinal x ⇒ ∀ y:GS⦁ y ∈⋎g x ⇒ connected y
⌝);
=TEX
Expanding the definition of ordinal and making use of transitivity enables us to infer that members of an ordinals are subsets and permits application of the previous result to obtain connectedness.
=SML
a (rewrite_tac (map get_spec [⌜ordinal⌝, ⌜transitive⌝])
	THEN REPEAT strip_tac);
a (all_asm_fc_tac []);
a (all_asm_fc_tac [conn_sub_conn]);
val conn_mem_ord = save_pop_thm "conn_mem_ord";
=TEX
To prove that the members of an ordinal are transitive, well-foundedness is needed.
Now we are ready to prove that the members of an ordinal are transitive.
=SML
set_goal([], ⌜∀ x:GS⦁ ordinal x ⇒ ∀ y:GS⦁ y ∈⋎g x ⇒ transitive y⌝);
=TEX
\ignore{
=SML
a (rewrite_tac (map get_spec [⌜ordinal⌝, ⌜transitive⌝]));
a (REPEAT strip_tac);
a (rewrite_tac[get_spec ⌜$⊆⋎g⌝]
	THEN REPEAT strip_tac);
a (REPEAT_N 4 (all_asm_fc_tac[∈⋎g⊆⋎g_thm]));
a (fc_tac[get_spec⌜connected⌝]);
a (lemma_tac ⌜y ∈⋎g e' ∨ y = e' ∨ e' ∈⋎g y⌝);
(* *** Goal "1" *** *)
a (list_spec_nth_asm_tac 1 [⌜e'⌝, ⌜y⌝]
	THEN REPEAT strip_tac);
a( POP_ASM_T ante_tac THEN once_asm_rewrite_tac[]);
a (rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_tac wf_l3);
a (list_spec_nth_asm_tac 1 [⌜e⌝, ⌜y⌝, ⌜e'⌝]);
(* *** Goal "3" *** *)
a (all_var_elim_asm_tac);
a (asm_tac wf_l2);
a (list_spec_nth_asm_tac 1 [⌜e⌝, ⌜e'⌝]);
val tran_mem_ord = save_pop_thm "tran_mem_ord";
=TEX
}%ignore

Finally we prove that all members of an ordinal are ordinals.
=SML
set_goal([], ⌜∀ x:GS⦁ ordinal x ⇒ ∀ y:GS⦁ y ∈⋎g x ⇒ ordinal y⌝);
=TEX

\ignore{
=SML
a (REPEAT strip_tac);
a (rewrite_tac [get_spec ⌜ordinal⌝]);
a (all_fc_tac [tran_mem_ord, conn_mem_ord]);
a contr_tac;
val ord_mem_ord = save_pop_thm "ord_mem_ord";
=TEX
}%ignore

\subsubsection{Galaxies are Closed under suc}

=GFT
GCloseSuc = ⊢ ∀g⦁ galaxy g ⇒ ∀x⦁ x ∈⋎g g ⇒ suc⋎o x ∈⋎g g
=TEX

\ignore{
=SML
set_goal ([], ⌜∀g⦁ galaxy g ⇒ ∀x⦁ x ∈⋎g g ⇒ suc⋎o x ∈⋎g g⌝);
a (rewrite_tac [get_spec ⌜suc⋎o⌝]);
a (REPEAT strip_tac);
a (REPEAT (all_fc_tac [GClose∪⋎g, GCloseSing]));
val GCloseSuc = save_pop_thm "GCloseSuc";
=TEX
}%ignore

\subsection{Theorem 2.4}

We prove that the ordinals are linearly ordered by $<⋎o$.

\subsubsection{}

First we prove some lemmas:
=SML
set_goal([], ⌜∀ x y:GS⦁ transitive x ∧ transitive y ⇒ transitive (x ∩⋎g y)⌝);
=TEX
\ignore{
=SML
a (rewrite_tac[get_spec ⌜transitive⌝]);
a (REPEAT strip_tac);
a (ALL_ASM_FC_T (MAP_EVERY ante_tac) []);
a (rewrite_tac [get_spec ⌜$⊆⋎g⌝]
	THEN prove_tac[]);
val tran_∩_thm = save_pop_thm "tran_∩_thm";
=TEX
}%ignore
=SML
set_goal([], ⌜∀ x y:GS⦁ transitive x ∧ transitive y ⇒ transitive (x ∪⋎g y)⌝);
=TEX
\ignore{
=SML
a (rewrite_tac[get_spec ⌜transitive⌝]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (ALL_ASM_FC_T (MAP_EVERY ante_tac) []);
a (rewrite_tac [get_spec ⌜$⊆⋎g⌝]
	THEN prove_tac[]);
(* *** Goal "2" *** *)
a (ALL_ASM_FC_T (MAP_EVERY ante_tac) []);
a (rewrite_tac [get_spec ⌜$⊆⋎g⌝]
	THEN prove_tac[]);
val tran_∪_thm = save_pop_thm "tran_∪_thm";
=TEX
}%ignore
=SML
set_goal([], ⌜∀ x y:GS⦁ connected x ∧ connected y ⇒ connected (x ∩⋎g y)⌝);
=TEX
\ignore{
=SML
a (rewrite_tac[get_spec ⌜connected⌝]);
a (REPEAT strip_tac);
a (list_spec_nth_asm_tac 8 [⌜t⌝, ⌜u⌝]);
val conn_∩_thm = save_pop_thm "conn_∩_thm";
=TEX
}%ignore
=SML
set_goal([], ⌜∀ x y:GS⦁ ordinal x ∧ ordinal y ⇒ ordinal (x ∩⋎g y)⌝);
=TEX
\ignore{
=SML
a (rewrite_tac[get_spec ⌜ordinal⌝]);
a (REPEAT_N 3 strip_tac);
a (all_asm_fc_tac [tran_∩_thm, conn_∩_thm]
	THEN contr_tac);
val ord_∩_thm = save_pop_thm "ord_∩_thm";
=TEX
}%ignore
=SML
set_goal([], ⌜∀ x y:GS⦁ ordinal x ∧ ordinal y ∧ x ⊆⋎g y ∧ ¬ x = y ⇒ x ∈⋎g y⌝);
=TEX
\ignore{
=SML
a (REPEAT strip_tac);
a (lemma_tac ⌜∃z⦁ z = Sep y (λv⦁ ¬ v ∈⋎g x)⌝
	THEN1 prove_∃_tac);
a (DROP_NTH_ASM_T 2 (fn x=> strip_asm_tac (rewrite_rule [gs_ext_axiom] x)));
(* *** Goal "1" *** *)
a (GET_NTH_ASM_T 4 (fn x=> all_asm_fc_tac [rewrite_rule [get_spec ⌜$⊆⋎g⌝] x]));
(* *** Goal "2" *** *)
a (lemma_tac ⌜e ∈⋎g z⌝ THEN1 asm_rewrite_tac[]);
a (strip_asm_tac gs_wf_min_thm);
a (spec_nth_asm_tac 1 ⌜z⌝);
(* *** Goal "2.1" *** *)
a (spec_nth_asm_tac 1 ⌜e⌝);
(* *** Goal "2.2" *** *)
a (lemma_tac ⌜z' ∈⋎g y ∧ ¬ z' ∈⋎g x⌝
	THEN1 (DROP_NTH_ASM_T 2 ante_tac
		THEN asm_rewrite_tac[]));
a (lemma_tac ⌜z' = x⌝
	THEN (DROP_NTH_ASM_T 3 ante_tac
		THEN asm_rewrite_tac[gs_ext_axiom]
		THEN REPEAT strip_tac));
(* *** Goal "2.2.1" *** *)
a (lemma_tac ⌜e' ∈⋎g  y⌝);
(* *** Goal "2.2.1.1" *** *)
a (lemma_tac ⌜transitive y⌝
	THEN1 (all_asm_fc_tac [get_spec ⌜ordinal⌝]));
a (LEMMA_T ⌜z' ⊆⋎g y⌝ ante_tac THEN1 (all_asm_fc_tac [get_spec ⌜transitive⌝]));
a (rewrite_tac [get_spec ⌜$⊆⋎g⌝]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
(* *** Goal "2.2.1.2" *** *)
a (spec_nth_asm_tac 3 ⌜e'⌝);
(* *** Goal "2.2.2" *** *)
a (lemma_tac ⌜e' ∈⋎g y⌝
	THEN1 (GET_NTH_ASM_T 11 ante_tac
		THEN rewrite_tac [get_spec ⌜$⊆⋎g⌝]
		THEN asm_prove_tac[]));
a (LEMMA_T ⌜connected y⌝ (fn x=> asm_tac(rewrite_rule [get_spec ⌜connected⌝] x)) 
	THEN1 (all_asm_fc_tac [get_spec ⌜ordinal⌝]));
a (list_spec_nth_asm_tac 1 [⌜e'⌝, ⌜z'⌝]);
(* *** Goal "2.2.2.1" *** *)
a (swap_nth_asm_concl_tac 4 THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2" *** *)
a (lemma_tac ⌜transitive x⌝
	THEN1 (all_asm_fc_tac [get_spec ⌜ordinal⌝]));
a (LEMMA_T ⌜e' ⊆⋎g x⌝ ante_tac THEN1 (all_asm_fc_tac [get_spec ⌜transitive⌝]));
a (rewrite_tac [get_spec ⌜$⊆⋎g⌝]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
val trichot_lemma = pop_thm();
=TEX

=IGN
set_goal([], ⌜∀ x y:GS⦁ ordinal x ∧ ordinal y ⇒ ordinal (x ∪⋎g y)⌝);
a (REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜y⌝] trich_for_ords_thm));
(* *** Goal "1" *** *)
a 

a (spec_nth_asm_tac 1  

a (rewrite_tac[get_spec ⌜ordinal⌝]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_asm_fc_tac [tran_∪_thm]);
(* *** Goal "2" *** *)
a (all_asm_ante_tac);
a (rewrite_tac[get_spec ⌜connected⌝, get_spec ⌜transitive⌝]);
a (REPEAT_N 6 strip_tac);

val ord_∪_thm = save_pop_thm "ord_∪_thm";
=TEX
}%ignore

=GFT
⦏trich_for_ords_thm⦎ =
	⊢ ∀ x y⦁ ordinal x ∧ ordinal y ⇒ x <⋎o y ∨ x = y ∨ y <⋎o x

⦏sub_leo_thm⦎ =
	⊢ ∀ x y⦁ ordinal x ∧ ordinal y ⇒ (x ⊆⋎g y ⇔ x ≤⋎o y)

⦏sub_leo_thm1⦎ =
	⊢ ∀ x y⦁ ordinal x ∧ ordinal y ∧ x ⊆⋎g y ⇒ x ≤⋎o y
=TEX


\ignore{
=SML
set_goal([], ⌜∀ x y:GS⦁ ordinal x ∧ ordinal y ⇒ x <⋎o y ∨ x = y ∨ y <⋎o x⌝);
a (rewrite_tac[get_spec ⌜$<⋎o⌝]);
a (REPEAT_N 3 strip_tac THEN asm_rewrite_tac[]);
a (lemma_tac ⌜ordinal (x ∩⋎g y)⌝
	THEN1 (all_fc_tac [ord_∩_thm]));
a (lemma_tac ⌜x ∩⋎g y ⊆⋎g x ∧ x ∩⋎g y ⊆⋎g y⌝
	THEN1 (prove_tac[gst_relext_clauses, gst_opext_clauses]));
a (lemma_tac ⌜x ∩⋎g y = x ∨ x ∩⋎g y = y⌝
	THEN1 contr_tac);
(* *** Goal "1" *** *)
a (strip_asm_tac trichot_lemma);
a (all_asm_fc_tac []);
(*
a (list_spec_nth_asm_tac 2 [⌜x ∩⋎g y⌝, ⌜x⌝]);
*)
a (strip_asm_tac wf_l1);
a (spec_nth_asm_tac 1 ⌜x ∩⋎g y⌝);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac [gst_relext_clauses, gst_opext_clauses]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜x ⊆⋎g y⌝
	THEN1 (POP_ASM_T ante_tac
		THEN prove_tac [gst_relext_clauses, gst_opext_clauses]));
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜y⌝] trichot_lemma)
	THEN contr_tac);
a (asm_fc_tac []);
(* *** Goal "3" *** *)
a (lemma_tac ⌜y ⊆⋎g x⌝
	THEN1 (POP_ASM_T ante_tac
		THEN prove_tac [gst_relext_clauses, gst_opext_clauses]));
a (strip_asm_tac (list_∀_elim [⌜y⌝, ⌜x⌝] trichot_lemma)
	THEN asm_rewrite_tac[]);
val trich_for_ords_thm = save_pop_thm "trich_for_ords_thm";

set_goal([], ⌜∀x y:GS⦁ ordinal x ∧ ordinal y ⇒ (x ⊆⋎g y ⇔ x ≤⋎o y)⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (asm_rewrite_tac [leo_lo_thm]);
a contr_tac;
a (all_fc_tac [trich_for_ords_thm]);
a (fc_tac [lto_psub_thm]);
a (POP_ASM_T ante_tac THEN DROP_NTH_ASM_T 4 ante_tac);
a (rewrite_tac [gst_relext_clauses, get_spec ⌜$⊂⋎g⌝]
	THEN prove_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [leo_sub_thm]);
val sub_leo_thm = save_pop_thm "sub_leo_thm";

=IGN
set_goal([], ⌜∀x y:GS⦁ ordinal x ∧ ordinal y ⇒ (x ⊂⋎g y ⇔ x <⋎o y)⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a contr_tac;
a (all_fc_tac [trich_for_ords_thm]);
a (fc_tac [leo_sub_thm]);
a (POP_ASM_T ante_tac THEN DROP_NTH_ASM_T 4 ante_tac);
a (rewrite_tac [gst_relext_clauses, get_spec ⌜$⊂⋎g⌝]
	THEN prove_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [leo_sub_thm]);
val sub_leo_thm = save_pop_thm "sub_leo_thm";

=SML
set_goal([], ⌜∀x y:GS⦁ ordinal x ∧ ordinal y ∧ x ⊆⋎g y ⇒ x ≤⋎o y⌝);
a (REPEAT strip_tac);
a (fc_tac [sub_leo_thm]);
a (asm_fc_tac[]);
val sub_leo_thm1 = save_pop_thm "sub_leo_thm1";

=IGN
set_goal([], ⌜∀x y:GS⦁ ordinal x ∧ ordinal y ∧ x ⊂⋎g y ⇒ x <⋎o y⌝);
a (REPEAT strip_tac);
a (fc_tac [psub_lo_thm]);
a (asm_fc_tac[]);
val sub_leo_thm1 = save_pop_thm "sub_leo_thm1";

=TEX
}%ignore

\subsection{Definition 2.6}

Successor and limit ordinals are defined.
Natural numbers are defined.

\subsubsection{}

These definitions are not the ones used by Drake, and not only the names but the concepts differ.
My successor predicate does not hold of the empty set.
I use the name "natural number" where he talks of integers, and generally I'm chosing longer names.

ⓈHOLCONST
 ⦏successor⦎ : GS → BOOL
├
  ∀s :GS⦁ successor s ⇔ ∃t⦁ ordinal t ∧ s = suc⋎o t
■

ⓈHOLCONST
 ⦏limit_ordinal⦎ : GS → BOOL
├
  ∀s :GS⦁ limit_ordinal s ⇔ ordinal s ∧ ¬ successor s ∧ ¬ s = ∅⋎g
■

\subsection{Theorem 2.7}

Induction theorems over ordinals.

\subsubsection{Successors are Ordinals}

=SML
set_goal([],⌜	∀ x:GS⦁ successor x ⇒ ordinal x	⌝);
a (rewrite_tac[get_spec ⌜successor⌝]
	THEN REPEAT strip_tac
	THEN fc_tac [ord_suc_ord_thm]
	THEN asm_rewrite_tac[]);
val successor_ord_thm = save_pop_thm "successor_ord_thm";
=TEX

\subsubsection{Well-foundedness of the ordinals}

First we prove that $<⋎o$ is well-founded.

=GFT
=TEX

\ignore{
=SML
set_goal([],⌜well_founded $<⋎o⌝);
a (asm_tac gs_wf_thm1);
a (fc_tac [wf_restrict_wf_thm]);
a (SPEC_NTH_ASM_T 1 ⌜λx y⦁ ordinal x ∧ ordinal y⌝ ante_tac
	THEN rewrite_tac[]);
a (lemma_tac ⌜$<⋎o = (λ x y⦁ (ordinal x ∧ ordinal y) ∧ x ∈⋎g y)⌝);
(* *** Goal "1" *** *)
a (once_rewrite_tac [ext_thm]);
a (once_rewrite_tac [ext_thm]);
a (prove_tac[get_spec ⌜$<⋎o⌝]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
val wf_ordinals_thm = save_pop_thm "wf_ordinals_thm";

set_goal([],⌜UWellFounded $<⋎o⌝);
a (rewrite_tac [UWellFounded_well_founded_thm, wf_ordinals_thm]);
val UWellFounded_ordinals_thm = pop_thm ();
=TEX
}%ignore

\subsubsection{An Ordinal is Zero, a successor or a limit}

=GFT
⦏ordinal_kind_thm⦎ =
	∀n⦁ ordinal n ⇒ n = ∅⋎g ∨ successor n  ∨ limit_ordinal n
=TEX

\ignore{
=SML
set_goal ([], ⌜∀n⦁ ordinal n ⇒ n = ∅⋎g ∨ successor n  ∨ limit_ordinal n⌝);
a (rewrite_tac [get_spec ⌜limit_ordinal⌝, get_spec ⌜successor⌝]);
a (REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜t⌝);
val ordinal_kind_thm = save_pop_thm "ordinal_kind_thm";
=TEX
}%ignore

\subsection{Supremum and Strict Supremum}

The supremum of a set of ordinals is the smallest ordinal greater than or equal to every ordinal in the set.
With the Von Neumann representation of ordinals this is just the union of the set of ordinals.

=SML
declare_infix (200, "ub");
declare_infix (200, "sub");
=TEX

ⓈHOLCONST
 $⦏ub⦎ : GS → GS → BOOL
├
  ∀α β⦁ α ub β ⇔ ∀γ⦁ γ ∈⋎g α ⇒ γ ≤⋎o β
■

ⓈHOLCONST
 ⦏sup⦎ : GS → GS
├
  ∀α⦁ sup α = ⋃⋎g α
■

=GFT
⦏ordinal_limit_thm⦎ =
	⊢ ∀ α⦁ (∀ β⦁ β ∈⋎g α ⇒ ordinal β) ⇒ ordinal (⋃⋎g α)

⦏sup_lub_thm⦎ =
	⊢ ∀ α ⦁	(∀ β⦁ β ∈⋎g α ⇒ ordinal β)
		⇒ α ub sup α
		∧ (∀ γ⦁ ordinal γ ∧ α ub γ ⇒ sup α ≤⋎o γ)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀α⦁ (∀β⦁ β ∈⋎g α ⇒ ordinal β) ⇒ ordinal (⋃⋎g α)⌝);
a (REPEAT strip_tac);
a (rewrite_tac [get_spec ⌜ordinal⌝, get_spec ⌜transitive⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [gst_relext_clauses] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 4 ⌜e'⌝);
a (fc_tac [get_spec ⌜ordinal⌝]);
a (fc_tac [get_spec ⌜transitive⌝]);
a (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[]);
a (SPEC_NTH_ASM_T 1 ⌜e⌝ (ante_tac o (rewrite_rule [gst_relext_clauses])));
a (asm_rewrite_tac [] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜connected⌝] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 7 ⌜e⌝);
a (spec_nth_asm_tac 8 ⌜e'⌝);
a (strip_asm_tac (list_∀_elim [⌜e⌝, ⌜e'⌝] trich_for_ords_thm));
(* *** Goal "2.1" *** *)
a (fc_tac [get_spec ⌜$<⋎o⌝]);
a (lemma_tac ⌜e ⊆⋎g e'⌝
	THEN1 (fc_tac [get_spec ⌜ordinal⌝]
	     THEN fc_tac [get_spec ⌜transitive⌝]
		THEN asm_fc_tac[]));
a (lemma_tac ⌜t ∈⋎g e'⌝
	THEN1 (POP_ASM_T (asm_tac o (rewrite_rule [get_spec ⌜$⊆⋎g⌝]))
		THEN asm_fc_tac []));
a (lemma_tac ⌜connected e'⌝ THEN1 fc_tac [get_spec ⌜ordinal⌝]);
a (fc_tac [get_spec⌜connected⌝]
	THEN all_asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (all_var_elim_asm_tac);
a (lemma_tac ⌜connected e'⌝ THEN1 fc_tac [get_spec ⌜ordinal⌝]);
a (fc_tac [get_spec⌜connected⌝]
	THEN all_asm_fc_tac[]);
(* *** Goal "2.3" *** *)
a (fc_tac [get_spec ⌜$<⋎o⌝]);
a (lemma_tac ⌜e' ⊆⋎g e⌝
	THEN1 (fc_tac [get_spec ⌜ordinal⌝]));
a (REPEAT_N 2 (POP_ASM_T discard_tac));
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜transitive⌝] THEN strip_tac);
a (asm_fc_tac[]);
a (lemma_tac ⌜u ∈⋎g e⌝
	THEN1 (POP_ASM_T (asm_tac o (rewrite_rule [get_spec ⌜$⊆⋎g⌝]))
		THEN asm_fc_tac []));
a (lemma_tac ⌜connected e⌝ THEN1 fc_tac [get_spec ⌜ordinal⌝]);
a (fc_tac [get_spec⌜connected⌝]
	THEN all_asm_fc_tac[]);
val ordinal_limit_thm = save_pop_thm "ordinal_limit_thm";

set_goal([], ⌜∀α⦁ (∀β⦁ β ∈⋎g α ⇒ ordinal β)
	⇒ α ub (sup α) ∧ ∀γ⦁ ordinal γ ∧ α ub γ ⇒ (sup α) ≤⋎o γ⌝);
a (rewrite_tac [get_spec ⌜$ub⌝, get_spec ⌜$sup⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [ordinal_limit_thm]);
a (asm_fc_tac[]);
a (LEMMA_T ⌜γ ⊆⋎g ⋃⋎g α ⇒ γ ≤⋎o ⋃⋎g α⌝ (fn x => bc_tac [x]));
(* *** Goal "1.1" *** *)
a (strip_tac);
a (all_fc_tac [sub_leo_thm1]);
(* *** Goal "1.2" *** *)
a (rewrite_tac[gst_relext_clauses]);
a (REPEAT strip_tac);
a (∃_tac ⌜γ⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac [ordinal_limit_thm]);
a (bc_tac [sub_leo_thm1]
	THEN_TRY asm_rewrite_tac[gst_relext_clauses]);
a (REPEAT strip_tac);
a (asm_fc_tac[]);
a (fc_tac [leo_sub_thm]);
a (POP_ASM_T ante_tac
	THEN rewrite_tac [gst_relext_clauses]
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
val sup_lub_thm = save_pop_thm "sup_lub_thm"; 
=TEX
}%ignore

The operand here is intended to be an arbitrary set of ordinals and the result is the smallest ordinal strictly greater than any in the set.

ⓈHOLCONST
 $⦏sub⦎ : GS → GS → BOOL
├
  ∀α β⦁ α sub β ⇔ ∀γ⦁ γ ∈⋎g α ⇒ γ <⋎o β
■

ⓈHOLCONST
 ⦏ssup⦎ : GS → GS
├
  ∀α⦁ ssup α = ⋃⋎g(Imagep suc⋎o α)
■

=GFT
⦏ordinal_ssup_thm⦎ =
	⊢ ∀ α⦁ (∀ β⦁ β ∈⋎g α ⇒ ordinal β) ⇒ ordinal (ssup α)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀α⦁ (∀β⦁ β ∈⋎g α ⇒ ordinal β) ⇒ ordinal (ssup α)⌝);
a (REPEAT strip_tac);
a (rewrite_tac [(*get_spec ⌜ordinal⌝, get_spec ⌜transitive⌝, *)get_spec ⌜ssup⌝] THEN REPEAT strip_tac);
a (lemma_tac ⌜∀β⦁ β ∈⋎g Imagep suc⋎o α ⇒ ordinal β⌝);
(* *** Goal "1" *** *)
a (rewrite_tac[]);
a (REPEAT strip_tac);
a (asm_fc_tac []);
a (fc_tac [ord_suc_ord_thm]);
a (once_asm_rewrite_tac[]);
a strip_tac;
(* *** Goal "2" *** *)
a (fc_tac [ordinal_limit_thm]);
val ordinal_ssup_thm = save_pop_thm "ordinal_ssup_thm";

=IGN
stop;
set_goal([], ⌜∀α⦁ (∀β⦁ β ∈⋎g α ⇒ ordinal β)
	⇒ α sub (ssup α) ∧ ∀γ⦁ ordinal γ ∧ α sub γ ⇒ (sup α) ≤⋎o γ⌝);
a (rewrite_tac (map get_spec [⌜$sub⌝])
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (asm_fc_tac[]);
a (fc_tac[ordinal_ssup_thm]);
a (fc_tac[]);


=TEX
}%ignore

\subsection{Rank}

We define the rank of a set.

\subsubsection{The Consistency Proof}

Before introducing the definition of rank we undertake the proof necessary to establish that the definition is conservative.
The key lemma in this proof is the proof that the relevant functional "respects" the membership relation.

=GFT
⦏respect_lemma⦎ =
	⊢ (λ f x⦁ ⋃⋎g (Imagep (suc⋎o o f) x)) respects $∈⋎g
=TEX

\ignore{
=SML
set_goal([],⌜(λf⦁ λx⦁ ⋃⋎g (Imagep (suc⋎o o f) x)) respects $∈⋎g⌝);
a (rewrite_tac [get_spec ⌜$respects⌝]
	THEN REPEAT strip_tac);
a (once_rewrite_tac [gst_relext_clauses]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜e'⌝ THEN REPEAT strip_tac);
a (∃_tac ⌜e''⌝ THEN REPEAT strip_tac);
a (POP_ASM_T ante_tac
	THEN rewrite_tac[get_spec⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝]
	THEN strip_tac);
a (lemma_tac ⌜h e'' = g e''⌝
	THEN1 (REPEAT_N 2 (asm_fc_tac[tc_incr_thm])
		THEN asm_rewrite_tac[]));
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜e'⌝ THEN REPEAT strip_tac);
a (∃_tac ⌜e''⌝ THEN REPEAT strip_tac);
a (POP_ASM_T ante_tac
	THEN rewrite_tac[get_spec⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝]
	THEN strip_tac);
a (lemma_tac ⌜h e'' = g e''⌝
	THEN1 (REPEAT_N 2 (asm_fc_tac[tc_incr_thm])
		THEN asm_rewrite_tac[]));
a (asm_rewrite_tac[]);
val respect_lemma = pop_thm();
=TEX
}%ignore

Armed with that lemma we can now prove that the function which we will call "rank" exists.

\ignore{
=SML
set_goal([],⌜∃rank⦁ ∀x⦁ rank x = ⋃⋎g (Imagep (suc⋎o o rank) x)⌝);
a (∃_tac ⌜fix (λf⦁ λx⦁ ⋃⋎g (Imagep (suc⋎o o f) x))⌝
	THEN strip_tac);
a (asm_tac gs_wf_thm1);
a (asm_tac respect_lemma);
a (fc_tac [∀_elim ⌜λf⦁ λx⦁ ⋃⋎g (Imagep (suc⋎o o f) x)⌝ (get_spec ⌜fix⌝)]);
a (asm_fc_tac []);
a (POP_ASM_T (rewrite_thm_tac o rewrite_rule [ext_thm]));
val _ = save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
 ⦏rank⦎ : GS → GS
├
  ∀x⦁ rank x = ⋃⋎g (Imagep (suc⋎o o rank) x)
■

\subsection{Ordinal Arithmetic}

\subsubsection{Addition}

The following lemma is used to demonstrate well-foundedness of the definition of ordinal addition:

=GFT
⦏plus⋎o_respect_lemma⦎ =
   ⊢ ∀ x⦁ (λ x_+ y⦁ if y = ∅⋎g then x else ssup (Imagep x_+ y)) respects $∈⋎g
=TEX

\ignore{
=IGN
set_goal([],⌜∀x⦁ (λx_+:GS → GS⦁ λy⦁ if y = ∅⋎g then x else ⋃⋎g(Imagep (suc⋎o o x_+) y)) respects $∈⋎g⌝);
a (rewrite_tac [get_spec ⌜$respects⌝]
	THEN REPEAT strip_tac);
a (cases_tac ⌜x' = ∅⋎g⌝ THEN asm_rewrite_tac[]);
a (LEMMA_T ⌜Imagep (suc⋎o o g) x' = Imagep (suc⋎o o h) x'⌝ rewrite_thm_tac);
a (once_rewrite_tac [gs_ext_axiom]);
a (rewrite_tac [get_spec ⌜Imagep⌝]);
a (REPEAT strip_tac);
(* ** Goal "1" *** *)
a (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[get_spec ⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝]);
a (fc_tac [tc_incr_thm]);
a (asm_fc_tac[] THEN (ALL_ASM_FC_T rewrite_tac []));
(* *** Goal "2" *** *)
a (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[get_spec ⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝]);
a (fc_tac [tc_incr_thm]);
a (asm_fc_tac[] THEN (ALL_ASM_FC_T rewrite_tac []));
val plus⋎o_respect_lemma = pop_thm ();
=SML
set_goal([],⌜∀x⦁ (λx_+:GS → GS⦁ λy⦁ if y = ∅⋎g then x else ssup (Imagep x_+ y)) respects $∈⋎g⌝);
a (rewrite_tac [get_spec ⌜$respects⌝]
	THEN REPEAT strip_tac);
a (cases_tac ⌜x' = ∅⋎g⌝ THEN asm_rewrite_tac[]);
a (LEMMA_T ⌜Imagep g x' = Imagep h x'⌝ rewrite_thm_tac);
a (once_rewrite_tac [gs_ext_axiom]);
a (rewrite_tac [get_spec ⌜Imagep⌝]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[get_spec ⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝]);
a (fc_tac [tc_incr_thm]);
a (asm_fc_tac[] THEN (ALL_ASM_FC_T rewrite_tac []));
(* *** Goal "2" *** *)
a (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[get_spec ⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝]);
a (fc_tac [tc_incr_thm]);
a (asm_fc_tac[] THEN (ALL_ASM_FC_T rewrite_tac []));
val plus⋎o_respect_lemma = pop_thm ();

declare_infix (300, "+⋎o");
declare_infix (300, "--⋎o");

set_goal([], ⌜∃$+⋎o:GS → GS → GS⦁ ∀α β:GS⦁ α +⋎o β
	= if β = ∅⋎g then α else ssup (Imagep ($+⋎o α) β)⌝);
a (∃_tac ⌜λα⦁ fix (λ x_+ y⦁ if y = ∅⋎g then α else ssup (Imagep x_+ y))⌝
	THEN REPEAT strip_tac THEN rewrite_tac[]);
a (asm_tac gs_wf_thm1);
a (asm_tac plus⋎o_respect_lemma);
a (fc_tac [∀_elim ⌜(λ x_+ y⦁ if y = ∅⋎g then α else ssup (Imagep x_+ y))⌝ (get_spec ⌜fix⌝)]);
a (spec_nth_asm_tac 2 ⌜α⌝);
a (spec_nth_asm_tac 2 ⌜α⌝);
a (POP_ASM_T (asm_tac o (rewrite_rule[ext_thm])));
a (SYM_ASMS_T rewrite_tac);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
 $⦏+⋎o⦎ : GS → GS → GS
├
  ∀α β⦁ α +⋎o β = if β = ∅⋎g then α else ssup (Imagep ($+⋎o α) β)
■

=GFT
ord_plus_thm =
	⊢ ∀ α β⦁ ordinal α ∧ ordinal β ⇒ ordinal (α +⋎o β)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀α β⦁ ordinal α ∧ ordinal β ⇒ ordinal (α +⋎o β)⌝);
a (REPEAT ∀_tac);
a (wf_induction_tac gs_wf_thm1 ⌜β⌝);
a (rewrite_tac [get_spec ⌜$+⋎o⌝]);
a (REPEAT strip_tac);
a (cases_tac ⌜t = ∅⋎g⌝ THEN asm_rewrite_tac[]);
a (lemma_tac ⌜∀γ⦁ ordinal γ ∧ γ ∈⋎g t ⇒ ordinal (α +⋎o γ)⌝);
(* *** Goal "1" *** *)
a (REPEAT strip_tac);
a (fc_tac [tc_incr_thm]);
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜∀ν⦁ ν ∈⋎g (Imagep ($+⋎o α) t) ⇒ ordinal ν⌝);
(* *** Goal "2.1" *** *)
a (rewrite_tac []);
a (REPEAT strip_tac);
a (asm_rewrite_tac[]);
a (fc_tac[ord_mem_ord]);
a (spec_nth_asm_tac 1 ⌜e⌝);
a (spec_nth_asm_tac 6 ⌜e⌝);
(* *** Goal "2.2" *** *)
a (fc_tac[ordinal_ssup_thm]);
val ord_plus_thm = save_pop_thm "ord_plus_thm";
=IGN
stop;
set_goal ([], ⌜∀α β⦁ ordinal α ∧ ordinal β ⇒ α +⋎o β = ⋃⋎g {γ | ∃η⦁ η <⋎o β ∧ γ = suc⋎o(α +⋎o η)}⌝);



set_goal ([], ⌜∀α⦁ ordinal α ⇒ ∅⋎g +⋎o α = α⌝);
a (strip_tac);
a (wf_induction_tac gs_wf_thm1 ⌜α⌝);
a (wf_induction_tac wf_ordinals_thm ⌜α⌝);
a (rewrite_tac [get_spec ⌜$+⋎o⌝]);
a (cases_tac ⌜t = ∅⋎g⌝ THEN asm_rewrite_tac[]);
a (once_rewrite_tac [gst_relext_clauses]);
a (rewrite_tac[]);
a (REPEAT strip_tac);
a (POP_ASM_T ante_tac
	THEN rewrite_tac [get_spec ⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝,
			get_spec ⌜$+⋎o⌝]);

set_goal ([], ⌜∀α β γ⦁ ordinal α ∧ ordinal β ∧ ordinal γ
		⇒ (α +⋎o (β +⋎o γ)) = ((α +⋎o β) +⋎o γ)⌝);
a (rewrite_tac [get_spec ⌜$+⋎o⌝] THEN REPEAT ∀_tac THEN strip_tac);
a (cases_tac ⌜γ = ∅⋎g⌝ THEN asm_rewrite_tac[]);
a (cases_tac ⌜β = ∅⋎g⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (LEMMA_T ⌜¬ ⋃⋎g (Imagep (suc⋎o o $+⋎o ∅⋎g) γ) = ∅⋎g⌝ rewrite_thm_tac);
(* *** Goal "1.1" *** *)
a (once_rewrite_tac [gs_ext_axiom]);
a (rewrite_tac []);
a strip_tac;
a (rewrite_tac []);
a (GET_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [gs_ext_axiom])));
a (∃_tac ⌜e⌝ THEN ∃_tac ⌜(suc⋎o o $+⋎o ∅⋎g) e⌝);
a (strip_tac);
(* *** Goal "1.1.1" *** *)
a (rewrite_tac [get_spec ⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝,
	get_spec ⌜$+⋎o⌝]);
a (cases_tac ⌜e = ∅⋎g⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.1.1.1" *** *)
a (rewrite_tac [get_spec ⌜suc⋎o⌝]);
(* *** Goal "1.1.1.2" *** *)
a (rewrite_tac (map get_spec [⌜suc⋎o⌝, ⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝]));
a (REPEAT strip_tac);
a (once_rewrite_tac [gst_relext_clauses]);
a (rewrite_tac[get_spec ⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝]);
a (REPEAT strip_tac);
(* *** Goal "1.1.1.2.1" *** *)
a (∃_tac ⌜suc⋎o e'⌝ THEN once_rewrite_tac [prove_rule [get_spec ⌜suc⋎o⌝] ⌜e' ∈⋎g suc⋎o e'⌝]);
a (rewrite_tac [] THEN ∃_tac ⌜e'⌝ THEN asm_rewrite_tac []);

a (rewrite_tac (map get_spec [⌜suc⋎o⌝, ⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝]));

a (lemma_tac ⌜suc⋎o o $+⋎o ∅⋎g = ∅⋎g⌝);
=TEX
}%ignore

\subsubsection{Subtraction}

The following definition is of reverse subtraction, i.e. the right operand is subtracted from the left and is taken from the left of that operand so that the following lemma (as yet unproven) obtains:

=GFT
⦏--⋎o_lemma⦎ =
	∀α β⦁ α ≤⋎o β ⇒ α +⋎o (β --⋎o α) = β
=TEX

\ignore{
=IGN
set_goal([], ⌜∀α β:GS⦁ α ≤⋎o β ⇒ ∃γ⦁  α +⋎o γ = β⌝);
a (REPEAT ∀_tac);
a (wf_induction_tac gs_wf_thm1 ⌜β⌝);
a (strip_tac);
a (∃_tac ⌜Imagep (λu⦁ εγ⦁ α +⋎o γ = u) (Sep t (λν⦁ α ≤⋎o ν))⌝);
a (lemma_tac ⌜∀η⦁ η ∈⋎g Imagep (λ u⦁ ε γ⦁ α +⋎o γ = u) (Sep t (λ ν⦁ α ≤⋎o ν))
	⇔ ∃κ⦁ κ ∈⋎g t ∧ α ≤⋎o κ ∧ η = ε γ⦁ α +⋎o γ = κ⌝);
(* *** Goal "1" *** *)
a (strip_tac THEN rewrite_tac [get_spec ⌜Imagep⌝]);
a (REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜κ⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜$+⋎o⌝]);
a (rewrite_tac [gs_ext_axiom]);

a (rewrite_tac [get_spec ⌜Imagep⌝]);
a (cases_tac ⌜α = t⌝ THEN_TRY asm_rewrite_tac[]);

;

set_goal([], ⌜∃$--⋎o⦁ ∀α β:GS⦁ α ≤⋎o β ⇒ α +⋎o (α --⋎o β) = β⌝);
a (∃_tac ⌜λα β⦁ if α ≤⋎o β then εγ⦁ α +⋎o γ = β else ∅⋎g⌝);
a (rewrite_tac[]);

frees⌜λα β⦁ if α ≤⋎o β then εγ⦁ α +⋎o γ = β else ∅⋎g⌝;
get_spec ⌜$≤⋎o⌝;
=TEX
}%ignore

ⓈHOLCONST
 $⦏--⋎o⦎ : GS → GS → GS
├
  T
■


\subsection{Proof Context}

In this section we define a proof context for ordinals.

\subsubsection{Proof Context}

=SML
add_pc_thms "'gst-ord" ([]);
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-ord"];
commit_pc "'gst-ord";
=TEX

\section{Natural Numbers}

=SML
open_theory "gst-ord";
force_new_theory "gst-nat";
force_new_pc "'gst-nat";
merge_pcs ["'savedthm_cs_∃_proof"] "'gst-nat";
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-ord", "'gst-nat"];
=TEX

ⓈHOLCONST
 ⦏natural_number⦎ : GS → BOOL
├
  ∀s :GS⦁ natural_number s ⇔ s = ∅⋎g ∨ (successor s ∧ ∀t⦁ t∈⋎g s ⇒ t = ∅⋎g ∨ successor t)
■

\subsubsection{Ordering the Natural Numbers}

To get an induction principle for the natural numbers we first define a well-founded ordering over them.
Since I don't plan to use this a lot I use the name $<⋎g⋎n$ (less than over the natural numbers defined in galactic set theory).

=SML
declare_infix(240,"<⋎g⋎n");
=TEX

ⓈHOLCONST
 $⦏<⋎g⋎n⦎ : GS → GS → BOOL
├
  ∀x y:GS⦁ x <⋎g⋎n y ⇔ natural_number x ∧ natural_number y ∧ x ∈⋎g y
■

Now we try to find a better proof that the one above that this is well-founded.
And fail, this is just a more compact rendition of the same proof.

=SML
set_goal([],⌜well_founded $<⋎g⋎n⌝);
a (asm_tac gs_wf_thm1);
a (fc_tac [wf_restrict_wf_thm]);
a (SPEC_NTH_ASM_T 1 ⌜λx y⦁ natural_number x ∧ natural_number y⌝ ante_tac
	THEN rewrite_tac[]);
a (lemma_tac ⌜$<⋎g⋎n = (λ x y⦁ (natural_number x ∧ natural_number y) ∧ x ∈⋎g y)⌝
	THEN1 (REPEAT_N 2 (once_rewrite_tac [ext_thm])
		THEN prove_tac[get_spec ⌜$<⋎g⋎n⌝]));
a (asm_rewrite_tac[]);
val wf_nat_thm = save_pop_thm "wf_nat_thm";
=TEX
This allows us to do well-founded induction over the natural number which the way I have implemented it is "course-of-values" induction.
However, for the sake of form I will prove that induction principle as an explicit theorem.
This is just what you get by expanding the definition of well-foundedness in the above theorem.
=SML
val nat_induct_thm = save_thm ("nat_induct_thm",
	(rewrite_rule [get_spec ⌜well_founded⌝] wf_nat_thm));
=TEX
Note that this theorem can only be used to prove properties which are true of all sets, so you have to make it conditional 
=INLINEFT
(natural_number n ⇒ whatever)
=TEX
I suppose I'd better do another one.
=SML
set_goal([], ⌜∀ p⦁ (∀ x⦁ natural_number x ∧ (∀ y⦁ y <⋎g⋎n x ⇒ p y) ⇒ p x)
	⇒ (∀ x⦁ natural_number x ⇒ p x)⌝);
a (asm_tac (rewrite_rule []
	(all_∀_intro (∀_elim ⌜λx⦁ natural_number x ⇒ p x⌝ nat_induct_thm))));
a (rewrite_tac [all_∀_intro (taut_rule ⌜a ∧ b ⇒ c ⇔ b ⇒ a ⇒ c⌝)]);
a (lemma_tac ⌜∀ p x⦁ (∀ y⦁ y <⋎g⋎n x ⇒ p y)
	⇔ (∀ y⦁ y <⋎g⋎n x ⇒ natural_number y ⇒ p y)⌝);
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜$<⋎g⋎n⌝]);
a (REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
val nat_induct_thm2 = save_pop_thm "nat_induct_thm2";
=TEX
I've tried using that principle and it too has disadvantages.
Because $<⋎g⋎n$ is used the induction hypothesis is more awkward to use (weaker) than it would have been if $∈⋎g$ had been used.
Unfortunately the proof of an induction theorem using plain set membership is not entirely trivial, so its proof has to be left til later.
=SML
set_goal([], ⌜∀ p⦁ (∀ x⦁ natural_number x ∧ (∀ y⦁ y ∈⋎g x ⇒ p y) ⇒ p x)
	⇒ (∀ x⦁ natural_number x ⇒ p x)⌝);
=IGN
a (asm_tac (rewrite_rule []
	(all_∀_intro (∀_elim ⌜λx⦁ natural_number x ⇒ p x⌝ nat_induct_thm))));
a (rewrite_tac [all_∀_intro (taut_rule ⌜a ∧ b ⇒ c ⇔ b ⇒ a ⇒ c⌝)]);
a (lemma_tac ⌜∀ p x⦁ ((∀ y⦁ y ∈⋎g x ⇒ p y) ⇒ natural_number x ⇒ p x)
	⇔ (∀ y⦁ y <⋎g⋎n x ⇒ natural_number y ⇒ p y) ⇒ natural_number x ⇒ p x⌝);
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜$<⋎g⋎n⌝]);
a (REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
val nat_induct_thm2 = save_pop_thm "nat_induct_thm2";
=TEX

\subsection{Theorem 2.8}

The set of natural numbers.

\subsubsection{Natural Numbers are Ordinals}

=SML
set_goal ([], ⌜∀n⦁ natural_number n ⇒ ordinal n⌝);
a (rewrite_tac [get_spec ⌜natural_number⌝, get_spec ⌜successor⌝]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[ordinal_∅⋎g]);
a (all_fc_tac [ord_suc_ord_thm]);
val ord_nat_thm = save_pop_thm "ord_nat_thm";
=TEX

\subsubsection{Members of Natural Numbers are Ordinals}

=SML
set_goal ([], ⌜∀n⦁ natural_number n ⇒ ∀m⦁ m ∈⋎g n ⇒ ordinal m⌝);
a (REPEAT strip_tac);
a (REPEAT (all_fc_tac[ord_nat_thm, ord_mem_ord]));
val mem_nat_ord_thm = save_pop_thm "mem_nat_ord_thm";
=TEX

\subsubsection{A Natural Number is not a Limit Ordinal}

=SML
set_goal ([], ⌜∀n⦁ natural_number n ⇒ ¬ limit_ordinal n⌝);
a (rewrite_tac [get_spec ⌜limit_ordinal⌝, get_spec ⌜natural_number⌝]);
a (REPEAT strip_tac);
val nat_not_lim_thm = save_pop_thm "nat_not_lim_thm";
=TEX

\subsubsection{A Natural Number is zero or a successor}

=SML
set_goal ([], ⌜∀n⦁ natural_number n ⇒ successor n ∨ n = ∅⋎g⌝);
a (rewrite_tac [get_spec ⌜natural_number⌝]);
a (REPEAT strip_tac);
val nat_zero_or_suc_thm = save_pop_thm "nat_zero_or_suc_thm";
=TEX

\subsubsection{A Natural Number does not contain a Limit Ordinal}

=SML
set_goal ([], ⌜∀m n⦁ natural_number n ∧ m ∈⋎g n ⇒ ¬ limit_ordinal m⌝);
a (rewrite_tac [get_spec ⌜limit_ordinal⌝, get_spec ⌜natural_number⌝]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [mem_not_empty_thm]);
(* *** Goal "2" *** *)
a (all_asm_fc_tac[]);
val mem_nat_not_lim_thm = save_pop_thm "mem_nat_not_lim_thm";
=TEX

\subsubsection{All Members of Natural Numbers are Natural Numbers}

=SML
set_goal ([], ⌜∀n⦁ natural_number n ⇒ ∀m⦁ m ∈⋎g n ⇒ natural_number m⌝);
a (rewrite_tac [get_spec ⌜natural_number⌝]);
a (REPEAT strip_tac THEN_TRY all_asm_fc_tac [mem_not_empty_thm]);
a (lemma_tac ⌜transitive n⌝ THEN1
	 (REPEAT (all_fc_tac [get_spec ⌜ordinal⌝, successor_ord_thm])));
a (lemma_tac ⌜t ∈⋎g n⌝ THEN1 (EVERY [all_fc_tac [get_spec ⌜transitive⌝],
	POP_ASM_T ante_tac, rewrite_tac [gst_relext_clauses], asm_prove_tac[]]));
a (all_asm_fc_tac[]);
val mem_nat_nat_thm = save_pop_thm "mem_nat_nat_thm";
=TEX

\subsubsection{Natural Numbers are in the Smallest Galaxy}

=SML
set_goal ([], ⌜∀n⦁ natural_number n ⇒ n ∈⋎g Gx ∅⋎g⌝);
a (strip_tac THEN gen_induction_tac1 nat_induct_thm2);
a (fc_tac [nat_zero_or_suc_thm]);
(* *** Goal "1" *** *)
a (fc_tac [get_spec ⌜successor⌝]);
a (lemma_tac ⌜t <⋎g⋎n n⌝
	THEN1 asm_rewrite_tac [get_spec ⌜$<⋎g⋎n⌝, get_spec ⌜suc⋎o⌝]);
(* *** Goal "1.1" *** *)
a (lemma_tac ⌜t ∈⋎g n⌝
	THEN1 asm_rewrite_tac [get_spec ⌜suc⋎o⌝]);
a (all_fc_tac [mem_nat_nat_thm]);
(* *** Goal "1.2" *** *)
a (asm_tac (∀_elim ⌜∅⋎g⌝ galaxy_Gx));
a (asm_rewrite_tac[]);
a (REPEAT (all_asm_fc_tac[GCloseSuc]));
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
val nat_in_G∅⋎g_thm = save_pop_thm "nat_in_G∅⋎g_thm";
=TEX

\subsubsection{The Existence of w}

This comes from the axiom of infinity, however, in galactic set theory we get that from the existence of galaxies, so the following proof is a little unusual.

=SML
set_goal ([], ⌜∃w⦁ ∀z⦁ z ∈⋎g w ⇔ natural_number z⌝);
a (∃_tac ⌜Sep (Gx ∅⋎g) natural_number⌝
	THEN rewrite_tac [gst_opext_clauses]);
a (rewrite_tac [all_∀_intro (taut_rule ⌜(a ∧ b ⇔ b) ⇔ b ⇒ a⌝)]);
a strip_tac;
a (gen_induction_tac1 nat_induct_thm2);
a (fc_tac [nat_zero_or_suc_thm]);
(* *** Goal "1" *** *)
a (fc_tac [get_spec ⌜successor⌝, nat_in_G∅⋎g_thm]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac []);
val w_exists_thm = save_pop_thm "w_exists_thm";
=TEX

\subsection{Naming the Natural Numbers}

It will be useful to be able to have names for the finite ordinals, which are used as tags in the syntax:

ⓈHOLCONST
│ ⦏Nat⋎g⦎: ℕ → GS
├───────────
│       Nat⋎g 0 = ∅⋎g
│ ∧ ∀n⦁ Nat⋎g (n+1) = suc⋎o (Nat⋎g n)
■

We will need to know that these are all distinct ordinals.

=GFT
⦏ord_nat_thm2⦎ =
	⊢ ∀ n⦁ ordinal (Nat⋎g n)

⦏not_suc_nat_zero_thm⦎ =
	⊢ ∀ n⦁ ¬ suc⋎o (Nat⋎g n) = ∅⋎g

⦏less_sum_thm⦎ =
	⊢ ∀ x y⦁ x ≤ y ⇒ (∃ z⦁ x + z = y)

⦏natg_mono_thm⦎ =
	⊢ ∀ x y⦁ Nat⋎g x ≤⋎o Nat⋎g (x + y)

⦏natg_one_one_thm⦎ =
	⊢ ∀ x y⦁ Nat⋎g x = Nat⋎g y ⇒ x = y

⦏natg_one_one_thm2⦎ =
	⊢ ∀ x y⦁ Nat⋎g x = Nat⋎g y ⇔ x = y
=TEX

\ignore{
=SML
set_goal([], ⌜∀n⦁ ordinal (Nat⋎g n)⌝);
a (strip_tac);
a (induction_tac ⌜n⌝);
a (rewrite_tac [get_spec ⌜Nat⋎g⌝, ordinal_∅⋎g]);
a (rewrite_tac [get_spec ⌜Nat⋎g⌝]);
a (fc_tac [ord_suc_ord_thm]);
val ord_nat_thm2 = save_pop_thm "ord_nat_thm2";

set_goal([], ⌜∀n⦁ ¬ suc⋎o (Nat⋎g n) = ∅⋎g⌝);
a (asm_tac ord_nat_thm2);
a (strip_asm_tac ∅⋎g_not_suc⋎o_thm);
a strip_tac;
a (spec_nth_asm_tac 1 ⌜Nat⋎g n⌝);
val not_suc_nat_zero_thm = save_pop_thm "not_suc_nat_zero_thm";

set_goal([], ⌜∀x y:ℕ⦁ x ≤ y ⇒ ∃z⦁ x + z = y⌝);
a (REPEAT ∀_tac);
a (induction_tac ⌜y⌝);
(* *** Goal "1" *** *)
a (strip_tac THEN ∃_tac ⌜0⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (strip_tac THEN ∃_tac ⌜0⌝
	THEN (PC_T1 "lin_arith" asm_prove_tac[]));
(* *** Goal "3" *** *)
a (strip_tac THEN ∃_tac ⌜z + 1⌝
	THEN (PC_T1 "lin_arith" asm_prove_tac[]));
val less_sum_thm = save_pop_thm "less_sum_thm";

set_goal([], ⌜∀x y:ℕ⦁ Nat⋎g x ≤⋎o Nat⋎g (x + y)⌝);
a (REPEAT ∀_tac);
a (induction_tac ⌜y⌝);
(* *** Goal "1" *** *)
a (rewrite_tac [leo_lo_thm, ord_nat_thm2]);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜Nat⋎g⌝,
	pc_rule1 "lin_arith" prove_rule [] ⌜x + y + 1 = (x + y) + 1⌝]);
a (asm_tac leo_suc_thm);
a (asm_tac ord_nat_thm2);
a (spec_nth_asm_tac 1 ⌜x+y⌝);
a (asm_fc_tac []);
a (all_asm_fc_tac [leo_trans_thm]);
val natg_mono_thm = save_pop_thm "natg_mono_thm";

set_goal([], ⌜∀x y⦁ Nat⋎g x = Nat⋎g y ⇒ x = y⌝);
a (REPEAT ∀_tac);
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜y⌝] ≤_cases_thm));
(* *** Goal "1" *** *)
a (fc_tac [less_sum_thm]);
a (POP_ASM_T ante_tac THEN induction_tac ⌜z⌝);
(* *** Goal "1.1" *** *)
a (rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a (strip_tac);
a (SYM_ASMS_T rewrite_tac);
a (lemma_tac ⌜Nat⋎g x ≤⋎o Nat⋎g (x + z)⌝
	THEN1 rewrite_tac [natg_mono_thm]);
a (lemma_tac ⌜Nat⋎g (x + z) <⋎o Nat⋎g (x + z + 1)⌝);
(* *** Goal "1.2.1" *** *)
a (rewrite_tac [pc_rule1 "lin_arith" prove_rule [] ⌜x + z + 1 = (x + z) + 1⌝]);
a (rewrite_tac [get_spec ⌜Nat⋎g⌝]);
a (asm_tac (∀_elim ⌜x+z⌝ ord_nat_thm2));
a (FC_T rewrite_tac [lo_suc_thm]);
(* *** Goal "1.2.2" *** *)
a (all_fc_tac [leo_lo_trans_thm]);
a (POP_ASM_T ante_tac
	THEN (rewrite_tac [get_spec ⌜$<⋎o⌝])
	THEN REPEAT strip_tac);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac [wf_l1]);
(* *** Goal "1.3" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "1.4" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [less_sum_thm]);
a (POP_ASM_T ante_tac THEN induction_tac ⌜z⌝);
(* *** Goal "2.1" *** *)
a (rewrite_tac[] THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (strip_tac);
a (SYM_ASMS_T rewrite_tac);
a (lemma_tac ⌜Nat⋎g y ≤⋎o Nat⋎g (y + z)⌝
	THEN1 rewrite_tac [natg_mono_thm]);
a (lemma_tac ⌜Nat⋎g (y + z) <⋎o Nat⋎g (y + z + 1)⌝);
(* *** Goal "2.2.1" *** *)
a (rewrite_tac [pc_rule1 "lin_arith" prove_rule [] ⌜y + z + 1 = (y + z) + 1⌝]);
a (rewrite_tac [get_spec ⌜Nat⋎g⌝]);
a (asm_tac (∀_elim ⌜y+z⌝ ord_nat_thm2));
a (FC_T rewrite_tac [lo_suc_thm]);
(* *** Goal "2.2.2" *** *)
a (all_fc_tac [leo_lo_trans_thm]);
a (POP_ASM_T ante_tac
	THEN (rewrite_tac [get_spec ⌜$<⋎o⌝])
	THEN REPEAT strip_tac);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac [wf_l1]);
(* *** Goal "2.3" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2.4" *** *)
a (asm_rewrite_tac[]);
val natg_one_one_thm = save_pop_thm "natg_one_one_thm";

set_goal([], ⌜∀x y⦁ Nat⋎g x = Nat⋎g y ⇔ x = y⌝);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (asm_fc_tac [natg_one_one_thm]);
val natg_one_one_thm2 = save_pop_thm "natg_one_one_thm2";

=IGN
set_goal([], ⌜∀x y⦁ Nat⋎g (x+y) = (Nat⋎g x) +⋎o (Nat⋎g y)⌝);
a (REPEAT ∀_tac);
a (induction_tac ⌜y⌝);
a (rewrite_tac[get_spec ⌜$+⋎o⌝, get_spec ⌜Nat⋎g⌝]);
a (rewrite_tac [pc_rule1 "lin_arith" prove_rule [] ⌜x + y + 1 = (x + y) + 1⌝]);
a (asm_rewrite_tac[get_spec⌜Nat⋎g⌝]);
=TEX
}%ignore

\subsection{Proof Context}

In this section we define a proof context for natural numbers.

\subsubsection{Proof Context}

=SML
add_pc_thms "'gst-nat" ([natg_one_one_thm2]);
set_merge_pcs ["basic_hol", "'gst-ax", "'gst-ord", "'gst-nat"];
commit_pc "'gst-nat";
=TEX

\section{Closing}

=SML
open_theory "gst-fun";
force_new_theory "GS";
(* new_parent "gst-sumprod";
new_parent "gst-fixp"; *)
new_parent "gst-ord";
new_parent "gst-nat";
force_new_pc "GS";
force_new_pc "'GS1";
val rewrite_thms = ref ([]:THM list);

merge_pcs ["'gst-ax", "'gst-fun"(*, "'gst-sumprod", "'gst-fixp", "'gst-lists"*),"'gst-ord", "'gst-nat"]
	"'GS1";
commit_pc "'GS1";
merge_pcs ["basic_hol", "'GS1"] "GS";
commit_pc "GS";
=TEX

%{\raggedright
%\bibliographystyle{fmu}
%\bibliography{rbj,fmu}
%} %\raggedright

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{gst-ax.th}
\include{gst-fun.th}
\include{gst-ord.th}
\include{gst-nat.th}
\include{GS.th}
}674  %\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
