=IGN
$Id: t007.doc,v 1.31 2013/01/28 19:30:13 rbj Exp $
open_theory "fixp";
set_merge_pcs ["basic_hol1", "'sets_alg", "'ℝ", "'savedthm_cs_∃_proof"];
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\tabstop=0.25in
\usepackage{A4}
\def\Hide#1{\relax}
\newcommand{\ignore}[1]{}

\title{Inductive and Co-inductive Definitions in ProofPower}
\makeindex
\author{Roger Bishop Jones\\rbj@rbjones.com}
\date{\ }
\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

\begin{document}
\vfill
\maketitle
\begin{abstract}
Systematic facilities for a range of different kinds of inductive and co-inductive definitions of sets and types in ProofPower HOL.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2004/07/15

Last Change $ $Date: 2013/01/28 19:30:13 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t007.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t007.pdf}

$ $Id: t007.doc,v 1.31 2013/01/28 19:30:13 rbj Exp $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

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
\section{INTRODUCTION}

Inductive definitions are so pervasive and diverse in logic, mathematics and computer science that it is doubtful that a comprehensive account could be given.
In this document I attempt to provide support for some kinds of inductive type definition commonly used in computing at the same time as facilitating various other kinds of inductive definition of sets which are relevant to my interests in set theory and foundational studies.
Some interest for me and perhaps some novelty for the reader may arise from the ecclectic mix of applications through which I have attempted to find common threads.

I began with a proof of the ``Knaster-Tarski'' theorem asserting that monotone functions over some power set have greatest and least fixed points, and this does provide at least one point common to all the material.

\subsection{Pre-Topologies, Closures and Interiors}

I'm groping here for the best language for describing what's going on.

It is natural to consider inductive definitions as arising from closures, and closure as a topological concept, though in fact the notion of closure is strictly broader than its use in topology.
I have adopted apparently topological terminology where that seems appropriate, primarily by taking ``open'' as a dual for ``closed'' even in our present non-topological context.
The kind of closure of interest here is strictly pre-topological, in the sense that these structures belong to a kind which is broader than the notion of topology (let's for the while call this a ``pre-topology''), and all the interesting cases from our present perspective are pre-topologies which are not actually topologies.

To make this explanation more informative let us chose a definition of pre-topology.
It won't do to generalise the idea of a topology as a set of open sets, because a pre-topology is not determined by its set of open sets.
What we do instead is generalise the notion of a limit to that of an operator, or the notion of a limit point to that of a point of closure.

Think of a topology as being determined by a (monotonic) function which maps each subset of some universe into its closure, i.e. the smallest enclosing set which contains all its limit points.
Such a map tells you what the open sets are (they are the complements of fixed points of the function), but not every such map determines a topology.
It will fail to do so if, as in all the cases of present interest, the empty set is not one of its fixed points.

This gives a generalised notion of open and closed, which is perhaps best spoken of by using ``closure point'' as a generalisation of ``limit point''.
A set is open if all its members are a among its closure points, and closed if it contains all its closure points.

In the pre-topologies of interest to us the empty set is never closed nor the universal set open.
There are really only two sets in a pre-topology which are of interest from our present point of view, the closure of the empty set, which is the set defined inductively by the pre-topology, and the interior of the universal set, which is the set defined co-inductively by the pre-topology.

Having thus explained our talk of closures and interiors, we will have no further use for the notion of a pre-topology, and will work only with sets of operators, which may be thought of as defining pre-topologies in relation to which talk of closures and interiors may be understood.

\subsection{Related Work}

For a general introduction to inductive definitions see Aczel \cite{aczel77}.

This work is conducted in a proof tool for higher order logic after the manner of LCF, and the literature concerning inductive definitions in similar contexts is therefore relevant.
Several papers by Larry Paulson fall into this category, for example \cite{paulson00}, in which may be found a more comprehensive guide to related work.
I am aware of having taken from Paulson the idea of using the Knaster-Tarski fixedpoint theorem, but it is probable that his contribution, direct or indirect, is pervasive.

The particular system I have used is {\Product}, in relation to which the problem of ``Free Types'' in the Z specification language is relevant, and is discussed by Rob Arthan in \cite{Arthan91c}.
So far however, the present work does not support any facilities specific to Z.

\subsection{Intended Applications}

Three kinds of application are approached:

\begin{enumerate}
\item support for defining (mutual) recursive datatypes where the character of the constructors is known but no particular types are known over which the constructions operate.
\item similar features for use in a context like set theory (in higher order logic) where it is essential to code up the constructors in that context (for example as required to prove Tarski's result about the definability of arithmetic or set theoretic truth in the languages of arithmetic or set theory).
\item support for a generalisation of what set theorists call ``Hereditarily P'' sets, i.e. sets which have property P all of whose members have property ``Hereditarily P''.
The generalisation is to allow the constituents which must have the property to be defined other than by plain membership, as for example, in the ``hereditarily pure functions'', even though the members of such a function are not themselves functions (because of the way functions are usually coded up in set theory).
In this case the relevant constutuents are the members of the domain and range of the function.
\end{enumerate}

\subsection{Formalities}

Create new theory ``fixp''.

=SML
open_theory "rbjmisc";
force_new_theory "fixp";
new_parent "U_orders";
new_parent "wf_relp";
(* new_parent "membership"; *)
force_new_pc ⦏"'fixp"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'fixp";
set_merge_pcs ["rbjmisc", "'fixp"];
=IGN
set_pc "rbjmisc";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℝ", "'savedthm_cs_∃_proof"];
set_flag ("pp_use_alias", false);
=TEX

\section{ORDERS AND BOUNDS}

We need to talk about greatest lower bounds etc.
This would have gone in ``ordered\_sets'' but it doesn't follow the general treatment their, so for the time being its here.

First lets say what a lower bound is:

ⓈHOLCONST
│ ⦏IsLb⦎ : ('a → 'a → BOOL) → 'a SET → 'a → BOOL
├───────────
│ ∀ r s e⦁ IsLb r s e = ∀x⦁ x ∈ s ⇒ r e x
■

ⓈHOLCONST
│ ⦏IsUb⦎ : ('a → 'a → BOOL) → 'a SET → 'a → BOOL
├───────────
│ ∀ r s e⦁ IsUb r s e = ∀x⦁ x ∈ s ⇒ r x e
■

Often the domain of our relations does not have a unique maximal element, and so there may be no greatest lower bound for the empty set.
However, this affects the applications rather than the concept:

ⓈHOLCONST
│ ⦏IsGlb⦎ : ('a → 'a → BOOL) → 'a SET → 'a → BOOL
├───────────
│ ∀ r s e⦁ IsGlb r s e ⇔ IsLb r s e ∧ ∀x⦁ IsLb r s x ⇒ r x e
■

ⓈHOLCONST
│ ⦏IsLub⦎ : ('a → 'a → BOOL) → 'a SET → 'a → BOOL
├───────────
│ ∀ r s e⦁ IsLub r s e ⇔ IsUb r s e ∧ ∀x⦁ IsUb r s x ⇒ r e x
■

ⓈHOLCONST
│ ⦏Lub⦎ : ('a → 'a → BOOL) → 'a SET → 'a
├───────────
│ ∀ r s⦁ Lub r s = εx⦁ IsLub r s x
■

ⓈHOLCONST
│ ⦏Glb⦎ : ('a → 'a → BOOL) → 'a SET → 'a
├───────────
│ ∀ r s⦁ Glb r s = εx⦁ IsGlb r s x
■

=GFT
⦏lub_unique_lemma⦎ =
   ⊢ ∀ X r x y⦁ Antisym (Universe, r) ⇒ IsLub r Y x ∧ IsLub r Y y ⇒ x = y

⦏lub_unique_lemma2⦎ =
   ⊢ ∀ X r x y
     ⦁ Antisym (X, r) ∧ x ∈ X ∧ y ∈ X ⇒ IsLub r X x ∧ IsLub r X y ⇒ x = y

⦏glb_unique_lemma⦎ =
   ⊢ ∀ X r x y⦁ Antisym (Universe, r) ⇒ IsGlb r X x ∧ IsGlb r X y ⇒ x = y

⦏glb_unique_lemma2⦎ =
   ⊢ ∀ X r x y
     ⦁ Antisym (X, r) ∧ x ∈ X ∧ y ∈ X ⇒ IsGlb r X x ∧ IsGlb r X y ⇒ x = y
=TEX

\ignore{
=SML
set_flag ("subgoal_package_quiet", true);

set_goal([], ⌜∀X r x y⦁ Antisym (Universe, r) ⇒ IsLub r X x ∧ IsLub r X y ⇒ x = y⌝);
a (rewrite_tac [get_spec ⌜IsLub⌝, get_spec ⌜Antisym⌝] THEN contr_tac);
a (REPEAT (asm_fc_tac[]));
val lub_unique_lemma = save_pop_thm "lub_unique_lemma";

set_goal([], ⌜∀X r x y⦁ Antisym (X, r) ∧ x ∈ X ∧ y ∈ X ⇒ IsLub r X x ∧ IsLub r X y ⇒ x = y⌝);
a (rewrite_tac [get_spec ⌜IsLub⌝, get_spec ⌜Antisym⌝] THEN contr_tac);
a (REPEAT (asm_fc_tac[]));
val lub_unique_lemma2 = save_pop_thm "lub_unique_lemma2";

set_goal([], ⌜∀X r x y⦁ Antisym (Universe, r) ⇒ IsGlb r X x ∧ IsGlb r X y ⇒ x = y⌝);
a (rewrite_tac [get_spec ⌜IsGlb⌝, get_spec ⌜Antisym⌝] THEN contr_tac);
a (REPEAT (asm_fc_tac[]));
val glb_unique_lemma = save_pop_thm "glb_unique_lemma";

set_goal([], ⌜∀X r x y⦁ Antisym (X, r) ∧ x ∈ X ∧ y ∈ X ⇒ IsGlb r X x ∧ IsGlb r X y ⇒ x = y⌝);
a (rewrite_tac [get_spec ⌜IsGlb⌝, get_spec ⌜Antisym⌝] THEN contr_tac);
a (REPEAT (asm_fc_tac[]));
val glb_unique_lemma2 = save_pop_thm "glb_unique_lemma2";
=TEX
}%ignore

=GFT
⦏isub_sub_lemma⦎ =
	⊢ ∀ X Y r y⦁ X ⊆ Y ∧ IsUb r Y y ⇒ IsUb r X y

⦏islb_sub_lemma⦎ =
	⊢ ∀ X Y r y⦁ X ⊆ Y ∧ IsLb r Y y ⇒ IsLb r X y

⦏isub_trans_lemma⦎ =
   ⊢ ∀ X r x y⦁ Trans (Universe, r) ∧ IsUb r X x ∧ r x y ⇒ IsUb r X y

⦏islb_trans_lemma⦎ =
   ⊢ ∀ X r x y⦁ Trans (Universe, r) ∧ IsLb r X y ∧ r x y ⇒ IsLb r X x

⦏islub_sub_lemma⦎ =
   ⊢ ∀ X Y r x y⦁ X ⊆ Y ∧ IsLub r X x ∧ IsLub r Y y ⇒ r x y

⦏isglb_sub_lemma⦎ =
   ⊢ ∀ X Y r x y⦁ X ⊆ Y ∧ IsGlb r X x ∧ IsGlb r Y y ⇒ r y x
=TEX

\ignore{
=SML
set_goal([], ⌜∀(X:'a ℙ) Y r y⦁ X ⊆ Y ∧ IsUb r Y y ⇒ IsUb r X y⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜IsUb⌝] THEN REPEAT strip_tac);
a (PC_T1 "hol1" asm_prove_tac[]);
val isub_sub_lemma = save_pop_thm "isub_sub_lemma";

set_goal([], ⌜∀(X:'a ℙ) Y r y⦁ X ⊆ Y ∧ IsLb r Y y ⇒ IsLb r X y⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜IsLb⌝] THEN REPEAT strip_tac);
a (PC_T1 "hol1" asm_prove_tac[]);
val islb_sub_lemma = save_pop_thm "islb_sub_lemma";

set_goal([], ⌜∀X r x y⦁ Trans (Universe, r) ∧ IsUb r X x ∧ r x y ⇒ IsUb r X y⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜IsUb⌝, get_spec ⌜Trans⌝] THEN REPEAT strip_tac);
a (REPEAT (all_asm_fc_tac[]));
val isub_trans_lemma = save_pop_thm "isub_trans_lemma";

set_goal([], ⌜∀X r x y⦁ Trans (Universe, r) ∧ IsLb r X y ∧ r x y ⇒ IsLb r X x⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜IsLb⌝, get_spec ⌜Trans⌝] THEN REPEAT strip_tac);
a (REPEAT (all_asm_fc_tac[]));
val islb_trans_lemma = save_pop_thm "islb_trans_lemma";

set_goal([], ⌜∀(X:'a ℙ) Y r x y⦁ X ⊆ Y ∧ IsLub r X x ∧ IsLub r Y y ⇒ r x y⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜IsLub⌝] THEN REPEAT strip_tac);
a (all_fc_tac [isub_sub_lemma]);
a (all_asm_fc_tac[]);
val islub_sub_lemma = save_pop_thm "islub_sub_lemma";

set_goal([], ⌜∀(X:'a ℙ) Y r x y⦁ X ⊆ Y ∧ IsGlb r X x ∧ IsGlb r Y y ⇒ r y x⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜IsGlb⌝] THEN REPEAT strip_tac);
a (all_fc_tac [islb_sub_lemma]);
a (all_asm_fc_tac[]);
val isglb_sub_lemma = save_pop_thm "isglb_sub_lemma";
=TEX
}%ignore


=GFT
⦏lub_lub_lemma⦎ =
   ⊢ ∀X r⦁ (∃z⦁ IsLub r X z) ⇒ IsLub r X (Lub r X)

⦏glb_glb_lemma⦎ =
   ⊢ ∀X r⦁ (∃z⦁ IsGlb r X z) ⇒ IsGlb r X (Glb r X)
=TEX

=GFT
⦏isglb_glb_lemma⦎ =
   ⊢ ∀ X r z⦁ Antisym (Universe, r) ⇒ IsGlb r X z ⇒ Glb r X = z

⦏isglb_lub_lemma⦎ =
   ⊢ ∀ X r z⦁ Antisym (Universe, r) ⇒ IsLub r X z ⇒ Lub r X = z
=TEX

\ignore{
=SML
set_goal([], ⌜∀X r⦁ (∃z⦁ IsLub r X z) ⇒ IsLub r X (Lub r X)⌝);
a (rewrite_tac[get_spec ⌜Lub⌝] THEN REPEAT strip_tac);
a (ε_tac ⌜ε x⦁ IsLub r X x⌝);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
val lub_lub_lemma = save_pop_thm "lub_lub_lemma";

set_goal([], ⌜∀X r⦁ (∃z⦁ IsGlb r X z) ⇒ IsGlb r X (Glb r X)⌝);
a (rewrite_tac[get_spec ⌜Glb⌝] THEN REPEAT strip_tac);
a (ε_tac ⌜ε x⦁ IsGlb r X x⌝);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
val glb_glb_lemma = save_pop_thm "glb_glb_lemma";

set_goal([], ⌜∀X r z⦁ Antisym (Universe, r) ⇒ IsGlb r X z ⇒ Glb r X = z⌝);
a (rewrite_tac[get_spec ⌜Glb⌝] THEN REPEAT strip_tac);
a (ε_tac ⌜ε x⦁ IsGlb r X x⌝);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
a (all_fc_tac [glb_unique_lemma]);
val isglb_glb_lemma = save_pop_thm "isglb_glb_lemma";

set_goal([], ⌜∀X r z⦁ Antisym (Universe, r) ⇒ IsLub r X z ⇒ Lub r X = z⌝);
a (rewrite_tac[get_spec ⌜Lub⌝] THEN REPEAT strip_tac);
a (ε_tac ⌜ε x⦁ IsLub r X x⌝);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
a (all_fc_tac [lub_unique_lemma]);
val islub_lub_lemma = save_pop_thm "islub_lub_lemma";
=TEX
}%ignore

=GFT
⦏ub_ub_lemma1⦎ =
	⊢ ∀ r X y⦁ IsUb r X y ⇒ (∀ x⦁ x ∈ X ⇒ r x y)

⦏lub_ub_lemma1⦎ =
	⊢ ∀ r X y⦁ IsLub r X y ⇒ (∀ x⦁ x ∈ X ⇒ r x y)

⦏lb_lb_lemma1⦎ =
	⊢ ∀ r X y⦁ IsLb r X y ⇒ (∀ x⦁ x ∈ X ⇒ r y x)

⦏glb_lb_lemma1⦎ =
	⊢ ∀ r X y⦁ IsGlb r X y ⇒ (∀ x⦁ x ∈ X ⇒ r y x)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r X y⦁ IsUb r X y ⇒ ∀x⦁ x ∈ X ⇒ r x y⌝);
a (REPEAT strip_tac THEN fc_tac [get_spec ⌜IsUb⌝]);
a (all_asm_fc_tac[get_spec ⌜IsUb⌝]);
val ub_ub_lemma1 = save_pop_thm "ub_ub_lemma1";

set_goal([], ⌜∀r X y⦁ IsLub r X y ⇒ ∀x⦁ x ∈ X ⇒ r x y⌝);
a (REPEAT strip_tac THEN fc_tac [get_spec ⌜IsLub⌝]);
a (all_asm_fc_tac[get_spec ⌜IsUb⌝]);
val lub_ub_lemma1 = save_pop_thm "lub_ub_lemma1";

set_goal([], ⌜∀r X y⦁ IsLb r X y ⇒ ∀x⦁ x ∈ X ⇒ r y x⌝);
a (REPEAT strip_tac THEN fc_tac [get_spec ⌜IsLb⌝]);
a (all_asm_fc_tac[get_spec ⌜IsLb⌝]);
val lb_lb_lemma1 = save_pop_thm "lb_lb_lemma1";

set_goal([], ⌜∀r X y⦁ IsGlb r X y ⇒ ∀x⦁ x ∈ X ⇒ r y x⌝);
a (REPEAT strip_tac THEN fc_tac [get_spec ⌜IsGlb⌝]);
a (all_asm_fc_tac[get_spec ⌜IsLb⌝]);
val glb_lb_lemma1 = save_pop_thm "glb_lb_lemma1";
=TEX
}%ignore

=GFT
⦏lin_refl_lub_lemma⦎ =
   ⊢ ∀ r X s l
     ⦁ LinearOrder (X, r) ∧ Refl (X, r) ∧ s ⊆ X ∧ l ∈ X ∧ IsLub r s l
         ⇒ (∀ y⦁ y ∈ X ∧ r y l ∧ ¬ r l y ⇒ (∃ z⦁ z ∈ s ∧ r y z))
=TEX

\ignore{
=SML
set_goal([], ⌜∀r X s l⦁ LinearOrder (X, r) ∧ Refl (X, r) ∧ s ⊆ X ∧ l ∈ X ∧ IsLub r s l
		⇒ ∀y⦁ y ∈ X ∧ r y l ∧ ¬ r l y ⇒ ∃ z⦁ z ∈ s ∧ r y z⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜IsLub⌝] THEN REPEAT strip_tac);
a (lemma_tac ⌜¬ IsUb r s y⌝ THEN1 (contr_tac THEN all_asm_fc_tac[]));
a (POP_ASM_T (strip_asm_tac o (rewrite_rule [get_spec ⌜IsUb⌝])));
a (fc_tac [get_spec ⌜LinearOrder⌝]);
a (fc_tac [get_spec ⌜Trich⌝]);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
a (lemma_tac ⌜x ∈ X⌝ THEN1 PC_T1 "hol1" asm_prove_tac[]);
a (contr_tac THEN list_spec_nth_asm_tac 3 [⌜x⌝, ⌜y⌝]);
a (var_elim_asm_tac ⌜x = y⌝ THEN fc_tac [get_spec ⌜Refl⌝] THEN all_asm_fc_tac[]);
val lin_refl_lub_lemma = save_pop_thm "lin_refl_lub_lemma";
=TEX
}%ignore


ⓈHOLCONST
│ ⦏NeGlbsExist⦎ : ('a → 'a → BOOL) → BOOL
├───────────
│ ∀ r⦁ NeGlbsExist r ⇔ ∀s⦁ (∃d⦁ d ∈ s) ⇒ ∃e⦁ IsGlb r s e
■

ⓈHOLCONST
│ ⦏GlbsExist⦎ : ('a → 'a → BOOL) → BOOL
├───────────
│ ∀ r⦁ GlbsExist r ⇔ ∀s⦁ ∃e⦁ IsGlb r s e
■

ⓈHOLCONST
│ ⦏LubsExist⦎ : ('a → 'a → BOOL) → BOOL
├───────────
│ ∀ r⦁ LubsExist r ⇔ ∀s⦁ ∃e⦁ IsLub r s e
■

=GFT
⦏lub_lub_lemma2⦎ =
   ⊢ ∀ r X⦁ LubsExist r ⇒ IsLub r X (Lub r X)

⦏glb_glb_lemma2⦎ =
   ⊢ ∀ r X⦁ GlbsExist r ⇒ IsGlb r X (Glb r X)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r X⦁ LubsExist r ⇒ IsLub r X (Lub r X)⌝);
a (rewrite_tac[get_spec ⌜LubsExist⌝]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜X⌝);
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜r⌝] lub_lub_lemma));
a (asm_fc_tac[]);
val lub_lub_lemma2 = save_pop_thm "lub_lub_lemma2";

set_goal([], ⌜∀r X⦁ GlbsExist r ⇒ IsGlb r X (Glb r X)⌝);
a (rewrite_tac[get_spec ⌜GlbsExist⌝]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜X⌝);
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜r⌝] glb_glb_lemma));
a (asm_fc_tac[]);
val glb_glb_lemma2 = save_pop_thm "glb_glb_lemma2";
=TEX
}%ignore

=GFT
⦏less_lub_lemma⦎ =
	⊢ ∀ r⦁ LubsExist r ⇒ (∀ x X⦁ x ∈ X ⇒ r x (Lub r X))
⦏gt_glb_lemma⦎ =
	⊢ ∀ r⦁ GlbsExist r ⇒ (∀ x X⦁ x ∈ X ⇒ r (Glb r X) x)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ LubsExist r ⇒ ∀x X⦁ x ∈ X ⇒ r x (Lub r X)⌝);
a (REPEAT strip_tac THEN fc_tac [lub_lub_lemma2]);
a (ufc_tac [lub_ub_lemma1]);
a (asm_fc_tac[]);
val less_lub_lemma = save_pop_thm "less_lub_lemma";

set_goal([], ⌜∀r⦁ GlbsExist r ⇒ ∀x X⦁ x ∈ X ⇒ r (Glb r X) x⌝);
a (REPEAT strip_tac THEN fc_tac [glb_glb_lemma2]);
a (ufc_tac [glb_lb_lemma1]);
a (asm_fc_tac[]);
val gt_glb_lemma = save_pop_thm "gt_glb_lemma";
=TEX
}%ignore

=GFT
⦏lub_sub_lemma⦎ =
   ⊢ ∀ r⦁ LubsExist r ⇒ (∀ X Y⦁ X ⊆ Y ⇒ r (Lub r X) (Lub r Y))

⦏glb_sub_lemma⦎ =
   ⊢ ∀ r⦁ GlbsExist r ⇒ (∀ X Y⦁ X ⊆ Y ⇒ r (Glb r Y) (Glb r X))
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ LubsExist r ⇒ ∀(X:'a ℙ) Y⦁ X ⊆ Y ⇒ r (Lub r X) (Lub r Y)⌝);
a (REPEAT strip_tac THEN fc_tac [lub_lub_lemma2]);
a (ufc_tac [get_spec ⌜IsLub⌝]);
a (lemma_tac ⌜IsUb r X (Lub r Y)⌝
	THEN1 (rewrite_tac [get_spec ⌜IsUb⌝]
		THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (GET_NTH_ASM_T 5 (PC_T1 "hol1" strip_asm_tac));
a (asm_fc_tac[]);
a (fc_tac [less_lub_lemma]);
a (list_spec_nth_asm_tac 1 [⌜x⌝, ⌜Y⌝]);
(* *** Goal "2" *** *)
a (asm_fc_tac[]);
val lub_sub_lemma = save_pop_thm "lub_sub_lemma";

set_goal([], ⌜∀r⦁ GlbsExist r ⇒ ∀(X:'a ℙ) Y⦁ X ⊆ Y ⇒ r (Glb r Y) (Glb r X)⌝);
a (REPEAT strip_tac THEN fc_tac [glb_glb_lemma2]);
a (ufc_tac [get_spec ⌜IsGlb⌝]);
a (lemma_tac ⌜IsLb r X (Glb r Y)⌝
	THEN1 (rewrite_tac [get_spec ⌜IsLb⌝]
		THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (GET_NTH_ASM_T 5 (PC_T1 "hol1" strip_asm_tac));
a (asm_fc_tac[]);
a (fc_tac [gt_glb_lemma]);
a (list_spec_nth_asm_tac 1 [⌜x⌝, ⌜Y⌝]);
(* *** Goal "2" *** *)
a (asm_fc_tac[]);
val glb_sub_lemma = save_pop_thm "glb_sub_lemma";
=TEX
}%ignore

=GFT
⦏le_islub_lub_lemma⦎ =
   ⊢ ∀ r⦁ LubsExist r ⇒ (∀ X⦁ IsLub r X (Lub r X))

⦏ge_isglb_glb_lemma⦎ =
   ⊢ ∀ r⦁ GlbsExist r ⇒ (∀ X⦁ IsGlb r X (Glb r X))
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ LubsExist r ⇒ ∀X⦁ IsLub r X (Lub r X)⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜LubsExist⌝]);
a (spec_nth_asm_tac 1 ⌜X⌝);
a (fc_tac [lub_lub_lemma]);
val le_islub_lub_lemma = save_pop_thm "le_islub_lub_lemma";

set_goal([], ⌜∀r⦁ GlbsExist r ⇒ ∀X⦁ IsGlb r X (Glb r X)⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜GlbsExist⌝]);
a (spec_nth_asm_tac 1 ⌜X⌝);
a (fc_tac [glb_glb_lemma]);
val ge_isglb_glb_lemma = save_pop_thm "ge_isglb_glb_lemma";
=TEX
}%ignore

=GFT
⦏lea_islub_lub_lemma⦎ =
   ⊢ ∀ r
     ⦁ LubsExist r ∧ Antisym (Universe, r)
         ⇒ (∀ X x⦁ IsLub r X x = Lub r X = x)

⦏gea_isglb_glb_lemma⦎ =
   ⊢ ∀ r
     ⦁ GlbsExist r ∧ Antisym (Universe, r)
         ⇒ (∀ X x⦁ IsGlb r X x = Glb r X = x)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ LubsExist r ∧ Antisym (Universe, r) ⇒ ∀X x⦁ IsLub r X x ⇔ Lub r X = x⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [le_islub_lub_lemma]);
a (all_ufc_tac [lub_unique_lemma]);
(* *** Goal "2" *** *)
a (SYM_ASMS_T rewrite_tac THEN fc_tac [le_islub_lub_lemma]);
a (asm_rewrite_tac[]);
val lea_islub_lub_lemma = save_pop_thm "lea_islub_lub_lemma";

set_goal([], ⌜∀r⦁ GlbsExist r ∧ Antisym (Universe, r) ⇒ ∀X x⦁ IsGlb r X x ⇔ Glb r X = x⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [ge_isglb_glb_lemma]);
a (all_ufc_tac [glb_unique_lemma]);
(* *** Goal "2" *** *)
a (SYM_ASMS_T rewrite_tac THEN fc_tac [ge_isglb_glb_lemma]);
a (asm_rewrite_tac[]);
val gea_isglb_glb_lemma = save_pop_thm "gea_isglb_glb_lemma";
=TEX
}%ignore

\section{FIXED POINTS}

The general scheme involves finding closures of sets under varieties of operators.
The operators take members or sets of members of elements of the set in question, and construct new values from them.
Taking the closure of such a set under certain operations involves adding the things which can be constructed from elements in the set to the set untill there are no longer any new values which can be constructed.

In seeking to provide general support for such closure operations in a typed framework the diversity of the possible operations is an issue.
For this reason, in addressing the fundamental problem for finding the required closure it is supposed that the operations over elements in the sets which are of interest have been compounded into a monotonic operator operating on a set and yeilding that same set augmented by the elements which can be constructed from them.

In the present type-theoretic context such an operator is always monotonic and unbounded, and therefore by the Knaster-Tarski fixedpoint theorem will have at least one fixed point.

In this section we prove the fixedpoint theorem and spin out some elementary consequences.

For reasons connected with the motivation of this work, the emphasis is on taking closures, and the concept of closure is made prominent.
There is a dual system of terminology, at least insofar the dual of induction is called ``co-induction'' and though I am not strongly motivated by the aplications of the dual system, there is so little extra work in providing both that I have systematically done so, in the hope that applications may become apparent.
In doing so I have used a "co" prefix whenever I know of no other terminology for the dual of a concept.

\subsection{Monotonicity, Closure and Interior}

Definition of the notion of a function over a powerset monotonic with respect to set inclusion.
The Knaster-Tarski fixed point theorem applies to bounded monotonic functions, when considering only HOL ``SET''s, as we do here, the boundedness condition is automatically satisfied.

ⓈHOLCONST
│ ⦏Monotonic⦎ : ('a SET → 'b SET) → BOOL
├
│ ∀f⦁ Monotonic f ⇔ ∀x y⦁ x ⊆ y ⇒ f(x) ⊆ f(y)
■

=SML
declare_infix (300, "ClosedUnder");
declare_infix (300, "OpenUnder");
=TEX

ⓈHOLCONST
│ $⦏ClosedUnder⦎ : 'a SET → ('a SET → 'a SET) → BOOL
├
│ ∀f X⦁ X ClosedUnder f ⇔ f(X) ⊆ X
■

ⓈHOLCONST
│ $⦏OpenUnder⦎ : 'a SET → ('a SET → 'a SET) → BOOL
├
│ ∀f X⦁ X OpenUnder f ⇔ X ⊆ f(X)
■

It would be possible here to provide an induction principle based on the well-founded ordering by rank, in which the rank is the number of iteration of f starting with the empty set necessary to reach the element in question.
However, I'm not convinved that this would be useful.
Induction principles derived from more specific features of particular constructions are likely to be more useful in practice.
I shall therefore hold off attemping such principles unless I find a need for them.

\ignore{
=SML
val Monotonic_def = get_spec ⌜Monotonic⌝;
val ClosedUnder_def = get_spec ⌜$ClosedUnder⌝;
val OpenUnder_def = get_spec ⌜$OpenUnder⌝;
=IGN
push_pc "hol1";
pop_pc();

set_goal([], ⌜∀ h⦁ Monotonic h ⇒ ∀s⦁ (∀t⦁ t ⊂ s ⇒ h t ⊆ s) ⇒ s ClosedUnder h⌝);
a (REPEAT strip_tac THEN rewrite_tac[ClosedUnder_def]);
a (fc_tac[Monotonic_def]);
a (PC_T1 "hol1" rewrite_tac[] THEN contr_tac);
a (lemma_tac ⌜∃t⦁ t = s \ {x}⌝ THEN1 prove_∃_tac);
a (lemma_tac ⌜s ⊂ h s⌝ THEN1 (PC_T1 "hol1" asm_rewrite_tac[] THEN REPEAT strip_tac));
(* *** Goal "1" *** *)

a (PC_T1 "hol1" (spec_nth_asm_tac 4) ⌜t⌝);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜x⌝);

=TEX
}%ignore

\subsection{Least and Greatest Fixed Points}

Now we define the conditions for being a least fixed point.

ⓈHOLCONST
│ ⦏IsLfp⦎ : ('a → 'a → BOOL) → ('a → 'a) → 'a → BOOL
├───────────
│ ∀ r f e⦁ IsLfp r f e ⇔
│	let fp = {x | f x = x}
│	in e ∈ fp ∧ IsGlb r fp e
■

ⓈHOLCONST
│ ⦏IsGfp⦎ : ('a → 'a → BOOL) → ('a → 'a) → 'a → BOOL
├───────────
│ ∀ r f e⦁ IsGfp r f e ⇔
│	let fp = {x | f x = x}
│	in e ∈ fp ∧ IsLub r fp e
■

=GFT
⦏islfp_lemma1⦎ =
	⊢ ∀ r f e⦁ IsLfp r f e ⇒ e = f e ∧ (∀ x⦁ x = f x ⇒ r e x)

⦏isgfp_lemma1⦎ =
	⊢ ∀ r f e⦁ IsGfp r f e ⇒ e = f e ∧ (∀ x⦁ x = f x ⇒ r x e)

⦏islfp_lemma2⦎ =
	⊢ ∀ r f e⦁ IsLfp r f e ⇒ f e = e ∧ (∀ x⦁ f x = x ⇒ r e x)

⦏isgfp_lemma2⦎ =
	⊢ ∀ r f e⦁ IsGfp r f e ⇒ f e = e ∧ (∀ x⦁ f x = x ⇒ r x e)

⦏islfp_unique_lemma⦎ =
	⊢ ∀ r f e d⦁ Antisym (Universe, r) ∧ IsLfp r f e ∧ IsLfp r f d ⇒ e = d

⦏isgfp_unique_lemma⦎ =
   ⊢ ∀ r f e d⦁ Antisym (Universe, r) ∧ IsGfp r f e ∧ IsGfp r f d ⇒ e = d
=TEX

\ignore{
=SML
set_goal([], ⌜∀r f e⦁ IsLfp r f e ⇒ e = f e
	∧ (∀x⦁ x = f x ⇒ r e x)⌝);
a (rewrite_tac [get_spec ⌜IsLfp⌝, let_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [get_spec ⌜IsGlb⌝]);
a (fc_tac [get_spec ⌜IsLb⌝]);
a (DROP_NTH_ASM_T 4 (asm_tac o (conv_rule eq_sym_conv)));
a (asm_fc_tac[]);
val islfp_lemma1 = save_pop_thm "islfp_lemma1";

set_goal([], ⌜∀r f e⦁ IsGfp r f e ⇒ e = f e
	∧ (∀x⦁ x = f x ⇒ r x e)⌝);
a (rewrite_tac [get_spec ⌜IsGfp⌝, let_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [get_spec ⌜IsLub⌝]);
a (fc_tac [get_spec ⌜IsUb⌝]);
a (DROP_NTH_ASM_T 4 (asm_tac o (conv_rule eq_sym_conv)));
a (asm_fc_tac[]);
val isgfp_lemma1 = save_pop_thm "isgfp_lemma1";

set_goal([], ⌜∀r f e⦁ IsLfp r f e ⇒ f e = e
	∧ (∀x⦁ f x = x⇒ r e x)⌝);
a (rewrite_tac [get_spec ⌜IsLfp⌝, let_def]
	THEN REPEAT strip_tac);
a (fc_tac [get_spec ⌜IsGlb⌝]);
a (fc_tac [get_spec ⌜IsLb⌝]);
a (all_asm_ante_tac THEN rewrite_tac[] THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
val islfp_lemma2 = save_pop_thm "islfp_lemma2";

set_goal([], ⌜∀r f e⦁ IsGfp r f e ⇒ f e = e
	∧ (∀x⦁ f x = x ⇒ r x e)⌝);
a (rewrite_tac [get_spec ⌜IsGfp⌝, let_def]
	THEN REPEAT strip_tac);
a (fc_tac [get_spec ⌜IsLub⌝]);
a (fc_tac [get_spec ⌜IsUb⌝]);
a (all_asm_ante_tac THEN rewrite_tac[] THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
val isgfp_lemma2 = save_pop_thm "isgfp_lemma2";

set_goal([], ⌜∀r f e d⦁ Antisym (Universe, r) ∧ IsLfp r f e ∧ IsLfp r f d ⇒ e = d⌝);
a (REPEAT strip_tac THEN fc_tac [islfp_lemma1, get_spec ⌜Antisym⌝]);
a (DROP_NTH_ASM_T 5 ante_tac THEN rewrite_tac [] THEN contr_tac);
a (all_asm_fc_tac[]);
a (all_asm_fc_tac[]);
val islfp_unique_lemma = pop_thm();

set_goal([], ⌜∀r f e d⦁ Antisym (Universe, r) ∧ IsGfp r f e ∧ IsGfp r f d ⇒ e = d⌝);
a (REPEAT strip_tac THEN fc_tac [isgfp_lemma1, get_spec ⌜Antisym⌝]);
a (DROP_NTH_ASM_T 5 ante_tac THEN rewrite_tac [] THEN contr_tac);
a (all_asm_fc_tac[]);
a (all_asm_fc_tac[]);
val isgfp_unique_lemma = pop_thm();
=TEX
}%ignore


ⓈHOLCONST
│ ⦏Lfp⦎ : ('a SET → 'a SET) → 'a SET
├
│ ∀f⦁ Lfp f = ⋂{X | X ClosedUnder f}
■

{\it Lfp} gives a fixed point:
=GFT
⦏lfp_fixedpoint_thm⦎ =
	⊢ ∀h⦁ Monotonic h ⇒ h (Lfp h) = Lfp h
=TEX

\ignore{
=SML
val Lfp_def = get_spec ⌜Lfp⌝;

set_goal([],⌜∀h⦁ Monotonic h ⇒ h (Lfp h) = Lfp h⌝);
a (rewrite_tac [ClosedUnder_def, Lfp_def] THEN REPEAT strip_tac);
a (lemma_tac ⌜h(⋂{X|h X ⊆ X}) ⊆ ⋂{X|h X ⊆ X}⌝);
(* *** Goal "1" *** *)
a (once_rewrite_tac[sets_ext_clauses] THEN REPEAT strip_tac);
a (lemma_tac ⌜(⋂{X|h X ⊆ X}) ⊆ s⌝);
(* *** Goal "1.1" *** *)
a (once_rewrite_tac[sets_ext_clauses] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜s⌝);
(* *** Goal "1.2" *** *)
a (all_asm_fc_tac [Monotonic_def]);
a (all_fc_tac[get_spec ⌜$⊆⌝]);
a (all_fc_tac[get_spec ⌜$⊆⌝]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜⋂{X|h X ⊆ X} ⊆ h(⋂{X|h X ⊆ X})⌝);
(* *** Goal "2.1" *** *)
a (once_rewrite_tac[sets_ext_clauses]);
a (REPEAT strip_tac);
a (spec_asm_tac ⌜∀ s⦁ s ∈ {X|h X ⊆ X} ⇒ x ∈ s⌝ ⌜h (⋂ {X|h X ⊆ X})⌝);
a (fc_tac [Monotonic_def]);
a (list_spec_asm_tac ⌜∀ x y⦁ x ⊆ y ⇒ h x ⊆ h y⌝ [⌜h(⋂ {X|h X ⊆ X})⌝, ⌜⋂ {X|h X ⊆ X}⌝]);
(* *** Goal "2.2" *** *)
a (all_asm_fc_tac [pc_rule "sets_ext" (prove_rule []) ⌜∀A B⦁ A ⊆ B ∧ B ⊆ A ⇒ A = B⌝]);
val lfp_fixedpoint_thm = save_pop_thm "lfp_fixedpoint_thm";
=TEX
}%ignore

{\it Lfp} gives the least fixed point:
=GFT
⦏Lfp_lfp_thm⦎ =
	⊢ ∀h⦁ Monotonic h ⇒ ∀g⦁ h g = g ⇒ (Lfp h) ⊆ g
=TEX

\ignore{
=SML
set_goal([],⌜∀h⦁ Monotonic h ⇒ ∀g⦁ h g = g ⇒ (Lfp h) ⊆ g⌝);
a (rewrite_tac [Lfp_def, ClosedUnder_def] THEN REPEAT strip_tac);
a (once_rewrite_tac [sets_ext_clauses]
	THEN REPEAT strip_tac);
a (spec_asm_tac ⌜∀ s⦁ s ∈ {X|h X ⊆ X} ⇒ x ∈ s⌝ ⌜g⌝);
a (DROP_ASM_T ⌜¬ h g ⊆ g⌝ ante_tac THEN asm_rewrite_tac []);
val Lfp_lfp_thm = save_pop_thm "Lfp_lfp_thm";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Gfp⦎ : ('a SET → 'a SET) → 'a SET
├
│ ∀f⦁ Gfp f = ⋃{X | X OpenUnder f}
■

{\it Gfp} gives a fixed point:
=GFT
⦏gfp_fixedpoint_thm⦎
	⊢ ∀h⦁ Monotonic h ⇒ h (Gfp h) = Gfp h
=TEX

\ignore{
=SML
val gfp_def = get_spec ⌜Gfp⌝;
set_goal([],⌜∀h⦁ Monotonic h ⇒ h (Gfp h) = Gfp h⌝);
a (rewrite_tac [gfp_def, OpenUnder_def] THEN REPEAT strip_tac);
a (lemma_tac ⌜⋃ {X|X ⊆ h X} ⊆ h (⋃ {X|X ⊆ h X})⌝);
(* *** Goal "1" *** *)
a (once_rewrite_tac[sets_ext_clauses] THEN REPEAT strip_tac);
a (lemma_tac ⌜s ⊆ ⋃ {X|X ⊆ h X}⌝);
(* *** Goal "1.1" *** *)
a (once_rewrite_tac[sets_ext_clauses] THEN REPEAT strip_tac);
a (∃_tac ⌜s⌝ THEN REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a (lemma_tac ⌜s ∈ {X|X ⊆ h X}⌝);
(* *** Goal "1.1" *** *)
a (once_rewrite_tac[sets_ext_clauses] THEN REPEAT strip_tac);
a (all_asm_fc_tac [Monotonic_def]);
a (all_asm_fc_tac [get_spec ⌜$⊆⌝]);
a (all_asm_fc_tac [get_spec ⌜$⊆⌝]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜h (⋃ {X|X ⊆ h X}) ∈ {X|X ⊆ h X}⌝);
(* *** Goal "2.1" *** *)
a (all_asm_fc_tac [Monotonic_def]);
a (asm_rewrite_tac [∈_in_clauses]);
(* *** Goal "2.2" *** *)
a (lemma_tac ⌜h (⋃ {X|X ⊆ h X}) ⊆ ⋃ {X|X ⊆ h X}⌝);
(* *** Goal "2.2.1" *** *)
a (once_rewrite_tac [sets_ext_clauses]);
a (REPEAT strip_tac);
a (∃_tac ⌜h (⋃ {X|X ⊆ h X})⌝);
a (REPEAT strip_tac);
(* *** Goal "2.2.2" *** *)
a (rewrite_tac [pc_rule "sets_ext" (prove_rule []) ⌜∀A B⦁ A = B ⇔ B ⊆ A ∧ A ⊆ B⌝]
	THEN asm_rewrite_tac[]);
val gfp_fixedpoint_thm = save_pop_thm "gfp_fixedpoint_thm";
=TEX
}%ignore

Gfp gives the greatest fixed point:

=GFT
⦏gfp_gfp_thm⦎ =
	⊢ ∀h⦁ Monotonic h ⇒ ∀g⦁ h g = g ⇒ g ⊆ (Gfp h)
=TEX

\ignore{
=SML
set_goal([],⌜∀h⦁ Monotonic h ⇒ ∀g⦁ h g = g ⇒ g ⊆ (Gfp h)⌝);
a (rewrite_tac [gfp_def, OpenUnder_def] THEN REPEAT strip_tac);
a (once_rewrite_tac [sets_ext_clauses]
	THEN REPEAT strip_tac);
a (∃_tac ⌜g⌝ THEN asm_rewrite_tac[]);
val gfp_gfp_thm = save_pop_thm "gfp_gfp_thm";
=TEX
}%ignore

\subsection{Closure and Interior}

=GFT
⦏lfp_closed_thm⦎ =
	⊢ ∀h⦁ Monotonic h ⇒ (Lfp h) ClosedUnder h

⦏lfp_closed_thm1⦎ =
	⊢ ∀ h⦁ Monotonic h ⇒ (∀ x⦁ x ∈ h (Lfp h) ⇒ x ∈ Lfp h)

⦏lfp_open_thm⦎ =
	⊢ ∀h⦁ Monotonic h ⇒ (Lfp h) OpenUnder h

⦏lfp_open_thm1⦎ =
	⊢ ∀ h⦁ Monotonic h ⇒ (∀ x⦁ x ∈ Lfp h ⇒ x ∈ h (Lfp h))
=TEX

\ignore{
=SML
set_goal([],⌜∀h⦁ Monotonic h ⇒ (Lfp h) ClosedUnder h⌝);
a (rewrite_tac [ClosedUnder_def] THEN REPEAT strip_tac);
a (fc_tac [lfp_fixedpoint_thm]
	THEN asm_rewrite_tac[]);
val lfp_closed_thm = save_pop_thm "lfp_closed_thm";
val lfp_closed_thm1 = save_thm ("lfp_closed_thm1",
	rewrite_rule [ClosedUnder_def, sets_ext_clauses] lfp_closed_thm);

set_goal([],⌜∀h⦁ Monotonic h ⇒ (Lfp h) OpenUnder h⌝);
a (rewrite_tac [OpenUnder_def] THEN REPEAT strip_tac);
a (fc_tac [lfp_fixedpoint_thm]
	THEN asm_rewrite_tac[]);
val lfp_open_thm = save_pop_thm "lfp_open_thm";
val lfp_open_thm1 = save_thm ("lfp_open_thm1",
	rewrite_rule [OpenUnder_def, sets_ext_clauses] lfp_open_thm);
=TEX
}%ignore

=GFT
⦏gfp_closed_thm⦎ =
	⊢ ∀h⦁ Monotonic h ⇒ (Gfp h) ClosedUnder h
⦏gfp_closed_thm1⦎ =
	⊢ ∀ h⦁ Monotonic h ⇒ (∀ x⦁ x ∈ h (Gfp h) ⇒ x ∈ Gfp h)
⦏gfp_open_thm⦎ =
	⊢ ∀h⦁ Monotonic h ⇒ (Gfp h) OpenUnder h
⦏gfp_open_thm1⦎ =
	⊢ ∀ h⦁ Monotonic h ⇒ (∀ x⦁ x ∈ Gfp h ⇒ x ∈ h (Gfp h))
=TEX

\ignore{
=SML
set_goal([],⌜∀h⦁ Monotonic h ⇒ (Gfp h) ClosedUnder h⌝);
a (rewrite_tac [ClosedUnder_def] THEN REPEAT strip_tac);
a (fc_tac [gfp_fixedpoint_thm]
	THEN asm_rewrite_tac[]);
val gfp_closed_thm = save_pop_thm "gfp_closed_thm";
val gfp_closed_thm1 = save_thm ("gfp_closed_thm1",
	rewrite_rule [ClosedUnder_def, sets_ext_clauses] gfp_closed_thm);

set_goal([],⌜∀h⦁ Monotonic h ⇒ (Gfp h) OpenUnder h⌝);
a (rewrite_tac [OpenUnder_def] THEN REPEAT strip_tac);
a (fc_tac [gfp_fixedpoint_thm]
	THEN asm_rewrite_tac[]);
val gfp_open_thm = save_pop_thm "gfp_open_thm";
val gfp_open_thm1 = save_thm ("gfp_open_thm1",
	rewrite_rule [OpenUnder_def, sets_ext_clauses] gfp_open_thm);
=TEX
}%ignore

\subsection{Induction and Co-induction}

To prove something about the members of an inductively defined set you prove that all the operations which were used to define the set preserve the required property.
In our case, where the operator is defined over sets of elements and we think of ourselves as starting out with the empty set, there is no ``base case'' for the induction
(alternatively think of the base case as the application of the operator to the empty set).

For some property represented as a set {\it s} and a set of constructors represented as a function {\it h} the induction principle states that if the property is closed under the function then all the elements of the set inductively defined by the function (e.g. its least fixed point) have the property.

The least fixed point induction principle may therefore be expressed:


\ignore{
=SML
set_goal([],⌜∀h⦁ Monotonic h ⇒ ∀s⦁ s ClosedUnder h ⇒ (Lfp h) ⊆ s⌝);
a (rewrite_tac [Lfp_def, ClosedUnder_def] THEN REPEAT strip_tac);
a (once_rewrite_tac [sets_ext_clauses] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
val lfp_induction_thm = save_pop_thm "lfp_induction_thm";

val lfp_induction_thm1 = save_thm ("lfp_induction_thm1",
	pc_rule1 "hol" rewrite_rule [get_spec ⌜$ClosedUnder⌝] lfp_induction_thm);
=TEX
}%ignore

=GFT
⦏lfp_induction_thm⦎ =
	⊢ ∀h⦁ Monotonic h ⇒ ∀s⦁ s ClosedUnder h ⇒ (Lfp h) ⊆ s
⦏lfp_induction_thm1⦎ =
	⊢ ∀h⦁ Monotonic h ⇒ ∀s⦁ h s ⊆ s ⇒ (Lfp h) ⊆ s
=TEX

This is the corresponding theorem for greatest fixed point to the ``induction'' principle for least fixed points.

\ignore{
=SML
set_goal([],⌜∀h⦁ Monotonic h ⇒ ∀s⦁ s OpenUnder h ⇒ s ⊆ (Gfp h)⌝);
a (rewrite_tac [gfp_def, OpenUnder_def] THEN REPEAT strip_tac);
a (once_rewrite_tac [sets_ext_clauses] THEN contr_tac);
a (asm_fc_tac[]);
val gfp_coinduction_thm = save_pop_thm "gfp_coinduction_thm";

val gfp_coinduction_thm1 = save_thm ("gfp_coinduction_thm1",
	pc_rule1 "hol" rewrite_rule [get_spec ⌜$OpenUnder⌝] gfp_coinduction_thm);
=TEX
}%ignore

=GFT
⦏gfp_coinduction_thm⦎ =
	⊢ ∀h⦁ Monotonic h ⇒ ∀s⦁ s OpenUnder h ⇒ s ⊆ (Gfp h)
⦏gfp_coinduction_thm1⦎ =
	⊢ ∀ h⦁ Monotonic h ⇒ (∀ s⦁ s ⊆ h s ⇒ s ⊆ Gfp h)
=TEX

These basic induction and co-induction theorems can be strengthened.
The induction principle tells us that any collection having the relevant closure property contains the closure.

The following allows properties to be established which are not themselves closed.

=GFT
⦏lfp_induction_thm2⦎ =
	⊢ ∀h⦁ Monotonic h ⇒ ∀s⦁ (s ∩ (Lfp h)) ClosedUnder h ⇒ (Lfp h) ⊆ s
⦏gfp_coinduction_thm2⦎ =
	⊢ ∀h⦁ Monotonic h ⇒ ∀s⦁ (s ∪ (Gfp h)) OpenUnder h ⇒ s ⊆ (Gfp h)
=TEX

\ignore{
=SML
set_goal([], ⌜∀h⦁ Monotonic h ⇒ ∀s⦁ (s ∩ (Lfp h)) ClosedUnder h ⇒ (Lfp h) ⊆ s⌝);
a (REPEAT strip_tac THEN all_fc_tac [lfp_induction_thm]);
a (PC_T1 "hol1" asm_prove_tac[]);
val lfp_induction_thm2 = save_pop_thm "lfp_induction_thm2";

set_goal([], ⌜∀h⦁ Monotonic h ⇒ ∀s⦁ (s ∪ (Gfp h)) OpenUnder h ⇒ s ⊆ (Gfp h)⌝);
a (REPEAT strip_tac THEN all_fc_tac [gfp_coinduction_thm]);
a (PC_T1 "hol1" asm_prove_tac[]);
val gfp_coinduction_thm2 = save_pop_thm "gfp_coinduction_thm2";
=TEX
}%ignore

Above one must show that the intersection of $s$ and the least fixed point of $h$ is closed under $h$.

It suffices however to show that the image of that set under $h$ is contained in $s$:

=GFT
⦏lfp_induction_thm3⦎ =
	⊢ ∀ h⦁ Monotonic h ⇒ (∀ s⦁ h (s ∩ Lfp h) ⊆ s ⇒ Lfp h ⊆ s)
⦏gfp_coinduction_thm3⦎ =
	⊢ ∀ h⦁ Monotonic h ⇒ (∀ s⦁ s ⊆ h (s ∪ Gfp h) ⇒ s ⊆ Gfp h)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ h⦁ Monotonic h ⇒ (∀ s⦁ h (s ∩ Lfp h) ⊆ s ⇒ Lfp h ⊆ s)⌝);
a (REPEAT strip_tac);
a (fc_tac [Monotonic_def]);
a (fc_tac [lfp_induction_thm1]);
a (lemma_tac ⌜s ∩ Lfp h ⊆ Lfp h⌝ THEN1 (PC_T1 "hol1" prove_tac[])); 
a (lemma_tac ⌜h (s ∩ Lfp h) ⊆ Lfp h⌝
	THEN1 (ALL_ASM_FC_T (MAP_EVERY ante_tac) []
		THEN FC_T rewrite_tac [lfp_fixedpoint_thm]
		THEN strip_tac));
a (lemma_tac ⌜h (s ∩ Lfp h) ⊆ s ∩ Lfp h⌝
	THEN1 (PC_T1 "hol1" asm_prove_tac[]));
a (all_fc_tac [lfp_induction_thm1]);
a (PC_T1 "hol1" asm_prove_tac[]);
val lfp_induction_thm3 = save_pop_thm "lfp_induction_thm3";

set_goal([], ⌜∀ h⦁ Monotonic h ⇒ (∀ s⦁ s ⊆ h (s ∪ Gfp h) ⇒ s ⊆ Gfp h)⌝);
a (REPEAT strip_tac);
a (fc_tac [Monotonic_def]);
a (fc_tac [gfp_coinduction_thm1]);
a (lemma_tac ⌜Gfp h ⊆ s ∪ Gfp h⌝ THEN1 (PC_T1 "hol1" prove_tac[])); 
a (lemma_tac ⌜Gfp h ⊆ h (s ∪ Gfp h)⌝
	THEN1 (ALL_ASM_FC_T (MAP_EVERY ante_tac) []
		THEN FC_T rewrite_tac [gfp_fixedpoint_thm]
		THEN strip_tac));
a (lemma_tac ⌜s ∪ Gfp h ⊆ h (s ∪ Gfp h)⌝
	THEN1 (PC_T1 "hol1" asm_prove_tac[]));
a (all_fc_tac [gfp_coinduction_thm1]);
a (PC_T1 "hol1" asm_prove_tac[]);
val gfp_coinduction_thm3 = save_pop_thm "gfp_coinduction_thm3";

=TEX
}%ignore

\subsection{Monotonicity Against Other Relations}

The above considers only functions on sets which are monotonic relative to the subset relationship.

In order to get fixed points the relations relative to which our functions are monotone must have appropriate kinds of completeness.
Ideally they will be simply ``complete'' i.e. having supremum and infimum of arbitrary sets of elements.
This makes the domain into a complete lattice, but since we focus on the relation and do not have operators for supremum and infimum in the structure we are considering, what we are doing doesn't look like lattice theory.

However, we sometimes want to obtain fixed points relative to orderings which are not complete.
We begin with chain-complete partial orders.
I should for consistency have done chain co-complete partial orders as well but that didn't occur to me at the time.

\subsection{Reflexive Partial Orders}

It is simpler to do this specifically for reflexive partial orders, whereas the theory of orders already available is not specific to reflexive orders.
The notion of of reflexive partial order is therefore defined first, and various relevant concepts (upper and lower bounds etc.) are introduced in this context.

Since the orders considered here are reflexive we will use the symbol $≤⋎v$ as a variable ranging over these relations.
Note however that the theory {\it ordered\_sets}, on which we draw, uses $<<$.
Note also that we do not follow generally here the practice of reasoning about relations over sets.
Usually we reason about relations over whole types.

In the theory {\it ordered\_sets} ordering relations are treated in many areas with indifference as to whether they are reflexive or strict or inbetween.
Here we work primarily with reflexive partial orders.
The distinction is marked (perhaps not consistently) by the choice of symbol for relation variable.
Where a reflexive relation is intended the symbol $≤⋎v$ is used, where the relation need not be reflexive we follow {\it ordered\_sets} in using $<<$.
Where I have used $r$ this is prior to my introducing this scheme and the relation is probably reflexive.

=SML
declare_infix (300, "⦏≤⋎v⦎");
=TEX

ⓈHOLCONST
│ ⦏Rpo⦎ : ('a SET) × ('a → 'a → BOOL) → BOOL
├───────────
│ ∀r⦁ Rpo r ⇔ PartialOrder r ∧ Refl r
■

=GFT
⦏rpo_fc_clauses⦎ =
   ⊢ ∀ (X, $≤⋎v)
     ⦁ Rpo (X, $≤⋎v)
         ⇒ (∀ x y⦁ x ∈ X ∧ y ∈ X ∧ x ≤⋎v y ∧ y ≤⋎v x ⇒ x = y)
           ∧ (∀ x y z⦁ x ∈ X ∧ y ∈ X ∧ z ∈ X ∧ x ≤⋎v y ∧ y ≤⋎v z ⇒ x ≤⋎v z)
           ∧ (∀ x⦁ x ∈ X ⇒ x ≤⋎v x)
=TEX

ⓈHOLCONST
│ ⦏RpoU⦎: ('a → 'a → BOOL) → BOOL
├──────
│ ∀ r⦁ RpoU r ⇔ Rpo (Universe, r)
■

=GFT
⦏rpou_fc_clauses⦎ =
   ⊢ ∀ $≤⋎v
     ⦁ Rpo (Universe, $≤⋎v)
         ⇒ (∀ x y⦁ x ≤⋎v y ∧ y ≤⋎v x ⇒ x = y)
           ∧ (∀ x y z⦁ x ≤⋎v y ∧ y ≤⋎v z ⇒ x ≤⋎v z)
           ∧ (∀ x⦁ x ≤⋎v x)

⦏rpou_fc_clauses2⦎ =
   ⊢ ∀ $≤⋎v
     ⦁ RpoU $≤⋎v
         ⇒ (∀ x y⦁ x ≤⋎v y ∧ y ≤⋎v x ⇒ x = y)
           ∧ (∀ x y z⦁ x ≤⋎v y ∧ y ≤⋎v z ⇒ x ≤⋎v z)
           ∧ (∀ x⦁ x ≤⋎v x)

⦏rpo_antisym_lemma⦎ =
   ⊢ ∀ X r f⦁ Rpo (X, r) ⇒ Antisym (X, r)

⦏rpo_∩_lemma⦎ =
   ⊢ ∀ X Y r⦁ Rpo (X, r) ∧ Rpo (Y, r) ⇒ Rpo (X ∩ Y, r)
=TEX

\ignore{
=SML
push_merge_pcs ["rbjmisc1", "'fixp"];

set_goal([], ⌜∀(X, $≤⋎v)⦁ Rpo (X, $≤⋎v)
	⇒ (∀ x y⦁ x ∈ X ∧ y ∈ X ∧ x ≤⋎v y ∧ y ≤⋎v x ⇒ x = y)
	∧ (∀ x y z⦁ x ∈ X ∧ y ∈ X ∧ z ∈ X ∧ x ≤⋎v y ∧ y ≤⋎v z ⇒ x ≤⋎v z)
	∧ (∀ x⦁ x ∈ X ⇒ x ≤⋎v x)
⌝);
a (rewrite_tac (map get_spec [⌜Rpo⌝, ⌜PartialOrder⌝, ⌜Antisym⌝, ⌜Trans⌝, ⌜Refl⌝])
	THEN REPEAT_N 6 strip_tac
	THEN REPEAT ∀_tac
	THEN_TRY asm_rewrite_tac[]
	THEN contr_tac);
a (all_asm_fc_tac[]);
val rpo_fc_clauses = save_pop_thm "rpo_fc_clauses";

set_goal([], ⌜∀$≤⋎v⦁ Rpo (Universe, $≤⋎v)
	⇒ (∀ x y⦁ x ≤⋎v y ∧ y ≤⋎v x ⇒ x = y)
	∧ (∀ x y z⦁ x ≤⋎v y ∧ y ≤⋎v z ⇒ x ≤⋎v z)
	∧ (∀ x⦁ x ≤⋎v x)
⌝);
a (strip_tac THEN strip_tac
	THEN (ASM_FC_T (MAP_EVERY ante_tac) [rpo_fc_clauses])
	THEN PC_T1 "hol1" rewrite_tac[]
	THEN contr_tac
	THEN REPEAT (asm_fc_tac[]));
val rpou_fc_clauses = save_pop_thm "rpou_fc_clauses";

set_goal([], ⌜∀$≤⋎v⦁ RpoU $≤⋎v
	⇒ (∀ x y⦁ x ≤⋎v y ∧ y ≤⋎v x ⇒ x = y)
	∧ (∀ x y z⦁ x ≤⋎v y ∧ y ≤⋎v z ⇒ x ≤⋎v z)
	∧ (∀ x⦁ x ≤⋎v x)
⌝);
a (rewrite_tac [get_spec ⌜RpoU⌝] THEN REPEAT strip_tac
	THEN fc_tac [rpou_fc_clauses]
	THEN asm_fc_tac[]
	THEN asm_fc_tac[]
	THEN asm_rewrite_tac[]);
val rpou_fc_clauses2 = save_pop_thm "rpou_fc_clauses2";

set_goal([], ⌜∀X r f⦁ Rpo (X,r) ⇒ Antisym (X, r)⌝);
a (rewrite_tac [get_spec ⌜Antisym⌝]
	THEN REPEAT strip_tac);
a (fc_tac [rpo_fc_clauses]);
a (list_spec_nth_asm_tac 1 [⌜x⌝, ⌜y⌝]);
val rpo_antisym_lemma = pop_thm ();

set_goal([], ⌜∀X Y r⦁ Rpo (X,r) ∧ Rpo (Y,r) ⇒ Rpo (X ∩ Y,r)⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜Rpo⌝]
	THEN strip_tac);
a (asm_tac (pc_rule1 "hol1" prove_rule [] ⌜X ∩ Y ⊆ X⌝));
a (strip_asm_tac (list_∀_elim [⌜Y⌝, ⌜X ∩ Y⌝, ⌜r⌝] subrel_partial_order_thm));
a (strip_asm_tac (list_∀_elim [⌜Y⌝, ⌜X ∩ Y⌝, ⌜r⌝] subrel_refl_thm));
a contr_tac;
val rpo_∩_lemma = pop_thm();

set_goal([], ⌜∃Lfp⋎c⦁ ∀ r f⦁ (∃ e⦁ IsLfp r f e) ⇒ IsLfp r f (Lfp⋎c r f)⌝);
a (REPEAT strip_tac
	THEN ∃_tac ⌜λr f⦁ εe⦁ IsLfp r f e⌝
	THEN rewrite_tac[]
	THEN REPEAT strip_tac);
a (ε_tac ⌜εe⦁ IsLfp r f e⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Lfp⋎c⦎: ('a → 'a → BOOL) → ('a → 'a) → 'a
├─────────
│ ∀ r f⦁ (∃ e⦁ IsLfp r f e) ⇒ IsLfp r f (Lfp⋎c r f)
■

\ignore{
=SML
set_goal([], ⌜∃Gfp⋎c⦁ ∀ r f⦁ (∃ e⦁ IsGfp r f e) ⇒ IsGfp r f (Gfp⋎c r f)⌝);
a (REPEAT strip_tac
	THEN ∃_tac ⌜λr f⦁ εe⦁ IsGfp r f e⌝
	THEN rewrite_tac[]
	THEN REPEAT strip_tac);
a (ε_tac ⌜εe⦁ IsGfp r f e⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Gfp⋎c⦎: ('a → 'a → BOOL) → ('a → 'a) → 'a
├─────────
│ ∀ r f⦁ (∃ e⦁ IsGfp r f e) ⇒ IsGfp r f (Gfp⋎c r f)
■

=GFT
⦏islfp_unique_lemma2⦎ =
   ⊢ ∀ r f e⦁ Antisym (Universe, r) ∧ IsLfp r f e ⇒ Lfp⋎c r f = e

⦏isgfp_unique_lemma2⦎ =
   ⊢ ∀ r f e⦁ Antisym (Universe, r) ∧ IsGfp r f e ⇒ Gfp⋎c r f = e
=TEX

\ignore{
=SML
set_goal([], ⌜∀ r f e⦁ Antisym(Universe, r) ∧ IsLfp r f e ⇒ (Lfp⋎c r f) = e⌝);
a (REPEAT strip_tac THEN fc_tac [get_spec ⌜Lfp⋎c⌝]);
a (all_fc_tac [islfp_unique_lemma]);
val islfp_unique_lemma2 = pop_thm ();

set_goal([], ⌜∀ r f e⦁ Antisym(Universe, r) ∧ IsGfp r f e ⇒ (Gfp⋎c r f) = e⌝);
a (REPEAT strip_tac THEN fc_tac [get_spec ⌜Gfp⋎c⌝]);
a (all_fc_tac [isgfp_unique_lemma]);
val isgfp_unique_lemma2 = pop_thm ();
=TEX
}%ignore

\subsubsection{Directed Sets}

These definitions are not actually used.

We need the concept of a directed set.

ⓈHOLCONST
│ ⦏Directed⦎ : ('a → 'a → BOOL) → 'a SET → BOOL
├───────────
│ ∀ r s⦁ Directed r s ⇔ ∀x y⦁ x ∈ s ∧ y ∈ s ⇒ ∃z⦁ z ∈ s ∧ IsUb r {x; y} z
■

Which we use to define the property of having directed upper bounds:

ⓈHOLCONST
│ ⦏DirectedUb⦎ : ('a → 'a → BOOL) → BOOL
├───────────
│ ∀ r⦁ DirectedUb r ⇔ ∀s⦁ Directed r s ⇒ ∃x⦁ IsUb r s x
■

\subsection{Monotonicity}

We need to establish the existence of least fixed points of monotone functions and so we want a result to the effect that the greatest lower bound of closed elements is a fixed point.
A closed element is one which maps to a point below itself in the ordering.

ⓈHOLCONST
│ ⦏Increasing⦎ : ('a → 'a → BOOL) → ('b → 'b → BOOL) → ('a → 'b) → BOOL
├───────────
│ ∀ r s f⦁ Increasing r s f ⇔ ∀x y⦁ r x y ⇒ s (f x) (f y)
■

=GFT
⦏increasing_funcomp_thm⦎ =
   ⊢ ∀ r1 r2 r3 f g
     ⦁ Increasing r1 r2 f ∧ Increasing r2 r3 g ⇒ Increasing r1 r3 (g o f)

⦏increasing_funcomp_thm2⦎ =
   ⊢ ∀ r1 r2 r3 f g
     ⦁ Increasing r1 r2 f ∧ Increasing r2 r3 g ⇒ Increasing r1 r3 (λx⦁ g(f(x)))
=TEX

\ignore{
=SML
set_goal([], ⌜∀r1 r2 r3 f g⦁ Increasing r1 r2 f ∧ Increasing r2 r3 g ⇒ Increasing r1 r3 (g o f)⌝);
a (rewrite_tac [get_spec ⌜Increasing⌝]
	THEN REPEAT strip_tac
	THEN REPEAT (all_asm_ufc_tac[]));
val increasing_funcomp_thm = save_pop_thm "increasing_funcomp_thm";

set_goal([], ⌜∀r1 r2 r3 f g⦁ Increasing r1 r2 f ∧ Increasing r2 r3 g ⇒ Increasing r1 r3 (λx⦁ g(f(x)))⌝);
a (rewrite_tac [get_spec ⌜Increasing⌝]
	THEN REPEAT strip_tac
	THEN REPEAT (all_asm_ufc_tac[]));
val increasing_funcomp_thm2 = save_pop_thm "increasing_funcomp_thm2";
=TEX
}%ignore

Since the least fixed point will be a greatest lower bound, we need to know that greatest lower bounds exist to prove that there is a fixed point.
Since we don't have a top element we assert only the existence of a greatest lower bound for non-empty sets.

=GFT
⦏mono_fixp_thm⦎ =
   ⊢ ∀ f r
     ⦁ Refl (Universe, r)
           ∧ (∀ x y⦁ r x y ∧ r y x ⇒ x = y)
           ∧ trans r
           ∧ Increasing r r f
           ∧ NeGlbsExist r
           ∧ (∃ x⦁ r (f x) x)
         ⇒ (∃ e⦁ IsGlb r {x|r (f x) x} e ∧ IsLfp r f e)

⦏mono_fixp_thm2⦎ =
   ⊢ ∀ f r
     ⦁ Refl (Universe, r)
           ∧ (∀ x y⦁ r x y ∧ r y x ⇒ x = y)
           ∧ trans r
           ∧ Increasing r r f
           ∧ GlbsExist r
         ⇒ (∃ e⦁ IsGlb r {x|r (f x) x} e ∧ IsLfp r f e)

⦏mono_fixp_thm3⦎ =
   ⊢ ∀ f r
     ⦁ Refl (Universe, r)
           ∧ (∀ x y⦁ r x y ∧ r y x ⇒ x = y)
           ∧ trans r
           ∧ Increasing r r f
           ∧ LubsExist r
         ⇒ (∃ e⦁ IsLub r {x|r x (f x)} e ∧ IsGfp r f e)
=TEX

\ignore{
=SML
set_goal([], ⌜∀f r⦁ Refl (Universe, r)
	∧ (∀x y⦁ r x y ∧ r y x ⇒ x = y)
	∧ trans r
	∧ Increasing r r f
	∧ NeGlbsExist r
	∧ (∃x⦁ r (f x) x)
	⇒ ∃e⦁ IsGlb r {x | r (f x) x} e ∧ IsLfp r f e⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜NeGlbsExist⌝]);
a (list_spec_nth_asm_tac 1 [⌜x⌝, ⌜{x|r (f x) x}⌝]);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
a (rewrite_tac [get_spec ⌜IsLfp⌝, let_def]);
a (lemma_tac ⌜f e = e⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (fc_tac [get_spec ⌜IsGlb⌝]);
a (all_asm_fc_tac[]);
a (fc_tac [get_spec ⌜Increasing⌝]);
a (lemma_tac ⌜r (f e) e⌝);
(* *** Goal "1.1" *** *)
a (spec_nth_asm_tac 4 ⌜f e⌝);
a (swap_nth_asm_concl_tac 1
	THEN rewrite_tac [get_spec ⌜IsLb⌝]
	THEN REPEAT strip_tac);
a (fc_tac [get_spec ⌜IsLb⌝]);
a (spec_nth_asm_tac 1 ⌜f x⌝);
(* *** Goal "1.1.1" *** *)
a (list_spec_nth_asm_tac 5 [⌜f x⌝, ⌜x⌝]);
(* *** Goal "1.1.2" *** *)
a (fc_tac [get_spec ⌜trans⌝]);
a (REPEAT (all_asm_fc_tac[]));
(* *** Goal "1.2" *** *)
a (lemma_tac ⌜r e (f e)⌝);
(* *** Goal "1.2.1" *** *)
a (lemma_tac ⌜r (f (f e)) (f e)⌝ THEN1 asm_fc_tac[]);
a (fc_tac [get_spec ⌜IsLb⌝]);
a (spec_nth_asm_tac 1 ⌜f e⌝);
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [get_spec ⌜IsGlb⌝]);
a (fc_tac [get_spec ⌜IsLb⌝]);
a (rewrite_tac [get_spec ⌜IsGlb⌝, get_spec ⌜IsLb⌝] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (spec_nth_asm_tac 2 ⌜x'⌝);
a (LEMMA_T ⌜x ∈ Universe⌝ asm_tac THEN1 prove_tac[]);
a (fc_tac [get_spec ⌜Refl⌝]);
a (spec_nth_asm_tac 1 ⌜x'⌝);
a (swap_nth_asm_concl_tac 4 THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (all_asm_fc_tac[]);
val mono_fixp_thm = save_pop_thm "mono_fixp_thm";

set_goal([], ⌜∀f r⦁ Refl (Universe, r)
	∧ (∀x y⦁ r x y ∧ r y x ⇒ x = y)
	∧ trans r
	∧ Increasing r r f
	∧ GlbsExist r
	⇒ ∃e⦁ IsGlb r {x | r (f x) x} e ∧ IsLfp r f e⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜GlbsExist⌝]);
a (spec_nth_asm_tac 1 ⌜{x|r (f x) x}⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
a (rewrite_tac [get_spec ⌜IsLfp⌝, let_def]);
a (lemma_tac ⌜f e = e⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (fc_tac [get_spec ⌜IsGlb⌝]);
a (all_asm_fc_tac[]);
a (fc_tac [get_spec ⌜Increasing⌝]);
a (lemma_tac ⌜r (f e) e⌝);
(* *** Goal "1.1" *** *)
a (spec_nth_asm_tac 4 ⌜f e⌝);
a (swap_nth_asm_concl_tac 1
	THEN rewrite_tac [get_spec ⌜IsLb⌝]
	THEN REPEAT strip_tac);
a (fc_tac [get_spec ⌜IsLb⌝]);
a (spec_nth_asm_tac 1 ⌜f x⌝);
(* *** Goal "1.1.1" *** *)
a (list_spec_nth_asm_tac 5 [⌜f x⌝, ⌜x⌝]);
(* *** Goal "1.1.2" *** *)
a (fc_tac [get_spec ⌜trans⌝]);
a (REPEAT (all_asm_fc_tac[]));
(* *** Goal "1.2" *** *)
a (lemma_tac ⌜r e (f e)⌝);
(* *** Goal "1.2.1" *** *)
a (lemma_tac ⌜r (f (f e)) (f e)⌝ THEN1 asm_fc_tac[]);
a (fc_tac [get_spec ⌜IsLb⌝]);
a (spec_nth_asm_tac 1 ⌜f e⌝);
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [get_spec ⌜IsGlb⌝]);
a (fc_tac [get_spec ⌜IsLb⌝]);
a (rewrite_tac [get_spec ⌜IsGlb⌝, get_spec ⌜IsLb⌝] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (spec_nth_asm_tac 2 ⌜x⌝);
a (LEMMA_T ⌜x ∈ Universe⌝ asm_tac THEN1 prove_tac[]);
a (fc_tac [get_spec ⌜Refl⌝]);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (swap_nth_asm_concl_tac 4 THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (all_asm_fc_tac[]);
val mono_fixp_thm2 = save_pop_thm "mono_fixp_thm2";

set_goal([], ⌜∀f r⦁ Refl (Universe, r)
	∧ (∀x y⦁ r x y ∧ r y x ⇒ x = y)
	∧ trans r
	∧ Increasing r r f
	∧ LubsExist r
	⇒ ∃e⦁ IsLub r {x | r x (f x)} e ∧ IsGfp r f e⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜LubsExist⌝]);
a (spec_nth_asm_tac 1 ⌜{x|r x (f x)}⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
a (rewrite_tac [get_spec ⌜IsGfp⌝, let_def]);
a (lemma_tac ⌜f e = e⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (fc_tac [get_spec ⌜IsLub⌝]);
a (all_asm_fc_tac[]);
a (fc_tac [get_spec ⌜Increasing⌝]);
a (lemma_tac ⌜r e (f e)⌝);
(* *** Goal "1.1" *** *)
a (spec_nth_asm_tac 4 ⌜f e⌝);
a (swap_nth_asm_concl_tac 1
	THEN rewrite_tac [get_spec ⌜IsUb⌝]
	THEN REPEAT strip_tac);
a (fc_tac [get_spec ⌜IsUb⌝]);
a (spec_nth_asm_tac 1 ⌜f x⌝);
(* *** Goal "1.1.1" *** *)
a (list_spec_nth_asm_tac 5 [⌜x⌝, ⌜f x⌝]);
(* *** Goal "1.1.2" *** *)
a (fc_tac [get_spec ⌜trans⌝]);
a (REPEAT (all_asm_fc_tac[]));
(* *** Goal "1.2" *** *)
a (lemma_tac ⌜r (f e) e⌝);
(* *** Goal "1.2.1" *** *)
a (lemma_tac ⌜r (f e) (f (f e))⌝ THEN1 asm_fc_tac[]);
a (fc_tac [get_spec ⌜IsUb⌝]);
a (spec_nth_asm_tac 1 ⌜f e⌝);
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [get_spec ⌜IsLub⌝]);
a (fc_tac [get_spec ⌜IsUb⌝]);
a (rewrite_tac [get_spec ⌜IsLub⌝, get_spec ⌜IsUb⌝] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (spec_nth_asm_tac 2 ⌜x⌝);
a (LEMMA_T ⌜x ∈ Universe⌝ asm_tac THEN1 prove_tac[]);
a (fc_tac [get_spec ⌜Refl⌝]);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (swap_nth_asm_concl_tac 4 THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (all_asm_fc_tac[]);
val mono_fixp_thm3 = save_pop_thm "mono_fixp_thm3";
=TEX
}%ignore

\section{CHAIN COMPLETE PARTIAL ORDERS}

A ccpo is a chain-complete partial order.
The proof of the fixed point result in this context is more difficult than in the case of a complete lattice, and the following version of it is a kludge, but will have to do for now.

The main point of this section is to obtain a least fixed point theorem for monotone functions over chain complete partial orders (CCPOs).

ⓈHOLCONST
│ ⦏ChainComplete⦎ : ('a SET × ('a → 'a → BOOL)) → BOOL
├───────────
│ ∀ X r⦁ ChainComplete (X, r) ⇔ ∀Y⦁ Y ⊆ X ∧ LinearOrder (Y, r) ⇒
│	∃x⦁ x ∈ X ∧ IsLub r Y x
■

=GFT
⦏cc_lub_lemma⦎ =
   ⊢ ∀ X r
     ⦁ ChainComplete (X, r)
         ⇒ (∀ Y⦁ Y ⊆ X ∧ LinearOrder (Y, r) ⇒ IsLub r Y (Lub r Y))

⦏ccu_lub_lemma⦎ =
   ⊢ ∀ r
     ⦁ ChainComplete (Universe, r)
         ⇒ (∀ Y⦁ LinearOrder (Y, r) ⇒ IsLub r Y (Lub r Y))
=TEX

\ignore{
=SML
set_goal([], ⌜∀(X:'a ℙ) r⦁ ChainComplete (X, r)
	⇒ ∀Y⦁ Y ⊆ X ∧ LinearOrder (Y, r)
	⇒ IsLub r Y (Lub r Y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜ChainComplete⌝]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]
	THEN all_fc_tac [lub_lub_lemma]);
val cc_lub_lemma = save_pop_thm "cc_lub_lemma";

val ccu_lub_lemma = save_thm ("ccu_lub_lemma", rewrite_rule [] (∀_elim ⌜Universe⌝ cc_lub_lemma));
=TEX
}%ignore


ⓈHOLCONST
│ ⦏CcRpo⦎ : ('a SET × ('a → 'a → BOOL)) → BOOL
├───────────
│ ∀ r⦁ CcRpo r ⇔ Rpo r ∧ ChainComplete r
■

ⓈHOLCONST
│ ⦏CcRpoU⦎ : ('a → 'a → BOOL) → BOOL
├───────────
│ ∀ r⦁ CcRpoU r ⇔ CcRpo (Universe, r)
■

=GFT
⦏ccrpou_fc_clauses⦎ =
   ⊢ ∀ r
     ⦁ CcRpoU r
         ⇒ ChainComplete (Universe, r)
           ∧ (∀ x⦁ r x x)
           ∧ (∀ x y z⦁ r x y ∧ r y z ⇒ r x z)
           ∧ (∀ x y⦁ r x y ∧ r y x ⇒ x = y)

⦏ccrpou_lub_lemma⦎ =
   ⊢ ∀ r⦁ CcRpoU r ⇒ (∀ Y⦁ LinearOrder (Y, r) ⇒ IsLub r Y (Lub r Y))

⦏ccrpou_lub_lemma2⦎ =
   ⊢ ∀ r⦁ CcRpoU r ⇒ (∀ Y⦁ LinearOrder (Y, r) ⇒ (∀ x⦁ x ∈ Y ⇒ r x (Lub r Y)))

⦏ccrpou_lub_unique_lemma⦎ =
   ⊢ ∀ r
     ⦁ CcRpoU r
         ⇒ (∀ Y⦁ LinearOrder (Y, r) ⇒ (∀ x⦁ IsLub r Y x ⇒ x = Lub r Y))
=TEX

\ignore{
=SML
set_goal ([], ⌜∀r⦁ CcRpoU r
	⇒ ChainComplete (Universe, r)
	∧ (∀ x⦁ r x x)
	∧ (∀ x y z⦁ r x y ∧ r y z ⇒ r x z)
	∧ (∀ x y⦁ r x y ∧ r y x ⇒ x = y)⌝
);
a (∀_tac THEN rewrite_tac [get_spec ⌜CcRpoU⌝, get_spec ⌜CcRpo⌝, get_spec ⌜Rpo⌝,
	get_spec ⌜Refl⌝, get_spec ⌜PartialOrder⌝,
	get_spec ⌜Antisym⌝, get_spec ⌜Trans⌝, get_spec ⌜LinearOrder⌝]
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]
	THEN_TRY all_asm_fc_tac[]
	THEN contr_tac THEN asm_fc_tac []);
val ccrpou_fc_clauses = save_pop_thm "ccrpou_fc_clauses";

set_goal([], ⌜∀r⦁ CcRpoU r
	⇒ ∀Y⦁ LinearOrder (Y, r)
	⇒ IsLub r Y (Lub r Y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜CcRpoU⌝, get_spec ⌜CcRpo⌝]
	THEN REPEAT strip_tac);
a (all_fc_tac [ccu_lub_lemma]);
val ccrpou_lub_lemma = save_pop_thm "ccrpou_lub_lemma";

set_goal([], ⌜∀ r
     ⦁ CcRpoU r
         ⇒ ∀ Y
         ⦁ LinearOrder (Y, r)
             ⇒ (∀ x⦁ x ∈ Y ⇒ r x (Lub r Y))⌝);
a (REPEAT strip_tac THEN  all_fc_tac [ccrpou_lub_lemma]);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜IsLub⌝, get_spec ⌜IsUb⌝]
	THEN strip_tac
	THEN all_asm_fc_tac[]);
val ccrpou_lub_lemma2 = save_pop_thm "ccrpou_lub_lemma2";

set_goal([], ⌜∀ r
     ⦁ CcRpoU r
         ⇒ ∀ Y
         ⦁ LinearOrder (Y, r)
             ⇒ ∀ x⦁ IsLub r Y x ⇒ x = Lub r Y⌝);
a (REPEAT strip_tac THEN  all_fc_tac [ccrpou_lub_lemma]);
a (fc_tac [get_spec ⌜CcRpoU⌝]);
a (fc_tac [get_spec ⌜CcRpo⌝]);
a (fc_tac [get_spec ⌜Rpo⌝]);
a (fc_tac [get_spec ⌜PartialOrder⌝]);
a (all_fc_tac [lub_unique_lemma]);
val ccrpou_lub_unique_lemma = save_pop_thm "ccrpou_lub_unique_lemma";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏CRpo⦎ : ('a → 'a → BOOL) → BOOL
├───────────
│ ∀ r⦁ CRpo r ⇔ Rpo (Universe, r) ∧ GlbsExist r
■

ⓈHOLCONST
│ ⦏FClosed⦎ : ('a → 'a) → 'a SET → BOOL
├───────────
│ ∀ f X⦁ FClosed f X ⇔ (∀x⦁ x ∈ X ⇒ f x ∈ X)
■

=GFT
⦏fclosed_universe_lemma⦎ =
   ⊢ ∀ f⦁ FClosed f Universe

⦏fclosed_∩_lemma⦎ =
   ⊢ ∀ X Y f⦁ FClosed f X ∧ FClosed f Y ⇒ FClosed f (X ∩ Y)
=TEX

\ignore{
=SML
set_goal([], ⌜∀f⦁ FClosed f Universe⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜FClosed⌝] THEN prove_tac[]);
val fclosed_universe_lemma = save_pop_thm "fclosed_universe_lemma";

set_goal ([], ⌜∀X Y f⦁ FClosed f X ∧ FClosed f Y ⇒ FClosed f (X ∩ Y)⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜FClosed⌝]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
val fclosed_∩_lemma = pop_thm();

add_pc_thms "'fixp" (map get_spec [] @ [fclosed_universe_lemma]);
set_merge_pcs ["rbjmisc1", "'fixp"];
=TEX
}%ignore

ⓈHOLCONST
│ ⦏FChainClosed⦎ : ('a → 'a) → ('a SET × ('a → 'a → BOOL)) → BOOL
├───────────
│ ∀ f X r⦁ FChainClosed f (X, r) ⇔ 
│	FClosed f X ∧ ChainComplete (X, r)
■

=GFT
⦏ccrpou_fchainclosed_lemma⦎ =
   ⊢ ∀ r⦁ CcRpoU r ⇒ FChainClosed f (Universe, r)

⦏ccrpou_fchainclosed_lemma2⦎ =
   ⊢ ∀ r X
     ⦁ CcRpoU r ∧ FChainClosed f (X, r)
         ⇒ (∀ s⦁ s ⊆ X ∧ LinearOrder (s, r) ⇒ Lub r s ∈ X)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀r⦁ CcRpoU r ⇒ FChainClosed f (Universe, r)⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜FChainClosed⌝, fclosed_universe_lemma]
	THEN strip_tac
	THEN fc_tac [ccrpou_fc_clauses]);
val ccrpou_fchainclosed_lemma = save_pop_thm "ccrpou_fchainclosed_lemma";

set_goal ([], ⌜∀r X⦁ CcRpoU r ∧ FChainClosed f (X, r) ⇒ ∀s⦁ s ⊆ X ∧ LinearOrder (s, r) ⇒ Lub r s ∈ X⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜FChainClosed⌝, get_spec ⌜ChainComplete⌝]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac []);
a (fc_tac [lub_lub_lemma]);
a (all_fc_tac [ccrpou_lub_unique_lemma]);
a (SYM_ASMS_T rewrite_tac);
val ccrpou_fchainclosed_lemma2 = save_pop_thm "ccrpou_fchainclosed_lemma2";
=TEX
}%ignore


ⓈHOLCONST
│ ⦏FChain⦎ : ('a → 'a) → ('a SET × ('a → 'a → BOOL)) → 'a SET
├───────────
│ ∀ f X r⦁ FChain f (X, r) = ⋂ {Y | Y ⊆ X ∧ FChainClosed f (Y, r)}
■

ⓈHOLCONST
│ ⦏FChainU⦎ : ('a → 'a) → ('a → 'a → BOOL) → 'a SET
├───────────
│ ∀ f r⦁ FChainU f r = FChain f (Universe, r)
■

=GFT
⦏fcc_fchain_lemma1⦎ =
   ⊢ (∃ V⦁ V ∈ W) ∧ (∀ V⦁ V ∈ W ⇒ V ⊆ X) ∧ Y ⊆ ⋂ W ⇒ Y ⊆ X

⦏fchain_lemma1⦎ =
   ⊢ ∀ X r f⦁ FChainClosed f (X, r) ⇒ FChain f (X, r) ⊆ X

⦏fchain_fchainclosed_lemma⦎ =
   ⊢ ∀ X r f
     ⦁ Antisym (Universe, r) ∧ FChainClosed f (X, r)
         ⇒ FChainClosed f (FChain f (X, r), r)

⦏fchain_fchainclosed_lemma2⦎ =
   ⊢ ∀ X r f
     ⦁ Rpo (Universe, r) ∧ FChainClosed f (X, r)
         ⇒ FChainClosed f (FChain f (X, r), r)

⦏ccrpou_fcclosed_fc_lemma⦎ =
   ⊢ ∀ r f⦁ CcRpoU r ⇒ FChainClosed f (FChainU f r, r)

⦏ccrpou_fcclosed_fc_lemma2⦎ =
   ⊢ ∀ r f X
     ⦁ CcRpoU r ∧ X ⊆ FChainU f r ∧ LinearOrder (X, r)
         ⇒ Lub r X ∈ FChainU f r
=TEX

\ignore{
=SML
set_goal([], ⌜(∃V⦁ V ∈ W) ∧ (∀V⦁ V ∈ W ⇒ V ⊆ X) ∧ Y ⊆ ⋂W ⇒ Y ⊆ X⌝);
a (REPEAT strip_tac THEN REPEAT (asm_fc_tac[]));
val fcc_fchain_lemma1 = pop_thm();

set_goal([], ⌜∀(X:'a ℙ) r f⦁ FChainClosed f (X, r) ⇒ FChain f (X,r) ⊆ X⌝);
a (rewrite_tac [get_spec ⌜FChain⌝]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜X⌝);
val fchain_lemma1 = save_pop_thm "fchain_lemma1";

push_merge_pcs ["rbjmisc", "'fixp"];

set_goal([], ⌜∀X r f⦁ Antisym (Universe, r) ∧ FChainClosed f (X, r)
	⇒ FChainClosed f (FChain f (X,r), r)⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜FChainClosed⌝]);
a (fc_tac [get_spec ⌜FClosed⌝]);
a (rewrite_tac [get_spec ⌜FChainClosed⌝, get_spec ⌜FClosed⌝]
	THEN REPEAT ∀_tac
	THEN strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜FChainClosed⌝,
		get_spec ⌜FClosed⌝,
		get_spec ⌜FChain⌝,
		get_spec ⌜ChainComplete⌝]
	THEN REPEAT strip_tac
	THEN REPEAT (asm_fc_tac[]));
(* *** Goal "2" *** *)
a (fc_tac [get_spec ⌜ChainComplete⌝]);
a (rewrite_tac [get_spec ⌜ChainComplete⌝]
	THEN REPEAT strip_tac);
a (fc_tac [fchain_lemma1]);
a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B C⦁ A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C⌝]);
a (all_asm_fc_tac []);
a (∃_tac ⌜x⌝ THEN REPEAT strip_tac);
a (REPEAT_N 3 (PC_T1 "hol1" once_rewrite_tac [get_spec ⌜FChain⌝])
	THEN REPEAT strip_tac);
a (fc_tac [get_spec ⌜FChainClosed⌝]);
a (fc_tac [get_spec ⌜FClosed⌝]);
a (fc_tac [get_spec ⌜ChainComplete⌝]);
a (lemma_tac ⌜FChain f (X, r) ⊆ s⌝
	THEN1 (rewrite_tac [get_spec ⌜FChain⌝] THEN REPEAT strip_tac
		THEN (PC_T1 "hol1" asm_rewrite_tac [])
		THEN REPEAT strip_tac THEN all_asm_fc_tac[]));
a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B C⦁ A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C⌝]);
a (all_asm_fc_tac[]);
a (fc_tac [lub_unique_lemma]);
a (all_asm_fc_tac[]);
a (var_elim_nth_asm_tac 8);
val fchain_fchainclosed_lemma = save_pop_thm "fchain_fchainclosed_lemma";

set_goal([], ⌜∀X r f⦁ Rpo (Universe, r) ∧ FChainClosed f (X, r)
	⇒ FChainClosed f (FChain f (X,r), r)⌝);
a (REPEAT strip_tac
	THEN fc_tac [rpo_antisym_lemma]
	THEN all_fc_tac [fchain_fchainclosed_lemma]);
val fchain_fchainclosed_lemma2 = save_pop_thm "fchain_fchainclosed_lemma2";

set_goal([], ⌜∀r f⦁ CcRpoU r ⇒ FChainClosed f (FChainU f r, r)⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜CcRpoU⌝]);
a (fc_tac [get_spec ⌜CcRpo⌝]);
a (lemma_tac ⌜FChainClosed f (Universe, r)⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜FChainClosed⌝]));
a (all_fc_tac [fchain_fchainclosed_lemma2]);
a (asm_rewrite_tac [get_spec ⌜FChainU⌝]);
val ccrpou_fcclosed_fc_lemma = save_pop_thm "ccrpou_fcclosed_fc_lemma";

set_goal([], ⌜∀r f X⦁ CcRpoU r ∧ X ⊆ FChainU f r ∧ LinearOrder (X, r)
	⇒ Lub r X ∈ FChainU f r⌝);
a (REPEAT strip_tac);
a (fc_tac [ccrpou_fcclosed_fc_lemma]);
a (spec_nth_asm_tac 1 ⌜f⌝);
a (fc_tac [get_spec ⌜FChainClosed⌝]);
a (fc_tac [get_spec ⌜ChainComplete⌝]);
a (all_fc_tac [ccrpou_fchainclosed_lemma2]);
val ccrpou_fcclosed_fc_lemma2 = save_pop_thm "ccrpou_fcclosed_fc_lemma2";
=TEX
}%ignore

=GFT
⦏fchain_lemma2⦎ =
   ⊢ ∀ X Y r f
     ⦁ Rpo (Universe, r)
           ∧ FChainClosed f (X, r)
           ∧ Y ⊆ FChain f (X, r)
           ∧ FChainClosed f (Y, r)
         ⇒ Y = FChain f (X, r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀X r f⦁ Rpo (Universe, r) ∧ FChainClosed f (X, r)
	⇒ ∀x⦁ x ∈ FChain f (X,r) ⇒ f x ∈ FChain f (X,r)⌝);
a (REPEAT strip_tac);
a (fc_tac [rpo_antisym_lemma]);
a (all_fc_tac [fchain_fchainclosed_lemma]);
a (all_fc_tac [get_spec ⌜FChainClosed⌝]);
a (all_fc_tac [get_spec ⌜FClosed⌝]);
val fc_fcclosed_fc_lemma = save_pop_thm "fc_fcclosed_fc_lemma";

set_goal([], ⌜∀(X:'a ℙ) Y r f⦁ Rpo (Universe, r) ∧ FChainClosed f (X, r)
	∧ Y ⊆ FChain f (X, r) ∧ FChainClosed f (Y, r)
	⇒ Y = FChain f (X, r)⌝);
a (REPEAT strip_tac
	THEN PC_T1 "hol1" rewrite_tac [get_spec ⌜FChain⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (GET_NTH_ASM_T 5 ante_tac
	THEN PC_T1 "hol1" rewrite_tac [get_spec ⌜FChain⌝]
	THEN REPEAT strip_tac);
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 1 ⌜Y⌝);
a (fc_tac [fchain_lemma1]);
a (ALL_ASM_FC_T (fc_tac o (map (pc_rule1 "hol1" rewrite_rule []))) [⊆_trans_thm]);
val fchain_lemma2 = save_pop_thm "fchain_lemma2";
=TEX
}%ignore

The last lemma is in effect an induction principle which is used several times in the proof which follows of the existence of least fixed points for monotone functors over chain-complete orders.
Though I don't have a plan to rationalise that proof, I propose here to improve support for induction over $FChain$s.

First I recast the above lemma to make it look more explicitly like an induction principle.
I am interested in the use of induction to prove results about least fixed points of functions which are monotone relative to some ordering which is complete over the whole type (though chain completeness suffices).
The inductive part of such a proof will establish a property common to the elements of the $FChain$ generated by the function starting from the bottom element.
In principle we could have an induction principle which yields a property of the least fixed point, but this would be less useful in general than proving the property of the whole $FChain$.
This will allow proofs to be broken into smaller pieces than would otherwise be the case.

First $fchain\_lemma2$ is simplified for the case that the relation is chain complete over the type.

=GFT
⦏fchain_lemma3⦎ =
   ⊢ ∀ X Y r f
     ⦁ CcRpoU r ∧ Y ⊆ FChainU f r ∧ FChainClosed f (Y, r) ⇒ Y = FChainU f r
=TEX

\ignore{
=SML
set_goal([], ⌜∀(X:'a ℙ) Y r f⦁ CcRpoU r ∧ Y ⊆ FChainU f r ∧ FChainClosed f (Y, r)
	⇒ Y = FChainU f r⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜FChainU⌝]
	THEN REPEAT strip_tac);
a (fc_tac [get_spec ⌜CcRpoU⌝]);
a (fc_tac [get_spec ⌜CcRpo⌝]);
a (lemma_tac ⌜FChainClosed f (Universe, r)⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜FChainClosed⌝, get_spec ⌜FClosed⌝]));
a (all_fc_tac [fchain_lemma2]);
val fchain_lemma3 = save_pop_thm "fchain_lemma3";
=TEX
}%ignore

Now we make this look more like an induction principle.
First, retaining the set theoretic casting, thinking of $Y$ as the extension of some property which is to be proven of all elements in the $FChain$ (in this case $Y$ need not be a subset of the chain):

=GFT
⦏fchain_lemma4⦎ =
   ⊢ ∀ r f Y
     ⦁ CcRpoU r
           ∧ FClosed f (Y ∩ FChainU f r)
           ∧ ChainComplete (Y ∩ FChainU f r, r)
         ⇒ FChainU f r ⊆ Y
=TEX

\ignore{
=SML
set_goal([], ⌜∀r f Y⦁ CcRpoU r ∧ FClosed f (Y ∩ (FChainU f r)) ∧ ChainComplete (Y ∩ (FChainU f r), r)
	⇒ FChainU f r ⊆ Y⌝);
a (REPEAT strip_tac THEN fc_tac [rewrite_rule [get_spec ⌜FChainClosed⌝] fchain_lemma3]);
a (lemma_tac ⌜Y ∩ FChainU f r ⊆ FChainU f r⌝ THEN1 PC_T1 "hol1" prove_tac[]);
a (list_spec_nth_asm_tac 2 [⌜Y ∩ FChainU f r⌝, ⌜f⌝]);
a (SYM_ASMS_T once_rewrite_tac
	THEN PC_T1 "hol1" prove_tac[]);
val fchain_lemma4 = save_pop_thm "fchain_lemma4";
=TEX
}%ignore

Now we come to a formulation suitable for use in a typical induction tactic, which expects the property to be obtained by abstraction on the conclusion of the current goal.

=GFT
⦏fchainu_lemma1⦎ =	
   ⊢ ∀ f r x⦁ x ∈ FChainU f r ⇒ f x ∈ FChainU f r

⦏fchainu_induction_thm1⦎ =
   ⊢ ∀ r f p
     ⦁ CcRpoU r
           ∧ (∀ x⦁ x ∈ FChainU f r ∧ p x ⇒ p (f x))
           ∧ (∀ s⦁ s ⊆ FChainU f r ∧ (∀ y⦁ y ∈ s ⇒ p y) ⇒ p (Lub r s))
         ⇒ x ∈ FChainU f r
         ⇒ p x
=TEX

\ignore{
=SML
set_goal([], ⌜∀f r x⦁ x ∈ FChainU f r ⇒ f x ∈ FChainU f r⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜FChainU⌝, get_spec ⌜FChainClosed⌝, get_spec ⌜FChain⌝, get_spec ⌜FClosed⌝]);
a (REPEAT ∀_tac THEN PC_T1 "hol1" rewrite_tac[] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
a (asm_fc_tac[]);
val fchainu_lemma1 = save_pop_thm "fchainu_lemma1";

set_goal([], ⌜∀r f p⦁ CcRpoU r
	∧ (∀x⦁ x ∈ FChainU f r ∧ p x ⇒ p (f x))
	∧ (∀s⦁ s ⊆ FChainU f r ∧ (∀y⦁ y ∈ s ⇒ p y) ⇒ p (Lub r s))
	⇒ x ∈ FChainU f r ⇒ p x⌝);
a (REPEAT strip_tac);
a (fc_tac [ccrpou_fcclosed_fc_lemma]);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜FChainClosed⌝]
	THEN STRIP_T (strip_asm_tac o (∀_elim ⌜f⌝)));
a (fc_tac [get_spec ⌜FClosed⌝]);
a (lemma_tac ⌜FClosed f ({x|p x} ∩ FChainU f r)⌝
	THEN1 (rewrite_tac [get_spec ⌜FClosed⌝]
		THEN REPEAT strip_tac
		THEN all_asm_fc_tac[]));
a (lemma_tac ⌜ChainComplete ({x|p x} ∩ FChainU f r, r)⌝
	THEN1 (rewrite_tac [get_spec ⌜ChainComplete⌝]
		THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 8 ⌜Y⌝);
(* *** Goal "1.1" *** *)
a (POP_ASM_T ante_tac THEN DROP_NTH_ASM_T 2 ante_tac
	THEN PC_T1 "rbjmisc1" prove_tac[]);
(* *** Goal "1.2" *** *)
a (REPEAT_N 2 (POP_ASM_T ante_tac) THEN DROP_NTH_ASM_T 2 ante_tac
	THEN PC_T1 "rbjmisc1" prove_tac[]);
(* *** Goal "1.3" *** *)
a (lemma_tac ⌜Y ⊆ FChainU f r⌝
	THEN1 (DROP_NTH_ASM_T 3 ante_tac THEN PC_T1 "rbjmisc1" prove_tac[]));
a (all_fc_tac [get_spec ⌜ChainComplete⌝]);
a (lemma_tac ⌜Antisym (Universe, r)⌝
	THEN1 (fc_tac [get_spec ⌜CcRpoU⌝]
		THEN fc_tac [get_spec ⌜CcRpo⌝]
		THEN fc_tac [get_spec ⌜Rpo⌝]
		THEN fc_tac [get_spec ⌜PartialOrder⌝]));
a (all_fc_tac [islub_lub_lemma]);
a (∃_tac ⌜x'⌝ THEN REPEAT strip_tac
	THEN (SYM_ASMS_T rewrite_tac));
a (all_fc_tac [fchain_lemma4]);
a (PC_T1 "rbjmisc1" asm_prove_tac []);
val fchainu_induction_thm1 = save_pop_thm "fchainu_induction_thm1";
=TEX
}%ignore

This induction theorem requires a proof that the property is chain-complete over the relevant $FChain$.
However, in this context a ``course of values'' induction theorem should be realisable, in which the hypothesis of the step case is stronger.
This amounts to the observation that the relevant $r$ is well-founded on the $FChain$. 
The statement and proof of the course of values induction principle is deferred a while because it requires a result not yet obtained.

The following lemmas leading towards the fixed point theorem are proven by the method supported by $fchain\_lemma2$

=GFT
⦏ccrpo_fixp_lemma1⦎ =
   ⊢ ∀ X r f
     ⦁ Increasing r r f
         ⇒ FClosed f {x|x ∈ FChain f (X, r) ∧ (r x (f x) ∨ x = f x)}

⦏ccrpo_fixp_lemma2⦎ =
   ⊢ ∀ X r f
     ⦁ Increasing r r f ∧ Rpo (Universe, r) ∧ FChainClosed f (X, r)
         ⇒ ChainComplete ({z|z ∈ FChain f (X, r) ∧ (r z (f z) ∨ z = f z)}, r)

⦏ccrpo_fixp_lemma3⦎ =
   ⊢ ∀ X r f
     ⦁ Increasing r r f ∧ Rpo (Universe, r) ∧ FChainClosed f (X, r)
         ⇒ FChainClosed
           f
           ({z|z ∈ FChain f (X, r) ∧ (r z (f z) ∨ z = f z)}, r)

⦏ccrpo_fixp_lemma4⦎ =
   ⊢ ∀ X r f
     ⦁ Increasing r r f ∧ Rpo (Universe, r) ∧ FChainClosed f (X, r)
         ⇒ (∀ z⦁ z ∈ FChain f (X, r) ⇒ r z (f z) ∨ z = f z)
=TEX

\ignore{
=SML
set_goal([], ⌜∀X r f⦁ Increasing r r f
	⇒ FClosed f {x | x ∈ FChain f (X,r) ∧ (r x (f x) ∨ x = (f x))}⌝);
a (REPEAT strip_tac);
a (rewrite_tac [get_spec ⌜FClosed⌝, get_spec ⌜FChain⌝]
	THEN REPEAT strip_tac THEN_TRY SYM_ASMS_T rewrite_tac);
(* *** Goal "1" *** *)
a (GET_NTH_ASM_T 4 (fn x => all_fc_tac [rewrite_rule [] x]));
a (fc_tac [get_spec ⌜FChainClosed⌝]);
a (fc_tac [get_spec ⌜FClosed⌝]);
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [get_spec ⌜Increasing⌝]);
a (asm_fc_tac[]);
(* *** Goal "3" *** *)
a (fc_tac [get_spec ⌜Increasing⌝]);
a (asm_fc_tac[]);
val ccrpo_fixp_lemma1 = pop_thm ();

set_goal([], ⌜∀X r f⦁ Increasing r r f ∧ Rpo (Universe, r) ∧ FChainClosed f (X, r)
	⇒ ChainComplete ({x | x ∈ FChain f (X,r) ∧ (r x (f x) ∨ x = (f x))}, r)⌝);
a (rewrite_tac [get_spec ⌜ChainComplete⌝]
	THEN REPEAT strip_tac);
a (fc_tac [ccrpo_fixp_lemma1]);
a (lemma_tac ⌜FChain f (X, r) ⊆ X⌝
	THEN1 (PC_T1 "hol1" rewrite_tac [get_spec ⌜FChain⌝]
		THEN REPEAT strip_tac
		THEN (spec_nth_asm_tac 1 ⌜X⌝)));
a (lemma_tac ⌜Y ⊆ FChain f (X, r)⌝
	THEN1 (PC_T1 "hol1" rewrite_tac []
		THEN REPEAT strip_tac
		THEN GET_NTH_ASM_T 5 (fn x => all_fc_tac [pc_rule1 "hol1" rewrite_rule [] x])));
a (lemma_tac ⌜Y ⊆ X⌝
	THEN1 (all_fc_tac [pc_rule1 "hol1" prove_rule []
	 ⌜∀A B C⦁ A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C⌝]));
a (fc_tac [get_spec ⌜FChainClosed⌝]);
a (all_fc_tac [get_spec ⌜ChainComplete⌝]);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
a (strip_tac);
(* *** Goal "1" *** *)
a (PC_T1 "hol1" rewrite_tac [get_spec ⌜FChain⌝]
	THEN REPEAT strip_tac);
a (fc_tac [get_spec ⌜FChainClosed⌝]);
a (lemma_tac ⌜Y ⊆ s⌝);
(* *** Goal "1.1" *** *)
a (lemma_tac ⌜FChain f (X, r) ⊆ s⌝
	THEN1 rewrite_tac [get_spec ⌜FChain⌝]);
(* *** Goal "1.1.1" *** *)
a (LEMMA_T ⌜s ∈ {Y|Y ⊆ X ∧ FChainClosed f (Y, r)}⌝ asm_tac
	THEN1 (PC_T1 "hol1" asm_rewrite_tac []));
a (bc_tac [pc_rule1 "hol1" prove_rule [] ⌜s ∈ A ⇒ ⋂A ⊆ s⌝]
	THEN CONTR_T check_asm_tac);
(* *** Goal "1.1.2" *** *)
a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B C⦁ A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C⌝]);
(* *** Goal "1.2" *** *)
a (GET_NTH_ASM_T 3 (fn x => (all_fc_tac [rewrite_rule [get_spec ⌜ChainComplete⌝] x])));
a (fc_tac [rpo_antisym_lemma]);
a (all_fc_tac [lub_unique_lemma]);
a (var_elim_nth_asm_tac 1);
(* *** Goal "2" *** *)
a (contr_tac);
a (lemma_tac ⌜IsUb r Y (f x)⌝
	THEN1 (rewrite_tac [get_spec ⌜IsUb⌝]
		THEN REPEAT strip_tac));
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜r x' (f x') ∨ x' = f x'⌝
	THEN1 GET_NTH_ASM_T 13 (fn x => asm_tac (pc_rule1 "hol1" rewrite_rule[] x)));
(* *** Goal "2.1.1" *** *)
a (spec_nth_asm_tac 1 ⌜x'⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1.2" *** *)
a (lemma_tac ⌜r x' x⌝);
(* *** Goal "2.1.2.1" *** *)
a (fc_tac [get_spec ⌜IsLub⌝]);
a (GET_NTH_ASM_T 1 ante_tac THEN rewrite_tac [get_spec ⌜IsUb⌝]
	THEN strip_tac
	THEN asm_fc_tac[]);
(* *** Goal "2.1.2.2" *** *)
a (fc_tac [get_spec ⌜Increasing⌝]
	THEN all_asm_fc_tac[]);
a (FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule[]))) [rpo_fc_clauses]);
a (all_asm_fc_tac[]);
(* *** Goal "2.1.3" *** *)
a (EXTEND_PC_T1 "'mmp1" fc_tac [get_spec ⌜IsLub⌝]);
a (GET_NTH_ASM_T 1 ante_tac THEN rewrite_tac [get_spec ⌜IsUb⌝]
	THEN strip_tac
	THEN EXTEND_PC_T1 "'mmp1"  asm_fc_tac[]);
a (EXTEND_PC_T1 "'mmp1" fc_tac [get_spec ⌜Increasing⌝]
	THEN EXTEND_PC_T1 "'mmp1" all_asm_fc_tac[]);
a (DROP_NTH_ASM_T 2 ante_tac THEN SYM_ASMS_T rewrite_tac);
(* *** Goal "2.2" *** *)
a (GET_NTH_ASM_T 4 ante_tac THEN rewrite_tac [get_spec ⌜IsLub⌝]);
a (REPEAT strip_tac);
a (all_asm_fc_tac[]);
val ccrpo_fixp_lemma2 = pop_thm ();

set_goal([], ⌜∀X r f⦁ Increasing r r f ∧ Rpo(Universe,r) ∧ FChainClosed f (X, r)
	⇒ FChainClosed f ({z|z ∈ FChain f (X,r) ∧ (r z (f z) ∨ z = f z)}, r)⌝);
a (REPEAT strip_tac);
a (rewrite_tac [get_spec ⌜FChainClosed⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac[ccrpo_fixp_lemma1]);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac[ccrpo_fixp_lemma1]);
a (all_fc_tac[rpo_antisym_lemma]);
a (all_fc_tac[fchain_fchainclosed_lemma]);
a (all_fc_tac[ccrpo_fixp_lemma2]);
val ccrpo_fixp_lemma3 = pop_thm ();

set_goal([], ⌜∀X r f⦁ Increasing r r f ∧ Rpo(Universe,r) ∧ FChainClosed f (X, r)
	⇒ ∀z⦁ z ∈ FChain f (X,r) ⇒ r z (f z) ∨ z = f z⌝);
a (REPEAT strip_tac);
a (all_fc_tac [ccrpo_fixp_lemma3]);
a (lemma_tac ⌜{z|z ∈ FChain f (X, r) ∧ (r z (f z) ∨ z = f z)} ⊆ FChain f (X, r)⌝
	THEN1 (PC_T1 "hol1" rewrite_tac[]
		THEN REPEAT strip_tac));
a (all_fc_tac [fchain_lemma2]);
a (DROP_NTH_ASM_T 5 ante_tac THEN SYM_ASMS_T once_rewrite_tac);
a (rewrite_tac[]);
a (contr_tac);
val ccrpo_fixp_lemma4 = save_pop_thm "ccrpo_fixp_lemma4";
=TEX
}%ignore

This result is needed to establish course of values induction over $FChain$s, for which purpose the following variant is handy.

=GFT
⦏ccrpou_fchainu_lemma1⦎ =
   ⊢ ∀ r f⦁ CcRpoU r ∧ Increasing r r f
	⇒ (∀ z⦁ z ∈ FChainU f r ⇒ r z (f z))
=TEX

\ignore{
=SML
set_goal([], ⌜∀r f⦁ CcRpoU r ∧ Increasing r r f
	⇒ ∀z⦁ z ∈ FChainU f r ⇒ r z (f z)⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜FChainU⌝, get_spec ⌜CcRpo⌝]
	THEN REPEAT strip_tac);
a (fc_tac [ccrpou_fc_clauses, get_spec ⌜CcRpoU⌝]);
a (fc_tac [get_spec ⌜CcRpo⌝, rewrite_rule [get_spec ⌜FChainClosed⌝] (list_∀_elim [⌜Universe⌝] ccrpo_fixp_lemma4)]);
a (list_spec_nth_asm_tac 2 [⌜z⌝]);
a (SYM_ASMS_T rewrite_tac);
val ccrpou_fchainu_lemma1 = save_pop_thm "ccrpou_fchainu_lemma1";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Extreme⦎ : (('a → 'a) × ('a SET × ('a → 'a → BOOL))) → 'a SET
├───────────
│ ∀ f X $≤⋎v⦁ Extreme (f, X, $≤⋎v) =
│	{x | x ∈ FChain f (X, $≤⋎v) ∧ ∀y⦁ y ∈ FChain f (X, $≤⋎v)
│		⇒ y ≤⋎v x ∧ ¬ y = x ⇒ f y ≤⋎v x}
■

ⓈHOLCONST
│ ⦏S⦎ : (('a → 'a) × ('a SET × ('a → 'a → BOOL))) → 'a → 'a SET
├───────────
│ ∀ f X $≤⋎v x⦁ S (f, X, $≤⋎v) x =
│	{y | y ∈ FChain f (X, $≤⋎v) ∧ (y ≤⋎v x ∨ f x ≤⋎v y)}
■

=GFT
⦏ccrpo_fixp_lemma5⦎ =
   ⊢ ∀ X $≤⋎v f x
     ⦁ Increasing $≤⋎v $≤⋎v f
           ∧ Rpo (Universe, $≤⋎v)
           ∧ FChainClosed f (X, $≤⋎v)
           ∧ x ∈ Extreme (f, X, $≤⋎v)
         ⇒ FClosed f (S (f, X, $≤⋎v) x)

⦏ccrpo_fixp_lemma6⦎ =
   ⊢ ∀ X $≤⋎v f x
     ⦁ Increasing $≤⋎v $≤⋎v f
           ∧ Rpo (Universe, $≤⋎v)
           ∧ FChainClosed f (X, $≤⋎v)
           ∧ x ∈ Extreme (f, X, $≤⋎v)
         ⇒ ChainComplete (S (f, X, $≤⋎v) x, $≤⋎v)

⦏ccrpo_fixp_lemma7⦎ =
   ⊢ ∀ X $≤⋎v f x
     ⦁ Increasing $≤⋎v $≤⋎v f
           ∧ Rpo (Universe, $≤⋎v)
           ∧ FChainClosed f (X, $≤⋎v)
           ∧ x ∈ Extreme (f, X, $≤⋎v)
         ⇒ FChainClosed f (S (f, X, $≤⋎v) x, $≤⋎v)

⦏ccrpo_fixp_lemma8⦎ =
   ⊢ ∀ X $≤⋎v f
     ⦁ Increasing $≤⋎v $≤⋎v f
           ∧ Rpo (Universe, $≤⋎v)
           ∧ FChainClosed f (X, $≤⋎v)
           ∧ x ∈ Extreme (f, X, $≤⋎v)
         ⇒ FChain f (X, $≤⋎v) = S (f, X, $≤⋎v) x
=TEX

\ignore{
=SML
set_goal([], ⌜∀X $≤⋎v f x⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FChainClosed f (X, $≤⋎v) ∧ x ∈ Extreme (f, X, $≤⋎v)
	⇒ FClosed f (S (f, X, $≤⋎v) x)⌝);
a (rewrite_tac (map get_spec [⌜FClosed⌝, ⌜S⌝, ⌜Extreme⌝])
	THEN REPEAT_N 7 strip_tac);
(* *** Goal "1" *** *)
a (ALL_FC_T rewrite_tac [fc_fcclosed_fc_lemma]);
a (cases_tac ⌜x' = x⌝ THEN1 var_elim_asm_tac ⌜x' = x⌝);
(* *** Goal "1.1" *** *)
a (fc_tac [get_spec ⌜Increasing⌝]
	THEN all_asm_fc_tac []
	THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (all_asm_fc_tac[] THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (ALL_FC_T rewrite_tac [fc_fcclosed_fc_lemma]);
a (lemma_tac ⌜x ≤⋎v (f x) ∨ x = f x⌝
	THEN1 (FC_T (MAP_EVERY (strip_asm_tac o (list_∀_elim [⌜X⌝, ⌜x⌝]))) [ccrpo_fixp_lemma4]
		THEN REPEAT strip_tac));
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜x' ≤⋎v (f x') ∨ x' = f x'⌝
	THEN1 (FC_T (MAP_EVERY (strip_asm_tac o (list_∀_elim [⌜X⌝, ⌜x'⌝]))) [ccrpo_fixp_lemma4]
		THEN REPEAT strip_tac));
(* *** Goal "2.1.1" *** *)
a (FC_T (MAP_EVERY(strip_asm_tac o (rewrite_rule[]))) [rpo_fc_clauses]);
a (all_asm_fc_tac[] THEN contr_tac);
(* *** Goal "2.1.2" *** *)
a (SYM_ASMS_T rewrite_tac);
(* *** Goal "2.2" *** *)
a (lemma_tac ⌜x ≤⋎v x'⌝
	THEN1 (GET_NTH_ASM_T 2 ante_tac
		THEN (POP_ASM_T (rewrite_thm_tac o map_eq_sym_rule))
		THEN strip_tac));
a (all_fc_tac [get_spec ⌜Increasing⌝]);
a (contr_tac);
val ccrpo_fixp_lemma5 = pop_thm ();

set_goal([], ⌜∀X $≤⋎v f x⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FChainClosed f (X, $≤⋎v) ∧ x ∈ Extreme (f, X, $≤⋎v)
	⇒ ChainComplete (S (f, X, $≤⋎v) x, $≤⋎v)⌝);
a (rewrite_tac (map get_spec [⌜ChainComplete⌝, ⌜S⌝, ⌜Extreme⌝])
	THEN REPEAT_N 7 strip_tac);
a (lemma_tac ⌜Y ⊆ FChain f (X, $≤⋎v)⌝);
(* *** Goal "1" *** *)
a (GET_NTH_ASM_T 2 (asm_tac o (pc_rule1 "hol1" rewrite_rule[]))); 
a (PC_T "hol1" (REPEAT strip_tac));
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac [fchain_fchainclosed_lemma2]);
a (all_fc_tac [get_spec ⌜FChainClosed⌝]);
a (all_fc_tac [get_spec ⌜ChainComplete⌝]);
a (∃_tac ⌜x'⌝
	THEN asm_rewrite_tac[]);
a (cases_tac ⌜∀c⦁ c ∈ Y ⇒ c ≤⋎v x⌝);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜x' ≤⋎v x⌝);
(* *** Goal "2.1.1" *** *)
a (lemma_tac ⌜IsUb $≤⋎v Y x⌝
	THEN1 (rewrite_tac [get_spec ⌜IsUb⌝]
		THEN REPEAT strip_tac THEN asm_fc_tac[]));
a (all_fc_tac [get_spec ⌜IsLub⌝]);
(* *** Goal "2.1.2" *** *)
a (contr_tac);
(* *** Goal "2.2" *** *)
a (DROP_NTH_ASM_T 12 (asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (all_asm_fc_tac[]);
a (all_fc_tac[get_spec ⌜IsLub⌝]);
a (all_fc_tac[get_spec ⌜IsUb⌝]);
a (all_fc_tac[rpou_fc_clauses]);
a contr_tac;
val ccrpo_fixp_lemma6 = pop_thm ();

set_goal([], ⌜∀X $≤⋎v f x⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FChainClosed f (X, $≤⋎v) ∧ x ∈ Extreme (f, X, $≤⋎v)
	⇒ FChainClosed f (S (f, X, $≤⋎v) x, $≤⋎v)⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜FChainClosed⌝]
	THEN all_fc_tac [ccrpo_fixp_lemma5]
	THEN all_fc_tac [ccrpo_fixp_lemma6]
	THEN contr_tac);
val ccrpo_fixp_lemma7 = pop_thm ();

set_goal([], ⌜∀X $≤⋎v f⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FChainClosed f (X, $≤⋎v) ∧ x ∈ Extreme (f, X, $≤⋎v)
	⇒ FChain f (X, $≤⋎v) = S (f, X, $≤⋎v)  x⌝);
a (REPEAT strip_tac
	THEN all_fc_tac [ccrpo_fixp_lemma7]);
a (all_fc_tac[get_spec ⌜FChainClosed⌝]);
a (PC_T1 "hol1" rewrite_tac [] THEN REPEAT strip_tac
	THEN EXTEND_PC_T1 "'mmp1" all_fc_tac [get_spec ⌜FClosed⌝]);
(* *** Goal "1" *** *)
a (lemma_tac ⌜S (f, X, $≤⋎v) x ⊆ FChain f (X, $≤⋎v)⌝
	THEN1 (rewrite_tac [get_spec ⌜S⌝]
		THEN PC_T "hol1" (REPEAT strip_tac)));
a (all_fc_tac [fchain_lemma2]
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac
	THEN rewrite_tac [get_spec ⌜S⌝]
		THEN PC_T "hol1" (REPEAT strip_tac));
val ccrpo_fixp_lemma8 = pop_thm();
=TEX
}%ignore

=GFT
⦏ccrpo_fixp_lemma9⦎ =
   ⊢ ∀ X $≤⋎v f
     ⦁ Increasing $≤⋎v $≤⋎v f
           ∧ Rpo (Universe, $≤⋎v)
           ∧ FChainClosed f (X, $≤⋎v)
         ⇒ FClosed f (Extreme (f, X, $≤⋎v))

⦏ccrpo_fixp_lemma10⦎ =
   ⊢ ∀ X $≤⋎v f
     ⦁ Increasing $≤⋎v $≤⋎v f
           ∧ Rpo (Universe, $≤⋎v)
           ∧ FChainClosed f (X, $≤⋎v)
         ⇒ ChainComplete (Extreme (f, X, $≤⋎v), $≤⋎v)

⦏ccrpo_fixp_lemma11⦎ =
   ⊢ ∀ X $≤⋎v f x
     ⦁ Increasing $≤⋎v $≤⋎v f
           ∧ Rpo (Universe, $≤⋎v)
           ∧ FChainClosed f (X, $≤⋎v)
         ⇒ FChainClosed f (Extreme (f, X, $≤⋎v), $≤⋎v)

⦏ccrpo_fixp_lemma12⦎ =
   ⊢ ∀ X $≤⋎v f
     ⦁ Increasing $≤⋎v $≤⋎v f
           ∧ Rpo (Universe, $≤⋎v)
           ∧ FChainClosed f (X, $≤⋎v)
         ⇒ FChain f (X, $≤⋎v) = Extreme (f, X, $≤⋎v)
=TEX



\ignore{
=SML
set_goal([], ⌜∀X $≤⋎v f⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FChainClosed f (X, $≤⋎v)
	⇒ FClosed f (Extreme (f, X, $≤⋎v))⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜FClosed⌝]
	THEN REPEAT strip_tac);
a (GET_NTH_ASM_T 1 ante_tac THEN rewrite_tac [get_spec ⌜Extreme⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [fchain_fchainclosed_lemma2]);
a (all_fc_tac [get_spec ⌜FChainClosed⌝]);
a (all_fc_tac [get_spec ⌜FClosed⌝]);
(* *** Goal "2" *** *)
a (all_fc_tac [ccrpo_fixp_lemma8]);
a (GET_NTH_ASM_T 4 ante_tac
	THEN GET_NTH_ASM_T 1 rewrite_thm_tac
	THEN rewrite_tac [get_spec ⌜S⌝]
	THEN strip_tac); 
(* *** Goal "2.1" *** *)
a (all_fc_tac [get_spec ⌜Increasing⌝]);
(* *** Goal "2.2" *** *)
a (all_fc_tac [rpou_fc_clauses]);
val ccrpo_fixp_lemma9 = pop_thm ();

set_goal([], ⌜∀X $≤⋎v f⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FChainClosed f (X, $≤⋎v)
	⇒ ChainComplete (Extreme (f, X, $≤⋎v), $≤⋎v)⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜ChainComplete⌝]
	THEN REPEAT strip_tac);
a (GET_NTH_ASM_T 2 (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule [get_spec ⌜Extreme⌝])));
a (lemma_tac ⌜Y ⊆ FChain f (X, $≤⋎v)⌝
	THEN1 (PC_T "hol1" (REPEAT strip_tac)
		THEN asm_fc_tac[]));
a (all_fc_tac [fchain_fchainclosed_lemma2]);
a (all_fc_tac [get_spec ⌜FChainClosed⌝]);
a (all_fc_tac [get_spec ⌜ChainComplete⌝]);
a (∃_tac ⌜x⌝
	THEN asm_rewrite_tac[]);
a (rewrite_tac [get_spec ⌜Extreme⌝]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜∃b⦁ b ∈ Y ∧ ¬ b ≤⋎v y⌝
	THEN1 contr_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜IsUb $≤⋎v Y y⌝
	THEN1 rewrite_tac [get_spec ⌜IsUb⌝]);
(* *** Goal "1.1" *** *)
a (REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜x'⌝);
(* *** Goal "1.2" *** *)
a (fc_tac [list_∀_elim [⌜$≤⋎v⌝, ⌜Y⌝, ⌜x⌝] (get_spec ⌜IsLub⌝)]);
a (spec_nth_asm_tac 2 ⌜y⌝);
a (all_fc_tac [rpou_fc_clauses]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜b ∈ Extreme (f, X, $≤⋎v)⌝
	THEN1 (GET_NTH_ASM_T 16 ante_tac
	THEN PC_T1 "hol1" rewrite_tac[]
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]));
a (all_fc_tac [ccrpo_fixp_lemma8]);
a (GET_NTH_ASM_T 7 ante_tac
	THEN GET_NTH_ASM_T 1 rewrite_thm_tac
	THEN rewrite_tac [get_spec ⌜S⌝]
	THEN strip_tac); 
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜¬ y = b⌝
	THEN1 (contr_tac
		THEN all_fc_tac [rpou_fc_clauses]
		THEN var_elim_nth_asm_tac 2
		THEN asm_fc_tac[]));
a (GET_NTH_ASM_T 4 (strip_asm_tac o (rewrite_rule [get_spec ⌜Extreme⌝])));
a (lemma_tac ⌜f y ≤⋎v b⌝ THEN1 all_asm_fc_tac[]);
a (lemma_tac ⌜b ≤⋎v x⌝);
(* *** Goal "2.1.1" *** *)
a (lemma_tac ⌜IsUb $≤⋎v Y x⌝  THEN1 fc_tac [get_spec ⌜IsLub⌝]);
a (POP_ASM_T (asm_tac o (rewrite_rule [get_spec ⌜IsUb⌝])));
a (asm_fc_tac[]);
(* *** Goal "2.1.2" *** *)
a (all_fc_tac [rpou_fc_clauses]);
(* *** Goal "2.2" *** *)
a (lemma_tac ⌜b ∈ FChain f (X, $≤⋎v)⌝
	THEN1 (GET_NTH_ASM_T 16 (fn x => fc_tac [pc_rule1 "hol1" rewrite_rule [] x])));
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜$≤⋎v⌝, ⌜f⌝] ccrpo_fixp_lemma4));
a (spec_nth_asm_tac 1 ⌜b⌝);
(* *** Goal "2.2.1" *** *)
a (all_fc_tac [rpou_fc_clauses]);
(* *** Goal "2.2.2" *** *)
a (DROP_NTH_ASM_T 4 ante_tac
	THEN SYM_ASMS_T rewrite_tac
	THEN contr_tac);
val ccrpo_fixp_lemma10 = pop_thm ();

set_goal([], ⌜∀X $≤⋎v f x⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FChainClosed f (X, $≤⋎v) 
	⇒ FChainClosed f (Extreme (f, X, $≤⋎v), $≤⋎v)⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜FChainClosed⌝]
	THEN all_fc_tac [ccrpo_fixp_lemma9]
	THEN all_fc_tac [ccrpo_fixp_lemma10]
	THEN contr_tac);
val ccrpo_fixp_lemma11 = pop_thm ();

set_goal([], ⌜∀X $≤⋎v f⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FChainClosed f (X, $≤⋎v)
	⇒ FChain f (X, $≤⋎v) = Extreme (f, X, $≤⋎v)⌝);
a (REPEAT strip_tac
	THEN all_fc_tac [ccrpo_fixp_lemma7]);
a (all_fc_tac[get_spec ⌜FChainClosed⌝]);
a (PC_T1 "hol1" rewrite_tac [] THEN REPEAT strip_tac
	THEN all_fc_tac [get_spec ⌜FClosed⌝]);
(* *** Goal "1" *** *)
a (lemma_tac ⌜Extreme (f, X, $≤⋎v) ⊆ FChain f (X, $≤⋎v)⌝
	THEN1 (rewrite_tac [get_spec ⌜Extreme⌝]
		THEN PC_T "hol1" (REPEAT strip_tac)));
a (all_fc_tac [ccrpo_fixp_lemma11]);
a (all_fc_tac [fchain_lemma2]
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac
	THEN rewrite_tac [get_spec ⌜Extreme⌝]
		THEN PC_T "hol1" (REPEAT strip_tac));
val ccrpo_fixp_lemma12 = pop_thm();
=TEX
}%ignore
 
The above result may be rendered as a property of $FChainU$s (which we need to prove the ``course of values'' induction principle).

=GFT
⦏ccrpou_fchainu_lemma2⦎ =
   ⊢ ∀ $≤⋎v f
     ⦁ CcRpoU $≤⋎v ∧ Increasing $≤⋎v $≤⋎v f
         ⇒ (∀ x y
         ⦁ x ∈ FChainU f $≤⋎v ∧ y ∈ FChainU f $≤⋎v
             ⇒ y ≤⋎v x ∧ ¬ y = x
             ⇒ f y ≤⋎v x)

⦏ccrpou_fchainu_lemma2b⦎ =
   ⊢ ∀ $≤⋎v f
     ⦁ CcRpoU $≤⋎v ∧ Increasing $≤⋎v $≤⋎v f
         ⇒ (∀ x y
         ⦁ x ∈ FChainU f $≤⋎v ∧ y ∈ FChainU f $≤⋎v
             ⇒ y ≤⋎v x ∧ ¬ x ≤⋎v y
             ⇒ f y ≤⋎v x)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀$≤⋎v f⦁ CcRpoU $≤⋎v ∧ Increasing $≤⋎v $≤⋎v f
	⇒ ∀x y⦁ x ∈ FChainU f $≤⋎v ∧ y ∈ FChainU f $≤⋎v
	   ⇒ y ≤⋎v x ∧ ¬ y = x ⇒ f y ≤⋎v x⌝);
a (REPEAT ∀_tac
	THEN REPEAT strip_tac);
a (fc_tac [get_spec ⌜CcRpoU⌝]);
a (fc_tac [get_spec ⌜CcRpo⌝]);
a (fc_tac [rewrite_rule [get_spec ⌜FChainClosed⌝, get_spec ⌜Extreme⌝] ccrpo_fixp_lemma12]);
a (LIST_SPEC_NTH_ASM_T 1 [⌜Universe⌝] (strip_asm_tac o (rewrite_rule[])));
a (POP_ASM_T ante_tac);
a (rewrite_tac [sets_ext_clauses, ∈_in_clauses]);
a (strip_tac);
a (SPEC_NTH_ASM_T 1 ⌜x⌝ ante_tac);
a (GET_NTH_ASM_T 9 (rewrite_thm_tac o (rewrite_rule [get_spec ⌜FChainU⌝])));
a (STRIP_T (strip_asm_tac o (∀_elim ⌜y⌝)));
a (POP_ASM_T ante_tac);
a (GET_NTH_ASM_T 8 (rewrite_thm_tac o (rewrite_rule [get_spec ⌜FChainU⌝])));
val ccrpou_fchainu_lemma2 = save_pop_thm "ccrpou_fchainu_lemma2";

set_goal ([], ⌜∀$≤⋎v f⦁ CcRpoU $≤⋎v ∧ Increasing $≤⋎v $≤⋎v f
	⇒ ∀x y⦁ x ∈ FChainU f $≤⋎v ∧ y ∈ FChainU f $≤⋎v
	   ⇒ y ≤⋎v x ∧ ¬ x ≤⋎v y ⇒ f y ≤⋎v x⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜¬ y = x⌝
	THEN1 (fc_tac [ccrpou_fc_clauses]
		THEN swap_nth_asm_concl_tac 5
		THEN asm_rewrite_tac []));
a (all_fc_tac [ccrpou_fchainu_lemma2]);
val ccrpou_fchainu_lemma2b = save_pop_thm "ccrpou_fchainu_lemma2b";
=TEX
}%ignore

=GFT
⦏ccrpo_fixp_lemma13⦎ =
   ⊢ ∀ X $≤⋎v f
     ⦁ Increasing $≤⋎v $≤⋎v f
           ∧ Rpo (Universe, $≤⋎v)
           ∧ FChainClosed f (X, $≤⋎v)
         ⇒ FChain f (X, $≤⋎v)
           = {x
           |x ∈ Extreme (f, X, $≤⋎v) ∧ FChain f (X, $≤⋎v) ⊆ S (f, X, $≤⋎v) x}

⦏ccrpo_fixp_lemma14⦎ =
   ⊢ ∀ X $≤⋎v f
     ⦁ Increasing $≤⋎v $≤⋎v f
           ∧ Rpo (Universe, $≤⋎v)
           ∧ FChainClosed f (X, $≤⋎v)
         ⇒ (∀ x y
         ⦁ {x; y} ⊆ FChain f (X, $≤⋎v)
             ⇒ (x ≤⋎v f x ∨ x = f x)
               ∧ (y ≤⋎v x ∧ ¬ y = x ⇒ f y ≤⋎v x)
               ∧ (y ≤⋎v x ∨ f x ≤⋎v y))
=TEX

\ignore{
=SML
set_goal([], ⌜∀X $≤⋎v f⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FChainClosed f (X, $≤⋎v)
	⇒ FChain f (X, $≤⋎v) = {x | x ∈ Extreme (f, X, $≤⋎v)
		∧ FChain f (X, $≤⋎v) ⊆ S (f,X, $≤⋎v) x}⌝);
a (PC_T "hol1" (REPEAT_N 9 strip_tac));
(* *** Goal "1" *** *)
a (all_fc_tac [ccrpo_fixp_lemma12]);
a (GET_NTH_ASM_T 2 (asm_tac o (rewrite_rule [asm_rule ⌜FChain f (X, $≤⋎v) = Extreme (f, X, $≤⋎v)⌝])));
a (REPEAT strip_tac);
a (all_fc_tac [ccrpo_fixp_lemma8]
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac [ccrpo_fixp_lemma12]
	THEN asm_rewrite_tac[]);
val ccrpo_fixp_lemma13 = pop_thm();
 
set_goal([], ⌜∀X $≤⋎v f⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FChainClosed f (X, $≤⋎v)
	⇒ ∀x y⦁ {x; y} ⊆ FChain f (X, $≤⋎v)
		⇒ (y ≤⋎v x ∧ ¬ y = x ⇒ f y ≤⋎v x)
		∧ (y ≤⋎v x ∨ f x ≤⋎v y)
		⌝);
a (REPEAT_N 6 strip_tac
	THEN all_fc_tac [ccrpo_fixp_lemma13]);
a (once_asm_rewrite_tac[]);
a (rewrite_tac[get_spec ⌜Extreme⌝, get_spec ⌜S⌝]);
a (PC_T "hol1" strip_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (spec_nth_asm_tac 4 ⌜y⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 7 ⌜y⌝);
(* *** Goal "2" *** *)
a (GET_NTH_ASM_T 5 ante_tac THEN PC_T1 "hol1" rewrite_tac[]
	THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜y⌝);
val ccrpo_fixp_lemma14 = pop_thm();
 
set_goal([], ⌜∀X $≤⋎v f⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FChainClosed f (X, $≤⋎v)
	⇒ ∀x y⦁ {x; y} ⊆ FChain f (X, $≤⋎v)
		⇒ (x ≤⋎v f x ∨ x = f x)
		∧ (y ≤⋎v x ∧ ¬ y = x ⇒ f y ≤⋎v x)
		∧ (y ≤⋎v x ∨ f x ≤⋎v y)
		⌝);
a (REPEAT_N 6 strip_tac
	THEN all_fc_tac [ccrpo_fixp_lemma13]);
a (once_asm_rewrite_tac[]);
a (rewrite_tac[get_spec ⌜Extreme⌝, get_spec ⌜S⌝]);
a (PC_T "hol1" strip_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (spec_nth_asm_tac 4 ⌜y⌝);
a (strip_tac);
(* *** Goal "1" *** *)
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜$≤⋎v⌝, ⌜f⌝] ccrpo_fixp_lemma4));
a (spec_nth_asm_tac 1 ⌜x⌝ THEN contr_tac);
(* *** Goal "2" *** *)
a (REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (spec_nth_asm_tac 7 ⌜y⌝);
(* *** Goal "2.2" *** *)
a (GET_NTH_ASM_T 5 ante_tac THEN PC_T1 "hol1" rewrite_tac[]
	THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜y⌝);
val ccrpo_fixp_lemma14 = pop_thm();
=TEX
}%ignore

=GFT
⦏ccrpo_fixp_lemma15⦎ =
   ⊢ ∀ X $≤⋎v f
     ⦁ Increasing $≤⋎v $≤⋎v f
           ∧ Rpo (Universe, $≤⋎v)
           ∧ FChainClosed f (X, $≤⋎v)
         ⇒ Trich (FChain f (X, $≤⋎v), $≤⋎v)

⦏ccrpo_fixp_lemma16⦎ =
   ⊢ ∀ X $≤⋎v f
     ⦁ Increasing $≤⋎v $≤⋎v f
           ∧ Rpo (Universe, $≤⋎v)
           ∧ FChainClosed f (X, $≤⋎v)
         ⇒ LinearOrder (FChain f (X, $≤⋎v), $≤⋎v)
=TEX

\ignore{
=SML
set_goal([], ⌜∀X $≤⋎v f⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FChainClosed f (X, $≤⋎v)
	⇒ Trich (FChain f (X, $≤⋎v), $≤⋎v)	⌝);
a (REPEAT ∀_tac);
a (REPEAT strip_tac
	THEN strip_asm_tac (list_∀_elim [⌜X⌝, ⌜$≤⋎v⌝, ⌜f⌝] ccrpo_fixp_lemma14)
	THEN rewrite_tac [get_spec ⌜Trich⌝]
	THEN REPEAT strip_tac);
a (PC_T "hol1" (list_spec_nth_asm_tac 5 [⌜x⌝, ⌜y⌝])
	THEN_TRY (var_elim_nth_asm_tac 2));
(* *** Goal "1" *** *)
a (all_fc_tac [rpou_fc_clauses]);
(* *** Goal "2" *** *)
a (all_fc_tac [rpou_fc_clauses]);
(* *** Goal "3" *** *)
a (POP_ASM_T ante_tac
	THEN SYM_ASMS_T rewrite_tac);
(* *** Goal "4" *** *)
a (POP_ASM_T ante_tac
	THEN SYM_ASMS_T rewrite_tac);
val ccrpo_fixp_lemma15 = pop_thm();

set_goal([], ⌜∀X $≤⋎v f⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FChainClosed f (X, $≤⋎v)
	⇒ LinearOrder (FChain f (X, $≤⋎v), $≤⋎v)⌝);
a (REPEAT strip_tac
	THEN all_asm_fc_tac [ccrpo_fixp_lemma15]
	THEN rewrite_tac [get_spec ⌜LinearOrder⌝]
	THEN REPEAT strip_tac);
a (fc_tac [get_spec ⌜Rpo⌝]);
a (LEMMA_T ⌜FChain f (X, $≤⋎v) ⊆ Universe⌝ asm_tac THEN1 PC_T1 "hol1" prove_tac[]);
a (all_fc_tac [subrel_partial_order_thm]);
val ccrpo_fixp_lemma16 = pop_thm ();
=TEX
}%ignore


=GFT
⦏ccrpou_fchainu_linear_lemma⦎ =
   ⊢ ∀ $≤⋎v f
     ⦁ CcRpoU $≤⋎v ∧ Increasing $≤⋎v $≤⋎v f
         ⇒ LinearOrder (FChainU f $≤⋎v, $≤⋎v)

⦏ccrpou_fchainu_linear_lemma2⦎ =
   ⊢ ∀ X $≤⋎v f
     ⦁ CcRpoU $≤⋎v ∧ Increasing $≤⋎v $≤⋎v f
         ⇒ (∀ X⦁ X ⊆ FChainU f $≤⋎v ⇒ LinearOrder (X, $≤⋎v))

⦏ccrpou_fchainu_lemma2c⦎ =
   ⊢ ∀ $≤⋎v f
     ⦁ CcRpoU $≤⋎v ∧ Increasing $≤⋎v $≤⋎v f
         ⇒ (∀ x y
         ⦁ x ∈ FChainU f $≤⋎v ∧ y ∈ FChainU f $≤⋎v ⇒ y ≤⋎v x ∨ f x ≤⋎v y)
=TEX

\ignore{
=SML
set_goal([], ⌜∀$≤⋎v f⦁ CcRpoU $≤⋎v ∧ Increasing $≤⋎v $≤⋎v f
	⇒ LinearOrder (FChainU f $≤⋎v, $≤⋎v)⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜CcRpoU⌝]);
a (fc_tac [get_spec ⌜CcRpo⌝]);
a (fc_tac [list_∀_elim [⌜Universe⌝] (rewrite_rule [get_spec ⌜FChainClosed⌝] ccrpo_fixp_lemma16)]);
a (asm_rewrite_tac[get_spec ⌜FChainU⌝]);
val ccrpou_fchainu_linear_lemma = save_pop_thm "ccrpou_fchainu_linear_lemma";

set_goal([], ⌜∀X $≤⋎v f⦁ CcRpoU $≤⋎v ∧ Increasing $≤⋎v $≤⋎v f
	⇒ ∀X⦁ X ⊆ FChainU f $≤⋎v ⇒ LinearOrder (X, $≤⋎v)⌝);
a (REPEAT strip_tac THEN all_asm_fc_tac [ccrpou_fchainu_linear_lemma]);
a (all_fc_tac [subrel_linear_order_thm]);
val ccrpou_fchainu_linear_lemma2 = save_pop_thm "ccrpou_fchainu_linear_lemma2";

set_goal ([], ⌜∀$≤⋎v f⦁ CcRpoU $≤⋎v ∧ Increasing $≤⋎v $≤⋎v f
	⇒ ∀x y⦁ x ∈ FChainU f $≤⋎v ∧ y ∈ FChainU f $≤⋎v
	   ⇒ y ≤⋎v x ∨ f x ≤⋎v y⌝);
a (REPEAT strip_tac);
a (fc_tac [ccrpou_fc_clauses]);
a (fc_tac [ccrpou_fchainu_lemma2]);
a (list_spec_nth_asm_tac 1 [⌜f⌝, ⌜y⌝, ⌜x⌝]);
(* *** Goal "1" *** *)
a (all_fc_tac [ccrpou_fchainu_linear_lemma]);
a (fc_tac [get_spec ⌜LinearOrder⌝]);
a (fc_tac [get_spec ⌜Trich⌝]);
a (list_spec_nth_asm_tac 1 [⌜y⌝, ⌜x⌝]);
a (var_elim_asm_tac ⌜y = x⌝
	THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (var_elim_asm_tac ⌜x = y⌝
	THEN all_asm_fc_tac[]);
val ccrpou_fchainu_lemma2c = save_pop_thm "ccrpou_fchainu_lemma2c";
=TEX
}%ignore

We now pause to prove the course of values induction principle, deferred to this point because this formulation requires the above result (though this induction principle is not used in the fixedpoint proof which predates it).

It is interesting perhaps that this is the first of the principles for induction over $FChain$s which depends upon the monoticity of the function $f$ which generates the chain.

=GFT
⦏fchainu_induction_thm2⦎ =
   ⊢ ∀ r f p
     ⦁ CcRpoU r
           ∧ Increasing r r f
           ∧ (∀ x
           ⦁ x ∈ FChainU f r ∧ (∀ y⦁ y ∈ FChainU f r ∧ r y x ∧ ¬ r x y ⇒ p y)
               ⇒ p x)
         ⇒ (∀ x⦁ x ∈ FChainU f r ⇒ p x)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r f p⦁ CcRpoU r ∧ Increasing r r f
	∧ (∀x⦁ x ∈ FChainU f r ∧ (∀y⦁ y ∈ FChainU f r ∧ r y x ∧ ¬ r x y ⇒ p y) ⇒ p x)
	⇒ ∀x⦁ x ∈ FChainU f r ⇒ p x⌝);
a (REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim [⌜r⌝, ⌜f⌝,
	⌜λz⦁ (∀ x⦁ x ∈ FChainU f r ∧ r x z
			∧ (∀ y⦁ y ∈ FChainU f r ∧ r y x ∧ ¬ r x y ⇒ p y)
			⇒ p x)
		⇒ (∀x⦁ x ∈ FChainU f r ∧ r x z ⇒ p x)⌝]
	fchainu_induction_thm1));
(* *** Goal "1" *** *)
a (swap_nth_asm_concl_tac 1 THEN rewrite_tac[] THEN REPEAT strip_tac);
a (DROP_NTH_ASM_T 5 (strip_asm_tac o (rewrite_rule[])));
(* *** Goal "1.1" *** *)
a (lemma_tac ⌜r x' (f x')⌝ THEN1 (all_fc_tac [ccrpou_fchainu_lemma1]));
a (lemma_tac ⌜r x''' (f x')⌝ THEN1 (fc_tac [ccrpou_fc_clauses] THEN all_asm_fc_tac []));
a (all_asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a (spec_nth_asm_tac 1 ⌜x''⌝);
a (lemma_tac ⌜f x' ∈ FChainU f r⌝ THEN1 (fc_tac [fchainu_lemma1]));
a (strip_asm_tac (list_∀_elim [⌜r⌝, ⌜f⌝] ccrpou_fchainu_lemma2));
a (list_spec_nth_asm_tac 1 [⌜x''⌝, ⌜x'⌝]);
(* *** Goal "1.2.1" *** *)
a (all_fc_tac [ccrpou_fchainu_linear_lemma]);
a (fc_tac [get_spec ⌜LinearOrder⌝]);
a (fc_tac [get_spec ⌜Trich⌝]);
a (list_spec_nth_asm_tac 1 [⌜x'⌝, ⌜x''⌝]);
a (var_elim_nth_asm_tac 1);
a (all_fc_tac [ccrpou_fc_clauses]);
a (all_asm_fc_tac[]);
(* *** Goal "1.2.2" *** *)
a (var_elim_nth_asm_tac 1);
a (all_fc_tac [ccrpou_fc_clauses]);
a (all_asm_fc_tac[]);
(* *** Goal "1.2.3" *** *)
a (fc_tac [ccrpou_fc_clauses]);
a (all_asm_fc_tac []);
a (var_elim_nth_asm_tac 3);
a (spec_nth_asm_tac 14 ⌜f x'⌝);
a (lemma_tac ⌜r y x'⌝ THEN_LIST
	[list_spec_nth_asm_tac 9 [⌜y⌝, ⌜x'⌝],
	all_asm_fc_tac[]]);
(* *** Goal "1.2.3.1" *** *)
a (all_fc_tac [ccrpou_fchainu_linear_lemma]);
a (fc_tac [get_spec ⌜LinearOrder⌝]);
a (fc_tac [get_spec ⌜Trich⌝]);
a (list_spec_nth_asm_tac 1 [⌜x'⌝, ⌜y⌝]);
a (asm_rewrite_tac[]);
(* *** Goal "1.2.3.2" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (swap_nth_asm_concl_tac 1 THEN rewrite_tac[]);
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule[])));
a (REPEAT strip_tac);
a (spec_nth_asm_tac 8 ⌜x'⌝);
a (lemma_tac ⌜∃z⦁ z ∈ s ∧ r y z⌝);
(* *** Goal "2.1" *** *)
a (all_fc_tac [ccrpou_fchainu_linear_lemma]);
a (fc_tac [ccrpou_fc_clauses]);
a (fc_tac [lin_refl_lub_lemma]);
a (lemma_tac ⌜Refl (FChainU f r, r)⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜Refl⌝] THEN REPEAT strip_tac THEN asm_rewrite_tac[]));
a (lemma_tac ⌜LinearOrder (s, r)⌝ THEN1 (all_fc_tac [subrel_linear_order_thm]));
a (lemma_tac ⌜(Lub r s) ∈ FChainU f r⌝);
(* *** Goal "2.1.1" *** *)
a (strip_asm_tac (list_∀_elim [⌜r⌝, ⌜f⌝] (ccrpou_fcclosed_fc_lemma)));
a (fc_tac [get_spec ⌜FChainClosed⌝]);
a (fc_tac [get_spec ⌜ChainComplete⌝]);
a (lemma_tac ⌜Lub r s ∈ FChainU f r⌝
	THEN1 (all_fc_tac [ccrpou_fcclosed_fc_lemma2]));
(* *** Goal "2.1.2" *** *)
a (lemma_tac ⌜IsLub r s (Lub r s)⌝ THEN1 (all_fc_tac [ccrpou_lub_lemma]));
a (lemma_tac ⌜r y (Lub r s)⌝ THEN1 (all_asm_fc_tac[]));
a (lemma_tac ⌜¬ r (Lub r s) y⌝ THEN1 (contr_tac THEN all_asm_fc_tac[]));
a (list_spec_nth_asm_tac 7 [⌜s⌝, ⌜Lub r s⌝, ⌜y⌝]);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (lemma_tac ⌜(∀x⦁ x ∈ FChainU f r ∧ r x z
		∧ (∀ y⦁ y ∈ FChainU f r ∧ r y x ∧ ¬ r x y ⇒ p y)
		⇒ p x)⌝
	THEN1 REPEAT strip_tac
	THEN all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac [] THEN strip_tac);
(* *** Goal "3.1" *** *)
a (all_asm_fc_tac []);
(* *** Goal "3.2" *** *)
a (fc_tac [ccrpou_fc_clauses]);
a (asm_fc_tac []);
a (asm_fc_tac []);
val fchainu_induction_thm2 = save_pop_thm "fchainu_induction_thm2";
=TEX
}%ignore


Now we return to the proof of the fixedpoint theorem.

=GFT
⦏ccrpo_fixp_lemma17⦎ =
   ⊢ ∀ X $≤⋎v f
     ⦁ Increasing $≤⋎v $≤⋎v f
           ∧ Rpo (Universe, $≤⋎v)
           ∧ FChainClosed f (X, $≤⋎v)
         ⇒ (∃ e
         ⦁ IsLub $≤⋎v (FChain f (X, $≤⋎v)) e
             ∧ e = f e
             ∧ e ∈ FChain f (X, $≤⋎v))
=TEX

\ignore{
=SML
set_goal([], ⌜∀X $≤⋎v f⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FChainClosed f (X, $≤⋎v)
	⇒ ∃e⦁ IsLub $≤⋎v (FChain f (X, $≤⋎v)) e ∧ e = f e ∧ e ∈ FChain f (X, $≤⋎v)⌝);
a (REPEAT strip_tac);
a (all_fc_tac [fchain_fchainclosed_lemma2]);
a (fc_tac[fchain_lemma1]);
a (all_fc_tac [ccrpo_fixp_lemma16]);
a (all_fc_tac [get_spec ⌜FChainClosed⌝]);
a (LEMMA_T ⌜FChain f (X, $≤⋎v) ⊆ FChain f (X, $≤⋎v)⌝ asm_tac
	THEN1 PC_T1 "hol1" prove_tac[]);
a (all_fc_tac [get_spec ⌜ChainComplete⌝]);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
a (lemma_tac ⌜f x ∈ FChain f (X, $≤⋎v)⌝
	THEN1 (all_fc_tac [get_spec ⌜FClosed⌝]));
a (strip_asm_tac (list_∀_elim [⌜X⌝, ⌜$≤⋎v⌝, ⌜f⌝] ccrpo_fixp_lemma4));
a (spec_nth_asm_tac 1 ⌜x⌝);
a (lemma_tac ⌜f x ≤⋎v x⌝);
a (all_fc_tac [get_spec ⌜IsLub⌝]);
a (strip_asm_tac (list_∀_elim [⌜$≤⋎v⌝, ⌜FChain f (X, $≤⋎v)⌝, ⌜x⌝]
			(get_spec ⌜IsUb⌝)));
(* *** Goal "1.1" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac [rpou_fc_clauses]);
val ccrpo_fixp_lemma17 = pop_thm ();
=TEX
}%ignore

=GFT
⦏ccrpo_fixp_lemma18⦎ =
   ⊢ ∀ X $≤⋎v f
     ⦁ Increasing $≤⋎v $≤⋎v f
           ∧ Rpo (Universe, $≤⋎v)
           ∧ FChainClosed f (X, $≤⋎v)
         ⇒ (∃ l⦁ IsLub $≤⋎v (FChain f (X, $≤⋎v)) l ∧ IsLfp $≤⋎v f l)

⦏ccrpou_fchainu_lfp_lemma⦎ =
   ⊢ ∀ X $≤⋎v f
     ⦁ CcRpoU $≤⋎v ∧ Increasing $≤⋎v $≤⋎v f
         ⇒ (∃ l⦁ IsLub $≤⋎v (FChainU f $≤⋎v) l ∧ IsLfp $≤⋎v f l)

⦏ccrpo_fixp_lemma19⦎ =
   ⊢ ∀ r f⦁ CcRpo (Universe, r) ∧ Increasing r r f ⇒ (∃ e⦁ IsLfp r f e)

⦏ccrpou_fixp_induction_thm⦎ =
   ⊢ ∀ r f p
     ⦁ CcRpoU r
           ∧ Increasing r r f
           ∧ (∀ x⦁ p x ⇒ p (f x))
           ∧ (∀ s
           ⦁ (∀ x⦁ x ∈ s ⇒ p x) ∧ LinearOrder (s, r)
               ⇒ (∃ y⦁ p y ∧ IsLub r s y))
         ⇒ p (Lfp⋎c r f)
=TEX


\ignore{
=SML
set_goal([], ⌜∀X $≤⋎v f⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FChainClosed f (X, $≤⋎v)
	⇒ ∃l⦁ IsLub $≤⋎v (FChain f (X, $≤⋎v)) l ∧ IsLfp $≤⋎v f l⌝);
a (REPEAT strip_tac
	THEN all_fc_tac [ccrpo_fixp_lemma17]);
a (∃_tac ⌜e⌝ THEN (SYM_ASMS_T rewrite_tac));
a (rewrite_tac [get_spec ⌜IsLfp⌝, let_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (SYM_ASMS_T rewrite_tac);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜IsGlb⌝, get_spec ⌜IsLb⌝]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜FChainClosed f ({y | y ∈ FChain f (X, $≤⋎v) ∧ y ≤⋎v x}, $≤⋎v)⌝
	THEN1 (rewrite_tac [get_spec ⌜FChainClosed⌝]
		THEN REPEAT strip_tac));
(* *** Goal "2.1.1" *** *)
a (rewrite_tac [get_spec ⌜FClosed⌝]
	THEN REPEAT strip_tac);
(* *** Goal "2.1.1.1" *** *)
a (all_fc_tac [fchain_fchainclosed_lemma2]);
a (all_fc_tac [get_spec ⌜FChainClosed⌝]);
a (all_fc_tac [get_spec ⌜FClosed⌝]);
(* *** Goal "2.1.1.2" *** *)
a (all_fc_tac [get_spec ⌜Increasing⌝]);
a (POP_ASM_T ante_tac
	THEN GET_NTH_ASM_T 3 rewrite_thm_tac);
(* *** Goal "2.1.2" *** *)
a (rewrite_tac [get_spec ⌜ChainComplete⌝]
	THEN REPEAT strip_tac);
a (all_fc_tac [fchain_fchainclosed_lemma2]);
a (all_fc_tac [get_spec ⌜FChainClosed⌝]);
a (lemma_tac ⌜Y ⊆ FChain f (X, $≤⋎v)⌝
	THEN1 (GET_NTH_ASM_T 7 ante_tac
		THEN PC_T1 "hol1" prove_tac[]));
a (all_fc_tac [get_spec ⌜ChainComplete⌝]);
a (∃_tac ⌜x'⌝ THEN REPEAT strip_tac);
a (lemma_tac ⌜IsUb $≤⋎v Y x⌝
	THEN1 (rewrite_tac [get_spec ⌜IsUb⌝]
		THEN GET_NTH_ASM_T 10 ante_tac
		THEN PC_T1 "hol1" prove_tac[]));
a (all_fc_tac [get_spec ⌜IsLub⌝]);
(* *** Goal "2.1.3" *** *)
a (lemma_tac ⌜{y|y ∈ FChain f (X, $≤⋎v) ∧ y ≤⋎v x} ⊆ FChain f (X, $≤⋎v)⌝
	THEN1 (PC_T1 "hol1" prove_tac[]));
a (all_fc_tac [fchain_lemma2]);
a (lemma_tac ⌜∀ x'⦁ x' ∈ FChain f (X, $≤⋎v) ⇒ x' ≤⋎v x⌝
	THEN1 (POP_ASM_T ante_tac THEN PC_T1 "hol1" prove_tac[]));
a (lemma_tac ⌜IsUb $≤⋎v (FChain f (X, $≤⋎v)) x⌝
	THEN1 (rewrite_tac [get_spec ⌜IsUb⌝]
		THEN REPEAT strip_tac
		THEN asm_fc_tac[]));
a (all_fc_tac [get_spec ⌜IsLub⌝]);
(* *** Goal "2.2" *** *)
a (spec_nth_asm_tac 1 ⌜e⌝);
a (POP_ASM_T ante_tac THEN SYM_ASMS_T rewrite_tac);
val ccrpo_fixp_lemma18 = pop_thm ();

set_goal([], ⌜∀X $≤⋎v f⦁ CcRpoU $≤⋎v ∧ Increasing $≤⋎v $≤⋎v f
	⇒ ∃l⦁ IsLub $≤⋎v (FChainU f $≤⋎v) l ∧ IsLfp $≤⋎v f l⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜CcRpoU⌝, get_spec ⌜CcRpo⌝]
	THEN REPEAT strip_tac);
a (LEMMA_T ⌜FChainClosed f (Universe, $≤⋎v)⌝ asm_tac
	THEN1 asm_rewrite_tac[get_spec ⌜FChainClosed⌝]);
a (all_fc_tac [ccrpo_fixp_lemma18]);
a (∃_tac ⌜l⌝ THEN asm_rewrite_tac[get_spec⌜FChainU⌝]);
val ccrpou_fchainu_lfp_lemma = save_pop_thm "ccrpou_fchainu_lfp_lemma";

set_goal([], ⌜∀r f⦁ CcRpoU r
	∧ Increasing r r f
	⇒ (∃ e⦁ IsLfp r f e)⌝);
a (REPEAT strip_tac
	THEN all_fc_tac [get_spec ⌜CcRpoU⌝]
	THEN all_fc_tac [get_spec ⌜CcRpo⌝]);
a (lemma_tac ⌜FClosed f Universe⌝
	THEN1 rewrite_tac [get_spec ⌜FClosed⌝]);
a (lemma_tac ⌜FChainClosed f (Universe, r)⌝
	THEN1 asm_rewrite_tac[get_spec⌜FChainClosed⌝]);
a (all_fc_tac [ccrpo_fixp_lemma18]);
a (∃_tac ⌜l⌝ THEN contr_tac);
val ccrpo_fixp_lemma19 = pop_thm ();

set_goal([], ⌜∀r f p⦁ CcRpoU r 
	∧ Increasing r r f
	∧ (∀x⦁ p x ⇒ p (f x))
	∧ (∀s⦁ (∀x⦁ x ∈ s ⇒ p x) ∧ LinearOrder (s, r) ⇒ ∃y⦁ p y ∧ (IsLub r s y))
	⇒ p (Lfp⋎c r f)
	⌝);
a (REPEAT strip_tac
	THEN all_fc_tac [ccrpo_fixp_lemma19]);
a (lemma_tac ⌜FChainClosed f ({x | p x}, r)⌝
	THEN1 (rewrite_tac [get_spec ⌜FChainClosed⌝]
		THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜FClosed⌝]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜ChainComplete⌝]
	THEN (PC_T1 "hol1" rewrite_tac [])
	THEN (PC_T1 "hol1" REPEAT strip_tac)
	THEN all_asm_fc_tac[]);
a (all_fc_tac [get_spec ⌜CcRpoU⌝]);
a (all_fc_tac [get_spec ⌜CcRpo⌝]);
a (fc_tac [get_spec ⌜ChainComplete⌝]);
a (POP_ASM_T (fn x => fc_tac [rewrite_rule[] x]));
a (∃_tac ⌜x⌝
	THEN asm_rewrite_tac[]);
a (all_fc_tac [rpo_antisym_lemma]);
a (all_fc_tac [lub_unique_lemma]);
a (var_elim_nth_asm_tac 1);
(* *** Goal "3" *** *)
a (FC_T (MAP_EVERY(asm_tac o (pc_rule1 "hol1" rewrite_rule[]))) [fchain_lemma1]);
a (fc_tac [get_spec ⌜FChainClosed⌝]);
a (fc_tac [get_spec ⌜CcRpoU⌝]);
a (all_fc_tac [get_spec ⌜CcRpo⌝]);
a (all_fc_tac [ccrpo_fixp_lemma16]);
a (all_asm_fc_tac[]);
a (all_fc_tac [ccrpo_fixp_lemma17]);
a (all_fc_tac [rpo_antisym_lemma]);
a (all_fc_tac [lub_unique_lemma]);
a (var_elim_asm_tac ⌜e' = y⌝);
a (all_fc_tac [ccrpo_fixp_lemma19]);
a (all_fc_tac [ccrpo_fixp_lemma18]);
a (all_fc_tac [lub_unique_lemma]);
a (var_elim_asm_tac ⌜l = y⌝);
a (lemma_tac ⌜Lfp⋎c r f = y⌝ THEN1 all_fc_tac [islfp_unique_lemma2]);
a (rewrite_tac[asm_rule ⌜Lfp⋎c r f = y⌝]);
a (contr_tac);
val ccrpou_fixp_induction_thm = save_pop_thm "ccrpou_fixp_induction_thm"; 

pop_pc();
pop_pc();
=TEX
}%ignore


The course of values induction theorem over fchains which I proved now seems to me to be more pretty than useful.
It seems unlikely that one will not want to prove the induction hypothesis separately for elements which are successors and elements which are limits.

At the least we also need a suitable cases theorem:

=GFT
⦏fchainu_cases_lemma⦎ =
   ⊢ ∀ r f
     ⦁ CcRpoU r ∧ Increasing r r f
         ⇒ (∀ x
         ⦁ x ∈ FChainU f r
             ⇒ (∃ y⦁ y ∈ FChainU f r ∧ x = f y)
               ∨ x = Lub r {z|z ∈ FChainU f r ∧ r z x ∧ ¬ r x z})

⦏fchainu_cases_lemma2⦎ =
   ⊢ ∀ r f
     ⦁ CcRpoU r ∧ Increasing r r f
         ⇒ (∀ x
         ⦁ x ∈ FChainU f r
             ⇒ (∃ y⦁ y ∈ FChainU f r ∧ ¬ y = x ∧ x = f y)
               ∨ x = Lub r {z|z ∈ FChainU f r ∧ r z x ∧ ¬ r x z})
=TEX

\ignore{
=SML
push_extend_pc "'mmp1";
set_goal([], ⌜∀r f⦁ CcRpoU r ∧ Increasing r r f ⇒ ∀x⦁ x ∈ FChainU f r
	⇒ (∃y⦁ y ∈ FChainU f r ∧ x = f y)
	∨ x = Lub r {z | z ∈ FChainU f r ∧ r z x ∧ ¬ r x z}⌝);
a (contr_tac);
a (lemma_tac ⌜IsUb r {z|z ∈ FChainU f r ∧ r z x ∧ ¬ r x z} x⌝
	THEN1 (rewrite_tac [get_spec ⌜IsUb⌝] THEN PC_T1 "hol1" prove_tac []));
a (lemma_tac ⌜{z|z ∈ FChainU f r ∧ r z x ∧ ¬ r x z} ⊆ FChainU f r⌝
	THEN1 PC_T1 "hol1" prove_tac[]);
a (lemma_tac ⌜LinearOrder ({z|z ∈ FChainU f r ∧ r z x ∧ ¬ r x z}, r)⌝
	THEN1 all_fc_tac[ccrpou_fchainu_linear_lemma2]);
a (lemma_tac ⌜∃l⦁ l = Lub r {z|z ∈ FChainU f r ∧ r z x ∧ ¬ r x z}⌝
	THEN1 prove_∃_tac);
a (lemma_tac ⌜l ∈ FChainU f r⌝
	THEN1 (asm_rewrite_tac [] THEN all_fc_tac [ccrpou_fcclosed_fc_lemma2]));
a (all_fc_tac [ccrpou_lub_lemma]);
a (POP_ASM_T ante_tac THEN (GET_NTH_ASM_T 2 (rewrite_thm_tac o eq_sym_rule))
	THEN contr_tac);
a (fc_tac [get_spec ⌜IsLub⌝]);
a (lemma_tac ⌜¬ r x l⌝	THEN1 (contr_tac
	THEN all_fc_tac [ccrpou_fc_clauses]
	THEN var_elim_asm_tac ⌜x = l⌝));
a (all_fc_tac [ccrpou_fchainu_lemma2b]);
a (lemma_tac ⌜¬ r x (f l)⌝
	THEN1 (spec_nth_asm_tac 12 ⌜l⌝
		THEN contr_tac
		THEN all_fc_tac [ccrpou_fc_clauses]));
a (lemma_tac ⌜f l ∈ FChainU f r⌝
	THEN1 (fc_tac [fchainu_lemma1]));
a (LEMMA_T ⌜f l ∈ {z|z ∈ FChainU f r ∧ r z x ∧ ¬ r x z}⌝ asm_tac
	THEN1 PC_T1 "hol1" asm_prove_tac[]);
a (GET_NTH_ASM_T 6 ante_tac
	THEN rewrite_tac [get_spec ⌜IsUb⌝]);
a (contr_tac);
a (spec_nth_asm_tac 1 ⌜f l⌝);
a (lemma_tac ⌜r l (f l)⌝ THEN1 all_fc_tac [ccrpou_fchainu_lemma1]);
a (lemma_tac ⌜l = f l⌝ THEN1 all_asm_fc_tac [ccrpou_fc_clauses]);
a (all_fc_tac [ccrpou_fchainu_lfp_lemma]);
a (FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule [let_def]))) [get_spec ⌜IsLfp⌝]);
a (fc_tac [get_spec ⌜IsGlb⌝]);
a (fc_tac [get_spec ⌜IsLb⌝]);
a (spec_nth_asm_tac 1 ⌜l⌝ THEN1 (POP_ASM_T ante_tac THEN (rewrite_tac [eq_sym_rule (asm_rule ⌜l = f l⌝)])));
a (fc_tac [get_spec ⌜IsLub⌝]);
a (lemma_tac ⌜r x l'⌝
	THEN1 (fc_tac [get_spec ⌜IsUb⌝]
		THEN all_asm_fc_tac [ccrpou_fc_clauses]
		THEN1 spec_nth_asm_tac 1 ⌜x⌝));
a (all_fc_tac [ccrpou_fc_clauses]);
val fchainu_cases_lemma = save_pop_thm "fchainu_cases_lemma";

set_goal([], ⌜∀r f⦁ CcRpoU r ∧ Increasing r r f ⇒ ∀x⦁ x ∈ FChainU f r
	⇒ (∃y⦁ y ∈ FChainU f r ∧ ¬ y = x ∧ x = f y)
	∨ x = Lub r {z | z ∈ FChainU f r ∧ r z x ∧ ¬ r x z}⌝);
a (contr_tac);
a (lemma_tac ⌜IsUb r {z|z ∈ FChainU f r ∧ r z x ∧ ¬ r x z} x⌝
	THEN1 (rewrite_tac [get_spec ⌜IsUb⌝] THEN PC_T1 "hol1" prove_tac []));
a (lemma_tac ⌜{z|z ∈ FChainU f r ∧ r z x ∧ ¬ r x z} ⊆ FChainU f r⌝
	THEN1 PC_T1 "hol1" prove_tac[]);
a (lemma_tac ⌜LinearOrder ({z|z ∈ FChainU f r ∧ r z x ∧ ¬ r x z}, r)⌝
	THEN1 all_fc_tac[ccrpou_fchainu_linear_lemma2]);
a (lemma_tac ⌜∃l⦁ l = Lub r {z|z ∈ FChainU f r ∧ r z x ∧ ¬ r x z}⌝
	THEN1 prove_∃_tac);
a (lemma_tac ⌜l ∈ FChainU f r⌝
	THEN1 (asm_rewrite_tac [] THEN all_fc_tac [ccrpou_fcclosed_fc_lemma2]));
a (all_fc_tac [ccrpou_lub_lemma]);
a (POP_ASM_T ante_tac THEN (GET_NTH_ASM_T 2 (rewrite_thm_tac o eq_sym_rule))
	THEN contr_tac);
a (fc_tac [get_spec ⌜IsLub⌝]);
a (lemma_tac ⌜¬ r x l⌝
	THEN1 (contr_tac
		THEN all_fc_tac [ccrpou_fc_clauses]
		THEN var_elim_asm_tac ⌜x = l⌝));
a (all_fc_tac [ccrpou_fchainu_lemma2b]);
a (cases_tac ⌜l = x⌝);
(* *** Goal "1" *** *)
a (var_elim_asm_tac ⌜l = x⌝);
(* *** Goal "2" *** *)
a (lemma_tac ⌜¬ r x (f l)⌝
	THEN1 (spec_nth_asm_tac 13 ⌜l⌝
		THEN contr_tac
		THEN all_fc_tac [ccrpou_fc_clauses]));
a (lemma_tac ⌜f l ∈ FChainU f r⌝
	THEN1 (fc_tac [fchainu_lemma1]));
a (LEMMA_T ⌜f l ∈ {z|z ∈ FChainU f r ∧ r z x ∧ ¬ r x z}⌝ asm_tac
	THEN1 PC_T1 "hol1" asm_prove_tac[]);
a (GET_NTH_ASM_T 7 ante_tac
	THEN rewrite_tac [get_spec ⌜IsUb⌝]);
a (contr_tac);
a (spec_nth_asm_tac 1 ⌜f l⌝);
a (lemma_tac ⌜r l (f l)⌝ THEN1 all_fc_tac [ccrpou_fchainu_lemma1]);
a (lemma_tac ⌜l = f l⌝ THEN1 all_asm_fc_tac [ccrpou_fc_clauses]);
a (all_fc_tac [ccrpou_fchainu_lfp_lemma]);
a (FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule [let_def]))) [get_spec ⌜IsLfp⌝]);
a (fc_tac [get_spec ⌜IsGlb⌝]);
a (fc_tac [get_spec ⌜IsLb⌝]);
a (spec_nth_asm_tac 1 ⌜l⌝ THEN1 (POP_ASM_T ante_tac THEN (rewrite_tac [eq_sym_rule (asm_rule ⌜l = f l⌝)])));
a (fc_tac [get_spec ⌜IsLub⌝]);
a (lemma_tac ⌜r x l'⌝
	THEN1 (fc_tac [get_spec ⌜IsUb⌝]
		THEN all_asm_fc_tac [ccrpou_fc_clauses]
		THEN1 spec_nth_asm_tac 1 ⌜x⌝));
a (all_fc_tac [ccrpou_fc_clauses]);
val fchainu_cases_lemma2 = save_pop_thm "fchainu_cases_lemma2";
pop_pc();
=TEX
}%ignore

If this is indeed the normal way of doing such proofs then the following induction principle, though more complicated than the plain ``course of values'' principle is probably going to be more convenient.

=GFT
⦏fchainu_induction_thm3⦎ =
   ⊢ ∀ r f p
     ⦁ CcRpoU r
           ∧ Increasing r r f
           ∧ (∀ x
           ⦁ x ∈ FChainU f r
                 ∧ (∀ y⦁ y ∈ FChainU f r ∧ r y x ∧ ¬ r (f x) y ⇒ p y)
               ⇒ p (f x))
           ∧ (∀ x
           ⦁ x ∈ FChainU f r
                 ∧ x = Lub r {y|y ∈ FChainU f r ∧ r y x ∧ ¬ r x y}
                 ∧ (∀ y⦁ y ∈ FChainU f r ∧ r y x ∧ ¬ r x y ⇒ p y)
               ⇒ p x)
         ⇒ (∀ x⦁ x ∈ FChainU f r ⇒ p x)

⦏fchainu_induction_thm4⦎ =
   ⊢ ∀ r f p
     ⦁ CcRpoU r
           ∧ Increasing r r f
           ∧ (∀ x
           ⦁ x ∈ FChainU f r ∧ (∀ y⦁ y ∈ FChainU f r ∧ r y x ⇒ p y)
               ⇒ p (f x))
           ∧ (∀ x
           ⦁ x ∈ FChainU f r
                 ∧ x = Lub r {y|y ∈ FChainU f r ∧ r y x ∧ ¬ r x y}
                 ∧ (∀ y⦁ y ∈ FChainU f r ∧ r y x ∧ ¬ r x y ⇒ p y)
               ⇒ p x)
         ⇒ (∀ x⦁ x ∈ FChainU f r ⇒ p x)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀r f p⦁ CcRpoU r ∧ Increasing r r f
	∧ (∀x⦁ x ∈ FChainU f r ∧ (∀y⦁ y ∈ FChainU f r ∧ r y x ∧ ¬ r (f x) y ⇒ p y) ⇒ p (f x))
	∧ (∀x⦁ x ∈ FChainU f r
		∧ (x = Lub r {y | y ∈ FChainU f r ∧ r y x ∧ ¬ r x y})
		∧ (∀y⦁ y ∈ FChainU f r ∧ r y x ∧ ¬ r x y ⇒ p y)
		⇒ p x)
	⇒ ∀x⦁ x ∈ FChainU f r ⇒ p x⌝);
a (REPEAT strip_tac THEN fc_tac [fchainu_induction_thm2]);
a (lemma_tac ⌜∀ x⦁ x ∈ FChainU f r ∧ (∀ y⦁ y ∈ FChainU f r ∧ r y x ∧ ¬ r x y ⇒ p y) ⇒ p x⌝
	THEN_LIST [REPEAT strip_tac, all_asm_fc_tac []]);
a (fc_tac [fchainu_cases_lemma]);
a (list_spec_nth_asm_tac 1 [⌜f⌝, ⌜x'⌝]);
(* *** Goal "1" *** *)
a (list_spec_nth_asm_tac 9 [⌜y⌝] THEN_TRY asm_rewrite_tac []);
a (lemma_tac ⌜r y (f y)⌝ THEN1 all_fc_tac [ccrpou_fchainu_lemma1]);
a (lemma_tac ⌜r y' x'⌝ THEN1 (asm_rewrite_tac[] THEN all_fc_tac [ccrpou_fc_clauses]));
a (var_elim_asm_tac ⌜x' = f y⌝);
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (list_spec_nth_asm_tac 7 [⌜x'⌝]);
a (all_asm_fc_tac[]);
val fchainu_induction_thm3 = save_pop_thm "fchainu_induction_thm3";

set_goal ([], ⌜∀r f p⦁ CcRpoU r ∧ Increasing r r f
	∧ (∀ x⦁ x ∈ FChainU f r ∧ (∀ y⦁ y ∈ FChainU f r ∧ r y x ⇒ p y) ⇒ p (f x))
	∧ (∀x⦁ x ∈ FChainU f r
		∧ (x = Lub r {y | y ∈ FChainU f r ∧ r y x ∧ ¬ r x y})
		∧ (∀y⦁ y ∈ FChainU f r ∧ r y x ∧ ¬ r x y ⇒ p y)
		⇒ p x)
	⇒ ∀x⦁ x ∈ FChainU f r ⇒ p x⌝);
a (REPEAT strip_tac THEN fc_tac [fchainu_induction_thm2]);
a (lemma_tac ⌜∀ x⦁ x ∈ FChainU f r ∧ (∀ y⦁ y ∈ FChainU f r ∧ r y x ∧ ¬ r x y ⇒ p y) ⇒ p x⌝
	THEN_LIST [REPEAT strip_tac, all_asm_fc_tac []]);
a (fc_tac [fchainu_cases_lemma2]);
a (list_spec_nth_asm_tac 1 [⌜f⌝, ⌜x'⌝]);
(* *** Goal "1" *** *)
a (list_spec_nth_asm_tac 10 [⌜y⌝] THEN_TRY asm_rewrite_tac []);
a (lemma_tac ⌜r y (f y)⌝ THEN1 all_fc_tac [ccrpou_fchainu_lemma1]);
a (lemma_tac ⌜¬ r (f y) y⌝ THEN1
	(contr_tac
		THEN DROP_ASM_T ⌜¬ y = x'⌝ (asm_tac o rewrite_rule[asm_rule ⌜x' = f y⌝])
		THEN all_fc_tac [ccrpou_fc_clauses]));
a (var_elim_asm_tac ⌜x' = f y⌝);
a (all_asm_fc_tac[]);
a (lemma_tac ⌜r y' (f y)⌝ THEN1 all_fc_tac [ccrpou_fc_clauses]);
a (lemma_tac ⌜¬ r (f y) y'⌝ THEN1
	(contr_tac
		THEN all_fc_tac [ccrpou_fc_clauses]));
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (list_spec_nth_asm_tac 7 [⌜x'⌝]);
a (all_asm_fc_tac[]);
val fchainu_induction_thm4 = save_pop_thm "fchainu_induction_thm4";
=TEX
}%ignore

=IGN
This one looks plausible enough to turn into an induction tactic:

⦏fchainu_induction_thm3⦎ =
   ⊢ ∀ r f p
     ⦁ CcRpoU r
           ∧ Increasing r r f
           ∧ (∀ x
           ⦁ x ∈ FChainU f r
                 ∧ (∀ y⦁ y ∈ FChainU f r ∧ r y x ∧ ¬ r (f x) y ⇒ p y)
               ⇒ p (f x))
           ∧ (∀ x
           ⦁ x ∈ FChainU f r
                 ∧ x = Lub r {y|y ∈ FChainU f r ∧ r y x ∧ ¬ r x y}
                 ∧ (∀ y⦁ y ∈ FChainU f r ∧ r y x ∧ ¬ r x y ⇒ p y)
               ⇒ p x)
         ⇒ (∀ x⦁ x ∈ FChainU f r ⇒ p x)

fun ⦏fchain_induction_tac⦎ (a, c) = (
	let val (l1, l2) = dest_⇒ c
	in 	    and l2 = mk_app (mk_app (mk_const ("∈", ⓣGS → GS SET → BOOL⌝), t),
					mk_const ("Syntax", ⓣGS SET⌝))
	in  let val l3 = mk_∀ (t, mk_⇒ (l2, l1))
	in  LEMMA_T l1 (rewrite_thm_tac o rewrite_rule[])
	THEN DROP_ASM_T l2 ante_tac
	THEN LEMMA_T l3 (rewrite_thm_tac o rewrite_rule[])
	THEN bc_tac [fchainu_induction_thm3]
	THEN rewrite_tac[]
	THEN strip_tac
	end end) (a,c);
=TEX

\section{CHAIN CO-COMPLETENESS}
\subsection{Inverse Relations}

In order to exploit the duality between induction and co-induction it is useful to have some results about the inverses of relations.

First the definition.

ⓈHOLCONST
│ ⦏RelInv⦎ : ('a → 'a → BOOL) → ('a → 'a → BOOL)
├───────────
│ ∀ r⦁ RelInv r = λx y⦁ r y x
■

Then we prove lemmas about various properties of relations and their inverses.

=GFT
⦏refl_inverse_lemma⦎ =
	⊢ ∀ X r⦁ Refl (X, RelInv r) = Refl (X, r)

⦏antisym_inverse_lemma⦎ =
	⊢ ∀ X r⦁ Antisym (X, RelInv r) = Antisym (X, r)

⦏trans_inverse_lemma⦎ =
	⊢ ∀ X r⦁ Trans (X, RelInv r) = Trans (X, r)

⦏trans_inverse_lemma⦎ =
	⊢ ∀ X r⦁ Trans (X, RelInv r) = Trans (X, r)

⦏trich_inverse_lemma⦎ =
	⊢ ∀ X r⦁ Trich (X, RelInv r) = Trich (X, r)

⦏linearorder_inverse_lemma⦎ =
	⊢ ∀ X r⦁ LinearOrder (X, r) = LinearOrder (X, RelInv r)

⦏rpo_inverse_lemma⦎ =
	⊢ ∀ X r⦁ Rpo (X, RelInv r) = Rpo (X, r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀X r⦁ Refl (X, RelInv r) ⇔ Refl (X, r)⌝);
a (rewrite_tac [get_spec ⌜Refl⌝, get_spec ⌜RelInv⌝]);
val refl_inverse_lemma = save_pop_thm "refl_inverse_lemma";

set_goal([], ⌜∀X r⦁ Antisym (X, RelInv r) ⇔ Antisym (X, r)⌝);
a (rewrite_tac [get_spec ⌜Antisym⌝, get_spec ⌜RelInv⌝]);
a (contr_tac THEN all_asm_fc_tac[]);
val antisym_inverse_lemma = save_pop_thm "antisym_inverse_lemma";

set_goal([], ⌜∀X r⦁ Trans (X, RelInv r) ⇔ Trans (X, r)⌝);
a (rewrite_tac [get_spec ⌜Trans⌝, get_spec ⌜RelInv⌝] THEN contr_tac);
a (list_spec_nth_asm_tac 7 [⌜z⌝, ⌜y⌝, ⌜x⌝]);
a (list_spec_nth_asm_tac 7 [⌜z⌝, ⌜y⌝, ⌜x⌝]);
val trans_inverse_lemma = save_pop_thm "trans_inverse_lemma";

set_goal([], ⌜∀X r⦁ PartialOrder (X, RelInv r) ⇔ PartialOrder (X, r)⌝);
a (rewrite_tac [get_spec ⌜PartialOrder⌝, antisym_inverse_lemma, trans_inverse_lemma]);
val partialorder_inverse_lemma = save_pop_thm "partialorder_inverse_lemma";

set_goal([], ⌜∀X r⦁ Trich (X, RelInv r) ⇔ Trich (X, r)⌝);
a (rewrite_tac [get_spec ⌜Trich⌝, get_spec ⌜RelInv⌝] THEN contr_tac
	THEN all_asm_fc_tac[]);
val trich_inverse_lemma = save_pop_thm "trich_inverse_lemma";

set_goal([], ⌜∀X r⦁ LinearOrder (X, RelInv r) ⇔ LinearOrder (X, r)⌝);
a (rewrite_tac [get_spec ⌜LinearOrder⌝, partialorder_inverse_lemma, trich_inverse_lemma]);
val linearorder_inverse_lemma = save_pop_thm "linearorder_inverse_lemma";

set_goal([], ⌜∀X r⦁ Rpo (X, RelInv r) ⇔ Rpo (X, r)⌝);
a (rewrite_tac [get_spec ⌜Rpo⌝, partialorder_inverse_lemma, refl_inverse_lemma]);
val rpo_inverse_lemma = save_pop_thm "rpo_inverse_lemma";
=TEX
}%ignore

=GFT
⦏isub_inverse_lemma⦎ =
	⊢ ∀ X r x⦁ IsUb (RelInv r) X x = IsLb r X x

⦏islb_inverse_lemma⦎ =
	⊢ ∀ X r x⦁ IsLb (RelInv r) X x = IsUb r X x

⦏islub_inverse_lemma⦎ =
	⊢ ∀ X r x⦁ IsLub (RelInv r) X x = IsGlb r X x

⦏isglb_inverse_lemma⦎ =
	⊢ ∀ X r x⦁ IsGlb (RelInv r) X x = IsLub r X x

⦏islfp_inverse_lemma⦎ =
	⊢ ∀ r f e⦁ IsLfp (RelInv r) f e = IsGfp r f e

⦏isgfp_inverse_lemma⦎ =
	⊢ ∀ r f e⦁ IsGfp (RelInv r) f e = IsLfp r f e

⦏increasing_inverse_lemma⦎ =
   ⊢ ∀ r1 r2⦁ Increasing (RelInv r1) (RelInv r2) = Increasing r1 r2
=TEX

\ignore{
=SML
set_goal([], ⌜∀X r x⦁ IsUb (RelInv r) X x = IsLb r X x⌝);
a (rewrite_tac [get_spec ⌜IsUb⌝, get_spec ⌜IsLb⌝, get_spec ⌜RelInv⌝]);
val isub_inverse_lemma = save_pop_thm "isub_inverse_lemma";

set_goal([], ⌜∀X r x⦁ IsLb (RelInv r) X x = IsUb r X x⌝);
a (rewrite_tac [get_spec ⌜IsUb⌝, get_spec ⌜IsLb⌝, get_spec ⌜RelInv⌝]);
val islb_inverse_lemma = save_pop_thm "islb_inverse_lemma";

set_goal([], ⌜∀X r x⦁ IsLub (RelInv r) X x = IsGlb r X x⌝);
a (rewrite_tac [get_spec ⌜IsLub⌝, get_spec ⌜IsGlb⌝, get_spec ⌜RelInv⌝,
	isub_inverse_lemma]);
val islub_inverse_lemma = save_pop_thm "islub_inverse_lemma";

set_goal([], ⌜∀X r x⦁ IsGlb (RelInv r) X x = IsLub r X x⌝);
a (rewrite_tac [get_spec ⌜IsGlb⌝, get_spec ⌜IsLub⌝, get_spec ⌜RelInv⌝,
	islb_inverse_lemma]);
val isglb_inverse_lemma = save_pop_thm "isglb_inverse_lemma";

set_goal([], ⌜∀r f e⦁ IsLfp (RelInv r) f e = IsGfp r f e⌝);
a (rewrite_tac [get_spec ⌜IsLfp⌝, get_spec ⌜IsGfp⌝,
	isglb_inverse_lemma]);
val islfp_inverse_lemma = save_pop_thm "islfp_inverse_lemma";

set_goal([], ⌜∀r f e⦁ IsGfp (RelInv r) f e = IsLfp r f e⌝);
a (rewrite_tac [get_spec ⌜IsLfp⌝, get_spec ⌜IsGfp⌝,
	islub_inverse_lemma]);
val isgfp_inverse_lemma = save_pop_thm "isgfp_inverse_lemma";

set_goal([], ⌜∀r1 r2⦁ Increasing (RelInv r1) (RelInv r2) = Increasing r1 r2⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [ext_thm, get_spec ⌜Increasing⌝, get_spec ⌜RelInv⌝]
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
val increasing_inverse_lemma = save_pop_thm "increasing_inverse_lemma";
=TEX
}%ignore

\subsection{Chain Co-Complete Partial Orders}

The results in this section could be achieved in either of two ways.
The first is by systematic modifications to the proof above to obtain their duals.
The second is by use of the original theorems on inverses of relationship.
I have done some by the first method, which is a bit tedious.
To use the second method here is the definition of the inverse of a relationship.

ⓈHOLCONST
│ ⦏ChainCoComplete⦎ : ('a SET × ('a → 'a → BOOL)) → BOOL
├───────────
│ ∀ X r⦁ ChainCoComplete (X, r) ⇔ ∀Y⦁ Y ⊆ X ∧ LinearOrder (Y, r) ⇒
│	∃x⦁ x ∈ X ∧ IsGlb r Y x
■

=GFT
⦏chaincocomplete_dual_lemma⦎ =
   ⊢ ∀ X r⦁ ChainCoComplete (X, r) = ChainComplete (X, RelInv r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀X r⦁ ChainCoComplete (X, r) ⇔ ChainComplete (X, RelInv r)⌝);
a (rewrite_tac [get_spec ⌜ChainCoComplete⌝, get_spec ⌜ChainComplete⌝,
	linearorder_inverse_lemma, islub_inverse_lemma]);
val chaincocomplete_dual_lemma = save_pop_thm "chaincocomplete_dual_lemma";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏CoCcRpo⦎ : ('a SET × ('a → 'a → BOOL)) → BOOL
├───────────
│ ∀ r⦁ CoCcRpo r ⇔ Rpo r ∧ ChainCoComplete r
■

=GFT
⦏coccrpo_dual_lemma⦎ =
	⊢ ∀ X r⦁ CoCcRpo (X, r) = CcRpo (X, RelInv r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀X r⦁ CoCcRpo (X, r) ⇔ CcRpo (X, RelInv r)⌝);
a (rewrite_tac [get_spec ⌜CoCcRpo⌝, get_spec ⌜CcRpo⌝,
	chaincocomplete_dual_lemma, rpo_inverse_lemma]);
val coccrpo_dual_lemma = save_pop_thm "coccrpo_dual_lemma";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏CoCcRpoU⦎ : ('a → 'a → BOOL) → BOOL
├───────────
│ ∀ r⦁ CoCcRpoU r ⇔ CoCcRpo (Universe, r)
■

=GFT
⦏coccrpou_dual_lemma⦎ =
	⊢ ∀ r⦁ CoCcRpoU r = CcRpoU (RelInv r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ CoCcRpoU r ⇔ CcRpoU (RelInv r)⌝);
a (rewrite_tac [get_spec ⌜CoCcRpoU⌝, get_spec ⌜CcRpoU⌝, coccrpo_dual_lemma]);
val coccrpou_dual_lemma = save_pop_thm "coccrpou_dual_lemma";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏FCoChainClosed⦎ : ('a → 'a) → ('a SET × ('a → 'a → BOOL)) → BOOL
├───────────
│ ∀ f X r⦁ FCoChainClosed f (X, r) ⇔ 
│	FClosed f X ∧ ChainCoComplete (X, r)
■

=GFT
⦏fcochainclosed_dual_lemma⦎ =
   ⊢ ∀ f X r⦁ FCoChainClosed f (X, r) = FChainClosed f (X, RelInv r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀f X r⦁ FCoChainClosed f (X, r) ⇔ FChainClosed f (X, RelInv r)⌝);
a (rewrite_tac [get_spec ⌜FCoChainClosed⌝, get_spec ⌜FChainClosed⌝,
	chaincocomplete_dual_lemma]);
val fcochainclosed_dual_lemma = save_pop_thm "fcochainclosed_dual_lemma";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏FCoChain⦎ : ('a → 'a) → ('a SET × ('a → 'a → BOOL)) → 'a SET
├───────────
│ ∀ f X r⦁ FCoChain f (X, r) = ⋂ {Y | Y ⊆ X ∧ FCoChainClosed f (Y, r)}
■

=GFT
⦏fcochain_dual_lemma⦎ =
	⊢ ∀ X r f⦁ FCoChain f (X, r) = FChain f (X, RelInv r)

⦏fcochain_lemma1⦎ =
	⊢ ∀ X r f⦁ FCoChainClosed f (X, r) ⇒ FCoChain f (X, r) ⊆ X

⦏fcochain_fcochainclosed_lemma⦎ =
   ⊢ ∀ X r f
     ⦁ Antisym (Universe, r) ∧ FCoChainClosed f (X, r)
         ⇒ FCoChainClosed f (FCoChain f (X, r), r)

⦏fcochain_fcochainclosed_lemma2⦎ =
   ⊢ ∀ X r f
     ⦁ Rpo (Universe, r) ∧ FCoChainClosed f (X, r)
         ⇒ FCoChainClosed f (FCoChain f (X, r), r)

⦏fcoc_fcocclosed_fcoc_lemma⦎ =
   ⊢ ∀ X r f
     ⦁ Rpo (Universe, r) ∧ FCoChainClosed f (X, r)
         ⇒ (∀ x⦁ x ∈ FCoChain f (X, r) ⇒ f x ∈ FCoChain f (X, r))

⦏fcochain_lemma2⦎ =
   ⊢ ∀ X Y r f
     ⦁ Rpo (Universe, r)
           ∧ FCoChainClosed f (X, r)
           ∧ Y ⊆ FCoChain f (X, r)
           ∧ FCoChainClosed f (Y, r)
         ⇒ Y = FCoChain f (X, r)

⦏coccrpo_fixp_lemma1⦎ =
   ⊢ ∀ X r f
     ⦁ Increasing r r f
         ⇒ FClosed f {x|x ∈ FCoChain f (X, r) ∧ (r (f x) x ∨ x = f x)}

⦏coccrpo_fixp_lemma2⦎ =
   ⊢ ∀ X r f
     ⦁ Increasing r r f ∧ Rpo (Universe, r) ∧ FCoChainClosed f (X, r)
         ⇒ ChainCoComplete
           ({x|x ∈ FCoChain f (X, r) ∧ (r (f x) x ∨ x = f x)}, r)

⦏coccrpo_fixp_lemma3⦎ =
   ⊢ ∀ X r f
     ⦁ Increasing r r f ∧ Rpo (Universe, r) ∧ FCoChainClosed f (X, r)
         ⇒ FCoChainClosed
           f
           ({z|z ∈ FCoChain f (X, r) ∧ (r (f z) z ∨ z = f z)}, r)

⦏coccrpo_fixp_lemma4⦎ =
   ⊢ ∀ X r f
     ⦁ Increasing r r f ∧ Rpo (Universe, r) ∧ FCoChainClosed f (X, r)
         ⇒ (∀ z⦁ z ∈ FCoChain f (X, r) ⇒ r (f z) z ∨ z = f z)
=TEX

\ignore{
=SML
push_merge_pcs ["hol1", "'fixp"];

set_goal([], ⌜∀X r f⦁ FCoChain f (X, r) = FChain f (X, RelInv r)⌝);
a (rewrite_tac [get_spec ⌜FCoChain⌝, get_spec ⌜FChain⌝, fcochainclosed_dual_lemma]
	THEN REPEAT strip_tac);
val fcochain_dual_lemma = save_pop_thm "fcochain_dual_lemma";


set_goal([], ⌜∀X r f⦁ FCoChainClosed f (X, r) ⇒ FCoChain f (X,r) ⊆ X⌝);
a (rewrite_tac [get_spec ⌜FCoChainClosed⌝, get_spec ⌜FCoChain⌝] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜X⌝);
val fcochain_lemma1 = save_pop_thm "fcochain_lemma1";

push_merge_pcs ["rbjmisc", "'fixp"];

set_goal([], ⌜∀X r f⦁ Antisym (Universe, r) ∧ FCoChainClosed f (X, r)
	⇒ FCoChainClosed f (FCoChain f (X,r), r)⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜FCoChainClosed⌝]);
a (fc_tac [get_spec ⌜FClosed⌝]);
a (rewrite_tac [get_spec ⌜FCoChainClosed⌝, get_spec ⌜FClosed⌝]
	THEN REPEAT ∀_tac
	THEN strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜FCoChainClosed⌝,
		get_spec ⌜FClosed⌝,
		get_spec ⌜FCoChain⌝,
		get_spec ⌜ChainCoComplete⌝]
	THEN REPEAT strip_tac
	THEN REPEAT (asm_fc_tac[]));
(* *** Goal "2" *** *)
a (fc_tac [get_spec ⌜ChainCoComplete⌝]);
a (rewrite_tac [get_spec ⌜ChainCoComplete⌝]
	THEN REPEAT strip_tac);
a (fc_tac [fcochain_lemma1]);
a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B C⦁ A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C⌝]);
a (all_asm_fc_tac []);
a (∃_tac ⌜x⌝ THEN REPEAT strip_tac);
a (REPEAT_N 3 (PC_T1 "hol1" once_rewrite_tac [get_spec ⌜FCoChain⌝])
	THEN REPEAT strip_tac);
a (fc_tac [get_spec ⌜FCoChainClosed⌝]);
a (fc_tac [get_spec ⌜FClosed⌝]);
a (fc_tac [get_spec ⌜ChainCoComplete⌝]);
a (lemma_tac ⌜FCoChain f (X, r) ⊆ s⌝
	THEN1 (rewrite_tac [get_spec ⌜FCoChain⌝] THEN REPEAT strip_tac
		THEN (PC_T1 "hol1" asm_rewrite_tac [])
		THEN REPEAT strip_tac THEN all_asm_fc_tac[]));
a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B C⦁ A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C⌝]);
a (all_asm_fc_tac[]);
a (fc_tac [glb_unique_lemma]);
a (all_asm_fc_tac[]);
a (var_elim_nth_asm_tac 8);
val fcochain_fcochainclosed_lemma = save_pop_thm "fcochain_fcochainclosed_lemma";

set_goal([], ⌜∀X r f⦁ Rpo (Universe, r) ∧ FCoChainClosed f (X, r)
	⇒ FCoChainClosed f (FCoChain f (X,r), r)⌝);
a (REPEAT strip_tac
	THEN fc_tac [rpo_antisym_lemma]
	THEN all_fc_tac [fcochain_fcochainclosed_lemma]);
val fcochain_fcochainclosed_lemma2 = save_pop_thm "fcochain_fcochainclosed_lemma2";

set_goal([], ⌜∀X r f⦁ Rpo (Universe, r) ∧ FCoChainClosed f (X, r)
	⇒ ∀x⦁ x ∈ FCoChain f (X,r) ⇒ f x ∈ FCoChain f (X,r)⌝);
a (REPEAT strip_tac);
a (fc_tac [rpo_antisym_lemma]);
a (all_fc_tac [fcochain_fcochainclosed_lemma]);
a (all_fc_tac [get_spec ⌜FCoChainClosed⌝]);
a (all_fc_tac [get_spec ⌜FClosed⌝]);
val fcoc_fcocclosed_fcoc_lemma = save_pop_thm "fcoc_fcocclosed_fcoc_lemma";

set_goal([], ⌜∀X Y r f⦁ Rpo (Universe, r) ∧ FCoChainClosed f (X, r)
	∧ Y ⊆ FCoChain f (X, r) ∧ FCoChainClosed f (Y, r)
	⇒ Y = FCoChain f (X, r)⌝);
a (REPEAT strip_tac
	THEN PC_T1 "hol1" rewrite_tac [get_spec ⌜FCoChain⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (GET_NTH_ASM_T 5 ante_tac
	THEN PC_T1 "hol1" rewrite_tac [get_spec ⌜FCoChain⌝]
	THEN REPEAT strip_tac);
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 1 ⌜Y⌝);
a (fc_tac [fcochain_lemma1]);
a (ALL_ASM_FC_T (fc_tac o (map (pc_rule1 "hol1" rewrite_rule []))) [⊆_trans_thm]);
val fcochain_lemma2 = save_pop_thm "fcochain_lemma2";

set_goal([], ⌜∀X r f⦁ Increasing r r f
	⇒ FClosed f {x | x ∈ FCoChain f (X,r) ∧ (r (f x) x ∨ x = (f x))}⌝);
a (REPEAT strip_tac);
a (rewrite_tac [get_spec ⌜FClosed⌝, get_spec ⌜FCoChain⌝]
	THEN REPEAT strip_tac THEN_TRY SYM_ASMS_T rewrite_tac);
(* *** Goal "1" *** *)
a (GET_NTH_ASM_T 4 (fn x => all_fc_tac [rewrite_rule [] x]));
a (fc_tac [get_spec ⌜FCoChainClosed⌝]);
a (fc_tac [get_spec ⌜FClosed⌝]);
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [get_spec ⌜Increasing⌝]);
a (asm_fc_tac[]);
(* *** Goal "3" *** *)
a (fc_tac [get_spec ⌜Increasing⌝]);
a (asm_fc_tac[]);
val coccrpo_fixp_lemma1 = pop_thm ();

push_extend_pc "'mmp1";

set_goal([], ⌜∀X r f⦁ Increasing r r f ∧ Rpo (Universe, r) ∧ FCoChainClosed f (X, r)
	⇒ ChainCoComplete ({x | x ∈ FCoChain f (X,r) ∧ (r (f x) x ∨ x = (f x))}, r)⌝);
a (rewrite_tac [get_spec ⌜ChainCoComplete⌝]
	THEN REPEAT strip_tac);
a (fc_tac [coccrpo_fixp_lemma1]);
a (lemma_tac ⌜FCoChain f (X, r) ⊆ X⌝
	THEN1 (PC_T1 "hol1" rewrite_tac [get_spec ⌜FCoChain⌝]
		THEN REPEAT strip_tac
		THEN (spec_nth_asm_tac 1 ⌜X⌝)));
a (lemma_tac ⌜Y ⊆ FCoChain f (X, r)⌝
	THEN1 (PC_T1 "hol1" rewrite_tac []
		THEN REPEAT strip_tac
		THEN GET_NTH_ASM_T 5 (fn x => all_fc_tac [pc_rule1 "hol1" rewrite_rule [] x])));
a (lemma_tac ⌜Y ⊆ X⌝
	THEN1 (all_fc_tac [pc_rule1 "hol1" prove_rule []
	 ⌜∀A B C⦁ A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C⌝]));
a (fc_tac [get_spec ⌜FCoChainClosed⌝]);
a (all_fc_tac [get_spec ⌜ChainCoComplete⌝]);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
a (strip_tac);
(* *** Goal "1" *** *)
a (PC_T1 "hol1" rewrite_tac [get_spec ⌜FCoChain⌝]
	THEN REPEAT strip_tac);
a (fc_tac [get_spec ⌜FCoChainClosed⌝]);
a (lemma_tac ⌜Y ⊆ s⌝);
(* *** Goal "1.1" *** *)
a (lemma_tac ⌜FCoChain f (X, r) ⊆ s⌝
	THEN1 rewrite_tac [get_spec ⌜FCoChain⌝]);
(* *** Goal "1.1.1" *** *)
a (LEMMA_T ⌜s ∈ {Y|Y ⊆ X ∧ FCoChainClosed f (Y, r)}⌝ asm_tac
	THEN1 (PC_T1 "hol1" asm_rewrite_tac []));
a (bc_tac [pc_rule1 "hol1" prove_rule [] ⌜s ∈ A ⇒ ⋂A ⊆ s⌝]
	THEN CONTR_T check_asm_tac);
(* *** Goal "1.1.2" *** *)
a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B C⦁ A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C⌝]);
(* *** Goal "1.2" *** *)
a (GET_NTH_ASM_T 3 (fn x => (all_fc_tac [rewrite_rule [get_spec ⌜ChainCoComplete⌝] x])));
a (fc_tac [rpo_antisym_lemma]);
a (all_fc_tac [glb_unique_lemma]);
a (var_elim_nth_asm_tac 1);
(* *** Goal "2" *** *)
a (contr_tac);
a (lemma_tac ⌜IsLb r Y (f x)⌝
	THEN1 (rewrite_tac [get_spec ⌜IsLb⌝]
		THEN REPEAT strip_tac));
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜r (f x') x' ∨ x' = f x'⌝
	THEN1 GET_NTH_ASM_T 13 (fn x => asm_tac (pc_rule1 "hol1" rewrite_rule[] x)));
(* *** Goal "2.1.1" *** *)
a (spec_nth_asm_tac 1 ⌜x'⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1.2" *** *)
a (lemma_tac ⌜r x x'⌝);
(* *** Goal "2.1.2.1" *** *)
a (fc_tac [get_spec ⌜IsGlb⌝]);
a (GET_NTH_ASM_T 1 ante_tac THEN rewrite_tac [get_spec ⌜IsLb⌝]
	THEN strip_tac
	THEN asm_fc_tac[]);
(* *** Goal "2.1.2.2" *** *)
a (fc_tac [get_spec ⌜Increasing⌝]
	THEN all_asm_fc_tac[]);
a (FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule[]))) [rpo_fc_clauses]);
a (all_asm_fc_tac[]);
(* *** Goal "2.1.3" *** *)
a (fc_tac [get_spec ⌜IsGlb⌝]);
a (GET_NTH_ASM_T 1 ante_tac THEN rewrite_tac [get_spec ⌜IsLb⌝]
	THEN strip_tac
	THEN asm_fc_tac[]);
a (fc_tac [get_spec ⌜Increasing⌝]
	THEN all_asm_fc_tac[]);
a (DROP_NTH_ASM_T 2 ante_tac THEN SYM_ASMS_T rewrite_tac);
(* *** Goal "2.2" *** *)
a (GET_NTH_ASM_T 4 ante_tac THEN rewrite_tac [get_spec ⌜IsGlb⌝]);
a (REPEAT strip_tac);
a (all_asm_fc_tac[]);
val coccrpo_fixp_lemma2 = pop_thm ();

set_goal([], ⌜∀X r f⦁ Increasing r r f ∧ Rpo(Universe,r) ∧ FCoChainClosed f (X, r)
	⇒ FCoChainClosed f ({z|z ∈ FCoChain f (X,r) ∧ (r (f z) z ∨ z = f z)}, r)⌝);
a (REPEAT strip_tac);
a (rewrite_tac [get_spec ⌜FCoChainClosed⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac[coccrpo_fixp_lemma1]);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac[coccrpo_fixp_lemma1]);
a (all_fc_tac[rpo_antisym_lemma]);
a (all_fc_tac[fcochain_fcochainclosed_lemma]);
a (all_fc_tac[coccrpo_fixp_lemma2]);
val coccrpo_fixp_lemma3 = pop_thm ();

set_goal([], ⌜∀X r f⦁ Increasing r r f ∧ Rpo(Universe,r) ∧ FCoChainClosed f (X, r)
	⇒ ∀z⦁ z ∈ FCoChain f (X,r) ⇒ r (f z) z ∨ z = f z⌝);
a (REPEAT strip_tac);
a (all_fc_tac [coccrpo_fixp_lemma3]);
a (lemma_tac ⌜{z | z ∈ FCoChain f (X, r) ∧ (r (f z) z ∨ z = f z)} ⊆ FCoChain f (X, r)⌝
	THEN1 (PC_T1 "hol1" rewrite_tac[]
		THEN REPEAT strip_tac));
a (all_fc_tac [fcochain_lemma2]);
a (DROP_NTH_ASM_T 5 ante_tac THEN SYM_ASMS_T once_rewrite_tac);
a (rewrite_tac[]);
a (contr_tac);
val coccrpo_fixp_lemma4 = save_pop_thm "coccrpo_fixp_lemma4";

pop_pc();
=TEX
}%ignore

=GFT
⦏coccrpo_fixp_lemma18⦎ =
   ⊢ ∀ X $≤⋎v f
     ⦁ Increasing $≤⋎v $≤⋎v f
           ∧ Rpo (Universe, $≤⋎v)
           ∧ FCoChainClosed f (X, $≤⋎v)
         ⇒ (∃ l⦁ IsGlb $≤⋎v (FCoChain f (X, $≤⋎v)) l ∧ IsGfp $≤⋎v f l)

⦏coccrpo_fixp_lemma19⦎ =
   ⊢ ∀ r f⦁ CoCcRpoU r ∧ Increasing r r f ⇒ (∃ e⦁ IsGfp r f e)
=TEX

\ignore{
=SML
set_goal([], ⌜∀X $≤⋎v f⦁ Increasing $≤⋎v $≤⋎v f ∧ Rpo(Universe,$≤⋎v)
	∧ FCoChainClosed f (X, $≤⋎v)
	⇒ ∃l⦁ IsGlb $≤⋎v (FCoChain f (X, $≤⋎v)) l ∧ IsGfp $≤⋎v f l⌝);
a (rewrite_tac [fcochainclosed_dual_lemma, isglb_inverse_lemma, fcochain_dual_lemma,
	isgfp_inverse_lemma]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜Rpo (Universe, RelInv $≤⋎v)⌝
	THEN1 asm_rewrite_tac [rpo_inverse_lemma]);
a (DROP_ASM_T ⌜Rpo (Universe, $≤⋎v)⌝ discard_tac);
a (lemma_tac ⌜Increasing (RelInv $≤⋎v) (RelInv $≤⋎v) f⌝
	THEN1 asm_rewrite_tac [increasing_inverse_lemma]);
a (DROP_ASM_T ⌜Increasing $≤⋎v $≤⋎v f⌝ discard_tac);
a (ALL_FC_T (MAP_EVERY ante_tac) [ccrpo_fixp_lemma18]
	THEN rewrite_tac [islub_inverse_lemma, islfp_inverse_lemma]
	THEN REPEAT strip_tac);
a (∃_tac ⌜l⌝ THEN asm_rewrite_tac[]);
val coccrpo_fixp_lemma18 = pop_thm ();

set_goal([], ⌜∀r f⦁ CoCcRpoU r
	∧ Increasing r r f
	⇒ (∃ e⦁ IsGfp r f e)⌝);
a (rewrite_tac [coccrpou_dual_lemma]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜Increasing (RelInv r) (RelInv r) f⌝
	THEN1 asm_rewrite_tac [increasing_inverse_lemma]);
a (DROP_ASM_T ⌜Increasing r r f⌝ discard_tac);
a (ALL_FC_T (MAP_EVERY ante_tac) [ccrpo_fixp_lemma19]
	THEN rewrite_tac [islfp_inverse_lemma]
	THEN strip_tac);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
val coccrpo_fixp_lemma19 = pop_thm ();

=IGN
set_goal([], ⌜∀r f p⦁ CoCcRpoU r 
	∧ Increasing r r f
	∧ (∀x⦁ p x ⇒ p (f x))
	∧ (∀s⦁ (∀x⦁ x ∈ s ⇒ p x) ∧ LinearOrder (s, r) ⇒ ∃y⦁ p y ∧ (IsGlb r s y))
	⇒ p (Gfp⋎c r f)
	⌝);
a (rewrite_tac [coccrpou_dual_lemma] THEN REPEAT strip_tac);
a (lemma_tac ⌜Increasing (RelInv r) (RelInv r) f⌝
	THEN1 asm_rewrite_tac [increasing_inverse_lemma]);
a (DROP_ASM_T ⌜Increasing r r f⌝ discard_tac);
a (lemma_tac ⌜∀s⦁ (∀x⦁ x ∈ s ⇒ p x) ∧ LinearOrder (s, RelInv r) ⇒ ∃y⦁ p y ∧ (IsLub (RelInv r) s y)⌝
	THEN1 asm_rewrite_tac [linearorder_inverse_lemma, islub_inverse_lemma]);
a (DROP_NTH_ASM_T 3 discard_tac);
=IGN
a (ALL_FC_T (MAP_EVERY ante_tac) [ccrpou_fixp_induction_thm]);
	THEN rewrite_tac [lfp_dual_lemma]
	THEN strip_tac);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
val coccrpou_fixp_induction_thm = save_pop_thm "coccrpou_fixp_induction_thm"; 
=SML
pop_pc();
pop_pc();
=TEX
}%ignore

\subsection{Closure}

If you start from bottom and iterate a function over some complete partial order you get a least fixed point of the function.
If you start somewhere else you get a ``closure''.
From a monotone function you obtain by transfinite iteration a closure operator.

The purpose of this subsection is to adapt the above material so that it can be applied to closure operators obtained in this way.

For this to work we need only chain completeness, so we will do the theory first in that context.

ⓈHOLCONST
│ ⦏Closed⋎c⦎: ('a → 'a → BOOL) × ('a → 'a) → 'a → BOOL
├──────
│ ∀ $≤⋎v f x⦁ Closed⋎c ($≤⋎v, f) x ⇔ f x ≤⋎v x
■

ⓈHOLCONST
│ ⦏Closure⋎c⦎: ('a → 'a → BOOL) × ('a → 'a) → 'a → 'a
├──────
│ ∀ $≤⋎v f x⦁ Closure⋎c ($≤⋎v, f) x = Glb $≤⋎v {y | x ≤⋎v y ∧ Closed⋎c ($≤⋎v, f) y}
■

=GFT
=TEX

\ignore{
=IGN
set_goal([], ⌜∀ $≤⋎v f x⦁ CRpoU $≤⋎v ⇒ IsLfp ({y | x ≤⋎v y} ◁⋎o $≤⋎v) f (Closure⋎c ($≤⋎v, f) x)⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜Closure⋎c⌝, get_spec ⌜Closed⋎c⌝, get_spec ⌜$◁⋎o⌝, get_spec ⌜IsLfp⌝, let_def]
	THEN REPEAT strip_tac);

set_goal([], ⌜∀ $≤⋎v f x⦁ Closure⋎c ($≤⋎v, f) x = Lfp⋎c ({y | x ≤⋎v y} ◁⋎o $≤⋎v) f⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜Closure⋎c⌝, get_spec ⌜Closed⋎c⌝, get_spec ⌜$◁⋎o⌝]
	THEN REPEAT strip_tac);
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Closure⋎d⦎: ('a → 'a → BOOL) × ('a → 'a) → 'a → 'a
├──────
│ ∀ $≤⋎v f x⦁ Closure⋎d ($≤⋎v, f) x = Lub $≤⋎v (FChain f ({y | x ≤⋎v y}, $≤⋎v))
■

The first result I am looking for is that the closure of a function {\it f} maps each element {\it x} in its domain to the least fixed point of {\it f} which is greater than {\it x}.

=GFT
=TEX

\ignore{
=IGN

set_goal([], ⌜∀X f $≤⋎v x⦁ Increasing $≤⋎v $≤⋎v f ∧ ChainComplete (X, $≤⋎v)
	⇒ FChainClosed f ({y | y ∈ X ∧ x ≤⋎v y}, $≤⋎v)⌝);
a (rewrite_tac [get_spec ⌜FChainClosed⌝, get_spec ⌜Increasing⌝,
	get_spec ⌜FClosed⌝, get_spec ⌜ChainComplete⌝]
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);


set_goal([], ⌜∀$≤⋎v f⦁ let g = Closure⋎c ($≤⋎v, f) in g o g = g⌝);
a (rewrite_tac [ext_thm, let_def, get_spec ⌜Closure⋎c⌝, get_spec ⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝]);
=TEX
}%ignore

\section{COMPLETE PARTIAL ORDERS}

ⓈHOLCONST
│ ⦏CRpoU⦎: ('a → 'a → BOOL) → BOOL
├──────
│ ∀ r⦁ CRpoU r ⇔ RpoU r ∧ LubsExist r ∧ GlbsExist r
■

=GFT
⦏crpou_ccrpou_lemma⦎ =
   ⊢ ∀ r⦁ CRpoU r ⇒ CcRpoU r

⦏crpou_lub_glb_∅_lemma⦎ =
   ⊢ ∀ r⦁ CRpoU r ⇒ (∀ x⦁ r (Lub r {}) x ∧ r x (Glb r {}))

⦏crpou_fc_clauses⦎ =
   ⊢ ∀ r
     ⦁ CRpoU r
         ⇒ GlbsExist r
           ∧ LubsExist r
           ∧ (∀ x⦁ r x x)
           ∧ (∀ x y z⦁ r x y ∧ r y z ⇒ r x z)
           ∧ (∀ x y⦁ r x y ∧ r y x ⇒ x = y)

⦏crpou_glb_lfp_lemma1⦎ =
   ⊢ ∀ r f
     ⦁ CRpoU r ∧ Increasing r r f
         ⇒ (∃ e⦁ IsGlb r {x|r (f x) x} e ∧ IsLfp r f e)

⦏crpou_increasing_lfp_lemma1⦎ =
   ⊢ ∀ r f⦁ CRpoU r ∧ Increasing r r f ⇒ (∃ l⦁ IsLfp r f l)

⦏crpou_increasing_lfp_lemma2⦎ =
   ⊢ ∀ r f⦁ CRpoU r ∧ Increasing r r f ⇒ IsLfp r f (Lfp⋎c r f)

⦏crpou_lub_gfp_lemma1⦎ =
   ⊢ ∀ r f
     ⦁ CRpoU r ∧ Increasing r r f
         ⇒ (∃ e⦁ IsLub r {x|r x (f x)} e ∧ IsGfp r f e)

⦏crpou_increasing_gfp_lemma1⦎ =
   ⊢ ∀ r f⦁ CRpoU r ∧ Increasing r r f ⇒ (∃ g⦁ IsGfp r f g)

⦏crpou_increasing_gfp_lemma2⦎ =
   ⊢ ∀ r f⦁ CRpoU r ∧ Increasing r r f ⇒ IsGfp r f (Gfp⋎c r f)

⦏isglb_glb_crpou_lemma⦎ =
   ⊢ ∀ r⦁ CRpoU r ⇒ (∀ X z⦁ IsGlb r X z ⇒ Glb r X = z)

⦏islub_lub_crpou_lemma⦎ =
   ⊢ ∀ r⦁ CRpoU r ⇒ (∀ X z⦁ IsLub r X z ⇒ Lub r X = z)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ CRpoU r ⇒ CcRpoU r⌝);
a (rewrite_tac (map get_spec [⌜CRpoU⌝, ⌜CcRpoU⌝, ⌜CcRpo⌝, ⌜RpoU⌝, ⌜ChainComplete⌝, ⌜LubsExist⌝])
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[]);
val crpou_ccrpou_lemma = save_pop_thm "crpou_ccrpou_lemma";

set_goal([], ⌜∀r⦁ CRpoU r ⇒ ∀x⦁ r (Lub r {}) x ∧ r x (Glb r {})⌝);
a (rewrite_tac [get_spec ⌜RpoU⌝, get_spec ⌜CRpoU⌝, get_spec ⌜LubsExist⌝, get_spec ⌜GlbsExist⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 2 ⌜{}⌝ THEN fc_tac [lub_lub_lemma]);
a (fc_tac [get_spec ⌜IsLub⌝]);
a (lemma_tac ⌜IsUb r {} x⌝
	THEN1 rewrite_tac [get_spec ⌜IsUb⌝]);
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 1 ⌜{}⌝ THEN fc_tac [glb_glb_lemma]);
a (fc_tac [get_spec ⌜IsGlb⌝]);
a (lemma_tac ⌜IsLb r {} x⌝
	THEN1 rewrite_tac [get_spec ⌜IsLb⌝]);
a (asm_fc_tac[]);
val crpou_lub_glb_∅_lemma = save_pop_thm "crpou_lub_glb_∅_lemma";

set_goal([], ⌜∀r⦁ CRpoU r ⇒
		GlbsExist r
	∧	LubsExist r
	∧	(∀x⦁ r x x)
	∧	(∀x y z⦁ r x y ∧ r y z ⇒ r x z)
	∧	(∀x y⦁ r x y ∧ r y x ⇒ x = y)⌝);
a (REPEAT_N 2 strip_tac
	THEN fc_tac [get_spec ⌜CRpoU⌝]
	THEN fc_tac [get_spec ⌜RpoU⌝]
	THEN fc_tac [rpou_fc_clauses]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]
	THEN_TRY asm_rewrite_tac[]);
val crpou_fc_clauses = save_pop_thm "crpou_fc_clauses";

set_goal([], ⌜∀r f⦁ CRpoU r ∧ Increasing r r f ⇒ ∃ e⦁ IsGlb r {x|r (f x) x} e ∧ IsLfp r f e⌝);
a (rewrite_tac [get_spec ⌜CRpoU⌝, get_spec ⌜RpoU⌝, get_spec ⌜Rpo⌝, get_spec ⌜PartialOrder⌝,
	get_spec ⌜Trans⌝, get_spec ⌜Antisym⌝]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜∀x y⦁ r x y ∧ r y x ⇒ x = y⌝
	THEN1 (contr_tac
		THEN ASM_FC_T (MAP_EVERY (strip_asm_tac o (try (rewrite_rule []))))
			[get_spec ⌜Antisym⌝]
		THEN all_asm_fc_tac[]));
a (lemma_tac ⌜trans r⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜trans⌝]));
a (all_fc_tac [mono_fixp_thm2]);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
val crpou_glb_lfp_lemma1 = save_pop_thm "crpou_glb_lfp_lemma1";

set_goal([], ⌜∀r f⦁ CRpoU r ∧ Increasing r r f ⇒ ∃l⦁ IsLfp r f l⌝);
a (rewrite_tac (map get_spec [⌜CRpoU⌝, ⌜RpoU⌝, ⌜Rpo⌝, ⌜PartialOrder⌝, ⌜Trans⌝])
	THEN REPEAT strip_tac);
a (lemma_tac ⌜∀x y⦁ r x y ∧ r y x ⇒ x = y⌝
	THEN1 (contr_tac
		THEN ASM_FC_T (MAP_EVERY (strip_asm_tac o (try (rewrite_rule []))))
			[get_spec ⌜Antisym⌝]
		THEN all_asm_fc_tac[]));
a (lemma_tac ⌜trans r⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜trans⌝]));
a (all_fc_tac [mono_fixp_thm2]);
a (∃_tac ⌜e⌝ THEN strip_tac);
val crpou_increasing_lfp_lemma1 = save_pop_thm "crpou_increasing_lfp_lemma1";

set_goal([], ⌜∀r f⦁ CRpoU r ∧ Increasing r r f ⇒ IsLfp r f (Lfp⋎c r f)⌝);
a (REPEAT strip_tac THEN all_fc_tac [crpou_increasing_lfp_lemma1]);
a (bc_tac [get_spec ⌜Lfp⋎c⌝]);
a (∃_tac ⌜l⌝ THEN strip_tac);
val crpou_increasing_lfp_lemma2 = save_pop_thm "crpou_increasing_lfp_lemma2";

set_goal([], ⌜∀r f⦁ CRpoU r ∧ Increasing r r f ⇒ ∃ e⦁ IsLub r {x|r x (f x)} e ∧ IsGfp r f e⌝);
a (rewrite_tac [get_spec ⌜CRpoU⌝, get_spec ⌜RpoU⌝, get_spec ⌜Rpo⌝, get_spec ⌜PartialOrder⌝,
	get_spec ⌜Trans⌝, get_spec ⌜Antisym⌝]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜∀x y⦁ r x y ∧ r y x ⇒ x = y⌝
	THEN1 (contr_tac
		THEN ASM_FC_T (MAP_EVERY (strip_asm_tac o (try (rewrite_rule []))))
			[get_spec ⌜Antisym⌝]
		THEN all_asm_fc_tac[]));
a (lemma_tac ⌜trans r⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜trans⌝]));
a (all_fc_tac [mono_fixp_thm3]);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
val crpou_lub_gfp_lemma1 = save_pop_thm "crpou_lub_gfp_lemma1";

set_goal([], ⌜∀r f⦁ CRpoU r ∧ Increasing r r f ⇒ ∃g⦁ IsGfp r f g⌝);
a (rewrite_tac (map get_spec [⌜CRpoU⌝, ⌜RpoU⌝, ⌜Rpo⌝, ⌜PartialOrder⌝, ⌜Trans⌝])
	THEN REPEAT strip_tac);
a (lemma_tac ⌜∀x y⦁ r x y ∧ r y x ⇒ x = y⌝
	THEN1 (contr_tac
		THEN ASM_FC_T (MAP_EVERY (strip_asm_tac o (try (rewrite_rule []))))
			[get_spec ⌜Antisym⌝]
		THEN all_asm_fc_tac[]));
a (lemma_tac ⌜trans r⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜trans⌝]));
a (all_fc_tac [mono_fixp_thm3]);
a (∃_tac ⌜e⌝ THEN strip_tac);
val crpou_increasing_gfp_lemma1 = save_pop_thm "crpou_increasing_gfp_lemma1";

set_goal([], ⌜∀r f⦁ CRpoU r ∧ Increasing r r f ⇒ IsGfp r f (Gfp⋎c r f)⌝);
a (REPEAT strip_tac THEN all_fc_tac [crpou_increasing_gfp_lemma1]);
a (bc_tac [get_spec ⌜Gfp⋎c⌝]);
a (∃_tac ⌜g⌝ THEN strip_tac);
val crpou_increasing_gfp_lemma2 = save_pop_thm "crpou_increasing_gfp_lemma2";

set_goal([], ⌜∀r⦁ CRpoU r ⇒ ∀X z⦁ IsGlb r X z ⇒ Glb r X = z⌝);
a (REPEAT strip_tac
	THEN fc_tac [get_spec ⌜CRpoU⌝]
	THEN fc_tac [get_spec ⌜RpoU⌝]
	THEN fc_tac [get_spec ⌜Rpo⌝]
	THEN fc_tac [get_spec ⌜PartialOrder⌝]
	THEN all_fc_tac [isglb_glb_lemma]);
val isglb_glb_crpou_lemma = save_pop_thm "isglb_glb_crpou_lemma";

set_goal([], ⌜∀r⦁ CRpoU r ⇒ ∀X z⦁ IsLub r X z ⇒ Lub r X = z⌝);
a (REPEAT strip_tac
	THEN fc_tac [get_spec ⌜CRpoU⌝]
	THEN fc_tac [get_spec ⌜RpoU⌝]
	THEN fc_tac [get_spec ⌜Rpo⌝]
	THEN fc_tac [get_spec ⌜PartialOrder⌝]
	THEN all_fc_tac [islub_lub_lemma]);
val islub_lub_crpou_lemma = save_pop_thm "islub_lub_crpou_lemma";
=TEX
}%ignore

\subsection{Continuity and Induction}

To prove the properties of least fixed points (not the properties of their members) one approach is to prove:

\begin{itemize}
\item that the bottom element has the property
\item that the function preserves the property
\item that the property is ``continuous''
\end{itemize}

The purpose of this section is to formulate suitable notions of continuity.

I did consider using the theory "topology" but that seemed likely to be too difficult to bend to this context.

Here's an induction principle:

=GFT
⦏crpou_induction_thm⦎ =
   ⊢ ∀ r f p
     ⦁ CRpoU r
           ∧ Increasing r r f
           ∧ (∀ x⦁ p x ⇒ p (f x))
           ∧ (∀ s⦁ (∀ x⦁ x ∈ s ⇒ p x) ⇒ p (Lub r s))
         ⇒ p (Lfp⋎c r f)

=TEX

\ignore{
=SML
set_goal([], ⌜∀r f p⦁ CRpoU r 
	∧ Increasing r r f
	∧ (∀x⦁ p x ⇒ p (f x))
	∧ (∀s⦁ (∀x⦁ x ∈ s ⇒ p x) ⇒ p (Lub r s))
	⇒ p (Lfp⋎c r f)
	⌝);
a (REPEAT strip_tac);
a (fc_tac [crpou_ccrpou_lemma]);
a (lemma_tac ⌜∀ s⦁ (∀ x⦁ x ∈ s ⇒ p x) ∧ LinearOrder (s, r) ⇒ (∃ y⦁ p y ∧ IsLub r s y)⌝
	THEN1 (REPEAT strip_tac THEN all_asm_fc_tac[]));
(* *** Goal "1" *** *)
a (fc_tac [crpou_fc_clauses]);
a (fc_tac [lub_lub_lemma2]);
a (∃_tac ⌜Lub r s⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac [ccrpou_fixp_induction_thm]);
val crpou_induction_thm = save_pop_thm "crpou_fixp_induction_thm";
=TEX
}%ignore

Here's a stronger induction principle:

=GFT
⦏crpou_induction_thm2⦎ =
   ⊢ ∀ r f p
     ⦁ CRpoU r
           ∧ Increasing r r f
           ∧ (∀ x⦁ p x ⇒ p (f x))
           ∧ (∀ s⦁ LinearOrder (s, r) ∧ (∀ x⦁ x ∈ s ⇒ p x) ⇒ p (Lub r s))
         ⇒ p (Lfp⋎c r f)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r f p⦁ CRpoU r 
	∧ Increasing r r f
	∧ (∀x⦁ p x ⇒ p (f x))
	∧ (∀s⦁ LinearOrder (s, r) ∧ (∀x⦁ x ∈ s ⇒ p x) ⇒ p (Lub r s))
	⇒ p (Lfp⋎c r f)
	⌝);
a (REPEAT strip_tac);
a (fc_tac [crpou_ccrpou_lemma]);
a (lemma_tac ⌜∀ s⦁ (∀ x⦁ x ∈ s ⇒ p x) ∧ LinearOrder (s, r) ⇒ (∃ y⦁ p y ∧ IsLub r s y)⌝
	THEN1 (REPEAT strip_tac THEN all_asm_fc_tac[]));
(* *** Goal "1" *** *)
a (fc_tac [crpou_fc_clauses]);
a (fc_tac [lub_lub_lemma2]);
a (∃_tac ⌜Lub r s⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac [ccrpou_fixp_induction_thm]);
val crpou_induction_thm2 = save_pop_thm "crpou_fixp_induction_thm2";
=TEX
}%ignore

=GFT
=TEX

I'm going to give a name to the condition required in this induction principle.

ⓈHOLCONST
│ ⦏ContProp⦎: ('a → 'a → BOOL) → ('a → BOOL) → BOOL
├──────
│ ∀ r p⦁ ContProp r p ⇔ ∀s⦁ (∀y⦁ y ∈ s ⇒ p y) ⇒ p (Lub r s)
■

And then restate the principle using the name:

=GFT
contprop_induction_thm =
   ⊢ ∀ r f p
     ⦁ CRpoU r ∧ Increasing r r f ∧ (∀ x⦁ p x ⇒ p (f x)) ∧ ContProp r p
         ⇒ p (Lfp⋎c r f)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r f p⦁ CRpoU r 
	∧ Increasing r r f
	∧ (∀x⦁ p x ⇒ p (f x))
	∧ ContProp r p
	⇒ p (Lfp⋎c r f)
	⌝);
a (rewrite_tac [get_spec ⌜ContProp⌝, crpou_induction_thm]);
val contprop_induction_thm = save_pop_thm "contprop_induction_thm";
=TEX
}%ignore

Least fixed point induction using a notion of continuity which is independent of the functor about whose least fixed point we are reasoning now seems to me a poor idea (not least because I have now a problem for which it is obviously inadequate).


ⓈHOLCONST
│ ⦏Rising⦎: ('a → 'a) → ('a → 'a → BOOL) → ('a → BOOL)
├──────
│ ∀ f r⦁ Rising f r = λx⦁ r x (f x)
■

ⓈHOLCONST
│ ⦏Falling⦎: ('a → 'a) → ('a → 'a → BOOL) → ('a → BOOL)
├──────
│ ∀ f r⦁ Falling f r = λx⦁ r (f x) x
■

=GFT
=TEX

\ignore{
=IGN
set_goal([], ⌜∀r f⦁ Increasing r r f ⇒ ∀e⦁ IsGlb r {x | Falling f r x} e ⇒ IsLfp r f e⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜Falling⌝, get_spec ⌜IsGlb⌝, get_spec ⌜IsLfp⌝, let_def,
	get_spec ⌜Increasing⌝, get_spec ⌜IsLb⌝]
	THEN REPEAT strip_tac);
=TEX
}%ignore

A second notion of continuity is:

ⓈHOLCONST
│ ⦏ContProp3⦎: ('a → 'a) → ('a → 'a → BOOL) → ('a → BOOL) → BOOL
├──────
│ ∀ f r p⦁ ContProp3 f r p ⇔ ∀x⦁ (∀y⦁ Rising f r y ∧ r y x ∧ ¬ r x y ⇒ p y) ⇒ p x
■

Hopefully all properties $p$ which have this property are true of the least fixed point of $f$ relative to $r$.

=GFT
? ∀r⦁ CRpoU r ⇒ ∀f p⦁ ContProp3 f r p ⇒ p (Lfp⋎c r f)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀r⦁ CRpoU r ⇒ ∀f p⦁ ContProp3 f r p ⇒ p (Lfp⋎c r f)⌝);
a (REPEAT ∀_tac THEN strip_tac THEN REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜ContProp3⌝, get_spec ⌜Rising⌝]
	THEN REPEAT strip_tac);

=TEX
}%ignore

\section{INDUCTIVE DEFINITIONS OF SETS}

We begin with inductive definitions of sets, later addressing the conversion of these sets into types.

The simplest example of interest here is the natural numbers, which can be defined (in HOL) as the smallest set of individuals which includes zero (the individual which is not in the range of the one-one function whose existence is asserted by the usual axiom of infinity) and is closed under the successor function (which is that same one-one function).

We can think of this as forming the natural numbers by starting with some set ({0}) and then adding further elements following some prescription until no more can be added.
Because we are always adding values, the operation on the set-of-values-so-far is monotonic.
If the closure is supplied in a suitable manner then a completely general proof of monotonicity will suffice.

There is a little difficulty in doing this automatically because the operators under which closure is wanted (counting the starting points as 0-ary operators) will be of diverse types.

We keep the constructor exactly as it is required on the representation type.
This is combined with an "immediate content" function on the domain of the constructor to give a relation which indicates which values are immediate constituents of a constructed value, and then we close up the empty set on the principle of adding a constructed value whenever its immediate constituents are available.

In addition to the constructor function and the content information we want to allow some constraint on values which are acceptable for the construction so that it need not be defined over the entire representation type.
In fact this can be coded into the content function by making it reflexive for values which we wish to exclude from the domain.
Actually its type doesn't allow reflexive, but mapping these to the universe of the representation type will do the trick.

\subsection{Generalised Hereditarily-P Sets}

The notion of a set being ``hereditarily P'' for some property of sets P is to be generalised in the following two ways:

\begin{enumerate}
\item Rather than taking any fixed notion of set, the machinery is to work in as broad a range of ``membership structures'' as possible, the minimal conditions on membership structures for this to work will be worked out as we go.
\item To allow more complex constructions, the generalised ``hereditarily'' will be parameterised by something more complex than a simple property, in particular it is not to be required that all the members of a ``hereditarily X'' set will be ``hereditarily X'', but only the bona-fide ``constituents''.
For example, in the notion of a hereditarily pure function, it is not the members of a hereditarily pure function which must be hereditarily pure functions, rather, the elements of its domain and range.
\end{enumerate}

\subsection{Hereditarily Over a Function}

Parameterising the notion of hereditarily by a relation allows the notion to be relativised to an arbitrary set theory or pseudo-set-theory.
As well as permitting the notion to be used within exotic set theories such as NF, the generalised notion can be applied to domains like the natural numbers, which given a suitable relation will masquerade as hereditarily finite sets, and can be further refined by hereditarily-p notions.

However, the presumption still present is that, albeit with a generalised notion of membership, the kinds construction involved are simply set formation.

It is easy to find natural examples which do not fit into this scheme.
For example the hereditarily pure functions.
If one simply takes the property P of being a pure function, then Hereditarily-P does not give what is desired, because the formation of a pure function over pure functions involves a construction more complex than set formation (or at least, requires multiple set formations, firstly the formation of ordered pairs and then the collection of the ordered pairs into a set).

To allow for this kind of generalisation we must leave behind the idea that the construction is taking place in the domain of a set theory.

We do this by working from a function which models the available constructions or derivations by mapping a set of objects (which need not themselves be sets) to the set of new objects which can be constructed from those objects.
Other things might be used in the construction, but no other ``objects'', so the purpose of this map, which I will call a content function, is not to fully capture the details of the available constructors or derivation rules, but rather to capture the {\it content} of the available constructions or the premises of the rules.

From a content function a fixed point can be obtained.
This is done by converting it into a monotonic function and then using the Knaster-Tarski result.

ⓈHOLCONST
│ ⦏Fun2MonoFun⦎: ('a SET → 'a SET) → ('a SET → 'a SET)
├──────
│ ∀ f s⦁ Fun2MonoFun f s = {x | ∃t⦁ t ⊆ s ∧ x ∈ f t}
■

This function does always deliver a monotonic result:

=GFT
⦏F2MF_Monotonic_thm⦎ =
	⊢ ∀ r⦁ Monotonic (Fun2MonoFun f)
=TEX

\ignore{
=SML
val Fun2MonoFun_def = get_spec ⌜Fun2MonoFun⌝;
set_goal([],⌜∀f⦁ Monotonic (Fun2MonoFun f)⌝);
a (rewrite_tac [Monotonic_def, Fun2MonoFun_def, sets_ext_clauses]
	THEN contr_tac
	THEN REPEAT (asm_fc_tac[]));
val F2MF_Monotonic_thm = save_pop_thm "F2MF_Monotonic_thm";
=TEX
}%ignore

We now define the function which maps such a content function to the least fixed point of the monotonic function obtained from it.

ⓈHOLCONST
│ ⦏HeredFun⦎: ('a SET → 'a SET) → 'a SET
├──────────
│ ∀ f⦁ HeredFun f = Lfp (Fun2MonoFun f)
■

And its dual:

ⓈHOLCONST
│ ⦏CoHeredFun⦎: ('a SET → 'a SET) → 'a SET
├──────────
│ ∀ f⦁ CoHeredFun f = Gfp (Fun2MonoFun f)
■

We define appropriate notions of closure and co-closure for expressing the key properties of these sets.

=SML
declare_infix (300, "ClosedUnderFun");
declare_infix (300, "OpenUnderFun");
=TEX 

ⓈHOLCONST
│ $⦏ClosedUnderFun⦎ : 'a SET → ('a SET → 'a SET) → BOOL
├────────
│ ∀s f⦁ s ClosedUnderFun f ⇔ s ClosedUnder (Fun2MonoFun f)  
■

ⓈHOLCONST
│ $⦏OpenUnderFun⦎ : 'a SET → ('a SET → 'a SET) → BOOL
├───────
│ ∀s f⦁ s OpenUnderFun f ⇔ s OpenUnder (Fun2MonoFun f)
■

We then prove the obvious claims about closure and openness, and the simplest induction and co-induction principles.

=GFT
⦏ClosedUnderFun_thm⦎ =
	⊢ ∀ f s⦁ s ClosedUnderFun f ⇔ (∀ t⦁ t ⊆ s ⇒ f t ⊆ s)
⦏OpenUnderFun_thm1⦎ =
	⊢ ∀ f s⦁ s OpenUnderFun f
         ⇔ (∀ t⦁ s ⊆ t ⇒ (∀ e⦁ e ∈ s ⇒ (∃ t'⦁ t' ⊆ t ∧ e ∈ f t')))
⦏OpenUnderFun_thm2⦎ =
	⊢ ∀ f s⦁ s OpenUnderFun f ⇔ (∀ t⦁ s ⊆ t ⇒ s ⊆ Fun2MonoFun f t)
=TEX

\ignore{
=SML
val Fun2MonoFun_def = get_spec ⌜Fun2MonoFun⌝;
val HeredFun_def = get_spec ⌜HeredFun⌝;
val CoHeredFun_def = get_spec ⌜CoHeredFun⌝;
val ClosedUnderFun_def = get_spec ⌜$ClosedUnderFun⌝;
val OpenUnderFun_def = get_spec ⌜$OpenUnderFun⌝;
=TEX
=SML
set_goal([], ⌜∀f s⦁ s ClosedUnderFun f ⇔ (∀ t⦁ t ⊆ s ⇒ f t ⊆ s)⌝);
a (rewrite_tac[ClosedUnderFun_def, ClosedUnder_def, Fun2MonoFun_def]);
a (PC_T1 "hol1" prove_tac[ClosedUnderFun_def, ClosedUnder_def, Fun2MonoFun_def]);
val ClosedUnderFun_thm = save_pop_thm "ClosedUnderFun_thm";

set_goal([], ⌜∀f s⦁ s OpenUnderFun f ⇔
	(∀t⦁ s ⊆ t ⇒ ∀e⦁ e ∈ s ⇒ ∃t'⦁ t' ⊆ t ∧ e ∈ f t')⌝);
a (PC_T1 "hol1" rewrite_tac[OpenUnderFun_def, OpenUnder_def, Fun2MonoFun_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (asm_ufc_tac[]);
a (∃_tac ⌜t'⌝ THEN asm_prove_tac[]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜s⌝);
a (asm_ufc_tac[]);
a (∃_tac ⌜t'⌝ THEN asm_rewrite_tac[]);
val OpenUnderFun_thm1 = save_pop_thm "OpenUnderFun_thm1";

set_goal([], ⌜∀f s⦁ s OpenUnderFun f ⇔ (∀ t⦁ s ⊆ t ⇒ s ⊆ (Fun2MonoFun f) t)⌝);
a (rewrite_tac[OpenUnderFun_def, OpenUnder_def]
	THEN REPEAT strip_tac
	THEN_TRY asm_fc_tac[]);
(* *** Goal "1" *** *)
a (fc_tac [rewrite_rule [Monotonic_def] (∀_elim ⌜f⌝ F2MF_Monotonic_thm)]);
a (spec_nth_asm_tac 1 ⌜f⌝ THEN all_fc_tac [⊆_trans_thm]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 1 ⌜s⌝);
val OpenUnderFun_thm2 = save_pop_thm "OpenUnderFun_thm2";
=TEX
}%ignore

=GFT
⦏HeredFun_Closed_thm⦎ =
	⊢ ∀f⦁ (HeredFun f) ClosedUnderFun f
⦏HeredFun_Closed_thm1⦎ =
	⊢ ∀ f x⦁ (∃ t⦁ (∀ x⦁ x ∈ t ⇒ x ∈ HeredFun f) ∧ x ∈ f t)
		⇒ x ∈ HeredFun f

⦏HeredFun_Open_thm⦎ =
	⊢ ∀f⦁ (HeredFun f) OpenUnderFun f
⦏HeredFun_Open_thm1⦎ =
	⊢ ∀ f x⦁ x ∈ HeredFun f
	⇒ (∃ t⦁ (∀ x⦁ x ∈ t ⇒ x ∈ HeredFun f) ∧ x ∈ f t)

⦏HeredFun_induction_thm⦎ =
	⊢ ∀f s⦁ s ClosedUnderFun f ⇒ HeredFun f ⊆ s
⦏HeredFun_induction_thm1⦎ =
	⊢ ∀f s⦁ (∀t⦁ t ⊆ s ⇒ f t ⊆ s) ⇒ HeredFun f ⊆ s
=TEX

\ignore{
=SML
set_goal([], ⌜∀f⦁ (HeredFun f) ClosedUnderFun f⌝);
a (rewrite_tac [HeredFun_def, ClosedUnderFun_def]);
a (REPEAT strip_tac);
a (lemma_tac ⌜Monotonic (Fun2MonoFun f)⌝
	THEN1 (rewrite_tac [F2MF_Monotonic_thm]));
a (FC_T rewrite_tac [lfp_closed_thm]);
val HeredFun_Closed_thm = save_pop_thm "HeredFun_Closed_thm";

set_goal([], ⌜∀ f x⦁ (∃ t⦁ (∀ x⦁ x ∈ t ⇒ x ∈ HeredFun f) ∧ x ∈ f t)
         ⇒ x ∈ HeredFun f⌝);
a (REPEAT strip_tac
	THEN strip_asm_tac (rewrite_rule
		[ClosedUnderFun_def, ClosedUnder_def, Fun2MonoFun_def, sets_ext_clauses]
		HeredFun_Closed_thm));
a (list_spec_nth_asm_tac 1 [⌜f⌝, ⌜x⌝]);
a (spec_nth_asm_tac 1 ⌜t⌝);
a (asm_fc_tac[]);
val HeredFun_Closed_thm1 = save_pop_thm "HeredFun_Closed_thm1";

set_goal([], ⌜∀f⦁ (HeredFun f) OpenUnderFun f⌝);
a (rewrite_tac [HeredFun_def, OpenUnderFun_def]);
a (REPEAT strip_tac);
a (lemma_tac ⌜Monotonic (Fun2MonoFun f)⌝
	THEN1 (rewrite_tac [F2MF_Monotonic_thm]));
a (FC_T rewrite_tac [lfp_open_thm]);
val HeredFun_Open_thm = save_pop_thm "HeredFun_Open_thm";

set_goal([], ⌜∀f s⦁ s ClosedUnderFun f ⇒ HeredFun f ⊆ s⌝);
a (rewrite_tac [HeredFun_def, ClosedUnderFun_def]);
a (REPEAT strip_tac);
a (lemma_tac ⌜Monotonic (Fun2MonoFun f)⌝
	THEN1 (rewrite_tac [F2MF_Monotonic_thm]));
a (ALL_FC_T rewrite_tac [lfp_induction_thm]);
val HeredFun_induction_thm = save_pop_thm "HeredFun_induction_thm";

set_goal([], ⌜∀f s⦁ (∀t⦁ t ⊆ s ⇒ f t ⊆ s) ⇒ HeredFun f ⊆ s⌝);
a (rewrite_tac [HeredFun_def]);
a (REPEAT strip_tac);
a (lemma_tac ⌜Monotonic (Fun2MonoFun f)⌝
	THEN1 (rewrite_tac [F2MF_Monotonic_thm]));
a (ufc_tac [lfp_induction_thm]);
a (spec_nth_asm_tac 1 ⌜s⌝);
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac [ClosedUnder_def, Fun2MonoFun_def]);
a (DROP_NTH_ASM_T 4 ante_tac
	THEN prove_tac [sets_ext_clauses]);
val HeredFun_induction_thm1 = save_pop_thm "HeredFun_induction_thm1";
=TEX

=IGN
set_goal([], ⌜x ∈ HeredFun f⌝);
a (rewrite_tac [HeredFun_def]);
a (lemma_tac ⌜Monotonic (Fun2MonoFun f)⌝
	THEN1 rewrite_tac [F2MF_Monotonic_thm]);
a (all_asm_fc_tac [lfp_fixedpoint_thm]);
a (SYM_ASMS_T once_rewrite_tac);
a (once_rewrite_tac [Fun2MonoFun_def]);

set_goal([], ⌜∀ f x⦁ x ∈ HeredFun f ⇒ (∃ t⦁ (∀ x⦁ x ∈ t ⇒ x ∈ HeredFun f) ∧ x ∈ f t)⌝);
a (REPEAT strip_tac);
a (⊆_induction_tac HeredFun_induction_thm ⌜x⌝);

val ⊆_induction_canon = 
	REPEAT_CAN (
		simple_∀_rewrite_canon
		ORELSE_CAN (rule_canon undisch_rule)
		ORELSE_CAN ∧_rewrite_canon)
	THEN_CAN ⊆_ext_canon
	THEN_CAN all_⇒_intro_canon;

fun ⊆_induction_tac thm term:TACTIC = fn (asms, concl) =>
	let val thm1 = rewrite_rule [] (∀_elim (mk_set_comp (term, concl)) thm)
	in (bc_tac (⊆_induction_canon thm1)) (asms, concl)
	end;

fun ⊆_induction_rule thm term = fn (asms, concl) =>
	let val thm1 = ∀_elim (mk_set_comp (term, concl)) thm
	in ⊆_induction_canon thm1
	end;

⊆_induction_rule HeredFun_induction_thm ⌜x⌝ (top_goal());
⊆_induction_canon HeredFun_induction_thm;
map (rewrite_rule []) it;
dest_simple_term ⌜{x | x=x}⌝;
a (bc_tac (map all_∀_intro it));
set_flag( "pp_show_HOL_types", true);
rewrite_rule [sets_ext_clauses] (undisch_rule (all_∀_elim HeredFun_induction_thm));
a (REPEAT ∀_tac THEN rewrite_tac [HeredFun_def] THEN strip_tac);
a (asm_tac (∀_elim ⌜f⌝ F2MF_Monotonic_thm));
a (ALL_FC_T (MAP_EVERY ante_tac)
	[rewrite_rule [OpenUnder_def, sets_ext_clauses] lfp_open_thm]);
a (rewrite_tac [Fun2MonoFun_def]);

a (list_spec_nth_asm_tac 1 [⌜f⌝, ⌜x⌝]);
a (spec_nth_asm_tac 1 ⌜t⌝);
a (asm_fc_tac[]);
val HeredFun_Closed_thm1 = save_pop_thm "HeredFun_Closed_thm1";
=TEX

=SML	
val HeredFun_Open_thm1 = save_thm ("HeredFun_Open_thm1",
	rewrite_rule [OpenUnderFun_def, OpenUnder_def, Fun2MonoFun_def, sets_ext_clauses]
	HeredFun_Open_thm);
=TEX
}%ignore

=GFT
⦏CoHeredFun_Closed_thm⦎ =
	⊢ ∀f⦁ (CoHeredFun f) ClosedUnderFun f
⦏CoHeredFun_Open_thm⦎ =
	⊢ ∀f⦁ (CoHeredFun f) OpenUnderFun f

⦏CoHeredFun_coinduction_thm⦎ =
	⊢ ∀s f⦁ s OpenUnderFun f ⇒ s ⊆ CoHeredFun f
⦏CoHeredFun_coinduction_thm2⦎ =
	⊢ ∀ s f⦁ s ⊆ Fun2MonoFun f s ⇒ s ⊆ CoHeredFun f
=TEX

\ignore{
=SML
set_goal([], ⌜∀f⦁ (CoHeredFun f) ClosedUnderFun f⌝);
a (rewrite_tac [CoHeredFun_def, ClosedUnderFun_def]);
a (REPEAT strip_tac);
a (lemma_tac ⌜Monotonic (Fun2MonoFun f)⌝
	THEN1 (rewrite_tac [F2MF_Monotonic_thm]));
a (FC_T rewrite_tac [gfp_closed_thm]);
val CoHeredFun_Closed_thm = save_pop_thm "CoHeredFun_Closed_thm";

set_goal([], ⌜∀f⦁ (CoHeredFun f) OpenUnderFun f⌝);
a (rewrite_tac [CoHeredFun_def, OpenUnderFun_def]);
a (REPEAT strip_tac);
a (lemma_tac ⌜Monotonic (Fun2MonoFun f)⌝
	THEN1 (rewrite_tac [F2MF_Monotonic_thm]));
a (FC_T rewrite_tac [gfp_open_thm]);
val CoHeredFun_Open_thm = save_pop_thm "CoHeredFun_Open_thm";

set_goal([], ⌜∀s f⦁ s OpenUnderFun f ⇒ s ⊆ CoHeredFun f⌝);
a (rewrite_tac [CoHeredFun_def, OpenUnderFun_def]);
a (REPEAT strip_tac);
a (lemma_tac ⌜Monotonic (Fun2MonoFun f)⌝
	THEN1 (rewrite_tac [F2MF_Monotonic_thm]));
a (ALL_FC_T rewrite_tac [gfp_coinduction_thm]);
val CoHeredFun_coinduction_thm = save_pop_thm "CoHeredFun_coinduction_thm";

val CoHeredFun_coinduction_thm2 = save_thm ("CoHeredFun_coinduction_thm2", rewrite_rule [OpenUnderFun_def, OpenUnder_def] CoHeredFun_coinduction_thm);

=TEX
}%ignore

The following stronger induction and co-induction principles correspond to the notion of strong induction principle in the hol4 package for definition of relations by taking transitive closures.
These principles are not specific to the definition of relations but their inclusion is motivated by problems arising in the definition of relations, more specifically in obtaining Church-Rosser or confluence results in combinatory logics.

The following principle is a very slight strengthening of the basic induction principle:


=GFT
⦏HeredFun_induct_thm0⦎ =
	⊢ ∀f s⦁ (s ∩ HeredFun f) ClosedUnderFun f ⇒ HeredFun f ⊆ s
=IGN
HeredFun_strong_induct_thm2 =
	⊢ ∀f s⦁ (∀t⦁ t ⊆ (s ∩ HeredFun f) ⇒ f t ⊆ HeredFun f) ⇒ HeredFun f ⊆ s

=TEX


\ignore{
=SML
set_goal([], ⌜∀f s⦁ (s ∩ HeredFun f) ClosedUnderFun f ⇒ HeredFun f ⊆ s⌝);
a (REPEAT strip_tac);
a (fc_tac [list_∀_elim [⌜f⌝, ⌜s ∩ HeredFun f⌝] HeredFun_induction_thm]);
a (POP_ASM_T ante_tac THEN PC_T1 "hol1" prove_tac[]);
val HeredFun_induct_thm0 = save_pop_thm "HeredFun_induct_thm0";

=IGN
set_goal([], ⌜∀f s⦁ (∀t⦁ t ⊆ (s ∩ HeredFun f) ⇒ f t ⊆ s)
	⇒ HeredFun f ⊆ s⌝);
a (REPEAT ∀_tac);
a (fc_tac [list_∀_elim [⌜f⌝, ⌜s ∩ HeredFun f⌝] HeredFun_induction_thm0]);


stop;

=TEX
}%ignore


\subsection{Collections of Rules}

When I came to try out the above (see \cite{rbjt008}) I concluded that the most convenient kind of object to define is a {\it set of rules}, in which each rule is a set of premises and a single conclusion.
This is a relation which need not be functional and need not be one-one (there can be several conclusions from the same set of premises, and several distinct sets of premises which yield the same conclusion).

So I am defining here how to convert one of those things into a content function.

ⓈHOLCONST
│ ⦏Rules2Fun⦎: ('a SET × 'a) SET → ('a SET → 'a SET)
├──────
│ ∀ r⦁ Rules2Fun r = λs⦁ {x | (s, x) ∈ r}
■

{\it Rules2Fun} is a bijection and so could be inverted.

\subsection{Hereditarily Over a Relation}

An alternative, but less general approach is to define the constructor from a `content' relation which indicates when a value is an immediate constituent of another value.
This approach is less general because for some inductive definitions of sets, e.g. for the set of theorems of a formal system, there are several ways of constructing the same object and so no obvious content relation which can be used to define the set.

ⓈHOLCONST
│ ⦏Rel2Fun⦎: ('a → 'a → BOOL) → ('a SET → 'a SET)
├──────
│ ∀ r⦁ Rel2Fun r = λs⦁ {x | {y | r y x} = s}
■

We now define the function which maps a content relation to the least fixed point of the monotonic function obtained from it.

ⓈHOLCONST
│ ⦏HeredRel⦎: ('a → 'a → BOOL) → 'a SET
├──────
│ ∀ r⦁ HeredRel r = HeredFun (Rel2Fun r)
■

And its dual:

ⓈHOLCONST
│ ⦏CoHeredRel⦎: ('a → 'a → BOOL) → 'a SET
├──────
│ ∀ r⦁ CoHeredRel r = CoHeredFun (Rel2Fun r)
■

To accomplish this we need the concepts of closure and co-closure for sets relative to one of our `content relations'

=SML
declare_infix (300, "ClosedUnderRel");
declare_infix (300, "OpenUnderRel");
=TEX 

ⓈHOLCONST
│ $⦏ClosedUnderRel⦎ : 'a SET → ('a → 'a → BOOL) → BOOL
├
│ ∀s r⦁ s ClosedUnderRel r ⇔ s ClosedUnderFun (Rel2Fun r)
■

ⓈHOLCONST
$⦏OpenUnderRel⦎ : 'a SET → ('a → 'a → BOOL) → BOOL
├
∀s r⦁ s OpenUnderRel r ⇔ s OpenUnderFun (Rel2Fun r)
■

=GFT
⦏HeredRel_Closed_thm⦎ =
	⊢ ∀f⦁ (HeredRel f) ClosedUnderRel f
⦏HeredRel_Open_thm⦎ =
	⊢ ∀f⦁ (HeredRel f) OpenUnderRel f
⦏HeredRel_induction_thm⦎ =
	⊢ ∀s f⦁ s ClosedUnderRel f ⇒ HeredRel f ⊆ s
=TEX

\ignore{
=SML
val Rel2Fun_def = get_spec ⌜Rel2Fun⌝;
val HeredRel_def = get_spec ⌜HeredRel⌝;
val CoHeredRel_def = get_spec ⌜CoHeredRel⌝;
val ClosedUnderRel_def = get_spec ⌜$ClosedUnderRel⌝;
val OpenUnderRel_def = get_spec ⌜$OpenUnderRel⌝;
=TEX
=SML
set_goal([], ⌜∀f⦁ (HeredRel f) ClosedUnderRel f⌝);
a (rewrite_tac [HeredRel_def, ClosedUnderRel_def, HeredFun_Closed_thm]);
val HeredRel_Closed_thm = save_pop_thm "HeredRel_Closed_thm";
=TEX
=SML
set_goal([], ⌜∀f⦁ (HeredRel f) OpenUnderRel f⌝);
a (rewrite_tac [HeredRel_def, OpenUnderRel_def, HeredFun_Open_thm]);
val HeredRel_Open_thm = save_pop_thm "HeredRel_Open_thm";
=TEX
=SML
set_goal([], ⌜∀s f⦁ s ClosedUnderRel f ⇒ HeredRel f ⊆ s⌝);
a (rewrite_tac [HeredRel_def, ClosedUnderRel_def, HeredFun_induction_thm]);
val HeredRel_induction_thm = save_pop_thm "HeredRel_induction_thm";
=TEX
}%ignore

=GFT
⦏CoHeredRel_Closed_thm⦎ =
	⊢ ∀f⦁ (CoHeredRel f) ClosedUnderRel f
⦏CoHeredRel_Open_thm⦎ =
	⊢ ∀f⦁ (CoHeredRel f) OpenUnderRel f
⦏CoHeredRel_coinduction_thm⦎ =
	⊢ ∀s f⦁ s OpenUnderRel f ⇒ s ⊆ CoHeredRel f
=TEX

\ignore{
=SML
set_goal([], ⌜∀f⦁ (CoHeredRel f) ClosedUnderRel f⌝);
a (rewrite_tac [CoHeredRel_def, ClosedUnderRel_def, CoHeredFun_Closed_thm]);
val CoHeredRel_Closed_thm = save_pop_thm "CoHeredRel_Closed_thm";
=TEX
=SML
set_goal([], ⌜∀f⦁ (CoHeredRel f) OpenUnderRel f⌝);
a (rewrite_tac [CoHeredRel_def, OpenUnderRel_def, CoHeredFun_Open_thm]);
val CoHeredRel_Open_thm = save_pop_thm "CoHeredRel_Open_thm";
=TEX
=SML
set_goal([], ⌜∀s f⦁ s OpenUnderRel f ⇒ s ⊆ CoHeredRel f⌝);
a (rewrite_tac [CoHeredRel_def, OpenUnderRel_def, CoHeredFun_coinduction_thm]);
val CoHeredRel_coinduction_thm = save_pop_thm "CoHeredRel_coinduction_thm";
=TEX
}%ignore

\subsection{Hereditarily Over a Property}

We now presume that the construction is always set formation and that the sets which are formed are those satisfying the given property.
However, everything is relativised to an arbitrary membership structure.

This is really (only a small generalisation of) what mathematicians call ``Hereditarily-P'' sets, so I shall give it its proper name.

A content relation is obtained from a property over a membership structure as follows:

ⓈHOLCONST
│ ⦏Prop2Rel⦎: ('a SET × ('a → 'a → BOOL)) → ('a → BOOL) → ('a → 'a → BOOL)
├──────
│ ∀ (X, $<<) p⦁ Prop2Rel (X, $<<) p = λx y⦁ x << y ∧ p y
■

ⓈHOLCONST
│ ⦏Hereditary⦎: ('a SET × ('a → 'a → BOOL)) → ('a → BOOL) → 'a SET
├──────
│ ∀ (X, $<<) p⦁ Hereditary (X, $<<) p = HeredRel (Prop2Rel (X, $<<) p)
■

And its dual:

ⓈHOLCONST
│ ⦏CoHereditary⦎: ('a SET × ('a → 'a → BOOL)) → ('a → BOOL) → 'a SET
├──────
│ ∀ (X, $<<) p⦁ CoHereditary (X, $<<) p = CoHeredRel (Prop2Rel (X, $<<) p)
■

To accomplish this we need the concepts of closure and co-closure for sets relative to one of our `content relations'

ⓈHOLCONST
│ $⦏ClosedUnderProp⦎ : ('a SET × ('a → 'a → BOOL)) → 'a SET
│ 			→ ('a → BOOL) → BOOL
├
│ ∀(X, $<<) s p⦁ ClosedUnderProp (X, $<<) s p
│ 	⇔ s ClosedUnderRel (Prop2Rel (X, $<<) p)
■

ⓈHOLCONST
│ $⦏OpenUnderProp⦎ : ('a SET × ('a → 'a → BOOL)) → 'a SET
│ 			→ ('a → BOOL) → BOOL
├
│ ∀(X, $<<) s p⦁ OpenUnderProp (X, $<<) s p
│ 	⇔ s OpenUnderRel (Prop2Rel (X, $<<) p)
■

=GFT
⦏Hereditary_Closed_thm⦎ =
	⊢ ∀(X, $<<) p⦁
	ClosedUnderProp (X, $<<) (Hereditary (X, $<<) p) p
⦏Hereditary_Open_thm⦎ =
	⊢ ∀(X, $<<) p⦁
	OpenUnderProp (X, $<<) (Hereditary (X, $<<) p) p
⦏Hereditary_induction_thm⦎ =
	⊢ ∀(X, $<<) s p⦁
	ClosedUnderProp (X, $<<) s p ⇒ Hereditary (X, $<<) p ⊆ s
=TEX

\ignore{
=SML
val Prop2Rel_def = get_spec ⌜Prop2Rel⌝;
val Hereditary_def = get_spec ⌜Hereditary⌝;
val CoHereditary_def = get_spec ⌜CoHereditary⌝;
val ClosedUnderProp_def = get_spec ⌜$ClosedUnderProp⌝;
val OpenUnderProp_def = get_spec ⌜$OpenUnderProp⌝;
=TEX
=SML
set_goal([], ⌜∀(X, $<<) p⦁ ClosedUnderProp (X, $<<) (Hereditary (X, $<<) p) p⌝);
a (rewrite_tac [Hereditary_def, ClosedUnderProp_def, HeredRel_Closed_thm]);
a (REPEAT strip_tac);
val Hereditary_Closed_thm = save_pop_thm "Hereditary_Closed_thm";
=TEX
=SML
set_goal([], ⌜∀(X, $<<) p⦁ OpenUnderProp (X, $<<) (Hereditary (X, $<<) p) p⌝);
a (rewrite_tac [Hereditary_def, OpenUnderProp_def, HeredRel_Open_thm]
	THEN REPEAT strip_tac);
val Hereditary_Open_thm = save_pop_thm "Hereditary_Open_thm";
=TEX
=SML
set_goal([], ⌜∀(X, $<<) s p⦁ ClosedUnderProp (X, $<<) s p ⇒ Hereditary (X, $<<) p ⊆ s⌝);
a (rewrite_tac [Hereditary_def, ClosedUnderProp_def, HeredRel_induction_thm]
	THEN REPEAT strip_tac);
val Hereditary_induction_thm = save_pop_thm "Hereditary_induction_thm";
=TEX
}%ignore

=GFT
⦏CoHereditary_Closed_thm⦎ =
	⊢ ∀(X, $<<) p⦁
	ClosedUnderProp (X, $<<) (CoHereditary (X, $<<) p) p
⦏CoHereditary_Open_thm⦎ =
	⊢ ∀(X, $<<) p⦁
	OpenUnderProp (X, $<<) (CoHereditary (X, $<<) p) p
⦏CoHereditary_coinduction_thm⦎ =
	⊢ ∀(X, $<<) s p⦁
	OpenUnderProp (X, $<<) s p ⇒ s ⊆ CoHereditary (X, $<<) p
=TEX

\ignore{
=SML
set_goal([], ⌜∀(X, $<<) p⦁ ClosedUnderProp (X, $<<) (CoHereditary (X, $<<) p) p⌝);
a (rewrite_tac [CoHereditary_def, ClosedUnderProp_def, CoHeredRel_Closed_thm]
	THEN REPEAT strip_tac);
val CoHereditary_Closed_thm = save_pop_thm "CoHereditary_Closed_thm";
=TEX
=SML
set_goal([], ⌜∀(X, $<<) p⦁ OpenUnderProp (X, $<<) (CoHereditary (X, $<<) p) p⌝);
a (rewrite_tac [CoHereditary_def, OpenUnderProp_def, CoHeredRel_Open_thm]
	THEN REPEAT strip_tac);
val CoHereditary_Open_thm = save_pop_thm "CoHereditary_Open_thm";
=TEX
=SML
set_goal([], ⌜∀(X, $<<) s p⦁ OpenUnderProp (X, $<<) s p ⇒ s ⊆ CoHereditary (X, $<<) p⌝);
a (rewrite_tac [CoHereditary_def, OpenUnderProp_def]
	THEN REPEAT strip_tac);
a (all_asm_fc_tac [CoHeredRel_coinduction_thm]);
val CoHereditary_coinduction_thm = save_pop_thm "CoHereditary_coinduction_thm";
=TEX
}%ignore

\subsection{Sets Defined Using CCPs}

The next two variations on the theme move us closer to the form in which the constructors for an inductively defined set are likely to be presented, and in particular to the kinds of constructors whose definitions can be derived from a {\it signature} for the desired inductive type.
It is particularly relevant to inductive definitions in a type theory rather than a set theory, where the constructors may have diverse types and some work is involved in obtaining a monotonic function whose fixed point can be taken.

There are two cases we consider.

In the most common case the compounded constructor (operating over the disjoint union of mutually defined sets) is an injection, and the content relation is probably the best way to define the type, which turns out to be the field of the well-founded part of the content relation, so that a well-founded relation for inductive proofs comes easily.

In the less common case the compounded constructor is not injective, and cannot therefore be adequately represented by a content relation, so we use a function from content sets to the set of objects with that content (allowing that the same object may appear in more than one of these sets as a result of being constructible by more than one constructor).

A CCP (constructor, content, predicate triple) consisting of:
\begin{enumerate}
\item a compounded constructor function
\item a content function
\item a compounded predicate
\end{enumerate}

play an important role here and in the sequel and is therefore defined as a HOL labelled product as follows:

ⓈHOLLABPROD ⦏CCP⦎─────
│ ⦏Constructor⦎: 'b → 'a;
│ ⦏Content⦎: 'b → 'a SET;
│ ⦏Predicate⦎: 'b → BOOL
■──────────────

In this the type variable $'b$ is used for the type of the compounded constructor function which is derived from the type of the desired constructors as follows.

\begin{enumerate}
\item the type is the disjoint union of the domain types for each individual constructor
\item for each constructor the domain type is the product of the types of the domains if it is a curried constructor, e.g. for a constructor of type $X → Y → Z$ the domain type is $X × Y$.
types to be introduced.
\end{enumerate}

The second type parameter is the representation type over which the constructors are defined, and which will be used to introduce the new types (if required).

A CCP can be converted into either a relation or a function as required for $HeredFun$ or $HeredRel$ using the following functions.

ⓈHOLCONST
│ ⦏CCP2Fun⦎: ('a,'b)CCP → ('a SET → 'a SET)
├──────
│ ∀ ccp x⦁ CCP2Fun ccp x =
│	{y | ∃b⦁ y = Constructor ccp b ∧ x = Content ccp b ∧ Predicate ccp b}
■

ⓈHOLCONST
│ ⦏CCP2Rel⦎: ('a,'b) CCP → ('a → 'a → BOOL)
├──────
│ ∀ ccp x y⦁ CCP2Rel ccp x y ⇔
│	∃b⦁ y = Constructor ccp b ∧ x ∈ Content ccp b ∧ Predicate ccp b
■

In cases such as that of the ``hereditarily pure functions'' which fall outside the scope of definition using $Hereditarily$ but are similar in spirit the desired effect can be obtained using a $CCP2$ in which the constructor is the identity function.
The predicate in this particular case would be the property of being a many one relation, and the content function would yield the field of the relation.
The $CCP2Rel$ conversion and $HeredRel$ would then yield the desired set and an induction principle.

\subsection{Using Multiple CCP's}

In principle it is possible to obtain a fixed point from a system of constructors via a single CCP in which the type variable $'b$ is instantiated to the disjoint union of the domains of the (uncurried) constructors.
This however leads, to unnecessarily large types, and to complications in the constructor function which arise from manipulating disjoint unions with many components.

The domain types of the constructors have only a transitory appearance in the process of obtaining a fixed point, as can be seen from the type of the functions $CCP2Fun$ and $CCP2Rel$ which convert a structure in which the type variable $'b$ occurs into one in which it does not occur.
This suggests that it may be best to convert each constructor individually into a content relation before attempting to compound the constructors and obtain a fixed point.

The details of how this can be done are sensitive to issues which have not yet been considered, relating to the manner in which constructors are compounded.
In the most common kind of inductive definition used in computer science it is expected that the constructors will be injective and will have disjoint ranges, resulting in an inductive type which is analogous to an initial or free algebra.
In other cases this may not be required.

The following definitions are intended only to address the former case.

In compounding the constructors it is necessary to ensure that the ranges of the constructors are disjoint in the compounded constructor, and also to ensure where there is more than one type that the types are disjoint, and that only objects of the appropriate `type' are supplied to the individual constructors in the compounded constructor.
The disjointness of the constructors is to be achieved by some kind of tagging operation in which the value yielded by a constructor is tagged with a value unique to that constructor.
This would also suffice to make the types disjoint, but it seems more convenient to use a double tagging to achieve the desired effect.
First the value is tagged by a number which discriminates between the constructors yielding values of a type, and then it is tagged again with the type.

This whole process can be accomplished by a single function application to a list of lists of constructor functions or relations, parameterised by an application specific tagging operation.

ⓈHOLCONST
│ ⦏MapNFun⦎: (ℕ → 'a → 'a) → 'a LIST → 'a LIST
├──────
│ ∀ tf al⦁ MapNFun tf al = Map (Uncurry tf) (Combine (1 ..⋎L (Length al)) al)
■
ⓈHOLCONST
│ ⦏MapTag⦎: (ℕ → 'a → 'a) → ('a → 'a) LIST → ('a → 'a) LIST
├──────
│ ∀ tf al⦁ MapTag tf al = MapNFun (λn f a⦁ tf n (f a)) al
■
ⓈHOLCONST
│ ⦏LiftTag⦎: (ℕ → 'a → 'a) → (ℕ → 'a SET → 'a SET)
├──────
│ ∀ tf n s⦁ LiftTag tf n s = {x | ∃y⦁ y ∈ s ∧ x = tf n y}
■
ⓈHOLCONST
│ ⦏CompoundFuns⦎: (ℕ → 'a → 'a) → ('a SET → 'a SET) LIST LIST
│		→ ('a SET → 'a SET)
├──────
│ ∀ tf asfll ⦁ CompoundFuns tf asfll =
│	ListFunUnion (Map	ListFunUnion (Map (MapTag (LiftTag tf)) asfll))
■
ⓈHOLCONST
│ ⦏HCF⦎: (ℕ → 'a → 'a) → ('a SET → 'a SET) LIST LIST → 'a SET
├──────
│ ∀ tf asfll ⦁ HCF tf asfll = HeredFun (CompoundFuns tf asfll)
■
ⓈHOLCONST
│ ⦏LiftTag2⦎: (ℕ → 'a → 'a) → (ℕ → ('a → 'a → BOOL) → ('a → 'a → BOOL))
├──────
│ ∀ tf n r⦁ LiftTag2 tf n r = λx y⦁ ∃z⦁ r x z ∧ y = tf n z
■
ⓈHOLCONST
│ ⦏MapTag2⦎: (ℕ → 'a → 'a) → ('a → 'a → BOOL) LIST → ('a → 'a → BOOL) LIST
├──────
│ ∀ tf rl⦁ MapTag2 tf rl = MapNFun (λn r x y⦁ ∃z⦁ y = tf n z ∧ r x z) rl
■
ⓈHOLCONST
│ ⦏ListRelUnion⦎: ('a → 'a → BOOL) LIST → ('a → 'a → BOOL)
├──────
│ ∀l x y⦁ ListRelUnion l x y ⇔ ∃r⦁ r ∈⋎L l ∧  r x y
■
ⓈHOLCONST
│ ⦏CompoundRels⦎: (ℕ → 'a → 'a) → ('a → 'a → BOOL) LIST LIST → ('a → 'a → BOOL)
├──────
│ ∀ tf arll ⦁ CompoundRels tf arll =
│	ListRelUnion (Map	ListRelUnion (Map (MapTag2 tf) arll))
■
ⓈHOLCONST
│ ⦏HCR⦎: (ℕ → 'a → 'a) → ('a → 'a → BOOL) LIST LIST → 'a SET
├──────
│ ∀ tf asrll ⦁ HCR tf asrll = HeredRel (CompoundRels tf asrll)
■

\section{INDUCTIVE DEFINITIONS OF RELATIONS}

This section is included to provided support for defining reduction systems over various kinds of terms.
The two kinds of term with which I am most concerned are those of combinatory logic, and of infinitary combinatory logic.
These are of course quite different, the material here is therefore independent of the type of terms involved.

This material is intended to provide an alternative to the facilities available in hol4 for defining relations.
These facilities work from a notation for defining rules, and define the reflexive transitive closure of the given rules, delivering a couple of induction principles and some other useful theorems.

The approach here is to assume that primitive reductions are defined using the normal definitional features in HOL, and provide the obvious operators for obtaining the required kind of relation from these primitive reductions.

The two main operations of interest are that of forming the reflexive and transitive closures and that of making a congruence relation.
The first two are independent of the term structure, but the last one is not.
To reason about that operation independently of the structure we would need to work with parameters which expose some aspects of the structure.








\section{PSEUDO (CO-)INDUCTIVE DEFINITIONS}

This discussion is tainted by the attempt to support a tendentious application of the notion of pseudo-inductive definition to the construction of pure, non-well-founded ontologies of concrete categories and functors.
I don't now have much inclination to believe that it will serve that purpose, but nevertheless would like to understand the notion of pseudo-inductiveness and get some idea of what it is good for.
I therefore propose to remove from this section the material motivated by category theoretic ontology, and in the first instance focus on working over the ideas presented in \cite{forster92}.

Forster \cite{forster92}, introduces pseudo well-foundedness as way of getting a kind of inductive proof principle in NF.
A pseudo-well-founded universe is partitioned into two clasess, in a way which suggests that the desired split of the universe into categories and functors might be definable by adaptation of this principle.
To see the connection observe that the `constituents' of categories are functors, and the constuents of functors are categories.
This means that, in a well-founded universe, a slightly gerrimandered notion of rank (in which rank increases by exactly one as we pass from a functor to a category containing that functor or from a category to a functor over that category) assigns even ranks to categories and odd ranks to functors (we need to enhance the notion of odd and even to cover limit points, which I think need to be even). 
Not only are categories and functors distinguished by the parity of their rank, there is a difference in parity for every descending path according to whether it begins at a category or a functor.
This fits in with the game theoretic flavour of pseudo well-foundedness in which a game is just such a descending path, and the winner of the game is determined by the parity of its length.

For these reasons I thought it might be interesting to see how a `pseudo-inductive` definition adapted from Forster's notion of pseudo-well-foundedness worked in this application.

Since embarking on this path a second method occurred to me, which is to use co-induction.
For the purposes which Forster had in mind (a principle which could be added to the axioms of NF to exclude certain possibly pathological sets (like a set which is its own unit set) while still leaving the important well-founded sets) co-induction would not suffice, since it looks like co-induction for what its worth, comes for free in NF.
However, in this application, where we are filtering out all but categories and functors, the coinductive defintiion will actually do something, and the fact (if it is a fact) that a principle of co-well-foundedness is derivable in NF would suggest that this form of definitions will give the most liberal ontology of the selected kind.

Once co-induction occurs as an alternative non-well-foundedness preserving definitional method, the question arised whether there is a similar dual to psuedo-well foundedness, and how this `pseudo-co-induction' differs from pseduo- and co-induction, if at all.

\subsection{Well Foundedness and Hereditarily Collections}

It would be a good idea eventually to define these first and check back that they are special cases of the pseudo versions and that the well-founded functor/category collections are contained in the pseudo-well-founded collections.

\subsection{Hereditarily and Co-Hereditarily PQ}

Though \cite{rbjt007} defines methods for inductive and co-inductive definition which generalise the notion of a `hereditarily P' set for arbitrary properties of sets P, it does not explicitly cover the present requirement for mutually dependent inductive definitions.
However, this can be achieved by two separate inductive definitions.

No additional machinery is required, the application to yield purely inductive and co-inductive conceptions of category and functor are shown in the next section.

\ignore{

Here is a stab at a {\it hereditarily P} construction suitably generalised.

ⓈHOLCONST
│ ⦏HereditarilyPQ⦎ : (('X → 'X ℙ) × ('X → 'X ℙ) × ('X → BOOL) × ('X → BOOL)) 
│		→ ('X ℙ × 'X ℙ)
├──────
│ ∀c d P Q⦁ HereditarilyPQ (c, d, P, Q) = 
│	(⋂ {X' | ∀x⦁ P x ∧ (∀y z⦁ y ∈ (c x) ∧ z ∈ (d y) ⇒ Q y ∧ z ∈ X') ⇒ x ∈ X'},
│	 ⋂ {Y' | ∀x⦁ Q x ∧ (∀y z⦁ y ∈ (d x) ∧ z ∈ (c y) ⇒ P y ∧ z ∈ Y') ⇒ x ∈ Y'})
■

}%ignore

\subsection{Pseudo-Well-Founded Collections}

I have previously done the kind of category theoretic construction in well-founded set theories.
The same method could be used here, but the result would be similar, the constructed domains would still be well-founded.

I am therefore hoping to extract from Forster's discussion about pseudo-induction some idea about how to do the construction without throwing away the non-well-founded sets.

First we define the concept ``pseudo-well-founded''.
The set theoretic language here (membership relation and power set) is the one which comes with ProofPower HOL (and is set theoretic syntax for predicates in a type theory), the target set theory is modelled as a membership relation (r) over some type (*X).
This is based on the definition in Thomas Forster's book, and is included mainly for reference.

The presentation has been restructured.
The restructuring serves three purposes.
The first is to expose the two classes which partition the universe so that we can talk about them (in the original they are existentially quantified in the definition.
This is done by splitting the definition into two parts, the existential quantification appearing in the second.
The second is to include the claim that these two classes exhaust the type under consideration in the second part, so that the first definition can still be used in a set theory which is not known to be pseudo-well-founded for talking about its pseudo-well-founded part.
Otherwise we would have to add an axiom to NFU for the construction we have in mind.
The third change is to split our definitions of {\it I\_closed} and {\it II\_closed}, to make the structure of proofs more transparent.

ⓈHOLCONST
│ ⦏I_closed⦎ : ('X → 'X → BOOL) → 'X ℙ → BOOL
├──────
│ ∀r w⦁ I_closed r w
│	⇔ ∀x⦁ (∃y⦁ r y x ∧ ∀z⦁ r z y ⇒ z ∈ w) ⇒ x ∈ w
■
ⓈHOLCONST
│ ⦏II_closed⦎ : ('X → 'X → BOOL) → 'X ℙ → BOOL
├──────
│ ∀r w⦁ II_closed r w
│	⇔ ∀x⦁ (∀y⦁ r y x ⇒ ∃z⦁ r z y ∧ z ∈ w) ⇒ x ∈ w
■

ⓈHOLCONST
│ ⦏I_closure⦎ : ('X → 'X → BOOL) → 'X ℙ
├──────
│ ∀r⦁ I_closure r = ⋂{x | I_closed r x}
■

ⓈHOLCONST
│ ⦏II_closure⦎ : ('X → 'X → BOOL) → 'X ℙ
├──────
│ ∀r⦁ II_closure r = ⋂{x | II_closed r x}
■

ⓈHOLCONST
│ ⦏PseudoWellFounded⦎ : ('X → 'X → BOOL) → BOOL
├──────
│ ∀r⦁ PseudoWellFounded r ⇔
│	(I_closure r) ∪ (II_closure r) = Universe
■

\ignore{
=SML
val I_closed_def = get_spec ⌜I_closed⌝;
val II_closed_def = get_spec ⌜II_closed⌝;
val I_closure_def = get_spec ⌜I_closure⌝;
val II_closure_def = get_spec ⌜II_closure⌝;
val PseudoWellFounded_def = get_spec ⌜PseudoWellFounded⌝;
=IGN
set_goal([], ⌜∀R⦁ I_closure R ∩ II_closure R = {}⌝);
a (rewrite_tac [I_closure_def, II_closure_def, I_closed_def, II_closed_def]);
a (PC_T1 "hol1" rewrite_tac [] THEN contr_tac);

set_goal([], ⌜∀R⦁ I_closure R ∩ II_closure R = {}⌝);
a (rewrite_tac [I_closure_def, II_closure_def]);
a (PC_T1 "hol1" rewrite_tac [] THEN contr_tac);
=SML
set_goal([], ⌜∀X' R⦁ I_closed R X' ⇒ I_closure R ⊆ X'⌝);
a (rewrite_tac [I_closure_def] THEN REPEAT strip_tac);
a (PC_T1 "hol1" asm_prove_tac[]);
val I_closure_lemma1 = pop_thm ();

set_goal([], ⌜∀X' R⦁ II_closed R X' ⇒ II_closure R ⊆ X'⌝);
a (rewrite_tac [II_closure_def] THEN REPEAT strip_tac);
a (PC_T1 "hol1" asm_prove_tac[]);
val II_closure_lemma1 = pop_thm ();

val p_induct_thm1 = save_thm ("p_induct_thm1", rewrite_rule [I_closed_def] I_closure_lemma1);
val p_induct_thm2 = save_thm ("p_induct_thm2", rewrite_rule [II_closed_def] II_closure_lemma1);

set_goal([], ⌜∀R x⦁ x ∈ I_closure R ⇒ ¬ x ∈ II_closure R⌝);


set_goal([], ⌜∀R⦁ I_closure R ∩ II_closure R = {}⌝);

set_goal([], ⌜∀R⦁ PseudoWellFounded R ⇔
	∃Ic IIc⦁ Ic ∪ IIc = Universe ∧ Ic ∩ IIc = {}
	∧ (∀ X' R⦁ (∀ x⦁ (∀ y⦁ R y x ⇒ (∃ z⦁ R z y ∧ z ∈ X')) ⇒ x ∈ X')
		⇒ IIc ⊆ X')
	∧ (∀ X' R⦁ (∀ x⦁ (∃ y⦁ R y x ∧ (∀ z⦁ R z y ⇒ z ∈ X')) ⇒ x ∈ X')
		⇒ Ic ⊆ X')
⌝);

=TEX
}%ignore

The following theorems correspond to the induction principles in \cite{forster92}, p14.

=GFT
⦏p_induct_thm1⦎ =
   ⊢ ∀ X' R
     ⦁ (∀ x⦁ (∃ y⦁ R y x ∧ (∀ z⦁ R z y ⇒ z ∈ X')) ⇒ x ∈ X')
         ⇒ I_closure R ⊆ X'

⦏p_induct_thm2⦎ =
   ⊢ ∀ X' R
     ⦁ (∀ x⦁ (∀ y⦁ R y x ⇒ (∃ z⦁ R z y ∧ z ∈ X')) ⇒ x ∈ X')
         ⇒ II_closure R ⊆ X'
=TEX



=GFT

=TEX

\ignore{
=SML
set_goal([], ⌜∀R⦁ I_closed R (I_closure R)⌝);
a (PC_T1 "hol1" rewrite_tac [I_closure_def, I_closed_def] THEN REPEAT strip_tac);
a (REPEAT (asm_fc_tac[]));
val I_closed_closure_lemma = save_pop_thm "I_closed_closure_lemma";

set_goal([], ⌜∀R⦁ II_closed R (II_closure R)⌝);
a (PC_T1 "hol1" rewrite_tac [II_closure_def, II_closed_def] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (REPEAT (asm_fc_tac[]));
val II_closed_closure_lemma = save_pop_thm "II_closed_closure_lemma";

set_goal([], ⌜∀R y⦁ (∀x⦁ x ∈ y ⇒ I_closed R x) ⇒ I_closed R (⋂y)⌝);
a (rewrite_tac [I_closed_def] THEN REPEAT strip_tac);
a (REPEAT (asm_fc_tac[]));
val I_closed_⋂_lemma = save_pop_thm "I_closed_⋂_lemma";

set_goal([], ⌜∀R y⦁ (∀x⦁ x ∈ y ⇒ II_closed R x) ⇒ II_closed R (⋂y)⌝);
a (rewrite_tac [II_closed_def] THEN REPEAT strip_tac);
a (asm_fc_tac []);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (REPEAT (asm_fc_tac[]));
val II_closed_⋂_lemma = save_pop_thm "II_closed_⋂_lemma";

=TEX
}%ignore

=GFT
⦏I_closed_⋂_lemma⦎ =
   ⊢ ∀ R y⦁ (∀ x⦁ x ∈ y ⇒ I_closed R x) ⇒ I_closed R (⋂ y)

⦏II_closed_⋂_lemma⦎ =
   ⊢ ∀ R y⦁ (∀ x⦁ x ∈ y ⇒ II_closed R x) ⇒ II_closed R (⋂ y)

⦏I_closed_closure_lemma⦎ =
   ⊢ ∀ R⦁ I_closed R (I_closure R)

⦏II_closed_closure_lemma⦎ =
   ⊢ ∀ R⦁ II_closed R (II_closure R)
=TEX

\ignore{
=IGN
set_goal([], ⌜∀R⦁ I_closure R ⊆ Universe \ (II_closure R)⌝);
a strip_tac;
a (bc_tac [list_∀_elim [⌜Universe \ (II_closure R)⌝, ⌜R⌝] p_induct_thm1]);
a (PC_T1 "hol1" rewrite_tac [II_closure_def] THEN REPEAT strip_tac);
a (∃_tac ⌜⋂{s' | ∃z'⦁ R z' y ∧ II_closed R s' ∧ ¬ z' ∈ s'}⌝
	THEN PC_T1 "hol1" rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜∀ x⦁ x ∈ {s'|∃ z'⦁ R z' y ∧ II_closed R s' ∧ ¬ z' ∈ s'} ⇒ II_closed R x⌝
	THEN1 (PC_T1 "hol1" prove_tac[]));
a (fc_tac [II_closed_⋂_lemma]);
(* *** Goal "2" *** *)

a (asm_tac II_closed_⋂_lemma);

rewrite_rule [II_closed_def] II_closed_closure_lemma;
II_closure_def;

a (PC_T1 "hol1" rewrite_tac [II_closure_def]);

=TEX
}%ignore


\ignore{
The following theorems show the correspondence between the definitions given above and definition 1.2.1 in \cite{Forster87}.
}%ignore

The idea is to use this to define a notion of "pseudo-hereditarily P" set for a property of sets P, analogously to the notion of a "heridtarily P" set in a well-founded set theory.

This is a bit too simplistic, because the idea of hereditarily P sets is {\it thin} in the following sense.
To prove that a set is hereditarily P you need only to know that each of its members is hereditarily P.
So, in a sense you are only looking one level down.
When you do this with categories and functors the categories and functors alternate as the rank increases.
You either need mutually recursive definitions or else the independent definitions of categories and functors have to look down two levels to express the required condition.
There is already something like this going on in the pseudo-well-foundedness condition.
I've no idea at present whether these work together or not.

\subsection{Pseudo-Well-Founded-PQ Collections}

This is derived from pseudo-well-foundedness by the following generalisations:

\begin{itemize}
\item instead of looking down one level at a time according to the membership relation, the property is parameterised by a function which extracts the `content' from an object.
This might be just the members, or it might be, say, the field of a function.
\item for each of the two classes in question there is an additional parameterised property which is required to be satisfied.
\end{itemize}

Note that we have apparently lost the membership relation here, which is effectively hidden in the content extractors {\it c} and {\it d}.

The structure of this definition is now broken down similarly to that of {\it PseudoWellFounded}.

ⓈHOLCONST
│ ⦏P_closed⦎ : (('X → 'X ℙ) × ('X → 'X ℙ) × ('X → BOOL) × ('X → BOOL))
│		→ 'X ℙ → BOOL
├──────
│ ∀c d P Q w⦁ P_closed (c, d, P, Q) w
│	⇔ ∀x⦁ P x ∧ (∀y⦁ y ∈ (c x) ⇒ Q y ∧ (∃z⦁ z ∈ (d y) ∧ z ∈ w)) ⇒ x ∈ w
■

ⓈHOLCONST
│ ⦏Q_closed⦎ : (('X → 'X ℙ) × ('X → 'X ℙ) × ('X → BOOL) × ('X → BOOL))
│		→ 'X ℙ → BOOL
├──────
│ ∀c d P Q w⦁ Q_closed (c, d, P, Q) w
│	⇔ ∀x⦁ Q x ∧ (∃y⦁ y ∈ (d x) ∧ P y ∧ ∀z⦁ z ∈ (c y) ⇒ z ∈ w) ⇒ x ∈ w
■
ⓈHOLCONST
│ ⦏P_closure⦎ : (('X → 'X ℙ) × ('X → 'X ℙ) × ('X → BOOL) × ('X → BOOL))
│		→ 'X ℙ
├──────
│ ∀z⦁ P_closure z = ⋂{x | P_closed z x}
■
ⓈHOLCONST
│ ⦏Q_closure⦎ : (('X → 'X ℙ) × ('X → 'X ℙ) × ('X → BOOL) × ('X → BOOL))
│		→ 'X ℙ
├──────
│ ∀z⦁ Q_closure z = ⋂{x | Q_closed z x}
■

ⓈHOLCONST
│ ⦏PseudoWellFoundedPQ⦎ :
│	(('X → 'X ℙ) × ('X → 'X ℙ) × ('X → BOOL) × ('X → BOOL)) → BOOL
├──────
│ ∀z⦁ PseudoWellFoundedPQ z ⇔
│	(P_closure z) ∩ (Q_closure z) = {}
│   ∧	(P_closure z) ∪ (Q_closure z) = Universe
■

Need to check that this encompasses pseudo-well-foundedness when suitably parameterised and that the `pseudo' bit only makes a difference for non-well-founded membership structures.

\ignore{
=SML
val P_closed_def = get_spec ⌜P_closed⌝;
val Q_closed_def = get_spec ⌜Q_closed⌝;
val P_closure_def = get_spec ⌜P_closure⌝;
val Q_closure_def = get_spec ⌜Q_closure⌝;
val PseudoWellFoundedPQ_def = get_spec ⌜PseudoWellFoundedPQ⌝;

set_goal([], ⌜∀c d P Q x⦁ x ∈ P_closure (c, d, P, Q) ⇒ P x⌝);
a (REPEAT ∀_tac THEN rewrite_tac[P_closure_def, P_closed_def]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜{x | P x}⌝);
val P_closed_⇒_P_thm = save_pop_thm "P_closed_⇒_P_thm";

set_goal([], ⌜∀c d P Q x⦁ x ∈ Q_closure (c, d, P, Q) ⇒ Q x⌝);
a (REPEAT ∀_tac THEN rewrite_tac[Q_closure_def, Q_closed_def]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜{x | Q x}⌝);
val Q_closed_⇒_Q_thm = save_pop_thm "Q_closed_⇒_Q_thm";

=IGN
set_goal([], ⌜∀c d P Q⦁ P_closed (c, d, P, Q) (P_closure (c, d, P, Q))⌝);
a (REPEAT ∀_tac THEN rewrite_tac[P_closed_def]
	THEN REPEAT strip_tac);
a (rewrite_tac[P_closure_def, P_closed_def] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
a (spec_nth_asm_tac 4 ⌜y⌝);
a (spec_nth_asm_tac 3 ⌜z⌝);
a (spec_nth_asm_tac 6 ⌜z⌝);
(* *** Goal "1" *** *)
a (all_fc_tac [P_closed_⇒_P_thm]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 9 ⌜y'⌝);
a (lemma_tac ⌜P z⌝ THEN1 all_fc_tac [P_closed_⇒_P_thm]);

a (asm_fc_tac[]);

val P_closed_⇒_P_thm = save_pop_thm "P_closed_⇒_P_thm";
=TEX
}%ignore

=GFT
⦏P_closed_⇒_P_thm⦎ =
	⊢ ∀ c d P Q x⦁ x ∈ P_closure (c, d, P, Q) ⇒ P x

⦏Q_closed_⇒_Q_thm⦎ =
	⊢ ∀ c d P Q x⦁ x ∈ Q_closure (c, d, P, Q) ⇒ Q x
=TEX

\subsection{Pseudo-Hereditarily-PQ Collections}

Even if we had a pseudo-well-founded universe in NFU, it would not be pseudo-well-founded-PQ for any interesting or useful properties P and Q.
The whole idea is to use these properties to create a pair of useful subclasses of the universe.
So what we want to do is just take the two closures resulting from P and Q, and use their union as new a psuedo-well-founded domain of discourse.
In fact, we won't take the union at all, we will be looking for a two-sorted foundational theory.

ⓈHOLCONST
│ ⦏PseudoHereditarilyPQ⦎ :
│	(('X → 'X ℙ) × ('X → 'X ℙ) × ('X → BOOL) × ('X → BOOL)) → ('X ℙ × 'X ℙ)
├──────
│ ∀z⦁ PseudoHereditarilyPQ z = (P_closure z, Q_closure z)
■

Among the important properties which we hope this construction will have are:

\begin{itemize}
\item The values in the left collection will all have property P.
\item The values in the right collection will all have property Q.
\item Both collections will include the corresponding {\it HereditarilyPQ} sets.
\end{itemize}

I am by no means confident of any of these features at present.

\ignore{
=SML
val P_closed_def = get_spec ⌜P_closed⌝;
val Q_closed_def = get_spec ⌜Q_closed⌝;
val P_closure_def = get_spec ⌜P_closure⌝;
val Q_closure_def = get_spec ⌜Q_closure⌝;
val PseudoHereditarilyPQ_def = get_spec ⌜PseudoHereditarilyPQ⌝;
=TEX
}%ignore

\section{A RECURSION PRINCIPLE}

An induction principle is often associated with a notion of well-foundedness such that some collection will be well-founded iff the induction principle holds over the collection.
There will then be a recursion theorem which tells us about the existence of functions satisfying recursive equations, to the effect that if the functor which captures the content of the recursion equations respects the well-founded relation then it will have a fixed point which is a solution to the equations.

In this pattern there is usually a clean separation between the well-founded relation and the functor which respects that relation, and to prove the existence of the fixed point using the recursion theorem one must show that the relation is well-founded (which may be done without reference to the functor) and then show that the functor respects the relation (which will not usually depend on its being well-founded).

The idea of a functor respecting some relation captures the idea that in evaluating the recursive function each time a recursion takes place the argument of the function is lower in some well-founded relation than the previous invocation, which guarantees that the recursion must eventually terminate.
The well founded relation therefore must capture the relationship ``in evaluating $f$ at $y$ reference may be made to its value at $x$''.

This relationship being simply a relationship over the domain of the proposed function, it cannot take into account the values of $f$, but a recursive definition of a function clearly can do so.
A function whose evaluation terminates only because its dependencies are sensitive to values of the function may not be provably terminating by these means.

Elsewhere I address the problem of constructing non-well-founded interpretations of set theory by seeking fixed points of recursive definitions of membership over suitable domains.
In some cases these constructions may be connected with problems which have proven very hard to solve, for example the consistency of Quine's NF, so it is reasonable to expect that proving the existence of a fixed point in such a case may depend upon a recursion principle stronger than the usual kind.
This is what I am attempting to fcrmulate.

To formulate the principle some auxiliary notions are helpful.
I need to ba able to talk about a region over which the values of a function are fixed under the operation of a functor.

ⓈHOLCONST
│ ⦏FunEquiv⦎: ('a → 'b) → ('a→ 'b) → 'a SET → BOOL
├──────
│ ∀f g X⦁ FunEquiv f g X ⇔ ∀x⦁ x ∈ X ⇒ g x = f x
■

ⓈHOLCONST
│ ⦏FixedRegion⦎: (('a → 'b) → ('a→ 'b)) → ('a → 'b) → 'a SET → BOOL
├──────
│ ∀G f X⦁ FixedRegion G f X ⇔
│	∀g⦁ (∀x⦁ x ∈ X ⇒ g x = f x) ⇒ (∀x⦁ x ∈ X ⇒ G g x = f x)
■

What I aim to say here is that if a functor satisfies something a bit like and induction principle then it has a fixed point.

=GFT
⦏special_recursion_thm⦎ = 
   ⊢? ∀ G⦁
	(∀P x⦁ (∃v X f⦁ ∀g⦁ (∀y⦁ y ∈ X ⇒ g y = f y)
			⇒ G g x = v ∧ (∀y⦁ y ∈ X ⇒ P y)) ⇒ P x)
			⇒ ∃g⦁ G g = g
=TEX



\ignore{
=IGN
stop;

set_goal ([], ⌜∀ G⦁
	(∀P (x:'a)⦁ (∃v X f⦁ ∀g⦁ (∀y⦁ y ∈ X ⇒ g y = f y) ⇒ G g x = v ∧ (∀y⦁ y ∈ X ⇒ P y)) ⇒ P x)
	⇒ ∃g⦁ G g = g⌝);
a (REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜λx:'a⦁ ∃h Y⦁ FixedRegion G h (Y ∪ {x})⌝);
a (POP_ASM_T (strip_asm_tac o (rewrite_rule[])));
a (lemma_tac ⌜∃g:'a → 'b⦁ ∀x:'a⦁ ∃h Y⦁ FixedRegion G h (Y ∪ {x}) ∧ g x = h x⌝);
a (prove_∃_tac THEN strip_tac);
a (SPEC_NTH_ASM_T 1 ⌜x'⌝ (STRIP_THM_THEN (STRIP_THM_THEN check_asm_tac)));
a (swap_nth_asm_concl_tac 1 THEN prove_∃_tac);

=TEX
}%ignore

\section{CODING CONSTRUCTIONS}

It is proposed in the first instance to use HOL types as ways of describing constructions.

It is also desirable to allow the domains of the constructors to be specified by predicates, especially since some type constructors like the power set will not be implementable without some constraint on the subsets.

\subsection{Constructor Translation Kits}

In order to make the translation of such a description of a system of constructors into a function whose fixedpoint can be taken to yield an implementation, the code will be parameterised by the necessary things to build the function.
For example, for type constructor allowed in the description a function is required to perform the construction of elements of that type over the chosen representation type.
So we need a map (in SML) from HOL type constructors to hol functions containing this information.

The type $CTK$ is defined as a 1-ary type constructor which in its in its primary role instantiated to type $TERM$.
When instantiated to $string$ the type can be used to package a set of aliases for these terms enabling the complex terms constructed for fixed points to be presented concisely in theory listings.
The aliases may be used temporarily just for the theory listing and then easily undeclared so that they do not interfere with parsing.

=SML
type 'a ⦏CTK⦎ = {
	tag : 'a,
	tagc : 'a,
	mk_leaf: 'a,
	node_constructors: 'a list,
	content_extractors: 'a list,
	leaf_injections: 'a list,
	leaf_content: 'a,
	ccp_converter: 'a,
	compound_fixp: 'a};
=TEX

\ignore{
=SML

=IGN
=TEX
}%ignore

\subsection{Lifting Over HOL Type Constructors}

The following functions allow the coding of constructors over a representation type to be written without concern for how the functions will be compounded.
They lift an operator over a representation type to be lifted to a functor which transforms constructors for the operand types into a constructor for the result type.

These lifting functions are specific to the HOL type constructors but independent of the representation type.

ⓈHOLCONST
│ ⦏LiftProduct⦎: ('t × 't → 't) → ('a → 't) → ('b→ 't) → ('a × 'b → 't)
├──────
│ ∀prod f g a b⦁ LiftProduct prod f g (a, b) = prod (f a, g b)
■

ⓈHOLCONST
│ ⦏LiftSum⦎: ('t + 't → 't) → ('a → 't) → ('b→ 't) → ('a + 'b → 't)
├──────
│ ∀sum f g ab⦁ LiftSum sum f g ab = sum ((Fun⋎+ f g) ab)
■

ⓈHOLCONST
│ ⦏LiftList⦎: ('t LIST → 't) → ('a → 't) → ('a LIST → 't)
├──────
│ ∀list f al⦁ LiftList list f al = list (Map f al)
■

ⓈHOLCONST
│ ⦏LiftSumUnion⦎: ('a → 'u SET) → ('b → 'u SET) → ('a + 'b → 'u SET)
├──────
│ ∀cfl cfr ab⦁ LiftSumUnion cfl cfr ab = if IsL ab then cfl (OutL ab) else cfr (OutR ab)
■

ⓈHOLCONST
│ ⦏LiftSumPred⦎: ('a → BOOL) → ('b → BOOL) → ('a + 'b → BOOL)
├──────
│ ∀pl pr ab⦁ LiftSumPred pl pr ab = if IsL ab then pl (OutL ab) else pr (OutR ab)
■

\subsection{Constructors Over Trees}

Definitions of constructors for products and lists, and injections for disjoint unions.

I'm trying to make this a general as possible, the idea is to allow for the construction of inductive datatypes based on arbitrary trees.

Then constructions may are therefore be thought of as parameterised by:

\begin{enumerate}
\item a type of leaf values
\item a type of arc tags
\end{enumerate}

And the tree we construct is a tree whose paths may be as long as the well-ordering and whose nodes and arcs have the appropriate kinds of tags.

A tree is then ``implemented'' as a function from paths to node tags, where a path is itself a function from an initial segment of the domain of the well-ordering into the arc tags.
Both of these kinds of function are partial and are therefore represented as relations.

The fact that we are dealing with sets and partial function is here immaterial to the definition of the constructor function, and can be taken account of later in the process of constructing the inductive datatype, so the parameterisation is evident at this point only by the presence of three type variables.

I can't see how to make use of a well-ordering larger than the natural numbers so that's fixed, and that makes a path into a list of arcs.

\subsubsection{Some Types, Some Properties}

To make the type information in the theory listing less cluttered I will use some labelled product definitions to introduce types.

ⓈHOLLABPROD ⦏TREEE⦎─────
│ ⦏Treee⦎: 'arc LIST → 'leaf → BOOL
■──────────────

One could make a proper subtype here by incorporating the necessary conditions on the relations involved, but in the construction of an inductive datatype there will almost invariably be another subtyping involved and one will probably suffice.
However, it may be helpful at this point to define the conditions for a ``TREEE'' to be a tree.
The conditions depend upon chosing a well-ordering of the index types, and are therefore parameterised by such a well-ordering.
There may not be to allow for this to be a well-ordering of a subset of the type, but since the definition of well-ordering we have is defined in such terms (i.e. as a property of set/relation pairs) we will define the well-formedness condition as accepting such a well-ordering.

ⓈHOLCONST
│ ⦏Domain⦎ : ('a → 'b → BOOL) → 'a SET
├
│ ∀r⦁ Domain r = {x | ∃y⦁ r x y}
■

ⓈHOLCONST
│ ⦏NullTreee⦎ : ('arc, 'leaf)TREEE
├
│ NullTreee = MkTREEE(λal n⦁ F)
■

ⓈHOLCONST
│ ⦏IsTreee⦎ : ('arc, 'leaf)TREEE → BOOL
├
│ ∀ t:('arc, 'leaf)TREEE⦁
│	IsTreee t ⇔
│	¬ t = NullTreee
│	∧ ManyOne (Treee t)
│	∧ (∀p q⦁ p ∈ Domain (Treee t) ⇒ ¬ Append p q ∈ Domain (Treee t))
■

\subsubsection{A Generic Constructor}

We have a single constructor function which takes a 'arc indexed set of trees and a 'leaf value.
This constructs a new tree from whose root node has the supplied value and whose children are the supplied trees, placed on the arc names used to index them.

The paths through the tree are therefore the paths of the original trees with a new arc slotted in at the head of each path.

ⓈHOLCONST
│ ⦏MkTreee⦎ : ('arc → ('arc, 'leaf)TREEE → BOOL) → ('arc, 'leaf)TREEE
├
│ ∀c⦁ MkTreee c = MkTREEE (λ path leaf⦁
│	∃ tr⦁ c (Hd path) tr ∧ Treee tr (Tail path) leaf)
■

Though this was written for use in inductive datatypes, I don't know a reason why it could not be used for co-inductive datatypes.
Presumably you have the same kind of definition but take the maximal rather than the minimal fixed point.

This construction is only one-one subject to some constraints on the supplied map, as follows:

ⓈHOLCONST
│ ⦏NiceChildren⦎ : ('arc → ('arc, 'leaf)TREEE → BOOL) → BOOL
├
│ ∀c⦁ NiceChildren c ⇔ ManyOne c ∧ ¬ ∃a⦁ c a NullTreee
■

\ignore{
=SML
val Treee_def = get_spec ⌜Treee⌝;
val MkTreee_def = get_spec ⌜MkTreee⌝;
val NullTreee_def = get_spec ⌜NullTreee⌝;
val ManyOne_def = get_spec ⌜ManyOne⌝;
val NiceChildren_def = get_spec ⌜NiceChildren⌝;

set_goal([], ⌜∃DestTreee : ('arc, 'leaf)TREEE → ('arc → ('arc, 'leaf)TREEE → BOOL) ⦁
	∀c⦁ NiceChildren c ⇒ DestTreee (MkTreee c) = c⌝);
a (∃_tac ⌜λt:('arc, 'leaf)TREEE⦁
		let tr = Treee t
		in  (λa:'arc; tr2⦁ Treee tr2 = (λal:'arc LIST; n:'leaf⦁ tr (Cons a al) n)
			∧ ¬ tr2 = NullTreee)
		   ⌝ THEN rewrite_tac [let_def, Treee_def, MkTreee_def]
	THEN REPEAT strip_tac);
a (rewrite_tac [ext_thm] THEN REPEAT ∀_tac);	
a (cases_tac ⌜c x x'⌝
	THEN TRY (asm_rewrite_tac[])
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜x'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac [NiceChildren_def]);
a (all_fc_tac [ManyOne_def]);
a (POP_ASM_T discard_tac THEN asm_rewrite_tac []);
(* *** Goal "3" *** *)
a (all_fc_tac [NiceChildren_def]);
a (swap_nth_asm_concl_tac 1 THEN strip_tac);
a (∃_tac ⌜x⌝
	THEN POP_ASM_T (rewrite_thm_tac o eq_sym_rule)
	THEN strip_tac);
(* *** Goal "4" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac [NullTreee_def]);
a (LEMMA_T ⌜x' = MkTREEE (λ al n⦁ F) ⇔ Treee x' = (λ al n⦁ F)⌝
	rewrite_thm_tac);
(* *** Goal "4.1" *** *)
a (REPEAT strip_tac THEN TRY (asm_rewrite_tac [Treee_def]));
a (SYM_ASMS_T rewrite_tac);
a (rewrite_tac[Treee_def]);
(* *** Goal "4.2" *** *)
a (rewrite_tac [ext_thm] THEN REPEAT strip_tac);	
a (swap_nth_asm_concl_tac 2);
a (spec_nth_asm_tac 1 ⌜x''⌝);
a (spec_nth_asm_tac 1 ⌜x'''⌝);
(* *** Goal "4.2.1" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "4.2.2" *** *)
a (lemma_tac ⌜∀ x'' x'''⦁ (∃ tr⦁ c x tr ∧ Treee tr x'' x''') ⇔ Treee tr x'' x'''⌝
	THEN REPEAT strip_tac THEN TRY (asm_rewrite_tac[]));
(* *** Goal "4.2.2.1" *** *)
a (all_fc_tac [NiceChildren_def]);
a (all_fc_tac [ManyOne_def]);
a (all_var_elim_asm_tac);
(* *** Goal "4.2.2.2" *** *)
a (∃_tac ⌜tr⌝ THEN asm_rewrite_tac[]);
(* *** Goal "4.2.2.3" *** *)
a (rename_tac []);
a (DROP_NTH_ASM_T 5 ante_tac);
a (DROP_NTH_ASM_T 1 rewrite_thm_tac
	THEN strip_tac);
a (lemma_tac ⌜Treee x' = Treee tr⌝
	THEN1 (rewrite_tac [ext_thm]
		THEN REPEAT ∀_tac
		THEN (POP_ASM_T rewrite_thm_tac)));
a (LEMMA_T ⌜MkTREEE (Treee x') = MkTREEE (Treee tr)⌝ ante_tac
	THEN1 (asm_rewrite_tac []));
a (rewrite_tac [Treee_def] THEN strip_tac THEN asm_rewrite_tac[]);
val _ = save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏DestTreee⦎ : ('arc, 'leaf)TREEE → ('arc → ('arc, 'leaf)TREEE → BOOL) 
├
│ ∀c⦁ NiceChildren c ⇒ DestTreee (MkTreee c) = c
■

\subsubsection{Specific Constructors}

The idea here is to code up the details of how to construct appropriate data for MkTreee for the commonly expected type constructors in an inductive datatype definition.

ⓈHOLCONST
│ ⦏MkLeafTreee⦎ : 'leaf → ('arc, 'leaf)TREEE
├
│ ∀l⦁ MkLeafTreee l = MkTREEE (λarc leaf⦁ arc = [] ∧ leaf = l)
■

ⓈHOLCONST
⦏MkProdTreee⦎ : (BOOL → 'arc) → (('arc, 'leaf)TREEE) × (('arc, 'leaf)TREEE)
│ 		→ ('arc, 'leaf)TREEE
├
│ ∀ai l r⦁
│ 	MkProdTreee ai (l, r) = MkTreee 
│ 	(λarc tree⦁ arc = (ai T) ∧ tree = l
│ 		∨ arc = (ai F) ∧ tree = r)
■

ⓈHOLCONST
│ ⦏MkSumTreee⦎ : (BOOL → 'arc)
│ 		→ (('arc, 'leaf)TREEE) + (('arc, 'leaf)TREEE)
│ 		→ ('arc, 'leaf)TREEE
├
│ ∀ai t⦁
│ 	MkSumTreee ai t = MkTreee 
│ 	(λarc tree⦁ if IsL t then arc = (ai T) ∧ tree = OutL t
│ 		else arc = (ai F) ∧ tree = OutR t)
■

ⓈHOLCONST
│ ⦏MkArcTreee⦎ : 'arc → ('arc, 'leaf)TREEE → ('arc, 'leaf)TREEE
├
│ ∀a t⦁
│ 	MkArcTreee a t = MkTreee (λarc tree⦁ arc = a ∧ tree = t)
■

ⓈHOLCONST
│ ⦏MkTagTreee⦎ : (ℕ → 'arc) → ℕ → ('arc, 'leaf)TREEE → ('arc, 'leaf)TREEE
├
│ ∀ai n t⦁
│ 	MkTagTreee ai n t = MkArcTreee (ai n) t
■

ⓈHOLCONST
│ ⦏IsTagTreee⦎ : (ℕ → 'arc) → ℕ → ('arc, 'leaf)TREEE → BOOL
├
│ 	∀ai n t⦁ IsTagTreee ai n t ⇔ ∃t2⦁ t = MkTagTreee ai n t2 
■

ⓈHOLCONST
│ ⦏UnTagTreee⦎ : ('arc, 'leaf)TREEE → ('arc, 'leaf)TREEE
├
│ 	∀t⦁ ∃ t2 a⦁ t = MkArcTreee a t2 ⇒ UnTagTreee t = t2
■

ⓈHOLCONST
│ ⦏MkListTreee⦎ : (ℕ → 'arc) → ('arc, 'leaf)TREEE LIST → ('arc, 'leaf)TREEE
├
│ ∀ai trl⦁
│ 	MkListTreee ai trl = MkTreee
│ 	(λarc tree⦁ ∃n⦁ arc = (ai n) ∧ (n, tree) ∈ ListRel trl)
■

Node injections will be dynamically constructed.

Arc injections are fixed in any particular implementation of these inductive datatypes, determined by the range of type constructors to be supported.
The arc type has to have a cardinality which is an upper bound of the cardinalities of those required by the type constructors.
So, for the above set of constructors $ℕ$ suffices and the arc injectors are therefore defined as follows:

ⓈHOLCONST
│ ⦏AiOneToN⦎ : ONE → ℕ;  AiBoolToN : BOOL → ℕ; AiNToN : ℕ → ℕ
├
│ 	(∀one⦁ AiOneToN one = 0)
│ ∧	(∀b⦁ AiBoolToN b = if b then 1 else 0)
│ ∧	(∀n⦁ AiNToN n = n)
■

\subsection{An ℕ Tree Constructor Translator Kit}

In order to make the definitions of types no more prolix than need be it is desirable not to use expressions in making up constructor toolkits.
So we here define constants for making a default toolkit based on trees with natural number arcs.

\subsubsection{Special Constructors}

The following definition instantiates the tree constructors to the injections into $ℕ$ and lifts them to give the functions required for a $CTK$.

ⓈHOLCONST
│ ⦏NTreeeTag⦎: ℕ → ('a  → (ℕ, 'leaf)TREEE) → ('a  → (ℕ, 'leaf)TREEE)
├──────
│ 	∀n f⦁ NTreeeTag n f = (MkTagTreee AiNToN n) o f
■

ⓈHOLCONST
│ ⦏NTreeeIsTag⦎: ℕ → (ℕ, 'leaf)TREEE → BOOL
├──────
│ 	NTreeeIsTag = IsTagTreee AiNToN
■

\subsubsection{Node Constructors}

ⓈHOLCONST
│ ⦏NTreeeMkList⦎: ('a → (ℕ, 'leaf)TREEE) → ('a LIST → (ℕ, 'leaf)TREEE)
├──────
│ 	 NTreeeMkList = LiftList (MkListTreee AiNToN)
■

ⓈHOLCONST
│ ⦏NTreeeMkProd⦎: ('a → (ℕ, 'leaf)TREEE) → ('b → (ℕ, 'leaf)TREEE)
│	 → ('a × 'b → (ℕ, 'leaf)TREEE);
│ ⦏NTreeeMkSum⦎: ('a → (ℕ, 'leaf)TREEE) → ('b → (ℕ, 'leaf)TREEE)
│	 → ('a + 'b → (ℕ, 'leaf)TREEE)
├──────
│ 	NTreeeMkProd = LiftProduct (MkProdTreee AiBoolToN)
│ ∧	NTreeeMkSum = LiftSum (MkSumTreee AiBoolToN)
■

\subsubsection{Content Extractors}

ⓈHOLCONST
│ ⦏NTrListC⦎: ('a → (ℕ, 'leaf)TREEE SET) → ('a LIST → (ℕ, 'leaf)TREEE SET)
├──────
│ 	 NTrListC = LiftList (λsl⦁ ⋃ {x | x ∈⋎L sl})
■

ⓈHOLCONST
│ ⦏NTrProdC⦎: ('a → (ℕ, 'leaf)TREEE SET) → ('b → (ℕ, 'leaf)TREEE SET)
│	 → ('a × 'b → (ℕ, 'leaf)TREEE SET);
│ ⦏NTrSumC⦎: ('a → (ℕ, 'leaf)TREEE SET) → ('b → (ℕ, 'leaf)TREEE SET)
│	 → ('a + 'b → (ℕ, 'leaf)TREEE SET)
├──────
│ 	NTrProdC = LiftProduct (Uncurry $∪)
│ ∧	NTrSumC = LiftSum (λx⦁ if IsL x then OutL x else OutR x)
■

ⓈHOLCONST
│ ⦏NTrLeafC⦎: ('a → (ℕ, 'leaf)TREEE SET)
├──────
│ 	 ∀l⦁ NTrLeafC l = {}
■

This function tags content as required by content extractors on type variables for the new types.
It also makes a unit set of the result.

ⓈHOLCONST
│ ⦏NTreeeTagC⦎: ℕ → (ℕ, 'leaf)TREEE → (ℕ, 'leaf)TREEE SET
├──────
│ 	∀n t⦁ NTreeeTagC n t = {MkTagTreee AiNToN n t}
■

\subsubsection{Ntree Ctk}

The following definition gives the required ccp to relation conversion:

ⓈHOLCONST
│ ⦏CR⦎: ('b → 'a) → ('b → 'a SET) → ('b → BOOL) → ('a → 'a → BOOL)
├──────
│ 	∀tor tent pred⦁ CR tor tent pred = CCP2Rel (MkCCP tor tent pred)
■

This definition provides the compounder which combines the relations for all the constructors and takes the fixed point.

ⓈHOLCONST
│ ⦏FR⦎: ((ℕ, 'a) TREEE → (ℕ, 'a) TREEE → BOOL) LIST LIST → (ℕ, 'a) TREEE SET
├──────
│ 	∀rll⦁ FR rll = HeredRel (CompoundRels (MkTagTreee AiNToN) rll)
■

=SML
val ⦏ntree_ctk⦎:TERM CTK = {
	tag = ⌜NTreeeTag⌝,
	tagc = ⌜NTreeeTagC⌝,
	mk_leaf = ⌜MkLeafTreee⌝,
	node_constructors = [⌜NTreeeMkProd⌝, ⌜NTreeeMkSum⌝, ⌜NTreeeMkList⌝],
	leaf_injections = [⌜MkLeafTreee:CHAR→(ℕ, CHAR)TREEE⌝],
	content_extractors = [⌜NTrProdC⌝, ⌜NTrSumC⌝, ⌜NTrListC⌝],
	leaf_content = ⌜NTrLeafC⌝,
	ccp_converter = ⌜CR⌝,
	compound_fixp = ⌜FR⌝
};
val ctk_aliases:string CTK ={
	tag = "υ",
	tagc = "ω",
	mk_leaf = "γ",
	node_constructors = ["×", "+", "φ"],
	leaf_injections = ["ρ"],
	content_extractors = ["×", "+", "φ"],
	leaf_content = "ρ",
	ccp_converter = "Ξ",
	compound_fixp = "Θ"
};

fun declare_ctk_aliases (ctk: TERM CTK) (sctk:string CTK) =
 let
	fun map_declare_alias (sl, tl) = map declare_alias (combine sl tl);
	val _ = declare_alias (#tag sctk, #tag ctk);
	val _ = declare_alias (#tagc sctk, #tagc ctk);
	val _ = declare_alias (#mk_leaf sctk, #mk_leaf ctk);
	val _ = map_declare_alias (#node_constructors sctk, #node_constructors ctk);
	val _ = map_declare_alias (#leaf_injections sctk, #leaf_injections ctk);
	val _ = map_declare_alias (#content_extractors sctk, #content_extractors ctk);
	val _ = declare_alias (#leaf_content sctk, #leaf_content ctk);
	val _ = declare_alias (#ccp_converter sctk, #ccp_converter ctk);
	val _ = declare_alias (#compound_fixp sctk, #compound_fixp ctk)
	in ()
	end;

fun undeclare_ctk_aliases (ctk: TERM CTK) (sctk:string CTK) =
 let
	fun map_undeclare_alias (sl, tl) = map undeclare_alias (combine sl tl);
	val _ = undeclare_alias (#tag sctk, #tag ctk);
	val _ = undeclare_alias (#tagc sctk, #tagc ctk);
	val _ = undeclare_alias (#mk_leaf sctk, #mk_leaf ctk);
	val _ = map_undeclare_alias (#node_constructors sctk, #node_constructors ctk);
	val _ = map_undeclare_alias (#leaf_injections sctk, #leaf_injections ctk);
	val _ = map_undeclare_alias (#content_extractors sctk, #content_extractors ctk);
	val _ = undeclare_alias (#leaf_content sctk, #leaf_content ctk);
	val _ = undeclare_alias (#ccp_converter sctk, #ccp_converter ctk);
	val _ = undeclare_alias (#compound_fixp sctk, #compound_fixp ctk)
	in ()
	end;

=TEX

\ignore{

\subsection{Coding into Membership Structures}

We provide here a method of coding inductely defined sets into membership structures.
This supports coding in the following three ways:

\begin{enumerate}
\item into a membership structure of choice and a ordered pair construction over that structure
\item into the natural numbers, given a suitable relation over the natural numbers
\item into the finite Von Neuman ordinals in a membership structure
\end{enumerate}

In relation to the first method, the Sierpinski and Quine ordered pair construction are provided.
In relation to the second, a method of encoding the hereditarily finite sets into natural numbers is provided.

One way to approach this would be to provide metalanguage facilities parameterized by membership structures with ordered pair constructors for preparing contructor translation kits giving fixed points which are in the membership structure.

There are two disadvantages to this.

The first small disadvantage is that either the facility would have to perform definitions for the constants in each CTK it produces, causing a proliferation of new constant definitions, or else expressions would have to be used, which would exacerbate the complexity of the terms involved.

The second disdvantage is that such a facility would not permit reasoning in general about what can be coded in membership structures.

To permit proof (for example) of a generalised negative definability result obtained via construction of a liar sentence, it is desirable that the parameterisation by membership structure should take place in the object rather than the metalangage.

We will therefore be defining a CTK in which the representation type is the domain of a membership structure which is expected (together with an ordered pair constructor) as an argument by the constructors in the CTK, which delivers not simply a fixed point, but a function from such a structure to a fixed point.

We might as well treat the necessary injection from the natural numbers into the membership structure in the same way as the pairing constructor.


 ⓈHOLCONST
│ ⦏SierpinskiPair⦎ ('a SET × ('a → 'a → BOOL)) → 'a × 'a → 'a
 ├──────
│ ∀ (S, $∈⋎m) (x,y) = 
 ■


 ⓈHOLCONST
│ ⦏MSUPair⦎ ('a SET × ('a → 'a → BOOL)) → 'a × 'a → 'a
 ├──────
│ ∀ (S, $∈⋎m) (x,y)⦁ MSUPair (S, $∈⋎m) (x,y) = 
 ■

\subsection{Constructing a Fixed Point}

The following function takes a HOL type and a list of constructors and computes a compound constructor.
The HOL type should have a sum of any finite number of distinct type variables as its codomain
The constructors should include one for each type constructor which is involved in the recursion.

=SML
fun match_mk_cons (t, u) = list_match_mk_app (⌜Cons⌝, (t::u::[]));
fun list_match_mk_cons l = foldr match_mk_cons ⌜Nil⌝ l;
=IGN
fun match_mk_sum (t, u) = list_match_mk_app (⌜FunSum⌝, (t::u::[]));
fun list_match_mk_sum (h::tl) = lfoldr match_mk_sum h tl;

fun match_mk_sum_union (t, u) = list_match_mk_app (⌜LiftSumUnion⌝, (t::u::[]));
fun list_match_mk_sum_union (h::tl) = lfoldr match_mk_sum_union h tl;

fun match_mk_sum_pred (t, u) = list_match_mk_app (⌜LiftSumPred⌝, (t::u::[]));
fun list_match_mk_sum_pred (h::tl) = lfoldr match_mk_sum_pred h tl;

fun tc_of_constructor c = (fst o dest_ctype o last o front) ((strip_→_type o type_of) c);
=SML
fun node_constructor_pair c = ((fst o dest_ctype o last o front) ((strip_→_type o type_of) c), c);

fun leaf_injection_pair li = ((fst o dest_ctype o fst o dest_→_type o type_of) li, li);

val node_extractor_pair = node_constructor_pair;

fun leaf_extractor_pair t li = ((fst o dest_ctype o fst o dest_→_type o type_of) li, t);

local
 fun aux1 (a,b) =
	let val (n,t) = dest_var a
	    val (tt::tl) = right_rotate_list (strip_→_type t)
	in (n, length tl, list_mk_×_type tl, tt, b) end;
 fun aux2 (_,_,_,d,_) = [dest_vartype d]
in
 fun sigproc sig1 =
  let    val sig2 = map aux1 sig1;
	val new_types = list_cup (map aux2 sig2)
	val sig3 = map (fn x => filter (fn (_,_,_,y,_) => x = dest_vartype y) sig2) new_types;
  in (new_types, sig3)
  end
end;

fun translate_mapper (ctk:TERM CTK) =
 let val cd = list_to_sdict (
		  (map node_constructor_pair (#node_constructors ctk))
		@ (map leaf_injection_pair (#leaf_injections ctk)))
 in (fn tcn =>
	let val Value x = s_lookup tcn cd
	in fn tl => list_match_mk_app (x, tl)
	end)
 end;

fun extract_mapper (ctk:TERM CTK) =
 let val cd = list_to_sdict (
		  (map node_extractor_pair (#content_extractors ctk))
		@ (map (leaf_extractor_pair (#leaf_content ctk)) (#leaf_injections ctk)))
 in (fn tcn =>
	let val Value x = s_lookup tcn cd
	in fn tl => list_match_mk_app (x, tl)
	end)
 end;

val constructor_types = [
	(⌜MkVarType: STRING → 'TYPE⌝,
				⌜λx:STRING⦁ Hd x = '''⌝),
	(⌜MkCType: STRING → 'TYPE LIST →'TYPE⌝,
				⌜λ(x:STRING, y:'TYPE LIST)⦁ ¬ Hd x = '''⌝),
	(⌜MkVarTerm: STRING → 'TYPE →'TERM⌝,
				⌜λ(x:STRING, y:'TYPE)⦁ Hd x = '''⌝),
	(⌜MkCTerm: STRING → 'TYPE →'TERM⌝,
				⌜λ(x:STRING, y:'TYPE)⦁ ¬ Hd x = '''⌝),
	(⌜MkLamTerm: STRING → 'TYPE → 'TERM → 'TERM⌝,
				⌜λ(x:STRING, y:'TYPE, z:'TERM)⦁ Hd x = '''⌝),
	(⌜MkAppTerm: 'TERM → 'TERM → 'TERM⌝,
				⌜λ(x:'TERM, y:'TERM)⦁ T⌝)
];

fun translate_sig ctk sign =
 let
	val psig = sigproc sign;
	val newtyvars = fst psig;
	fun tagnum tv = (mk_ℕ o integer_of_int) (list_pos tv newtyvars);
	val cf = translate_mapper ctk;
	val tag = #tag  ctk;
	val tagc = #tagc ctk;
	fun id_vf x = ⌜I⌝;
     	fun aux (_,_,ty1,_,_) = gen_type_map cf id_vf ty1;
	fun tvcon_vf tv = match_mk_app (tagc, tagnum tv);
	val xf = extract_mapper ctk;
     	fun aux2 (_,_,ty1,_,_) = gen_type_map xf tvcon_vf ty1;
	val dtll = map (map (fn x as (a,b,c,d,e) =>
		list_match_mk_app (#ccp_converter ctk, [aux x, aux2 x, e]))) (snd psig)
	val tll = list_match_mk_cons (map list_match_mk_cons dtll)
 in      match_mk_app (#compound_fixp ctk, tll)
 end;

set_flag ("subgoal_package_quiet", false);
=IGN
set_flag ("pp_use_alias", true);
declare_ctk_aliases ntree_ctk ctk_aliases;
translate_sig ntree_ctk constructor_types;
=TEX

}%ignore

\section{MAKING NEW TYPES}

The last stage in this process takes place where the objective is to introduce new types and constructors over the new types.
The preceding material enables the description of a system of constructors to be translated into a realisation of that system over various sets.

This final stage involves the creation of a new type (possibly a type constructor) for each of the distinct sets which are the co-domains of the constructors, the definition of operators over these types corresponding to the constructors, and the transfer of the properties of the sets to theorems over the types.

These facilities will I hope be orthogonal to most aspects of variation in the definition of the underlying sets.
It is most strongly motivated by the recursive datatypes of computer science, where there is a desire to abstract away from the details of how the constructions are coded, and may not be required in metatheoretic applications.
An example of the latter applications is where the system of constructors is providing a coding of syntax into some domain of interest (as in Goedel numbering).
However, in other metatheoretic studies, where the details of the construction are important and specific to the application, e.g. in the definition of mutually dependent hereditarily pure concrete functors and  categories, it may be desired at the end to abstract away from the constructions and have separate new types for functors and categories.


\section{Proof Contexts}

=SML
commit_pc "'fixp";

force_new_pc "⦏fixp⦎";
merge_pcs ["rbjmisc", "'fixp"] "fixp";
commit_pc "fixp";

force_new_pc "⦏fixp1⦎";
merge_pcs ["rbjmisc1", "'fixp"] "fixp1";
commit_pc "fixp1";
=TEX

\appendix

{\let\Section\section
\def\section#1{\Section{#1}\label{TheoryListing}}
\include{fixp.th}
}  %\let

\twocolumn[\section{INDEX}\label{INDEX}]
{\small\printindex}

\end{document}
=SML
val aliasflag = set_flag ("pp_use_alias", true);
declare_ctk_aliases ntree_ctk ctk_aliases;
output_theory{out_file="fixp.th.doc", theory="fixp"};
undeclare_ctk_aliases ntree_ctk ctk_aliases;
set_flag ("pp_use_alias", aliasflag);
=TEX
