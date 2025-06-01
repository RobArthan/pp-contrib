=IGN
$Id: t021.doc,v 1.16 2012/08/11 21:01:53 rbj Exp $
open_theory "ICsyn";
set_merge_pcs ["hol1", "'GS1", "'ICsyn"];
open_theory "ICsem";
set_merge_pcs ["hol", "'GS1", "'ICsyn", "'ICsem"];
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\usepackage{A4}

%\def\ExpName{\mbox{{\sf exp}
%\def\Exp#1{\ExpName(#1)}

\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{Set Theory as Consistent Infinitary Comprehension}
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
This paper is concerned with set theory conceived as a maximal consistent theory of set comprehension.
This is interpreted by looking for large subdomains of a notation for infinitary comprehension, and the theory is developed from such interpretations.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created: 2006/11/29

Last Change $ $Date: 2012/08/11 21:01:53 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t021.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t021.pdf}

$ $Id: t021.doc,v 1.16 2012/08/11 21:01:53 rbj Exp $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize

\end{centering}

\thispagestyle{empty}
\end{titlepage}
\newpage
\addtocounter{page}{1}
%\section{DOCUMENT CONTROL}
%\subsection{Contents list}
{\parskip=0pt\tableofcontents}
%\newpage
%\subsection{Document cross references}

\subsection*{To Do}
\begin{itemize}
\item 
\item 
\end{itemize}

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\newpage
\section{INTRODUCTION}

The idea is to come up with a set theory whose subject matter combines the well-founded sets of the cumulative heirarchy with a similarly rich non-well-founded ontology.

The well-founded ontology is based on a simple ontological principle embodied in the following informal definition (transfinite, inductive) of ``well-founded set'':
{\quote a well-founded set is any definite collection of well-founded sets}

Analysis and futher explication of this definition is worthwhile, but is not our present purpose, for which we will assume that the above description suffices and proceed to the non-well-founded sets.

There are different conceptions of well-founded-set from which we may chose, and I do not know of any single all encompassing conception.
Probably the single most prominent conception comes from the idea of set comprehension, viz. that to some useful subset of the properties of sets there correspond sets which are the extensions of the properties.
In the beginnings, Frege allowed unrestrained comprehension, which resulted in inconsistency.
A variety of set theories may then be regarded as limitations on the ideal of unrestrained comprehension sufficient to avoid incoherence.
One of these yields the well-founded sets (or some of them).

If the incoherence of unrestricted comprehension could be located in specific properties then sets correponding to their extension could be omitted from the the domain of discourse and a maximal consistent theory of set comprehension might result.
There is however no obvious way to do this.
The properties are themselves all equally coherent, it is only when we attempt to realise an ontology of sets whose extensions correpond to the properties that we run into trouble, and when this happens it is not so easy to say which properties are at fault.
Nevertheless, this is what we are going to attempt here.

There is another problem which must be mentioned here.
When we seek a full theory of comprehension, we are looking for a set theory in which the set properties of sets is the same as the set of sets itself.
There is a problem of cardinality here, which forces us to limit our selection of properties.
This problem we address by taking, instead of the notion of property in general, the notion of definable property or rule will be used.
The number of such definable properties depends upon the language in which the definition takes place, and we arrange for the cardinality of the syntax of this language to be the same as the cardinality of the domain of our set theory (which will also be the cardinality of the well-founded part of the domain).
This effect can be achieved by coding up the properties in an infinitary language whose syntax is made from well-founded sets.
The language will have sufficent syntax for every well-founded set to correspond to a definable property as well as the non-well-founded sets, and we therefore by means of this infinitary syntax assimilate both non well-founded and well-founded sets, but also the notion of set as graph an set as rule.

The plan is:

\begin{itemize}

\item Define using the ontology of a well-founded set theory (GS) a notation for infinitary comprehension (this will be a transfinite inductive definition of a way of coding up set comprehension in an infinitary language for set theory).

\item Give a semantics to this notation as a functor which transforms pairs of partial equality and membership relations over closed comprehensions.

\item Find maximal subsets of the class of closed comprehensions over which the functor has a fixed point, and consider the theory which arises when these subsets with the fixedpoint semantics are taken as interpretations of set theory.

\end{itemize}

\newpage

=SML
open_theory "GS";
force_new_theory "⦏ICsyn⦎";
new_parent "U_orders";
force_new_pc "⦏'ICsyn⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'ICsyn";
set_merge_pcs ["hol1", "'GS1", "'ICsyn"];
=TEX

\section{MISCELLANEA}

I am at present using a set theory based on an old version of the theory of well-foundedness and well-founded recursion.

Some definitions are supplied here which patch over the differences between the new and old treatments of well-foundedness.

\subsection{Some Synonyms}

=GFT
⦏tc_TranClsr_thm⦎ =
	⊢ ∀ r⦁ (Universe, tc r) = TranClsr (Universe, r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ (Universe, tc r) = TranClsr (Universe, r)⌝);
a (rewrite_tac (map get_spec [
	⌜tc⌝,
	⌜TranClsr⌝,
	⌜trans⌝,
	⌜Trans⌝]));
val tc_TranClsr_thm = save_pop_thm "tc_TranClsr_thm";
=TEX
}%ignore

\section{SYNTAX}

\subsection{Informal Abstract Syntax}
Here is an abstract syntax:

=GFT
term    ::= ordinal
	 | SetComp formula

formula ::= term = term
          | term ∈ term
          | tf ordinal (ℙ formula)
=TEX

Note that the use of the powerset constructor on the right disqualifies this from being a normal recursive datatype.
The apparent incoherence of having an equation with the powerset of the lhs occuring in the rhs is resolved by the powerset in question not being a HOL powerset, but a set of sets in a full blooded set theory.
The definition defines two classes which are not sets, and because they are classes they have the same size as the class of their subsets and the cardinality problem goes away.
A definition of this kind can be formalised as what Isabelle calls an inductive set definition bearing in mind here that the sets in question are HOL subsets of a type which is a class of sets.
i.e. it is really an inductive class definition.

The ordinals here are used as variables, and Von Neumann ordinals are required.
They are in fact used like De Bruijn indices, so comprehension always binds the variable zero at the outermost level, and binds a higher numbered variable in inner scopes.
A single constructor is provided for truth functional expressions and is to be understood as the negation of the universal quantification of the conjunction of a set (of any cardinality) of formulae.
This quantified simultaneously quantifies over any number of variables.

\subsection{Constructors, Discriminators and Destructors}

Preliminary to presenting the inductive definition of the required classes we define the nuts and bolts operations on the required syntactic entities (some of which will be used in the inductive definition).

A constructor puts together some syntactic entity from its constituents, discriminators distinguist between the different kinds of entity and destructors take them apart.

ⓈHOLCONST
│ ⦏MkVar⦎ : GS → GS
├───────────
│    ∀v⦁ MkVar v = (Nat⋎g 0) ↦⋎g v
■

ⓈHOLCONST
│ ⦏IsVar⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsVar t = fst t = (Nat⋎g 0)
■

ⓈHOLCONST
│ ⦏VarNum⦎ : GS → GS
├───────────
│    VarNum = snd
■

ⓈHOLCONST
│ ⦏MkComp⦎ : GS → GS
├───────────
│    ∀f⦁ MkComp f = (Nat⋎g 1) ↦⋎g f
■

ⓈHOLCONST
│ ⦏IsComp⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsComp t = fst t = (Nat⋎g 1)
■

ⓈHOLCONST
│ ⦏CompBody⦎ : GS → GS
├───────────
│    CompBody = snd
■

ⓈHOLCONST
│ ⦏MkEq⦎ : GS × GS → GS
├───────────
│ ∀lr⦁ MkEq lr = (Nat⋎g 2) ↦⋎g ((Fst lr) ↦⋎g (Snd lr))
■

ⓈHOLCONST
│ ⦏IsEq⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsEq t = fst t = (Nat⋎g 2)
■

ⓈHOLCONST
│ ⦏MkMem⦎ : GS × GS → GS
├───────────
│ ∀ lr⦁  MkMem lr = (Nat⋎g 3) ↦⋎g ((Fst lr) ↦⋎g (Snd lr))
■

ⓈHOLCONST
│ ⦏IsMem⦎ : GS → BOOL
├───────────
│ ∀t⦁ IsMem t = fst t = (Nat⋎g 3)
■

ⓈHOLCONST
│ ⦏AtomLhs⦎ : GS → GS
├───────────
│  AtomLhs = λx⦁ fst(snd x)
■

ⓈHOLCONST
│ ⦏AtomRhs⦎ : GS → GS
├───────────
│  AtomRhs = λx⦁ snd(snd x)
■

ⓈHOLCONST
│ ⦏MkTf⦎ : GS × GS → GS
├───────────
│ ∀vc⦁ MkTf vc = (Nat⋎g 4) ↦⋎g ((Fst vc) ↦⋎g (Snd vc))
■

ⓈHOLCONST
│ ⦏IsTf⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsTf t = fst t = (Nat⋎g 4)
■

ⓈHOLCONST
│ ⦏TfVars⦎ : GS → GS
├───────────
│  TfVars = λx⦁ fst(snd x)
■

ⓈHOLCONST
│ ⦏TfForms⦎ : GS → GS
├───────────
│  TfForms = λx⦁ snd(snd x)
■

=GFT
⦏Is_clauses⦎ =
   ⊢ ((∀ v⦁ IsVar (MkVar v))
         ∧ (∀ f⦁ ¬ IsVar (MkComp f))
         ∧ (∀ lr⦁ ¬ IsVar (MkEq lr))
         ∧ (∀ lr⦁ ¬ IsVar (MkMem lr))
         ∧ (∀ vc⦁ ¬ IsVar (MkTf vc)))
       ∧ ((∀ v⦁ ¬ IsComp (MkVar v))
         ∧ (∀ f⦁ IsComp (MkComp f))
         ∧ (∀ lr⦁ ¬ IsComp (MkEq lr))
         ∧ (∀ lr⦁ ¬ IsComp (MkMem lr))
         ∧ (∀ vc⦁ ¬ IsComp (MkTf vc)))
       ∧ ((∀ v⦁ ¬ IsEq (MkVar v))
         ∧ (∀ f⦁ ¬ IsEq (MkComp f))
         ∧ (∀ lr⦁ IsEq (MkEq lr))
         ∧ (∀ lr⦁ ¬ IsEq (MkMem lr))
         ∧ (∀ vc⦁ ¬ IsEq (MkTf vc)))
       ∧ ((∀ v⦁ ¬ IsMem (MkVar v))
         ∧ (∀ f⦁ ¬ IsMem (MkComp f))
         ∧ (∀ lr⦁ ¬ IsMem (MkEq lr))
         ∧ (∀ lr⦁ IsMem (MkMem lr))
         ∧ (∀ vc⦁ ¬ IsMem (MkTf vc)))
       ∧ (∀ v⦁ ¬ IsTf (MkVar v))
       ∧ (∀ f⦁ ¬ IsTf (MkComp f))
       ∧ (∀ lr⦁ ¬ IsTf (MkEq lr))
       ∧ (∀ lr⦁ ¬ IsTf (MkMem lr))
       ∧ (∀ vc⦁ IsTf (MkTf vc))

⦏Is_not_fc_clauses⦎ =
   ⊢ (∀ x⦁ IsVar x ⇒ ¬ IsComp x ∧ ¬ IsEq x ∧ ¬ IsMem x ∧ ¬ IsTf x)
       ∧ (∀ x⦁ IsComp x ⇒ ¬ IsVar x ∧ ¬ IsEq x ∧ ¬ IsMem x ∧ ¬ IsTf x)
       ∧ (∀ x⦁ IsEq x ⇒ ¬ IsComp x ∧ ¬ IsVar x ∧ ¬ IsMem x ∧ ¬ IsTf x)
       ∧ (∀ x⦁ IsMem x ⇒ ¬ IsComp x ∧ ¬ IsVar x ∧ ¬ IsEq x ∧ ¬ IsTf x)
       ∧ (∀ x⦁ IsTf x ⇒ ¬ IsComp x ∧ ¬ IsVar x ∧ ¬ IsEq x ∧ ¬ IsMem x)
=TEX

\ignore{
=SML
set_goal([], ⌜(∀v⦁ IsVar (MkVar v))
	∧ (∀f⦁ ¬ IsVar (MkComp f))
	∧ (∀lr⦁ ¬ IsVar (MkEq lr))
	∧ (∀lr⦁ ¬ IsVar (MkMem lr))
	∧ (∀vc⦁ ¬ IsVar (MkTf vc))⌝);
a (rewrite_tac [get_spec ⌜IsVar⌝,
	get_spec ⌜MkVar⌝,
	get_spec ⌜MkComp⌝,
	get_spec ⌜MkEq⌝,
	get_spec ⌜MkMem⌝,
	get_spec ⌜MkTf⌝]);
val IsVar_clauses = pop_thm();

set_goal([], ⌜(∀v⦁ ¬ IsComp (MkVar v))
	∧ (∀f⦁ IsComp (MkComp f))
	∧ (∀lr⦁ ¬ IsComp (MkEq lr))
	∧ (∀lr⦁ ¬ IsComp (MkMem lr))
	∧ (∀vc⦁ ¬ IsComp (MkTf vc))⌝);
a (rewrite_tac [get_spec ⌜IsComp⌝,
	get_spec ⌜MkVar⌝,
	get_spec ⌜MkComp⌝,
	get_spec ⌜MkEq⌝,
	get_spec ⌜MkMem⌝,
	get_spec ⌜MkTf⌝]);
val IsComp_clauses = pop_thm ();

set_goal([], ⌜(∀v⦁ ¬ IsEq (MkVar v))
	∧ (∀f⦁ ¬ IsEq (MkComp f))
	∧ (∀lr⦁ IsEq (MkEq lr))
	∧ (∀lr⦁ ¬ IsEq (MkMem lr))
	∧ (∀vc⦁ ¬ IsEq (MkTf vc))⌝);
a (rewrite_tac [get_spec ⌜IsEq⌝,
	get_spec ⌜MkVar⌝,
	get_spec ⌜MkComp⌝,
	get_spec ⌜MkEq⌝,
	get_spec ⌜MkMem⌝,
	get_spec ⌜MkTf⌝]);
val IsEq_clauses = pop_thm ();

set_goal([], ⌜(∀v⦁ ¬ IsMem (MkVar v))
	∧ (∀f⦁ ¬ IsMem (MkComp f))
	∧ (∀lr⦁ ¬ IsMem (MkEq lr))
	∧ (∀lr⦁ IsMem (MkMem lr))
	∧ (∀vc⦁ ¬ IsMem (MkTf vc))⌝);
a (rewrite_tac [get_spec ⌜IsMem⌝,
	get_spec ⌜MkVar⌝,
	get_spec ⌜MkComp⌝,
	get_spec ⌜MkEq⌝,
	get_spec ⌜MkMem⌝,
	get_spec ⌜MkTf⌝]);
val IsMem_clauses = pop_thm ();

set_goal([], ⌜(∀v⦁ ¬ IsTf (MkVar v))
	∧ (∀f⦁ ¬ IsTf (MkComp f))
	∧ (∀lr⦁ ¬ IsTf (MkEq lr))
	∧ (∀lr⦁ ¬ IsTf (MkMem lr))
	∧ (∀vc⦁ IsTf (MkTf vc))⌝);
a (rewrite_tac [get_spec ⌜IsTf⌝,
	get_spec ⌜MkVar⌝,
	get_spec ⌜MkComp⌝,
	get_spec ⌜MkEq⌝,
	get_spec ⌜MkMem⌝,
	get_spec ⌜MkTf⌝]);
val IsTf_clauses = pop_thm ();

val Is_clauses = list_∧_intro [IsVar_clauses, IsComp_clauses, IsEq_clauses, IsMem_clauses, IsTf_clauses];

add_pc_thms "'ICsyn" (map get_spec [] @ [ord_nat_thm, Is_clauses]);
set_merge_pcs ["hol1", "'GS1", "'ICsyn"];


set_goal ([], ⌜
	(∀x⦁ IsVar x ⇒ ¬ IsComp x ∧ ¬ IsEq x ∧ ¬ IsMem x ∧ ¬ IsTf x)
∧	(∀x⦁ IsComp x ⇒ ¬ IsVar x ∧ ¬ IsEq x ∧ ¬ IsMem x ∧ ¬ IsTf x)
∧	(∀x⦁ IsEq x ⇒ ¬ IsComp x ∧ ¬ IsVar x ∧ ¬ IsMem x ∧ ¬ IsTf x)
∧	(∀x⦁ IsMem x ⇒ ¬ IsComp x ∧ ¬ IsVar x ∧ ¬ IsEq x ∧ ¬ IsTf x)
∧	(∀x⦁ IsTf x ⇒ ¬ IsComp x ∧ ¬ IsVar x ∧ ¬ IsEq x ∧ ¬ IsMem x)
⌝);
a (rewrite_tac (map get_spec [⌜IsVar⌝, ⌜IsComp⌝, ⌜IsEq⌝, ⌜IsMem⌝, ⌜IsTf⌝]));
a (REPEAT strip_tac THEN asm_rewrite_tac[]
	THEN contr_tac THEN FC_T (MAP_EVERY ante_tac) [natg_one_one_thm]
	THEN PC_T1 "lin_arith" rewrite_tac[]);
val Is_not_fc_clauses = save_pop_thm "Is_not_fc_clauses";
=TEX

}%ignore

Some derived syntax:

ⓈHOLCONST
│ ⦏MkNot⦎ : GS → GS
├───────────
│ ∀f⦁ MkNot f = MkTf (∅⋎g, Pair⋎g f f)
■

ⓈHOLCONST
│ ⦏IsTerm⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsTerm t ⇔ IsVar t ∨ IsComp t
■

ⓈHOLCONST
│ ⦏Terms⦎ : GS SET → GS SET
├───────────
│    ∀s⦁ Terms s = {x | x ∈ s ∧ IsTerm x}
■

=GFT
⦏terms_mono_thm⦎ =
	⊢ ∀ s t⦁ s ⊆ t ⇒ Terms s ⊆ Terms t
=TEX

\ignore{
=SML
set_goal([], ⌜∀s t⦁ s ⊆ t ⇒ Terms s ⊆ Terms t⌝);
a (rewrite_tac [get_spec ⌜Terms⌝] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
val terms_mono_thm = save_pop_thm "terms_mono_thm";
=TEX
}%ignore


ⓈHOLCONST
│ ⦏IsForm⦎ : GS → BOOL
├───────────
│    ∀x⦁ IsForm x ⇔ IsMem x ∨ IsEq x ∨ IsTf x
■

ⓈHOLCONST
│ ⦏Formulas⦎ : GS SET → GS SET
├───────────
│    ∀s⦁ Formulas s = {x | x ∈ s ∧ IsForm x}
■

=GFT
⦏formulas_mono_thm⦎ =
	⊢ ∀ s t⦁ s ⊆ t ⇒ Formulas s ⊆ Formulas t
=TEX

\ignore{
=SML
set_goal([], ⌜∀s t⦁ s ⊆ t ⇒ Formulas s ⊆ Formulas t⌝);
a (rewrite_tac [get_spec ⌜Formulas⌝]
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
val formulas_mono_thm = save_pop_thm "formulas_mono_thm";
=TEX
}%ignore

\subsection{The Inductive Definition of Syntax}

This is accomplished by defining the required closure condition (closure under the above constructors for arguments of the right kind) and then taking the intersection of all sets which satisfy the closure condition.

The closure condition is:

ⓈHOLCONST
│ ⦏RepClosed⦎: GS SET → BOOL
├───────────
│ ∀ s⦁ RepClosed s ⇔
	(∀ ord⦁  ordinal ord ⇒ MkVar ord ∈ s)
∧	(∀ f⦁ f ∈ Formulas s ⇒ MkComp f ∈ s)
∧	(∀ t1 t2⦁ t1 ∈ Terms s ∧ t2 ∈ Terms s
		⇒ MkEq (t1, t2) ∈ s
           	∧ MkMem (t1, t2) ∈ s)
∧	(∀ ord fs⦁ ordinal ord ∧ X⋎g fs ⊆ Formulas s
         ⇒ MkTf (ord, fs) ∈ s)
■

The ``Rep'' in ``RepClosed'' stands for representatives, the idea being that we are defining a syntax for objects which represent sets (and will later assign a semantics to these representatives as sets of representatives).
As it happens it is only the comprehensions which represent sets.

The well-formed syntax is then the smallest set closed under these constructions.

ⓈHOLCONST
│ ⦏Syntax⦎ : GS SET
├───────────
│ Syntax = ⋂{x | RepClosed x}
■

=GFT
⦏syntax_⊆_repclosed_thm⦎ =
	⊢ ∀ s⦁ RepClosed s ⇒ Syntax ⊆ s

⦏repclosed_term_thm⦎ =
	⊢ ∀ t⦁ RepClosed t ⇒ Terms Syntax ⊆ Terms t

⦏repclosed_forn_thm⦎ =
	⊢ ∀ t⦁ RepClosed t ⇒ Formulas Syntax ⊆ Formulas t
=TEX

\ignore{
=SML
set_goal([], ⌜∀s⦁ RepClosed s ⇒ Syntax ⊆ s⌝);
a (rewrite_tac [get_spec ⌜Syntax⌝]
	THEN REPEAT strip_tac THEN asm_fc_tac[]);
val syntax_⊆_repclosed_thm = pop_thm ();

val repclosed_term_thm = (*save_thm ("repclosed_term_thm",*)
all_∀_intro (⇒_trans_rule
(∀_elim ⌜t:GS SET⌝ syntax_⊆_repclosed_thm)
(list_∀_elim [⌜Syntax⌝, ⌜t:GS SET⌝] terms_mono_thm))(*)*);

val repclosed_form_thm = (*save_thm ("repclosed_form_thm",*)
all_∀_intro (⇒_trans_rule
(∀_elim ⌜t:GS SET⌝ syntax_⊆_repclosed_thm)
(list_∀_elim [⌜Syntax⌝, ⌜t:GS SET⌝] formulas_mono_thm))(*)*);
=TEX
}%ignore

This is an ``inductive datatype'' so we should expect the usual kinds of theorems.

Informally these should say:

\begin{itemize}
\item Everything in Syntax is either a Term or a Formula.
\item Syntax is closed under the five syntactic constructors.
\item The syntax constructors are all injections, have disjoint ranges, and partition the syntax. 
\item Any syntactic property which is preserved by the constructors (i.e. is true of any construction if it is true of all its syntactic constituents) is true of everything in syntax (this is an induction principle).
\end{itemize}

=GFT
⦏repclosed_syntax_lemma⦎ =
	⊢ RepClosed Syntax

⦏repclosed_syntax_thm⦎ =
   ⊢ (∀ ord⦁ ordinal ord ⇒ MkVar ord ∈ Syntax)
       ∧ (∀ f⦁ f ∈ Formulas Syntax ⇒ MkComp f ∈ Syntax)
       ∧ (∀ t1 t2
       ⦁ t1 ∈ Terms Syntax ∧ t2 ∈ Terms Syntax
           ⇒ MkEq (t1, t2) ∈ Syntax ∧ MkMem (t1, t2) ∈ Syntax)
       ∧ (∀ ord fs
       ⦁ ordinal ord ∧ (∀ x⦁ x ∈ X⋎g fs ⇒ x ∈ Formulas Syntax)
           ⇒ MkTf (ord, fs) ∈ Syntax)

⦏repclosed_syntax_lemma1⦎ =
	⊢ ∀ s⦁ RepClosed s ⇒ Syntax ⊆ s

⦏repclosed_syntax_lemma2⦎ =
	⊢ ∀ p⦁ RepClosed {x|p x} ⇒ (∀ x⦁ x ∈ Syntax ⇒ p x)
=TEX

\ignore{
=SML
set_goal([], ⌜RepClosed Syntax⌝);
a (rewrite_tac (map get_spec [⌜RepClosed⌝])
	THEN strip_tac);
a (rewrite_tac (map get_spec [⌜RepClosed⌝, ⌜Syntax⌝])
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
a (REPEAT strip_tac);
a (rewrite_tac (map get_spec [⌜Syntax⌝])
	THEN REPEAT strip_tac
	THEN fc_tac [repclosed_form_thm]);
a (asm_fc_tac[get_spec ⌜RepClosed⌝]);
a (asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (rewrite_tac (map get_spec [⌜Syntax⌝])
	THEN REPEAT strip_tac
	THEN fc_tac [repclosed_term_thm]);
a (asm_fc_tac[get_spec ⌜RepClosed⌝]);
a (all_asm_fc_tac[]);
(* *** Goal "2.3" *** *)
a (rewrite_tac (map get_spec [⌜Syntax⌝])
	THEN REPEAT strip_tac
	THEN fc_tac [repclosed_term_thm]);
a (asm_fc_tac[get_spec ⌜RepClosed⌝]);
a (all_asm_fc_tac[]);
(* *** Goal "2.4" *** *)
a (rewrite_tac (map get_spec [⌜Syntax⌝])
	THEN REPEAT strip_tac
	THEN fc_tac [repclosed_form_thm]);
a (asm_fc_tac[get_spec ⌜RepClosed⌝]);
a (lemma_tac ⌜∀ x⦁ x ∈ X⋎g fs ⇒ x ∈ Formulas s⌝
	THEN1 (REPEAT strip_tac
		THEN asm_prove_tac[]));
a (all_asm_fc_tac[]);
val repclosed_syntax_lemma = pop_thm ();

val repclosed_syntax_thm = save_thm ("repclosed_syntax_thm",
	rewrite_rule [get_spec ⌜RepClosed⌝] repclosed_syntax_lemma);

set_goal([], ⌜∀s⦁ RepClosed s ⇒ Syntax ⊆ s⌝);
a (rewrite_tac [get_spec ⌜Syntax⌝]
	THEN prove_tac[]);
val repclosed_syntax_lemma1 = save_pop_thm "repclosed_syntax_lemma1";

set_goal([], ⌜∀p⦁ RepClosed {x | p x} ⇒ ∀x⦁ x ∈ Syntax ⇒ p x⌝);
a (rewrite_tac [get_spec ⌜Syntax⌝] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
val repclosed_syntax_lemma2 = save_pop_thm "repclosed_syntax_lemma2";

set_goal([], ⌜∀x⦁ x ∈ Syntax ⇒ IsTerm x ∨ IsForm x⌝);
a (asm_tac (∀_elim ⌜{x | IsTerm x ∨ IsForm x}⌝ repclosed_syntax_lemma1));
a (lemma_tac ⌜RepClosed {x|IsTerm x ∨ IsForm x}⌝
	THEN1 (rewrite_tac (map get_spec [
	⌜RepClosed⌝, ⌜IsTerm⌝, ⌜IsForm⌝, ⌜MkVar⌝, ⌜IsVar⌝, ⌜MkComp⌝, ⌜IsComp⌝,
	⌜MkEq⌝, ⌜IsEq⌝, ⌜MkMem⌝, ⌜IsMem⌝, ⌜MkTf⌝, ⌜IsTf⌝])));
a (rewrite_tac [get_spec ⌜Syntax⌝] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
val term_or_formula_thm = save_pop_thm "term_or_formula_thm";
=TEX
}%ignore


We need to be able to define functions by recursion over the syntax of comprehensions.
For this we need a recursion theorem.
We have a recursion theorem for well founded recursion already, so we can build on that.
To use that recursion theorem we need to prove that the syntax of comprehensions is well-founded.
This is itself equivalent to an induction principle, so we can try and derive it using the induction principles already available for the syntax of comprehension.

We must first define the relation of priority over the syntax, i.e. the relation between an element of the syntax and its constitutents.

ⓈHOLCONST
│ ⦏ScPrec⦎ : GS → GS → BOOL
├───────────
│ ∀α γ⦁ ScPrec α γ ⇔
│	({α; γ} ⊆ Syntax ∧ γ = MkComp α)
│  ∨	(∃β⦁ {α; β; γ} ⊆ Syntax ∧ γ = MkEq (α, β))
│  ∨	(∃β⦁ {α; β; γ} ⊆ Syntax ∧ γ = MkEq (β, α))
│  ∨	(∃β⦁ {α; β; γ} ⊆ Syntax ∧ γ = MkMem (α, β))
│  ∨	(∃β⦁ {α; β; γ} ⊆ Syntax ∧ γ = MkMem (β, α))
│  ∨	(∃ord fs⦁ α ∈⋎g fs ∧ {α; γ} ⊆ Syntax ∧ γ = MkTf (ord, fs))
■

=GFT
⦏ScPrec_tc_∈_thm⦎ =
	⊢ ∀ x y⦁ ScPrec x y ⇒ tc $∈⋎g x y

⦏well_founded_ScPrec_thm⦎ =
	⊢ well_founded ScPrec

⦏well_founded_tcScPrec_thm⦎ =
	⊢ well_founded (tc ScPrec)
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y⦁ ScPrec x y ⇒ tc $∈⋎g x y⌝);
a (rewrite_tac (map get_spec [⌜ScPrec⌝, ⌜MkComp⌝, ⌜MkEq⌝, ⌜MkMem⌝, ⌜MkTf⌝]));
a (REPEAT strip_tac THEN asm_rewrite_tac [↦_tc_thm]);
(* *** Goal "1" *** *)
a (lemma_tac ⌜tc $∈⋎g x (x ↦⋎g β) ∧ tc $∈⋎g (x ↦⋎g β) (Nat⋎g 2 ↦⋎g x ↦⋎g β)⌝
	THEN1 rewrite_tac [↦_tc_thm]);
a (all_fc_tac [tran_tc_thm2]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜tc $∈⋎g x (β ↦⋎g x) ∧ tc $∈⋎g (β ↦⋎g x) (Nat⋎g 2 ↦⋎g β ↦⋎g x)⌝
	THEN1 rewrite_tac [↦_tc_thm]);
a (all_fc_tac [tran_tc_thm2]);
(* *** Goal "3" *** *)
a (lemma_tac ⌜tc $∈⋎g x (x ↦⋎g β) ∧ tc $∈⋎g (x ↦⋎g β) (Nat⋎g 3 ↦⋎g x ↦⋎g β)⌝
	THEN1 rewrite_tac [↦_tc_thm]);
a (all_fc_tac [tran_tc_thm2]);
(* *** Goal "4" *** *)
a (lemma_tac ⌜tc $∈⋎g x (β ↦⋎g x) ∧ tc $∈⋎g (β ↦⋎g x) (Nat⋎g 3 ↦⋎g β ↦⋎g x)⌝
	THEN1 rewrite_tac [↦_tc_thm]);
a (all_fc_tac [tran_tc_thm2]);
(* *** Goal "5" *** *)
a (lemma_tac ⌜tc $∈⋎g fs (ord ↦⋎g fs) ∧ tc $∈⋎g (ord ↦⋎g fs) (Nat⋎g 4 ↦⋎g ord ↦⋎g fs)⌝
	THEN1 rewrite_tac [↦_tc_thm]);
a (all_fc_tac [tran_tc_thm2, tc_incr_thm]);
a (all_fc_tac [tran_tc_thm2, tc_incr_thm]);
val ScPrec_tc_∈_thm = pop_thm ();

set_goal ([], ⌜well_founded ScPrec⌝);
a (rewrite_tac [get_spec ⌜well_founded⌝]);
a (REPEAT strip_tac);
a (asm_tac (∀_elim ⌜s⌝ gs_cv_ind_thm));
a (lemma_tac ⌜∀ x⦁ (∀ y⦁ tc $∈⋎g y x ⇒ s y) ⇒ s x⌝
	THEN1 REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜∀ y⦁ ScPrec y x ⇒ s y⌝
	THEN1 (REPEAT strip_tac THEN all_fc_tac [ScPrec_tc_∈_thm]
		THEN asm_fc_tac []));
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (asm_fc_tac[]);
a (asm_rewrite_tac[]);
val well_founded_ScPrec_thm =  save_pop_thm "well_founded_ScPrec_thm";

set_goal([], ⌜well_founded (tc ScPrec)⌝);
a (asm_tac well_founded_ScPrec_thm);
a (fc_tac [wf_tc_wf_thm]);
val well_founded_tcScPrec_thm = save_pop_thm ("well_founded_tcScPrec_thm");

=TEX

}%ignore

=SML
val ⦏SC_INDUCTION_T⦎ = WFCV_INDUCTION_T well_founded_ScPrec_thm;
val ⦏sc_induction_tac⦎ = wfcv_induction_tac well_founded_ScPrec_thm;
=TEX

The set Syntax gives us the syntactically well-formed phrases of our language.
It will be useful to have some predicates which incorporate well-formedness, which are defined here.

ⓈHOLCONST
│ ⦏WfTerms⦎ : GS SET
├───────────
│ WfTerms = Terms Syntax
■

ⓈHOLCONST
│ ⦏WfComp⦎ : GS SET
├───────────
│    WfComp = {x | x ∈ WfTerms ∧ IsComp x}
■

ⓈHOLCONST
│ ⦏WfForms⦎ : GS SET
├───────────
│ WfForms = Formulas Syntax
■

=GFT
⦏syntax_disj_thm⦎ =
   ⊢ ∀ x
     ⦁ x ∈ Syntax
         ⇒ (∃ ord⦁ ordinal ord ∧ x = MkVar ord)
           ∨ (∃ f⦁ f ∈ WfForms ∧ x = MkComp f)
           ∨ (∃ t1 t2⦁ t1 ∈ WfTerms ∧ t2 ∈ WfTerms ∧ x = MkEq (t1, t2))
           ∨ (∃ t1 t2⦁ t1 ∈ WfTerms ∧ t2 ∈ WfTerms ∧ x = MkMem (t1, t2))
           ∨ (∃ ord fs⦁ ordinal ord ∧ X⋎g fs ⊆ WfForms ∧ x = MkTf (ord, fs))

⦏is_fc_clauses⦎ =
   ⊢ ∀ x
     ⦁ x ∈ Syntax
         ⇒ (IsVar x ⇒ (∃ ord⦁ ordinal ord ∧ x = MkVar ord))
           ∧ (IsComp x ⇒ (∃ f⦁ f ∈ WfForms ∧ x = MkComp f))
           ∧ (IsEq x
             ⇒ (∃ t1 t2⦁ t1 ∈ WfTerms ∧ t2 ∈ WfTerms ∧ x = MkEq (t1, t2)))
           ∧ (IsMem x
             ⇒ (∃ t1 t2⦁ t1 ∈ WfTerms ∧ t2 ∈ WfTerms ∧ x = MkMem (t1, t2)))
           ∧ (IsTf x
             ⇒ (∃ ord fs
             ⦁ ordinal ord ∧ X⋎g fs ⊆ WfForms ∧ x = MkTf (ord, fs)))

⦏syn_proj_clauses⦎ =
    ⊢ (∀ ord⦁ VarNum (MkVar ord) = ord)
       ∧ (∀ f⦁ CompBody (MkComp f) = f)
       ∧ (∀ l r⦁ AtomLhs (MkEq (l, r)) = l)
       ∧ (∀ l r⦁ AtomRhs (MkEq (l, r)) = r)
       ∧ (∀ l r⦁ AtomLhs (MkMem (l, r)) = l)
       ∧ (∀ l r⦁ AtomRhs (MkMem (l, r)) = r)
       ∧ (∀ v f⦁ TfVars (MkTf (v, f)) = v)
       ∧ (∀ v f⦁ TfForms (MkTf (v, f)) = f)

⦏is_fc_clauses2⦎ =
   ⊢ ∀ x
     ⦁ x ∈ Syntax
         ⇒ (IsVar x ⇒ ordinal (VarNum x))
           ∧ (IsComp x ⇒ CompBody x ∈ WfForms)
           ∧ (IsEq x ⇒ AtomLhs x ∈ WfTerms ∧ AtomRhs x ∈ WfTerms)
           ∧ (IsMem x ⇒ AtomLhs x ∈ WfTerms ∧ AtomRhs x ∈ WfTerms)
           ∧ (IsTf x
             ⇒ ordinal (TfVars x) ∧ (∀ y⦁ y ∈⋎g TfForms x ⇒ y ∈ WfForms))

⦏syn_comp_fc_clauses⦎ =
   ⊢ (∀ x⦁ MkVar x ∈ Syntax ⇒ ordinal x)
       ∧ (∀ x⦁ MkComp x ∈ Syntax ⇒ x ∈ WfForms)
       ∧ (∀ l r⦁ MkEq (l, r) ∈ Syntax ⇒ l ∈ WfTerms ∧ r ∈ WfTerms)
       ∧ (∀ l r⦁ MkMem (l, r) ∈ Syntax ⇒ l ∈ WfTerms ∧ r ∈ WfTerms)
       ∧ (∀ v f
       ⦁ MkTf (v, f) ∈ Syntax ⇒ ordinal v ∧ (∀ y⦁ y ∈⋎g f ⇒ y ∈ WfForms))=TEX

⦏ft_syntax_thm⦎ =
   ⊢ ∀ x⦁ x ∈ WfForms ∨ x ∈ WfTerms ⇒ x ∈ Syntax

⦏formula_cases_thm⦎ =
	⊢ ∀ x⦁ x ∈ WfForms ∨ IsForm x ⇒ IsEq x ∨ IsMem x ∨ IsTf x

⦏term_cases_thm⦎ =
	⊢ ∀ x⦁ x ∈ WfTerms ∨ IsTerm x ⇒ IsVar x ∨ IsComp x

⦏scprec_fc_clauses⦎ =
   ⊢ ∀ α β γ ord fs
     ⦁ γ ∈ Syntax
         ⇒ γ = MkComp α
           ∨ γ = MkEq (α, β)
           ∨ γ = MkEq (β, α)
           ∨ γ = MkMem (α, β)
           ∨ γ = MkMem (β, α)
           ∨ γ = MkTf (ord, fs) ∧ α ∈⋎g fs
         ⇒ ScPrec α γ

⦏scprec_fc_clauses2⦎ =
   ⊢ ∀ t
     ⦁ t ∈ Syntax
         ⇒ (IsComp t ⇒ ScPrec (CompBody t) t)
           ∧ (IsEq t ∨ IsMem t ⇒ ScPrec (AtomLhs t) t ∧ ScPrec (AtomRhs t) t)
           ∧ (IsTf t ⇒ (∀ f⦁ f ∈⋎g TfForms t ⇒ ScPrec f t))
=TEX

\ignore{
=SML
set_goal([], ⌜∀x⦁	x ∈ Syntax
⇒	(∃ord⦁ ordinal ord ∧ x = MkVar ord)
  ∨	(∃f⦁ f ∈ WfForms ∧ x = MkComp f)
  ∨	(∃t1 t2⦁ t1 ∈ WfTerms ∧ t2 ∈ WfTerms ∧ x = MkEq (t1,t2))
  ∨	(∃t1 t2⦁ t1 ∈ WfTerms ∧ t2 ∈ WfTerms ∧ x = MkMem (t1,t2))
  ∨	(∃ord fs⦁ ordinal ord ∧ (∀y⦁ y ∈⋎g fs ⇒ y ∈ WfForms) ∧ x = MkTf (ord, fs))
⌝);
a (contr_tac);
a (lemma_tac ⌜RepClosed (Syntax \ {x})⌝
	THEN1 (rewrite_tac [get_spec ⌜RepClosed⌝]
		THEN strip_tac));
(* *** Goal "1" *** *)
a (strip_tac THEN strip_tac
	THEN asm_fc_tac [repclosed_syntax_thm]
	THEN asm_rewrite_tac[]);
a (spec_nth_asm_tac 8 ⌜ord⌝);
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (strip_tac);
(* *** Goal "2.1" *** *)
a (strip_tac THEN strip_tac);
a (lemma_tac ⌜f ∈ Formulas (Syntax)⌝
	THEN1(POP_ASM_T ante_tac
		THEN rewrite_tac [get_spec ⌜Formulas⌝]
		THEN prove_tac[]));
a (ALL_FC_T rewrite_tac [repclosed_syntax_thm]);
a (spec_nth_asm_tac 6 ⌜f⌝);
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac [get_spec ⌜WfForms⌝]);
a (strip_tac);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a strip_tac;
a (REPEAT ∀_tac THEN strip_tac);
a (lemma_tac ⌜t1 ∈ Terms (Syntax) ∧ t2 ∈ Terms (Syntax)⌝
	THEN1(POP_ASM_T ante_tac
		THEN POP_ASM_T ante_tac
		THEN rewrite_tac [get_spec ⌜Terms⌝]
		THEN prove_tac[]));
a (ALL_FC_T rewrite_tac [repclosed_syntax_thm]);
a (spec_nth_asm_tac 7 ⌜t1⌝);
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac [get_spec ⌜WfTerms⌝]);
a (swap_nth_asm_concl_tac 1);
a (spec_nth_asm_tac 1 ⌜t2⌝);
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "2.2.1.2" *** *)
a (spec_nth_asm_tac 7 ⌜t1⌝);
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac [get_spec ⌜WfTerms⌝]);
a (swap_nth_asm_concl_tac 1);
a (spec_nth_asm_tac 1 ⌜t2⌝);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a (REPEAT strip_tac);
(* *** Goal "2.2.2.1" *** *)
a (lemma_tac ⌜∀ x⦁ x ∈ X⋎g fs ⇒ x ∈ Formulas Syntax⌝);
a (POP_ASM_T ante_tac);
a (rewrite_tac [get_spec ⌜Formulas⌝]);
a (REPEAT strip_tac THEN asm_fc_tac[]);
a (ALL_FC_T rewrite_tac [repclosed_syntax_thm]);
(* *** Goal "2.2.2.2" *** *)
a (LEMMA_T ⌜∀ y⦁ y ∈ X⋎g fs ⇒ y ∈ WfForms⌝ ante_tac
	THEN1 (rewrite_tac [get_spec ⌜WfForms⌝]
		THEN POP_ASM_T ante_tac
		THEN rewrite_tac [get_spec ⌜Formulas⌝]
		THEN REPEAT strip_tac
		THEN_TRY asm_fc_tac[]));
a (rewrite_tac [get_spec ⌜X⋎g⌝] THEN strip_tac);
a (spec_nth_asm_tac 4 ⌜ord⌝);
a (SPEC_NTH_ASM_T 1 ⌜fs⌝ ante_tac);
a (GET_NTH_ASM_T 4 rewrite_thm_tac);
a (GET_NTH_ASM_T 2 (rewrite_thm_tac));
a (strip_tac);
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (asm_tac repclosed_syntax_lemma1);
a (spec_nth_asm_tac 1 ⌜Syntax \ {x}⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
val syntax_disj_thm = save_pop_thm "syntax_disj_thm";

set_goal([], ⌜∀x⦁	x ∈ Syntax
⇒	(IsVar x ⇒ ∃ord⦁ ordinal ord ∧ x = MkVar ord)
∧	(IsComp x ⇒ ∃f⦁ f ∈ WfForms ∧ x = MkComp f)
∧	(IsEq x ⇒ ∃t1 t2⦁ t1 ∈ WfTerms ∧ t2 ∈ WfTerms ∧ x = MkEq (t1,t2))
∧	(IsMem x ⇒ ∃t1 t2⦁ t1 ∈ WfTerms ∧ t2 ∈ WfTerms ∧ x = MkMem (t1,t2))
∧	(IsTf x ⇒ ∃ord fs⦁ ordinal ord ∧ (∀y⦁ y ∈⋎g fs ⇒ y ∈ WfForms) ∧ x = MkTf (ord, fs))
⌝);
a (REPEAT_N 2 strip_tac);
a (asm_tac (syntax_disj_thm));
a (asm_fc_tac[] THEN asm_rewrite_tac [Is_clauses]);
(* *** Goal "1" *** *)
a (∃_tac ⌜ord⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜f⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜t1⌝ THEN ∃_tac ⌜t2⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜t1⌝ THEN ∃_tac ⌜t2⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜ord⌝ THEN ∃_tac ⌜fs⌝ THEN asm_rewrite_tac[]);
val is_fc_clauses = save_pop_thm "is_fc_clauses";

set_goal([], ⌜(∀ord⦁ VarNum (MkVar ord) = ord)
	∧	(∀f⦁ CompBody (MkComp f) = f)
	∧	(∀l r⦁ AtomLhs (MkEq (l, r)) = l)
	∧	(∀l r⦁ AtomRhs (MkEq (l, r)) = r)
	∧	(∀l r⦁ AtomLhs (MkMem (l, r)) = l)
	∧	(∀l r⦁ AtomRhs (MkMem (l, r)) = r)
	∧	(∀v f⦁ TfVars (MkTf (v, f)) = v)
	∧	(∀v f⦁ TfForms (MkTf (v, f)) = f)
⌝);
a (rewrite_tac (map get_spec [
	⌜VarNum⌝, ⌜MkVar⌝, ⌜CompBody⌝, ⌜MkComp⌝,
	⌜AtomLhs⌝, ⌜AtomRhs⌝, ⌜MkEq⌝, ⌜MkMem⌝,
	⌜TfVars⌝, ⌜MkTf⌝, ⌜TfForms⌝]));
val syn_proj_clauses = save_pop_thm "syn_proj_clauses";

add_pc_thms "'ICsyn" [syn_proj_clauses];
set_merge_pcs ["hol1", "'GS1", "'ICsyn"];

set_goal([], ⌜∀x⦁	x ∈ Syntax
⇒	(IsVar x ⇒ ordinal (VarNum x))
∧	(IsComp x ⇒ CompBody x ∈ WfForms)
∧	(IsEq x ⇒ AtomLhs x ∈ WfTerms ∧ AtomRhs x ∈ WfTerms)
∧	(IsMem x ⇒ AtomLhs x ∈ WfTerms ∧ AtomRhs x ∈ WfTerms)
∧	(IsTf x ⇒ ordinal (TfVars x) ∧ (∀y⦁ y ∈⋎g (TfForms x) ⇒ y ∈ WfForms))
⌝);
a (REPEAT strip_tac
	THEN all_fc_tac [is_fc_clauses]
	THEN GET_NTH_ASM_T 1 (var_elim_asm_tac o concl)
	THEN_TRY asm_rewrite_tac[]);
a (GET_NTH_ASM_T 3 (asm_tac o (rewrite_rule [])));
a (all_asm_fc_tac[]);
val is_fc_clauses2 = save_pop_thm "is_fc_clauses2";

set_goal([], ⌜∀v f lr vf⦁
		¬ MkVar v = MkComp f
	∧	¬ MkVar v = MkEq lr
	∧	¬ MkVar v = MkMem lr
	∧	¬ MkVar v = MkTf vf
	∧	¬ MkComp f = MkVar v
	∧	¬ MkComp f = MkEq lr
	∧	¬ MkComp f = MkMem lr
	∧	¬ MkComp f = MkTf vf
	∧	¬ MkEq lr = MkVar v
	∧	¬ MkEq lr = MkComp f
	∧	¬ MkEq lr = MkMem lr
	∧	¬ MkEq lr = MkTf vf
	∧	¬ MkMem lr = MkVar v
	∧	¬ MkMem lr = MkComp f
	∧	¬ MkMem lr = MkEq lr
	∧	¬ MkMem lr = MkTf vf
	∧	¬ MkTf vf = MkVar v
	∧	¬ MkTf vf = MkComp f
	∧	¬ MkTf vf = MkEq lr
	∧	¬ MkTf vf = MkMem lr
⌝);
a (rewrite_tac (map get_spec [⌜MkVar⌝, ⌜MkComp⌝, ⌜MkEq⌝, ⌜MkMem⌝, ⌜MkTf⌝]));
val syn_con_neq_clauses = save_pop_thm "syn_con_neq_clauses";

add_pc_thms "'ICsyn" [syn_con_neq_clauses];
set_merge_pcs ["hol1", "'GS1", "'ICsyn"];

set_goal([], ⌜(∀x⦁ MkVar x ∈ Syntax ⇒ ordinal x)
∧	(∀x⦁ MkComp x ∈ Syntax ⇒ x ∈ WfForms)
∧	(∀l r⦁ MkEq (l, r) ∈ Syntax ⇒ l ∈ WfTerms ∧ r ∈ WfTerms)
∧	(∀l r⦁ MkMem (l, r) ∈ Syntax ⇒ l ∈ WfTerms ∧ r ∈ WfTerms)
∧	(∀v f⦁ MkTf (v, f) ∈ Syntax ⇒ ordinal v ∧ (∀y⦁ y ∈⋎g f ⇒ y ∈ WfForms))⌝);
a (REPEAT strip_tac
	THEN FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule []))) [is_fc_clauses2]);
a (asm_fc_tac[]);
val syn_comp_fc_clauses = save_pop_thm "syn_comp_fc_clauses";

set_goal([], ⌜∀x⦁ x ∈ WfForms ∨ x ∈ WfTerms ⇒ x ∈ Syntax⌝);
a (rewrite_tac (map get_spec [⌜WfForms⌝, ⌜WfTerms⌝, ⌜Formulas⌝, ⌜Terms⌝])
	THEN REPEAT strip_tac);
val ft_syntax_thm = save_pop_thm "ft_syntax_thm";

set_goal([], ⌜∀x⦁ x ∈ WfForms ∨ IsForm x ⇒ IsEq x ∨ IsMem x ∨ IsTf x⌝);
a (rewrite_tac (map get_spec [⌜WfForms⌝, ⌜IsForm⌝, ⌜Formulas⌝]));
a (REPEAT strip_tac);
val formula_cases_thm = save_pop_thm "formula_cases_thm";

set_goal([], ⌜∀x⦁ x ∈ WfTerms ∨ IsTerm x ⇒ IsVar x ∨ IsComp x⌝);
a (rewrite_tac (map get_spec [⌜WfTerms⌝, ⌜IsTerm⌝, ⌜Terms⌝]));
a (REPEAT strip_tac);
val term_cases_thm = save_pop_thm "term_cases_thm";

set_goal([], ⌜∀α β γ ord fs⦁ γ ∈ Syntax ⇒
		(γ = MkComp α
	∨	γ = MkEq (α, β)
	∨	γ = MkEq (β, α)
	∨	γ = MkMem (α, β)
	∨	γ = MkMem (β, α)
	∨	γ = MkTf (ord, fs) ∧ α ∈⋎g fs) ⇒ ScPrec α γ
⌝);
a (rewrite_tac [get_spec ⌜ScPrec⌝]);
a (REPEAT ∀_tac THEN strip_tac THEN strip_tac);
(* *** Goal "1" *** *)
a (GET_NTH_ASM_T 1 (var_elim_asm_tac o concl)
	THEN fc_tac [syn_comp_fc_clauses]
	THEN fc_tac [ft_syntax_thm] THEN rewrite_tac[]
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (GET_NTH_ASM_T 1 (var_elim_asm_tac o concl)
	THEN fc_tac [syn_comp_fc_clauses]
	THEN fc_tac [ft_syntax_thm] THEN_TRY rewrite_tac[]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 3 ⌜β⌝);
a (var_elim_asm_tac  ⌜x = α⌝);
a (var_elim_asm_tac  ⌜x = β⌝);
a (var_elim_asm_tac  ⌜x = MkEq (α, β)⌝);
(* *** Goal "3" *** *)
a (GET_NTH_ASM_T 1 (var_elim_asm_tac o concl)
	THEN fc_tac [syn_comp_fc_clauses]
	THEN fc_tac [ft_syntax_thm] THEN_TRY rewrite_tac[]
	THEN contr_tac);
a (spec_nth_asm_tac 3 ⌜β⌝);
a (GET_NTH_ASM_T 2 (var_elim_asm_tac o concl));
a (GET_NTH_ASM_T 2 (var_elim_asm_tac o concl));
a (GET_NTH_ASM_T 2 (var_elim_asm_tac o concl));
(* *** Goal "4" *** *)
a (GET_NTH_ASM_T 1 (var_elim_asm_tac o concl)
	THEN fc_tac [syn_comp_fc_clauses]
	THEN fc_tac [ft_syntax_thm] THEN_TRY rewrite_tac[]
	THEN contr_tac);
a (spec_nth_asm_tac 2 ⌜β⌝);
a (GET_NTH_ASM_T 2 (var_elim_asm_tac o concl));
a (GET_NTH_ASM_T 2 (var_elim_asm_tac o concl));
a (GET_NTH_ASM_T 2 (var_elim_asm_tac o concl));
(* *** Goal "5" *** *)
a (GET_NTH_ASM_T 1 (var_elim_asm_tac o concl)
	THEN fc_tac [syn_comp_fc_clauses]
	THEN fc_tac [ft_syntax_thm] THEN_TRY rewrite_tac[]
	THEN contr_tac);
a (spec_nth_asm_tac 1 ⌜β⌝);
a (GET_NTH_ASM_T 2 (var_elim_asm_tac o concl));
a (GET_NTH_ASM_T 2 (var_elim_asm_tac o concl));
a (GET_NTH_ASM_T 2 (var_elim_asm_tac o concl));
(* *** Goal "6" *** *)
a (GET_NTH_ASM_T 2 (var_elim_asm_tac o concl)
	THEN fc_tac [syn_comp_fc_clauses]
	THEN asm_fc_tac[]
	THEN fc_tac [ft_syntax_thm] THEN_TRY rewrite_tac[]
	THEN contr_tac);
a (spec_nth_asm_tac 1 ⌜ord⌝);
a (spec_nth_asm_tac 1 ⌜fs⌝);
a (GET_NTH_ASM_T 2 (var_elim_asm_tac o concl));
a (GET_NTH_ASM_T 2 (var_elim_asm_tac o concl));
val scprec_fc_clauses = save_pop_thm "scprec_fc_clauses";

set_goal ([], ⌜∀t⦁ t ∈ Syntax ⇒ (IsComp t ⇒ ScPrec (CompBody t) t)
	∧ (IsEq t ∨ IsMem t ⇒ ScPrec (AtomLhs t) t ∧ ScPrec (AtomRhs t) t)
	∧ (IsTf t ⇒ ∀f⦁ f ∈⋎g TfForms t ⇒ ScPrec (f) t)⌝);
a (REPEAT strip_tac
	THEN all_fc_tac [is_fc_clauses]
	THEN all_fc_tac [scprec_fc_clauses]
	THEN POP_ASM_T ante_tac
	THEN_TRY asm_rewrite_tac []);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a (strip_tac);
a (DROP_NTH_ASM_T 4 ante_tac
	THEN asm_rewrite_tac[]
	THEN strip_tac
	THEN all_fc_tac [scprec_fc_clauses]);
a (SYM_ASMS_T rewrite_tac);
val scprec_fc_clauses2 = save_pop_thm "scprec_fc_clauses2";
=TEX
}%ignore

\subsection{Proof Contexts}

=SML
add_pc_thms "'ICsyn" [];
commit_pc "'ICsyn";

force_new_pc "⦏ICsyn⦎";
merge_pcs ["hol", "'GS1", "'ICsyn"] "ICsyn";
commit_pc "ICsyn";

force_new_pc "⦏ICsyn1⦎";
merge_pcs ["hol1", "'GS1", "'ICsyn"] "ICsyn1";
commit_pc "ICsyn1";
=TEX

\section{SEMANTICS}

=SML
open_theory "ICsyn";
force_new_theory "⦏ICsem⦎";
force_new_pc "⦏'ICsem⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'ICsem";
(* set_merge_pcs ["hol", "'GS1", "'ICsyn", "'ICsem"]; *)
set_merge_pcs ["ICsyn", "'ICsem"];
=TEX

The semantics will be defined as a functor which transforms partial membership and equality relations, and is parameterised by a domain set (which gives the range of the quantifiers).

We want to be able to evaluate membership claims between closed comprehensions.
This is done by substituting the comprehension on the left for the variable zero in the body of the comprehension on the right and evaluating the result.
Alternatively, evaluating the body of the comprehension on the right in a context which consists just of the assignment to variable zero of the comprehsion on the left.
When we reach atomic equations and membership claims during this evaluation we look them up using the initial values for the equality and membership relations.
We can only do this with closed comprehensions, so at this point, if not before we must substitute values from the context for the free variables in the comprehensions (these variables will be bound by quantifiers so we will be doing this substitution for every comprehension in turn).

So we need to be able to evaluate and to instantiate, evaluation taking place down to the level of atomic formulae and instantiation below that level (note that the terms in an atomic formulae will usually be comprehesions and hence may contain non-atomic formulae).

The following type abbreviations are intended to make the specification more readable:

\begin{description}
\item{EV}
Expression value
\item{VA}
Variable assignment
\item{TD}
Term denotation
\item{TV}
Truth value
\item{FD}
Formula denotation
\item{R}
Partial relation
\item{PR}
Pair of partial relations
\end{description}

=SML
declare_type_abbrev("⦏EV⦎", [], ⓣGS⌝);
declare_type_abbrev("⦏VA⦎", [], ⓣGS × (GS → EV)⌝);
declare_type_abbrev("⦏TD⦎", [], ⓣVA → EV⌝);
declare_type_abbrev("⦏TV⦎", [], ⓣBOOL + ONE⌝);
declare_type_abbrev("⦏FD⦎", [], ⓣVA → TV⌝);
declare_type_abbrev("⦏R⦎", [], ⓣGS → GS → TV⌝);
declare_type_abbrev("⦏PR⦎", [], ⓣR × R⌝);
=TEX

Sometimes in the semantics similar operations are defined several times over different kinds of objects.
In these cases we sometimes distinguish between the variants by using the same name subscripted by and indicator of the type.

\begin{itemize}
\item[$name⋎r$] type ⓣR⌝
\item[$name⋎p⋎r$] type ⓣPR⌝
\end{itemize}

\subsection{Substitution}

This will be an inductive definition over the relevant syntactic structures, but the definition is given in pieces.

To define the semantics of comprehension we need to be able to modify a variable assignment.
The modification required is to insert a new value for variable zero shifting all the existing values up one variable number.

ⓈHOLCONST
│ ⦏VaRan⦎ : VA → EV SET
├───────────
│ ∀va⦁ VaRan va = {tv | ∃α⦁ α <⋎o Fst va ∧ tv = Snd va α}
■

ⓈHOLCONST
│ ⦏InsertVar⦎ : VA → EV → VA
├───────────
│ ∀d f tv⦁ InsertVar (d, f) tv = 
│	(suc⋎o d, λβ⦁ if β = ∅⋎g then tv else f (β --⋎o (Nat⋎g 1)))
■

This one concatenates two variable assignments.

ⓈHOLCONST
│ ⦏InsertVars⦎ : VA → VA → VA
├───────────
│ ∀α β f1 f2⦁ InsertVars (α, f1) (β, f2) = 
│	(α +⋎o β, λγ⦁ if γ <⋎o α then f1 γ else f2 (γ --⋎o α))
■

We now define the operation of substituting into a term or formula values for free variables as specified by an assignment.
The substitution is for free variables and the operator requires as an argument the number of bound variables for any particular context (the numbers of the free variables a shifted upwards as bound variables are introduced.

ⓈHOLCONST
│ ⦏SubstTerm⦎ : ((GS × VA) × GS → GS) → ((GS × VA) × GS) → GS
├───────────
│ SubstTerm = λsf ((α, (β, f)), t)⦁
│	if t ∈ WfTerms
│	then	if IsVar t
│		then if α ≤⋎o VarNum t ∧ VarNum t <⋎o (α +⋎o β)
│		     then f ((VarNum t) --⋎o α)
│	    	     else t
│		else sf ((α, (InsertVar (β, f) ∅⋎g)), CompBody t)
│	else t
■

The following gives us a well-founded ordering on the parameters to SubstForm which will be useful in proving its well-definedness.

ⓈHOLCONST
│ ⦏SubOrder⦎ : ((GS × VA) × GS) → ((GS × VA) × GS) → BOOL
├───────────
│ SubOrder = λs t⦁ tc ScPrec (Snd s) (Snd t)
■

The following results will be useful later in proving the existence of a fixed point.

First some points about the constituents of terms.

=GFT
⦏tran_suborder_thm⦎ =
   ⊢ trans SubOrder

⦏tran_suborder_thm2⦎ =
	⊢ ∀ s t u⦁ SubOrder s t ∧ SubOrder t u ⇒ SubOrder s u

⦏substterm_lemma1⦎ =
   ⊢ ∀ sf1 sf2 t
     ⦁ (∀ α β_f y
         ⦁ SubOrder ((α, β_f), y) ((α, β_f), t)
             ⇒ sf1 ((α, β_f), y) = sf2 ((α, β_f), y))
         ⇒ (∀ α β_f⦁ SubstTerm sf1 ((α, β_f), t) = SubstTerm sf2 ((α, β_f), t))

⦏well_founded_SubOrder_thm⦎ =
   ⊢ well_founded SubOrder

=TEX

\ignore{
=SML
set_goal([], ⌜trans SubOrder⌝);
a (rewrite_tac [get_spec ⌜SubOrder⌝, get_spec ⌜trans⌝]
	THEN REPEAT strip_tac);
a (all_fc_tac [tran_tc_thm2]);
val tran_suborder_thm = save_pop_thm "tran_suborder_thm";

val tran_suborder_thm2 = save_thm ("tran_suborder_thm2", rewrite_rule [get_spec ⌜trans⌝] tran_suborder_thm);

set_goal([], ⌜well_founded SubOrder⌝);
a (rewrite_tac [get_spec ⌜SubOrder⌝]);
a (asm_tac (∀_elim ⌜Snd: (GS × VA) × GS → GS⌝
(⇒_elim (∀_elim ⌜tc ScPrec⌝ wf_image_wf_thm) well_founded_tcScPrec_thm)));
a (strip_tac);
val well_founded_SubOrder_thm = save_pop_thm "well_founded_SubOrder_thm";

set_goal([], ⌜∀sf1 sf2 p⦁
	(∀ y⦁ SubOrder y p ⇒ sf1 y = sf2 y)
		⇒ SubstTerm sf1 p = SubstTerm sf2 p⌝);
a (rewrite_tac [get_spec ⌜SubstTerm⌝] THEN REPEAT strip_tac);
a (cases_tac ⌜Snd p ∈ WfTerms⌝ THEN asm_rewrite_tac[]);
a (cases_tac ⌜IsVar (Snd p)⌝ THEN asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule (map get_spec
	[⌜WfTerms⌝, ⌜Terms⌝, ⌜IsTerm⌝]))));
a (lemma_tac ⌜SubOrder ((Fst (Fst p), InsertVar (Snd (Fst p)) ∅⋎g), CompBody (Snd p)) (Fst p, Snd p)⌝);
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜SubOrder⌝]);
a (lemma_tac ⌜ScPrec (CompBody (Snd p)) (Snd p)⌝ THEN1 all_fc_tac [scprec_fc_clauses2]);
a (fc_tac [tc_incr_thm]);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac[]);
a (strip_tac THEN asm_fc_tac []);
val substterm_lemma1 = save_pop_thm "substterm_lemma1";
=TEX
}%ignore

Substitution over formulae is defined by recursion over the syntax and is thefore as the fixed point of a functor.

ⓈHOLCONST
│ ⦏SubstAtom⦎ : ((GS × VA) × GS → GS) → ((GS × VA) × GS → GS)
├───────────
│ SubstAtom = λsf ((α, va), f)⦁
│    (if IsEq f then MkEq else MkMem)
│	(SubstTerm sf ((α, va), (AtomLhs f)),
│	 SubstTerm sf ((α, va), (AtomRhs f)))
■

=GFT
substatom_lemma1 =
   ⊢ ∀ sf1 sf2 f
     ⦁ Snd f ∈ Syntax
         ⇒ IsEq (Snd f) ∨ IsMem (Snd f)
         ⇒ (∀ y⦁ SubOrder y f ⇒ sf1 y = sf2 y)
         ⇒ SubstAtom sf1 f = SubstAtom sf2 f
=TEX

\ignore{
=SML
set_goal([], ⌜∀sf1 sf2 f⦁ Snd f ∈ Syntax ⇒ (IsEq (Snd f) ∨ IsMem (Snd f)) ⇒
	(∀ y⦁ SubOrder y f ⇒ sf1 y = sf2 y)
		⇒ SubstAtom sf1 f = SubstAtom sf2 f⌝);
a (rewrite_tac [get_spec ⌜SubstAtom⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜SubstTerm sf1 (Fst f, AtomLhs (Snd f))
	   = SubstTerm sf2 (Fst f, AtomLhs (Snd f))⌝);
(* *** Goal "1.1" *** *)
a (lemma_tac ⌜(∀ y⦁ SubOrder y (Fst f, AtomLhs (Snd f)) ⇒ sf1 y = sf2 y)⌝
	THEN1 REPEAT strip_tac);
(* *** Goal "1.1.1" *** *)
a (lemma_tac ⌜SubOrder (Fst f, AtomLhs (Snd f)) (Fst f, Snd f)⌝);
(* *** Goal "1.1.1.1" *** *)
a (rewrite_tac [get_spec ⌜SubOrder⌝]);
a (lemma_tac ⌜ScPrec (AtomLhs (Snd f)) (Snd f)⌝);
(* *** Goal "1.1.1.1.1" *** *)
a (all_fc_tac [scprec_fc_clauses2]);
a (fc_tac [tc_incr_thm]);
(* *** Goal "1.1.1.1.2" *** *)
a (ALL_FC_T (MAP_EVERY (asm_tac o (rewrite_rule []))) [tran_suborder_thm2]);
a (all_asm_fc_tac []);
(* *** Goal "1.1.2" *** *)
a (fc_tac [substterm_lemma1]);
(* *** Goal "1.2" *** *)
a (asm_rewrite_tac[]);
a (lemma_tac ⌜(∀ y⦁ SubOrder y (Fst f, AtomRhs (Snd f)) ⇒ sf1 y = sf2 y)⌝
	THEN1 REPEAT strip_tac);
(* *** Goal "1.2.1" *** *)
a (lemma_tac ⌜SubOrder (Fst f, AtomRhs (Snd f)) (Fst f, Snd f)⌝);
(* *** Goal "1.2.1.1" *** *)
a (rewrite_tac [get_spec ⌜SubOrder⌝]);
a (lemma_tac ⌜ScPrec (AtomRhs (Snd f)) (Snd f)⌝);
(* *** Goal "1.2.1.1.1" *** *)
a (all_fc_tac [scprec_fc_clauses2]);
a (fc_tac [tc_incr_thm]);
(* *** Goal "1.2.1.2" *** *)
a (ALL_FC_T (MAP_EVERY (asm_tac o (rewrite_rule []))) [tran_suborder_thm2]);
a (all_asm_fc_tac []);
(* *** Goal "1.2.2" *** *)
a (fc_tac [substterm_lemma1]);
(* *** Goal "1.2" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜SubstTerm sf1 (Fst f, AtomLhs (Snd f))
	   = SubstTerm sf2 (Fst f, AtomLhs (Snd f))⌝);
(* *** Goal "1.1" *** *)
a (lemma_tac ⌜(∀ y⦁ SubOrder y (Fst f, AtomLhs (Snd f)) ⇒ sf1 y = sf2 y)⌝
	THEN1 REPEAT strip_tac);
(* *** Goal "1.1.1" *** *)
a (lemma_tac ⌜SubOrder (Fst f, AtomLhs (Snd f)) (Fst f, Snd f)⌝);
(* *** Goal "1.1.1.1" *** *)
a (rewrite_tac [get_spec ⌜SubOrder⌝]);
a (lemma_tac ⌜ScPrec (AtomLhs (Snd f)) (Snd f)⌝);
(* *** Goal "1.1.1.1.1" *** *)
a (all_fc_tac [scprec_fc_clauses2]);
a (fc_tac [tc_incr_thm]);
(* *** Goal "1.1.1.1.2" *** *)
a (ALL_FC_T (MAP_EVERY (asm_tac o (rewrite_rule []))) [tran_suborder_thm2]);
a (all_asm_fc_tac []);
(* *** Goal "1.1.2" *** *)
a (fc_tac [substterm_lemma1]);
(* *** Goal "1.2" *** *)
a (asm_rewrite_tac[]);
a (lemma_tac ⌜(∀ y⦁ SubOrder y (Fst f, AtomRhs (Snd f)) ⇒ sf1 y = sf2 y)⌝
	THEN1 REPEAT strip_tac);
(* *** Goal "1.2.1" *** *)
a (lemma_tac ⌜SubOrder (Fst f, AtomRhs (Snd f)) (Fst f, Snd f)⌝);
(* *** Goal "1.2.1.1" *** *)
a (rewrite_tac [get_spec ⌜SubOrder⌝]);
a (lemma_tac ⌜ScPrec (AtomRhs (Snd f)) (Snd f)⌝);
(* *** Goal "1.2.1.1.1" *** *)
a (all_fc_tac [scprec_fc_clauses2]);
a (fc_tac [tc_incr_thm]);
(* *** Goal "1.2.1.2" *** *)
a (ALL_FC_T (MAP_EVERY (asm_tac o (rewrite_rule []))) [tran_suborder_thm2]);
a (all_asm_fc_tac []);
(* *** Goal "1.2.2" *** *)
a (fc_tac [substterm_lemma1]);
(* *** Goal "1.2" *** *)
a (asm_rewrite_tac[]);
val substatom_lemma1 = save_pop_thm "substatom_lemma1";
=TEX
}%ignore


ⓈHOLCONST
│ ⦏SubstTf⦎ : ((GS × VA) × GS → GS) → ((GS × VA) × GS → GS)
├───────────
│ SubstTf = λsf ((α, va), f)⦁
│	let ν = TfVars f
│	and fs = TfForms f
│	in (MkTf (ν, (Imagep (λf⦁ sf ((ν +⋎o α, va), f)) fs)))
■

=GFT
⦏substtf_lemma1⦎ =
   ⊢ ∀ sf1 sf2 f
     ⦁ Snd f ∈ Syntax
         ⇒ IsTf (Snd f)
         ⇒ (∀ y⦁ SubOrder y f ⇒ sf1 y = sf2 y)
         ⇒ SubstTf sf1 f = SubstTf sf2 f
=TEX

\ignore{
=SML
set_goal([], ⌜∀sf1 sf2 f⦁ Snd f ∈ Syntax ⇒ IsTf (Snd f) ⇒
	(∀ y⦁ SubOrder y f ⇒ sf1 y = sf2 y)
		⇒ SubstTf sf1 f = SubstTf sf2 f⌝);
a (rewrite_tac [get_spec ⌜SubstTf⌝, let_def] THEN REPEAT strip_tac);
a (lemma_tac ⌜∀g⦁ g ∈⋎g (TfForms (Snd f)) ⇒
	SubOrder ((TfVars (Snd f) +⋎o Fst (Fst f), Snd (Fst f)), g) f⌝
	THEN1 REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜SubOrder⌝]);
a (all_fc_tac [scprec_fc_clauses2]);
a (fc_tac [tc_incr_thm]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜∀g⦁ g ∈⋎g (TfForms (Snd f)) ⇒
	  sf1 ((TfVars (Snd f) +⋎o Fst (Fst f), Snd (Fst f)), g)
	= sf2 ((TfVars (Snd f) +⋎o Fst (Fst f), Snd (Fst f)), g)⌝
	THEN1 (REPEAT strip_tac
		THEN all_asm_fc_tac[]
		THEN all_asm_fc_tac[]));
a (lemma_tac ⌜Imagep (λ f''⦁ sf1 ((TfVars (Snd f) +⋎o Fst (Fst f), Snd (Fst f)), f''))
                       (TfForms (Snd f))
	   = Imagep (λ f''⦁ sf2 ((TfVars (Snd f) +⋎o Fst (Fst f), Snd (Fst f)), f'')) (TfForms (Snd f))⌝
	THEN1 (once_rewrite_tac [gs_ext_axiom]
	       THEN rewrite_tac [get_spec ⌜Imagep⌝]));
(* *** Goal "2.1" *** *)
a (REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[]);
a (asm_fc_tac[]);
(* *** Goal "2.1.2" *** *)
a (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[]);
a (ASM_FC_T rewrite_tac []);
(* *** Goal "2.2" *** *)
a (asm_rewrite_tac[]);
val substtf_lemma1 = save_pop_thm "substtf_lemma1";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏SubstFormFunct⦎ : ((GS × VA) × GS → GS) → ((GS × VA) × GS → GS)
├───────────
│ SubstFormFunct = λsf ((α, va), f)⦁
│    if f ∈ Syntax
│    then if IsEq f ∨ IsMem f
│	  then SubstAtom sf ((α, va), f)
│	  else if IsTf f
│		then SubstTf sf ((α, va), f)
│		else ∅⋎g
│    else ∅⋎g
■

=GFT
⦏substformfunct_lemma1⦎ =
	⊢ SubstFormFunct respects SubOrder
=TEX
\ignore{
=SML
set_goal([], ⌜SubstFormFunct respects SubOrder⌝);
a (rewrite_tac [get_spec ⌜$respects⌝, get_spec ⌜SubstFormFunct⌝]
	THEN REPEAT strip_tac);
a (cases_tac ⌜Snd x ∈ Syntax⌝ THEN asm_rewrite_tac[]);
a (lemma_tac ⌜∀ y⦁ SubOrder y x ⇒ g y = h y⌝
	THEN1 (REPEAT strip_tac
		THEN fc_tac [tc_incr_thm]
		THEN asm_fc_tac[]));
a (cases_tac ⌜IsEq (Snd x) ∨ IsMem (Snd x)⌝ THEN asm_rewrite_tac []);
(* *** Goal "1" *** *)
a (strip_asm_tac (list_∀_elim [⌜g⌝, ⌜h⌝, ⌜x⌝] substatom_lemma1));
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (strip_asm_tac (list_∀_elim [⌜g⌝, ⌜h⌝, ⌜x⌝] substatom_lemma1));
a (asm_fc_tac[]);
(* *** Goal "3" *** *)
a (cases_tac ⌜IsTf (Snd x)⌝ THEN asm_rewrite_tac []);
a (strip_asm_tac (list_∀_elim [⌜g⌝, ⌜h⌝, ⌜x⌝] substtf_lemma1));
a (asm_fc_tac[]);
val substformfunct_lemma1 = save_pop_thm "substformfunct_lemma1";
=TEX
}%ignore


ⓈHOLCONST
│ ⦏SubstForm⦎ : (GS × VA) × GS → GS
├───────────
│ SubstForm = fix SubstFormFunct
■ 

=GFT
⦏substformfunct_fixp_lemma⦎ =
	⊢ SubstForm = SubstFormFunct SubstForm

⦏substformfunct_thm⦎ =
   ⊢ SubstForm
       = (λ ((α, va), f)
       ⦁ if f ∈ Syntax
         then
           if IsEq f ∨ IsMem f
           then SubstAtom SubstForm ((α, va), f)
           else if IsTf f
           then SubstTf SubstForm ((α, va), f)
           else ∅⋎g
         else ∅⋎g)

⦏substformfunct_thm2⦎ =
   ⊢ ∀ x
     ⦁ SubstForm x
         = (if Snd x ∈ Syntax
           then
             if IsEq (Snd x) ∨ IsMem (Snd x)
             then SubstAtom SubstForm x
             else if IsTf (Snd x)
             then SubstTf SubstForm x
             else ∅⋎g
           else ∅⋎g)
=TEX

\ignore{
=SML
set_goal([], ⌜SubstForm = SubstFormFunct SubstForm⌝);
a (asm_tac well_founded_SubOrder_thm);
a (asm_tac substformfunct_lemma1);
a (fc_tac [∀_elim ⌜SubOrder⌝ (∀_elim ⌜SubstFormFunct⌝ (get_spec ⌜fix⌝))]);
a (rewrite_tac [get_spec ⌜SubstForm⌝]);
a (asm_rewrite_tac[]);
val substformfunct_fixp_lemma = save_pop_thm "substformfunct_fixp_lemma";

val substformfunct_thm = save_thm ("substformfunct_thm",
	rewrite_rule [get_spec ⌜SubstFormFunct⌝] substformfunct_fixp_lemma);

val substformfunct_thm2 = save_thm ("substformfunct_thm2",
	rewrite_rule [ext_thm] substformfunct_thm);
=TEX
}%ignore

\subsection{Evaluation}

Now we define the evaluation of formulae.
The definition assumes that partial relations for the atomic formulae are available, and is the main part of the definition of a functor which transforms membership and equality relations.
Interpretations of non-well-founded set theories are then sought as fixed points of this functor over subsets of the infinitary comprehensions.

Partial relations are represented by curried functions with values of type ⓣBOOL + ONE⌝, a type abbreviated as ⓣTV⌝.
To improve readability of the specification the three truth values are give names as follows:


ⓈHOLCONST
│ ⦏pTrue⦎ : TV
├───────────
│ pTrue = InL T
■
ⓈHOLCONST
│ ⦏pFalse⦎ : TV
├───────────
│ pFalse = InL F
■
ⓈHOLCONST
│ ⦏pU⦎ : TV
├───────────
│ pU = InR One
■

=GFT
⦏tv_cases_thm⦎ =
	⊢ ∀ x⦁ x = pTrue ∨ x = pFalse ∨ x = pU

⦏tv_distinct_clauses⦎ =
	⊢ ¬ pTrue = pFalse
             ∧ ¬ pTrue = pU
             ∧ ¬ pFalse = pTrue
             ∧ ¬ pFalse = pU
             ∧ ¬ pU = pTrue
             ∧ ¬ pU = pFalse
=TEX

\ignore{
=SML
set_goal([], ⌜∀x⦁ x = pTrue ∨ x = pFalse ∨ x = pU⌝);
a (rewrite_tac (map get_spec [⌜pTrue⌝, ⌜pFalse⌝, ⌜pU⌝]) THEN prove_tac[]);
a (strip_asm_tac (∀_elim ⌜x⌝ sum_cases_thm));
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac);
a (LEMMA_T ⌜y = T ∨ y = F⌝ (STRIP_THM_THEN asm_tac) THEN1 prove_tac[]
	THEN var_elim_nth_asm_tac 1
	THEN strip_tac);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[one_def]);
val tv_cases_thm = save_pop_thm "tv_cases_thm";

set_goal([], ⌜¬ pTrue = pFalse
	∧ ¬ pTrue = pU
	∧ ¬ pFalse = pTrue
	∧ ¬ pFalse = pU
	∧ ¬ pU = pTrue
	∧ ¬ pU = pFalse
⌝);
a (rewrite_tac (map get_spec [⌜pTrue⌝, ⌜pFalse⌝, ⌜pU⌝]) THEN prove_tac[]);
val tv_distinct_clauses = save_pop_thm "tv_distinct_clauses";

add_pc_thms "'ICsem" (map get_spec [] @ [tv_distinct_clauses]);
set_merge_pcs ["ICsyn", "'ICsem"];

=TEX
}%ignore

=SML
declare_infix (300, "⦏∈⋎v⦎");
declare_infix (300, "⦏=⋎v⦎");
=TEX

Now we begin the specification of evaluation with the evaluation of atomic formulae.

ⓈHOLCONST
│ ⦏EvalAtom⦎ : PR → (VA × GS) → TV
├───────────
│ ∀($∈⋎v:R) ($=⋎v:R)⦁ EvalAtom ($∈⋎v, $=⋎v) = (λ(va, f)⦁ 
│	(if IsEq f then $=⋎v else $∈⋎v) 
│		  (SubstTerm SubstForm ((∅⋎g, va), (AtomLhs f)))
│		  (SubstTerm SubstForm ((∅⋎g, va), (AtomRhs f))))
■

It is helpful for the subsequent proofs to structure the specification of {\it EvalTf}, pulling out the following definition, which shows the set of truth values arising from the quantification occuring in this construct.

ⓈHOLCONST
│ ⦏EvalTf_results⦎ : GS SET → ((VA × GS) → TV) → (VA × GS) → (TV) SET
├───────────
│ ∀V⦁ EvalTf_results V = λef (va, f)⦁ 
│	 let ν = TfVars f
│	 and fs = TfForms f
│	 in {pb |
│		∃v f⦁ VaRan (ν, v) ⊆ V
│		∧ f ∈⋎g fs
│		∧ pb = ef (InsertVars (ν, v) va, f)}
■

ⓈHOLCONST
│ ⦏EvalTf_tf⦎ : TV SET → TV
├───────────
│ ∀results⦁ EvalTf_tf results = 
│	if results ⊆ {pTrue} then pFalse
│		else if (pFalse) ∈ results then pTrue
│		else pU
■

ⓈHOLCONST
│ ⦏EvalTf⦎ : (GS SET × R × R) → ((VA × GS) → TV) → (VA × GS) → TV
├───────────
│ ∀V ($∈⋎v:R) ($=⋎v:R)⦁ EvalTf (V, $∈⋎v, $=⋎v) = λef (va, f)⦁ 
│	 EvalTf_tf (EvalTf_results V ef (va, f))
■

ⓈHOLCONST
│ ⦏SubOrder2⦎ : (VA × GS) → (VA × GS) → BOOL
├───────────
│ SubOrder2 = λs t⦁ tc ScPrec (Snd s) (Snd t)
■

=GFT
⦏tran_suborder2_thm⦎ =
   ⊢ trans SubOrder2

⦏tran_suborder2_thm2⦎ =
	⊢ ∀ s t u⦁ SubOrder2 s t ∧ SubOrder2 t u ⇒ SubOrder2 s u

⦏well_founded_SubOrder2_thm⦎ =
   ⊢ well_founded SubOrder2

=TEX

\ignore{
=SML
set_goal([], ⌜trans SubOrder2⌝);
a (rewrite_tac [get_spec ⌜SubOrder2⌝, get_spec ⌜trans⌝]
	THEN REPEAT strip_tac);
a (all_fc_tac [tran_tc_thm2]);
val tran_suborder2_thm = save_pop_thm "tran_suborder2_thm";

val tran_suborder2_thm2 = save_thm ("tran_suborder2_thm2", rewrite_rule [get_spec ⌜trans⌝] tran_suborder2_thm);

set_goal([], ⌜well_founded SubOrder2⌝);
a (rewrite_tac [get_spec ⌜SubOrder2⌝]);
a (asm_tac (∀_elim ⌜Snd: (GS × (GS → GS)) × GS → GS⌝
(⇒_elim (∀_elim ⌜tc ScPrec⌝ wf_image_wf_thm) well_founded_tcScPrec_thm)));
a (strip_tac);
val well_founded_SubOrder2_thm = save_pop_thm "well_founded_SubOrder2_thm";
=TEX
}%ignore

=GFT
evaltf_lemma1 =
   ⊢ ∀ (v, m, e) ef1 ef2 vaf
     ⦁ Snd vaf ∈ Syntax
         ⇒ IsTf (Snd vaf)
         ⇒ (∀ y⦁ SubOrder2 y vaf ⇒ ef1 y = ef2 y)
         ⇒ EvalTf (v, m, e) ef1 vaf = EvalTf (v, m, e) ef2 vaf
=TEX

\ignore{
=SML
set_goal([], ⌜∀(v, m, e) ef1 ef2 vaf⦁ Snd vaf ∈ Syntax
	⇒ IsTf (Snd vaf)
	⇒ (∀ y⦁ SubOrder2 y vaf ⇒ ef1 y = ef2 y)
	⇒ EvalTf (v, m, e) ef1 vaf = EvalTf (v, m, e) ef2 vaf
⌝);
a (REPEAT strip_tac);
a (rewrite_tac [get_spec ⌜EvalTf⌝]);
a (LEMMA_T ⌜EvalTf_results v ef1 vaf
	= EvalTf_results v ef2 vaf⌝ rewrite_thm_tac);
a (rewrite_tac [get_spec ⌜EvalTf_results⌝, sets_ext_clauses, let_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜v'⌝ THEN ∃_tac ⌜f'⌝ THEN asm_rewrite_tac[]);
a (spec_nth_asm_tac 4 ⌜(InsertVars (TfVars (Snd vaf), v') (Fst vaf), f')⌝);
a (swap_nth_asm_concl_tac 1 THEN DROP_NTH_ASM_T 1 discard_tac);
a (rewrite_tac [get_spec ⌜SubOrder2⌝]);
a (lemma_tac ⌜ScPrec f' (Snd vaf)⌝);
(* *** Goal "1.1" *** *)
a (all_fc_tac [scprec_fc_clauses2]);
(* *** Goal "1.2" *** *)
a (fc_tac [tc_incr_thm]);
(* *** Goal "2" *** *)
a (∃_tac ⌜v'⌝ THEN ∃_tac ⌜f'⌝ THEN asm_rewrite_tac[]);
a (spec_nth_asm_tac 4 ⌜(InsertVars (TfVars (Snd vaf), v') (Fst vaf), f')⌝
	THEN_TRY asm_rewrite_tac[]);
a (swap_nth_asm_concl_tac 1 THEN DROP_NTH_ASM_T 1 discard_tac);
a (rewrite_tac [get_spec ⌜SubOrder2⌝]);
a (lemma_tac ⌜ScPrec f' (Snd vaf)⌝);
(* *** Goal "2.1" *** *)
a (all_fc_tac [scprec_fc_clauses2]);
(* *** Goal "2.2" *** *)
a (fc_tac [tc_incr_thm]);
val evaltf_lemma1 = save_pop_thm "evaltf_lemma1";

set_goal([], ⌜∀(v, m, e) ef1 ef2 vaf⦁ Snd vaf ∈ Syntax
	⇒ IsTf (Snd vaf)
	⇒ (∀ y⦁ SubOrder2 y vaf ⇒ ef1 y = ef2 y)
	⇒ EvalTf (v, m, e) ef1 vaf = EvalTf (v, m, e) ef2 vaf⌝);

=TEX
}%ignore

ⓈHOLCONST
│ ⦏EvalFormFunct⦎ : (GS SET × R × R) → (VA × GS → TV)	
│			→ (VA × GS → TV)
├───────────
│ ∀V ($∈⋎v:R) ($=⋎v:R)⦁ EvalFormFunct (V, $∈⋎v, $=⋎v) = (λef (va, f)⦁ 
│	if f ∈ WfForms
│	then
│		if IsEq f ∨ IsMem f
│		then EvalAtom ($∈⋎v, $=⋎v) (va, f)
│		else EvalTf (V, $∈⋎v, $=⋎v) ef (va, f)
│	else pU)
■

=GFT

=TEX

\ignore{
=SML
set_goal([], ⌜∀(V, $∈⋎v, $=⋎v)⦁ (EvalFormFunct (V, $∈⋎v, $=⋎v)) respects SubOrder2⌝);
a (rewrite_tac [get_spec ⌜EvalFormFunct⌝, get_spec ⌜$respects⌝]);
a (REPEAT strip_tac);
a (cases_tac ⌜Snd x ∈ WfForms⌝ THEN asm_rewrite_tac[]);
a (fc_tac [ft_syntax_thm]);
a (fc_tac [formula_cases_thm] THEN_TRY asm_rewrite_tac[]);
a (cases_tac ⌜IsEq (Snd x) ∨ IsMem (Snd x)⌝ THEN asm_rewrite_tac[]);
a (fc_tac [evaltf_lemma1]);
a (asm_fc_tac[]);
a (list_spec_nth_asm_tac 1 [⌜g⌝, ⌜h⌝, ⌜V⌝, ⌜$∈⋎v⌝, ⌜$=⋎v⌝]);
a (swap_nth_asm_concl_tac 1 THEN POP_ASM_T discard_tac
	THEN POP_ASM_T ante_tac);
a (DROP_NTH_ASM_T 8 ante_tac THEN rewrite_tac [get_spec ⌜SubOrder2⌝]);
a (REPEAT strip_tac);
a (lemma_tac ⌜trans (λ (s : (GS × (GS → GS)) × GS) t⦁ tc ScPrec (Snd s) (Snd t))⌝
	THEN1 rewrite_tac [get_spec ⌜trans⌝, tran_tc_thm2]);
a (fc_tac [tran_tc_id_thm]);
a (SPEC_NTH_ASM_T 4 ⌜y⌝ ante_tac);
a (GET_NTH_ASM_T 1 rewrite_thm_tac);
a (strip_tac THEN asm_fc_tac[]);
val evalformfunct_lemma1 = save_pop_thm "evalformfunct_lemma1";
=TEX
}%ignore


ⓈHOLCONST
│ ⦏EvalForm⦎ : (GS SET × R × R) → VA × GS → TV
├───────────
│ ∀V ($∈⋎v:R) ($=⋎v:R)⦁ EvalForm (V, $∈⋎v, $=⋎v) = fix (EvalFormFunct (V, $∈⋎v, $=⋎v))
■

=GFT
⦏evalformfunct_fixp_lemma⦎ =
   ⊢ ∀ (V, $∈⋎v, $=⋎v)
     ⦁ EvalForm (V, $∈⋎v, $=⋎v)
         = EvalFormFunct (V, $∈⋎v, $=⋎v) (EvalForm (V, $∈⋎v, $=⋎v))

⦏evalformfunct_thm⦎ =
   ⊢ ∀ (V, $∈⋎v, $=⋎v)
     ⦁ EvalForm (V, $∈⋎v, $=⋎v)
         = (λ (va, f)
         ⦁ if f ∈ WfForms
           then
             if IsEq f ∨ IsMem f
             then EvalAtom ($∈⋎v, $=⋎v) (va, f)
             else EvalTf (V, $∈⋎v, $=⋎v) (EvalForm (V, $∈⋎v, $=⋎v)) (va, f)
           else pU)

⦏evalformfunct_thm2⦎ =
   ⊢ ∀ (V, $∈⋎v, $=⋎v) x
     ⦁ EvalForm (V, $∈⋎v, $=⋎v) x
         = (if Snd x ∈ WfForms
           then
             if IsEq (Snd x) ∨ IsMem (Snd x)
             then EvalAtom ($∈⋎v, $=⋎v) x
             else EvalTf (V, $∈⋎v, $=⋎v) (EvalForm (V, $∈⋎v, $=⋎v)) x
           else pU)
=TEX

\ignore{
=SML
set_flag ("pp_show_HOL_types", false);

set_goal([], ⌜∀(V, $∈⋎v, $=⋎v)⦁ EvalForm (V, $∈⋎v, $=⋎v)
	= (EvalFormFunct(V, $∈⋎v, $=⋎v)) (EvalForm(V, $∈⋎v, $=⋎v))⌝);
a (asm_tac well_founded_SubOrder2_thm);
a (asm_tac evalformfunct_lemma1);
a (fc_tac [∀_elim ⌜SubOrder2⌝ (∀_elim ⌜EvalFormFunct(V, $∈⋎v, $=⋎v)⌝ (get_spec ⌜fix⌝))]);
a (rewrite_tac [get_spec ⌜EvalForm⌝]);
a (REPEAT ∀_tac);
a (list_spec_nth_asm_tac 2 [⌜(V, $∈⋎v, $=⋎v)⌝]);
a (asm_fc_tac[]);
a (asm_rewrite_tac[]);
val evalformfunct_fixp_lemma = save_pop_thm "evalformfunct_fixp_lemma";

val evalformfunct_thm = save_thm ("evalformfunct_thm",
	rewrite_rule [get_spec ⌜EvalFormFunct⌝] evalformfunct_fixp_lemma);

val evalformfunct_thm2 = save_thm ("evalformfunct_thm2",
	rewrite_rule [ext_thm] evalformfunct_thm);
=TEX
}%ignore

\newpage

\subsection{Membership and Equality}

Note that in the evaluation of formulae above {\it EvalForm} atomic membership and equality relations are evaluated by reference to given membership and equality relationships.

We are seeking a functor which when supplied with membership and equality relations will deliver new relationships at least as detailed as the original (they are partial relationships).
This is what we now define.

ⓈHOLCONST
│ ⦏MemRel⦎ : (GS SET × R × R) → R
├───────────
│ ∀V ($∈⋎v:R) ($=⋎v:R)⦁ 
│	MemRel (V, $∈⋎v, $=⋎v) = λe s⦁
│		let va = (Nat⋎g 1, λv⦁ e)
│		in EvalForm (V, $∈⋎v, $=⋎v) (va, (snd s))
■

The equality of two closed comprehensions is determined here by evaluating the formula in which the bodies of the two comprehensions are first combined into an equivalence and then universally quantified over the common variable.

ⓈHOLCONST
│ ⦏EqRel⦎ : (GS SET × R × R) → R
├───────────
│ ∀V ($∈⋎v:R) ($=⋎v:R)⦁ EqRel (V, $∈⋎v, $=⋎v) = λl r⦁
│	if l ∈ V ∧ r ∈ V
│	then
│		if ∃c⦁ c ∈ V ∧ ((c ∈⋎v l) = pU ∨ (c ∈⋎v r) = pU)
│		then pU
│		else if ((λc⦁ c ∈ V ∧ ¬ (c ∈⋎v l) = pU) = (λc⦁ c ∈ V ∧ ¬ (c ∈⋎v r) = pU))
			then pTrue else pFalse
│	else pU	
■

The semantics of equality and membership are to be combined into a parameterised functor of which we seek fixed points.
These fixed points yield interpretations of non-well-founded set theories (or as a special and easy test case an image of our well-founded set theory).

\subsection{The Semantic Functor}

The required functor is a monotonic functor over equality and membership relation pairs, parameterised by the domain of discourse V.

ⓈHOLCONST
│ ⦏SemanticFunctor⦎ : GS SET → PR → PR
├───────────
│ ∀V ($∈⋎v:R) ($=⋎v:R)⦁ 
│	SemanticFunctor V = λ($∈⋎v, $=⋎v)⦁ (MemRel (V, $∈⋎v, $=⋎v), EqRel (V, $∈⋎v, $=⋎v))
■

Minor variations on this are possible, such as obtaining the equality relation from the new rather than the old membership relation, or even iterating the construction of the equality to an extensional fixed point in each application of the semantic functor.
However, these devices are unlikely to affect the fixed points and their effect on the complexity of proofs might as well be negative as positive.

\section{THE EXISTENCE OF FIXED POINTS}

When I began working with infinitary comprehension the idea was to use it for interpretations of the usual first order language of set theory.
This was to have been realised by identifying large subsets V of {\it WfComp} for which there exists a fixed point of the functor {\it SemanticFunctor V} in which the equality and membership relations are total over V.
It is easy to believe that there are such subsets which include copies of the well-founded sets we started out with, and also, for example, all the PolySets and many other useful non-well-founded sets.

Before reaching the stage at which reasoning about such fixed points could be undertaken it occurred to me that for my intended application, the classical set theories might well be dispensed with, possibly resulting in significant savings.

The intended application was to languages suitable for the formal computer assisted development of mathematics and its applications, and the next stage in the construction of such languages was to be an illative lambda calculus.
An illative lambda calculus must be effectively a many valued logic, for there is no type system or other means which prevents the consideration of arbitrary lambda terms as propositions.
For application in this context, the effort of coming up with a two-valued membership relation may not be beneficial.
There must still be a system of type assignment which allows the user to work with subdomains better behaved than the whole ontology, and if this works as well as it needs to work, then the presence of sets which are not really sets in the classical sense will not be problematic, and effort directed toward their elimination may prove not to be beneficial.

I therefore propose at least initially to explore the option of going straight from partial fixed points (meaning in this case, fixed points, over the whole of {\it WfComp}, which are partial membership and equality relations) to an illative lambda calculus whose domain of discourse is a partition of the whole of {\it WfComp}.

At this stage it is not clear whether any old fixed point will do or whether we have to be more fussy than that, so I will start with an arbitrary fixed point and see how far I get.
To do this I do have to prove that there does exist a fixed point, and this is to be realised by demonstrating that the semantic functor is monotone and therefore has a least fixed point.

\subsection{Monotonicity}

To establish the existence of fixed points it is helpful to show that the semantic functor is monotonic.

It is therefore necessary to define the ordering relative to which it is monotonic.

=SML
declare_infix(300, "≤⋎t");
declare_infix(300, "≤⋎t⋎s");
declare_infix(300, "≤⋎r");
declare_infix(300, "≤⋎p⋎r");
=TEX

First an ordering on the ``truth values'' is defined.

ⓈHOLCONST
│ ⦏$≤⋎t⦎ : (TV) → (TV) → BOOL
├───────────
│ ∀ t1 t2⦁ 
│	t1 ≤⋎t t2 ⇔ t1 = t2 ∨ t1 = pU	
■

=GFT
⦏≤⋎t_refl_thm⦎ =
	⊢ ∀ x⦁ x ≤⋎t x

⦏≤⋎t_trans_thm⦎ =
	⊢ ∀ x y z⦁ x ≤⋎t y ∧ y ≤⋎t z ⇒ x ≤⋎t z

⦏≤⋎t_clauses⦎ =
   ⊢ pU ≤⋎t pTrue
       ∧ pU ≤⋎t pFalse
       ∧ ¬ pTrue ≤⋎t pU
       ∧ ¬ pFalse ≤⋎t pU
       ∧ ¬ pFalse ≤⋎t pTrue
       ∧ ¬ pTrue ≤⋎t pFalse
=TEX

\ignore{
=SML
set_goal([], ⌜∀x⦁ x ≤⋎t x⌝);
a (rewrite_tac [get_spec ⌜$≤⋎t⌝]);
val ≤⋎t_refl_thm = save_pop_thm "≤⋎t_refl_thm";

set_goal([], ⌜∀x y z⦁ x ≤⋎t y ∧ y ≤⋎t z ⇒ x ≤⋎t z⌝);
a (rewrite_tac [get_spec ⌜$≤⋎t⌝]
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
a (all_var_elim_asm_tac);
val ≤⋎t_trans_thm = save_pop_thm "≤⋎t_trans_thm";

set_goal([], ⌜(∀x⦁ pU ≤⋎t x)
	∧ ¬ pTrue ≤⋎t pU
	∧ ¬ pFalse ≤⋎t pU
	∧ ¬ pFalse ≤⋎t pTrue
	∧ ¬ pTrue ≤⋎t pFalse⌝);
a (rewrite_tac [get_spec ⌜$≤⋎t⌝] THEN prove_tac[]);
val ≤⋎t_clauses = save_pop_thm "≤⋎t_clauses";

add_pc_thms "'ICsem" (map get_spec [] @ [≤⋎t_refl_thm, ≤⋎t_clauses]);
set_merge_pcs ["ICsyn", "'ICsem"];
=TEX
}%ignore

Then an ordering on partial relations over term values.

ⓈHOLCONST
│ ⦏$≤⋎r⦎ : R → R → BOOL
├───────────
│ ∀ r1 r2⦁ 
│	r1 ≤⋎r r2 ⇔ ∀x y⦁ (r1 x y) ≤⋎t (r2 x y)	
■

and an ordering over pairs of partial relations (membership and equality partial relations).

ⓈHOLCONST
│ ⦏$≤⋎p⋎r⦎ : PR → PR → BOOL
├───────────
│ ∀ r12 s12⦁ 
│	r12 ≤⋎p⋎r s12 ⇔ (Fst r12) ≤⋎r (Fst s12) ∧ (Snd r12) ≤⋎r (Snd s12)	
■

Our aim is to prove the monotonicity of the semantic functor for every domain which is a subset of the well formed comprehensions.
The relevant notion of monotonicity is defined here.

ⓈHOLCONST
│ ⦏MonoFunct⦎ : (PR → PR) → BOOL
├───────────
│ ∀ f⦁  MonoFunct f ⇔ ∀v w x y⦁ (v,w) ≤⋎p⋎r (x,y) ⇒ (f (v,w)) ≤⋎p⋎r (f (x,y))
■

In order to prove monotonicity of the semantic functor various lemmas about the functions used in defining the semantic functor are needed, often expressing monotonicity of objects of various types.

\subsubsection{EvalAtom}

The required characteristic of {\\it EvalAtom} is straightforward to define and prove.

The following is the property of partial truth predicates parameterised by pairs of partial relations of being monotonic with respect to those relations.

ⓈHOLCONST
│ ⦏MonoPprF⦎ : (PR → 'a → TV) → BOOL
├───────────
│ ∀f⦁ MonoPprF f ⇔ ∀ v w x y⦁
│	(v, w) ≤⋎p⋎r (x, y) ⇒ ∀z:'a⦁ f (v, w) z ≤⋎t f (x, y) z
■

=GFT
⦏evalatom_monotone_lemma⦎ =
   ⊢ ∀ v w x y
     ⦁ $≤⋎p⋎r (v, w) (x, y) ⇒ (∀ z⦁ EvalAtom (v, w) z ≤⋎t EvalAtom (x, y) z)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ v w x y
           ⦁ $≤⋎p⋎r (v, w) (x, y)
               ⇒ (∀ z⦁ EvalAtom (v, w) z ≤⋎t EvalAtom (x, y) z)⌝);
a (rewrite_tac (map get_spec [⌜MonoPprF⌝, ⌜EvalAtom⌝,
	⌜$≤⋎r⌝, ⌜$≤⋎p⋎r⌝])
	THEN REPEAT strip_tac);
a (cases_tac ⌜IsEq (Snd z)⌝
	THEN asm_rewrite_tac []);
val evalatom_monotone_lemma = save_pop_thm "evalatom_monotone_lemma";
=TEX
}%ignore

\subsubsection{Monotonicity of Membership and Equality}

The following are lemmas specific to the definitions of {\it EqRel} and {\it MemRel}.

=GFT
⦏eqrel_mono_thm⦎ =
   ⊢ ∀ V v w x y
     ⦁ $≤⋎p⋎r (x, y) (v, w) ⇒ $≤⋎r (EqRel (V, x, y)) (EqRel (V, v, w))

⦏monpprf_memrel_lemma1⦎ =
   ⊢ ∀ V
     ⦁ MonoPprF (λ (m, e)⦁ EvalForm (V, m, e))
         ⇒ MonoPprF (λ (m, e) (l, r)⦁ MemRel (V, m, e) l r)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀V⦁ ∀v w x y⦁ $≤⋎p⋎r (x,y) (v,w) ⇒ $≤⋎r (EqRel (V,x,y)) (EqRel (V,v,w))⌝);
a (rewrite_tac (map get_spec [⌜EqRel⌝, ⌜$≤⋎r⌝])
	THEN REPEAT strip_tac);
a (cases_tac ⌜x' ∈ V ∧ y' ∈ V⌝ THEN asm_rewrite_tac[get_spec ⌜$≤⋎t⌝]);
a (fc_tac [get_spec ⌜$≤⋎p⋎r⌝]);
a (FC_T (MAP_EVERY (asm_tac o (rewrite_rule[]))) [get_spec ⌜$≤⋎r⌝]);
a (CASES_T ⌜∃ c⦁ c ∈ V ∧ (x c x' = pU ∨ x c y' = pU)⌝ asm_tac
	THEN_TRY asm_rewrite_tac[]);
a (CASES_T ⌜∃ c⦁ c ∈ V ∧ (v c x' = pU ∨ v c y' = pU)⌝ asm_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac THEN POP_ASM_T ante_tac
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (spec_nth_asm_tac 3 ⌜c⌝);
a (list_spec_nth_asm_tac 6 [⌜c⌝, ⌜x'⌝]);
a (fc_tac [get_spec ⌜$≤⋎t⌝]);
a (DROP_NTH_ASM_T 4 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (spec_nth_asm_tac 3 ⌜c⌝);
a (list_spec_nth_asm_tac 6 [⌜c⌝, ⌜y'⌝]);
a (fc_tac [get_spec ⌜$≤⋎t⌝]);
a (DROP_NTH_ASM_T 3 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (DROP_NTH_ASM_T 1 ante_tac THEN strip_tac);
a (DROP_NTH_ASM_T 2 ante_tac THEN strip_tac);
a (LEMMA_T ⌜¬ (if (λ c⦁ c ∈ V ∧ ¬ x c x' = pU) = (λ c⦁ c ∈ V ∧ ¬ x c y' = pU)
                 then pTrue
                 else pFalse)
               = pU⌝ rewrite_thm_tac
	THEN1 (cases_tac ⌜(λ c⦁ c ∈ V ∧ ¬ x c x' = pU) = (λ c⦁ c ∈ V ∧ ¬ x c y' = pU)⌝
		THEN asm_rewrite_tac[]));
a (LEMMA_T ⌜(λ c⦁ c ∈ V ∧ ¬ x c x' = pU) = (λ c⦁ c ∈ V ∧ ¬ x c y' = pU)
	⇔ (λ c⦁ c ∈ V ∧ ¬ v c x' = pU) = (λ c⦁ c ∈ V ∧ ¬ v c y' = pU)⌝
	rewrite_thm_tac);
a (rewrite_tac [ext_thm]
	THEN contr_tac
	THEN asm_fc_tac[]);
val eqrel_mono_thm = save_pop_thm "eqrel_mono_thm";

set_goal ([], ⌜∀ V⦁ MonoPprF(λ(m, e)⦁ EvalForm (V,m,e))
			⇒ MonoPprF (λ(m, e) (l,r)⦁ MemRel (V, m, e) l r)⌝);
a (rewrite_tac [get_spec ⌜MonoPprF⌝, get_spec ⌜MemRel⌝, let_def]
	THEN REPEAT strip_tac);
a (asm_fc_tac[]);
a (asm_rewrite_tac[]);
val monpprf_memrel_lemma1 = save_pop_thm "monpprf_memrel_lemma1";
=TEX
}%ignore

\subsubsection{Monotonicity of EvalTf}

This result is more difficult.
Because {\it EvalTf} participates in the recursion over the syntactic structure of comprehensions which is used to define evaluation of formulae, it is supplied with an evaluation function on whose behaviour its monotonicity depends.

The definition of {\it EvalTf} has been split into three parts to break up the proof.
The first part obtains a set of ``truth values'' (true, false or unknown) and we here define an ordering over these sets. 

ⓈHOLCONST
│ ⦏$≤⋎t⋎s⦎ : (TV SET) → (TV SET) → BOOL
├───────────
│ ∀ m n⦁ 
│	m ≤⋎t⋎s n ⇔
│		(∀x⦁ x ∈ m ⇒ ∃y⦁ y ∈ n ∧ x ≤⋎t y)
│	∧	(∀y⦁ y ∈ n ⇒ ∃x⦁ x ∈ m ∧ x ≤⋎t y)
■

=GFT
⦏≤t⋎t⋎s_clauses⦎ =
   ⊢ ∀ s t
     ⦁ $≤⋎t⋎s s t
         ⇒ pTrue ∈ s
         ⇒ pTrue ∈ t ∧ pFalse ∈ s
         ⇒ pFalse ∈ t ∧ pU ∈ t
         ⇒ pU ∈ s ∧ (s = {} ⇔ t = {})

⦏mono_evaltf_≤⋎t⋎s_lemma1⦎ =
   ⊢ ∀ s t⦁ $≤⋎t⋎s s t ⇒ s ⊆ {pTrue} ⇒ s ⊆ {pTrue}

⦏mono_evaltftf_lemma⦎ =
   ⊢ ∀ res1 res2⦁ $≤⋎t⋎s res1 res2 ⇒ EvalTf_tf res1 ≤⋎t EvalTf_tf res2
=TEX

\ignore{
=SML
set_goal([], ⌜∀rs⦁ $≤⋎t⋎s rs rs⌝);
a (rewrite_tac [get_spec ⌜$≤⋎t⋎s⌝]
	THEN REPEAT strip_tac);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
val ≤⋎t⋎s_refl_thm = save_pop_thm "≤⋎t⋎s_refl_thm";

add_pc_thms "'ICsem" (map get_spec [] @ [≤⋎t⋎s_refl_thm]);
set_merge_pcs ["ICsyn", "'ICsem"];

set_goal([], ⌜∀s t⦁ $≤⋎t⋎s s t ⇒
		(pTrue ∈ s ⇒ pTrue ∈ t)
	∧ 	(pFalse ∈ s ⇒ pFalse ∈ t)
	∧ 	(pU ∈ t ⇒ pU ∈ s)
	∧	(s = {} ⇔ t = {})⌝);
a (rewrite_tac [get_spec ⌜$≤⋎t⋎s⌝]
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 3 ⌜pTrue⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜$≤⋎t⌝]);
a (STRIP_T rewrite_thm_tac THEN strip_tac);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 3 ⌜pFalse⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜$≤⋎t⌝]);
a (STRIP_T rewrite_thm_tac THEN strip_tac);
(* *** Goal "3" *** *)
a (spec_nth_asm_tac 2 ⌜pU⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜$≤⋎t⌝]);
a strip_tac;
a (var_elim_nth_asm_tac 1);
(* *** Goal "4" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac [sets_ext_clauses]
	THEN contr_tac);
a (spec_nth_asm_tac 3 ⌜x⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜$≤⋎t⌝]);
a (spec_nth_asm_tac 3 ⌜x'⌝);
(* *** Goal "5" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac [sets_ext_clauses]
	THEN contr_tac);
a (REPEAT (asm_fc_tac[]));
val ≤⋎t⋎s_fc_clauses = save_pop_thm "≤⋎t⋎s_fc_clauses";

set_goal([], ⌜∀s t⦁ $≤⋎t⋎s s t ⇒
		(s ⊆ {pTrue} ⇒ t ⊆ {pTrue})⌝);
a (REPEAT strip_tac);
a (cases_tac ⌜s = {}⌝);
(* *** Goal "1" *** *)
a (all_fc_tac [≤⋎t⋎s_fc_clauses]);
a (asm_rewrite_tac []);
(* *** Goal "2" *** *)
a (lemma_tac ⌜¬ t = {}⌝ THEN1 FC_T1 fc_⇔_canon (MAP_EVERY asm_tac) [≤⋎t⋎s_fc_clauses]);
a (GET_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[]);
a (fc_tac [get_spec ⌜$≤⋎t⋎s⌝]);
a (rewrite_tac [sets_ext_clauses]);
a (contr_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ tv_cases_thm));
(* *** Goal "2.2.1" *** *)
a (swap_nth_asm_concl_tac 3 THEN asm_rewrite_tac[] THEN contr_tac);
a (spec_nth_asm_tac 5 ⌜pFalse⌝);
a (GET_NTH_ASM_T 10 ante_tac THEN rewrite_tac [sets_ext_clauses]
	THEN contr_tac);
a (spec_nth_asm_tac 1 ⌜x'⌝);
a (swap_nth_asm_concl_tac 3 THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a (swap_nth_asm_concl_tac 3 THEN asm_rewrite_tac[] THEN contr_tac);
a (spec_nth_asm_tac 5 ⌜pU⌝);
a (GET_NTH_ASM_T 10 ante_tac THEN rewrite_tac [sets_ext_clauses]
	THEN contr_tac);
a (spec_nth_asm_tac 1 ⌜x'⌝);
a (swap_nth_asm_concl_tac 3 THEN asm_rewrite_tac[]);
val mono_evaltf_≤⋎t⋎s_lemma1 = save_pop_thm "mono_evaltf_≤⋎t⋎s_lemma1";

set_goal([], ⌜∀res1 res2⦁ $≤⋎t⋎s res1 res2
	⇒ EvalTf_tf res1 ≤⋎t EvalTf_tf res2⌝);
a (rewrite_tac [get_spec ⌜EvalTf_tf⌝]
	THEN REPEAT strip_tac);
a (cases_tac ⌜res1 ⊆ {pTrue}⌝ THEN asm_rewrite_tac[]);
(* a (strip_asm_tac (list_∀_elim [⌜res1⌝, ⌜res2⌝] mono_evaltf_≤⋎t⋎s_lemma1)
	THEN asm_rewrite_tac[]); *)
(* *** Goal "1" *** *)
a (all_asm_fc_tac [mono_evaltf_≤⋎t⋎s_lemma1]
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜pFalse ∈ res1 ⇒ pFalse ∈ res2⌝
	THEN1 (strip_tac THEN all_fc_tac [≤⋎t⋎s_fc_clauses])
	THEN asm_rewrite_tac[]);
a (lemma_tac ⌜¬ res2 ⊆ {pTrue}⌝
	THEN1 (rewrite_tac [sets_ext_clauses]
		THEN REPEAT strip_tac
		THEN ∃_tac ⌜pFalse⌝
		THEN asm_rewrite_tac[])
	THEN asm_rewrite_tac[]);
a (cases_tac ⌜pFalse ∈ res1⌝ THEN asm_rewrite_tac[]);
val mono_evaltftf_lemma = save_pop_thm "mono_evaltftf_lemma";

set_goal([], ⌜∀ V⦁ MonoPprF(λ(m, e)⦁ EvalForm (V,m,e))⌝);
a (rewrite_tac [get_spec ⌜MonoPprF⌝]
	THEN REPEAT_N 6 strip_tac);
a (lemma_tac ⌜∀g va⦁ EvalForm (V, v, w) (va, g) ≤⋎t EvalForm (V, x, y)  (va, g)⌝
	THEN1 strip_tac);
(* *** Goal "1" *** *)
a (sc_induction_tac ⌜g⌝);
a (strip_tac THEN rewrite_tac [evalformfunct_thm2]
	THEN REPEAT strip_tac);
a (cases_tac ⌜t ∈ WfForms⌝ THEN asm_rewrite_tac[]);
a (cases_tac ⌜IsEq t ∨ IsMem t⌝
	THEN asm_rewrite_tac[]
	THEN fc_tac [evalatom_monotone_lemma]
	THEN_TRY asm_rewrite_tac[]);
a (fc_tac [formula_cases_thm]);
a (rewrite_tac [get_spec ⌜EvalTf⌝, let_def]);
a (LEMMA_T ⌜∃res1 res2⦁ res1 = EvalTf_results V (EvalForm (V, v, w)) (va, t)
	∧ res2 = EvalTf_results V (EvalForm (V, x, y)) (va, t)⌝
	(REPEAT_TTCL STRIP_THM_THEN
	(fn x => (rewrite_thm_tac o map_eq_sym_rule) x THEN strip_asm_tac x)
	)
	THEN1 prove_∃_tac);
a (lemma_tac ⌜$≤⋎t⋎s res1 res2⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜$≤⋎t⋎s⌝]
		THEN REPEAT_N 2 strip_tac));
(* *** Goal "1.1" *** *)
a (lemma_tac ⌜∀ c⦁ c ∈⋎g TfForms t ⇒
	∀ va⦁ EvalForm (V, v, w) (va, c) ≤⋎t EvalForm (V, x, y) (va, c)⌝
	THEN1 (REPEAT strip_tac));
(* *** Goal "1.1.1" *** *)
a (fc_tac [ft_syntax_thm]);
a (lemma_tac ⌜tc ScPrec c t⌝
	THEN1 (all_fc_tac [scprec_fc_clauses2]
		THEN fc_tac [tc_incr_thm]));
a (all_asm_fc_tac[] THEN asm_rewrite_tac[]);
(* *** Goal "1.1.2" *** *)
a (rewrite_tac [get_spec ⌜EvalTf_results⌝, let_def]);
a (strip_tac);
a (all_asm_fc_tac[]);
a (∃_tac ⌜EvalForm (V, x, y) (InsertVars (TfVars t, v') va, f')⌝);
a (strip_tac);
(* *** Goal "1.1.2.1" *** *)
a (∃_tac ⌜v'⌝ THEN ∃_tac ⌜f'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.1.2.2" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (lemma_tac ⌜∀ c⦁ c ∈⋎g TfForms t ⇒
	∀ va⦁ EvalForm (V, v, w) (va, c) ≤⋎t EvalForm (V, x, y) (va, c)⌝
	THEN1 (REPEAT strip_tac));
(* *** Goal "1.2.1" *** *)
a (fc_tac [ft_syntax_thm]);
a (lemma_tac ⌜tc ScPrec c t⌝
	THEN1 (all_fc_tac [scprec_fc_clauses2]
		THEN fc_tac [tc_incr_thm]));
a (all_asm_fc_tac[] THEN asm_rewrite_tac[]);
(* *** Goal "1.2.2" *** *)
a (rewrite_tac [get_spec ⌜EvalTf_results⌝, let_def]);
a (strip_tac);
a (all_asm_fc_tac[]);
a (∃_tac ⌜EvalForm (V, v, w) (InsertVars (TfVars t, v') va, f')⌝);
a (strip_tac);
(* *** Goal "1.2.2.1" *** *)
a (∃_tac ⌜v'⌝ THEN ∃_tac ⌜f'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2.2.2" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "1.3" *** *)
a (GET_NTH_ASM_T 1 ante_tac THEN rewrite_tac [get_spec ⌜$≤⋎t⋎s⌝] THEN strip_tac);
a (lemma_tac ⌜res1 = {pTrue} ⇒ res2 = {pTrue}⌝
	THEN1 (rewrite_tac [sets_ext_clauses] THEN REPEAT strip_tac));
(* *** Goal "1.3.1" *** *)
a (all_asm_fc_tac[]);
a (all_asm_fc_tac[]);
a (DROP_NTH_ASM_T 6 ante_tac THEN asm_rewrite_tac[get_spec ⌜$≤⋎t⌝]);
a (STRIP_T rewrite_thm_tac);
(* *** Goal "1.3.2" *** *)
a (POP_ASM_T ante_tac THEN SYM_ASMS_T rewrite_tac
	THEN strip_tac);
a (all_asm_fc_tac[]);
a (POP_ASM_T ante_tac
	THEN rewrite_tac [get_spec ⌜$≤⋎t⌝]);
a strip_tac;
a (var_elim_nth_asm_tac 1);
a (var_elim_nth_asm_tac 3);
(* *** Goal "1.3.3" *** *)
a (all_fc_tac [mono_evaltftf_lemma]);
(* *** Goal "1.3.4" *** *)
a (all_fc_tac [mono_evaltftf_lemma]);
(* *** Goal "2" *** *)
a (strip_tac);
a (list_spec_nth_asm_tac 1 [⌜Snd z⌝, ⌜Fst z⌝]);
a (POP_ASM_T ante_tac THEN rewrite_tac[]);
val evalform_mono_thm = save_pop_thm "evalform_mono_thm";
=TEX
}%ignore

\subsubsection{The Semantic Functor}

=GFT
mono_semanticfunct_lemma1 =
   ⊢ ∀ V
     ⦁ MonoPprF (λ (m, e)⦁ EvalForm (V, m, e))
         ⇒ MonoFunct (SemanticFunctor V) 

mono_semanticfunctor_thm =
   ⊢ ∀ V⦁ MonoFunct (SemanticFunctor V)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀ V⦁ MonoPprF (λ(m, e)⦁ EvalForm (V,m,e))
		⇒ MonoFunct (SemanticFunctor V)⌝);
a (rewrite_tac (map get_spec [⌜MonoFunct⌝, ⌜SemanticFunctor⌝] @ [let_def])
	THEN REPEAT strip_tac);
a (fc_tac [monpprf_memrel_lemma1]);
a (DROP_NTH_ASM_T 3 discard_tac);
a (asm_tac eqrel_mono_thm);
a (FC_T (MAP_EVERY (ante_tac o (rewrite_rule[]))) [get_spec ⌜MonoPprF⌝]
	THEN_TRY rewrite_tac []
	THEN REPEAT strip_tac);
a (all_asm_fc_tac[]);
a (asm_rewrite_tac [get_spec ⌜$≤⋎p⋎r⌝]);
a (asm_rewrite_tac [get_spec ⌜$≤⋎r⌝]);
a (REPEAT ∀_tac);
a (SPEC_NTH_ASM_T 2 ⌜(x', y')⌝ (rewrite_thm_tac o (rewrite_rule [])));
val mono_semanticfunct_lemma1 = save_pop_thm "mono_semanticfunct_lemma1";

set_goal([], ⌜∀V⦁ MonoFunct (SemanticFunctor V)⌝);
a strip_tac;
a (asm_tac evalform_mono_thm);
a (spec_nth_asm_tac 1 ⌜V⌝);
a (fc_tac [mono_semanticfunct_lemma1]);
val mono_semanticfunctor_thm = save_pop_thm "mono_semanticfunctor_thm";
=TEX
}%ignore

\subsection{The Least Partial Fixed Point}

Having established the monotonicity of the semantic functor we can obtain a fixed point for any class V.
This will not immediately yield an interpretation of first order set theory because the fixed point will be a pair of relations which are not total over V.

To obtain interpretations of first order set theory we must chose V so as to omit sets which are problematic, and we may view this as seeking a notion of consistency appropriate to this context, i.e. a notion of when a property is consistently reifiable.

The partial fixed points may however be independently useful in applications where the systems of interest are not first order set theories, as in our case where an illative lamdba calculus is sought.

In order to obtain a least fixed point we must define the greatest lower bound of a set of pairs of relations.

For this purpose we need to know the greatest lower bound of a set of truth values.

ⓈHOLCONST
│ ⦏glb⋎t⋎s⦎ : TV SET → TV
├───────────
│ ∀ tvs⦁ glb⋎t⋎s tvs =
│	if tvs = {pTrue} then pTrue
│	else if tvs= {pFalse} then pFalse
│	else pU
■

We need to know that this is indeed the greatest lower bound, and to express this claim we define the relevan notion of lower bound.

ⓈHOLCONST
│ ⦏IsLb⋎t⋎s⦎ : TV SET → TV → BOOL
├───────────
│ ∀ tvs lb⦁ IsLb⋎t⋎s tvs lb =
	∀tv⦁ tv ∈ tvs ⇒ lb ≤⋎t tv
■

=GFT
⦏glb⋎t⋎s_thm⦎ =
   ⊢ ∀ tvs
     ⦁ (∃ tv⦁ tv ∈ tvs)
         ⇒ IsLb⋎t⋎s tvs (glb⋎t⋎s tvs)
           ∧ (∀ tv⦁ IsLb⋎t⋎s tvs tv ⇒ tv ≤⋎t glb⋎t⋎s tvs)
=TEX

\ignore{
=SML
set_goal([], ⌜∀tvs⦁ (∃tv⦁ tv ∈ tvs) ⇒	
	IsLb⋎t⋎s tvs (glb⋎t⋎s tvs)
	∧ ∀tv⦁ IsLb⋎t⋎s tvs tv ⇒ tv ≤⋎t (glb⋎t⋎s tvs)⌝);
a (rewrite_tac [get_spec ⌜IsLb⋎t⋎s⌝, get_spec ⌜glb⋎t⋎s⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (cases_tac ⌜tvs = {pTrue}⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a (var_elim_nth_asm_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (cases_tac ⌜tvs = {pFalse}⌝ THEN asm_rewrite_tac[]);
a (var_elim_nth_asm_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (cases_tac ⌜tvs = {pTrue}⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (var_elim_nth_asm_tac 1 THEN spec_nth_asm_tac 1 ⌜pTrue⌝);
(* *** Goal "2.2" *** *)
a (cases_tac ⌜tvs = {pFalse}⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.1" *** *)
a (var_elim_nth_asm_tac 1 THEN spec_nth_asm_tac 2 ⌜pFalse⌝);
(* *** Goal "2.2.2" *** *)
a (rewrite_tac [get_spec ⌜$≤⋎t⌝]);
a (asm_fc_tac[]);
a (strip_asm_tac (∀_elim ⌜tv'⌝ tv_cases_thm));
(* *** Goal "2.2.2.1" *** *)
a (var_elim_nth_asm_tac 1);
a (DROP_NTH_ASM_T 3 (strip_asm_tac o (rewrite_rule [sets_ext_clauses])));
a (spec_nth_asm_tac 5 ⌜x⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜$≤⋎t⌝]);
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.1.2" *** *)
a (var_elim_nth_asm_tac 2);
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [get_spec ⌜$≤⋎t⌝])));
a (POP_ASM_T (asm_tac o (conv_rule eq_sym_conv)));
a (var_elim_nth_asm_tac 1);
(* *** Goal "2.2.2.2" *** *)
a (var_elim_nth_asm_tac 1);
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [sets_ext_clauses])));
(* *** Goal "2.2.2.2.1" *** *)
a (spec_nth_asm_tac 5 ⌜x⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜$≤⋎t⌝]);
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2" *** *)
a (var_elim_nth_asm_tac 2);
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [get_spec ⌜$≤⋎t⌝])));
a (POP_ASM_T (asm_tac o (conv_rule eq_sym_conv)));
a (var_elim_nth_asm_tac 1);
val glb⋎t⋎s_thm = save_pop_thm "glb⋎t⋎s_thm";
=TEX
}%ignore

The greatest lower bound of a set of partial relations is:

ⓈHOLCONST
│ ⦏glb⋎r⋎s⦎ : R SET → R
├───────────
│ ∀ spr⦁ glb⋎r⋎s spr =
│	λx y⦁ glb⋎t⋎s {tv | ∃pr⦁ pr ∈ spr ∧ pr x y = tv}	
■

The relevant notion of lower bound is:

ⓈHOLCONST
│ ⦏IsLb⋎r⋎s⦎ : R SET → R → BOOL
├───────────
│ ∀ prs lb⦁ IsLb⋎r⋎s prs lb =
│	∀pr⦁ pr ∈ prs ⇒ lb ≤⋎r pr 
■

=GFT
=TEX

\ignore{
=IGN
set_goal([], ⌜∀prs⦁ (∃pr⦁ pr ∈ prs) ⇒	
	IsLb⋎r⋎s prs (glb⋎r⋎s prs)
	∧ ∀pr⦁ IsLb⋎r⋎s prs pr ⇒ $≤⋎r pr (glb⋎r⋎s prs)⌝);
a (rewrite_tac [get_spec ⌜IsLb⋎r⋎s⌝, get_spec ⌜glb⋎r⋎s⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜$≤⋎r⌝] THEN REPEAT strip_tac);
a (asm_tac glb⋎t⋎s_thm);
a (spec_nth_asm_tac 1 ⌜{tv|∃ pr⦁ pr ∈ prs ∧ pr x y = tv}⌝);
(* *** Goal "1.1" *** *)
a (spec_nth_asm_tac 1 ⌜pr x y⌝);
a (spec_nth_asm_tac 1 ⌜pr⌝);
(* *** Goal "1.2" *** *)

=TEX
}%ignore

The greatest lower bound of a set of pairs of partial relations is then:

ⓈHOLCONST
│ ⦏glb⋎s⋎p⋎r⦎ : PR SET → PR
├───────────
│ ∀ sppr⦁ glb⋎s⋎p⋎r sppr =
│	(glb⋎r⋎s {pr | ∃ppr⦁ ppr ∈ sppr ∧ pr = Fst ppr},
│	 glb⋎r⋎s {pr | ∃ppr⦁ ppr ∈ sppr ∧ pr = Snd ppr})	
■

and the least fixed point of a functor over pairs of partial relations is:

ⓈHOLCONST
│ ⦏lfp⋎p⋎r⦎ : (PR → PR) → PR
├───────────
│ ∀ f⦁ lfp⋎p⋎r f =
│	glb⋎s⋎p⋎r {ppr | $≤⋎p⋎r (f ppr) ppr}
■

=GFT
=TEX

\ignore{
=IGN
set_goal([], ⌜⌝)


set_goal([], ⌜∀f⦁ MonoFunct f ⇒ f(lfp⋎r f) = (lfp⋎r f)⌝);
a (REPEAT strip_tac THEN asm_fc_tac [get_spec ⌜MonoFunct⌝]);
a (lemma_tac ⌜$≤⋎p⋎r (f (lfp⋎r f)) (lfp⋎r f)⌝);
(* *** Goal "1" *** *)
a (rewrite_tac (map get_spec [⌜$≤⋎p⋎r⌝])
	THEN REPEAT ∀_tac);
a (rewrite_tac (map get_spec [⌜$≤⋎r⌝])
	THEN REPEAT ∀_tac);
a (rewrite_tac (map get_spec [⌜$≤⋎r⌝, ⌜$≤⋎t⌝])
	THEN REPEAT ∀_tac);
(* *** Goal "1.1" *** *)
a (lemma_tac ⌜$≤⋎p⋎r (lfp⋎r f) ⌝);

=TEX
}%ignore

\subsection{Alternative Definition of Least Fixed Point}

The proof that the above definition does yield a least fixed point is eluding me, so I thought I would try harder to make use of the fixed point result already available 


\section{SEMANTICS}

Now meaning is attached to the representatives.
This is done in such a way as to yield a functor from one membership structure to another, of which we will then be seeking useful partial fixed points. 

This functor will be compounded from maps for individual constructs which, parameterised by the incoming structure, return the extension of the interpreted construct in that context.
These extensions are collected to give both a new membership relation and an equivalence relative to which that relation is extensional.

The membership relations concerned are over equivalance classes of representatives, and the domains of the structures are partial partitions of the set of representations.

The semantics is therefore defined in a piecemeal way for each constructor in turn and then sewn together to give the required functor.

The fact that we have inter-defined membership and equality relationships, and also that we are expecting at best partial fixed points, together hint that we might benefit from working in the more general context of ``Boolean Values Models'' (see, for example, \cite{Jech2002}), so I propose to begin in that more general context and see how it goes.
i.e. the equality and membership relations will be functions yielding values in an arbitrary boolean algebra rather than classical relationships, and the relationship between them will be as prescribed for boolean valued models unless a problem is found with this.

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{ICsyn.th}
\include{ICsem.th}
}  %\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
