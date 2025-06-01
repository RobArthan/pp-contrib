=IGN
$Id: t018.doc,v 1.13 2010/08/13 10:57:22 rbj Exp $
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

\makeindex
\title{The Category of Categories}
\author{Roger Bishop Jones}
\date{\ }

\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

\makeindex

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
Explorations into the possibility of contructing non-well-founded foundations systems which are ontologically category theoretic and include a category of all categories.
\end{abstract}

\vfill

\begin{centering}
{\footnotesize

Created 2006/09/11

Last Checkin $ $Date: 2010/08/13 10:57:22 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t018.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t018.pdf}

$ $Id: t018.doc,v 1.13 2010/08/13 10:57:22 rbj Exp $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize
\end{centering}

\thispagestyle{empty}
\end{titlepage}
\newpage
\addtocounter{page}{1}
%\section{DOCUMENT CONTROL}
%\subsection{Contents list}
{\parskip=0pt \tableofcontents}
%\newpage
%\subsection{Document cross references}

\subsection*{To Do}
\begin{itemize}

\item
This document was started when I was working with NF and NFU, and is for the sake of simpliticy based directly on the formalisation of NFU following Holmes \cite{rbjt019}.
I have now come to a better understanding of the difficulties in working with NFU in ProofPower and am inclined to adopt a different non-well-founded set theory.

The next time I do any work on this, I am therefore likely to decouple it from any specific set theory, and define it as a construction on an arbitrary set theory.

Another aspect of this work which I now regard as obsolete is my attempt to make something of pseudo-induction (which I never really understood).
In my subsequent work on non-well-founded set theories I have abandoned pseudo-induction.
In particular my work on infinitarily definable non-well-founded sets yeilds its own kinds of induction over non-well-founded sets.

\end{itemize}

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\newpage

\section{Prelude}
In well-founded set theories there is no category of (all) categories.
This is one of a wider collection of issues which might be raised against the foundation of mathematics exclusively on well-founded sets.
More commonly perhaps, the failure in well-founded set theories of the notion of cardinal numbers as equivalence classes under equipollence may be thought a primary motivation for considering non-well-founded set theories.
Here we investigate non-well-founded ontologies without seeking new ways of representing numbers, but rather in order to have richer ontological support for abstract mathematics.

There are two aims for this document concerned with the category of categories.
The more ambitious and exotic, perhaps even frivolous, is the construction of a category theoretic foundational ontology which might serve as an alternative to the established ontology of well-founded sets.
This itself does not demand a departure from well-foundedness, but in our case we add the additional requirement that there be a category of all categories and more generally that the distinction between large and small categories which is necessary in well-founded set theories are rendered nugatory by the existence of categories encompassing the totality of relevant kinds of mathematical structures (e.g. a category corresponding to each kind of algebra).

Though in this we aim for a category theoretic foundation which stands on its own (rather than being based on a set theory) we need a meta-language to describe this system, and the ontology of that meta-language will include a non-well-founded set theory.
This set theory will also be expected to have a category of categories.

The exploration involves more than one set theoretic starting point, and more than one way of constructing concrete category theoretic structures from the chosen set theories.
The interest is primarily in systems which combine a substantial collection of well-founded entities with a non-well-founded ontology including a universal set or category.


\section{INTRODUCTION}

The material here concerns non-well-founded formal foundations for mathematics.

It builds on formalisations of non-well-founded set theories in \cite{rbjt019,rbjt020} some based on books by Forster \cite{forster92} and Holmes \cite{holmes98} and engages in a process of ontological transformation, whereby the ontology for an established foundation system is used to construct an alternative ontology, for which a suitable axiomatisation is formally established.

The rationale here is as follows:

\begin{itemize}

\item It is natural, even in an untyped universe, to abstract away from the detailed coding of functions as sets by treating both sets and functions as primitive.

\item In set theory we find a foundational ontology which is as simple as can be (i.e. sets are completely unstructured collections, all other ontologies involve working with structures which have more information in them than the collection of things from which they are built.
This presumably has many advantages in the investigation of foundational problems.
It may be however, that ontologies of more structured entities are pragmatically superior in applications.
Sets and functions are special cases of Categories (which are sets with some structure) and functors (more generally arrows) which are functions which preserve some structure.
This more complex ontology subsumes in a very direct way the more primitive set/function ontology.
A set is a discrete category, a function is a functor whose domain is discrete.

\item all the above has nothing to do with universal sets or well-foundedness.
The kind of construction described is easily done in a well-founded set theory, but I have found the prospective advantages in a well-founded context insufficient motivation to carry through from the construction to development of the resulting theory.
Partly this is because category theory more conspicuously than set theory screams against the constraint of well-foundedness.
When done in a non=well-founded context, the additional merit of a category theory in which talk about size becomes less pervasive is added to the incentive to see how the theory works out.

\end{itemize}

There are several approaches to this problem addressed in this document.
Some are based on the axiomatisation of NFU in \cite{rbjt019}, and some on the model for a theory of poly-sets in \cite{rbjt020}.
The former appear in section \ref{NFUBased} the latter in section \ref{PSBased}.

\subsection{Approaches Based on NFU}\label{NFUBased}

Two approaches to this construction are presented, the first based on the notion of pseudo-well-foundedness presented in \cite{forster92} and the second a ``Co-Inductive'' definition using methods from \cite{rbjt007}, one other is defined, {\it en passant} i.e. the well-founded inductive definition (which differs from the co-inductive case only in taking a least instead of a greatest fixed point), but taken not further.
One more case might merit consideration if we had decided to take pseudo-induction more seriously, and that is pseudo-co-induction (again taking a greatest rather than a least fixed point).

I will spell this out informally a little more fully.

Let us begin considering the hereditarily finite sets.
A hereditarily finite set is a finite set whose {\it members} are hereditarily finite set, nothing else is.
This is an inductive definition, in higher order set theory we can define them as the intersection of all collections of sets which are closed under the formation of finite sets.
One can imagine doing this for any property of sets, there is nothing special about "finite".

Now consider the ``hereditarily functional sets''.
A set is functional if it is a set of ordered pairs which considered as a relation is many-one.
Too close a parallel with the description of ``hereditarily finite'' fails in this case.
If we say: ``the hereditarily functional sets are those functional sets all of whose members are hereditarily functional sets'' we are immediately in trouble, because the members of a function are ordered pairs, not functions.

So in this case we need to generalise from ``member'' to constituent, the notion of constituent being a parameter along with the property.
In this case the constituents are the things in the domain and range of the function.

So now we say ``the `hereditarily functional sets' are those many-one relations whose field consists entirely of hereditarily functional sets''.
This elaboration of the idea of `hereditarily P' sets provides a semantic way of getting new foundation systems from old, the theory of hereditarily functional sets would make a foundation system similar in strength to the set theory on which its definition is based, and can be independently axiomatised, throwing away all reference to the original set theory.
To suggest that the resulting theory is a peer to set theory rather than remaining in some way parasitic upon it, I observe that by a broadly similar construction the original set theory can be constructed from the new function theory, as the `hereditarily empty set valued functions'' (i.e. the functions which always return the empty set, differing only in their domain, and which can therefore be taken as representatives of their domains).

Though there is some attraction in a foundation system based on functions rather than sets, this particular one (an untyped theory involving only well-founded functions) has attracted little interest.
Unfortunately the only ``problem'' it appears to fix is the awkwardness of coding up functions as graphs using sets, and this it replaces with the awkwardness of representing sets by special kinds of function.

We really need both sets and functions, ideally perhaps without coding either, so one might attempt an inductive construction which involved both concepts and yielded a two-sorted theory.
However, its more interesting to go one step further and consider sets and functions as special cases of concrete categories and functors.
This I have previously done in the well-founded case (at least, so far as defining the domains is concerned).
The objective here is to do something similar, without the constraint to well-foundedness, so that we get a foundation system which is categorical and in which there is a universal category.

The well-founded case has been addressed in a web page, at:

\href{http://www.rbjones.com/rbjpub/pp/gst/pcf-defns.html}
{http://www.rbjones.com/rbjpub/pp/gst/pcf-defns.html}

using a pair of rather cumbersome constructions.
The material here offers an alternative presentation of essentially the same material as well as different constructions not confined to well-founded ontologies.

Here I propose to take from that only the manner of representing categories and functors, and to recode the construction following Forster's definition of pseudo-well-foundedness.
Thus, a functor will be a triple consisting of a set which is the domain, a set which is the codomain and a function which is a many one relation between the domain and the codomain, total on the domain.
A category is a set of functors.
The left and right identity operations yeild the domain and codomain of the functors, composition is relational composition on the graphs.
 
In the well-founded case the construction is a liberalisation of the notion of `hereditarily P' set. which is closely coupled to the notion of well-foundedness.
The two liberalisations are, firstly that the notion of constituent replaces that of member and secondly that we have two sorts of entity involved.
In the non well-founded case we begin with the idea of pseudo-hereditary set which is coupled with Forster's notion of pseudo-wellfoundedness.
This already is two sorted, so the hope is that these two sorts can be the categories and functors.
So we perform the same liberalisation as before (from talk of members to talk of constituents) and then we have a notion of two sets being `pseudo-C-hereditarily (P,Q)' (the `C' being the notion of constituent at stake, of which strictly there are two).
Then we plumb in the properies specific to the category theoretic application.

All of this would be to no avail if done in the context of a well-founded set theory, though it would be useful to know whether it yields the same result as `C-heredicarily (P,Q)' in such a context.
To get a result which is not well-founded, we need to start with a non-well-founded collection of sets.
For this purpose we have axiomatisations in {\Product} HOL of NF and NFU.
The work is done by defining operators on set membersbip relations, so that the same construction can be applied to more than one set theory.

\subsection{Approaches Based on Poly-Sets}\label{PSBased}

The most distinctive feature of this material, in contrast with the material based on NFU is not the particular set theory conceived of as its content, but rather that the material is mainly presented as a construction over a more or less arbitrary set theory and only at the end instantiated to a particular set theory.
In fact, the theory of Poly-Sets is given in the same manner.
This makes it possible to demonstrate more fully the relationship between properties in the underlying set theories and properties in the resulting category theoretic system.

One this approach has been completed it should be possible to use the material in it to restate the definition based on NFU, until that is done this document will appear to have two superficial different treatments of the same category theoretic material.

\section{PRE-FUNCTORS}

This is a theory of the kind of functions which are suitable for use as the arrows in a concrete category.
Since the concrete categories which are of interest here are all categories of categories, the arrows will be functors and it is therefore not inappropriate to call this special kind of function a ``pre-functor''.

The sole difference between a prefunctor and a many-one relation in set theory is simply that the pre-functors have a defined codomain which may be distinct from its range.
It does not have a domain which is distinct from the set of values for which it is defined, since we expect the functions in a concrete category and the functors in a category of categories to be total functions.

This theory is a child of the formalisation of NFU in \cite{rbjt019} (roughly) following Holmes \cite{holmes98}.

=SML
open_theory "nfu_f";
force_new_theory "pre_func";
set_merge_pcs ["hol1", "'savedthm_cs_∃_proof", "'nfu_f1"];
=TEX

ⓈHOLCONST
│ ⦏PreFunctor⦎ : SET⋎nf → BOOL
├──────
│ ∀p⦁ PreFunctor p ⇔ ∃x y⦁ p = op(x, y) ∧ Rel x ∧ ManyOne⋎nf x ∧ rng x ⊆⋎nf y   
■

\ignore{
=SML
val PreFunctor↘u↕_def = get_spec ⌜PreFunctor⌝;
=IGN
set_goal([], ⌜PreFunctor (op(∅, ∅))⌝);
a (rewrite_tac[PreFunctor_def]);
a (∃_tac ⌜∅⌝ THEN ∃_tac ⌜∅⌝ THEN rewrite_tac[Rel↘u↕_∅↘u↕_thm, rng↘u↕_∅↘u↕_thm]);
=TEX
}%ignore

We define functions giving the graph, domain and codomain and field of a pre-functor and for application and composition of prefunctors.

ⓈHOLCONST
│ ⦏PFgraph⦎ : SET⋎nf → SET⋎nf
├──────
│ PFgraph = fst   
■

ⓈHOLCONST
│ ⦏PFdom⦎ : SET⋎nf → SET⋎nf
├──────
│ ∀p⦁ PFdom p = dom (PFgraph p)   
■

ⓈHOLCONST
│ ⦏PFcod⦎ : SET⋎nf → SET⋎nf
├──────
│ PFcod = snd
■

ⓈHOLCONST
│ ⦏PFfield⦎ : SET⋎nf → SET⋎nf
├──────
│ ∀p⦁ PFfield p = PFdom p ∪⋎nf PFcod p
■

\ignore{
=SML
val PFgraph↘u↕_def = get_spec ⌜PFgraph⌝;
val PFdom↘u↕_def = get_spec ⌜PFdom⌝;
val PFcod↘u↕_def = get_spec ⌜PFcod⌝;
val PFfield↘u↕_def = get_spec ⌜PFfield⌝;
=TEX
}%ignore

=SML
declare_infix(300, "⨾⋎p");
=TEX

This composition operator does not check that the pre-functors being compose have matching `types'.

ⓈHOLCONST
│ $⦏⨾⋎p⦎ : SET⋎nf → SET⋎nf → SET⋎nf
├──────
│ ∀p q⦁ p ⨾⋎p q = op((PFgraph p) ⨾⋎nf (PFgraph q), PFcod q)   
■

The identity pre-functor over some set is:

ⓈHOLCONST
│ ⦏PFid⦎ : SET⋎nf → SET⋎nf
├──────
│ ∀a⦁ PFid a = op(id a, a)   
■

We can now define the left and right identities for a pre-functor.

ⓈHOLCONST
│ ⦏PFleft⦎ : SET⋎nf → SET⋎nf
├──────
│ ∀a⦁ PFleft a = PFid (PFdom a)   
■

ⓈHOLCONST
│ ⦏PFright⦎ : SET⋎nf → SET⋎nf
├──────
│ ∀a⦁ PFright a = PFid (PFcod a)   
■

Pre-functor composition is an infix suffix {\it p}.

=SML
declare_infix (320, "⋎p");
=TEX

ⓈHOLCONST
│ $⦏⋎p⦎ : SET⋎nf → SET⋎nf → SET⋎nf
├──────
│ ∀p c d⦁ op(c, d) ∈⋎nf (PFgraph p) ⇒ p ⋎nf c = d 
■


\section{CATEGORIES AND FUNCTORS}

More than one approach is considered for defining collections of categories and functors in terms of the selected axiomatisation of set theory.

The first approach considered was inspired by the notion of pseudo-well-foundedness discussed in \cite{forster92}, the second on co-inductive methods described in \cite{rbjt007}.
Some initial material describing the categories and functors under discussion is used by both approached and is therefore presented first.

\subsection{Common Material on Categories and Functors}

Now we define the properties and content functions corresponding to concrete categories and functors.
This could be done by defining a function which takes a membership relation as an argument and returns a full set of four values for use with the function {\it PseudoCDPQHeredirary}.
However, this involves additional effort which would only be repaid if the construction were used over multiple set theories so I shall begin with a more direct definition.

The intention is that when the two collections have been defined they will be used to create two new types, and that theorems would then be proven about those types which would be suitable for an independent axiomatisation of the theories (for use as a foundation system).
This all involves quite a bit of reasoning which strictly belongs to the metatheory and would best not stored in the same theories as contain then object theory.
I will therefore create a theory {\it meta\_cf} which will contain the `metatheory' and put the theory itself in theory {\it cf} (for Categories and Functors).
I propose to base the construction on NFU.

=SML
force_new_theory "catfun";
(*new_parent "fixp";*)
=TEX

A concrete category (here) is a set of functors (the arrows) which is closed under composition (where the domain and codomains match) and includes the identity functors on the domain and codomain of each functor.
Composition is the same operation in all categories, and is associative as here defined.

A concrete functor is an ordered pair of which:
\begin{itemize}
\item the first element is a many-one relation
\item the second element is a set which includes the right field of the relation
\item the mapping defined by the first element over its domain respects composition on that domain
\end{itemize}

Note that the codomain is explicit in the right hand element of the functor, the domain is recovered from the graph on the left, hence all functors are total.

ⓈHOLCONST
│ ⦏CatProp⦎ : SET⋎nf → BOOL
├──────
│ ∀a⦁ CatProp a ⇔
│	(∀b⦁ b ∈⋎nf a ⇒ PFleft b ∈⋎nf a ∧ PFright b ∈⋎nf a)
│  ∧	(∀b c:SET⋎nf⦁ b ∈⋎nf a ∧ c ∈⋎nf a ∧ PFdom c = PFcod b ⇒ (b ⨾⋎p c) ∈⋎nf a)
■

This function returns the set of functors in a category.

ⓈHOLCONST
│ ⦏CatCon⦎ : SET⋎nf → SET⋎nf SET
├──────
│ ∀a⦁ CatCon a = {f | f ∈⋎nf a}
■

ⓈHOLCONST
│ ⦏FuncProp⦎ : SET⋎nf → BOOL
├──────
│ ∀a⦁ FuncProp a ⇔
│	rng (PFgraph a) ⊆⋎nf (PFcod a)
│  ∧	(∀b c⦁ b ∈⋎nf PFdom a ∧ c ∈⋎nf PFdom a ∧ PFcod b = PFdom c
│		⇒ op (b ⨾⋎p c, (a ⋎p b) ⨾⋎nf (a ⋎p c)) ∈⋎nf a)
■

This function returns the set of categories in the field of a functor.

ⓈHOLCONST
│ ⦏FuncCon⦎ : SET⋎nf → SET⋎nf SET
├──────
│ ∀f⦁ FuncCon f = {PFdom f; PFcod f}
■

\ignore{
=SML
val CatProp_def = get_spec ⌜CatProp⌝;
val CatCon_def = get_spec ⌜CatCon⌝;
val FuncProp_def = get_spec ⌜FuncProp⌝;
val FuncCon_def = get_spec ⌜FuncCon⌝;
=TEX
}%ignore

The following is a deeper category property, which asserts that the members of the category are all functors.

ⓈHOLCONST
│ ⦏CatFuncProp⦎ : SET⋎nf → BOOL
├──────
│ ∀a⦁ CatFuncProp a ⇔ CatProp a ∧ ∀f⦁ f ∈ CatCon a ⇒ FuncProp f
■

If the deeper property is in use, a deep content function may also be needed.
This gives for each category the set of categories which appear as the domain or codomain of one of the functors in the category.

ⓈHOLCONST
│ ⦏CatFuncCon⦎ : SET⋎nf → SET⋎nf SET
├──────
│ ∀c⦁ CatFuncCon c = ⋃{fc | ∃f⦁ f ∈ CatCon c ∧ fc = FuncCon f}
■

Next we have the corresponding deeper functor property which asserts that the domain and codomain of the functor are categories.

ⓈHOLCONST
│ ⦏FuncCatProp⦎ : SET⋎nf → BOOL
├──────
│ ∀a⦁ FuncCatProp a ⇔ FuncProp a ∧ ∀c⦁ c ∈ FuncCon a ⇒ CatProp c
■

Similarly the deeper functor content: 

ⓈHOLCONST
│ ⦏FuncCatCon⦎ : SET⋎nf → SET⋎nf SET
├──────
│ ∀f⦁ FuncCatCon f = ⋃{cf | ∃c⦁ c ∈ FuncCon f ∧ cf = CatCon c}
■

\ignore{
=SML
val CatFuncProp_def = get_spec ⌜CatFuncProp⌝;
val CatFuncCon_def = get_spec ⌜CatFuncCon⌝;
val FuncCatProp_def = get_spec ⌜FuncCatProp⌝;
val FuncCatCon_def = get_spec ⌜FuncCatCon⌝;
=TEX
}%ignore

For use in co-inductive definitions the property and the content function are combined into a single content function which effectively incorporates the property.
This function maps sets to sets.
It maps each set to the set of objects which can be constructed from the members in the argument set.

\subsection{Meta-Theory by Pseudo-Induction}

=SML
force_new_theory "metapi";
new_parent "nfu_f";
(*new_parent "fixp";*)
set_merge_pcs["hol1", "'savedthm_cs_∃_proof"];
=IGN
open_theory "metapi";
set_merge_pcs["hol1", "'savedthm_cs_∃_proof"];
=TEX

Since these sets (the categories and functors) are expected to be disjoint, at most (hopefully exactly) one of them will contain the empty set.
In our scheme the empty set is a category (but not a functor, functors will all be ordered pairs).
Looking at our definition of hereditarily above we see that the empty set can only be a member of the left hand collection, and so (c,P) must be the content function and characterising property for the categories and (d,Q) are those for functors.


We are now in a position to define the sets of pseudo-well-founded categories and functors.

ⓈHOLCONST
│ ⦏PWFcf⦎ : SET⋎nf SET × SET⋎nf SET
├──────
│ PWFcf = PseudoHereditarilyPQ (CatCon, FuncCon, CatProp, FuncProp)
■

We need them as properties for introducing types.

ⓈHOLCONST
│ ⦏PWFcategory⦎ : SET⋎nf → BOOL
├──────
│ PWFcategory = λc⦁ c ∈ (Fst PWFcf)
■

ⓈHOLCONST
│ ⦏PWFfunctor⦎ : SET⋎nf → BOOL
├──────
│ PWFfunctor = λf⦁ f ∈ (Snd PWFcf)
■

In order to use these properties to introducing new types we have to prove that they are non-empty.
Its useful to keep the theorems for the specific witnesses, the empty categort and the trivial functor.

\ignore{
=SML
val PWFcf_def = get_spec ⌜PWFcf⌝;
val PWFcategory_def = get_spec ⌜PWFcategory⌝;
val PWFfunctor_def = get_spec ⌜PWFfunctor⌝;

set_goal([], ⌜PWFcategory ∅⌝);
a (rewrite_tac[PWFcategory_def, PWFcf_def, PseudoHereditarilyPQ_def,
	P_closure_def, Q_closure_def, P_closed_def, Q_closed_def, CatCon_def]
	THEN REPEAT strip_tac);
a (strip_asm_tac (get_spec ⌜∅⌝));
a (spec_nth_asm_tac 2 ⌜∅⌝ THEN_TRY asm_fc_tac[]);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac [CatProp_def]);
val pwf_cat_∅_thm = save_pop_thm "pwf_cat_∅_thm";

set_goal([], ⌜∃a⦁ PWFcategory a⌝);
a (∃_tac ⌜∅⌝ THEN accept_tac pwf_cat_∅_thm);
val ∃_pwf_cat_thm = save_pop_thm "∃_pwf_cat_thm";

set_merge_pcs ["hol1", "'savedthm_cs_∃_proof", "'nfu_f1"];

set_goal([], ⌜PWFfunctor (op(∅, ∅))⌝);
a (rewrite_tac[PWFfunctor_def, PWFcf_def, PseudoHereditarilyPQ_def,
	P_closure_def, Q_closure_def, P_closed_def, Q_closed_def, CatCon_def]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜op (∅, ∅)⌝);
(* *** Goal "1" *** *)
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac [FuncProp_def]);
a (strip_tac);
(* *** Goal "1.1" *** *)
a (rewrite_tac[get_spec ⌜PFgraph⌝, get_spec ⌜PFcod⌝]);
a (lemma_tac ⌜Set(dom (∅ ⋏-⋏1⋏nf)) ∧ Set(∅)⌝ THEN1 rewrite_tac []);
a (rewrite_tac[get_spec ⌜$⊆⋎nf⌝] THEN ∀_tac THEN rewrite_tac[get_spec ⌜$⋏-⋏1⋏nf⌝]);
(* *** Goal "1.2" *** *)
a (rewrite_tac[PFdom↘u↕_def, PFgraph↘u↕_def]);
(* *** Goal "2" *** *)
a (swap_nth_asm_concl_tac 1);
a (strip_tac);
a (∃_tac ⌜∅⌝);
a (rewrite_tac[FuncCon_def, CatProp_def, PFgraph↘u↕_def, PFdom↘u↕_def, PFcod↘u↕_def]);
val ∅_pwf_func_thm = save_pop_thm "∅_pwf_func_thm";

set_goal([], ⌜∃a⦁ PWFfunctor a⌝);
a (∃_tac ⌜op(∅, ∅)⌝ THEN accept_tac ∅_pwf_func_thm);
val ∃_pwf_func_thm = save_pop_thm "∃_pwf_func_thm";
=TEX
}%ignore

=GFT
pwf_cat_∅_thm = 	⊢ PWFcategory ∅

∃_pwf_cat_thm = 	⊢ ∃ a⦁ PWFcategory a

∅_pwf_func_thm = 	⊢ PWFfunctor (op(∅, ∅))

∃_pwf_func_thm = 	⊢ ∃ a⦁ PWFfunctor a
=TEX

\subsection{Object Theory by Pseudo-Induction}

Now we introduce a new theory in which the types of pseudo-well-founded categories and functors are defined, and whose theories are intended to be a suitable independent axiomatisation for a two-sorted foundation system for which these two types supply a model. 

=SML
open_theory "metapi";
force_new_theory "cfpi";
force_new_pc "cfpi";
new_type_defn(["CAT"], "CAT", [], ∃_pwf_cat_thm);
new_type_defn(["FUNC"], "FUNC", [], ∃_pwf_func_thm);
=TEX

\subsection{Meta-Theory by (Co-)Induction}

The one we want here is co-induction, but we also show elements of the treatment by induction.

=SML
open_theory "catfun";
force_new_theory "metaci";
new_parent "nfu_f";
(*new_parent "fixp";*)
set_merge_pcs["hol1", "'savedthm_cs_∃_proof"];
=IGN
open_theory "metaci";
set_merge_pcs["hol1", "nfu", "'savedthm_cs_∃_proof"];
=TEX

We must first chose one of the kinds of representation which are supported by the theory `fixp' and convert our available functions to the chosen format.
In this case a `content relation' will suffice.
This is the relation between an object and those things of which it is an immediate constituent.
In this case we take two of these, one giving the relation between a category and those categories of which it is the domain or codomain of a functor, the other that between a functor and those functors of whose domain or codomain the functor is a member.


ⓈHOLCONST
│ ⦏CatRel⦎ : SET⋎nf → SET⋎nf → BOOL
├──────
│ ∀c d⦁ CatRel c d ⇔ CatFuncProp d ∧ c ∈ CatFuncCon d
■

ⓈHOLCONST
│ ⦏FuncRel⦎ : SET⋎nf → SET⋎nf → BOOL
├──────
│ ∀f g⦁ FuncRel f g ⇔ FuncCatProp g ∧ f ∈ FuncCatCon g
■

We may now use these two functions to obtain the least and greatest fixed points which are the respective inductive and co-inductively defined classes.

First the inductive case:

ⓈHOLCONST
│ ⦏WFcf⦎ : SET⋎nf SET × SET⋎nf SET
├──────
│ WFcf = (HeredRel CatRel, HeredRel FuncRel)
■

Then the co-inductive case:

ⓈHOLCONST
│ ⦏CWFcf⦎ : SET⋎nf SET × SET⋎nf SET
├──────
│ CWFcf = (CoHeredRel CatRel, CoHeredRel FuncRel)
■

For the purpose of introducing new types we need this as two properties:

ⓈHOLCONST
│ ⦏CWFcategory⦎ : SET⋎nf → BOOL
├──────
│   ∀c⦁ CWFcategory c = c ∈ Fst CWFcf
■

ⓈHOLCONST
│ ⦏CWFfunctor⦎ : SET⋎nf → BOOL
├──────
│   ∀f⦁ CWFfunctor f = f ∈ Snd CWFcf
■

\ignore{
=SML
val CatRel_def = get_spec ⌜CatRel⌝;
val FuncRel_def = get_spec ⌜FuncRel⌝;
val CWFcf_def = get_spec ⌜CWFcf⌝;
val CWFcategory_def = get_spec ⌜CWFcategory⌝;
val CWFfunctor_def = get_spec ⌜CWFfunctor⌝;

set_goal([], ⌜∃c⦁ CWFcategory c⌝);
a (∃_tac ⌜∅⌝ THEN rewrite_tac ([CWFcf_def, CWFcategory_def] @
	map get_spec [⌜CoHeredRel⌝, ⌜CoHeredFun⌝, ⌜Gfp⌝, ⌜Rel2Fun⌝, ⌜Fun2MonoFun⌝, ⌜$OpenUnder⌝]));
a (∃_tac ⌜{∅}⌝ THEN rewrite_tac [] THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
a (∃_tac ⌜{}⌝ THEN rewrite_tac [CatRel_def, CatFuncCon_def, CatCon_def, CatFuncProp_def]);
a (REPEAT strip_tac THEN swap_nth_asm_concl_tac 3);
a (rewrite_tac[nfu_f_op_ext_clauses1]);
val ∃_CWFcategory_thm = save_pop_thm "∃_CWFcategory_thm";

=IGN
set_goal([], ⌜∃f⦁ CWFfunctor f⌝);
a (∃_tac ⌜op(∅, ∅)⌝ THEN rewrite_tac ([CWFcf_def, CWFfunctor_def] @
	map get_spec [⌜CoHeredRel⌝, ⌜CoHeredFun⌝, ⌜Gfp⌝, ⌜Rel2Fun⌝, ⌜Fun2MonoFun⌝, ⌜$OpenUnder⌝]));
a (∃_tac ⌜{∅; op(∅, ∅)}⌝ THEN rewrite_tac [] THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜{∅}⌝ THEN rewrite_tac
	[FuncRel_def, FuncCatCon_def, FuncCatProp_def, FuncCon_def, FuncProp_def, ∅↘u↕_ax]);
a (strip_tac);
(* *** Goal "1.1" *** *)
a (REPEAT strip_tac);
(* *** Goal "1.2" *** *)

val ∃_CWFcategory_thm = save_pop_thm "∃_CWFcategory_thm";
=TEX
}%ignore



\ignore{
=SML
=TEX
} %ignore

\ignore{
=SML
=TEX
} %ignore

\ignore{
 ⓈHOLCONST
│ ⦏⦎ :
├──────
│
 ■
} %ignore

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{pre_func.th}
}  %\let

{\let\Section\section
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{catfun.th}
}  %\let

{\let\Section\section
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{metapi.th}
}  %\let

{\let\Section\section
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{cfpi.th}
}  %\let

{\let\Section\section
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{metaci.th}
}  %\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
=SML
open_theory "pre_func";
output_theory{out_file="pre_func.th.doc", theory="pre_func"};
open_theory "catfun";
output_theory{out_file="catfun.th.doc", theory="catfun"};
open_theory "metapi";
output_theory{out_file="metapi.th.doc", theory="metapi"};
open_theory "cfpi";
output_theory{out_file="cfpi.th.doc", theory="cfpi"};
open_theory "metaci";
output_theory{out_file="metaci.th.doc", theory="metaci"};
=IGN
