=IGN
$Id: t004.doc,v 1.19 2011/10/25 09:10:46 rbj Exp $
open_theory "membership";
set_merge_pcs ["hol1", "'savedthm_cs_∃_proof"];
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\tabstop=0.25in
\usepackage{A4}

\newcommand{\ignore}[1]{}
\def\Hide#1{\relax}
\def\pindex#1{#1\index{#1}}

\title{Membership Structures}
\author{Roger Bishop Jones}
\date{\ }
\vfill

\makeindex
\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

\begin{document}
\vfill
\maketitle
\begin{abstract}
A queer way of doing set theory in HOL (together with some queer reasons for doing it that way).
\end{abstract}
\vfill

\begin{centering}
{\footnotesize

Created 2004/07/15

Last Change $ $Date: 2011/10/25 09:10:46 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t004.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t004.pdf}

$ $Id: t004.doc,v 1.19 2011/10/25 09:10:46 rbj Exp $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize
\end{centering}

\newpage
{\parskip=0pt\tableofcontents}
\newpage
%%%%
%%%%
\subsection*{To Do}
\begin{itemize}

\item

\end{itemize}

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}} %\raggedright

%%%%
%%%%
\section{INTRODUCTION}

\subsection{Original Purposes}

This document was originally intended to serve various purposes which I will
attempt to describe here under the headings:

\begin{itemize}
\item The Foundations of Abstract Semantics.

\item Model Construction for Foundation Systems.

\item Formalistic Fallacies in Set Theory
\end{itemize}

\subsubsection{Foundations of Abstract Semantics}

This is concerned with what can be done formally to progress my understanding of the issues in this area.
It remains unclear whether any of the lines which I am considering has any potential.

A foundation for formal semantics is as I conceive it a language and a logic suitable for giving an abstract semantics to a broad range of other languages, and of enabling formal demonstration of truths which are relative to that semantics {\it analytic} or logically true.
The most obvious such language is that of set theory, so this topic is closely connected with the foundations of mathematics.

Here is an indication of some of the questions which seem to me to be of interest in this area and which it may be possibly to progress by formal methods:

\begin{itemize}

\item The relationship between languages L1 and L2 which obtains when the semantics of L1 is expressible in L2 is of particular interest.
Different such relationships will obtain according to what is held to constitute a semantics (e.g. a truth conditional semantics or a denotational semantics) and according to what counts as expressing a semantics in a language.
For the interesting particularisations of this class of partial orders it is of interest whether there is a universal language (in some class of languages under the relevant order) or class of languages (set theory is the most obvious candidate, and it is not immediately obvious whether it could be said to be universal either as a single or as a family of languages).

\item The question what are the key features of a language which makes it score high in expressiveness is of interest.
It is evident that the ontology of set theory, in particular the kind of entity involved as opposed to the particulars of which entities of that kind exist, is not crucial to expressiveness (other kinds of thing are equally suitable, e.g. functions).
On the other hand, it seems possible that the cardinality of the domain of discourse is important at least for sufficiently rich kinds of semantics.
But size surely cannot be all?

\end{itemize}

It is in fact rather more concerned with philosophy than with the brute technical development, and I don't really expect the formal development to get far enough to be valuable in itself.

The philosophy is concerned with set theory as a foundation for abstract semantics, and with the question how set theory can be made sufficiently definite in its meaning to serve well in that role.

Before starting on membership structures I have included an exploration of well-orderings, which may possibly be moved to a separate document at a later date.

\subsubsection{Set Theory as a Universal Semantic Foundation System}

Set theory is considered here primarily as a candidate universal foundation for semantics, i.e. as a language in which the abstract semantics of any other language may be given and to which, by such means, logical truth in its broadest sense, may be reduced.

\subsubsection{An Aside on Logical Truth}

Logical truth in its broadest sense I take to be {\it analyticity} which I also closely associate with necessary truth.
Very briefly my rationale in this is as follows.
In the first identification I am simply disinclined to follow the novelty of the twentieth century in using the notion of logical truth in as narrow and arbitrary a manner as has become common.
You may regard this if you like as a terminological eccentricity (which is how I regard modern usage in this matter).

On the relationship between analyticity with necessity I have more interesting reasons for rejecting the possibility of necessity {\it de re} (which I take to be any necessity which is not {\it de dicto}, necessity de dicto being analyticity).
If we were free to take any account of the semantics of a language, including some otherwise correct but substantively incomplete account, as the basis for defining the notion of analyticity then we could of course easily contrive examples of necessity {\it de re}.
Take for example the content free semantics for a language, which tells us nothing about which sentences are true or false.
Relative to the notion of analyticity (or necessity {\it de dicto}) which flows from that account all necessity is {\it de re}.
This is of course absurd.
To make a judgement about kinds of necessity one must of course judge necessity {\it de dicto} against a semantics which is complete, at least in its account of the truth conditions for a language.
A necessary proposition must however be true {\it under all conditions}.
Any complete account of the truth conditions of the relevant language must of course tell us whenever a statement is unconditionally true.
If any statement is judged necessary {\it de re} it must be that the denial of its being necessary {\it de re} is based upon an incomplete account of the truth conditions of the language.

There is however one distinction which I would draw between analyticity and necessity.
If we think of analyticity as truth in virtue of meaning, and think of propositions as the meanings of indicative sentences, then it is only sentences which can be analytic, which they are if they express a necessary proposition.

All this is far too much on this topic for this context.

\subsubsection{Constructing Models for Foundation Systems}

This is a fairly concrete aspect which is connected with the more
philosophical aspects relating to semantic foundations but not quite so speculative.

I will illustrate this with a brief statement of the actuall application which is driving this part of the work.

I am attempting in \cite{rbjt018} the construction of a model for a foundational system whose ontology is category theoretic.
This model is obtained in several stages, ultimately from a model of well-founded set theory.
The machinery for working with models of set theory is provided by this document.

I have previously done this kind of thing by axiomatising a strong set theory in HOL and then constructing the required models in that set theory with a view to deriving and then applying the theory from there.
This is OK for work in these alternative foundational ontologies but is not particularly suitable for meta-theory, and it does not facilitate evaluation of the effects of different set theoretic staring points on the constructed systems.

The idea of working from membership structures instead of from an axiomatisation of set theory is to make the constructions less dependent on any particular set theory, and to enable exploration of therelationship between properties of the initial model of set theory and the various other models constructed from it.

\subsubsection{Set Theory Generalised}

The kind of ``generalisation'' which I have in mind here is {\it without reference to any specific axiomatisation}.
The idea is to consider not so much the consequences and the models of particular axiom systems, but rather to consider particular models and the question what properties they posess, and also the properties themselves (including properties which are not expressible in first order logic).

Thus, the interest is not so much in sets as they appear in some theory, but on membership structures and their properties, and how to construct membership structures meeting various desiderata.

\subsubsection{Formalistic Fallacies in Set Theory}

Formalistic fallacies (of the kind which concern us here) are a species of sceptical fallacy, so I will begin with a few words about sceptical fallacies.
Scepticism in radical but consistent forms is a philosophy of doubt, an anti-dogmatic philosophy.
In practice it is very common for those of sceptical inclinations to slip into negative dogmatism, of which the most obvious and extreme form is to assert that nothing can be known.

Formalism was in Hilbert a symptom of naive overenthusiasm about the expressiveness of formal axiomatic systems.
He believed that all meaning (at least for mathematics) could be captured axiomatically, and therefore should be.
In its manifestation in the culture of mathematical logic today it is a kind of scepticism about semantics.
Limitations on the semantic expressiveness of formal languages are now well known, but the formalistic tendency (present in mathematical logic as a whole, not just among those who consider themselves formalists) is to avoid as far as possible the use of concepts which can be formalised or the pursuit of problems which are not formally tractible.

If this were confined to retaining an open mind on those problems which fall beyond the pale that would be OK.
These problems beyond the pale might nevertheless be addressed as philosophical problems.

However, the language of mathematical logic slips under this formalistic influence into negative dogmatism.
Concepts which should properly involve semantic (definability) are give purely syntactic definitions, denuding the vocabulary with which one might discuss properly semantic questions.
Semantics in mathematical logic is reduced to the relationship between syntax and its possible meanings, no longer concerned with identifying the particular meanings which elude formal characterisation.
Higher Order Logic is said not to be a logic, but rather a bastard semantic for which no proof system is available, thus perverting at once the notion of logic so that no logic can be incomplete (notwithstanding famous results to the contrary) and semantics, which can not longer express intended or desirable meaning if that could not be matched with a complete proof system.

It seems to me that some of the definite technical results in set theory are spoken of in language which misrepresents their significance, and it is these misrepresentations which I am calling here ``formalsitic fallacies''.

Here are some prime examples.

Results about what cannot be proven in ZFC, for example about the cardinality of the continuum or other aspects of cardinal exponentialtion, and presented as establishing negative results about what certain cardinals might be.

The relationship between V=L and the existence of measurable cardinals seems to me to be presented in a paradoxical manner.

\subsubsection{More Objectives}

I have so far poorly stated my objectives, so I will try harder here.

The idea of a semantic approach to set theory as universal semantic foundation system suggests to me that a relationship of interpretability is important.
This not the usual rather syntactic notion of interpretability as a relation between theories.
The differences I perceive are as follows:

\begin{itemize}

\item firstly, the required notion is not interpretability of theoremhood, which gives us an ordering in terms of proof theoretic strength, but of truth.
The interpretation must be truth preserving, not derivability preserving.

\item secondly, there is an interest in interpretations which not only respect truth, but which respect {\it meaning}.
One may for example complain of an interpretation of set theory in arithmetic, that even if it preserves truth it cannot preserve meaning, since it is of the essence of the meaning of set theory that it is concerned with collections of very large size, and that any interpretation in which all collections are countable (even if there is a paucity of demonstrable bijections to provide evidence of this) cannot be faithful to the meaning of set theory.

\item thirdly, all this talk of set {\it theory} is too syntactic, and wherever possible I am looking to eliminate syntactic in favour of semantics concepts.
How to do this remains to be seen, it may be appropriate to consider a language as some collection of properties of membership (or other) structures, and an interpretation as a mapping from properties over one kind of structure to properties of some other kind of structure.
\end{itemize}

This last point suggests, as is indeed the case, that I am not exclusively concerned with membership structures, though this particular document may remain dedicated to them.
I am interested in methods for transforming one foundational ontology into another, for example.

\subsection{Other Purposes}

The purposes I sought to describe in the previous section have never been significantly progressed, and a lot of the material in this document deserves to be discarded.

However, in the course of my deliberations in relation to non-well-founded set theories, some of the material has been used and additional materials have been included specific to or motivated by work on non-well-founded set theories.

These are:

\begin{itemize}
\item the definition of stratified property (section \ref{Stratified Properties}) and the axiom of stratified comprehension (section \ref{An Axiom of Stratified Comprehension}), done while investigating NF/NFU in HOL
\item the material on boolean membership structures (section \ref{BOOLEAN VALUED MEMBERSHIP STRUCTURES}), intended for use in finding non-well-founded interpretations but never used
\item the material on membership functors (section \ref{MEMBERSHIP FUNCTORS})
\end{itemize}

It is probable that future development of this document will continue to be along lines suggested by my investigations into non-well-founded set theory, the odds on my returning to the original motivations are not very high.

\subsection{Methods}

The methods supporting the above objective are still uncertain and evolving.
This is not because they are new and original, but because I do not yet understand well enough the pragmatics of doing set theory in {\Product-HOL} along the intended lines.

Partly because the methods are unstable, and partly because of my very limited knowledge of the literature, I am not able to say much about how this relates to what has been done before.
On one aspect, the formal definition of semantics using models in set theory without actually adopting an axiomatisation of set theory in HOL, the formal semantics for {\Product-HOL} by Rob Arthan \cite{ds/fmu/ied/spc002} should be mentioned.

The following methodological features can be noted at this point.

\begin{itemize}
\item No axioms, no preferred set theory.
\item Semantics preferred to syntax, focus on models not theories. 
\end{itemize}

\subsubsection{No Axioms}

It is this feature which distinguishes the set theory here from my previous formal work in set theory, and which is the reason for starting this document.

Previously I have axiomatised in HOL a higher order version of a first order set theory, typically something like ZFC +inaccessibles and worked with that theory.
Either developing that theory (though I have never got very far with that) or using the ontology of that theory in the construction of models for other kinds of foundation system.

The intention here is to avoid commitment to any particular axiomatisation of set theory by talking generally about membership structures and the relationships between their properties.
In this approach what might previously have been done by proving a result in an axiomatic set theory would be done by demonstrating that some property of membership structures (corresponding roughly to the parts of an axiomatisation necessary for the particular result) entails some other property (corresponding to the theorem).

In the case of model constructions, instead of working with an axiomatic system and constructing the model using the ontology of that system (the members of the HOL type which is the domain of the axiomatisation), we take a more external standpoint defining a construction which takes a (more or less arbitrary) membership structure and yields some other kind of structure and showing that the desired properties of target ontology are delivered by the construction provided that certain necessary properties obtain in the membership structure on which the construction is based.

\subsubsection{Semantics}

\section{MEMBERSHIP STRUCTURES}

Create new theory ``membership''.

=SML
set_flag("pp_use_alias", true);
open_theory "rbjmisc";
force_new_theory "⦏membership⦎";
new_parent "ordered_sets";
new_parent "bin_rel";
set_merge_pcs["hol1", "'ℤ", "'savedthm_cs_∃_proof"];
open RbjTactics1;
=IGN
open_theory "membership";
set_merge_pcs["hol1", "'ℤ", "'savedthm_cs_∃_proof"];
=TEX

The following types are used:
\begin{itemize}
\item[MS] membership structure
\item[PMS] property of membership structure
\end{itemize}

A membership structure is a set together with a binary relation over that set.
This constitutes an interpretation of the language of first order set theory, though not necessarily a model for any particular axiomatisation of set theory such as ZFC.

We are interested in properties of membership structures.
We are not exclusively interested in any particular kinds of properties, but we will introduce various classifications of these properties, the first of which will be those which are captured by sentences of first order set theory.

=SML
declare_type_abbrev ("⦏MS⦎", ["'a"], ⓣ'a SET × ('a → 'a → BOOL)⌝);
declare_type_abbrev ("⦏PMS⦎", ["'a"], ⓣ'a MS → BOOL⌝);
=TEX
=SML
declare_infix (305, "⦏∈⋎r⦎");
declare_infix (305, "⦏∈⋎a⦎");
declare_infix (305, "⦏∈⋎b⦎");
=TEX

The interest in first order properties is rather subsidiary, the real point of this approach to set theory is to escape from being constrained to first order properties.
There is some interest in showing why this is a good thing, and the notion of first order property is defined primarily in order to be able to show that interesting properties of membership structures often are not first order.

I don't know whether that will prove feasible, its not so hard to prove that properties are first order, but it will probably be a lot harder to prove that properties are not (even where that is pretty obviously the case on the basis of established results like the incompleteness theorems).
The most obvious example of a property which is not first order is well-foundedness.
The obvious way to prove that well-foundedness is not first order is to prove that if it were we would could get from first order set theory a complete arithmetic.
This route however presupposes a proof of the incompleteness of arithmetic, which is not so easy to do formally.

\subsection{Operators Over Sets}

Most of the operations over sets can be obtained in a canonical manner from a membership structure (even though the structure may not be closed under the operation).
This is because typically they are defined extensionally and the membership structures of interest usually are extensional.

There are two exceptions to this.
The first is the empty set, which represents the most common point of deviation from extensionality.
In a set theory with urelements the urelements will often have no members and are therefore extensionally equivalent to the empty set.
This means that you cannot tell from the membership structure alone the identity of the empty set.
The second case is the ordered pair constructor.
The problem here is that the defining characteristic is not extensional, and there are many ways in which it can be realised extensionally.

The operators over sets will be defined using an abstraction operator which, given some extension returns a set having that extension, if there is one.
We also define the function which gives the extension of a member of a membership structure.

ⓈHOLCONST
│ ⦏Ex⦎: 'a MS → 'a → 'a SET
├──────
│ ∀ (X, $∈⋎r) s⦁ Ex (X, $∈⋎r) s = {y | s ∈ X ∧ y ∈ X ∧ y ∈⋎r s}  
■

\ignore{
=SML
push_merge_pcs ["hol", "'savedthm_cs_∃_proof"];
set_goal([], ⌜∃Co⦁ ∀ (X, $∈⋎r) s⦁ (∃x⦁ x ∈ X  ∧ Ex (X, $∈⋎r) x = s)
	⇒ Ex (X, $∈⋎r) (Co (X, $∈⋎r) s) = s⌝);
a (prove_∃_tac THEN REPEAT strip_tac);
a (∃_tac ⌜εx⦁ x ∈ Fst x' ∧ Ex x' x = s'⌝
	THEN strip_tac);
a (ε_tac ⌜ε x⦁ x ∈ Fst x' ∧ Ex x' x = s'⌝);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
pop_pc();
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Co⦎: 'a MS → 'a SET → 'a
├──────
│ ∀ (X, $∈⋎r) s⦁ (∃x⦁ x ∈ X  ∧ Ex (X, $∈⋎r) x = s)
│	⇒ Ex (X, $∈⋎r) (Co (X, $∈⋎r) s) = s
■

We need to be able to talk about membership structures using the wider vocabulary associated with set theory (not just the membership relationship).
This of course does not make sense for arbitrary membership relations, which may not be closed under these operators.
We could add to and constrain the notion of membership structure to meet this requirement, but instead I propose a function which yields a set of operators which will have the required properties provided that the membership structure has appropriate closure and otherwise will not.

It might convenient if our function delivers a tuple of operators so we define it as follows:

=SML
declare_infix (310, "∪⋎m");
declare_infix (310, "↾⋎m");
declare_infix (310, "⦇⦈");
=TEX

ⓈHOLCONST
│ ⦏MS_ops⦎: 'a MS → ('a
│		× ('a × 'a → 'a)
│		× ('a → 'a → 'a)
│		× ('a → 'a)
│		× ('a → 'a)
│		× ('a → ('a SET) → 'a)
│		× ('a → ('a → 'a) → 'a)
│	)
├──────
│ ∀(X:'a SET) ($∈⋎a:'a → 'a → BOOL) ∅⋎m Pair⋎m $∪⋎m ⋃⋎m ℙ⋎m $↾⋎m $⦇⦈⦁
│	MS_ops (X, $∈⋎a) = (∅⋎m, Pair⋎m, $∪⋎m, ⋃⋎m, ℙ⋎m, $↾⋎m, $⦇⦈)
│	⇒ (∀ys y x⦁ 
│	∅⋎m = Co (X, $∈⋎a) {}
│	∧ Pair⋎m (x, y) = Co (X, $∈⋎a) {x; y}
│	∧ x ∪⋎m y = Co (X, $∈⋎a) ((Ex (X, $∈⋎a) x) ∪ (Ex (X, $∈⋎a) y))
│	∧ ⋃⋎m x = Co (X, $∈⋎a)
│		(⋃ {z | ∃y⦁ y ∈ X ∧ y ∈⋎a x ∧ z = Ex (X, $∈⋎a) y})
│	∧ ℙ⋎m x = Co (X, $∈⋎a) {y | Ex (X, $∈⋎a) y ∈ (ℙ (Ex (X, $∈⋎a) x))}
│	∧ x ↾⋎m ys = Co (X, $∈⋎a) {u | u ∈ X ∧ u ∈⋎a x ∧ u ∈ ys})
■

ⓈHOLCONST
│ ⦏union⦎: 'a MS → 'a → 'a
├──────
│ ∀ (X, $∈⋎a) x⦁ union (X, $∈⋎a) x = Co (X, $∈⋎a)
│		(⋃ {z | ∃y⦁ y ∈ X ∧ y ∈⋎a x ∧ z = Ex (X, $∈⋎a) y})
■



\subsection{Extended Membership Structures}

For some applications it seems possible that having just a little more structure will be helpful.
The two elements which seem most desirable are the empty set and an ordered pair constructor (with projections).

If there is an empty set, it can of course be identified from the membership relation, but there may be more than one, and it is sometimes important to chose one of them.
There are of course ways of defining the ordered pair constructor, but most of the applications I have in mind would rather not have to make the choice.

The following notion of extended membership structure is therefore introduced, and may be subject to adjustments or abandonment in the light of how useful it turns out to be.

There are enough pieces to make use of a HOL labelled product type worthwhile.

ⓈHOLLABPROD XMS─────────────────
│	Car⋎x	: 'a SET;
│	In⋎x	: 'a → 'a → BOOL;
│	∅⋎x	: 'a;
│	Op⋎x	: ('a × 'a) → 'a;
│	Fst⋎x	: 'a → 'a;
│	Snd⋎x	: 'a → 'a;
│	Abs⋎x	: 'a SET → 'a
■─────────────────────────

The minimal properties one would expect are:

\begin{itemize}
\item that the empty set is in the carrier and is empty
\item that the ordered pairs are in the carrier and the projections deliver the right values
\end{itemize}

ⓈHOLCONST
│ ⦏is_XMS⦎: 'a XMS → BOOL
├──────
│ ∀xms:'a XMS⦁ is_XMS xms
│ ⇔
│	(∅⋎x xms ∈ Car⋎x xms ∧ ¬ ∃s⦁ s ∈ Car⋎x xms ∧ In⋎x xms s (∅⋎x xms))
│   ∧	(∀l r⦁ l ∈ Car⋎x xms ∧ r ∈ Car⋎x xms
│		⇒ Op⋎x xms (l,r) ∈ Car⋎x xms
│		∧ Fst⋎x xms (Op⋎x xms (l,r)) = l
│		∧ Snd⋎x xms (Op⋎x xms (l,r)) = r)
│   ∧	(∀s:'a SET⦁ (∃t:'a⦁ ∀u:'a⦁ u ∈ s ⇔ (In⋎x xms) u t) ⇒
│		(∀u:'a⦁ u ∈ s ⇔ (In⋎x xms) u (Abs⋎x xms s)))
│   ∧	WellFounded (Car⋎x xms, In⋎x xms)
■

\section{BASIC PROPERTIES OF MEMBERSHIP RELATIONS}

The term ``membership relation'' is use purely to indicate motivation, this is not a non trivial subclass of binary relationships.

The following are key properties which yield our broadest classification of membersip relations:

\begin{enumerate}
\item extensionality
\item purity
\item well-foundedness
\end{enumerate}

\subsection{Extensionality}

None of these properties is essential for a membership relation.
The one which is perhaps most conspiciously characteristic of set membership is extensionality, but constructive set theories are likely not to be extensional, and set theories with urelements may have a qualified extensionality (as in NFU).

A set theory is ``pure'' if everything in the domain of discourse is a set.
This is connected with extensionality, since non-sets have no members and are therefore extensionally the same as the empty set (except for Quine atoms which are their own unit set, and permit something like urelements in a fully extensional theory).

We are concerned here only with relations whose type is some instance of $ⓣ'a → 'a → BOOL⌝$ and so there is only one type of entity in the domain of discourse, and so in some sense everything is a set.
However, if extensionality is weakened there may be any number of sets which have no members, and we may think of the extra ones as urelements.
If well-foundedness is absent or qualified then Quine's trick of treating urlements as their own unit set allows full extensionality to be retained in a system in which some things are not thought of as sets.

ⓈHOLCONST
│ ⦏extensional⦎: 'a PMS
├──────
│ ∀ (X, $∈⋎r)⦁ extensional (X, $∈⋎r) ⇔ ∀s t⦁ s ∈ X ∧ t ∈ X ⇒
│	(s = t ⇔ (∀ u⦁ u ∈ X ⇒ (u ∈⋎r s ⇔ u ∈⋎r t)))
■

The following weakend extensionality is satisfied by models of NFU:

ⓈHOLCONST
│ ⦏weakly_extensional⦎: 'a PMS
├──────
│ ∀ (X, $∈⋎r)⦁ weakly_extensional (X, $∈⋎r) ⇔ ∀s t⦁
│	s ∈ X ∧ t ∈ X ∧ (∃v⦁ v ∈ X ∧ v ∈⋎r s) ⇒
│	(s = t ⇔ (∀ u⦁ u ∈ X ⇒ (u ∈⋎r s ⇔ u ∈⋎r t)))
■

\ignore{
=SML
val extensional_def = get_spec ⌜extensional⌝;
set_goal([], ⌜∀ ms:'a MS⦁ extensional ms ⇔ ∀s t:'a⦁ s ∈ Fst ms ∧ t ∈ Fst ms ⇒
	(s = t ⇔ ∀ u:'a⦁ u ∈ Fst ms ⇒ (Snd ms u s ⇔ Snd ms u t))⌝);
a (strip_tac THEN once_rewrite_tac [prove_rule [] ⌜ms = (Fst ms, Snd ms)⌝]
	THEN rewrite_tac[extensional_def]
	THEN REPEAT strip_tac
	THEN TRY (all_asm_fc_tac[]));
val extensional_thm = save_pop_thm "extensional_thm";
=TEX
}%ignore

Any membership relation can be collapsed into one which is extensional, though in the worst case it might be trivial, by forming equivalence classes and redefining the relationship over those classes.

We obtain the new membership structure by taking the domain to be equivalence classes of members under some equivalence relation and then defining a new membership operation over those classes as follows:

It is convenient to use the theory {\it equiv\_rel} in which equivalences are curried binary relations rather than  sets of ordered pairs (as in theory {\it bin\_rel}).
We need to take an intersection of a collection of such relations so this is defined first.

ⓈHOLCONST
│ ⦏∧⋎r⦎: ('a → 'a → BOOL) SET → ('a → 'a → BOOL)
├──────
│ ∀ sr⦁ ∧⋎r sr = λx y⦁ ∀z⦁ z ∈ sr ⇒ z x y
■


Then {\it ExtQuot} gives the set of sets of elements which must be identified to give an extensional relationship. 

ⓈHOLCONST
│ ⦏ExtQuot⦎: 'a MS → 'a SET SET
├──────
│ ∀ (X, $∈⋎r)⦁ ExtQuot (X, $∈⋎r) =
│	QuotientSet X (∧⋎r {r : 'a → 'a → BOOL
│	   |  Equiv (X, r)
│	      ∧ ∀x y⦁ x ∈ X ∧ y ∈ X ∧ ((∀z⦁ z ∈⋎r x ⇔ z ∈⋎r y)
│		⇒ r x y)})
■

Finally we define the relationship:

ⓈHOLCONST
│ ⦏ExtRel⦎: 'a MS → 'a SET MS 
├──────
│ ∀ (X, $∈⋎r)⦁ ExtRel (X, $∈⋎r) =
│	let Y = ExtQuot (X, $∈⋎r)
	in (Y, λl r⦁ ∃u v⦁ u ∈ l ∧ v ∈ r ∧ u ∈⋎r v)
■

\subsection{Well-Foundedness}

The definition of well-foundedness used here is the concept {\it WellFounded} from the theory ``ordered\_sets''.

Set theories whose intuition is based in the cumulative or iterative heirarchy are both extensional and well-founded, and I will be concerned for the time being with just these kinds of membersbip relation.
These two properties can be thought of as telling us what kind of thing a set is, and the rest of the axioms in a systems like ZFC, possibly with large cardinal axioms, are trying to maximise the how many of the things with these properties can be shown to be in the domain of discourse.

This explanation connects with the usual description of the cumulative heirarchy, in which the formation of the domain of discourse of set theory is presented as occurring in stages.
At each stage one adds to the cumulative hierarchy all the sets which can be formed from those already obtained (the first ``all'') and then we are to understand that one goes through as many stages as one possibly can (the second ``all''), thereby aggregating all the pure well-founded collections.
Unfortunately, if one ever could complete this process the result would be a well-founded collection which would not contain itself, and so we must suppose that the construction cannot be completed.

My present interest is therefore, at present, in considering how to formalise the description of larger and larger parts of this incompletable construction.

The decomposition of the ``all'' in the intuitive concept suggests that the formalisation may be able to treat these two ``all''s separately.
The idea is that we can say that at each stage all possible new subsets are created, and then consider how to say that the number of stages is very large, separating questions of width and height.
A clean separation turns out not to be possible in a first order axiomatisation, but in the present context, i.e. in a higher order logic construed under the standard semantics, it is possible (though perhaps more by theft than honest toil, the relevant notion of ``all'' being readily expressed under the standard semantics).

However, there are some preliminaries which seem to be necessary to adeqately address either ``all''.
To get ``full-width'' we want to say that at each stage all the subsets of the previous stage become sets.
For this we need to be able to talk about the stages.

\subsection{Order Morphisms etc.}

ⓈHOLCONST
│ ⦏homomorph⦎: ('a MS × ('b MS)) → ('a → 'b) → BOOL
├──────
│ ∀ (X, $∈⋎a):'a MS; (Y, $∈⋎b):'b MS; f:'a → 'b⦁
│	homomorph ((X, $∈⋎a), (Y, $∈⋎b)) f ⇔  ∀s t:'a⦁ s ∈ X ∧ t ∈ X ∧ s ∈⋎a t
│						⇒ (f s) ∈ Y ∧ (f t) ∈ Y ∧ (f s) ∈⋎b (f t)
■

An embedding is not just an injective homomorphism:

ⓈHOLCONST
│ ⦏embedding⦎: ('a MS × ('b MS)) → ('a → 'b) → BOOL
├──────
│ ∀ (X, $∈⋎a):'a MS; (Y, $∈⋎b):'b MS; f:'a → 'b⦁
│	embedding ((X, $∈⋎a), (Y, $∈⋎b)) f ⇔  OneOne f
		∧ ∀s t:'a⦁ s ∈ X ∧ t ∈ X ⇒ (f s) ∈ Y ∧ (f t) ∈ Y ∧ (s ∈⋎a t ⇔ (f s) ∈⋎b (f t))
■

A substructure is something which embeds in the above sense.

=SML
declare_infix (300, "substructure_of");
=TEX

ⓈHOLCONST
│ $⦏substructure_of⦎: ('a MS) → ('a MS) → BOOL
├──────
│ ∀ (X, $∈⋎a) (Y, $∈⋎b)⦁
│	 (X, $∈⋎a) substructure_of (Y, $∈⋎b) ⇔ X ⊆ Y ∧ ∀s t:'a⦁ s ∈ X ∧ t ∈ X ⇒ (s ∈⋎a t ⇔ s ∈⋎b t)
■

Since the sets in a substructure need not have the same extension as those in the extension, we have a stronger notion here which corresponds to inclusion between transitive models in preserving the extension of the original sets.

=SML
declare_infix (300, "xsubstr");
=TEX

ⓈHOLCONST
│ $⦏xsubstr⦎: ('a MS) → ('a MS) → BOOL
├──────
│ ∀ (X, $∈⋎a) (Y, $∈⋎b)⦁
│	(X, $∈⋎a) xsubstr (Y, $∈⋎b) ⇔ X ⊆ Y ∧ ∀s t⦁ t ∈ X ∧ s ∈ Y ⇒ (s ∈⋎a t ⇔ s ∈⋎b t)
■

=SML
declare_infix (310, "◁⋎m");
=TEX

ⓈHOLCONST
│ $⦏◁⋎m⦎: ('a → BOOL) → 'a MS → 'a MS
├──────
│ ∀ P (X, $∈⋎a) ⦁ P ◁⋎m (X, $∈⋎a) = (X ∩ {x | P x}, $∈⋎a)
■

Membership structures need not be extensional. and so there may not be a unique set with no elements.
It is convenient to be able to talk about the empty things.

ⓈHOLCONST
│ $⦏ms_∅⦎: 'a MS → 'a → BOOL
├──────
│ ∀ (X, $∈⋎a) s⦁ ms_∅ (X, $∈⋎a) s
│	⇔ s ∈ X ∧ ∀z⦁ z ∈ X ⇒ ¬ z ∈⋎a s 
■

\subsection{Ordinals}

The reason for treating ordinals here is as follows.
One of the important properties of structures is their height.
Strong set theories are those with large cardinal axioms, which appear to be ensisting on the existence of very large sets, but which as is well know, do not succeed in their objective.
Set theories with large cardinal axioms still have countable models.
This is because {\it true} large cardinal properties are not expressible in first order logic, they are not first order properties of membership structures (as defined below).

So that we can talk about models which really do have large sets in them we need to define large cardinal {\it properties} as distinct from large cardinal axioms.
It is desirable to do this independently of any particular axiomatisation of set theory.

In our present context we could treat cardinals as equivalence classes of equipollent collections, but I propose nonetheless to follow more closely their treatment in well-founded set theories by taking them to be {\it alephs}, those ordinals which are larger than all their predecessors.

The stages can be ordered using ordinals, and so first we need a concept of ordinal number.
We can think of ordinals in terms of width, for the ordinals are among the membership relations of least width (which are those in which only one new set is introduced at each stage).

There are two kinds of (representation or realisation of) ordinals of interest here.
The first kind of ordinal is an element in the domain of a membership relation.
The second is a membership relation of which the domain as a whole is an ordinal.
In this case all the elements in the domain are ordinals and the relation of a whole may be thought of as the class of these ordinals.

Subscripts will be used to distinguish properties of ordinal relations from the corresponding property of ordinal elements.

A {\it relation} is ``ordinal'' iff it is a transitive strict well-ordering.
The concept of {\it WellOrdering} in the theory n$ordered\_sets$ does not require strictness so we define an ordinal using $WellFounded$ (which does require strictness) and $LinearOrder$.

ⓈHOLCONST
│ ⦏Ordinal⋎ms⦎: 'a PMS
├──────
│ ∀ ms⦁ Ordinal⋎ms ms ⇔ LinearOrder ms ∧ Trans ms ∧ WellFounded ms
■

An ordinal set is one which is transitive and well ordered by membership.

ⓈHOLCONST
│ ⦏⊆⋎ms⦎: 'a MS → 'a → 'a → BOOL
├──────
│ ∀ (X, $∈⋎r):'a MS; a b:'a⦁ ⊆⋎ms (X, $∈⋎r) a b ⇔ ∀x⦁ x ∈ X ∧ x ∈⋎r a ⇒ x ∈⋎r b
■

=SML
declare_alias ("⊆↘↕", ⌜⊆⋎ms⌝);
=TEX

ⓈHOLCONST
│ ⦏TransitiveSet⦎: 'a MS → 'a → BOOL
├──────
│ ∀ (X, $∈⋎r):'a MS; a:'a⦁ TransitiveSet (X, $∈⋎r) a ⇔
		∀x⦁ x ∈ X ∧ x ∈⋎r a ⇒ ⊆⋎ms (X, $∈⋎r) x a
■

The following function delivers the restriction of a membership relation to the extension of one of its sets.

ⓈHOLCONST
│ ⦏set2rel⦎: 'a MS → 'a → 'a MS
├──────
│ ∀ (X, $∈⋎r):'a MS; a:'a⦁ set2rel (X, $∈⋎r) a = ({x:'a | x ∈⋎r a ∧ x ∈ X}, $∈⋎r)
■

We then define the ordinals sets as those sets which are transitive and well-ordered by membership.

ⓈHOLCONST
│ ⦏Ordinal⦎: 'a MS → 'a → BOOL
├──────
│ ∀ ms s⦁ Ordinal ms s ⇔ TransitiveSet ms s ∧ WellOrdering (set2rel ms s)
■

ⓈHOLCONST
│ ⦏ordinals⦎: 'a MS → 'a SET
├──────
│ ∀ ms⦁ ordinals ms = {s | Ordinal ms s}
■

\subsection{Ordinal Arithmetic}

In this section I am using {\it Co} freely, in effect assuming extensionality in the membership structure.

First, zero.

ⓈHOLCONST
│ ⦏∅⦎: 'a MS → 'a
├──────
│ ∀ (X, $∈⋎a)⦁ ∅ (X, $∈⋎a) = Co (X, $∈⋎a) {}
■

\ignore{
=IGN
set_goal([], ⌜∀(X, $∈⋎a)⦁ (∃x⦁ x ∈ X ∧ ∀y⦁ y ∈ X ⇒ ¬ y ∈⋎a x) ⇒ ∀z⦁ z ∈ X ⇒ ¬ z ∈⋎a (∅ (X, $∈⋎a))⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜∅⌝]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜Ex (X, $∈⋎r) x = {}⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜Ex⌝]
		THEN contr_tac
		THEN asm_fc_tac[]));

get_spec ⌜Co⌝;

a (
=TEX
}%ignore

Next the successor relationship:

ⓈHOLCONST
│ ⦏Succ⋎o⦎: 'a MS → 'a → 'a → BOOL
├──────
│ ∀ ms a b⦁ Succ⋎o ms a b ⇔ Ex ms b = {x | x = a ∨ x ∈ Ex ms a}
■

ⓈHOLCONST
│ ⦏SuccClosed⋎o⦎: 'a MS → BOOL
├──────
│ ∀ ms⦁ SuccClosed⋎o ms ⇔ ∀x⦁ Ordinal ms x ⇒ ∃y⦁ Succ⋎o ms x y
■

Then the successor function:

ⓈHOLCONST
│ ⦏succ⋎o⦎: 'a MS → 'a → 'a
├──────
│ ∀ (X, $∈⋎a) x⦁ succ⋎o (X, $∈⋎a) x =
│	Co (X, $∈⋎a) {y | y ∈ X ∧ (y = x ∨ y ∈⋎a x)}
■

\ignore{
=IGN
set_goal([], ⌜∀(X, $∈⋎a)⦁ SuccClosed⋎o (X, $∈⋎a) ⇒ ∀x⦁ Ordinal (X, $∈⋎a) x ⇒ Succ⋎o (X, $∈⋎a) x (succ⋎o (X, $∈⋎a) x)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜SuccClosed⋎o⌝, get_spec⌜succ⋎o⌝]
	THEN REPEAT strip_tac);
a (asm_fc_tac[]);
a (POP_ASM_T ante_tac THEN rewrite_tac[get_spec ⌜Succ⋎o⌝, get_spec ⌜Co⌝, get_spec ⌜Ex⌝, get_spec ⌜Ordinal⌝]);
a strip_tac;

	THEN REPEAT strip_tac);



set_goal([], ⌜∀ms⦁ SuccClosed ms ⇒ ∀x y⦁ Ordinal ms x ∧ Ordinal ms y 
	∧ succ⋎o ms x = succ⋎o ms y ⇒ x = y⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜SuccClosed⌝, get_spec ⌜succ⋎o⌝]
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]);

stop;
set_goal([], ⌜∃pred⋎o⦁ ∀ ms x⦁ Ordinal ms x ⇒ pred⋎o ms (succ⋎o ms x) = x⌝);
a (prove_∃_tac THEN REPEAT strip_tac);
a (∃_tac ⌜λx⦁ εy⦁ Ordinal ms y ∧ succ⋎o ms' y = x⌝ THEN rewrite_tac[]
	THEN REPEAT strip_tac);
a (ε_tac ⌜ε y⦁ Ordinal ms' y ∧ succ⋎o ms' y = succ⋎o ms' x⌝);
(* *** Goal "1" *** *)
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);

delete_specification;

=TEX
}%ignore

ⓈHOLCONST
│ ⦏pred⋎o⦎: 'a MS → 'a → 'a
├──────
│ ∀ ms x⦁ Ordinal ms x ⇒ pred⋎o ms (succ⋎o ms x) = x
■

Addition is defined using transfinite recursion.

\ignore{
=IGN
stop;
set_goal([], ⌜∃sum⋎o⦁ 
 ∀ ms x y⦁ {x;y} ⊆ ordinals ms
 ⇒	sum⋎o ms x (∅ ms) = x
 ∧	sum⋎o ms x (succ⋎o ms y) = succ⋎o ms (sum⋎o ms x y)
⌝);
a (prove_∃_tac THEN REPEAT strip_tac);
a (lemma_tac ⌜∃G:('a → 'a) → ('a → 'a)⦁ ∀f s⦁ G f s = 
	if s = (∅ ms') then x' else succ⋎o ms' (f (pred⋎o ms' s))⌝
	THEN1 prove_∃_tac);
a (lemma_tac ⌜FunctRespects G (Car⋎x xms', In⋎x xms')⌝
	THEN1 (rewrite_tac [get_spec ⌜FunctRespects⌝]
		THEN REPEAT strip_tac
		THEN asm_rewrite_tac[]));
(* *** Goal "1" *** *)
a (cases_tac ⌜x = ∅ ms'⌝ THEN asm_rewrite_tac[]);
=TEX
}%ignore

ⓈHOLCONST
│ ⦏$sum⋎o⦎: 'a MS → 'a → 'a → 'a
├──────
│ ∀ ms x y⦁ {x;y} ⊆ ordinals ms
│ ⇒	sum⋎o ms x (∅ ms) = x
│ ∧	sum⋎o ms x (succ⋎o ms y) = succ⋎o ms (sum⋎o ms x y)
■


\subsection{Ordinals in Extended Membership Structures}

The VonNeuman ordinals can be extracted from an XMS as follows:

ⓈHOLCONST
│ ⦏xms_ordinals⦎: 'a XMS → 'a SET
├──────
│ ∀xms⦁	xms_ordinals xms =
│	{x | x ∈ Car⋎x xms ∧ Ordinal (Car⋎x xms, In⋎x xms) x}
■

\subsection{WK Ordered Pairs}

The following relation tells us when something in the domain of a relationship structure is an ordered pair.

ⓈHOLCONST
│ $⦏ms_pair⦎: 'a MS → ('a × 'a) → 'a → BOOL
├──────
│ ∀ (X, $∈⋎a) (l,r) p⦁ ms_pair (X, $∈⋎a) (l,r) p
│	⇔ p ∈ X ∧ ∀z⦁ z ∈ X ⇒ (z ∈⋎a p ⇔ z = l ∨ z = r)
■

ⓈHOLCONST
│ $⦏ms_unit⦎: 'a MS → 'a → 'a → BOOL
├──────
│ ∀ ms s u⦁ ms_unit ms s u
│	⇔ ms_pair ms (s,s) u
■

ⓈHOLCONST
│ $⦏ms_wkp⦎: 'a MS → ('a × 'a) → 'a → BOOL
├──────
│ ∀ ms (l,r) p⦁ ms_wkp ms (l,r) p
│	⇔ ∃s t:'a⦁ ms_unit ms l s ∧ ms_pair ms (l, r) t ∧ ms_pair ms (s,t) p  
■

\subsection{Standard Models}

The use of {\it standard} here follows its use in the context of higher order logic, in which a standard model is one in which the power sets are complete.
In set theory this comes down to the idea that the standard models are the {\it V}(α) for some ordinal α.

\footnote{
There is a weaker notion of standard in set theory which originates I believe in the theory of forcing.
This effectively enforces only well-foundedness, a standard model as defined by Cohn is just a transitive set.
}%footnote

We therefore define the relationship {\it V} between ordinals and standard models of rank α.
The relationship is defined by transfinite recursion, and we therefore need to use a suitable recursion theorem to establish its consistency.

First of all we will have to defined certain elementary concepts.
The definition informally is:

=GFT
	V α = ⋃↘{β < α}↕ ℙ(V β)
=TEX

The universe of rank α is the union of the power sets of the universes of all smaller ranks.

or:

=GFT
	V α = {x | ∃β < α⦁ x ⊆ V β}
=TEX

To formalise this we need to a functor over which this is a fixed point.

ⓈHOLCONST
│ ⦏Vf⦎: (('b → 'b → BOOL) × 'a MS → 'a) → (('b → 'b → BOOL) × 'a MS → 'a)
├──────
│ ∀f⦁ Vf f =  λ($<<, ms)⦁ 
│	let (∅⋎m, Pair⋎m, $∪⋎m, ⋃⋎m, ℙ⋎m, $↾⋎m, $⦇⦈) = MS_ops ms
│	in Co ms {z	| z ∈ Fst ms
		  	∧ ∃v⦁ (Ex ms z) ⊆ (Ex ms (f ((λx y⦁ x << y ∧ y << v), ms)))}
■

=GFT
=TEX

Using a recursion theorem we derive from this the condition necessary to justify the following definition of V:

\ignore{
=IGN
set_goal([], ⌜∀((X : 'a SET), ($<< : 'a → 'a → BOOL))⦁ FuncRespects Vf (Universe, λ(x,y) (v,w)⦁ ∃z⦁ (∀p q⦁ x p q ⇔ v p q ∧ v q z))⌝);


set_goal([], ⌜∃V⦁ ∀($<< : 'a → 'a → BOOL) ms⦁ WellFounded (Universe, $<<)
	⇒ V ms $<< =
		let (∅⋎m, Pair⋎m, $∪⋎m, ⋃⋎m, ℙ⋎m, $↾⋎m, $⦇⦈) = MS_ops ms
		in Co ms {z	| z ∈ Fst ms
		  	∧ ∃v⦁ (Ex ms z) ⊆ (Ex ms (V ms (λx y⦁ x << y ∧ y << v)))}
⌝);
a (∃_tac ⌜Vf⌝ THEN rewrite_tac[]);
=TEX
}%ignore



=GFT
recursion_theorem =
   ⊢ ∀ ((X : 'a SET), ($<< : 'a → 'a → BOOL)) (G : ('a → 'b) → 'a → 'b)⦁
	FunctRespects G (X, $<<) ∧ WellFounded (X, $<<)
         ⇒ UniquePartFixp X G : THM
=TEX


\ignore{
 ⓈHOLCONST
│ ⦏V⦎: 'a MS → 'b MS → BOOL
 ├──────
│ ∀ (X, $∈⋎a) (Y, $∈⋎b) ⦁ Ordinal (X, $∈⋎a) ∧ 
 ■
}%ignore
\section{FIRST ORDER PROPERTIES}

In order to define the notion of a ``first order property'' we need to mimic the satisfaction relation.
Sentences define sets of interpretations, but formulae only do so in the context of an assignment to the free variables in the formula.
The operators we define therefore operate over parameterised properties of interpretations.

It proves desirable to make this theory polymorphic not only in the type of the sets involved, but also in the notion of variable (sometimes we may wish to work with assignments to terms).
An assignment to free variables is modelled as a function from objects of type ⓣ'v⌝ (a type variable) to elements in the domain of the relation (here ⓣ's⌝).

=SML
declare_type_abbrev ("⦏VA⦎", ["'s", "'v"], ⓣ'v → 's⌝);
=TEX

ⓈHOLLABPROD ⦏PPMS⦎─────
│ ppms : ('s, 'v) VA → 's PMS
■──────────────

Various operators over properties of membership relations are now defined.

The language of set theory which we consider has the following simplifying characteristics:

\begin{enumerate}
\item the only terms are variables
\item the relations are equality and membership
\item the propositional connectives are conjunction and negation
\item there is just one, existential, quantifier
\end{enumerate}

Membership statements are parameterised by the names of the two variables between which membership is predicated, and the parameterised property of membership relations which they denote is:

=SML
declare_infix (305, "∈⋎p");
=TEX

ⓈHOLCONST
│ $⦏∈⋎p⦎: 'v → 'v → ('s, 'v) PPMS
├──────
│ ∀ s t:'v⦁ (s ∈⋎p t) = MkPPMS (λva: ('s, 'v) VA; (X, $∈⋎r):'s MS⦁
│	(va s) ∈⋎r (va t))
■

Equality is defined similarly.

=SML
declare_infix (305, "=⋎p");
=TEX

ⓈHOLCONST
│ $⦏=⋎p⦎: 'v → 'v → ('s, 'v) PPMS
├──────
│ ∀ s t:'v⦁ s =⋎p t = MkPPMS(λ va:('s, 'v) VA; (X, $∈⋎r): 's MS⦁
│	(va s) = (va t))
■

Conjunction denotes a binary operation over PPMS's.

=SML
declare_infix (302, "∧⋎p");
=TEX

ⓈHOLCONST
│ $⦏∧⋎p⦎: ('s, 'v) PPMS → ('s, 'v) PPMS → ('s, 'v) PPMS
├──────
│ ∀ l r⦁ l ∧⋎p r = MkPPMS(λva (X, $∈⋎r)⦁ (ppms l va (X, $∈⋎r)) ∧ (ppms r va (X, $∈⋎r)))
■

Negation denotes a monadic operator.

ⓈHOLCONST
│ ⦏¬⋎p⦎: ('s, 'v) PPMS → ('s, 'v) PPMS
├──────
│ ∀ f⦁ ¬⋎p f = MkPPMS(λva (X, $∈⋎r)⦁ ¬ (ppms f va (X, $∈⋎r)))
■

The existential quantifier binds a variable and its value depends upon assigning values to that variable in a variable assignment.
The following function modifies a variable assignment.

ⓈHOLCONST
│ ⦏assign⦎:  's → 'v → ('s, 'v) VA → ('s, 'v) VA
├──────
│ ∀ a s va t ⦁ assign a s va t = if t = s then a else va t
■

Finally the existential quantifier, which is parameterised by the name of the variable it binds and the value of the formula it quantifies over.

ⓈHOLCONST
│ ⦏∃⋎p⦎: 'v → ('s, 'v) PPMS → ('s, 'v) PPMS
├──────
│ ∀ s f⦁ ∃⋎p s f = MkPPMS(λva (X, $∈⋎r)⦁ ∃a⦁ a ∈ X ∧ ppms f (assign a s va) (X, $∈⋎r))
■

\ignore{
=SML
val PPMS_def = get_spec ⌜MkPPMS⌝;
val eq⋎p_def = get_spec ⌜$=⋎p⌝;
val eq⋎p_def = get_spec ⌜$=⋎p⌝;
val ∈⋎p_def = get_spec ⌜$∈⋎p⌝;
val ¬⋎p_def = get_spec ⌜¬⋎p⌝;
val ∧⋎p_def = get_spec ⌜$∧⋎p⌝;
val assign_def = get_spec ⌜assign⌝;
val ∃⋎p_def = get_spec ⌜∃⋎p⌝;
=TEX
}%ignore

Next we define the set of parameterised properties which can be constructed by these operators and then take their closures to eliminate the parameters.

ⓈHOLCONST
│ ⦏fof⦎: ('s, 'v) PPMS → BOOL
├──────
│ ∀ppms1⦁ fof ppms1 ⇔
│	∀pppms⦁ (∀s1 s2 p1 p2 ⦁
│		pppms (s1 ∈⋎p s2)
│		∧ pppms (s1 =⋎p s2)
│		∧ (pppms p1 ∧ pppms p2
│			⇒ pppms (p1 ∧⋎p p2)
│			∧ pppms (¬⋎p p1)
│			∧ pppms (∃⋎p s1 p1))
│		)
│		⇒ pppms ppms1
■

Finally we define the property of properties of membership structures which consists in being definable by a set of sentences of first order set theory.

First we define the closure of a first order formula.
Note that this function serves to convert a paramaterised property of membership structures into a plain property of membership structures, and this is its primary purpose.
The fact that it also effectively undertakes a universal closure is a side effect (though this will simplify some demonstrations), since it is primarily intended for application to closed formulae.

An awkwardness arises here in dealing with the possibility of empty structures.
An interpretation of a first order language must be non-empty, but for present purposes it is convenient for the notion of a first order property of structures to take into account the possibility of empty structures.

ⓈHOLCONST
│ ⦏foc⦎: ('s, 'v) PPMS → 's PMS
├──────
│ ∀ppms1 (X, $∈⋎m)⦁ foc ppms1 (X, $∈⋎m) ⇔
│	∀va⦁ X = {} ∨ (∀v⦁ va v ∈ X)
│		⇒ ppms ppms1 va (X, $∈⋎m)
■

The concept of first order sentence, as here presented using semantic rather than syntactic entities, is in fact the property of being a property of membership structures which can be expressed by a sentence in the language of first order set theory.
The name {\it fop} for {\it first order property} is therefore chosen rather than {\it fos} for {\it first order sentence}.

This property is independent of the type of variables, but is defined in terms of entities which are polymorphic in the type of variables.
For the definition to be conservative we have to parameterise it with a variable, which is ignored.
In applications this definition can be instantiated to the application type to yield a property.

ⓈHOLCONST
│ ⦏fop⦎: 'v → 's PMS → BOOL
├──────
│ ∀pmr v⦁ fop v pmr ⇔ ∃f: ('s, 'v) PPMS⦁ fof f ∧ pmr = foc f
■

For convenience the following derived constructors are defined:

=SML
declare_infix (298, "∨⋎p");
declare_infix (295, "⇒⋎p");
declare_infix (290, "⇔⋎p");
=TEX

ⓈHOLCONST
│ $⦏∨⋎p⦎ : ('s, 'v) PPMS → ('s, 'v) PPMS → ('s, 'v) PPMS
├──────
│  ∀l r⦁ l ∨⋎p r = ¬⋎p (¬⋎p l ∧⋎p ¬⋎p r)
■

ⓈHOLCONST
│ $⦏⇒⋎p⦎ : ('s, 'v) PPMS → ('s, 'v) PPMS → ('s, 'v) PPMS
├──────
│  ∀l r⦁ l ⇒⋎p r = r ∨⋎p ¬⋎p l
■

ⓈHOLCONST
│ $⦏⇔⋎p⦎ : ('s, 'v) PPMS → ('s, 'v) PPMS → ('s, 'v) PPMS
├──────
│  ∀l r⦁ l ⇔⋎p r = (l ⇒⋎p r) ∧⋎p (r ⇒⋎p l)
■

ⓈHOLCONST
│ ⦏∀⋎p⦎: 'v → ('s, 'v) PPMS → ('s, 'v) PPMS
├──────
│ ∀ s p ⦁ ∀⋎p s p = ¬⋎p (∃⋎p s (¬⋎p p))
■

\ignore{
=SML
val fof_def = get_spec ⌜fof⌝;
val foc_def = get_spec ⌜foc⌝;
val fop_def = get_spec ⌜fop⌝;
val ∨⋎p_def = get_spec ⌜$∨⋎p⌝;
val ⇒⋎p_def = get_spec ⌜$⇒⋎p⌝;
val ⇔⋎p_def = get_spec ⌜$⇔⋎p⌝;
val ∀⋎p_def = get_spec ⌜∀⋎p⌝;
=TEX

=SML
set_goal([], ⌜∀ppms1 ms⦁ foc ppms1 ms ⇔ ∀va⦁ Fst ms = {} ∨ (∀v⦁ va v ∈ Fst ms) ⇒ ppms ppms1 va ms⌝);
a (once_rewrite_tac [prove_rule [] ⌜ms = (Fst ms, Snd ms)⌝]
	THEN rewrite_tac [foc_def]);
val foc_thm = save_pop_thm "foc_thm";
=TEX

=SML
set_goal([], ⌜∀s1 s2: 'v ⦁
	  fof (s1 =⋎p s2)
	∧ fof (s1 ∈⋎p s2)⌝);
a (REPEAT strip_tac THEN TRY (rewrite_tac [fof_def]
	THEN REPEAT strip_tac
	THEN all_fc_tac [fof_def]
	THEN asm_rewrite_tac[]));
val fof_base_clauses = save_pop_thm "fof_base_clauses";
=TEX
=SML
set_goal([], ⌜∀s s1; p1 p2: ('s, 'v) PPMS ⦁
	  (fof p1 ⇒ fof (¬⋎p p1)
		∧ fof (∃⋎p s p1)
		∧ fof (∀⋎p s p1))
	 ∧ (fof p1 ∧ fof p2 ⇒
		  fof (p1 ∧⋎p p2)
		∧ fof (p1 ∨⋎p p2)
		∧ fof (p1 ⇒⋎p p2)
		∧ fof (p1 ⇔⋎p p2))⌝);
a (REPEAT strip_tac THEN TRY (rewrite_tac
	[fof_def, ∨⋎p_def, ⇒⋎p_def, ⇔⋎p_def, ∀⋎p_def]
	THEN REPEAT strip_tac
	THEN all_fc_tac [fof_def]));
(* *** Goal "1" *** *)
a (REPEAT (all_asm_fc_tac[]));
(* *** Goal "2" *** *)
a (list_spec_nth_asm_tac 2 [⌜s⌝, ⌜s⌝, ⌜p1⌝, ⌜p1⌝]);
(* *** Goal "3" *** *)
a (lemma_tac ⌜pppms (¬⋎p p1)⌝ 
	THEN1 list_spec_nth_asm_tac 2 [⌜s⌝, ⌜s⌝, ⌜p1⌝, ⌜p1⌝]);
a (lemma_tac ⌜pppms (∃⋎p s (¬⋎p p1))⌝ 
	THEN1 list_spec_nth_asm_tac 3 [⌜s⌝, ⌜s⌝, ⌜¬⋎p p1⌝, ⌜p1⌝]);
a (REPEAT (all_asm_fc_tac[]));
(* *** Goal "4" *** *)
a (REPEAT (all_asm_fc_tac[]));
(* *** Goal "5" *** *)
a (lemma_tac ⌜pppms (¬⋎p p1) ∧ pppms (¬⋎p p2)⌝
	THEN1 (strip_tac THEN REPEAT (all_asm_fc_tac[])));
a (lemma_tac ⌜pppms (¬⋎p p1 ∧⋎p ¬⋎p p2)⌝
	THEN1 (REPEAT (all_asm_fc_tac[])));
a (REPEAT (all_asm_fc_tac[]));
(* *** Goal "6" *** *)
a (lemma_tac ⌜pppms (¬⋎p p1) ∧ pppms (¬⋎p p2)⌝
	THEN1 (strip_tac THEN REPEAT (all_asm_fc_tac[])));
a (lemma_tac ⌜pppms (¬⋎p (¬⋎p p1))⌝
	THEN1 (REPEAT (all_asm_fc_tac[])));
a (list_spec_nth_asm_tac 6 [⌜εx:'v⦁T⌝, ⌜εx:'v⦁T⌝, ⌜¬⋎p p2⌝, ⌜¬⋎p (¬⋎p p1)⌝]);
a (list_spec_nth_asm_tac 11 [⌜εx:'v⦁T⌝, ⌜εx:'v⦁T⌝, ⌜(¬⋎p p2) ∧⋎p (¬⋎p (¬⋎p p1))⌝, ⌜¬⋎p p2⌝]);
(* *** Goal "7" *** *)
a (lemma_tac ⌜pppms (¬⋎p p1) ∧ pppms (¬⋎p p2)⌝
	THEN1 (strip_tac THEN REPEAT (all_asm_fc_tac[])));
a (lemma_tac ⌜pppms (¬⋎p (¬⋎p p1)) ∧ pppms (¬⋎p (¬⋎p p2))⌝
	THEN1 (strip_tac THEN REPEAT (all_asm_fc_tac[])));
a (lemma_tac ⌜pppms (¬⋎p p2 ∧⋎p ¬⋎p (¬⋎p p1))⌝ 
	THEN1 list_spec_nth_asm_tac 7 [⌜εx:'v⦁T⌝, ⌜εx:'v⦁T⌝, ⌜¬⋎p p2⌝, ⌜¬⋎p (¬⋎p p1)⌝]);
a (lemma_tac ⌜pppms (¬⋎p p1 ∧⋎p ¬⋎p (¬⋎p p2))⌝ 
	THEN1 list_spec_nth_asm_tac 8 [⌜εx:'v⦁T⌝, ⌜εx:'v⦁T⌝, ⌜¬⋎p p1⌝, ⌜¬⋎p (¬⋎p p2)⌝]);
a (lemma_tac ⌜pppms (¬⋎p (¬⋎p p2 ∧⋎p ¬⋎p (¬⋎p p1)))⌝ 
	THEN1 list_spec_nth_asm_tac 9 [⌜εx:'v⦁T⌝, ⌜εx:'v⦁T⌝, ⌜¬⋎p p2 ∧⋎p ¬⋎p (¬⋎p p1)⌝, ⌜¬⋎p p2⌝]);
a (lemma_tac ⌜pppms (¬⋎p (¬⋎p p1 ∧⋎p ¬⋎p (¬⋎p p2)))⌝ 
	THEN1 list_spec_nth_asm_tac 10 [⌜εx:'v⦁T⌝, ⌜εx:'v⦁T⌝, ⌜¬⋎p p1 ∧⋎p ¬⋎p (¬⋎p p2)⌝, ⌜¬⋎p p2⌝]);
a (list_spec_nth_asm_tac 11 [⌜εx:'v⦁T⌝, ⌜εx:'v⦁T⌝, ⌜¬⋎p (¬⋎p p2 ∧⋎p ¬⋎p (¬⋎p p1))⌝,
	⌜¬⋎p (¬⋎p p1 ∧⋎p ¬⋎p (¬⋎p p2))⌝]);
val fof_step_clauses = save_pop_thm "fof_step_clauses";
=TEX

=SML
set_goal ([], ⌜fof (∀⋎p "x" (∀⋎p "y" ("x" =⋎p "y" ⇔⋎p ∀⋎p "z" ("z" ∈⋎p "x" ⇔⋎p "z" ∈⋎p "y"))))⌝);
a (abc_tac [fof_step_clauses, fof_base_clauses]);
val fof_extensionality_lemma1 = pop_thm ();
=TEX

=SML
set_goal ([], ⌜fof (∀⋎p "x" (∀⋎p "y" ( ∀⋎p "z" ("z" ∈⋎p "x" ⇔⋎p "z" ∈⋎p "y") ⇒⋎p "x" =⋎p "y")))⌝);
a (REPEAT (CHANGED_T (bc_tac (abc_canon fof_step_clauses)))
	THEN rewrite_tac [fof_base_clauses]);
val fof_extensionality_lemma1b = pop_thm ();
=TEX

=SML
set_goal ([], ⌜fop "" (foc(∀⋎p "x" (∀⋎p "y" ("x" =⋎p "y" ⇔⋎p ∀⋎p "z" ("z" ∈⋎p "x" ⇔⋎p "z" ∈⋎p "y")))))⌝);
a (rewrite_tac [fop_def, foc_def]);
a (∃_tac ⌜(∀⋎p "x" (∀⋎p "y" ("x" =⋎p "y" ⇔⋎p ∀⋎p "z" ("z" ∈⋎p "x" ⇔⋎p "z" ∈⋎p "y"))))⌝
	THEN rewrite_tac [fof_extensionality_lemma1]);
val fof_extensionality_lemma2 = pop_thm ();
=TEX

=SML
set_goal ([], ⌜fop "" (foc(∀⋎p "x" (∀⋎p "y" (∀⋎p "z" ("z" ∈⋎p "x" ⇔⋎p "z" ∈⋎p "y") ⇒⋎p "x" =⋎p "y"))))⌝);
a (rewrite_tac [fop_def, foc_def]);
a (∃_tac ⌜∀⋎p "x" (∀⋎p "y" ( ∀⋎p "z" ("z" ∈⋎p "x" ⇔⋎p "z" ∈⋎p "y") ⇒⋎p "x" =⋎p "y"))⌝
	THEN rewrite_tac [fof_extensionality_lemma1b]);
val fof_extensionality_lemma2b = pop_thm ();
=TEX

=SML
set_goal([], ⌜fop "" extensional⌝);
a (rewrite_tac [fop_def]);
a (∃_tac ⌜∀⋎p "x" (∀⋎p "y" ( ∀⋎p "z" ("z" ∈⋎p "x" ⇔⋎p "z" ∈⋎p "y") ⇒⋎p "x" =⋎p "y"))⌝
	THEN rewrite_tac [fof_extensionality_lemma1b]);
a (rewrite_tac[extensional_thm, foc_thm, eq⋎p_def, ∃⋎p_def, ¬⋎p_def,
	∧⋎p_def, ∨⋎p_def, ∀⋎p_def, ⇒⋎p_def, ⇔⋎p_def, ∈⋎p_def, PPMS_def,
	assign_def]);
a (REPEAT strip_tac
	THEN TRY all_var_elim_asm_tac
	THEN TRY (list_spec_nth_asm_tac 5 [⌜a⌝, ⌜a'⌝]
		THEN (list_spec_nth_asm_tac 4 [⌜u⌝])));
a (list_spec_nth_asm_tac 4 [⌜λv:STRING⦁ εy⦁ y ∈ Fst x⌝]);
(* *** Goal "1" *** *)
a (swap_nth_asm_concl_tac 1
	THEN ε_tac ⌜ε y⦁ y ∈ Fst x⌝
	THEN1 (∃_tac ⌜x'⌝ THEN asm_rewrite_tac[]));
a (asm_rewrite_tac []);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 1 ⌜s⌝);
a (spec_nth_asm_tac 1 ⌜t⌝);
(* *** Goal "2.1" *** *)
a (all_asm_fc_tac []);
(* *** Goal "2.2" *** *)
a (spec_nth_asm_tac 6 ⌜a''⌝);
val fop_extensional_thm = save_pop_thm "fop_extensional_thm";
=TEX

}%ignore

\subsection{Stratified Properties}\label{Stratified Properties}

Some set theories, notably Quine's NF and NFU, are defined using \pindex{stratified\ comprehension} rather than the more usual {\it separation}.
Stratification is a syntactic constraint on the formulae of set theory which can be used to define a set.
This limited class of formulae defines a subset of the first order properties of membership structures, which we will call stratified first order properties.

The {\it semantics} of formulae is unaffected by this constraint, so in defining a stratified property exactly the same constuctors can be used as for non-stratified formulae.
However, when two properties are combined, there must be a check imposed to establish that the combined property is stratified.
This only happens in conjunction, so only one check need be specified.
The check is that there is a type assignment to the free variables of the formula, and this is best performed using a type assignment to the formulae to be combined.
The type assignments are therefore produced intially for the atomic formulae, and then elaborated by each syntactic construction, with a possibility of failure on conjunction.

\subsubsection{Type Assignment}

This version differs from the previous in the following respects:

\begin{itemize}
\item A type assignment is represented as a set of lists of sets of variable names

\item The specification for a stratified property uses a single type assignment given ab initio rather than building up a type assignement as the property is built from the primitive relations.

\item The type assignment does not take account of bound variables, and this means that some terms in which the same variable is used more than once in quantifiers there may not be a type assignment adequate for these purpose.
In these cases it will be necessary to rename some bound variables before a type assignment becomes available.
Because the type assignment comes top down it must contain information about the types of bound variables, which was not the case in the previous version, and since we have not made provision for scoping such information a proper description of the types may not be possible where the same name is bound more than once.

\end{itemize}

=SML
declare_type_abbrev("⦏TA⦎", ["'v"], ⓣ(('v SET)LIST)LIST⌝);
=TEX

In the type assignment each list is a list of sets of type-related variable names.
The members of each set all have the same type, the members of successive sets have successive types.
Separate lists are each independent of each other.
For example the formula ⌜x ∈ y ∧ b ∈ y ∧ v = w ∧ w ∈ u⌝ would have the type assignment
=INLINEFT
 ⌜[[{x;b};{y}]; [{v;w};{u}]]⌝.
=TEX
The well-formedness conditions are simply that no name occurs more than once, i.e. that the sets in each list are pairwise disjoint and the unions of the sets in each list are pairwise disjoint.
To test an atomic formula for correctness relative to a type assignment, restrict the assignment to the names in the formula, then you should have, for ⌜a ∈ b⌝, ⌜[[\{a\};\{b\}]]⌝ and for a = b, ⌜[[\{a;b\}]]⌝ (bearing in mind that order in list displays is signficant but in set displays is not.

To check a formula you need only check each atomic sentence which occurs in it.

Now we formalise this.

\ignore{
 ⓈHOLCONST
│ ⦏ListUnion⦎: 'a SET LIST → 'a SET
├──────
│ ∀ ls⦁ ListUnion ls = Fold $∪ ls {}
 ■
}%ignore

ⓈHOLCONST
│ ⦏Disjoint⦎: 'a SET LIST → BOOL
├──────
│ (Disjoint [] ⇔ T)
│  ∧ ∀ h t⦁ Disjoint (Cons h t) ⇔ ((h ∩ (ListUnion t) = {}) ∧ Disjoint t)
■

ⓈHOLCONST
│ ⦏SetMap⦎: ('a → 'b) → 'a SET → 'b SET
├──────
│ ∀ f s⦁ SetMap f s = {x | ∃y⦁ y ∈ s ∧ x = f y}
■

ⓈHOLCONST
│ ⦏TaDom⦎: 'v TA → 'v SET
├──────
│ ∀ ta⦁ TaDom ta = ListUnion (Map ListUnion ta)
■

ⓈHOLCONST
│ ⦏WfTa⦎: 'v TA → BOOL
├──────
│ ∀ta⦁ WfTa ta ⇔
│	∀⋎L (Map Disjoint ta)
│	∧ Disjoint (Map ListUnion ta)
■

\ignore{
=SML
set_goal([], ⌜∀f⦁ SetMap f {} = {} ∧ ∀s e⦁ SetMap f (Insert e s) = Insert (f e) (SetMap f s)⌝);
a (rewrite_tac [get_spec ⌜SetMap⌝]);
a (REPEAT strip_tac);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
val SetMap_display_thm = save_pop_thm "SetMap_display";

set_goal([], ⌜∀x s t⦁ (Insert x s) ∩ t = ({x} ∩ t) ∪ (s ∩ t)⌝);
a (rewrite_tac[] THEN REPEAT strip_tac);
val Disp_∩_thm = save_pop_thm "Disp_∩_thm";

set_goal([], ⌜∀x y v w⦁ {x} ∩ Insert x y = {x}
	∧ Insert x y ∩ Insert x w = {x} ∪ (y ∩ w)⌝);
a (rewrite_tac[] THEN REPEAT strip_tac);
val Disp_∩_thm2 = save_pop_thm "Disp_∩_thm2";
=IGN
here;

set_merge_pcs["hol1", "'ℤ", "'savedthm_cs_∃_proof"];
set_merge_pcs["hol", "'ℤ", "'savedthm_cs_∃_proof"];
set_goal([],⌜WfTa {[{"x";"b"};{"y"}]; [{"v";"w"};{"u"}]}⌝);
a (rewrite_tac [get_spec ⌜WfTa⌝, SetMap_display_thm, ListUnion_thm,
	get_spec ⌜Disjoint⌝]);
set_goal([], ⌜{"1";"2"} ∩ {"2"} = {"2"}⌝);
a (prove_tac[]);

=TEX
}%ignore

=GFT
ListUnion_thm =
   ⊢ ListUnion [] = {} ∧ (∀ h t⦁ ListUnion (Cons h t) = h ∪ ListUnion t)
=TEX

=SML
declare_infix (310, "◁⋎ta");
=TEX

ⓈHOLCONST
│ $⦏◁⋎ta⦎: 'v SET → 'v TA → 'v TA
├──────
│ ∀ vs ta⦁ vs ◁⋎ta ta = Map (λl⦁ Map ($∩ vs) l) ta
■

We do not need functions to construct these type assignments, we need only to be able to check properties against them.
In fact we only need to check the atomic propositions.

ⓈHOLCONST
│ ⦏Check_eq⦎: 'v TA → 'v → 'v → BOOL
├──────
│ ∀ ta a b⦁ Check_eq ta a b ⇔ {a; b} ◁⋎ta ta = [[{a;b}]]
■

ⓈHOLCONST
│ ⦏Check_∈⦎: 'v TA → 'v → 'v → BOOL
├──────
│ ∀ ta a b⦁ Check_∈ ta a b ⇔ {a; b} ◁⋎ta ta = [[{a};{b}]]
■

ⓈHOLCONST
│ ⦏wtfof⦎: 'v TA → ('s, 'v)PPMS → BOOL
├──────
│ ∀ppms1 ta⦁ wtfof ta ppms1 ⇔
│	∀pppms⦁ (∀s1 s2 p1 p2⦁
│		  (Check_∈ ta s1 s2 ⇒ pppms (s1 ∈⋎p s2))
│		∧ (Check_eq ta s1 s2 ⇒ pppms (s1 =⋎p s2))
│		∧ (pppms p1 ∧ pppms p2
│			⇒ pppms (¬⋎p p1)
│			∧ pppms (∃⋎p s1 p1)
│			∧ pppms (p1 ∧⋎p p2))
│		)
│		⇒ pppms ppms1
■

We are now in a position to define the notion of a stratified first order property.

ⓈHOLCONST
│ ⦏StratProp⦎: ('s, 'v)PPMS → BOOL
├──────
│ ∀ppms1⦁ StratProp ppms1 ⇔ ∃ta⦁ WfTa ta ∧ wtfof ta ppms1
■

My interest in stratified first order properties differs from that in arbitrary first order properties.
My interest is in their use in determining the extension of sets and thence in properties of stratified abstraction for non-well founded set theories (such as NF and NFU).

There are two ways in which I propose to apply the concepts.
The primary consideration so far as this document is concerned is in formalising the property of membership which consists in closure under stratified abstraction.
However, I also want to export to another document in which I am exploring the formalisations of NF and NFU a property suitable for use in expressing an axiom of stratified abstraction.

Lets look first at the first of these and then consider how the second requirement can be satisfied.

To realise the first we need to abstract over a variables (which may or may not actually have free occurrences in the formula corresponding to the property at hand).
This of course is a set abstraction i.e. a comprehension.
It should convert a parameterised property of membership systems to another property which is true of those membership systems in which there exists a set with an appropriate extension.

ⓈHOLCONST
│ ⦏Comp⦎: 'v → ('s,'v)PPMS → ('s,'v)PPMS
├──────
│ ∀v ppms1⦁ Comp v ppms1 = MkPPMS
│	(λva (V, $∈⋎r)⦁
│		∃s⦁ s ∈ V ∧ ∀t⦁ t ∈ V ⇒
│			(t ∈⋎r s ⇔
│			ppms ppms1 (λw⦁ if w = v then t else va w) (V, $∈⋎r)
│			)
│	)
■

This should be understood as taking a formula and returning the formula which asserts the existence of the set with that extension, which differs from an instance of a comprehension axiom only in possibly having free variables.
So we want to close this formula and then quantify over the stratified properties.

We now define the property of membership structures which consists in being closed under stratified comprehension.
This has to have a variable name supplied as a parameter to make the definition type check, but the argument is ignored.

ⓈHOLCONST
│ ⦏StratCompClosed⦎: 'v → ('s)PMS
├──────
│ ∀v ms⦁ StratCompClosed v ms = 
│	∀sp ⦁ StratProp sp ⇒ ∀v:'v⦁ foc (Comp v sp) ms
■

\subsection{An Axiom of Stratified Comprehension}\label{An Axiom of Stratified Comprehension}

In this section we address the formulation of an axiom of stratified comprehension for NF and NFU.

This could be achived using the property {\it StratCompClosed} along the following lines:

=GFT
	⊢ StratCompClosed (Universe, ∈⋎nf)
=TEX

However, if would be nice to have something which is a bit closer to the way an axiom of comprehension would be expected to look, along the lines:

=GFT
	⊢ ∀v p⦁ Stratified p ⇒ ∃s⦁ ∀x⦁ x ∈⋎nf s ⇔ p v x 
=TEX

Where  `v' is a bundle of variables packaged together nas a function.

The property {\it Stratified} would have to be defined in the relevant context since it would have to make use of the correct membership relation.
To make this possible we define here the closest support for this we can, viz. a notion of stratified property which is parameterised by the membership relationship.
Assuming we are axiomatising a set theory as a new type so that the domain of the relationship us the whole type this gives us:

=GFT
	⊢ ∀va v p⦁ Stratified p ⇒ ∃s⦁
		∀x⦁ x ∈⋎nf s ⇔ p $∈⋎nf (λy⦁ if y = v then x else va y) 
=TEX

It is this which we now seek to define.
{\it Stratified} here plays a role similar to that of  StratProp but needs to have a rather different type, e.g.:\\
=INLINEFT
ⓣ('s → 's → BOOL) → (('v → 's) → 's → BOOL) → BOOL⌝
=TEX
\\
whereas {\it StratProp} has type:
=INLINEFT
ⓣ('s,'v)PPMS → BOOL⌝
=TEX
\\
which is similar to \\
=INLINEFT
ⓣ('v → 's) → (('s SET × ('s → 's → BOOL)) → BOOL) → BOOL⌝
=TEX

So here goes:

ⓈHOLCONST
│ ⦏Stratified⦎: (('s → 's → BOOL) → (STRING → 's) → 's SET) → BOOL
├──────
│ ∀p⦁	Stratified p
│	⇔
│	StratProp (MkPPMS λva: STRING + ONE → 's; (V, mr)⦁
│		(va (InR One)) ∈ p mr (va o InL))
■

\section{BOOLEAN VALUED MEMBERSHIP STRUCTURES}\label{BOOLEAN VALUED MEMBERSHIP STRUCTURES}

Following Thomas Zech \cite{jech2002}.

\subsection{Filters}

=SML
open_theory "membership";
force_new_theory "⦏fba⦎";
set_merge_pcs["hol", "'savedthm_cs_∃_proof"];
=TEX

ⓈHOLCONST
│ ⦏Filter⦎: 'a SET SET → BOOL
├──────
│ ∀f⦁	Filter f
│	⇔
│	   ⋃f ∈ f ∧ ¬ {} ∈ f
│	∧  (∀x y⦁ x ∈ f ∧ y ∈ f ⇒ x ∩ y ∈ f)
│	∧  (∀x y⦁ x ⊆ ⋃f ∧ y ⊆ ⋃f ∧ x ∈ f ∧ x ⊆ y ⇒ y ∈ f)
■

ⓈHOLCONST
│ ⦏Ideal⦎: 'a SET SET → BOOL
├──────
│ ∀i⦁	Ideal i
│	⇔
│	   ¬ ⋃ i ∈ i ∧ {} ∈ i
│	∧  (∀x y⦁ x ∈ i ∧ y ∈ i ⇒ x ∪ y ∈ i)
│	∧  (∀x y⦁ x ⊆ ⋃i ∧ y ⊆ ⋃i ∧ x ∈ i ∧ y ⊆ x ⇒ y ∈ i)
■

\ignore{
=IGN
set_goal([], ⌜∀f⦁ Filter f ⇔ Ideal {x | ∃y⦁ y ∈ f ∧ x = (⋃f) \ y}⌝);
a (rewrite_tac [get_spec ⌜Filter⌝, get_spec ⌜Ideal⌝]
	THEN REPEAT strip_tac);

a (REPEAT_N 2 strip_tac);
a (REPEAT_N 5 strip_tac);
=TEX
}%ignore

\subsection{Boolean Algebras}

=SML
open_theory "rbjmisc";
force_new_theory "⦏ba⦎";
new_parent "ordered_sets";
set_merge_pcs["hol", "'ℤ", "'savedthm_cs_∃_proof"];
=TEX

ⓈHOLLABPROD BA─────────────────
│	Car⋎BA	:'a SET;
│	Sum⋎BA	:'a → 'a → 'a;
│	Prod⋎BA	:'a → 'a → 'a;
│	Comp⋎BA	:'a → 'a;
│	Bot⋎BA	:'a;
│	Top⋎BA	:'a
■─────────────────────────

=SML
declare_infix (310, "+⋎B");
declare_infix (320, ".⋎B");
=TEX

ⓈHOLCONST
│ ⦏BooleanAlgebra⦎ : 'a BA → BOOL
├──────
│ ∀ BA⦁
│	BooleanAlgebra BA
│ ⇔	∀B $+⋎B $.⋎B ~⋎B 0⋎B 1⋎B⦁ BA = MkBA B $+⋎B $.⋎B ~⋎B 0⋎B 1⋎B
	⇒ 0⋎B ∈ B ∧ 1⋎B ∈ B
	∧ ∀ u v w⦁ u ∈ B ∧ v ∈ B ∧ w ∈ B
	  ⇒	u +⋎B v ∈ B
	  ∧	u .⋎B v ∈ B
	  ∧	~⋎B u ∈ B
	  ∧	u +⋎B v = v +⋎B u
	  ∧	u +⋎B (v +⋎B w) = (u +⋎B v) +⋎B w
	  ∧	u .⋎B v = v .⋎B u
	  ∧	u .⋎B (v .⋎B w) = (u .⋎B v) .⋎B w
	  ∧	u .⋎B (v +⋎B w) = (u .⋎B v) +⋎B (u .⋎B w)
	  ∧	u .⋎B (v +⋎B w) = (u .⋎B v) +⋎B (u .⋎B w)
	  ∧	u +⋎B (v .⋎B w) = (u +⋎B v) .⋎B (u +⋎B w)
	  ∧	u .⋎B (u +⋎B v) = u
	  ∧	u +⋎B (u .⋎B v) = u
	  ∧	u +⋎B (~⋎B u) = 1⋎B
	  ∧	u .⋎B (~⋎B u) = 0⋎B
■

\ignore{
=SML
set_goal ([], ⌜∀ BA⦁
	BooleanAlgebra BA
 ⇒	∀B $+⋎B $.⋎B ~⋎B 0⋎B 1⋎B⦁ BA = MkBA B $+⋎B $.⋎B ~⋎B 0⋎B 1⋎B
	⇒ 0⋎B ∈ B ∧ 1⋎B ∈ B
	∧ ∀ u v w⦁ u ∈ B ∧ v ∈ B ∧ w ∈ B
	  ⇒	u +⋎B v ∈ B
	  ∧	u .⋎B v ∈ B
	  ∧	~⋎B u ∈ B
	  ∧	u +⋎B v = v +⋎B u
	  ∧	u +⋎B (v +⋎B w) = (u +⋎B v) +⋎B w
	  ∧	u .⋎B v = v .⋎B u
	  ∧	u .⋎B (v .⋎B w) = (u .⋎B v) .⋎B w
	  ∧	u .⋎B (v +⋎B w) = (u .⋎B v) +⋎B (u .⋎B w)
	  ∧	u .⋎B (v +⋎B w) = (u .⋎B v) +⋎B (u .⋎B w)
	  ∧	u +⋎B (v .⋎B w) = (u +⋎B v) .⋎B (u +⋎B w)
	  ∧	u .⋎B (u +⋎B v) = u
	  ∧	u +⋎B (u .⋎B v) = u
	  ∧	u +⋎B (~⋎B u) = 1⋎B
	  ∧	u .⋎B (~⋎B u) = 0⋎B⌝);
a (rewrite_tac[get_spec ⌜BooleanAlgebra⌝]);
val BA_fc_lem1 = save_pop_thm "BA_fc_lem1";

set_goal([], ⌜∀ BA B $+⋎B $.⋎B ~⋎B 0⋎B 1⋎B⦁
	BooleanAlgebra BA ∧ BA = MkBA B $+⋎B $.⋎B ~⋎B 0⋎B 1⋎B
	⇒ 0⋎B ∈ B ∧ 1⋎B ∈ B
	∧ ∀ u v w⦁ u ∈ B ∧ v ∈ B ∧ w ∈ B
	  ⇒	u +⋎B v ∈ B
	  ∧	u .⋎B v ∈ B
	  ∧	~⋎B u ∈ B
	  ∧	u +⋎B v = v +⋎B u
	  ∧	u +⋎B (v +⋎B w) = (u +⋎B v) +⋎B w
	  ∧	u .⋎B v = v .⋎B u
	  ∧	u .⋎B (v .⋎B w) = (u .⋎B v) .⋎B w
	  ∧	u .⋎B (v +⋎B w) = (u .⋎B v) +⋎B (u .⋎B w)
	  ∧	u .⋎B (v +⋎B w) = (u .⋎B v) +⋎B (u .⋎B w)
	  ∧	u +⋎B (v .⋎B w) = (u +⋎B v) .⋎B (u +⋎B w)
	  ∧	u .⋎B (u +⋎B v) = u
	  ∧	u +⋎B (u .⋎B v) = u
	  ∧	u +⋎B (~⋎B u) = 1⋎B
	  ∧	u .⋎B (~⋎B u) = 0⋎B⌝);
a (REPEAT (∀_tac ORELSE ⇒_tac));
a (strip_asm_tac (all_∀_elim BA_fc_lem1));
a (list_spec_nth_asm_tac 1 [⌜B⌝, ⌜$+⋎B⌝, ⌜$.⋎B⌝, ⌜~⋎B⌝, ⌜0⋎B⌝, ⌜1⋎B⌝]);
a (REPEAT_N 6 strip_tac);
a (list_spec_nth_asm_tac 4 [⌜u⌝, ⌜v⌝, ⌜w⌝]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
val BA_fc_lem2 = save_pop_thm("BA_fc_lem2");

val BA_fc_lem3 = save_thm("BA_fc_lem3", all_∀_elim BA_fc_lem2);

set_goal ([], ⌜∀BA B $+⋎B $.⋎B ~⋎B 0⋎B 1⋎B⦁
	BooleanAlgebra BA ∧ BA = MkBA B $+⋎B $.⋎B ~⋎B 0⋎B 1⋎B
 ⇒	∀ u v w⦁ u ∈ B ∧ v ∈ B ∧ w ∈ B
	  ⇒ u +⋎B 0⋎B = u
	  ∧ u .⋎B 1⋎B = u
	  ∧ u .⋎B u = u
	  ∧ u +⋎B u = u
	  ∧ u .⋎B 0⋎B = 0⋎B
	  ∧ u +⋎B 1⋎B = 1⋎B⌝);
a (REPEAT (∀_tac ORELSE ⇒_tac));
a (strip_asm_tac BA_fc_lem3);
a (list_spec_nth_asm_tac 1 [⌜u⌝, ⌜v⌝, ⌜w⌝]);
a (lemma_tac ⌜u +⋎B 0⋎B = u⌝);
(* *** Goal "1" *** *)
a (list_spec_nth_asm_tac 14 [⌜u⌝, ⌜~⋎B u⌝, ⌜w⌝]);
a (GET_NTH_ASM_T 11 (rewrite_thm_tac o map_eq_sym_rule));
a strip_tac;
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
a (lemma_tac ⌜u .⋎B 1⋎B = u⌝);
(* *** Goal "2.1" *** *)
a (list_spec_nth_asm_tac 15 [⌜u⌝, ⌜~⋎B u⌝, ⌜w⌝]);
a (GET_NTH_ASM_T 13 (rewrite_thm_tac o map_eq_sym_rule));
a strip_tac;
(* *** Goal "2.2" *** *)
a (asm_rewrite_tac[]);
a (lemma_tac ⌜u .⋎B u = u⌝);
(* *** Goal "2.2.1" *** *)
a (LEMMA_T ⌜u .⋎B u = u .⋎B (u +⋎B 0⋎B)⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a (list_spec_nth_asm_tac 16 [⌜u⌝, ⌜0⋎B⌝, ⌜w⌝]);
(* *** Goal "2.2.2" *** *)
a (asm_rewrite_tac[]);
a (lemma_tac ⌜u +⋎B u = u⌝);
(* *** Goal "2.2.2.1" *** *)
a (LEMMA_T ⌜u +⋎B u = u +⋎B (u .⋎B 1⋎B)⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a (list_spec_nth_asm_tac 17 [⌜u⌝, ⌜1⋎B⌝, ⌜w⌝]);
(* *** Goal "2.2.2.2" *** *)
a (asm_rewrite_tac[]);
a (lemma_tac ⌜u .⋎B 0⋎B = 0⋎B⌝);
(* *** Goal "2.2.2.2.1" *** *)
a (LEMMA_T ⌜u .⋎B 0⋎B = (u +⋎B 0⋎B) .⋎B 0⋎B⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a (list_spec_nth_asm_tac 18 [⌜u⌝, ⌜0⋎B⌝, ⌜w⌝]);
a (GET_NTH_ASM_T 8 (rewrite_thm_tac));
a (lemma_tac ⌜0⋎B +⋎B u ∈ B⌝
	THEN1 (list_spec_nth_asm_tac 28 [⌜0⋎B⌝, ⌜u⌝, ⌜w⌝]));
a (list_spec_nth_asm_tac 29 [⌜0⋎B +⋎B u⌝, ⌜0⋎B⌝, ⌜w⌝]);
a (asm_rewrite_tac[]);
a (list_spec_nth_asm_tac 42 [⌜0⋎B⌝, ⌜u⌝, ⌜w⌝]);
(* *** Goal "2.2.2.2.2" *** *)
a (asm_rewrite_tac[]);
a (LEMMA_T ⌜u +⋎B 1⋎B = (u .⋎B 1⋎B) +⋎B 1⋎B⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a (list_spec_nth_asm_tac 19 [⌜u⌝, ⌜1⋎B⌝, ⌜w⌝]);
a (GET_NTH_ASM_T 6 (rewrite_thm_tac));
a (lemma_tac ⌜1⋎B .⋎B u ∈ B⌝
	THEN1 (list_spec_nth_asm_tac 29 [⌜1⋎B⌝, ⌜u⌝, ⌜w⌝]));
a (list_spec_nth_asm_tac 30 [⌜1⋎B .⋎B u⌝, ⌜1⋎B⌝, ⌜w⌝]);
a (asm_rewrite_tac[]);
a (list_spec_nth_asm_tac 43 [⌜1⋎B⌝, ⌜u⌝, ⌜w⌝]);
val BA_lem4 = save_pop_thm "BA_lem4";
=TEX
}%ignore

=SML
declare_infix(310, "-⋎B");
declare_infix(300, "≤⋎B");
=TEX

=SML
set_flag ("pp_show_HOL_types", false);
=TEX

\subsection{Filters and Ideals over Boolean Algebras}

ⓈHOLCONST
│ ⦏Filter⋎BA⦎: 'a BA → 'a SET → BOOL
├──────
│ ∀BA f ⦁
│	Filter⋎BA BA f
│	⇔
	∀B $+⋎B $.⋎B ~⋎B 0⋎B 1⋎B⦁
	(MkBA B $+⋎B $.⋎B ~⋎B 0⋎B 1⋎B) = BA
	⇒
│	let x ≤⋎B y = x .⋎B (~⋎B y) = 0⋎B
│	in f ⊆ B	   
│	∧  1⋎B ∈ f ∧ ¬ 0⋎B ∈ f
│	∧  (∀x y⦁ x ∈ f ∧ y ∈ f ⇒ x .⋎B y ∈ f)
│	∧  (∀x y⦁ x ∈ f ∧ y ∈ B ∧ x ≤⋎B y ⇒ y ∈ f)
■

ⓈHOLCONST
│ ⦏Ideal⋎BA⦎: 'a BA → 'a SET → BOOL
├──────
│ ∀BA i⦁
│	Ideal⋎BA BA i
│	⇔
│	∀B $+⋎B $.⋎B ~⋎B 0⋎B 1⋎B⦁
│	(MkBA B $+⋎B $.⋎B ~⋎B 0⋎B 1⋎B) = BA
│	⇒
│	let  x ≤⋎B y = x .⋎B (~⋎B y) = 0⋎B
│	in i ⊆ B
│	∧  ¬ 1⋎B ∈ i ∧ 0⋎B ∈ i
│	∧  (∀x y⦁ x ∈ i ∧ y ∈ i ⇒ x +⋎B y ∈ i)
│	∧  (∀x y⦁ y ∈ i ∧ x ∈ B ∧ x ≤⋎B y ⇒ x ∈ i)
■


\subsection{Boolean Valued Interpretations}

Here we define the rather more elaborate structures which we generalise the notion of a membership structure.

They do so in two distinct ways.
Firstly, instead of allowing only classical relations as interpretations of the membership relation, they allow membership to be interpreted by functions into some boolean algebra.
Secondly. they allow that equality be similarly liberalised.
In a classical membership structure membership is not mentioned, and is assumed to be the standard equality, in which two elements of the domain are equal as sets if and only if they are in fact the same element.

=SML
open_theory "ba";
force_new_theory "⦏bvi⦎";
=TEX

ⓈHOLLABPROD BI─────────────────
│	U⋎BI	:'a SET;
│	BA⋎BI	:'b BA;
│	Eq⋎BI	:'a → 'a → 'b;
│	Mem⋎BI	:'a → 'a → 'b
■─────────────────────────

=SML
declare_infix (300, "=⋎B");
declare_infix (300, "∈⋎B");
=TEX

This should require that the boolean algebra be complete.

ⓈHOLCONST
│ ⦏BoolInterp⦎ : ('a, 'b) BI → BOOL
├──────
│ ∀ i⦁
│	BoolInterp i
│ ⇔	∀A x y z v w $=⋎B $∈⋎B (B, $+⋎B, $.⋎B, ~⋎B, 0⋎B, 1⋎B)⦁
│	  A = U⋎BI i ∧ MkBA B $+⋎B $.⋎B ~⋎B 0⋎B 1⋎B = BA⋎BI i
│	∧ $=⋎B = Eq⋎BI i ∧ $∈⋎B =  Mem⋎BI i
│	∧ x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ v ∈ A ∧ w ∈ A
│	⇒
│	let  x ≤⋎B y = x .⋎B (~⋎B y) = 0⋎B
│	in 	x =⋎B x = 1⋎B
│	∧	x =⋎B y = y =⋎B x
│	∧	(x =⋎B y) .⋎B  (y =⋎B z) ≤⋎B x =⋎B z
│	∧	(x ∈⋎B y) .⋎B  (v =⋎B x) .⋎B  (w =⋎B y) ≤⋎B v ∈⋎B w
■

\section{MEMBERSHIP FUNCTORS}\label{MEMBERSHIP FUNCTORS}

One way of obtaining an interpretation of set theory is as follows:

\begin{enumerate}
\item chose some domain of set representatives
\item define a membership relation over the representatives
\end{enumerate}

If the intended interpretation is not well-founded, the natural definition of the membership relation over the representatives may be recursive, and there will be a problem in establishing that the recursion is well-founded or in establishing by some other means that the functor encapsulating the recursive definition has a fixed point.

This approach to constructing interpretations of set theory is adopted in \cite{rbjt026} using representatives which are definitions of properties in an infinitary set theory, but there are some general results in relation to functors over membership relations which are useful there but do not belong in that specific context.

We introduce a new theory for this material:

=SML
open_theory "membership";
force_new_theory "⦏memfunct⦎";
force_new_pc "⦏'memfunct⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'memfunct";
set_merge_pcs ["hol", "'memfunct"];
=TEX


\appendix

%%%%
%%%%
{\let\Section\section
\def\section#1{\Section{#1}\label{membership.th}}
\include{membership.th}
\def\section#1{\Section{#1}\label{fba.th}}
\include{fba.th}
\def\section#1{\Section{#1}\label{ba.th}}
\include{ba.th}
\def\section#1{\Section{#1}\label{bvi.th}}
\include{bvi.th}
\def\section#1{\Section{#1}\label{memfunct.th}}
\include{memfunct.th}
}  %\let

\twocolumn[\section{INDEX}\label{INDEX}]
{\small\printindex}

\end{document}
