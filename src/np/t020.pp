=IGN
$Id: t020.doc,v 1.11 2013/01/28 19:30:14 rbj Exp $
open_theory "poly-sets";
set_merge_pcs ["hol1", "'savedthm_cs_∃_proof"];
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\usepackage{A4}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}

\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{PolySet Theory}
\makeindex

\author{Roger Bishop Jones}
\date{\ }
\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
This document is concerned with the specification of an interpretation of the first order language of set theory.

The purpose of this is to provide an ontological basis for foundation systems suitable for the formal derivation of mathematics.
The ontology is to include the pure well-founded sets of rank up to some arbitrary large cardinal together with the graphs of the polymorphic functions definable in a polymorphic functional language such as ML, and the categories corresponding to abstract mathematical concepts.

The interpretation is constructed by defining ``names'' or ``representatives'' for the sets in the domain of discourse by transfinite inductive definition in the context of a suitably large collection of pure well-founded sets.
A membership relation and a equality congruence are then defined simultaneously over this domain, so that the domain of the new intepretation is a collection of equivalence classes of these representatives.
Relative to a natural semantic for the names, the definitions of these is not well-founded, and special measures are required to obtain a fixed point for the defining functional.
These include choice of a suitable boolean algebra of truth values for the defined relations, and the location of a suitable subdomain of the representatives.

\end{abstract}

\vfill

\begin{centering}
{\footnotesize
Created 2006/10/15

Last Changed $ $Date: 2013/01/28 19:30:14 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t020.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t020.pdf}

$ $Id: t020.doc,v 1.11 2013/01/28 19:30:14 rbj Exp $ $

\copyright\  Roger Bishop Jones; Licenced under Gnu LGPL \\

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

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\newpage
\section{INTRODUCTION}

The work here involves an attempt to realise a couple of ontological desiderata in set theory, using several methods which may be of more general interest.

It is at present speculative and incomplete.

\subsection{Desiderata}

The two desiderata are:

\begin{enumerate}
\item that there exist sets whose extensions are the graphs of the polymorphic functions definable in ML (e.g. the identity function)
\item that there be sets which represent categories of abstract objects (e.g. the category of groups, not just the category of small groups)
\end{enumerate}

Note in respect of the first desiderata that a single graph is required for each polymorphic function, not a family of graphs one for each monomorphic instance.
The second desiderata I usually think of in terms of having a well populated category of categories which is a member of itself.

\subsection{Ontological Intuitions}

This investigation was provoked by a single intuition about the nature of ML polymorphism.

Polymorphic functions in ML are implemented without benefit of any runtime type information.
This is possible because the type system ensures that the only thing which a function will ever do with a value whose type is completely unknown is transcribe it.
These functions therefore look only at relatively superficial aspects of the structure of their arguments, and the extent of this structure is determined by the type constructors in the type of the argument.
Once the function has probed through this structure to reach values whose types are plain type variables it will probe no deeper.

The implication of this for the graph of the function is that at certain points in the structure of a set in the graph you can plug in any set whatever, as if all the portions of the structure which correspond to values whose type is a type variable were replaced by wild-cards.

To realise this we envisage ``poly-sets'' which are effectively very large unions, the union of families of sets indexed by products of the universe of the set theory.

Putting aside for a moment the graph of these sets, we can consider how such a set might be represented, or named.
This can be done by using ordinals as wild-cards.
We allow any number of such wildcards, i.e. the set of wild-cards used in such a representative will be an ordinal, and to avoid confusion, any occurrence of an ordinal which is intended as an ordinal rather than a wild-card will be increased by adding on the left the number of wild-cards.

A poly set might then be represented by an ordered pair.
On the left a ordinal which tells us how many ordinals are used as wild-card.
On the right a set of sets, each of which is a poly set interpreted as a pattern.
The set represented has as members any poly-set which can be obtained by substituting values for the wild-cards in one of the members on the right (at the same reducing appropriate the magnitude of the ordinals which are not in use as wild-cards).

Note that ordinary well-founded sets are a special case of these poly-sets, in which there happen to be no wild-cards.

This cleans up to give us an ontology which combines the a nice collection of well-founded sets with a similar number of non-sell-founded sets which include the polymorphic functions definable in ML (the construction is straightforward, the proofs remain to be seen).
It is doubtful that it covers all that we might hope to see in a category of categories.

It does not provide complements.
It does include the complement of the empty set, (the set of all sets) but I have not yet come across an other complementary pairs.

When I first thought about how to fill out the ontology, I decided to provide representatives for all the first order properties, as if we were going to allow full comprehension.
The semantics for this could be defined as a functor over membership structures even if there could be no fixed point to this functor (because of Russell's paradox).
I first approached this quite directly, encoding the syntax of first order set theory.
Then I decided that my representation for polysets looked like an infinitary union and hence provided something rather like existential quantification and that simply adding negation might suffice.
After pondering this for a while I concluded that this was too spartan to work.
It wasn't clear that the polysets were close enough to existential quantification, and even if it was, we would still give only first order logic with equality, we would need to do something for the membership relation.

My present tack is to modify the patterns to make them more definitely yield infinitary unions over the universe, build complementation into that to give the effect full first order logic, and to make the quantification effectively over a dependent product which would allow the equality and membership relations to be definable.

\subsection{The Strategy}

Not all of this is settled.
I will describe first the bits which seem to me most definite.

Firstly, the representatives are to be a suitable inductive datatype which includes sets of patterns for the polymorphic functions which also in the special non-polymorphic cases represent the well-founded sets, and which also includes representatives for complements.

We aim to define a boolean valued interpretation of set theory using these representatives.
Such a boolean valued interpretation will consist of:

\begin{itemize}
\item a boolean valued congruence relation
\item a 
\end{itemize}


\section{THE INTERPRETATION}

First we have a new theory.

=SML
open_theory "GST";
force_new_theory "poly-sets";
new_parent "fixp";
new_parent "bvi";
set_merge_pcs ["hol1", "'savedthm_cs_∃_proof"];
=TEX

The plan is:

\begin{itemize}
\item In a well-founded set theory construct a set of representatives for poly-sets.

\item Define a functor over boolean valued interpretations which captures the intended meaning of the representatives and the notion of extensional equivalence over these representatives.

\item Explore the partial fixed points of this functor.

\end{itemize}

\subsection{The Set of Poly-Set Reps}

This is done in stages.

First the a subset of the Poly-Set representatives isomorphic to the Von Neumann ordinals in well-founded set theory is defined.
Then the full set of Poly-Set representatives is defined using that special representation of ordinals.

The set is defined inductively as a fixed point of a monotonic function.

ⓈHOLCONST
│ ⦏mk_PSR⦎: GST × GST → GST
├──────
│ ∀or s⦁ mk_PSR (or, s) = or ↦⋎g s 
■

The following functor maps a set of sets to the set of PSRs which can be constructed from it (assuming that they are all themselves PSRs).

ⓈHOLCONST
│ ⦏PSR_func⦎: GST SET → GST SET
├──────
│ ∀gss⦁ PSR_func gss =
│	{s
│	| ∃or psrs⦁ Ordinal or
│	∧ X⋎g psrs ⊆ gss
│	∧ s = mk_PSR (or, psrs)}
■

Now we take the least fixed point.

ⓈHOLCONST
│ ⦏PSR⦎: GST SET
├──────
│ PSR = HeredFun PSR_func
■

\ignore{
=SML
push_pc "hol";
set_goal([], ⌜∀s⦁ (∀t⦁ t ⊆ s ⇒ PSR_func t ⊆ s) ⇒ PSR ⊆ s⌝);
a (rewrite_tac [get_spec ⌜PSR⌝, HeredFun_induction_thm1]);
val PSR_induction_thm = save_pop_thm "PSR_induction_thm";
pop_pc();
=TEX
}%ignore

=GFT
PSR_induction_thm =
	⊢ ∀ s⦁ (∀ t⦁ t ⊆ s ⇒ PSR_func t ⊆ s) ⇒ PSR ⊆ s
=TEX

\subsection{The Functor}

The semantics of these polyset representatives can be captured by a functor over boolean valued interpretations.
To get an interpretation we would then need to find a fixed point for the functor.

\section{POLY-SETS}




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
\include{poly-sets.th}
}  %\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
