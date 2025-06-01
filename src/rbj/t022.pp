=IGN
$Id: t022.doc,v 1.8 2010/08/13 10:57:22 rbj Exp $
open_theory "GST";
set_merge_pcs ["hol1", "'savedthm_cs_∃_proof"];
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

\title{Surreal Geometric Analysis}
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
This document is an exploration into formalisation of geometric algebra and analysis using surreal numbers instead of real numbers.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2006/12/04

Last Change $ $Date: 2010/08/13 10:57:22 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t022.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t022.pdf}

$ $Id: t022.doc,v 1.8 2010/08/13 10:57:22 rbj Exp $ $

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

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\newpage
\section{INTRODUCTION}

This document is a toe in the water to get a first idea of how hard it is to work with surreal numbers, with the objective ultimately of providing a formal basis for theoretical physics based on geometric algebra.

The stages envisaged are:

\begin{enumerate}
\item The theory of surreals
\item Geometric algebra (GA(0, $\infty$)) based on surreals.
\item Geometric analysis
\item General Relativity and other theoretical physics
\end{enumerate}

We have here also, pro-tem, an axiomatic set theory in which to construct the surreals (but which I intend to put to other uses as well).

\subsection{Preliminary Discussion}

My motivations for undertaking this exploration fall into two categories.

The most important of these, which may however be misconceived, are concerned with possible problems in the formalisation of Physics.

The less important motivation is simply curiosity, which arises I think for me primarily because of the relationship between the surreal numbers and the underlying set theory.

I will discuss these two kinds of motivation separately.

\subsubsection{Motivations Connected with the Formalisation of Physics}

I am interested in the formalisation of Physics:
\begin{itemize}
\item as an exercise in the scientific application of formal methods worthwhile in its own right
\item as a way of approaching related philosophical problems (which I am inclined to class as \emph{metaphysics})
\item as a part of that larger project in the automation of reason which we associate with Leibniz (his \emph{lingua characteristica} and \emph{calculus ratiocinator}). 
\end{itemize}

There are some (rather slender) reasons which have encouraged me to consider whether the analysis on which a formalisation of physics is based might best be a \emph{non-standard} analysis, and some other tenuous reasons for considering that such a non-standard analysis might best be based on the surreal numbers.

My provocations for considering non-standard analysis are as follows:

\begin{itemize}
\item In the course of my investigations to date (see \cite{rbjt002}) I was offered by Rob Arthan some input on differential geometry (see \cite{rbjt003}), in which a centrepiece is the Frechet derivative.
The Frechet generalises the derivative from ordinary analysis to a derivative over functions over vector spaces.
The formulation shown in \cite{rbjt003} delivers for total function between two vector spaces a derivative at some point, if the function is differentiable at that point.
In effect, we begin with a total function, but may well end up with a partial function (the derivative), and this renders awkward the iteration of the function to obtain nth derivatives.
Since the result of the first application need not be a total function, we may not be able to apply the function again.

One way of resolving this problem is shown also in \cite{rbjt003} which is to define the Frechet derivative as delivering a total function of which the value at points where the argument function is not differentiable will be unknown.
This can then be iterated.

Whether this is the right way to deal with iterated differentiation of functions which are not everywhere differentiable unclear.

\item

One of the principle targets for the formalisation of physics envisaged is the theories of special and general relativity, partly because of their relevance to the metaphysics of space and time.
One of the interesting features of the general theory is the occurence of singularities (black holes) under certain circumstances.
Strictly speaking the occurence of a singularity is a breakdown of the theory rather than a bona-fide solution to the differential equations.
In informal mathematical treatments one can safely reason about these partial solutions to the equations, but in a formal treatment it will be necessary to spell out in detail what such a partial solution is so that it can be reasoned about with complete formal rigour.
This might turn out to be awkward and complicated.

The possibility that the use of non-standard analysis might admit full solutions to the equations in these circumstances arises.
If, in the interesting cases where the equations have partial solutions under standard analysis the equations had full solutions under non-standard analysis, then this might provide a better route to formalisation of the theory.

\end{itemize}

Two questions then arise.
First is this the case, and, if the answer to that question is not known, what is the best way to go about getting closer to an answer.

Up until recently I have not had positive views about non-standard analysis and my reasons for this were:
\begin{itemize}
\item I have not been well motivated by the usual grounds offered for adopting non-standard analysis.
It is usually offered as permitting the rigorous use of infinitesimal in accounts of analysis, which corresponds to the best original formulations and is supposed to be more intelligible than the later epsilon-delta formulations which were for about a century thought to be the only way to make these matters fully rigorous.

For my part however, the epsilon-delta formulation has always seemed to me clearer, not least because I could not begin to understand the treatment in terms of infinitesimals until I could understand the number system in which infinitesimals feature.

\item
I have found it much more difficult to get an intuitive grasp of what the numbers used in non-standard analysis are.
The fact that they are arrived at as a non-standard model of the first order axiom system definitely did not recommend it to me.
\end{itemize}

Conway's surreal numbers seemed to me until recently disconnected from these issues.
I thought that to do analysis with them it was necessary to separate out a subset which corresponded to the numbers either of non-standard or of standard analysis (the hyper-reals or the reals), and this promised to be a difficult task.
My interest in the surreal numbers had not been much exercised by the possibility of using them for analysis.

However, in December 2006 I heard a talk by Philip Ehrlich in which he claimed that contrary to what Conway had suggested it was not necessary to separate out a subdomain for non-standard analysis, the surreal numbers as a whole provided a model for non-standard analysis.
This made me immediately consider the possibility of using the surreals as a base for a non-standard analysis to be used in the formalisation of physics.

The surreals can be constructed by two different methods both of which seemed to me to give clear intuitive semantic basis, and if non-standard analysis offered a smoother way to deal with singularities then it was worth serious consideration.

This provoked the explorations in this document, which I undertook at first with a rather hazy indifference to the question whether non-standard analysis really would be any better for physics than standard analysis.

My present view is that formalisation is unlikely to contribute (in any sensible timescale) to the question whether non-standard analysis might be good for formalised physics, and that talking to people who understand the physics and the mathematics better than I do would be more likely to clarify that point.

\subsubsection{Some Objections}

I briefly discuss some objections.

First I note two minor misundertandardings on my part which gave rise to easily dismissed objections to the idea that the surreals provide a model for non-standard analysis.

\begin{enumerate}
\item
The first was that since the surreals include the ordinals, and addition on ordinals is non-commutative, the surreals cannot provide a field.
This is a pretty dumb objection, because you only have to look at the definition of addition on the surreals to see that it is commutative.
Of course that means that addition over the surreals does not agree with ordinal addition when restricted to the surreals which correspond to the ordinals, but there is nothing to stop the usual ordinal addition from being defined as a separate operation.
\item
A second minor point to note is that the surreals are not complete in the same way as the reals.
But non-standard analysis is based on a non-standard model of the field axioms, the hyperreals are not equired to be complete.
There is a different completeness axiom for the surreals, and it should be possible for formulate one which corresponds to completeness of the real subset fo the surreals (supposing as I am guessing at present that the reals are the finite surreals of rank not greater than $2\omega$. 
\item
Finally, even in non-standard analysis you can't divide by zero.
Singularities may not go away.
\end{enumerate}

It now appears to me the grounds I have for thinking that there might be solutions in non-standard analysis corresponding to situations involving singularities in general relativity are very slender indeed.
I need to check out whether anyone has tried doing relativity with non-standard analysis.

Rob Arthan has expressed to me strong objections to the idea that surreals might be applicable in physics on the grounds that the surreals go beyond his geometric intuitions.
Though I can give some credence to this objection, there are many aspects of modern physics which go beyond our intuitive expectations about the nature of space and time.
My own intuitions object to the idea that there might really be singularities in the physical universe, but the theories I seek to formalise embrace that possibility and must therefore depend on a conception of space and time which goes beyond my intuitions.
The possibilities which arise once gravitational fields are eliminated by incorporation into the curvature of space time (for example, worm holes) seem to go beyond anything for which we have direct observational evidence.






\subsubsection{Other Motivations}

My other motivation I declared as curiousity, but since it probably has the upper hand at present it may be worth my while to tease that out a bit more.

A principal cause of the curiousity is the fact that the surreals expand to the size of the set theoretic universe in which they are formulated.
There is therefore some special difficulty in an axiomatic formulation independent of set theory, and also the rather bizarre possibility that such a formulation might itself technically suffice as a foundation for mathematics.

When doing mathematics in HOL (Higher Order Logic) an axiom of infinity is required.
If you want to do set theory in HOL (apart from the limited theory obtained by treated properties as typed sets) you either need to axiomatise the set theory, or else you need a stronger axiom of infinity.
This latter option is philosophically and technically interesting (independently of considering surreal numbers), but also interacts with the problem of formalising surreals in HOL.
This is because the surreals include the ordinals, and you have to find a way of saying how many ordinals you are going to get (if this is not to be determined by doing a construction in a set theory and just picking up the ordinals from the set theory).

So this question of how to formulate strong axioms of infinity outside the context of set theory (strong enough to assert that the cardinality of the indviduals is some large cardinal) and the question of whether and how such a strong axiom of infinity might provide a basis for a foundational theory (such as a set theory) is of interest.
Bear in mind that I am working in the context of a Higher Order Logic, so if standard semantics of set theory is factorised into two parts (think of iterative construction of the cumulative heirarchy of sets), taking at each rank the set of {\it all} sets which can be constructed from sets of lower rank, and then running through sufficienlty many ranks to get an adequate population, then the first part of the semantics (all sets of some rank) comes from the higher order logic (second order would do), and the second part is what we need a strong axiom of infinity for.
Implicit in this discussion is that you don't have the option to go the whole hog and get {\it ALL} the pure well-founded sets.
You just make successively more outrageous speculations expressed in ever stronger axioms of infinity which place greater lower bound on how far you can go, it is actually incoherent to suppose that the process can be completed. 

\newpage
\section{GALACTIC SET THEORY}

This is basically a higher order set theory with ``universes'' which I insist on calling ``galaxies''.
I'm going to follow an approach first adopted for the formalisation of the theory of PolySets in Isabell-HOL, in which I make maximal use of the set theoretic vocabulary already available in HOL by defining maps from sets in galactic set theory and the sets (subsets of types) already available in HOL,

First we have a new theory.

=SML
open_theory "rbjmisc";
force_new_theory "GST";
new_parent "fixp";
new_parent "ordered_sets";
set_merge_pcs ["hol1", "'savedthm_cs_∃_proof"];
=TEX

Now the new type and the primitive constant, membership:
=SML
new_type("GST", 0);
new_const("∈⋎g", ⓣGST → GST → BOOL⌝);
declare_infix (70, "∈⋎g");
=TEX

The axioms of extensionality and well-foundedness can be stated immediately:

=SML
val ⦏GST_Ext_ax⦎ = new_axiom(["⦏Ext⦎"],
   ⌜∀x y⦁ x=y ⇔ ∀z⦁ z ∈⋎g x ⇔ z ∈⋎g y⌝);

val ⦏GST_wf_ax⦎ = new_axiom(["⦏Wf⦎"],
   ⌜∀P⦁ (∀s⦁ (∀t⦁ t ∈⋎g s ⇒ P t) ⇒ P s) ⇒ ∀x⦁ P x⌝);
=TEX

The final axiom states that every set is a member of a galaxy, and also asserts a more global version of replacement.
First the notion of Galaxy is defined.
To do this I first introduce some mappings between GST's and set so GST's.

ⓈHOLCONST
│ ⦏X⋎g⦎ : GST → GST SET
├─────────
│ ∀s⦁ X⋎g s = {x | x ∈⋎g s}
■

ⓈHOLCONST
│ ⦏XX⋎g⦎ : GST → GST SET SET
├─────────
│ ∀s⦁ XX⋎g s = {x | ∃y⦁ y ∈⋎g s ∧ x = X⋎g y}
■

ⓈHOLCONST
│ ⦏∃⋎g⦎ : GST SET → BOOL
├─────────
│ ∀s⦁ ∃⋎g s ⇔ ∃t⦁ X⋎g t = s
■

\ignore{
=SML
set_goal([],⌜∃C⋎g⦁ ∀s:GST SET⦁ ∃⋎g s ⇒ X⋎g (C⋎g s) = s⌝);
a (rewrite_tac [get_spec ⌜∃⋎g⌝]);
a (prove_∃_tac THEN strip_tac);
a (∃_tac ⌜εt⦁ ∀ x⦁ x ∈ X⋎g t ⇔ x ∈ s'⌝
	THEN strip_tac);
a (ε_tac ⌜εt⦁ ∀ x⦁ x ∈ X⋎g t ⇔ x ∈ s'⌝);
a (∃_tac ⌜t⌝ THEN strip_tac);
a (asm_rewrite_tac[]);
save_cs_∃_thm(pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏C⋎g⦎ : GST SET → GST
├─────────
│ ∀s⦁ ∃⋎g s ⇒ X⋎g (C⋎g s) = s
■

We are now in a position to define galaxies.

ⓈHOLCONST
│ ⦏G⋎g⦎ : GST → BOOL
├─────────
│ ∀s⦁ G⋎g s ⇔ ∀x⦁ x ∈⋎g s ⇒
│	(∃v⦁ v ∈⋎g s ∧ X⋎g v = ⋃(XX⋎g x))
│      ∧ (∃v⦁ v ∈⋎g s ∧ XX⋎g v = {z | z ⊆ X⋎g x})
│      ∧ (∀r⦁ r ∈ Functional ⇒ ∃v⦁ v ∈⋎g x ∧ X⋎g v = r Image (X⋎g x))
■

Galaxies have the following properties:

\ignore{
=SML
set_goal([], ⌜∀x⦁ G⋎g x ⇒ ∃⋎g {}⌝);
a (rewrite_tac (map get_spec [⌜G⋎g⌝, ⌜∃⋎g⌝])
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜εv:GST⦁ v ∈⋎g x⌝);
(* *** Goal "1" *** *)
a (∃_tac ⌜x⌝ THEN rewrite_tac [get_spec ⌜X⋎g⌝] THEN strip_tac);
a (swap_nth_asm_concl_tac 1);
a (ε_tac ⌜ε v⦁ v ∈⋎g x⌝);
a (∃_tac ⌜x'⌝ THEN strip_tac);
(* *** Goal "2" *** *)
a (lemma_tac ⌜{x: GST×GST | F} ∈ Functional⌝
	THEN1 rewrite_tac[get_spec ⌜Functional⌝]);
a (spec_nth_asm_tac 2 ⌜{x: GST×GST | F}⌝);
a (∃_tac ⌜v''⌝ THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜x'⌝);
a (swap_nth_asm_concl_tac 2
	THEN rewrite_tac[get_spec ⌜$Image⌝]);
val G_⇒_∅_lemma = save_pop_thm "G_⇒_∅_lemma";
=TEX
}%ignore

=GFT
G_⇒_∅_lemma =
	⊢ ∀ x⦁ G⋎g x ⇒ ∃⋎g {}
=TEX


The primarily ontological axiom is then:

=SML
val G_ax = new_axiom(["G"], 
   ⌜∀x⦁ ∃g⦁ x ∈⋎g g ∧ G⋎g g⌝);
=TEX

The ontological consequences of this need to be teased out.

\ignore{
=SML
set_goal([], ⌜∃⋎g{}⌝);
a (strip_asm_tac (∀_elim ⌜εx:GST⦁T⌝ G_ax));
a (fc_tac [G_⇒_∅_lemma]);
val ∃_∅_lemma = save_pop_thm "∃_∅_lemma";
=TEX
}%ignore

=GFT
∃_∅_lemma =
	⊢ ∃⋎g {}
=TEX

I might possibly also need a global replacement axiom.

\subsection{Relations and Operations over Sets}

=SML
declare_infix (50, "⊆⋎g");
declare_infix (50, "⊂⋎g");
=TEX

ⓈHOLCONST
│ $⦏⊆⋎g⦎: GST → GST → BOOL
├───────────
│ ∀s t⦁ s ⊆⋎g t ⇔ ∀x⦁ x ∈⋎g s ⇒ x ∈⋎g t
■

ⓈHOLCONST
│ $⦏⊂⋎g⦎: GST → GST → BOOL
├───────────
│ ∀s t⦁ s ⊂⋎g t ⇔ s ⊆⋎g t ∧ ¬ s = t
■


ⓈHOLCONST
│ ⦏⋃⋎g⦎: GST → GST
├───────────
│ ∀s⦁ ⋃⋎g s = C⋎g (⋃ (XX⋎g s))
■

We will need an ordered pair, for which the Wiener-Kuratowski version will do:

ⓈHOLCONST
│ ⦏Wkp⋎g⦎: GST → GST → GST
├───────────
│ ∀l r⦁ Wkp⋎g l r = C⋎g {C⋎g{l}; C⋎g{l;r}}
■

=SML
declare_alias ("↦⋎g", ⌜Wkp⋎g⌝);
declare_infix (1100, "↦⋎g");
=TEX

\subsection{Ordinals}

Zero:

ⓈHOLCONST
│ ⦏∅⋎g⦎: GST
├───────────
│ ∅⋎g = C⋎g {}
■

\ignore{
=SML
set_goal([], ⌜∀x⦁ ¬ x ∈⋎g ∅⋎g⌝);
a (rewrite_tac (map get_spec [⌜∅⋎g⌝]));
a (asm_tac (∃_∅_lemma));
a (FC_T (MAP_EVERY ante_tac) [get_spec ⌜C⋎g⌝]);
a (rewrite_tac (map get_spec [⌜X⋎g⌝]));
val ¬∈∅_thm = save_pop_thm "¬∈∅_thm" ;

set_goal([], ⌜C⋎g {} = ∅⋎g ∧ C⋎g {x|F} = ∅⋎g⌝);
a (rewrite_tac [get_spec ⌜∅⋎g⌝]);
a (LEMMA_T ⌜{x:GST|F} = {}⌝ rewrite_thm_tac THEN1 prove_tac[]);
val C_∅_lemma = save_pop_thm "C_∅_lemma";

set_goal([], ⌜∀s⦁ ∅⋎g ⊆⋎g s⌝);
a (rewrite_tac [get_spec ⌜$⊆⋎g⌝,  ¬∈∅_thm]);
val ⊆⋎g∅_lemma = save_pop_thm "⊆⋎g∅_lemma";
=TEX
}%ignore

=GFT
¬∈∅_thm =
	⊢ ∀ x⦁ ¬ x ∈⋎g ∅⋎g
C_∅_lemma =
	⊢ C⋎g {} = ∅⋎g ∧ C⋎g {x|F} = ∅⋎g
⊆⋎g∅_lemma =
	⊢ ∀ s⦁ ∅⋎g ⊆⋎g s
=TEX

and the successor function:

ⓈHOLCONST
│ ⦏succ⋎g⦎: GST → GST
├───────────
│ ∀on⦁ succ⋎g on = C⋎g {x | x = on ∨ x ∈⋎g on}
■

A property of sets is ordinal closed if it is true of the empty set and is closed under successor and limit constructions.

ⓈHOLCONST
│ ⦏Oclosed⦎: (GST → BOOL) → BOOL
├───────────
│ ∀ps⦁ Oclosed ps ⇔ ps ∅⋎g
│	∧ (∀x⦁ ps x ⇒ ps (succ⋎g x))
│	∧ (∀ss⦁ (∀x⦁ x ∈⋎g ss ⇒ ps x) ⇒ ps (⋃⋎g ss)) 
■

ⓈHOLCONST
│ ⦏Ordinal⦎: GST → BOOL
├───────────
│ ∀s⦁ Ordinal s ⇔ ∀ps⦁ Oclosed ps ⇒ ps s
■

\ignore{
=SML
set_goal([], ⌜Ordinal ∅⋎g⌝);
a (rewrite_tac [get_spec ⌜Ordinal⌝, get_spec ⌜Oclosed⌝]
	THEN REPEAT strip_tac);
val ord_∅_lemma = save_pop_thm "ord_∅_lemma";

set_goal([], ⌜∀s⦁ Ordinal s ⇒ Ordinal (succ⋎g s)⌝);
a (rewrite_tac [get_spec ⌜succ⋎g⌝]);
=TEX
}%ignore

=GFT
ord_∅_lemma =
	⊢ Ordinal ∅⋎g
=TEX

ⓈHOLCONST
│ ⦏1⋎g⦎ ⦏2⋎g⦎: GST
├───────────
│ 1⋎g = succ⋎g ∅⋎g ∧ 2⋎g = succ⋎g 1⋎g 
■


ⓈHOLCONST
│ ⦏Transitive⋎g⦎: GST → BOOL
├───────────
│ ∀s⦁ Transitive⋎g s ⇔ ∀t⦁ t ∈⋎g s ⇒ t ⊆⋎g s
■


\ignore{
=IGN
set_goal([], ⌜∀s⦁ Ordinal s ⇒ Transitive⋎g s⌝);
a (rewrite_tac [get_spec ⌜Transitive⋎g⌝]);

set_goal([], ⌜WellFounded (ordinals, $⊂⋎g)⌝);
a (rewrite_tac [well_founded_induction_thm, get_spec ⌜$⊂⋎g⌝, get_spec ⌜$⊆⋎g⌝]
	THEN REPEAT strip_tac);
a (asm_tac (((rewrite_rule []) o (∀_elim ⌜λx⦁ x ∈ ordinals ⇒ p x⌝)) GST_wf_ax));
a (lemma_tac ⌜∀ s⦁ (∀ t⦁ t ∈⋎g s ⇒ t ∈ ordinals ⇒ p t) ⇒ s ∈ ordinals ⇒ p s⌝
	THEN1 REPEAT strip_tac);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 5 ⌜s⌝);


=TEX
}%ignore

\subsection{Relations and Functions}

ⓈHOLCONST
│ ⦏Relation⦎: GST → BOOL
├───────────
│ ∀s⦁ Relation s ⇔ ∀x⦁ x ∈⋎g s ⇒ ∃l r:GST⦁ x = l ↦⋎g r 
■

\ignore{
=SML
set_goal([], ⌜Relation ∅⋎g⌝);
a (rewrite_tac [get_spec ⌜Relation⌝, ¬∈∅_thm]);
val rel_∅_lemma = save_pop_thm "rel_∅_lemma";
=TEX
}%ignore

=GFT
rel_∅_lemma = 
	⊢ Relation ∅⋎g
=TEX

ⓈHOLCONST
│ ⦏Function⦎: GST → BOOL
├───────────
│ ∀s⦁ Function s ⇔ Relation s ∧ ∀x y z:GST⦁ x ↦⋎g y ∈⋎g s ∧ x ↦⋎g z ∈⋎g s ⇒ y = z   
■

\ignore{
=SML
set_goal([], ⌜Function ∅⋎g⌝);
a (rewrite_tac [get_spec ⌜Function⌝, rel_∅_lemma, ¬∈∅_thm]);
val func_∅_lemma = save_pop_thm "func_∅_lemma";
=TEX
}%ignore

=GFT
func_∅_lemma =
	⊢ Function ∅⋎g
=TEX

ⓈHOLCONST
│ ⦏domain⦎: GST → GST
├───────────
│ ∀s⦁ domain s = C⋎g {x | ∃y⦁ x ↦⋎g y ∈⋎g s}   
■

\ignore{
=SML
set_goal([], ⌜domain ∅⋎g = ∅⋎g⌝);
a (rewrite_tac [get_spec ⌜domain⌝, rel_∅_lemma, ¬∈∅_thm, C_∅_lemma]);
val dom_∅_lemma = save_pop_thm "dom_∅_lemma";
=TEX
}%ignore

=GFT
dom_∅_lemma =
	⊢ domain ∅⋎g = ∅⋎g
=TEX

ⓈHOLCONST
│ ⦏range⦎: GST → GST
├───────────
│ ∀s⦁ range s = C⋎g {y | ∃x⦁ x ↦⋎g y ∈⋎g s}   
■

\ignore{
=SML
set_goal([], ⌜range ∅⋎g = ∅⋎g⌝);
a (rewrite_tac [get_spec ⌜range⌝, rel_∅_lemma, ¬∈∅_thm, C_∅_lemma]);
val ran_∅_lemma = save_pop_thm "ran_∅_lemma";
=TEX
}%ignore

=GFT
ran_∅_lemma =
	⊢ range ∅⋎g = ∅⋎g
=TEX

=SML
declare_infix (900, "×⋎g");
=TEX

Cartesian product:

ⓈHOLCONST
│ $⦏×⋎g⦎: GST → GST → GST
├───────────
│ ∀s t⦁ s ×⋎g t = C⋎g {p:GST | ∃l r⦁ l ∈⋎g s ∧ r ∈⋎g t ∧ p = l ↦⋎g r}   
■

=GFT
=TEX

\subsection{Proof Context}

\ignore{
=SML
set_goal([], ⌜C⋎g {} = ∅⋎g
	∧ C⋎g {x|F} = ∅⋎g
	∧ (∀ s⦁ ∅⋎g ⊆⋎g s)
	∧ Ordinal ∅⋎g
	∧ Relation ∅⋎g
	∧ Function ∅⋎g
	∧ domain ∅⋎g = ∅⋎g
	∧ range ∅⋎g = ∅⋎g
⌝);

a (rewrite_tac [C_∅_lemma, ⊆⋎g∅_lemma, ord_∅_lemma, rel_∅_lemma, func_∅_lemma,
	dom_∅_lemma, ran_∅_lemma]);
val GST_∅_clauses = save_pop_thm "GST_∅_clauses";
=TEX
}%ignore

=GFT
GST_∅_clauses =
   ⊢ C⋎g {} = ∅⋎g
       ∧ C⋎g {x|F} = ∅⋎g
       ∧ (∀ s⦁ ∅⋎g ⊆⋎g s)
       ∧ Ordinal ∅⋎g
       ∧ Relation ∅⋎g
       ∧ Function ∅⋎g
       ∧ domain ∅⋎g = ∅⋎g
       ∧ range ∅⋎g = ∅⋎g
=TEX

\ignore{
=SML
force_new_pc "'GST1";
add_rw_thms [GST_∅_clauses] "'GST1";
add_sc_thms [GST_∅_clauses] "'GST1";
add_st_thms [GST_∅_clauses] "'GST1";
=IGN
force_new_pc "'nfu_f2";
set_rw_eqn_cxt ([(⌜x = y⌝, nfu_f_eq_ext_conv)]) "'nfu_f2";
add_rw_thms [get_spec ⌜$⊆⋎nf⌝, nfu_f_op_ext_clauses2] "'nfu_f2";

set_pr_conv nfu_f_prove_conv "'nfu_f2";
set_pr_tac nfu_f_prove_tac "'nfu_f2";
=SML
set_merge_pcs ["hol1", "'savedthm_cs_∃_proof", "'GST1"];
=TEX
}%ignore

\newpage
\section{SURREAL NUMBERS}

The plan of action here is as follows.
First I speculate on an axiomatisation of the surreal numbers sufficient for non-standard analysis (the surreals of rank up to 2*w would probably suffice).
Then this axiomatisation is evaluated in two different ways.
It is used for the development of parts of the theory of surreals, heading as rapidly as is possible in the direction of analysis.
It is also validated by performing a construction which delivers the axioms.

Three theories are therefore produced.
The first, \emph{sra}, contains the axiomatisation and its development.
The second, \emph{src}, contains the construction preliminary to {\it defining} (in the third theory, \emph{srd}) a type of surreals satisfying the axioms in the first theory.

If this were to go well, then the surreals would be used as a base for something like geometric algebra and analysis would then be developed in that context.
If I can find a way of exploring these latter two options without completing the previous developments then I may do that.
Unfortunately my main motivation for considering the surreal numbers is in the possibility that non-standard analysis would provide a better base than standard analysis for reasoning formally about general relativity, and in particular reasoning about ``solutions'' to the gravitational ``field equations'' in those circumstances in which singularities arise (i.e. black holes).
I really have no idea whether it will help.
Even in non-standard analysis division by zero fails, so possibly the singularities remain.

From that point of view I should be looking at non-standard analysis not at the construction of surreal numbers.


\subsection{An Axiomatisation of the Surreal Numbers}

Since this document is exploratory in nature, and proofs take time, it is worthwhile to explore the axiomatisation of surreal numbers independently of the construction.
This may help in deciding how the development of the theory on the basis of the construction should be done, or it may just be a faster way of deciding whether the entire enterprise is worth the candle.

I understand from Philip Ehrich that he has published an axiomatisation of the surreals independent of set theory in the Journal of Symbolic logic, but I don't have ready access to it so I am importing into this document an axiomatisation which I did a few years back.

For this purpose a new theory ``sra'' is introduced in a context which does not include an axiomatic set theory.
=SML
open_theory "rbjmisc";
force_new_theory "sra";
new_parent "ordered_sets";
set_merge_pcs ["hol1", "'savedthm_cs_∃_proof"];
=TEX

\subsubsection{Primitive Types and Constants}
=SML
new_type ("No", 0);
new_const ("∅⋎s", ⓣNo⌝);
declare_alias ("∅", ⌜∅⋎s⌝);
new_const ("IC", ⓣ(No → BOOL) → No → No⌝);
new_const ("<⋎𝕊", ⓣNo → No → BOOL⌝);
declare_infix (240, "<⋎𝕊");
declare_alias ("<", ⌜$<⋎𝕊⌝);
declare_infix (240, "<<");
=TEX

\subsubsection{Definitions}

ⓈHOLCONST
│	rank: No → No
├
│	∀n⦁ rank n = IC (λx⦁T) n
■
ⓈHOLCONST
│	$<<: No → No → BOOL
├
│	∀n m:No⦁ n << m = rank n <⋎𝕊 rank m
■
=TEX

\subsubsection{The Zero Axiom}
=SML
new_axiom (["SZeroAx"], ⌜∀x⦁ rank x = ∅ ⇔ x = ∅⌝ );
=TEX

\subsubsection{The Cut Axiom}

The following axiom states that, for:

\begin{enumerate}
\item any property p of surreals and
\item surreal n such that p is downward closed on the surreals of lower rank than n
\end{enumerate}

there exists a surreal number (IC p n) such that:

\begin{itemize}
\item (IC p n) is in between the surreals of rank less than n with the property and those of rank less than n without the property, and
\item where p and q define the same cut on the surreals of rank less than n then (IC p n) is the same surreal as (IC q n).
\end{itemize}

=SML
new_axiom (["SCutAx"],
⌜∀p: No → BOOL; n: No⦁
	(∀x y: No⦁ x << n ∧ y << n ∧ x < y ∧ p y ⇒ p x)
	⇒ (∀x: No⦁ x << n ⇒ (p x ⇔ x < (IC p n)) ∧ (¬ p x ⇔ (IC p n) < x))
	∧ (∀q: No → BOOL⦁ (∀x⦁ x << n ⇒ (p x ⇔ q x)) ⇔ (IC p n) = (IC q n))
⌝);
=TEX

\subsubsection{The Induction Axiom}

The following axiom states that for any property p of surreals, if p holds for a surreal n whenever it holds for all the surreals of lower rank than n, then it holds for all surreals.

This is the same as Conway's induction axiom since the union of the two sides of the canonical cuts ("games") on which this axiomatization is based is the set of all numbers of lower rank.

=SML
new_axiom (["SIndAx"], ⌜WellFounded (Universe, $<<)⌝);
=TEX

\subsubsection{Infinity}

This is the ordinal version of my strong infinity for HOL axiom, asserted of the surreals rather than the individuals.
I have a fairly low level of confidence in this as yet, and am no longer inclined to this style of axiom.
I don't know whether it's best to assert it of $<<$, or of $<<$ restricted to ordinals.
For the present I will just display rather than actually adopt the axiom and assert a much weaker axiom which will probably suffice for the applications I have in mind (i.e. for analysis).
=GFT
declare_infix (240, "e");
new_axiom (["SInfAx"], ⌜
   ∀p⦁ ∃q⦁ p << q 
	∧ (∀x⦁ x << q ⇒
		((∃y $e⦁ y << q
		  ∧ (∀Z⦁ ∃u⦁ u << y
			∧ (∀v⦁ v << x ⇒ (v e u ⇔ Z v))
		     )
		  )
		∧ (∀G⦁ (∀u⦁ u << x ⇒ (G u) << q)
		    ⇒ ∃y⦁ y << q ∧ ∀u⦁ u << x ⇒ (G u) << y
	           )
            )
)
⌝);
=TEX

The weak axiom of infinity has some similarity with the galactic closure axiom for GST.
Taking the idea of a galaxy but limiting the closure properties to closure under replacement, we get the following axiom.
Think of it in terms of ordinals which we may think of according the the Von Neumann conception (though the model behind the surreals is not the same) in which each ordinal is the set of its predecessors (in the surreals it is more like an ordinal is the set of numbers of smaller rank).
So we are asserting that for every surreal ordinal $s$ there is a large ordinal $g$ which is ``closed under replacement'', i.e. the image of an ordinal $x$ under a function $f$ is bounded in the galaxy if it is a subset of it.


=SML
new_axiom (["WInfAx"], ⌜
     ∀s⦁ ∃g⦁ s << g
     ∧ ∀x f⦁
	  x << g
	∧ (∀y⦁ y << x ⇒ f y << g)
	⇒ ∃z⦁ z << g ∧ ∀v⦁ v << x ⇒ f v << z⌝);

=TEX

\subsection{Constructing the Surreal Numbers}

=SML
open_theory "GST";
force_new_theory "src";
set_merge_pcs ["hol1", "'savedthm_cs_∃_proof", "'GST1"];
=TEX

\subsubsection{The Representation of Surreals}

Its not clear what is the best way to do this, so I may end up trying more than one method.
The first method is to use transfinite binary expansions which I have done following the Wikpedia account (though not slavishly).

A surreal number is a function whose domain is an ordinal and whose range is a subset of $2⋎g$:

ⓈHOLCONST
│ ⦏Surreal_rep⦎: GST → BOOL
├───────────
│ ∀s⦁ Surreal_rep s ⇔ Function s ∧ Ordinal (domain s) ∧ (range s) ⊆⋎g 2⋎g   
■

\ignore{
=SML
set_goal([], ⌜∃x⦁ Surreal_rep x⌝);
a (rewrite_tac (map get_spec [⌜Surreal_rep⌝]));
a (∃_tac ⌜∅⋎g⌝);
a (rewrite_tac []);
val Surreal_exists_thm = save_pop_thm "Surreal_exists_thm";
=TEX
}%ignore

=GFT
Surreal_exists_thm =
	⊢ ∃ x⦁ Surreal_rep x
=TEX

Sometimes its handy to have this as a set:

ⓈHOLCONST
│ ⦏surreal_reps⦎: GST SET
├───────────
│ surreal_reps = {s | Surreal_rep s}
■

\subsubsection{Defining The Constants used in The Axioms}

We will need to define operations over the surreals using transfinite recursion, and for that purpose a suitable well-founded relation is needed.
The surreal representatives are partially ordered by their length, which is of course, their domain.

=SML
declare_infix (70, "<<⋎srr");
=TEX

ⓈHOLCONST
│ $⦏<<⋎srr⦎: GST → GST → BOOL
├───────────
│ ∀x y⦁ x <<⋎srr y ⇔ Surreal_rep x ∧ Surreal_rep y ∧ domain x ⊂⋎g domain y
■

\ignore{
=IGN
stop;
set_goal([], ⌜WellFounded (surreal_reps, $<<⋎srr)⌝);
a (rewrite_tac [get_spec ⌜surreal_reps⌝, well_founded_induction_thm, get_spec ⌜$<<⋎srr⌝]);
a (REPEAT strip_tac);
a (asm_tac (∀_elim ⌜p⌝ GST_wf_ax));
a (lemma_tac ⌜(∀ s⦁ (∀ t⦁ t ∈⋎g s ⇒ p t) ⇒ p s)⌝
	THEN REPEAT strip_tac);

=TEX
}%ignore

=GFT
=TEX

=SML
declare_infix (70, "<⋎srr");
=TEX

The next key element of the construction is the usual linear ordering of the surreals.
ⓈHOLCONST
│ $⦏<⋎srr⦎: GST → GST → BOOL
├───────────
│ ∀s t⦁ s <⋎srr t ⇔
│	s ⊆⋎g t ∧ (domain s ↦⋎g 1⋎g) ∈⋎g t
│   ∨	t ⊆⋎g s ∧ (domain t ↦⋎g ∅⋎g) ∈⋎g s
│   ∨	(∃z⦁ z ⊆⋎g s ∧ z ⊆⋎g t
│	∧ (domain z ↦⋎g ∅⋎g) ∈⋎g s ∧ (domain z ↦⋎g 1⋎g) ∈⋎g t)
■

In order to do this we need to define some auxiliary functions which translate between binary expansions and cuts in the numbers.

First, from a number obtain a left and a right set of numbers:

ⓈHOLCONST
│ ⦏L⦎: GST → GST
├───────────
│ ∀n⦁ L n =  C⋎g{m | m ⊂⋎g n ∧ domain m ↦⋎g 1⋎g ∈⋎g n}   
■
ⓈHOLCONST
│ ⦏R⦎: GST → GST
├───────────
│ ∀n⦁ R n =  C⋎g {m | m ⊂⋎g n ∧ domain m ↦⋎g ∅⋎g ∈⋎g n}   
■

Each pair of sets of numbers $L$, $R$ such that every element of $L$ is less than every element of $R$, determines a unique number $σ(L, R)$ which is the simplest number between the two sets.

This does not correspond precisely to the WIkpedia account, since in it $σ(L,R)$ is supposed to be strictly between $L$ and $R$, and right now I can't see how to do that in the case that one half contains a number which is an initial segment of a number in the other half.

ⓈHOLCONST
│ ⦏σ⦎: GST × GST → GST
├───────────
│ ∀ls rs⦁ σ(ls, rs) =  C⋎g (⋃ {i | ∃le re⦁ le ∈⋎g ls ∧ re ∈⋎g rs ∧ i = (X⋎g le) ∩ (X⋎g re)})
■


\subsubsection{Defining the Arithmetic Operators}

These are the definitions of the arithmetic operations which go with the above definition of the construction of the surreals.
They probably can and should be done in the new type of surreals after it has been introduced, but I had already done them before that occurred to me, and will remain at least until I have satisfied myself that definition the later is preferable.

=SML
declare_right_infix (210, "+⋎srr");
declare_right_infix (210, "-⋎srr");
declare_right_infix (220, "*⋎srr");
=TEX

The following definition is by transfinite recursion on the rank of the surreal numbers involved.
A proof script is required (not yet supplied) to show that the function is well-defined.

\ignore{
=IGN
stop;
set_goal([], ⌜∃$+⋎srr⦁ ∀x y⦁ Surreal_rep x ∧ Surreal_rep y ⇒
     x +⋎srr y = σ(
	C⋎g({a | ∃u⦁ a = u +⋎srr y ∧ u ∈⋎g L(x)} ∪ {a | ∃v⦁ a = x +⋎srr v ∧ v ∈⋎g L(y)}),
	C⋎g({a | ∃u⦁ a = u +⋎srr y ∧ u ∈⋎g R(x)} ∪ {a | ∃v⦁ a = x +⋎srr v ∧ v ∈⋎g R(y)}))
⌝);
a (PC_T1 "hol" lemma_tac ⌜∃f⦁ f = λp⦁ (Surreal_rep x ∧ Surreal_rep y ⇒
     p x y = σ(
	C⋎g({a | ∃u⦁ a = p u y ∧ u ∈⋎g L(x)} ∪ {a | ∃v⦁ a = p x v ∧ v ∈⋎g L(y)}),
	C⋎g({a | ∃u⦁ a = p u y ∧ u ∈⋎g R(x)} ∪ {a | ∃v⦁ a = p x v ∧ v ∈⋎g R(y)})))⌝
	THEN prove_∃_tac);

recursion_theorem

=TEX
}%ignore

ⓈHOLCONST
│ $⦏+⋎srr⦎: GST → GST → GST
├───────────
│ ∀x y⦁ Surreal_rep x ∧ Surreal_rep y ⇒
│     x +⋎srr y = σ(
│	C⋎g({a | ∃u⦁ a = u +⋎srr y ∧ u ∈⋎g L(x)} ∪ {a | ∃v⦁ a = x +⋎srr v ∧ v ∈⋎g L(y)}),
│	C⋎g({a | ∃u⦁ a = u +⋎srr y ∧ u ∈⋎g R(x)} ∪ {a | ∃v⦁ a = x +⋎srr v ∧ v ∈⋎g R(y)}))
■

ⓈHOLCONST
│ $⦏~⋎srr⦎: GST → GST
├───────────
│ ∀x⦁ Surreal_rep x ⇒
│     ~⋎srr x = C⋎g{z | ∃u v⦁ z = u ↦⋎g v ∧ u ↦⋎g (if v = ∅⋎g then 1⋎g else ∅⋎g) ∈⋎g x}
■

ⓈHOLCONST
│ $⦏-⋎srr⦎: GST → GST → GST
├───────────
│ ∀x y⦁ Surreal_rep x ∧ Surreal_rep y ⇒
│     x -⋎srr y = x +⋎srr (~⋎srr y)
■

ⓈHOLCONST
│ $⦏*⋎srr⦎: GST → GST → GST
├───────────
│ ∀x y⦁ Surreal_rep x ∧ Surreal_rep y ⇒
│     x *⋎srr y = σ(
│	C⋎g{a | ∃u v⦁ a = u *⋎srr y +⋎srr x *⋎srr v -⋎srr u *⋎srr v
│		∧ (u ∈⋎g L(x) ∧ v ∈⋎g L(y) ∨ u ∈⋎g R(x) ∧ v ∈⋎g R(y))},
│	C⋎g{a | ∃u v⦁ a = u *⋎srr y +⋎srr x *⋎srr v -⋎srr u *⋎srr v
│		∧ (u ∈⋎g L(x) ∧ v ∈⋎g R(y) ∨ u ∈⋎g R(x) ∧ v ∈⋎g L(y))})
■

\ignore{
=IGN

=TEX
}%ignore


\subsection{The Theory of Surreal Numbers}

=SML
open_theory "src";
force_new_theory "sr";
set_merge_pcs ["hol1", "'savedthm_cs_∃_proof", "'GST1"];
new_type_defn (["sr"], "sr", [], Surreal_exists_thm);
=TEX

\ignore{
=SML

=TEX
}%ignore

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{GST.th}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{sra.th}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{src.th}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{sr.th}
}  %\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
