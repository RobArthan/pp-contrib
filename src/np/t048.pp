=TEX
\ignore{
=VDUMP t048i.tex
Last Change $ $Date: 2014/05/30 20:58:18 $ $

$ $Id: t048.pp $ $
=TEX
}%ignore

The idea of applying the adjective ``iterative'' to ontologies other than that of well-founded sets came to me from Thomas Forster whose paper on the iterative conception of set\cite{forsterTICS} extends that idea to embrace set theories with a universal set.
Tt then seems natural to observe that foundational ontologies of entities other than sets may also be conveniently described under an iterative conception.

The ontologies which I consider here were not inspired by an iterative model, but they can nevertheless be presented in that way.
The motivation for the ideas is primarily pragmatic, arising from a conception of the applicability of formal languages and methods to deductive and nomologico-deductive science.

\subsection{Carnap's Programme}

It may be helpful to relate some aspects of the ideas presented here to the philosophical programme of Rudolf Carnap, or at least to my understanding of its most important central thread.
That central thread is the desire to facilitate the application of formal languages to deductive and nomologico-deductive science (an important part of philosophy being considered one of the deductive sciences).

Carnap began within the universalistic conception of logic presented by Frege and Russell, but the application of logic to empirical science seemed to demand languages which transcended the limits of such universalistic conceptions.
In consequence, early in his career Carnap adopted the more pluralistic attitude towards formal languages which was pioneered by Hilbert and his associates.
During this transition to pluralism he showed particular concern for the question whether implicit definitions embodied in some formal axiomatisation of a subject matter are categorical.
This is a part of an ongoing concern for \emph{meaningfulness} which ran through all the phases in his intellectual development, which was a principal source of his opposition to `metaphysics'\footnote{
To the extent that in some of his best work \emph{meaninglessness} seems to becomes a criterion of metaphysics rather than a critique of it.}%
. 






\section{What is a Foundational Ontology}

A \emph{logical foundation for mathematics} is a formal deductive system in which a large part of mathematics can be derived by conservative extension.

This connects with Frege's logicist thesis, which may be paraphrased:

\begin{quote}
mathematics = logic + definitions
\end{quote}

with `logical foundation system' rather than `logic' (since that term is commonly used in a narrower sense today) and with the notion of `definition' liberalised to that of `conservative extension'.

Such a foundation may serve more than one purpose.
The first was to demonstrate the logicist thesis (in which purpose it is now generally held to have failed, primarily in virtue of the differences which are now perceived between `logic' simpliciter and the kind of logical system needed to serve this foundational role).
This is not my present concern, which is with three other roles which such a foundation system may fulfil.

\begin{enumerate}
\item as a foundation for abstract semantics
\item as a source of proof theoretic strength
\item as a logical system in which to formally derive mathematics, ideally with good software support.
\end{enumerate}

It is not necessary that all of these roles be assumed by the same foundation system.
There may be tension between the first two roles and the last.

The plan I follow in this document is as follows.

The document falls into three parts, concerned primarily with each of these three foundation roles in turn.

In the first part the foundational role will be assumed by an ontology of well-founded-sets, under the hypothesis that this is the best way of fulfilling this role.
At this stage ontology is firmly in the driving seat.
To the extent that formal theories come into the discussion there will be just two.
The first order language with just two relations, membership and equality, and a polymorphic ω-order logic with the same primitive relations over the individuals.
The aim is a universal foundation for semantics, either in the form of a single formal language with semantics and deductive system, in which abstract semantics for arbitrary languages may be defined, or, more plausibly, as a single language together with a heirarchy of semantics and deductive systems are available.

An important aim of this part is a resolution of the problem of \emph{semantic regress}.
By semantic regress I refer to obvious problem that to give a formal semantics one needs a formal language in a language which has a well-defined semantics.
This problem is dealt with in two principal ways.
The first is to formulate a semantics which is effectively `meta-circular', in which the same language, or a language in the same family, as the object language, is used as the meta-language in which the semantics is defined.

In such a formal context foundational ontologies can be defined, resulting in ontologies confined by that of the meta-language.
This allows formal techniques to be used to clarify the characteristics of various formal descriptions of foundational ontologies.
Once thus clarified, these definitions can then be exported into a foundational context.
In that context the definitions are no longer locating an ontology within a metatheoretic context, but are working in an empty context carving out an ontology without constraint by the ontology of the metalanguage.

In the second part, we consider the interplay between semantics for first order languages defined by such ontologies and axioms for a first order theory.

In the third part we address various pragmatic considerations which arise in the formalisation of mathematics and its applications, speculate about how these might influence the choice of formal language in which to conduct such formalisation, and about the kind of foundational ontology required to underpin languages suitable for large scale application of formal methods.
In this section, the semantics are defined in the systems considered in the first part, and the deductive systems would then be derived from the deductive systems for the semantic foundations.

\section{Pure Well-Founded Sets}

The term set is used for a variety of different kinds of collections.
Almost any characteristic which has been mooted as an essential characteristic of sets is sometimes absent from conceptions of set.

Among these characteristics we may include:

\begin{itemize}
\item purity
\item well-foundedness
\item extensionality
\item definiteness
\end{itemize}

`Purity' in a set theory consists in there being nothing but sets in the domain of discourse, or formally perhaps in their being more than one thing with no members (only one of them being `the empty set'.

Counterexamples to well-foundedness appear in numerous set theories, including all those in which there is a universal set, of which perhaps the best known is Quine's NF.
Technical counterexamples to full extensionality are found in those set theories with urelements which are formalised for convenience in single sorted first order logic by deeming urelements to have no members.
Full-blooded counterexamples to extensionality are found in constructive notions of set, in which a set is determined by a rule (for deciding membership) and equality of sets is provable co-extensionality of the rules which determine them.

By definiteness I have in mind here only that very weak notion of definiteness which arises from membership being a relation in a first order langage, i.e. that in any interpretation of the theory it is either true or false for any two values $x$ and $y$ that $x$ is a member of $y$.
This characteristic is absent in fuzzy set theory.
 
I will not be further considering in relation to the foundations of abstract semantics any set theory which lacks any of the above characteristics.
This is because the concept of pure well-founded set is the simplest, and hence easiest to make clear and precise, and I know of no reason to believe that the extra complications which arise from dropping any of the above requirements gives any benefit.

Later, when we come to consider foundational systems for use in the derivation of mathematics (rather than as semantic foundations), then these characteristics are gradually whittled away until ultimately we propose foundationl ontologies which are simply not sets.

\subsection{Iteration, Recursion, Induction}

The best known description of the intended interpretation of modern set theory is the iterative conception of the cumulative heirarchy.
The concept of set described by the iterative conception is that of a pure-well-founded set (though Zermelo who is usually credited with this conception \cite{zermelo30b,ewald1996} began his iteration from some collection of urlements, and therefore allowed for an ontology which is not `pure').

The ontology in this conception is obtained by transfinite iteration of the `powerset' construction.
The structure of this definition is similar to inductive definitions of set which may be expressed using recursion.

\section{A Plan}

\subsection{Themes}

\subsection{Formality}

The work aims to contribute to the development of effective ways of formalising deductive reason in all its applications, in the spirit of Leibniz and Carnap.
It aims to do so by reflection on how appropriate formal notations or languages can be established.
More specifically in respect of determining the semantics of the formal languages.

For the purposes of establishing the soundness of deductive systems, abstract semantics suffices, and in developing such semantics, a good place to start is with the underlying ontology in relation to which the semantics will be given.




\subsection{Universalism and Pluralism}




\subsection{Iterative}



\section{Well Founded Ontologies}




\subsection{}


=SML
open_theory "rbjmisc";
force_new_theory "⦏t048a⦎";
=TEX

\ignore{
=SML
force_new_pc ⦏"'t048a"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'t048a";
set_merge_pcs ["rbjmisc", "'t048a"];
set_flag ("pp_use_alias", true);
set_flag ("profiling", true);
init_stats();
=TEX
}%ignore

=SML
declare_infix(230, "⦏<<⦎");
=TEX

ⓈHOLCONST
│ ⦏hereditary⦎: ('a → 'a → BOOL) → ('a → BOOL) → BOOL
├─────────
│ ∀$<< p⦁ hereditary $<< p ⇔ ∀x⦁ (∀y⦁ y << x ⇒ p y) ⇒ p x
■

ⓈHOLCONST
│ ⦏inductive⦎: ('a → 'a → BOOL) → 'a → BOOL
├─────────
│ ∀r x⦁ inductive r x ⇔ ∀p⦁ hereditary r p ⇒ p x
■

ⓈHOLCONST
│ ⦏well_founded⦎: ('a → 'a → BOOL) → BOOL
├─────────
│ ∀r⦁ well_founded r ⇔ ∀x⦁ inductive r x
■

ⓈHOLCONST
│ ⦏wf_part⦎: ('a → 'a → BOOL) → ('a → 'a → BOOL) 
├─────────
│ ∀r⦁ wf_part r = λx y⦁ r x y ∧ inductive r y
■

=GFT
=TEX

\ignore{
=SML
val hereditary_def = get_spec ⌜hereditary⌝;
val well_founded_defn = get_spec ⌜well_founded⌝;
val wf_part_def = get_spec ⌜wf_part⌝;
val inductive_def = get_spec ⌜inductive⌝;
=IGN
set_goal([], ⌜∀r⦁ well_founded (wf_part r)⌝);
a (strip_tac THEN rewrite_tac [well_founded_defn, wf_part_def, hereditary_def] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
=TEX
}%ignore


\ignore{
=SML
add_pc_thms "'t048a" [];
set_merge_pcs ["rbjmisc", "'t048a"];
=TEX
}%ignore


\ignore{
=IGN
pc_rule1 "lin_arith" prove_rule [] ⌜2+2=4⌝;
=SML
commit_pc "'t048a";

force_new_pc "⦏t048a⦎";
merge_pcs ["rbjmisc", "'t048a"] "t048a";
commit_pc "t048a";

=IGN
force_new_pc "⦏t048a1⦎";
merge_pcs ["rbjmisc1", "'t048a"] "t048a1";
commit_pc "t048a1";
=TEX


=SML
set_flag ("subgoal_package_quiet", false);
set_flag ("pp_use_alias", true);
output_stats ("t048.stats.doc");
set_flag ("profiling", false);
=TEX
}%ignore

