


=TEX
\ignore{
=VDUMP t049i.tex
Last Change $ $Date: 2012/06/03 21:32:27 $ $

$ $Id: t049.doc,v 1.2 2012/06/03 21:32:27 rbj Exp $ $
=TEX
}%ignore


This document was originally provoked by a discussion on {\it hol-info} about how best to do Euclidean geometry using one of the HOL tools, and was intended to exemplify a straightforward axiomatic approach, to describe the limitations of this approach and to illustrate other ways of approaching the theory which overcome some of those limitations.
My own interest is primarily methodological, and it quickly became clear that this was peripheral to the main thrust of the dialogue on \emph{hol-info}.

\subsection{A brief history of Axiomatic Method}

The axiomatic method begins in the mathematics of ancient Greece and is most famously exemplified in Euclid's ``Elements'' \cite{euclidEL1}.
Euclid's Elements exemplify the method but do not describe them, it is usual to refer to Aristotle's Posterior Analytics for accounts of the methods.%
\footnote{\href{http://www.texts.rbjones.com/rbjpub/philos/classics/aristotl/o4110c.htm}{Posterior Analytics, Book 1 Part 10}}


The axiomatic method at this stage is concerned with the organisation of deductive proofs, and answers two problems of regress in relation to what Aristotle called ``demonstrative'' proof.
The problem is where to start from, which evidently was a matter of controversy between those who believed that one should begin with un demonstrated propositions or whether circular proofs should be admitted.
Aristotle settles for the former

\subsection{Some Aristotelian Terminology}

These are based on Aristotle's Posterior Analytics%
\footnote{Posterior Analytics, Book 1, \href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o4102c.htm}{part 2},
\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o4106c.htm}{part 6},
\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o4110c.htm}{part 10}.
}.


\begin{description}
\item[axiom]
an immediate basic truth which must be known before anything else can be known

\item[basic]
a basic proposition is an immediate proposition

\item[dialectical]
a proposition (usually a premiss) is dialectical if it assumes either part (affirmation or negation) of a predication (regardless of which part is in fact true)

\item[definition]
a thesis which does not assert or deny existence

\item[demonstration]
a syllogism productive of scientific knowledge, the grasp of which is, \emph{eo ipso}, knowledge.

\item[demonstrative]
a proposition is demonstrative if (by contrast with a dialectical proposition) it lays down one part (affirmation or negation) of a predication to the definite exclusion of the other because that part is true

\item[hypothesis]
a thesis which asserts or denies existence

\item[immediate]
a proposition to which no proposition is prior

\item[premiss]
starting points for demonstrations, which must be true, primary (and indemonstrable), immediate, better known than and prior to the conclusion

\item[primary]
an appropriate basic truth

\item[prior]

\item[proposition]
the predication of a single attribute of a single subject

\item[thesis]

an immediate basic truth which though not demonstrable is not an axiom.

\end{description}

\section{Foundational Axiomatic Methods}

Toward the end of the 19th Century there was a famous controversy bewteen Frege and Hilbert which is significant for the development of the axiomatic method.

Frege's work is foundational and universalistic, he envisages a single language, his \emph{begriffscrift} or \emph{concept language} in which logical reasoning in any domain may be conducted, but expects this language and the concepts which are used in it to have definite meanings.
We may note also that the language is intended for \emph{use} in expressing and proving propositions, it is not intended as a new subject matter for mathematical investigation.

By contrast, Hilbert takes geometry into new territory primarily by instigating metatheory as a part of mathematics.
His ``Foundations of Geomtry'' \cite{hilbertFG} not only advances the content of axiomatic geometry, but also demonstrated results about the axiom systems in use, such as the consistency and independence of the axioms.
In order to prove independence results it is necessary to consider different interpretations of the language of geometry, and it therefore becomes natural to regard axiomatic geometry in a more abstract way, as concerned with any mathematical structure which satisfies the axioms rather than with some particular structure of which the axioms are true.

Frege's logicist foundationalism provides a different perspective on the development of mathematics, which emphasises the formality and deprecates the use of axioms of a non-logical character.
The idea here is that one establishes, once and for all, axioms for logic independent of any particular mathematical subject matter, and that it then suffices to introduce new subject matters by defining the relevant concepts are reasoning logically about them.
The axiomatic characterisation of a domain is replaced by the definition of its terms.
This addresses the issue of consistency, because the use of definitions is conservative, and will yield a system consistent if the underlying logic is consistent.
It is oriented towards the formal development of the various mathematical (and other) subject matters, not to the metatheory of axiomatic systems (though this can also be addressed using this method).

The following examples are intended to illustrate various ways in which the kinds of axiomatic method can be deployed using mechanised logical foundation systems.
They are ways of reconciling the differences between Frege and Hilbert and getting the best of both worlds. 
The foundation system in the context of which these examples are presented is HOL (a higher order logic based on Church's Simple Type Theory) and the tool used is {\Product}.

There are four methods which I propose to consider:

\begin{description}
\item[axiomatic]
Though working in a foundation system it is still possible to introduce axioms as if we were just in first order logic.
\item[interpreted]
The required theory is effected by conservative extension typically involving defining new types or type constructors and defining constants over these types which can be proven to satisfy the required axioms.
\item[structural]
Define the class of structures satisfying the required axioms and reason about this class.
\item[?]
I thought I had four but can't remember what the last one was!
\end{description}


\section{Euclid's Elements}\label{euclid}

\cite{euclidEL1}


\section{Axiomatic Approach}\label{axiomatic}

The subsections of this section correspond roughly to sections in Hilbert \cite{hilbertFG}.

=SML
open_theory "rbjmisc";
force_new_theory "⦏t049a⦎";
=TEX

\ignore{
=SML
force_new_pc ⦏"'t049a"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'t049a";
set_merge_pcs ["rbjmisc", "'t049a"];
set_flag ("pp_use_alias", true);
set_flag ("profiling", true);
init_stats();
=TEX
}%ignore

\subsection{The Elements}

First we introduce some primitive ``collections'' for which we use types.

=SML
new_type("⦏POINT⦎", 0);
new_type("⦏LINE⦎", 0);
new_type("⦏PLANE⦎", 0);
=TEX

Hilbert is not explicit about which concepts are primitive, we have to mine these from the axioms.
I have brought the introduction of these together here since we have to mention the constants before we use them in axioms.
The list here encompasses only those concepts used in the axioms which follow.

Since Hilbert does not explicitly state what is primitive there is some lattitude in the choice of primitives.
For example, it is not clear whether one should take the relationship between points and planes as primitive or that between lines and planes.
I have taken the former as primitive since it is used first.

=SML
new_const ("⦏on⦎", ⓣPOINT → LINE → BOOL⌝);
declare_infix(300, "on");
new_const ("⦏in⋎p⦎", ⓣPOINT → PLANE → BOOL⌝);
declare_infix(300, "in⋎p");
=TEX

\subsection{Axioms of Connection}

Two distinct point determine a unique line.

=SML
val ⦏I1⦎ = new_axiom(["I1"], ⌜
	∀ A B a b⦁ ¬ A = B ∧ A on a ∧ B on a ∧ A on b ∧ B on b
		⇒ a = b ⌝);
=TEX

This justifies Hilbert's use of the notation ``AB'' for the line containing the points ``A'' and ``B''.
We have to chose a more slightly different notation and define a constant for the purpose.

=SML
declare_infix(600, "↔⋎l");
=TEX

ⓈHOLCONST
│ $⦏↔⋎l⦎: POINT → POINT → LINE
├─────────
│ ∀A B⦁ A ↔⋎l B = εa⦁ A on a ∧ B on a
■

To use this definition we need the following theorem:

=GFT
⦏↔⋎l_thm⦎ = ⊢ ∀ a A B⦁ ¬ A = B ∧ A on a ∧ B on a ⇒ A ↔⋎l B = a
=TEX

The following proof script obtains the result.

=SML
val ↔⋎l_def = get_spec ⌜$↔⋎l⌝;

set_goal([], ⌜∀a A B⦁ ¬ A = B ∧ A on a ∧ B on a ⇒ A ↔⋎l B = a⌝);
a (rewrite_tac[↔⋎l_def]);
a (REPEAT strip_tac);
a (ε_tac ⌜ε a⦁ A on a ∧ B on a⌝);
(* *** Goal "1" *** *)
a (∃_tac ⌜a⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac [I1]);
val ↔⋎l_thm = save_pop_thm "↔⋎l_thm";
=TEX


Any two distinct points on a line determine that line.

=SML
val ⦏I2⦎ = new_axiom(["I2"], ⌜
	∀ a A B⦁ ¬ A = B ∧ A on a ∧ B on a
		⇒ A ↔⋎l B = a ⌝);
=TEX

Any three non-colinear points determine a plane.

=SML
val ⦏I3⦎ = new_axiom(["I3"], ⌜
	∀ A B C α β ⦁ ¬ (∃a⦁ A on a ∧ B on a ∧ C on a)
		∧ A in⋎p α ∧ B in⋎p α ∧ C in⋎p α
		∧ A in⋎p β ∧ B in⋎p β ∧ C in⋎p β
		⇒ α = β⌝);
=TEX

We now need a notation for the plane determined by three non-colinear points.

ⓈHOLCONST
│ ⦏Δ⋎p⦎: POINT × POINT × POINT → PLANE
├─────────
│ ∀A B C⦁ Δ⋎p (A, B, C) = εα⦁ A in⋎p α ∧ B in⋎p α ∧ C in⋎p α
■

To use this definition the following result is required:

=GFT
⦏Δ⋎p_thm⦎ = ⊢ ∀α A B C⦁ ¬ (∃a⦁ A on a ∧ B on a ∧ C on a)
		∧ A in⋎p α ∧ B in⋎p α ∧ C in⋎p α
		⇒ Δ⋎p (A, B, C) = α
=TEX

=SML
val ⦏Δ⋎p_def⦎ = get_spec ⌜Δ⋎p⌝;

set_goal([], ⌜∀α A B C⦁ ¬ (∃a⦁ A on a ∧ B on a ∧ C on a)
			∧ A in⋎p α ∧ B in⋎p α ∧ C in⋎p α
		⇒ Δ⋎p (A, B, C) = α⌝);
a (REPEAT strip_tac THEN rewrite_tac[Δ⋎p_def]);
a (ε_tac ⌜ε α⦁ A in⋎p α ∧ B in⋎p α ∧ C in⋎p α⌝);
(* *** Goal "1" *** *)
a (∃_tac ⌜α⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac [I3]);
val Δ⋎p_thm = save_pop_thm "Δ⋎p_thm";
=TEX

Any three non-colinear points in a plane determine that plane.

=SML
val ⦏I4⦎ = new_axiom(["I4"], ⌜∀ A B C α⦁ ¬ (∃a⦁ A on a ∧ B on a ∧ C on a)
		∧ A in⋎p α ∧ B in⋎p α ∧ C in⋎p α
		⇒ Δ⋎p (A, B, C) = α⌝);
=TEX

If two points of a line lie in a plane then every point in the line is in the plane.

=SML
val ⦏I5⦎ = new_axiom(["I5"], ⌜
	∀ A B a α⦁ ¬ A = B ∧ A on a ∧ B on a ∧ A in⋎p α ∧ B in⋎p α
		⇒ ∀C⦁ C on a ⇒ C in⋎p α⌝);
=TEX

We can now define the relationship between lines and planes.

=SML
declare_infix(300, "in⋎l");
=TEX

ⓈHOLCONST
│ $⦏in⋎l⦎: LINE → PLANE → BOOL
├─────────
│ ∀a α⦁ a in⋎l α ⇔ ∃A⦁ A on a ∧ A in⋎p α
■

If two planes have one point in common, then they have another in common.


=SML
val ⦏I6⦎ = new_axiom(["I6"], ⌜∀α β A⦁ A in⋎p α ∧ A in⋎p β
			⇒ ∃B⦁ ¬ A = B ∧ B in⋎p α ∧ B in⋎p β⌝);
=TEX
On every straight line there are at least two points, on every plain at least three non-co-linear points and ``in space'' at least four points not in a plain.

=SML
val ⦏I7⦎ = new_axiom(["I7"], ⌜(∀a⦁ ∃ x y⦁ x on a ∧ y on a ∧ ¬ x = y)
	∧	(∀α⦁ ∃ A B C⦁ A in⋎p α ∧ B in⋎p α ∧ C in⋎p α
			∧ ¬ ∃a⦁ A on a ∧ B on a ∧ C on a)
	∧	(∃A B C D⦁ ¬ ∃α⦁ A in⋎p α ∧ B in⋎p α ∧ C in⋎p α ∧ D in⋎p α)
⌝);
=TEX

I do not assert that the points are distinct since that is provable using earlier axioms.

=IGN
new_axiom([""], ⌜⌝);
=TEX

\subsubsection{Theorems}

=GFT
Theorem_1a = ⊢ ∀ a b⦁ ¬ a = b
	⇒ ¬ (∃ A B⦁ ¬ A = B ∧ A on a ∧ B on a ∧ A on b ∧ B on b)
=TEX


=SML
set_goal([], ⌜∀a b⦁ ¬ a=b ⇒ ¬ ∃A B⦁ ¬ A=B ∧ A on a ∧ B on a ∧ A on b ∧ B on b⌝);
a (contr_tac);
=GFT ProofPower output
(* *** Goal "" *** *)

(*  6 *)  ⌜¬ a = b⌝
(*  5 *)  ⌜¬ A = B⌝
(*  4 *)  ⌜A on a⌝
(*  3 *)  ⌜B on a⌝
(*  2 *)  ⌜A on b⌝
(*  1 *)  ⌜B on b⌝

(* ?⊢ *)  ⌜F⌝
=SML
a (all_fc_tac [I1]);
=GFT ProofPower output
Tactic produced 0 subgoals:
Current and main goal achieved
=SML
val Theorem_1a = save_pop_thm "Theorem_1a";
=TEX

=SML
set_goal([], ⌜∀α β⦁ (∃A⦁ A in⋎p α ∧ A in⋎p β) ⇒ ∃a⦁ a in⋎l α ∧ a in⋎l β⌝);
a (REPEAT strip_tac);
=GFT ProofPower output
(* *** Goal "" *** *)

(*  2 *)  ⌜A in⋎p α⌝
(*  1 *)  ⌜A in⋎p β⌝

(* ?⊢ *)  ⌜∃ a⦁ a in⋎l α ∧ a in⋎l β⌝
=SML
a (strip_asm_tac (list_∀_elim [⌜α⌝, ⌜β⌝, ⌜A⌝] I6));
=GFT
(* *** Goal "" *** *)

(*  5 *)  ⌜A in⋎p α⌝
(*  4 *)  ⌜A in⋎p β⌝
(*  3 *)  ⌜¬ A = B⌝
(*  2 *)  ⌜B in⋎p α⌝
(*  1 *)  ⌜B in⋎p β⌝

(* ?⊢ *)  ⌜∃ a⦁ a in⋎l α ∧ a in⋎l β⌝
=SML
a (∃_tac ⌜A ↔⋎l B⌝);
=GFT
(* *** Goal "" *** *)

(*  5 *)  ⌜A in⋎p α⌝
(*  4 *)  ⌜A in⋎p β⌝
(*  3 *)  ⌜¬ A = B⌝
(*  2 *)  ⌜B in⋎p α⌝
(*  1 *)  ⌜B in⋎p β⌝

(* ?⊢ *)  ⌜A ↔⋎l B in⋎l α ∧ A ↔⋎l B in⋎l β⌝

=IGN ProofPower output
Tactic produced 0 subgoals:
Current and main goal achieved
val it = (): unit
=IGN
val Theorem_1b = save_pop_thm "Theorem_1b";
=TEX


\section{Meta-theoretic Method}\label{meta-theoretic}

The ``axiomatic'' approach illustrated in section \ref{axiomatic} is appropriate for proving theorems of geometry.
However, possibly the most significant of the results in Hilbert's \emph{Foundations of Geometry} are of a meta-theoretic character.
This includes demonstration of the consistency and independence of the axioms.

Results of this kind cannot be obtained by the same methods.
In this section I illustrate one way in which such results can be obtained.
The results are obtained by reasoning about models of the axioms, and so the crucial decision to be made is what kind of thing a model is.

In present day model theory a first order theory is interpreted in a \emph{structure}.
A structure is a non-empty set which is the domain of discourse, together with values over that domain for each of the constants, relations or functions in the language.

Hilbert's book was written before first order logic was established, and he is deliberately working with three kinds of entity (rather than speaking only of collections of points, say), so he is better understood as if working in a many-sorted logic.
The structure would then have three sets representing the three sorts together with appropriate constants, relations and functions defined over them.

Hilbert is not himself explicit about what consititues an interpretation of the axioms, and so we have to discover the signature by trawling through the axioms.

In the present context there are three most obvious ways to model such a structure.

\begin{enumerate}
\item as a tuple in which the first three elementa are sets (or propositional functions) and the remainder are the constants, relations and functions.
\item as a tuple in which the first element is a set (the entire ontology), then we have three predicates delimiting the points lines and plains, and then the constants relations and functions.
\item assume that the three domains will each be whole \emph{types} and use a structure in which they are not explicitly represented but are found in the types of the constants, relations and predicates.
\end{enumerate}

The last of these is without loss of generality since any non-empty set can be made into a type.
It does represent a simplification from the point of view of the formalisation of the various axioms, so I will go that way.

The required signature can then be read off the previous axiomatic presentation by enumerating the types of the primitive constants (those which are characterised by the axioms rather than defined) with the primitive types replaced by corresponding type variables.

I will use a type abbreviation for the type of such structures, a first stab at this is:



=SML
open_theory "rbjmisc";
force_new_theory "⦏t049b⦎";
=TEX

\ignore{
=SML
force_new_pc ⦏"'t049b"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'t049b";
set_merge_pcs ["rbjmisc", "'t049b"];
set_flag ("pp_use_alias", true);
set_flag ("profiling", true);
=IGN
init_stats();
=TEX
}%ignore


=SML
declare_type_abbrev("G", [], ⓣ ('pt → 'li → BOOL) × ('li → 'pl → BOOL)⌝);
=TEX
=IGN
"'pt","'li","'pl"
=TEX
Which the two elements of the structure are the relations between point and line and that between line and plain.

We then present the axioms as definitions of properties of these structures.
I will use the same names for the primitive constants, though in this case they will be variable names rather than constant names.
The names of the axioms will be the same as in the previous section (as in Hilbert), but with `M' prefixed to distinguish them.


=SML
declare_infix(300, "on");
declare_infix(300, "in⋎p");
=TEX

ⓈHOLCONST
│ $⦏MI1⦎: G → BOOL
├─────────
│ ∀$on $in⋎p⦁ MI1 ($on, $in⋎p) ⇔
│	∀ A B a b⦁ ¬ A = B ∧ A on a ∧ B on a ∧ A on b ∧ B on b
│		⇒ a = b
■

To make use of defined constants in the axioms we need to have a function which derives the values of the defined constants from the primitive constants.
This is defined by first giving definitions of the constants parameterised by the primitives and then packing them together.

Because of the extra parameter we have to drop the infix status of the constant.

ⓈHOLCONST
│ ⦏↔⋎l⦎: G → 'pt → 'pt → 'li
├─────────
│ ∀$on $in⋎p A B⦁ ↔⋎l ($on, $in⋎p) A B = εa⦁ A on a ∧ B on a
■


ⓈHOLCONST
│ $⦏MI2⦎: G → BOOL
├─────────
│ ∀$on $in⋎p⦁ MI2 ($on, $in⋎p) ⇔
│	∀ a A B⦁ ¬ A = B ∧ A on a ∧ B on a
│		⇒ ↔⋎l ($on, $in⋎p) A B = a
■

\ignore{
=SML
add_pc_thms "'t049b" [];
set_merge_pcs ["rbjmisc", "'t049b"];
=TEX
}%ignore


\ignore{
=IGN
pc_rule1 "lin_arith" prove_rule [] ⌜2+2=4⌝;
=SML
commit_pc "'t049b";

force_new_pc "⦏t049b⦎";
merge_pcs ["rbjmisc", "'t049b"] "t049b";
commit_pc "t049b";

=IGN
force_new_pc "⦏t049a1⦎";
merge_pcs ["rbjmisc1", "'t049a"] "t049a1";
commit_pc "t049a1";
=TEX


=SML
set_flag ("subgoal_package_quiet", false);
set_flag ("pp_use_alias", true);
output_stats ("t049.stats.doc");
set_flag ("profiling", false);
=TEX
}%ignore

