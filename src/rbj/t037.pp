=TEX
\def\rbjidtADHdoc{$$Id: t037.doc,v 1.12 2011/11/04 16:38:42 rbj Exp $$}

I will endeavour to follow the structure of Grice's paper \emph{Vacuous names}\cite{griceVN, quineWO}.
However, the method employed for the formal analysis, which is called ``shallow embedding'', is essentially semantic, and involves addressing semantic fundamentals before finding manageable syntactic presentations, and I therefore find it necessary to address key aspects of the semantics before considering the details of syntax.

\subsection{Background}

Grice's deliberations about Vacuous Names may be understood primarily against those who have supposed or desired a significant difference between formal logics and the logic of ordinary discourse, by one who felt that the differences are, or need only be, modest.
In some of his writings. for example in the ``Retrospective Epilogue'' in \emph{Sudies in the Way of Words}\cite{grice89}, Grice describes two camps, ``Modernists'' and ``Neo-traditionalists'', the former making more and the latter less of the distinctions between formal and ordinary logic.

Elsewhere in Grice's philosophy, in connection with this controversy, the relationship between the logical connectives and their ordinary language counterparts is discussed.
Here we are concerned with the problem of referring expressions which lack a referent.

Modern discussion of this problem begins with Russell \cite{russellOD,russell1956}, who sought formal languages for mathematics which were more precise and more transparent in their logical structure than is ordinary language.

There are two aspects of the problems here at stake which are separable.
One concerns logic and language; how we talk and reason using words or phrases which do not, or might not, refer to any existent entity.
The second is the metaphysical question of what exists.
Russell's most important work in this area arose from his making a transition away from a lavish Meinongian ontology in which there are different kinds or grades of existence, to the adoption of Occam's razor, leading to a spartan ontology.
Key to this is the acceptance that some referring phrases fail to refer, and Russell's principal contribution here is in his theory of descriptions \cite{russell1956,russellOD}.

Russell's theory treats definite and indefinite descriptions as ``incomplete symbols'', which contribute to the meaning of the sentence as a whole even if they fail to refer.
Such incomplete symbols are only meaningful in certain particular context, and their meaning is given by translated the whole into some other phrase in which the incomplete symbol does not occur and in which there remains no explicit reference to an entity which might not exist.
Usually this involves quantification.
Proper names are then eliminated in favour of descriptions.

Grice's principal aim is to resurrect the conception of names as references, rather than as surrogates for descriptions.
He wants to do this without being forced to regard names of non-existent entities, such as Pegasus, as yielding sentences which are neither true nor false.
This he achieves by allowing that names which do not designate nevertheless refer to some kind of entity which he calls its correlate, and by the rule that predications to non-designating names are to yield falsehoods.

\subsection{Preliminary Formalities}

I consider two different approaches, both derived from Grice, to the problems discussed in \emph{Vacuous Names}\cite{griceVN}.
Much of the discussion concerns matters which are common to both, and this involves some formal material.
In order to avoid replication the formalisation of this common ground is provided first in a separate theory before matters specific to the two variants are entered into.

Common material is in the theory `grice' whose listing may be found in appendix \ref{grice}.

=SML
open_theory "rbjmisc";
force_new_theory "grice";
=TEX

\ignore{
=SML
force_new_pc ⦏"'grice"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'grice";
set_merge_pcs ["rbjmisc", "'grice"];
=TEX
}%ignore

\section{The Problem}\label{G1}

Grice uses several lists in his presentation.
To simplify unambiguous reference I have prefixed some of the numbering schemes with capital letters.

Our starting point is a list of eight \emph{inclinations} supplied by Grice and summarised here:

\begin{itemize}\label{inclinations}\index{inclinations}
\item[I1] That individual constants be admitted.
\item[I2] Note that names are sometimes ``vacuous''
\item[I3] Thence that a constant might lack a designatum.
\item[I4] That excluded middle and bi-valence nevertheless remain unqualified.
\item[I5] That a claim about (predication to) a non-designating constant be false and its negation true.
\item[I6] That no unusual constraints on ``U.I.'' \footnote{Universal Instantiation} and ``E.G.'' \footnote{Existential Generalisation} be introduced.
\item[I7] That the law of identity (in the form $∀x⦁ x=x$) be a theorem\footnote{Which seems to suggest that identity is not a predicate.}.
\item[I8] That derivability implies entailment.\footnote{i.e. that the system be sound!}
\end{itemize}

In relation to these Grice points out two \emph{difficulties} as follows:

\begin{itemize}\label{difficulties}\index{difficulties}
\item[(a)] I2, I3 and I7 between them seem \emph{prima facie} to enable proofs of the existence of non-existent entities (e.g. ``Pegasus exists'').

\item[(b)] I5 and I6 would if gratified permit us to infer that there exists something which does not fly from the premise that Pegasus does not exist.

\end{itemize}

He then lists five possible \emph{resolutions} the difficulties:

\begin{itemize}\label{resolutions}\index{resolutions}
\item[R1] To resist I3 and insist that constants have a designatum.
\item[R2] Resisting I4 and I5, insist that predications to non designating terms and their negations lack a truth value. 
\item[R3] Resist I1 and do without individual constants.
\item[R4] Resist I2 by insisting that all constants have a designatum, which might perhaps ``be'' without existing.
\item[R5] Resist I6 by adding requirements on existential generalisation that the relevant constant be shown to designate.
\item[R6] Resist I8, allowing that the deductive system be not strictly sound, but only so subject to the condition (or ``marginal'' assumption) that all names have bearers.
\end{itemize}

Grice does not discuss any of these alternatives, but instead proposes to attempt to square the circle by devising a system which satisfies all these (apparently) incompatible inclinations.

\section{System Q: Objectives}

Grice now proposes a first order predicate calculus meeting two particular objectives, spelt out in five points of further detail.

\begin{itemize}\label{objectives}\index{objectives}
\item[(i)] That a sentence such as ``Pegasus does not fly'' be capable of rendition in two distinct ways one of which will be true and the other false in the case that Pegasus does not exist. 
These correspond to disambiguations of the logical structure of the sentence either as predicating non-flying or denying a predication as flying.
\item[(ii)] That in either case the inference from ``Pegasus does not fly'' to ``there is something which does not fly'' is to be admitted.
\end{itemize}

\begin{itemize}\label{objectivesdetailed}\index{objectives!detailed}
\item[O1] U.I. and E.G. are acceptable without special side conditions.
\item[O2] Some sentences involving non-denoting constants will be true and provable.
\item[O3] It will be formally decidable whether a sentence depends for its truth on whether some constant designates.
\item[O4] It will be possible to find in Q representation of sentences such as ``Pegasus exists''.
\item[O5] There will be an extension of Q in which identity is represented.\footnote{No discussion here of whether identity is a predicate.}
\end{itemize}

\section{Classical Logic using HOL}

Grice tries to make his system as close as possible to ``classical logic'', basing his system on a first order predicate calculus presented as a natural deduction system based on a textbook by Mates \cite{matesEL}.
I hope that the pertinent sense of ``classical'' here is \emph{two-valued}.

In this presentation we work with a ``classical'' higher order logic (based on Church's formulation of the Simple Theory of Types\cite{church40}) in the form of a sequent calculus.
In this section we replicate in this system theorems which show the closeness of the relationship between this classical logic and the one from which Grice departs.

Grice discusses the problem of the scope of names before getting into the details of his classical logic, but since we here adopt a different manner of resolving this problem which depends upon special features of our ``classical logic'', the discussion of scope belongs here.

\subsection{Scope}

A part of the novelty and difficulty in system Q lies in its special provisions for controlling the ``scope'' of names.

The use of the word scope in this context is distinct from its more common usage (at least in mathematical logic and computer science) in which the (or a) scope of a name (variable or constant) is a syntactic region within which it may be used with the same sense (as opposed to uses of the same name for entirely distinct purposes as may appear in different scopes of the name).

In this case the relevant ambiguity of scope is not a region of significance of the name, but the extent of some predicate applied to the name.
Thus in the example used by Grice, there is an ambiguity in the sentence ``Pegasus does not fly'' about the logical structure of the sentence which leaves doubt about what predicate is being applied to Pegasus.
We may regard the sentences as predicating ``x does not fly'' of Pegasus, or we may be denying that the predicate ``flies'' applies to Pegasus.
The question is whether the negation is part of the predicate or is applied to the result of the predication.

In System Q Grice provides a predicate logic in which numerical subscripts may be used to disambiguate the predications which are taking place.
Unfortunately, this notation, like the dot notation in Principia Mathematica is not as readable as the more usual use of brackets for disambiguating scope.
Furthermore, this aspect of the syntax would be hard to replicate by the methods we propose to adopt, which are intended to permit a lightweight analysis of semantic issues and their connection with the validity of sentences and the soundness of derivations.

In our analysis we will therefore provide for the desired control over predication by the use of Church's lambda notation.
We expect that our syntax will be readily related to that of System Q, but since the system we formalise is at least syntactically distinct we will call it system C\footnote{This in homage to Rudolf Carnap, Q having been chosen by Grice in homage to Quine, and G having been chosen by Myro\cite{grice86a,myroIT} in homage to Grice.}.

System C is obtained by conservative extension to HOL, which is a version of higher order logic derived directly from Church's Simple Theory of Types \cite{church40}.
Church's STT\index{STT} is distinctive for its very slender logical core, achieved by building the logical system from the simply typed lambda calculus.
In this logical system boolean valued functions serve for predication, and the ideas of Grice on vacuous names are realised principally by defining a different kind of predication.
To minimise confusion, the word predicate will only be used when Grice's notion of predication is intended, otherwise propositional or boolean valued function will be used.


The use of lambda notation for making explicit the predicate to be applied may be illustrated simply using Grice's Pegasus example.
In using this method we must distinguish two kinds of predication.
The kind whose scope we are now discussing, which is the only kind of predication in System Q, and the kind of predication which we have in HOL, consisting in the application of a propositional function to some argument.
Henceforth these two will be distinguished by using the term ``predication'' only for the former, by making this kind of predication explicit in the concrete syntax as a copula, and by using the phrase ``application of a propositional function'' for the second kind of predication.
The use of a copula not only visually distinguishes Griceian predication, but also allows us to control its semantics through the definition of the copula.

The copula will be the word ``is'', and since we will be discussion more than one variant of Grice's system, the copulas will be distinguished by subscripts giving the name of the system to which they belong.
In System C, then, the copula is ``$is⋎c$'', so the application of the predicate ``$Flier$'' to the term ``$Pegasus$'' will be written ``%
=INLINEFT
Pegasus is⋎c Flier
=TEX
''.

The two variants of ``Pegasus does not fly'' are then expressed as:

\begin{centering}
``%
=INLINEFT
¬ (Pegasus is⋎c Flier)
=TEX
\end{centering}
''

and

\begin{centering}
``%
=INLINEFT
Pegasus is⋎c (λx⦁ ¬ Flier x)
=TEX
''.
\end{centering}

In the first case the predicate applied to Pegasus is $⌜Flier⌝$, in the second case it is $⌜λx⦁ ¬ Flier\ x⌝$ (which is a negation of Flier, ``not a flier'').

This technique makes it possible to examine the semantic aspects of System Q using formal machine assisted deductive reasoning, while avoiding the special intricacies of formalising Grice's special syntax.
Whether this pays off in terms of perspicuity and penetration in the analysis remains to be seen.

We will therefore offer no further discussion of Grices notational devices for scoping at this point, but may consider later how much may have been lost by this approach.

At this stage I am looking at two alternatives for the underpining semantics, and the following two section work through these two alternatives.
In each case, we are devising a ``shallow embedding'' of something close to Grice's System Q in {\Product} HOL.
These embedded aproximations to System Q are called System C (in homage to Rudolf Carnap) and System S (a nod to Speranza).

\subsection{Semantic Domains}

Grice goes on from his discussions of scope to the presentation of the remaining aspects of the syntax, notably of the various aspects of the deductive system.

We will track this discussion of inference in a semantic way, demonstrating the semantic principles which ensure the soundness of the deductive system presented in a manner which makes reasonably clear the relationship between the two.
This amounts to a semantic embedding into HOL of a system which is intended to be semantically parallel to system Q, though not syntactically quite the same.

To do this we must first provide some basic definitions on which the semantics is based, and before doing that I must explain part of the method of semantic embedding which might seem to, but does not in fact, prejudice one of the principle issues at stake.
That is that the embedding consists in a development of a semantics which is purely denotational, i.e. in which every expression has a denotatum.
These denotation need not be what one would naturally suppose the reference of an expression to be, they may be purely abstract surrogates which suffice to describe the truth conditions of the language.
So the way we model a language in which term expressions may not denote, is by taking the range of things which they might possibly denote, and adding one or more extra items which are values which they are give to indicate that they have no denotation.

\subsubsection{Interpretations}

Grice's definition of an interpretation of Q (VIII A of \cite{griceVN}) is ambiguous in what it says about the domain of an interpretation.
The domain is a set of correlates, some of which may be unit sets the element of which is a designatum.
Grice tells us that there need not be any such unit sets, but does not say explicitly that there may be no other correlates.
He does tell us that he has in mind that there will be exactly one non-designating correlate, the empty set, but he does not place this as a requirement, so the significance of his having this in mind is unclear.

There are three possibilities concerning the number of non-designating correlates in an interpretation, that there are none, exactly one, or more than one.
In relation to these there are a number of possible positions in relation to the definition of an interpretation, the most obvious are:

\begin{enumerate}
\item no constraint
\item there must be at least one
\item there must be exactly one
\end{enumerate}

Of course there may be more, but I propose to discuss just these three.

From a literal reading of Grice in this section I would take the first.
However, from the fact that he explicitly allows there to be no designata but does not explicitly say this for non-designating correlates, we might infer that he intends  but does not state that there will be at least one non-designating correlate.
Alternatively we might take the case he had in mind more presciptively and work with item 3.

These are significant semantically, of course.

Allowing interpretations with no designata will create problems with descriptions if these were to be introduced into Q, for one would then have no correlate available for a non-designating descriptions.
It also affects a matter which Grice later discusses, which is whether certain existential claims are valid, notably the claim that there is something which does not exist.
This (or something similar ``
=INLINEFT
∃x⋎4. ¬⋎3 F⋎1 x⋎2''
=TEX
'', VIII B p137) Grice later claims to be valid, and this is evidence against interpretation 1 in favour of 2 or 3.

Item 2, though the one perhaps preferred by Grice, has the disadvantage that all non-designating terms have the same correlate, and will therefore be equal in a sense of equality which satisfies the universal law of reflexivity of identity.
Do we want Pegasus and Sherlock Holmes to be identical?

Nevertheless, in our shallow embedding of Q we will adopt 2, for, in addition to its possible preferment by Grice, and its confirming Grice's belief in the validity of the cited existentials, it allows a simpler and more transparent shallow embedding than either of the others.
\emph{[fuller explanation to be supplied]}

First let us give a name for the domain of discourse of an interpretation of the language $Q$.
We will suppose this to be a ``type'' in HOL, but will leave open the type by using a type variable.
To serve as denotions for terms in system $G_{HP}$ we use a disjoint union of two types, the first of which is the type of those things which do exist (candidate designata) and the second is a type of surrogates (``correllates'' in Grice) for those things which do not exist.
We use \emph{V} for Value.

\subsection{Descriptions}

When Grice comes to discuss descriptions he has in mind a distinction between descriptions and names which would impact upon the kind of interpretation necessary for a semantic embedding.
This in turn would impact the detailed definition of the copula.

To make apparent the differences which would arise in treating descriptions as Grice intends we provide two treatments of those aspects of the logical system which depend upon the details of the semantics.
These will be called System C and System S.

Certain aspects of our presentation, particularly those which simply illustrate the correspondence between the classical propositional logic in System Q and that in {\Product-HOL}, are common to System C and System S and are therefore treated first.

\subsection{Propositional Logic}\label{PropRules}

The following material is common to Systems C and S and shows how these systems relate to the propositional logic in System Q.
Since we are working with a semantic embedding rather than a syntactic meta-theory we cannot prove results about derivations and instead present proofs about the semantics which show that the required inference rules would be sound.

To do this we adopt a notation for expressing entailment in C in a manner parallel to the presentation of the natural deduction system of Q.
This is done by defining the infix relationship
=INLINEFT
(al Ξ c)
=TEX
\ holding between a list of assumptions (or premises) \emph{al} and a single conclusion \emph{c} when the conclusion is entailed by the premises.

=SML
declare_infix(4, "Ξ");
=TEX

ⓈHOLCONST
│ $Ξ : BOOL LIST → BOOL → BOOL
├──────
│ ∀al c⦁ (al Ξ c) ⇔ (∀⋎L al) ⇒ c
■

In the following theorems which capture the content of Grices rules for Q as theorems of C, the variables φ, ψ, ζ... range over formulae (boolean terms) and Γ, Δ, Θ... over lists (finite sequences) of formulae.
$P$ ranges over propositional functions, values whose types are instances of ⓣ'a → BOOL⌝ (in which $'a$ is a type variable). 
The notation ``[φ; ψ; ...]'' is an explicit list formation (``[φ]'' being a single element list) and the symbol ``$⁀$'' is the concatenation operator over lists.

In general the rules of Q can be formulated as theorems of HOL because in a higher order logic, and can quantify over predicates.
This means that where substitution is involved in a rule, this is captured as a theorem by the use of a variable as a predicate applied to a variable as an argument.
When such a theorem is instantiated using a lambda expression as the predicate, the substitution into the expression will be achieved by beta-reduction.

=GFT
⦏ASS⦎ =	⊢ ∀ φ⦁ [φ] Ξ φ
⦏RAA⦎ =	⊢ ∀φ ψ ζ Γ⦁ ([φ] ⁀ Γ Ξ ψ ∧ ¬ψ) ⇒ (Γ Ξ ¬φ)
⦏DN⦎ =	⊢ ∀ φ⦁ [¬ ¬ φ] Ξ φ
⦏∧I⦎ =		⊢ ∀ φ ψ⦁ [φ; ψ] Ξ φ ∧ ψ
⦏∧E⦎ =	⊢ ∀ φ ψ⦁ ([φ ∧ ψ] Ξ φ) ∧ ([φ ∧ ψ] Ξ ψ)
⦏∨I⦎ =		⊢ ∀ φ ψ⦁ ([φ] Ξ φ ∨ ψ) ∧ ([φ] Ξ ψ ∨ φ)
⦏∨E⦎ =	⊢ ∀ φ ψ ζ Γ Δ Θ⦁ ([φ] ⁀ Γ Ξ ζ) ∧ ([ψ] ⁀ Δ Ξ ζ) ∧ (Θ Ξ φ ∨ ψ)
			⇒ (Γ ⁀ Δ ⁀ Θ Ξ ζ)
⦏CP⦎ =	⊢ ∀ φ ψ Γ⦁ ([φ] ⁀ Γ Ξ ψ) ⇒ (Γ Ξ φ ⇒ ψ)
⦏MPP⦎ =	⊢ ∀ φ ψ⦁ [φ ⇒ ψ; φ] Ξ ψ
=TEX

\ignore{
=SML
val Ξ_def = get_spec ⌜$Ξ⌝;

set_goal([], ⌜∀φ⦁ [φ] Ξ φ⌝);
a (rewrite_tac [Ξ_def] THEN REPEAT strip_tac);
val ASS = save_pop_thm "ASS";

set_goal([], ⌜∀φ ψ ζ Γ⦁ ([φ]⁀ Γ Ξ ψ ∧ ¬ψ) ⇒ (Γ Ξ ¬φ)⌝);
a (rewrite_tac [Ξ_def, append_def, ∀⋎L_def, fold_def] THEN REPEAT strip_tac);
val RAA = save_pop_thm "RAA";

set_goal([], ⌜∀φ⦁ [¬¬φ] Ξ φ⌝);
a (rewrite_tac [Ξ_def] THEN REPEAT strip_tac);
val DN = save_pop_thm "DN";

set_goal([], ⌜∀φ ψ⦁ [φ; ψ] Ξ φ ∧ ψ⌝);
a (rewrite_tac [Ξ_def, ∀⋎L_def, fold_def] THEN REPEAT strip_tac);
val ∧I = save_pop_thm "∧I";

set_goal([], ⌜∀φ ψ⦁ ([φ ∧ ψ] Ξ φ) ∧ ([φ ∧ ψ] Ξ ψ)⌝);
a (rewrite_tac [Ξ_def, ∀⋎L_def, fold_def] THEN REPEAT strip_tac);
val ∧E = save_pop_thm "∧E";

set_goal([], ⌜∀φ ψ⦁ ([φ] Ξ φ ∨ ψ) ∧ ([φ] Ξ ψ ∨ φ)⌝);
a (rewrite_tac [Ξ_def, ∀⋎L_def, fold_def] THEN REPEAT strip_tac);
val ∨I = save_pop_thm "∨I";

set_goal([], ⌜∀φ ψ (ζ:BOOL) (Γ:BOOL LIST) (Δ:BOOL LIST) (Θ:BOOL LIST)⦁ ([φ]⁀ Γ Ξ ζ) ∧ ([ψ]⁀ Δ Ξ ζ) ∧ (Θ Ξ φ ∨ ψ) ⇒ (Γ ⁀ Δ ⁀ Θ Ξ ζ)⌝);
a (rewrite_tac [Ξ_def] THEN REPEAT strip_tac);
val ∨E = save_pop_thm "∨E";

set_goal([], ⌜∀φ ψ Γ⦁ ([φ]⁀ Γ Ξ ψ) ⇒ (Γ Ξ φ ⇒ ψ)⌝);
a (rewrite_tac [Ξ_def, append_def, ∀⋎L_def, fold_def] THEN REPEAT strip_tac);
val CP = save_pop_thm "CP";

set_goal([], ⌜∀φ ψ⦁ ([φ ⇒ ψ; φ] Ξ ψ)⌝);
a (rewrite_tac [Ξ_def, append_def, ∀⋎L_def, fold_def] THEN REPEAT strip_tac);
val MPP = save_pop_thm "MPP";
=TEX
}%ignore

\subsection{Quantifier Inference-Rules}

We now show the correspondence between the quantification rule in System Q with the standard quantifiers in HOL.
Because of this correspondence we can use the standard HOL quantifiers in System C and get a good correspondence with System Q in this area.
When we come to System S it will be necessary to redefine the quantifiers to obtain those qualifications on $∀E$ and $∃I$ which are necessary to cope with Grice's ideas about failing descriptions.

=GFT
⦏∀I⦎ =		⊢ ∀ Γ P⦁ (∀ x⦁ Γ Ξ P x) ⇒ (Γ Ξ (∀ x⦁ P x))
⦏∀E⦎ =		⊢ ∀ Γ P c⦁ (Γ Ξ (∀ x⦁ P x)) ⇒ (Γ Ξ P c)
⦏∃I⦎ =		⊢ ∀ Γ P x⦁ (Γ Ξ P x) ⇒ (Γ Ξ (∃ x⦁ P x))
⦏∃E⦎ =		⊢ ∀ P Q⦁ (∀ x⦁ [P x] Ξ Q) ⇒ ([∃ x⦁ P x] Ξ Q)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ Γ P⦁ (∀x⦁ (Γ Ξ P x)) ⇒ (Γ Ξ ∀x⦁ P x)⌝);
a (rewrite_tac [Ξ_def] THEN REPEAT strip_tac THEN asm_fc_tac[] THEN asm_rewrite_tac[]);
val ∀I = save_pop_thm "∀I";

set_goal([], ⌜∀ Γ P c⦁ (Γ Ξ ∀x⦁ P x) ⇒ (Γ Ξ P c)⌝);
a (rewrite_tac [Ξ_def] THEN REPEAT strip_tac THEN asm_fc_tac[] THEN asm_rewrite_tac[]);
val ∀E = save_pop_thm "∀E";

set_goal([], ⌜∀ Γ P x⦁ (Γ Ξ P x) ⇒ (Γ Ξ ∃x⦁ P x)⌝);
a (rewrite_tac [Ξ_def] THEN REPEAT strip_tac);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val ∃I = save_pop_thm "∃I";

set_goal([], ⌜∀ P Q⦁ (∀x⦁ ([P x] Ξ Q)) ⇒ ([∃x⦁ P x] Ξ Q)⌝);
a (rewrite_tac [Ξ_def] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
val ∃E = save_pop_thm "∃E";
=TEX
}%ignore

\subsection{P Committal}

The notion of E-committal is defined syntactically by Grice, and tells us which formulae in System Q are true only if some name has a designatum, i.e. to the existence of which named individuals our assertion of the formula would commit us.

In HOL we can formalise this idea without resort to reasoning about syntax, furthermore, the main detail in the definition is independent of whether we are in System C or System S, and is therefore provided here.
To achieve this we parameterise the definition of E-committal so that it can be specialised to the different ways of asserting existence in Systems C and S, the parameterised version being called \emph{P\_committal}.

The formal criteria for \emph{E\_committal} then becomes provability in HOL (which is not in general decidable).

In Grice \emph{E\_committal} is a relationship, here it is a parameterised property of propositional functions (the parameter being the relevant notion of existence).

=SML
declare_infix(100, "committal");
=TEX

ⓈHOLCONST
│ $⦏committal⦎ : ('a → BOOL) → ('a → BOOL) → BOOL
├──────
│ ∀P φ⦁ P committal φ ⇔ ∀α⦁ φ α ⇒ P α
■

The following theorems correspond to clauses in Grice's definition of \emph{E\_committal}:

=GFT
⦏P_2⦎ =	⊢ ∀ P φ⦁ P committal φ
			⇒ P committal (λα⦁ ¬ ¬ φ α)
⦏P_3⦎ =	⊢ ∀ P φ ψ⦁ P committal φ ∨ P committal ψ
			⇒ P committal (λ α⦁ φ α ∧ ψ α)
⦏P_4⦎ =	⊢ ∀ P φ ψ⦁ P committal φ ∧ P committal ψ
			⇒ P committal (λ α⦁ φ α ∨ ψ α)
⦏P_5⦎ =	⊢ ∀ P φ ψ⦁ P committal (λ α⦁ ¬ φ α) ∧ P committal ψ
			⇒ P committal (λ α⦁ φ α ⇒ ψ α)
⦏P_6∀⦎ =	⊢ ∀ P φ⦁ (∃ β⦁ P committal (φ β))
			⇒ P committal (λ α⦁ ∀ β⦁ φ β α)
=TEX

I have a problem proving the existential element of (6), so this clause is in doubt.
I think Grice should be asking for ``%
=INLINEFT
∀β⦁ ψ(β/ω)
=TEX
'' to be \emph{E\_committal} for α (in system Q), which corresponds in systems C and S to the theorem:

=GFT
⦏P_6∃b⦎ =	⊢ ∀ P φ⦁ (∀ β⦁ P committal (φ β))
			⇒ P committal (λ α⦁ ∃ β⦁ φ β α)
=TEX

(with P suitably instantiated).

\ignore{
=SML
val committal_def = get_spec ⌜$committal⌝;

set_goal([], ⌜∀ P φ⦁ P committal φ ⇒ P committal (λα⦁ ¬ ¬ (φ α))⌝);
a (REPEAT strip_tac THEN asm_rewrite_tac[η_axiom]);
val P_2 = save_pop_thm "P_2";

set_goal([], ⌜∀ P φ ψ⦁ P committal φ ∨ P committal ψ ⇒ P committal (λα⦁ φ α ∧ ψ α)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[committal_def] THEN REPEAT strip_tac THEN asm_fc_tac[]);
val P_3 = save_pop_thm "P_3";

set_goal([], ⌜∀ P φ ψ⦁ P committal φ ∧ P committal ψ ⇒ P committal (λα⦁ φ α ∨ ψ α)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[committal_def] THEN REPEAT strip_tac THEN asm_fc_tac[]);
val P_4 = save_pop_thm "P_4";

set_goal([], ⌜∀ P φ ψ⦁ P committal (λα⦁ ¬ (φ α)) ∧ P committal ψ ⇒ P committal (λα⦁ φ α ⇒ ψ α)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[committal_def] THEN REPEAT strip_tac THEN asm_fc_tac[]);
val P_5 = save_pop_thm "P_5";

set_goal([], ⌜∀ P φ⦁ (∃β⦁ P committal (φ β)) ⇒ P committal (λα⦁ ∀β⦁ (φ β) α)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[committal_def] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜β⌝ THEN asm_fc_tac[]);
val P_6∀ = save_pop_thm "P_6∀";

set_goal([], ⌜∀ P φ⦁ (∀β⦁ P committal (φ β)) ⇒ P committal (λα⦁ ∃β⦁ (φ β) α)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[committal_def] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
val P_6∃b = save_pop_thm "P_6∃b";
=TEX
}%ignore

\section{System C}

A new theory is needed which I will call ``griceC'' which is created here:

=SML
open_theory "grice";
force_new_theory "griceC";
set_pc "rbjmisc";
=TEX

Grice introduces a special notion of interpretation in terms of which to give the semantics of Q.
An interpretation has a domain which is a set of correlates, some of which are unit sets, in which case the member of that unit set is called a designatum.
For uniformity of type we assume that all correlates are sets of sets.

We allow the domain of an interpretation to be any type and for some element of that type to be identified as THE non-designating element.

ⓈHOLCONST
│ ⦏⊥⦎: 'a 
├──────
│ T
■
We can then use inequality with $⊥$ as the property of being a designatum.
The structure of these interpretations is isomorphic to that of Grice's preferred notion of interpretation, even though we do not use unit sets for correlates of designating constants.

We may use HOL constants of appropriate type for Q constants and predicates, and HOL variables for Q variables, and the consequence should be that the theorems provable in HOL should be just those which are valid in Q.

This is done by using T and F instead of Corr(1) and Corr(0) respectively.

Now we define our special kind of predication.
This is done by introducing `is' subscripted with `c' as a copula.

=SML
declare_infix (400, "is⋎c");
=TEX

ⓈHOLCONST
│ $is⋎c: 'a → ('a → BOOL) → BOOL
├──────
│ ∀ p t⦁ t is⋎c p ⇔ if t = ⊥ then F else p t
■

The definition says, if the term denotes then apply the predicate to the value denoted, otherwise the result of the predication is F (false).

Note that this will not work for relations, we would have to define a separate similar predicator for each arity of relation in use.

Here is the copula for applying a 2-ary relation.

=SML
declare_infix (400, "is⋎c⋎2");
=TEX

ⓈHOLCONST
│ $is⋎c⋎2: ('a × 'b) → ('a × 'b → BOOL) → BOOL
├──────
│ ∀ p t⦁ t is⋎c⋎2 p ⇔ if Fst t = ⊥ ∨ Snd t = ⊥ then F else p t
■

\ignore{
=SML
val is⋎c_def = get_spec ⌜$is⋎c⌝;
val is⋎c⋎2_def = get_spec ⌜$is⋎c⋎2⌝;
=TEX
}%ignore

Now let's introduce Pegasus.
The ``definition'' just says that Pegasus is the non-denoting value.

ⓈHOLCONST
│ ⦏Pegasus⦎ : 'a
├──────
│ Pegasus = ⊥
■

And the predicate \emph{Flier}.
Note that the predicates apply only to real desigata under the normal HOL application, its only under our special predication that they become applicatble to possibly non denoting values.

ⓈHOLCONST
│ ⦏Flier⦎ : 'a → BOOL
├──────
│ T
■

We can now prove in HOL the elementary facts we know about Pegasus flying, yielding the following theorems:

=GFT
⦏Pegasus_lemma_1⦎ =
	⊢ Pegasus is⋎c Flier ⇔ F

⦏Pegasus_lemma_2⦎ =
	⊢ Pegasus is⋎c (λ x⦁ ¬ Flier x) ⇔ F

⦏Pegasus_lemma_3⦎ =
	⊢ ¬ Pegasus is⋎c Flier 

⦏Pegasus_lemma_4⦎ =
	⊢ ¬ Pegasus is⋎c (λ x⦁ ¬ Flier x)
=TEX

\ignore{
=SML
val is⋎c_def = get_spec ⌜$is⋎c⌝;
val Pegasus_def = get_spec ⌜Pegasus⌝;
val Flier_def = get_spec ⌜Flier⌝;

set_goal([], ⌜Pegasus is⋎c Flier ⇔ F⌝);
a (rewrite_tac [is⋎c_def, Pegasus_def]);
val Pegasus_lemma_1 = save_pop_thm "Pegasus_lemma_1";

set_goal([], ⌜Pegasus is⋎c (λ x⦁ ¬ Flier x) ⇔ F⌝);
a (rewrite_tac [is⋎c_def, Pegasus_def]);
val Pegasus_lemma_2 = save_pop_thm "Pegasus_lemma_2";

set_goal([], ⌜¬ Pegasus is⋎c Flier⌝);
a (rewrite_tac [is⋎c_def, Pegasus_def]);
val Pegasus_lemma_3 = save_pop_thm "Pegasus_lemma_3";

set_goal([], ⌜¬ Pegasus is⋎c (λ x⦁ ¬ Flier x)⌝);
a (rewrite_tac [is⋎c_def, Pegasus_def]);
val Pegasus_lemma_4 = save_pop_thm "Pegasus_lemma_4";
=TEX
}%ignore

In case you may doubt the neutrality of our use of lambda expressions, we show here that they are inessential to this approach, and can be dispensed with in favour of explict definitions of the predicates required.
Thus we may instead define a predicate which is the denial of \emph{Flier}:

ⓈHOLCONST
│ ⦏NonFlier⦎ : 'a → BOOL
├──────
│ ∀x⦁ NonFlier x ⇔ ¬ Flier x
■

We can then prove the slightly reworded:

=GFT
⦏Pegasus_lemma_5⦎ = ⊢ Pegasus is⋎c NonFlier ⇔ F
=TEX

the proof of which need not mention the predicate, since it suffices to know that the subject does not exist.

\ignore{
=SML
set_goal([], ⌜Pegasus is⋎c NonFlier ⇔ F⌝);
a (rewrite_tac [is⋎c_def, Pegasus_def]);
val Pegasus_lemma_5 = save_pop_thm "Pegasus_lemma_5";
=TEX
}%ignore

This general claim can be expressed in HOL and proven.
To make it read sensibly however, it is best for us to define the relevant notion of existence.

ⓈHOLCONST
│ ⦏Existent⦎ : 'a → BOOL
├──────
│ ∀x⦁ Existent x ⇔ T
■

The definition looks a bit bizarre and works for just the same reason that we do not need to know the predicate to know that predication to a non-existent will be false.
This predicate will always be true, unless it is applied to a term which fails to denote.
So we satisfy another of Grice's desiderata, that the non-existence of Pegasus can be stated.

But first a more general result:

=GFT
⦏Existent_lemma_1⦎ =
	⊢ ∀ P x⦁ ¬ x is⋎c Existent ⇒ ¬ x is⋎c P
=TEX

\ignore{
=SML
val Existent_def = get_spec ⌜Existent⌝;

set_goal([], ⌜∀P x⦁ ¬ (x is⋎c Existent) ⇒ ¬ (x is⋎c P)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [is⋎c_def, Existent_def]
	THEN REPEAT strip_tac);
val Existent_lemma_1 = save_pop_thm "Existent_lemma_1";
=TEX
}%ignore

Desideratum A8 is satisfied by the standard quantifiers in HOL.

=GFT
⦏∃_lemma_1⦎ = 
	⊢ ∀ P⦁ Pegasus is⋎c P ⇒ (∃ x⦁ x is⋎c P)

⦏∀_lemma_1⦎ =
	⊢ ∀ P⦁ (∀ x⦁ x is⋎c P) ⇒ Pegasus is⋎c P
=TEX

\ignore{
=SML
set_goal([], ⌜∀P:'a → BOOL⦁ Pegasus is⋎c P ⇒ (∃ x⦁ x is⋎c P)⌝);
a (REPEAT strip_tac);
a (∃_tac ⌜Pegasus⌝);
a (asm_rewrite_tac []);
val ∃_lemma_1 = save_pop_thm "∃_lemma_1";

set_goal([], ⌜∀P⦁ (∀ x⦁ x is⋎c P) ⇒ Pegasus is⋎c P⌝);
a (REPEAT strip_tac);
a (asm_rewrite_tac []);
val ∀_lemma_1 = save_pop_thm "∀_lemma_1";
=TEX
}%ignore


\ignore{
=SML
force_new_pc "'griceC";
merge_pcs ["'savedthm_cs_∃_proof"] "'griceC";
set_merge_pcs ["rbjmisc", "'griceC"];
=TEX
}%ignore

\subsection{Quantifier Inference-Rules}

An example of the effect of substitutions obtained by use of these theorems in C intended to mimic the rules of Q is as follows.

Take ths simple case of $∀E$, with the predicate
=INLINEFT
λx⦁ ¬ x is⋎c Flier
=TEX
, which we seek to instantiate to Pegasus.

We can specialise $∀E$ to this case like this:
=SML
val sve = list_∀_elim [⌜[]:BOOL LIST⌝, ⌜λx⦁ ¬ x is⋎c Flier⌝, ⌜Pegasus⌝] ∀E;
=TEX

This gives the theorem:

=GFT
val sve =	⊢ ([] Ξ (∀ x⦁ (λ x⦁ ¬ x is⋎c Flier) x))
		⇒ ([] Ξ (λ x⦁ ¬ x is⋎c Flier) Pegasus) : THM
=TEX

in which there are two occurrences of the lambda expression in the places previously occupied by the variable $P$.

The substitutions can then be effected by beta reduction which can be achieved by rewriting the theorem as follows:

=SML
rewrite_rule [] sve;
=TEX

Which yields a theorem justifying the required inference.

=GFT
val it = ⊢ ([] Ξ (∀ x⦁ ¬ x is⋎c Flier)) ⇒ ([] Ξ ¬ Pegasus is⋎c Flier) : THM
=TEX

All the above rules simply explicate the standard aspects of the logic of Q and C and do not reflect the specific additional features which Grice requires in connection with vacuous names.
They simply illustrate that the logical context for C includes as much standard logic as is provided in Q, and provide some tenuous indication that Grice's rules conform to standard logic as defined in Church's simple theory of types.
The main risk for Grice is in the detail of his presentation, bearing in mind the additional complexities arising from his suffix notation, and the above exercise offers no assurance in that matter.

\subsection{Existence}

\subsubsection{A. (E Committal)}

We have already defined the predicate ``Existent'' which tells us whether a name designates.

The following theorem indicates that the propositional function captures the intent of Grice's ``+exists'' notation.

=GFT
⦏E1⦎ =	⊢ ∀φ α⦁ α is⋎c φ ⇒ α is⋎c Existent
=TEX

\ignore{
=SML
set_goal([], ⌜∀φ α⦁ α is⋎c φ ⇒ α is⋎c Existent⌝);
a (REPEAT ∀_tac THEN rewrite_tac [Existent_def, get_spec ⌜$is⋎c⌝]);
a (cond_cases_tac ⌜α = ⊥⌝);
val E1 = save_pop_thm "E1";
=TEX
}%ignore

\paragraph{E Committal}

Grice's notion of E committal corresponds in System C to the previously defined generic notion of committal instantiated to the propositional function \emph{Existent}.

The definition we have already given for \emph{Existent} is similar in character and identical in effect to Grices suggestions for \emph{+exists}.

\subsubsection{B. Existentially Quantified Formulae}

This has already been covered.

Grice wishes to distinguish himself from Meinong, but his system allows quantification over non-existents, and he can therefore only distinguish himself from Meinong by distancing himself also from Quine's criterion of ontological committment.
This he could easily do by adopting Carnap's distinction between internal and external questions, and denying that any metaphysical significance attaches to something being counted in the range of quantification.

\subsection{Identity}

HOL already has identity and this identity is good for System C.
In HOL identity is a curried propositional function of polymorphic type ⓣ'a → 'a → BOOL⌝.
If applied using function application the universal law of reflexivity holds.

To get a ``strict'' version of equality (i.e. one which is false when either argument does not exist) it is necessary to uncurry equality so that its type becomes ⓣ('a × 'a) → BOOL⌝ and apply it using the system C copula for binary relations.

These two seem to correspond to Grice's intended two kinds of equality, insofar as the difference between the two is primarily that one does and the other does not allow that there may be true identities between non-denoting names.
However this is achieved in system C by having two quite distinct identity relations only one of which is properly a predicate, and applied through our copula $is⋎c$.
The other is a propositional function which must be applied without use of the copula (because the copula forces strictness, i.e. forces predication to undefined values to yield falsehoods).

Grice seems to think that the required distinction between equalities can be achieved by the use of his scoping subscripts, but I have not yet been convinced that he is correct in this.
Whatever the scope of the predicate, predication to non-denoting names must yield falsehood, so I can't see how any use of subscripts will make ``Pegasus = Pegasus'' to be true.

To illustrate the effect of the built-in equality the following theorems suffice:

=GFT
⦏Pegasus_eq_lemma1⦎ =
	⊢ Pegasus = Pegasus
=TEX

Note the lack of copula.
This is of course an instance of the theorem:

=GFT
⦏eq_refl_thm⦎ =
	⊢ ∀ x⦁ x = x
=TEX

\ignore{
=SML
set_goal([], ⌜Pegasus = Pegasus⌝);
a (rewrite_tac[]);
val Pegasus_eq_lemma1 = save_pop_thm "Pegasus_eq_lemma1";

set_goal([], ⌜∀x⦁ x=x⌝);
a (rewrite_tac[]);
val eq_refl_thm = save_pop_thm "eq_refl_thm";
=TEX
}%ignore

To get a nice notation for ``strong'' equality we need to define it as an infix symbol, which requires that the copula be built into the definition.
We could use the $≡$ symbol, but this usually represents an equivalence relation which is weaker than identity, so we will subscript the $=$ sign with c, suggesting that it is just the same thing applied through our copula.

=SML
declare_infix (200, "=⋎c");
=TEX

ⓈHOLCONST
│ $⦏=⋎c⦎ : 'a → 'a → BOOL
├──────
│ ∀x y:'a⦁ (x =⋎c y) = (x,y) is⋎c⋎2 (Uncurry $=)
■

We can now prove:

=GFT
Pegasus_eq_lemma2 =
	⊢ ¬ Pegasus =⋎c Pegasus
=TEX

And must rest content with the qualified rule:

=GFT
⦏eq⋎c_refl_thm⦎ =
	⊢ ∀ x⦁ x is⋎c Existent ⇔ x =⋎c x
=TEX

The ``strictness'' of this equality is expressed by the theorem (which would have made a better definition):

=GFT
eq⋎c_strict_thm =
	⊢ ∀ x y⦁ x =⋎c y ⇔ x is⋎c Existent ∧ y is⋎c Existent ∧ x = y
=TEX

\ignore{
=SML
val eq⋎c_def = get_spec ⌜$=⋎c⌝;

set_goal([], ⌜¬ Pegasus =⋎c Pegasus⌝);
a (rewrite_tac[eq⋎c_def, is⋎c⋎2_def, Pegasus_def]);
val Pegasus_eq_lemma2 = save_pop_thm "Pegasus_eq_lemma2";

set_goal([], ⌜∀x⦁ x is⋎c Existent ⇔ x =⋎c x⌝);
a (rewrite_tac[eq⋎c_def, is⋎c_def, is⋎c⋎2_def, Existent_def]);
val eq⋎c_refl_thm = save_pop_thm "eq⋎c_refl_thm";

set_goal([], ⌜∀x y⦁ x =⋎c y ⇔ x is⋎c Existent ∧ y is⋎c Existent ∧ x = y⌝);
a (rewrite_tac[eq⋎c_def, is⋎c_def, is⋎c⋎2_def, Existent_def]);
a (REPEAT strip_tac);
val eq⋎c_strict_thm = save_pop_thm "eq⋎c_strict_thm";
=TEX
}%ignore

On reflection Grice's treatment by scoping is presented in the context of a second order definition of equality, and therefore for the weak equality does not define equality as a predicate, but as a second order formula.
Its equivalence to the primitive equality in HOL can be illustrated by the following theorem:

=GFT
⦏snd_order_eq_thm⦎ =
	⊢ ∀ x y⦁ x = y ⇔ (∀ P⦁ x is⋎c P ⇔ y is⋎c P)
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y⦁ x = y ⇔ (∀P⦁ x is⋎c P ⇔ y is⋎c P)⌝);
a (rewrite_tac[is⋎c_def] THEN REPEAT strip_tac THEN_TRY all_var_elim_asm_tac);
a (spec_nth_asm_tac 1 ⌜λz⦁ z = x⌝ THEN all_asm_ante_tac
	THEN_TRY rewrite_tac[] THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac THEN_TRY asm_rewrite_tac[]
	THEN DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac [] THEN REPEAT strip_tac
	THEN SPEC_NTH_ASM_T 1 ⌜λx⦁ x = y⌝ (strip_asm_tac o (rewrite_rule[])));
val snd_order_eq_thm = save_pop_thm "snd_order_eq_thm";
=TEX
}%ignore

This equivalence only holds because we adopted Grice's preferred (but not stipulated) domain of interpretation, in which there is exactly one non-designating correlate.
If there was more than one non-designating correlate then Grice's second order definition would give a notion of identity under which all non-designating correlates are considered equal, which would not be the case for the primitive equality in HOL.

Even in that case a similar device would work as illuatrated by the following theorem:
=GFT
⦏snd_order_eq_thm2⦎ =
	⊢ ∀ x y⦁ x = y ⇔ (∀ P⦁ P x ⇔ P y)
=TEX

In which the griceian copula has been dropped so that the predication is no longer strict.

\ignore{
=SML
set_goal([], ⌜∀x y⦁ x = y ⇔ (∀P⦁ P x ⇔ P y)⌝);
a (REPEAT strip_tac THEN_TRY all_var_elim_asm_tac);
a (SPEC_NTH_ASM_T 1 ⌜λx⦁ x = y⌝ (strip_asm_tac o (rewrite_rule[])));
val snd_order_eq_thm2 = save_pop_thm "snd_order_eq_thm2";
=TEX
}%ignore

\subsection{Names and Descriptions}

I note here pro-tem just that the method adopted in System C for controlling the scope of predications, viz. the use either of lambda expressions or of naming complex predicates by definitions, enables scope to be controlled in predication to descriptions which are formed as terms.
We can therefore follow Grice's system Q in introducing such descriptions.

=SML
declare_binder "ι";
=TEX

ⓈHOLCONST
│ $⦏ι⦎ : ('a → BOOL) → 'a
├──────
│ ∀φ⦁ ($ι φ) = εα⦁ (α is⋎c φ ∧ ∀β⦁ β is⋎c φ ⇒ β = α) 
		∨ (¬∃γ⦁ γ is⋎c φ ∧ ∀β⦁ β is⋎c φ ⇒ β = γ) ∧ α = ⊥
■

=GFT
⦏ι_thm1⦎ = ⊢ ∀ γ⦁ γ is⋎c φ ∧ (∀ β⦁ β is⋎c φ ⇒ β = γ) ⇒ $ι φ = γ
⦏ι_thm2⦎ = ⊢ ¬ (∃ γ⦁ γ is⋎c φ ∧ (∀ β⦁ β is⋎c φ ⇒ β = γ)) ⇒ $ι φ = ⊥
=TEX

\ignore{
=SML
val ι_def = get_spec ⌜$ι⌝;

set_goal([], ⌜∀γ:'a⦁ γ is⋎c φ ∧ (∀β⦁ β is⋎c φ ⇒ β = γ) ⇒ ($ι φ) = γ ⌝);
a (REPEAT strip_tac THEN rewrite_tac [ι_def]);
a (ε_tac ⌜ε α
             ⦁ α is⋎c φ ∧ (∀ β⦁ β is⋎c φ ⇒ β = α)
                 ∨ ¬ (∃ γ⦁ γ is⋎c φ ∧ (∀ β⦁ β is⋎c φ ⇒ β = γ)) ∧ α = ⊥⌝);
(* *** Goal "1" *** *)
a (∃_tac ⌜γ⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_fc_tac[]);
(* *** Goal "3" *** *)
a (asm_rewrite_tac[]);
a (asm_fc_tac[]);
val ι_thm1 = save_pop_thm "ι_thm1";

set_goal([], ⌜(¬∃γ:'a⦁ γ is⋎c φ ∧ (∀β⦁ β is⋎c φ ⇒ β = γ)) ⇒ ($ι φ) = ⊥⌝);
a (strip_tac);
a (REPEAT strip_tac THEN rewrite_tac [ι_def]);
a (ε_tac ⌜ε α
             ⦁ α is⋎c φ ∧ (∀ β⦁ β is⋎c φ ⇒ β = α)
                 ∨ ¬ (∃ γ⦁ γ is⋎c φ ∧ (∀ β⦁ β is⋎c φ ⇒ β = γ)) ∧ α = ⊥⌝);
(* *** Goal "1" *** *)
a (∃_tac ⌜⊥⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 3 ⌜ε α
             ⦁ α is⋎c φ ∧ (∀ β⦁ β is⋎c φ ⇒ β = α)
                 ∨ ¬ (∃ γ⦁ γ is⋎c φ ∧ (∀ β⦁ β is⋎c φ ⇒ β = γ)) ∧ α = ⊥⌝);
a (spec_nth_asm_tac 3 ⌜β⌝);
val ι_thm2 = save_pop_thm "ι_thm2";
=TEX
}%ignore

There is a difficulty in adopting Grice's reticence to allow existential generalisation on the basis of such a predication.
This cannot be supported in system C without changing the underlying semantics.

Grice has effectively split the non-denoting expressions into two, those which correlate with something in the domain of quantification and those which do not.
Since our embedding requires all expressions to have a value, we would have to add another kind of entity into the domain of interpretation and define quantifiers which operate over expressions which have a correlate but not over the values of non-denoting descriptions.

This would effect most of the embedding, the whole would have to be reworked (in a routine way).
We investigate this possibility in the next section.

\section{System S}

System S contains two minor adjustments to System C which are concerned with the treatment of non-designating names and failing descriptions.
In relation to non-designating names, the semantics in System S now allows that they have distinct correlates.
In addition a new subdomain is introduced which provides at least one (since we can always prove that there is a failing description) surrogate for a failing description.
The primary reason for recognising, in the semantics, denotations for failing descriptions, is so that we can arrange as Grice seems to require, that they do not fall into the range of the System S quantifiers.
This in turn results in the qualification of the rules EG and UI.

A new theory is needed which I will call ``griceS'' which is created here:

=SML
open_theory "grice";
force_new_theory "griceS";
set_pc "rbjmisc";
=TEX

We liberalise the notion of interpretation from system C in the following two ways.
Firstly we allow that there may me more than one non-denoting correllate. and hence then there may be semantic distinctions between non-denoting names, overcoming one obstacle to substantial discussions about fictional entities.
Secondly we introduce values to stand for non-referring descriptions.
These are not intended to be values and will be excluded from the range of quantification, with the effect that EG and UI will not work with failing descriptions.

This will be done using a ``disjoint union'' the right disjunct of which will be surrogates for failing descriptions, and the left will be correlates for names of which there will be at least one which is not a denotatum.
The ``normal'' quantifiers for system S will quantify only over the correlates.

\ignore{
=SML
set_goal([], ⌜∃denotatum:'a → BOOL⦁ ∃x⦁ ¬ denotatum x⌝);
a (∃_tac ⌜λy⦁F⌝ THEN ∃_tac ⌜εz⦁T⌝ THEN rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

To effect this we introduce the property of being a denotatum which is left open except to the extent that there must be at least one correlate which is not a denotatum.

ⓈHOLCONST
│ ⦏denotatum⦎: 'a → BOOL
├──────
│ ∃x⦁ ¬ denotatum x
■

\ignore{
=SML
val denotatum_def = get_spec ⌜denotatum⌝;

set_goal([], ⌜∃⊥_corr:'a⦁ ¬ denotatum ⊥_corr⌝);
a (strip_asm_tac denotatum_def);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore


ⓈHOLCONST
│ ⦏⊥_corr⦎: 'a
├──────
│ ¬ denotatum ⊥_corr
■

The type of exressions in System S is given by the following type abbreviation:

=SML
declare_type_abbrev("SC", [], ⓣ'a + 'b⌝);
=TEX


ⓈHOLCONST
│ ⦏⊥⦎: SC
├──────
│ ⊥ = InL ⊥_corr
■

It will be useful to have tests and projections for values of type ⓣSC⌝.

This propositional function tests whether an SC is a correlate:

ⓈHOLCONST
│ ⦏IsCorr⦎: SC → BOOL
├──────
│ ∀v:SC⦁ IsCorr v ⇔ IsL v
■

This function extracts the correlate (of type ⓣ'a⌝) from a value of type ⓣSC⌝.

ⓈHOLCONST
│ ⦏Corr⦎: SC → 'a
├──────
│ ∀v:SC⦁ Corr v = OutL v
■

This propositional function tells us whether a value of type ⓣSC⌝ is a denotatum.

ⓈHOLCONST
│ ⦏IsDen⦎: SC → BOOL
├──────
│ ∀v:SC⦁ IsDen v ⇔ IsCorr v ∧ denotatum (Corr v)
■

There are now difficulties in the treatment of constants and variables, since a HOL constant or variable constrained only by the type of the elements of an interpretation will not be known to denote (which is OK), but will not even be known to correlate, and hence may not even be in the range of quantification.
Such results as can be obtained using unconstrained variables will nevertheless be valid, and will be generalisable.

Now we define our special kind of predication (the copula for System S).

=SML
declare_infix (400, "is⋎s");
=TEX

ⓈHOLCONST
│ $is⋎s: SC → ('a → BOOL) → BOOL
├──────
│ ∀ p t⦁ t is⋎s p ⇔ if IsDen t then p (Corr t) else F
■

The definition says, if the term denotes then apply the predicate to the value denoted, otherwise the result of the predication is F (false).

Note that this will not work for relations, we would have to define a separate similar predicator for each arity of relation in use.

Here is the copula for applying a 2-ary relation.

=SML
declare_infix (400, "is⋎s⋎2");
=TEX

ⓈHOLCONST
│ $is⋎s⋎2: (SC × SC) → ('a × 'a → BOOL) → BOOL
├──────
│ ∀ p t⦁ t is⋎s⋎2 p ⇔	if IsDen (Fst t) ∧ IsDen (Snd t)
			then p (Corr (Fst t), Corr (Snd t))
			else F
■

\ignore{
=SML
val is⋎s_def = get_spec ⌜$is⋎s⌝;
val is⋎s⋎2_def = get_spec ⌜$is⋎s⋎2⌝;
=TEX
}%ignore

Now let's introduce Pegasus.
The ``definition'' just says that Pegasus is a non-denoting correlate.
We know that there must be such a thing (though we don't know that there are any denoting correlates).

\ignore{
=SML
val ⊥_corr_def = get_spec ⌜⊥_corr⌝;
val ⊥_def = get_spec ⌜⊥⌝;
val IsCorr_def = get_spec ⌜IsCorr⌝;
val Corr_def = get_spec ⌜Corr⌝;
val IsDen_def = get_spec ⌜IsDen⌝;

set_goal([], ⌜∃Pegasus:SC⦁ IsCorr Pegasus ∧ ¬ IsDen Pegasus⌝);
a (∃_tac ⌜InL ⊥_corr⌝);
a (rewrite_tac [IsCorr_def, IsDen_def, Corr_def, ⊥_corr_def]);
val _ = save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Pegasus⦎ : SC
├──────
│ IsCorr Pegasus ∧ ¬ IsDen Pegasus
■

And the predicate \emph{Flier}.
Note that the predicates apply only to real desigata under the normal HOL application, its only under our special predication that they become applicatble to possibly non denoting values.

ⓈHOLCONST
│ ⦏Flier⦎ : 'a → BOOL
├──────
│ T
■

We can now prove in HOL the elementary facts we know about Pegasus flying, yielding the following theorems:

=GFT
⦏Pegasus_lemma_1⦎ =
	⊢ Pegasus is⋎s Flier ⇔ F

⦏Pegasus_lemma_2⦎ =
	⊢ Pegasus is⋎s (λ x⦁ ¬ Flier x) ⇔ F

⦏Pegasus_lemma_3⦎ =
	⊢ ¬ Pegasus is⋎s Flier

⦏Pegasus_lemma_4⦎ =
	⊢ ¬ Pegasus is⋎s (λ x⦁ ¬ Flier x)
=TEX

\ignore{
=SML
val Pegasus_def = get_spec ⌜Pegasus⌝;
val Flier_def = get_spec ⌜Flier⌝;

set_goal([], ⌜Pegasus is⋎s Flier ⇔ F⌝);
a (rewrite_tac [is⋎s_def, Pegasus_def]);
val Pegasus_lemma_1 = save_pop_thm "Pegasus_lemma_1";

set_goal([], ⌜Pegasus is⋎s (λx⦁ ¬ Flier x) ⇔ F⌝);
a (rewrite_tac [is⋎s_def, Pegasus_def]);
val Pegasus_lemma_2 = save_pop_thm "Pegasus_lemma_2";

set_goal([], ⌜¬ Pegasus is⋎s Flier⌝);
a (rewrite_tac [is⋎s_def, Pegasus_def]);
val Pegasus_lemma_3 = save_pop_thm "Pegasus_lemma_3";

set_goal([], ⌜¬ Pegasus is⋎s (λx⦁ ¬ Flier x)⌝);
a (rewrite_tac [is⋎s_def, Pegasus_def]);
val Pegasus_lemma_4 = save_pop_thm "Pegasus_lemma_4";
=TEX
}%ignore

In case you may doubt the neutrality of our use of lambda expressions, we show here that they are inessential to this approach, and can be dispensed with in favour of explict definitions of the predicates required.
Thus we may instead define a predicate which is the denial of \emph{Flier}:

ⓈHOLCONST
│ ⦏NonFlier⦎ : 'a → BOOL
├──────
│ ∀x⦁ NonFlier x ⇔ ¬ Flier x
■

We can then prove the slightly reworded:

=GFT
⦏Pegasus_lemma_5⦎ = ⊢ Pegasus is⋎s NonFlier ⇔ F
=TEX

the proof of which need not mention the predicate, since it suffices to know that the subject does not exist.

\ignore{
=SML
set_goal([], ⌜Pegasus is⋎s NonFlier ⇔ F⌝);
a (rewrite_tac [is⋎s_def, Pegasus_def]);
val Pegasus_lemma_5 = save_pop_thm "Pegasus_lemma_5";
=TEX
}%ignore

This general claim can be expressed in HOL and proven.
To make it read sensibly however, it is best for us to define the relevant notion of existence.

ⓈHOLCONST
│ ⦏Existent⦎ : 'a → BOOL
├──────
│ ∀x⦁ Existent x ⇔ T
■

The definition looks a bit bizarre and works for just the same reason that we do not need to know the predicate to know that predication to a non-existent will be false.
This predicate will always be true, unless it is applied to a term which fails to denote.
So we satisfy another of Grice's desiderata, that the non-existence of Pegasus can be stated.

But first a more general result:

=GFT
⦏Existent_lemma_1⦎ =
	⊢ ∀ P x⦁ ¬ x is⋎s Existent ⇒ ¬ x is⋎s P
=TEX

\ignore{
=SML
val Existent_def = get_spec ⌜Existent⌝;

set_goal([], ⌜∀P x⦁ ¬ (x is⋎s Existent) ⇒ ¬ (x is⋎s P)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [is⋎s_def, Existent_def]
	THEN REPEAT strip_tac);
val Existent_lemma_1 = save_pop_thm "Existent_lemma_1";
=TEX
}%ignore

Desideratum A8 is satisfied by the standard quantifiers in HOL.

=GFT
⦏∃_lemma_1⦎ = 
	⊢ ∀ P⦁ Pegasus is⋎s P ⇒ (∃ x⦁ x is⋎s P)

⦏∀_lemma_1⦎ =
	⊢ ∀ P⦁ (∀ x⦁ x is⋎s P) ⇒ Pegasus is⋎s P
=TEX

\ignore{
=SML
set_goal([], ⌜∀P:'a → BOOL⦁ (Pegasus: 'a + 'b) is⋎s P ⇒ (∃ x: 'a + 'b⦁ x is⋎s P)⌝);
a (REPEAT strip_tac);
a (∃_tac ⌜Pegasus⌝);
a (asm_rewrite_tac []);
val ∃_lemma_1 = save_pop_thm "∃_lemma_1";

set_goal([], ⌜∀P⦁ (∀ x: 'a + 'b⦁ x is⋎s P) ⇒ (Pegasus:'a + 'b) is⋎s P⌝);
a (REPEAT strip_tac);
a (asm_rewrite_tac []);
val ∀_lemma_1 = save_pop_thm "∀_lemma_1";
=TEX
}%ignore

However, the HOL native quantifiers are unsatisfactory since they quantify over the values introduced into the domain of the interpretation as correlates for failing descriptions.

This is shown by the following theorem:

=GFT
⦏∃_not_Corr_thm⦎ =
	⊢ ∃ x⦁ ¬ IsCorr x
=TEX

\ignore{
=SML
set_goal([], ⌜∃x:SC⦁ ¬ IsCorr x⌝);
a (rewrite_tac [IsCorr_def]);
a (∃_tac ⌜InR (εx:'b⦁T)⌝ THEN rewrite_tac[]);
val ∃_not_Corr_thm = save_pop_thm "∃_not_Corr_thm";
=TEX
}%ignore


\ignore{
=SML
force_new_pc "'syss";
merge_pcs ["'savedthm_cs_∃_proof"] "'syss";
set_merge_pcs ["rbjmisc", "'syss"];
=TEX
}%ignore

\subsection{Quantifier Definitions}

We now define quantifiers which quantify over correlates only, not over the values of failing descriptions.

Quantifiers are propositional functions over propositional functions, and are usually syntactically ``binders'', so that they are expected to be applied to a lambda abstraction and the lambda in that expression is to be omitted.
We use the usual quantifier symbols subscripted with \emph{s} to distinguish them from the standard quantifiers.

=SML
declare_binder "∀⋎s";
declare_binder "∃⋎s";
=TEX

The domain of interpretation now includes correlates and some other things (for failing descriptions).
The things for failing descriptions are to be excluded from the range of the quantifiers (they really really don't exist) so quantifiers range only over correlates.
The dollar sign locally supresses the binder status for the purpose of giving the definition.

ⓈHOLCONST
│ $⦏∀⋎s⦎ : (SC → BOOL) → BOOL
├──────
│ ∀f⦁ $∀⋎s f ⇔ ∀x⦁ IsCorr x ⇒ f x
■

ⓈHOLCONST
│ $⦏∃⋎s⦎ : (SC → BOOL) → BOOL
├──────
│ ∀f⦁ $∃⋎s f ⇔ ∃x⦁ IsCorr x ∧ f x
■

To express the rules for these new quantifiers we define a new notion of existence.
This cannot be a bona-fide predicate, since such a predicate would of necessity be false of the correlates which are not designata (if applied through the copula), so it must be thought of as a propositional function to be applied without the copula.

ⓈHOLCONST
│ ⦏Existent⋎s⦎ : SC → BOOL
├──────
│ ∀x⦁ Existent⋎s x ⇔ ∃⋎s y⦁ x = y
■

\subsection{Quantifier Inference-Rules}

The propositional rules are common to Systems C and S and are shown above in Section \ref{PropRules}.

We have new quantifiers in System S, and the quantifier rules will be modified accordingly.

=GFT
⦏∀I⋎s⦎ =	⊢ ∀ Γ P⦁ (∀ x⦁ Γ Ξ Existent⋎s x ∧ P x) ⇒ (Γ Ξ (∀⋎s x⦁ P x))
⦏∀E⋎s⦎ =	⊢ ∀ Γ P c⦁ (Γ Ξ Existent⋎s c ∧ (∀⋎s x⦁ P x)) ⇒ (Γ Ξ P c)
⦏∃I⋎s⦎ =	⊢ ∀ Γ P x⦁ (Γ Ξ Existent⋎s x ∧ P x) ⇒ (Γ Ξ (∃⋎s x⦁ P x))
⦏∃E⋎s⦎ =	⊢ ∀ P Q c⦁ (∀ x⦁ [Existent⋎s x ∧ P x] Ξ Q) ⇒ ([∃⋎s x⦁ P x] Ξ Q)
=TEX

\ignore{
=SML
val ∀⋎s_def = get_spec ⌜$∀⋎s⌝;
val ∃⋎s_def = get_spec ⌜$∃⋎s⌝;
val Existent⋎s_def = get_spec ⌜Existent⋎s⌝;

set_goal([], ⌜∀ Γ P⦁ (∀x⦁ (Γ Ξ Existent⋎s x ∧ P x)) ⇒ (Γ Ξ ∀⋎s x⦁ P x)⌝);
a (rewrite_tac [Ξ_def, ∀⋎s_def, Existent⋎s_def] THEN REPEAT strip_tac THEN asm_fc_tac[] THEN asm_rewrite_tac[]);
val ∀I⋎s = save_pop_thm "∀I⋎s";

set_goal([], ⌜∀ Γ P c⦁ (Γ Ξ Existent⋎s c ∧ ∀⋎s x⦁ P x) ⇒ (Γ Ξ P c)⌝);
a (rewrite_tac [Ξ_def, ∃⋎s_def, ∀⋎s_def, Existent⋎s_def] THEN REPEAT strip_tac THEN asm_fc_tac[] THEN_TRY asm_rewrite_tac[]);
val ∀E⋎s = save_pop_thm "∀E⋎s";

set_goal([], ⌜∀ Γ P x⦁ (Γ Ξ Existent⋎s x ∧ P x) ⇒ (Γ Ξ ∃⋎s x⦁ P x)⌝);
a (rewrite_tac [Ξ_def, ∃⋎s_def, Existent⋎s_def] THEN REPEAT strip_tac);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val ∃I⋎s = save_pop_thm "∃I⋎s";

push_extend_pc "'mmp1";

set_goal([], ⌜∀ P Q c⦁ (∀x⦁ ([Existent⋎s x ∧ P x] Ξ Q)) ⇒ ([∃⋎s x⦁ P x] Ξ Q)⌝);
a (rewrite_tac [Ξ_def, ∃⋎s_def, Existent⋎s_def] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
val ∃E⋎s = save_pop_thm "∃E⋎s";

pop_pc();
=TEX
}%ignore


An example of the effect of substitutions obtained by use of these theorems in S intended to mimic the rules of Q is as follows.

Take ths simple case of $∀E⋎s$, with the predicate
=INLINEFT
λx⦁ ¬ x is⋎s Flier
=TEX
 which we seek to instantiate to Pegasus.

We can specialise $∀E⋎s$ to this case like this:

=SML
val sves = list_∀_elim [⌜[]:BOOL LIST⌝, ⌜λx: 'a + 'b⦁ ¬ x is⋎s Flier⌝, ⌜Pegasus⌝] ∀E⋎s;
=TEX

This gives the theorem:

=GFT
val sves =	⊢ ([] Ξ Existent⋎s Pegasus ∧ (∀⋎s x⦁ (λ x⦁ ¬ x is⋎s Flier) x))
			⇒ ([] Ξ (λ x⦁ ¬ x is⋎s Flier) Pegasus) : THM
=TEX

in which there are two occurrences of the lambda expression in the places previously occupied by the variable $P$.

The substitutions can then be effected by beta reduction which can be achieved by rewriting the theorem as follows:

=SML
rewrite_rule [] sves;
=TEX

Which yields a theorem justifying the required inference.

=GFT
val it =	⊢ ([] Ξ Existent⋎s Pegasus ∧ (∀⋎s x⦁ ¬ x is⋎s Flier))
			⇒ ([] Ξ ¬ Pegasus is⋎s Flier) : THM
=TEX

\subsection{Existence}

\subsubsection{A. (E Committal)}

We have already defined the propositional function ``Existent'' which tells us whether a name designates.

The following theorem indicates that the propositional function captures the intent of Grice's ``+exists'' notation.

=GFT
⦏E1⦎ =	⊢ ∀ φ α⦁ α is⋎s φ ⇒ Existent α
=TEX

\ignore{
=SML
set_goal([], ⌜∀φ α⦁ α is⋎s φ ⇒ Existent α⌝);
a (REPEAT ∀_tac THEN rewrite_tac [Existent_def, get_spec ⌜$is⋎s⌝]);
val E1 = save_pop_thm "E1";
=TEX
}%ignore

Once again, Grice's notion of \emph{E\_committal} is obtainable for System S by instantiation of our generic notion of \emph{committal} by the propositional function \emph{Existent}.

The definition we have already given for \emph{Existent} is similar in character and identical in effect to Grices suggestions for \emph{+exists}.

\subsubsection{B. Existentially Quantified Formulae}

This has already been covered.

Grice wishes to distinguish himself from Meinong, but his system allows quantification over non-existents, and he can therefore only distinguish himself from Meinong by distancing himself also from Quine's criteria of ontological committment.
This he could easily do by adopting Carnap's distinction between internal and external questions, and denying that any metaphysical significance attaches to something being counted in the range of quantification.

\subsection{Identity}

HOL already has identity and this identity is good for System C.
It HOL it is a curried propositional function of polymorphic type ⓣ'a → 'a → BOOL⌝.
If applied using function application the universal law of reflexivity holds.

To get a ``strict'' version of equality (i.e. one which is false when either argument does not exist) it is necessary to uncurry equality so that its type becomes ⓣ('a × 'a) → BOOL⌝ and apply it using the system C copula for binary relations.

These two seem to correspond to Grice's intended two kinds of equality insofar as the difference between the two is primarily that one does and the other does not allow that there may be true identities between non-denoting names.
However this is achieved in system C by having two quite distinct identity relations only one of which is properly a predicate, and applied through our copula $is⋎s$.
The other is a propositional function which must be applied without use of the copula (because the copula forces strictness, i.e. forces predication to undefined values to yield falsehoods).

Grice seems to think that the required distinction between equalities can be achieved by the use of his scoping subscripts, but I have not yet been convinced that his is correct in this.
Whatever the scope of the predicate, predication to non-denoting names must yield falsehood, so I can't see how any use of subscripts will make ``Pegasus = Pegasus'' true.

To illustrate the effect of the built in equality the following theorems suffice:

=GFT
⦏Pegasus_eq_lemma1⦎ =
	⊢ Pegasus = Pegasus
=TEX

Note the lack of copula.
This is of course an instance of the theorem:

=GFT
⦏eq_refl_thm⦎ =
	⊢ ∀ x⦁ x = x
=TEX

\ignore{
=SML
set_goal([], ⌜Pegasus = Pegasus⌝);
a (rewrite_tac[]);
val Pegasus_eq_lemma1 = save_pop_thm "Pegasus_eq_lemma1";

set_goal([], ⌜∀x⦁ x=x⌝);
a (rewrite_tac[]);
val eq_refl_thm = save_pop_thm "eq_refl_thm";
=TEX
}%ignore

To get a nice notation for ``strong'' equality we need to define it as an infix symbol, which requires that the copula be built into the definition.
We could use the $≡$ symbol, but this usually represents an equivalence relation which is weaker than identity, so we will subscript the $=$ sign with g, suggesting that it is just the same thing applied through our copula.

=SML
declare_infix (200, "=⋎s");
=TEX

ⓈHOLCONST
│ $⦏=⋎s⦎ : SC → SC → BOOL
├──────
│ ∀x y:SC⦁ (x =⋎s y) = (x,y) is⋎s⋎2 (Uncurry $=)
■

We can now prove:

=GFT
Pegasus_eq_lemma2 =
	⊢ ¬ Pegasus =⋎s Pegasus
=TEX

And must rest content with the qualified rule:

=GFT
⦏eq⋎s_refl_thm⦎ =
	⊢ ∀ x⦁ x is⋎s Existent ⇔ x =⋎s x
=TEX

The ``strictness'' of this equality is expressed by the theorem (which would have made a better definition):

=GFT
eq⋎s_strict_thm =
	⊢ ∀ x y⦁ x =⋎s y ⇔ x is⋎s Existent ∧ y is⋎s Existent ∧ x = y
=TEX

\ignore{
=SML
val eq⋎s_def = get_spec ⌜$=⋎s⌝;

set_goal([], ⌜¬ Pegasus =⋎s Pegasus⌝);
a (rewrite_tac[eq⋎s_def, is⋎s⋎2_def, Pegasus_def]);
val Pegasus_eq_lemma2 = save_pop_thm "Pegasus_eq_lemma2";

set_goal([], ⌜∀x⦁ x is⋎s Existent ⇔ x =⋎s x⌝);
a (rewrite_tac[eq⋎s_def, is⋎s_def, is⋎s⋎2_def, Existent_def]);
val eq⋎s_refl_thm = save_pop_thm "eq⋎s_refl_thm";

set_goal([], ⌜∀x y⦁ x =⋎s y ⇔ x is⋎s Existent ∧ y is⋎s Existent ∧ x = y⌝);
a (rewrite_tac[eq⋎s_def, is⋎s_def, is⋎s⋎2_def, Existent_def, IsDen_def, IsCorr_def, Corr_def]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (fc_tac [sum_clauses]);
a (DROP_ASM_T ⌜InL (OutL x) = x⌝ ante_tac THEN asm_rewrite_tac[]);
a (STRIP_T rewrite_thm_tac);
val eq⋎s_strict_thm = save_pop_thm "eq⋎s_strict_thm";
=TEX
}%ignore

The primitive equality in HOL no longer corresponds to Grice's second order definition and the proof of $snd\_order\_eq\_thm$ fails.

=GFT
⦏neg_snd_order_eq_thm⦎ =
	⊢ ¬ (∀ x y⦁ x = y ⇔ (∀ P⦁ x is⋎s P ⇔ y is⋎s P))
=TEX

There are two reasons for this.
The first is that there is now more than one possible non-denoting correlate, and Leibniz's formula, applied through the System S copula does not distinguish between them.
The second is the presence of values for failing descriptions.

The values for failing descriptions should not be in the range of quantification, so we do need to have special quantifiers in System S, it will then also be necessary to qualify the quantification to get a version of the second order definition which takes account of possibly distinct non-designating names.

\ignore{
=SML
set_goal([], ⌜¬ ∀x y:SC⦁ x = y ⇔ (∀P:'a → BOOL⦁ x is⋎s P ⇔ y is⋎s P)⌝);
a (strip_tac);
a (∃_tac ⌜⊥⌝ THEN strip_tac);
a (∃_tac ⌜InR (εx⦁T)⌝ THEN strip_tac);
a (lemma_tac ⌜¬ ⊥ = InR (ε x⦁ T)⌝ THEN asm_rewrite_tac [⊥_def, is⋎s_def, IsDen_def, IsCorr_def, Corr_def, ⊥_corr_def]);
val neg_snd_order_eq_thm = save_pop_thm "neg_snd_order_eq_thm";
=TEX
}%ignore

This equivalence fails because we now allow (in fact, require) more than one non-designating value in the domain of an interpretation.

However, if the copula is dropped we still get a working definition of a `weak' equality.

=GFT
⦏snd_order_eq_thm2⦎ =
	⊢ ∀ x y⦁ x = y ⇔ (∀ P⦁ P x ⇔ P y)
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y⦁ x = y ⇔ (∀P⦁ P x ⇔ P y)⌝);
a (REPEAT strip_tac THEN_TRY all_var_elim_asm_tac);
a (SPEC_NTH_ASM_T 1 ⌜λx⦁ x = y⌝ (strip_asm_tac o (rewrite_rule[])));
val snd_order_eq_thm2 = save_pop_thm "snd_order_eq_thm2";
=TEX
}%ignore


\section{Conclusions}
