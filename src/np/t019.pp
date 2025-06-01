=IGN
$Id: t019.doc,v 1.11 2009/10/15 19:46:58 rbj Exp $
=TEX
\documentclass[a4paper,11pt]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\usepackage{A4}
\def\N{\mathbb{N}}
\def\D{\mathbb{D}}
\def\B{\mathbb{B}}
\def\R{\mathbb{R}}
\def\Z{\mathbb{Z}}
\def\Q{\mathbb{Q}}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}

\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{NFU and NF in ProofPower-HOL}
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
Three formalisations in {\Product-HOL} are undertaken of NFU and NF.
One is based on Hailperin's axioms.
Another tries to follow Quine's original formulation by expressing stratified comprehension as a single higher-order axiom (axiom schemes are not supported by {\Product}.
The last is a finite axiomatisation based on one originating with Holmes.
\end{abstract}
\vfill
\begin{centering}

{\footnotesize

Created 2006/09/25

Last Change $ $Date: 2009/10/15 19:46:58 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t019.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t019.pdf}

$ $Id: t019.doc,v 1.11 2009/10/15 19:46:58 rbj Exp $ $

\copyright\ Roger Bishop Jones; licenced under Gnu LGPL

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
Everything.

\end{itemize}

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\newpage
\section{INTRODUCTION}

The material here concerns non-well-founded formal foundations for mathematics, particularly those with a universal set, and more specifically Quine's NF and its relative NFU.

Though my primary sources of information about NF and NFU are Forster \cite{forster92} and Holmes \cite{holmes98} the formalisations here follow neither closely.
In a previous exploration I transcribed into {\Product-HOL} both a finite axiom system due to Hailperin more or less as presented in Forster \cite{forster92}, and a finite axiomatisation due to Holmes more or less as presented in \cite{holmes98}.
These first transcriptions are sufficiently unsatisfactory in various ways that a completely fresh start seems a good idea.

These new approaches have the following aims:
\begin{itemize}

\item To attempt an axiomatisation closer to Quine's original in having an explicit axiom of stratified comprehension, rendered as a higher order axiom (axiom schemes are not supported by {\Product}).

\item To produce a finite axiomatisation, not involving stratified comprehension, which is more compact and uniform in presentation than my previous rendering of Holmes' system.
This is to have some similarities in character to the Hailperin axioms, but substantially based on Holmes and retaining most of the latter's accessibility.

\end{itemize}

In both cases two theories will be presented, the first being NFU and the second NF, defined as a child of NFU by adding a further axiom.
The names of the four theories will be {\it nfu\_s}, {\it nf\_s}, {\it nfu\_f}, {\it nf\_f}, in which the `s' suggests a schema of comprehension and the `f' that the axiomatisation is finite. 

Before addressing these we provide a rendering of Hailperin's axioms.

\section{NF FOLLOWING HAILPERIN}

This is based on Forster's presentation of Hailperin's axiom in \cite{forster92}, as I have not yet been able to look at the original.
I have not understood this, in two different ways.
First I do not yet understand how this axiom system works, how for example one might derive from these axioms those of Holmes \cite{holmes98} or demonstrate closure under stratified comprehension.
Worse however, I am not at all confident that I have a good rendition of Hailperin's axioms.
In particular it is not clear to me how I should be treating the ordered pair and ordered triple constructors.

I understand from Forster firstly that the ordered pair constructor must be construed in the manner of Wiener-Kuratowski, but that the triples are not an iteration of the pair constructor, but are constructed so that all three constituents are at the same depth.

What is not clear is which of these should be taken as primitive and whether the axioms encompass the characterisation of the pairs and triples.

What I have done is treat unordered pairs as primitive and defined the ordered pairs and triples in terms of them, and then I have added an extra axiom for the pairs.

I have as yet done almost nothing with these axioms, they are here for reference.

\subsection{Technical Prelude}

First of all, we must give the the ML commands to  introduce the new theory ``nf\_h'' as a child of the theory ``rbjmisc''.

=SML
(* open_theory "rbjmisc"; *)
open_theory "fixp";
force_new_theory "nf_h";
set_merge_pcs["hol1", "'savedthm_cs_∃_proof"];
=TEX

\ignore{
=SML
set_flag ("pp_use_alias", true);
=IGN
open_theory "nf_h";
set_merge_pcs["hol1", "'savedthm_cs_∃_proof"];
=TEX
}%ignore

In the context in which the development is taking place there is already a set theory, and we will make occasional use of it.
The normal set theoretic symbols are interpreted in this prior set theory, and the new set theory (NF) which we are introducing will therefore use symbols systematically subscripted with a small roman `n'.

Here is the new type for NF:

=SML
new_type ("NF", 0);
=TEX

This axioms use membership, the unit set and ordered pair constructors.
I will take the ordinary pair constructor as primitive and define unit set and ordered pair in terms of them before introducing the axiom.

=SML
declare_infix (310, "∈⋎n");
declare_infix (310, "∈↘↕");
new_const("∈⋎n", ⓣNF → NF → BOOL⌝);
declare_alias("∈↘↕", ⌜$∈⋎n⌝);
new_const("pair⋎n", ⓣNF × NF → NF⌝);
declare_prefix (320, "ι");
=TEX

ⓈHOLCONST
│ $⦏ι⦎ : NF → NF
├──────
│ ∀u⦁ ι u = pair⋎n (u, u)
■

ⓈHOLCONST
│ ⦏wkp⦎ : NF × NF → NF
├──────
│ ∀u v⦁ wkp(u, v) = pair⋎n(ι u, pair⋎n(u, v))
■

ⓈHOLCONST
│ ⦏Kt⦎ : NF × NF × NF → NF
├──────
│ ∀u v w⦁ Kt(u, v, w) = wkp(ι ι u, wkp(v, w)) 
■

\subsection{The Hailperin Axioms}

=SML
val Ext⋎n = new_axiom(["Ext⋎n"],

	⌜∀u v⦁ (∀x⦁ x ∈↘↕ u ⇔ x ∈↘↕ v) ⇒ u = v⌝);

val pair⋎n = new_axiom(["pair⋎n"],	

	⌜∀u v⦁ (∀x⦁ x ∈↘↕ pair⋎n(u,v) ⇔ x = u ∨ x = v)⌝);

val P1 = new_axiom(["P1"],

	⌜∀u v⦁ ∃ y⦁ ∀ x⦁ x ∈↘↕ y ⇔ ¬ x ∈↘↕ u ∨ ¬ x ∈↘↕ v⌝);

val P2 = new_axiom(["P2"],

	⌜∀u⦁∃v⦁∀x y⦁ wkp(ι x, ι y) ∈↘↕ v ⇔ wkp(x, y) ∈↘↕ u⌝);

val P3 = new_axiom(["P3"],

	⌜∀u⦁∃v⦁∀x y z⦁ Kt(x, y, z) ∈↘↕ v ⇔ wkp(x, y) ∈↘↕ u⌝);

val P4 = new_axiom(["P4"],

	⌜∀u⦁∃v⦁∀x y z⦁ Kt(x, z, y) ∈↘↕ v ⇔ wkp(x, y) ∈↘↕ u⌝);

val P5 = new_axiom(["P5"],

	⌜∀u⦁∃v⦁∀x y⦁ wkp(x, y) ∈↘↕ v ⇔ x ∈↘↕ u⌝);

val P6 = new_axiom(["P6"],

	⌜∀u⦁∃v⦁∀x⦁ x ∈↘↕ v ⇔ ∀z⦁ wkp(z, ι x) ∈↘↕ u⌝);

val P7 = new_axiom(["P7"],

	⌜∀u⦁∃v⦁∀x y⦁ wkp(y, x) ∈↘↕ u ⇔ wkp(x, y) ∈↘↕ v⌝);

val P8 = new_axiom(["P8"],

	⌜∃v⦁∀x⦁ x ∈↘↕ v ⇔ ∃y⦁ x = ι y⌝);

val P9 = new_axiom(["P9"],

	⌜∃v⦁∀x y⦁ wkp(ι x, y) ∈↘↕ v ⇔ x ∈↘↕ y⌝);
=TEX

The following axiom says that for every two sets $u$ and $v$ there exists a set $y$ of those elements $x$ which appear in neither $u$ nor $v$.
This is of course the complement of the union of the two sets, and the axiom allows us to define complement and union and various other operations over sets.

\subsection{Definitions}

Many of the following definitions depend upon a consistency proof, the details of which are not presented.

Axiom P1 allows the definition of complementation and intersection, these two operators are the set theoretic counterpart to negation and conjunction which provide a universal set of operators for the propositional calculus.
Axiom P1 therefore leads by itself to the definition of any set operations which correspond to propositional truth functions.

\subsubsection{Complement}

=SML
declare_postfix (320, "⋏c");
=TEX

\ignore{
=SML
set_goal([], ⌜∃ $⋏c:NF → NF⦁ ∀u x⦁ x ∈↘↕ u ⋏c ⇔ ¬ x ∈↘↕ u⌝);
a (∃_tac ⌜λx⦁ εy⦁ ∀z⦁ z ∈↘↕ y ⇔ ¬ z ∈↘↕ x⌝ THEN rewrite_tac[]
	THEN REPEAT_N 2 strip_tac);
a (ε_tac ⌜ε y⦁ ∀ z⦁ z ∈↘↕ y = (¬ z ∈↘↕ u)⌝);
(* *** Goal "1" *** *)
a (strip_asm_tac (list_∀_elim [⌜u⌝, ⌜u⌝] P1));
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
save_cs_∃_thm(pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ $⦏⋏c⦎ : NF → NF
├──────
│ ∀u x⦁ x ∈↘↕ u ⋏c ⇔ ¬ x ∈↘↕ u
■

\subsubsection{Intersection}

=SML
declare_infix(310, "∩⋎n");
=TEX

\ignore{
=SML
val ⋏c⋎n_def = get_spec ⌜$⋏c⌝;

set_goal([], ⌜∃$∩⋎n:NF → NF → NF⦁ ∀u v x⦁ x ∈↘↕ u ∩⋎n v ⇔ x ∈↘↕ u ∧ x ∈↘↕ v⌝);
a (∃_tac ⌜λu v⦁ εw⦁ ∀x⦁ x ∈↘↕ w ⇔ x ∈↘↕ u ∧ x ∈↘↕ v⌝
	THEN rewrite_tac[]
	THEN REPEAT_N 3 strip_tac);
a (ε_tac ⌜εw⦁ ∀x⦁ x ∈↘↕ w ⇔ x ∈↘↕ u ∧ x ∈↘↕ v⌝);
(* *** Goal "1" *** *)
a (strip_asm_tac (list_∀_elim [⌜u⌝, ⌜v⌝] P1));
a (∃_tac ⌜y ⋏c⌝ THEN asm_rewrite_tac[⋏c⋎n_def]
	THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
save_cs_∃_thm(pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ $⦏∩⋎n⦎ : NF → NF → NF
├──────
│ ∀u v x⦁ x ∈↘↕ (u ∩⋎n v) ⇔ x ∈↘↕ u ∧ x ∈↘↕ v
■

\ignore{
=SML
val ∩⋎n_def = get_spec ⌜$∩⋎n⌝; 
=TEX
}%ignore


\subsubsection{Union}

=SML
declare_infix(305, "∪⋎n");
=TEX

ⓈHOLCONST
│ $⦏∪⋎n⦎ : NF → NF → NF
├──────
│ ∀u v⦁ u ∪⋎n v = ((u ⋏c) ∩⋎n (v ⋏c)) ⋏c
■

\ignore{
 ⓈHOLCONST
│ $⦏⋏c⦎ : NF → NF
├──────
│ 
 ■
} %ignore

\section{NFU USING STRATIFIED COMPREHENSION}

\subsection{Introducing the Theory}

The notion of stratified comprehension is defined in a previous document \cite{rbjt004} and applied here in this axiomatisation.
The theory containing this prior material is called `membership', and `nfu\_s' is therefore introduced as a child of that theory.

=SML
open_theory "membership";
force_new_theory "nfu_s";
set_merge_pcs["hol1", "'savedthm_cs_∃_proof"];
=IGN
open_theory "nfu_s";
set_merge_pcs["hol1", "'savedthm_cs_∃_proof"];
=TEX

First we introduce a new type for the domain of the set theory.
The elements of this type are the sets of NF(U).

=SML
new_type("nfs", 0);
=TEX

We already have a polymorphic equality which will work over this type, but we will need a constant for the membership relation over this type.
The usual membership symbol is already in use for the typed membership in {\Product-HOL} so we use that symbol subscripted with ``s'' for membership in NF and introduce an alias to allow the subscript to be omitted where no ambiguity results.

=SML
declare_infix (310, "∈⋎s");
new_const("∈⋎s", ⓣnfs → nfs → BOOL⌝);
declare_alias("∈", ⌜$∈⋎s⌝);
=TEX

\subsection{Weak Extensionality}

=SML
val WkExt_ax = new_axiom (["WkExt"],
	⌜∀x y:nfs⦁ (∃z⦁ z ∈ x ∨ z ∈ y) ⇒ (x = y ⇔ (∀z⦁ z ∈ x ⇔ z ∈ y))⌝);
=TEX

\subsection{Notation for Existence and Comprehension}

There is special syntactic support for the typed set theory in {\Product-HOL}, notably for the usual way of writing a set comprehension.
The following two definitions will allow us to make use of this notation.

First a notation for asserting the existence of a set in NF(U).

ⓈHOLCONST
│  ⦏∃⋎s⦎: nfs SET → BOOL
├────────
│  ∀s⦁ ∃⋎s s ⇔ ∃a:nfs⦁ ∀x:nfs⦁ x ∈ s ⇔ x ∈⋎s a 
■

Thus
=INLINEFT
⌜∃⋎s⌝
=TEX
when applied to a term of type ⓣnfs SET⌝ asserts the existence of a set in NF(U) (of type ⓣnfs⌝) with the same extension. 

The following constant enables us to pull out of the air a set with some specified extension, and therefore is analogous to the usual set abstraction notation.

\ignore{
=SML
set_goal([], ⌜∃ Λ: nfs SET → nfs⦁ ∀s: nfs SET⦁ ∃⋎s s ⇒ ∀e:nfs⦁ e ∈ Λ s ⇔ e ∈ s⌝);
a (∃_tac ⌜λs:nfs SET⦁ εt: nfs⦁ ∃⋎s s ⇒ ∀e:nfs⦁ e ∈ t ⇔ e ∈ s⌝
	THEN strip_tac THEN rewrite_tac[get_spec ⌜$∃⋎s⌝]
	THEN REPEAT_N 2 strip_tac);
a (ε_tac ⌜ε t:nfs⦁ (∃ a:nfs⦁ ∀ x⦁ x ∈ s ⇔ x ∈ a) ⇒ (∀ e⦁ e ∈ t ⇔ e ∈ s)⌝);
(* *** Goal "1" *** *)
a (∃_tac ⌜a⌝ THEN REPEAT strip_tac);
a (DROP_NTH_ASM_T 2 discard_tac THEN asm_rewrite_tac[]);
a (SYM_ASMS_T rewrite_tac);
(* *** Goal "2" *** *)
a (SPEC_NTH_ASM_T 1 ⌜a⌝ ante_tac);
a (POP_ASM_T discard_tac THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│  ⦏Λ⦎: nfs SET → nfs
├────────
│  ∀s:nfs SET⦁ ∃⋎s s ⇒ ∀e⦁ e ∈⋎s Λ s ⇔ e ∈ s 
■

Thus applying ⌜Λ⌝ to an object of type ⓣnfs SET⌝ will yield a value of type ⓣnfs⌝ which will have the same extension if such a set exists.
To make use of this we need to be able to prove that the required set exists.

\subsection{Stratified Comprehension}

Stratified comprehension is an axiom scheme in first order logic.
We do not have support for axiom schemes, but we do have a higher order logic.

If we were axiomatising separation in ZF, a higher order axiom of separation could be used quantifying over properties of sets.
This would be slightly stronger than the first order axiom of separation, since not all properties in the range of a higher-order quantifier are expressible as formulae of first order logic.
If this extra strength had to be avoided, then the property of properties which consists in their being expressible in first order logic can be defined in higher order logic, and the quantification could be restricted to these properties.

A similar technique can be used for stratified comprehension.
The property of being a property expressible by a stratified first order formula is definable in higher order logic, and an axiom could quantify over these properties.
This property has been defined in the theory `membership' in \cite{rbjt004}.

There is one further complication.
The usual schema involves universal quantification over any number of variables which may appear free in the comprehension.
To express this in a single higher order axiom requires one further subterfuge.

A variable valuation may be represented as a function from variable names to sets.
We quantify over such valuations.

=SML
val StratComp_ax = new_axiom(["StratComp"],
	⌜∀va; p:(nfs→(nfs→BOOL))→((CHAR)LIST→nfs)→(nfs)SET⦁
	Stratified p ⇒ ∃⋎s (p $∈⋎s va)⌝);
=TEX

I need to do some checks on this since the formulation was not straightforward and there is a good chance of errors.

One way of checking is to see that it gives the results one expects, but that doesn't ensure that it is not too strong.

The following conjecture is worth checking.
(and so far doesn't look at all plausible!)
=SML
new_conjecture(["Strat"], 
	⌜(∀va p⦁	Stratified p ⇒ ∃⋎s (p $∈⋎s va))
	⇔
	StratCompClosed "" (Universe, $∈⋎s)⌝);
=TEX

\ignore{
=IGN
set_goal([], get_conjecture "-" "Strat");
a (rewrite_tac (map get_spec [⌜Stratified⌝, ⌜StratCompClosed⌝, ⌜foc⌝, ⌜∃⋎s⌝]));
=TEX
}%ignore

\subsection{Deriving the Basic Principles}

We want to be able to prove all the principles in the finite axiomatisation which we use later in the document.
Since they aren't axioms here I shall call them the {\it Basic Principles}.

They will have the same names here as later, but with the suffix "\_thm" rather than "\_ax".
Details of the proofs are not shown, here is the list of the principles which have been demonstrated:


\ignore{
=GFT
set_goal([], ⌜∃⋎s (λm va⦁ $∈⋎s (λx:ℕ.ε) ∀y⦁ ¬ y ∈⋎nf x)⌝);


set_goal([], ⌜∃x⦁ ∀y⦁ ¬ y ∈⋎nf x⌝);
=TEX
}%

\subsection{Strong Extensionality}

We start a new theory for this so that it remains possibly to use nfu. 

=SML
open_theory "nfu_s";
force_new_theory "nf_s";
set_merge_pcs["hol1", "'savedthm_cs_∃_proof"];
=TEX

We could add something weak to upgrade the qualified extensionality of NFU, but instead plump for a full statement of extensionality.
We might express this as the implication from equal extensions to equality, but the equivalence with equality on the left is more useful, so we might as well have that. 

=SML
new_axiom(["Extensionality"], ⌜∀x y⦁ x = y ⇔ (∀z⦁ z ∈⋎s x ⇔ z ∈⋎s y)⌝);
=TEX

\section{FINITE AXIOMATISATION OF NFU}

This is mainly based on Holmes' axiom system \cite{holmes98}.

The following points give some indication of the motivation and character of the differences between the system present here and that of Holmes.

\begin{itemize}

\item It seems likely that at least the presentation and perhaps also in some degree the substance of Holmes' axioms is pedagogical.
We have no such purpose in mind here, and are aiming for a system which is practical for formal machine checked reasoning, but still intelligible.

\item As in my previous version, the pragmatics will result in the system being as extensional as possible and not distinguishing between the empty set and the urelements more often than is necessary.
This is expected to make automation of reasoning more effective.

\item A uniform style of axiomatisation by existential assertion will be adopted.
This means that the existence of sets is stipulated before the introduction of operations which yield the stipulated sets.

\item The axiom system will be presented, as far as is practical, as a whole prior to the development of the theory, rather than interleaved with the development as it is in \cite{holmes98} and in my previous version.

\item The question will be considered of how stratified comprehension can be automated, and the convenience of the axioms for this purpose will be taking into account.

\end{itemize}

\subsection{Axioms I}

First some preliminaries, setting up a new theory, a new type for the NF(U) sets and declaring the constant for the membership relation.

=SML
(* open_theory "hol";*)
open_theory "fixp";
force_new_theory "nfu_f";
force_new_pc "'nfu_f1";
declare_infix (290, "∈⋎nf");
new_type ("SET⋎nf", 0);
new_const ("∈⋎nf", ⓣSET⋎nf → SET⋎nf → BOOL⌝);
set_merge_pcs["hol1", "'savedthm_cs_∃_proof"];
=IGN
open_theory "nfu_f";
set_merge_pcs["hol1", "'savedthm_cs_∃_proof", "'nfu_f1"];
=TEX

A principle difference in presentation is that this presentation will be primarily {\it existential}, i.e. consisting of set existence assertions.
Holmes' more pedagogical presentation takes the more commmon approach of giving axioms for new set constructors in which the existence claim is implicit.

In the case of NFU there are special details which complicate the characterisation but which are properly irrelevant to the axiom system (it is desirable to assert that operations over sets always yield sets, even where the required extension is empty, but the bald existence claim need not do this).

We would begin with a weak axiom of extensionality for NFU to be strengthened later for NF.

=SML
val weak_ext_ax = new_axiom(["weak_ext"],
	⌜∀x y⦁ (∃z⦁ z ∈⋎nf x ∨ z ∈⋎nf y) ⇒ (x = y ⇔ ∀z⦁ z ∈⋎nf x ⇔ z ∈⋎nf y)⌝);
=TEX

Instead of the universe we begin with the empty set:

=SML
val empty_set_ax = new_axiom(["empty_set"],
	⌜∃x⦁ ∀y⦁ ¬ y ∈⋎nf x⌝);
=TEX

This nextx axiom is taken from Hailperin and states more concisely than Holmes' the sets form a boolean algebra.

=SML
val nand_ax = new_axiom(["nand"],
	⌜∀v w⦁ ∃x⦁ ∀y⦁ y ∈⋎nf x ⇔ ¬ y ∈⋎nf v ∨ ¬ y ∈⋎nf w⌝);

val union_ax = new_axiom(["union"],
	⌜∀v⦁ ∃x⦁ ∀y⦁ y ∈⋎nf x ⇔ ∃z⦁ z ∈⋎nf v ∧ y ∈⋎nf z⌝);

val unit_ax = new_axiom(["unit"],
	⌜∀v⦁ ∃x⦁ ∀y⦁ y ∈⋎nf x ⇔ y = v⌝);
=TEX

The axioms from here onward depend upon the ordered pair constructor.
I will therefore break here in statement of the axioms to undertake various definitions and some elementary proofs before completing the axioms.

\subsection{Definitions}

Now we introduce a collection of constants by definition (or at least, by conservative extension).
The minor complications which arise here from the possibility of urelements will be apparent.

The subsections here follow the early chapter headings in Holmes \cite{holmes98}.

\subsubsection{The Set Concept}

We are free to take any of the objects with no members as the empty set (all the others will then be urelements).
We do this by introding a constant to designate that object.

\ignore{
=SML
set_goal([], ⌜∃∅⦁ ∀x⦁ ¬ x ∈⋎nf ∅⌝);
a (accept_tac empty_set_ax);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏∅⦎ : SET⋎nf
├──────
│ ∀x⦁ ¬ x ∈⋎nf ∅
■

Once we have "chosen" the empty set we can define a predicate which distinguished the sets from the urelements.
Alternatively this predicate could have been taken as primitive, instead of our choice of empty set.

ⓈHOLCONST
│ ⦏Set⦎ : SET⋎nf → BOOL
├──────
│ ∀x⦁ Set x ⇔ x = ∅ ∨ ∃y⦁ y ∈⋎nf x
■

We might as well have a name for the other things:

ⓈHOLCONST
│ ⦏Ur⦎ : SET⋎nf → BOOL
├──────
│ ∀x⦁ Ur x ⇔ ¬ Set x
■

\subsubsection{Comprehension}

Notation for set comprehension will probably be useful.
We have syntax for sets, which in this context will yield values of type
=INLINEFT
ⓣSET⋎nf SET⌝
=TEX
, so we define two new constants, one to assert the existence of a set with a particular extension, and the other to convert an object of type 
=INLINEFT
ⓣSET⋎nf SET⌝
=TEX
 to one of type 
=INLINEFT
ⓣSET⋎nf⌝
=TEX
.

The constant
=INLINEFT
⌜∃⋎nf⌝
=TEX
 simply asserts the existence of a set with some particular extension.

ⓈHOLCONST
│ ⦏∃⋎nf⦎ : SET⋎nf SET → BOOL
├──────
│ ∀s⦁ ∃⋎nf s ⇔ ∃a⦁ Set a ∧ ∀x⦁ x ∈⋎nf a ⇔ x ∈ s
■

The constant 
=INLINEFT
⌜Υ⋎nf⌝$
=TEX
 simulates set comprehension in NFU.
If applied to an extension (as an object of type
=INLINEFT
ⓣ(NFU)SET⌝
=TEX
) for which a set exists it yields that set.

\ignore{
=SML
val ∃⋎nf_def = get_spec ⌜∃⋎nf⌝;

set_goal([], ⌜∃ Υ⋎nf⦁ ∀s⦁ ∃⋎nf s ⇒ Set (Υ⋎nf s) ∧ ∀x⦁ x ∈⋎nf (Υ⋎nf s) ⇔ x ∈ s⌝);
a (∃_tac ⌜λs⦁ εn⦁ Set n ∧ ∀x⦁ x ∈⋎nf n ⇔ x ∈ s⌝ THEN rewrite_tac[]
	THEN strip_tac THEN rewrite_tac [∃⋎nf_def]
	THEN strip_tac
	THEN strip_tac);
(* *** Goal "1" *** *)
a (ε_tac ⌜εn⦁ Set n ∧ ∀x⦁ x ∈⋎nf n ⇔ x ∈ s⌝);
a (∃_tac ⌜a⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (ε_tac ⌜εn⦁ Set n ∧ ∀x⦁ x ∈⋎nf n ⇔ x ∈ s⌝);
a (∃_tac ⌜a⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
} %ignore

ⓈHOLCONST
│ ⦏Υ⋎nf⦎ : SET⋎nf SET → SET⋎nf
├──────
│ ∀s⦁ ∃⋎nf s ⇒ Set (Υ⋎nf s) ∧ ∀x⦁ x ∈⋎nf (Υ⋎nf s) ⇔ x ∈ s
■

\ignore{
=SML
val ∃↘u↕_def = get_spec ⌜∃⋎nf⌝;
val Υ↘u↕_def = get_spec ⌜Υ⋎nf⌝;
=TEX
}%ignore

\ignore{
=SML
set_goal([], ⌜∃⋎nf {}⌝);
a (rewrite_tac[∃↘u↕_def]);
a (∃_tac ⌜∅⌝ THEN rewrite_tac [get_spec ⌜∅⌝, get_spec ⌜Set⌝]);
val ∃⋎nf_empty_thm = pop_thm ();
=IGN
set_goal([], ⌜Υ⋎nf {} = ∅⌝);
a (asm_tac ∃⋎nf_empty_thm THEN FC_T1 fc_⇔_canon (MAP_EVERY asm_tac) [Υ↘u↕_def]);
a (asm_tac Set↘u↕_∅↘u↕_thm);
a (ALL_FC_T1 fc_⇔_canon (MAP_EVERY asm_tac) [Υ↘u↕_def]);
a (ALL_FC_T1 fc_⇔_canon (MAP_EVERY asm_tac) [Ext↘u↕_set_thm]);
a (asm_rewrite_tac[∅↘u↕_ax]);
val Υ↘u↕_∅↘u↕_thm = save_pop_thm "Υ↘u↕_∅↘u↕_thm";
=TEX
}%ignore

Of course this is all mere notation, there are no assertions made here about which sets exist.

\subsubsection{Boolean operations on Sets}

=SML
declare_postfix (320, "⋏c");
=TEX
\ignore{
=SML
set_goal([], ⌜∃ $⋏c:SET⋎nf → SET⋎nf⦁ ∀x⦁ Set (x ⋏c) ∧ ∀y⦁ y ∈⋎nf (x ⋏c) ⇔ ¬ y ∈⋎nf x⌝);
a (∃_tac ⌜λx⦁ εy⦁ Set y ∧ ∀v⦁ v ∈⋎nf y ⇔ ¬ v ∈⋎nf x⌝ THEN strip_tac
	THEN rewrite_tac[]);
a (ε_tac ⌜ε y⦁ Set y ∧ ∀ v⦁ v ∈⋎nf y ⇔ ¬ v ∈⋎nf x⌝);
(* *** Goal "1" *** *)
a (asm_tac nand_ax);
a (list_spec_nth_asm_tac 1 [⌜x⌝, ⌜x⌝]);
a (∃_tac ⌜if (∃y:SET⋎nf⦁ y ∈⋎nf x') then x' else ∅⌝ THEN asm_rewrite_tac[get_spec ⌜Set⌝]);
a (CASES_T ⌜∃ y⦁ ¬ y ∈⋎nf x⌝ asm_tac THEN asm_rewrite_tac[get_spec ⌜∅⌝]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[] THEN strip_tac);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ $⦏⋏c⦎ : SET⋎nf → SET⋎nf
├──────
│ ∀x⦁ Set (x ⋏c) ∧ ∀y⦁ y ∈⋎nf (x ⋏c) ⇔ ¬ y ∈⋎nf x
■

The Universe is the complement of the empty set.

ⓈHOLCONST
│ ⦏V⦎ : SET⋎nf
├──────
│ V = ∅ ⋏c
■

=SML
declare_infix(305, "∩⋎nf");
=TEX

\ignore{
=SML
set_goal([],⌜∃ $∩⋎nf:SET⋎nf → SET⋎nf → SET⋎nf⦁ ∀a b⦁
	Set (a ∩⋎nf b) ∧ ∀x⦁ x ∈⋎nf (a ∩⋎nf b) ⇔ x ∈⋎nf a ∧ x ∈⋎nf b⌝);
a (∃_tac ⌜λa b⦁ εc⦁ Set c ∧ ∀x⦁ x ∈⋎nf c ⇔ x ∈⋎nf a ∧ x ∈⋎nf b⌝
	THEN rewrite_tac[]
	THEN REPEAT ∀_tac
	THEN ε_tac ⌜εc⦁ Set c ∧ ∀x⦁ x ∈⋎nf c ⇔ x ∈⋎nf a ∧ x ∈⋎nf b⌝
	THEN_TRY asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim [⌜a⌝, ⌜b⌝] nand_ax));
a (∃_tac ⌜x ⋏c⌝ THEN rewrite_tac[get_spec⌜$⋏c⌝]);
a (asm_prove_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ $⦏∩⋎nf⦎ : SET⋎nf → SET⋎nf → SET⋎nf
├──────
│ ∀a b⦁ Set (a ∩⋎nf b) ∧ ∀x⦁ x ∈⋎nf (a ∩⋎nf b) ⇔ x ∈⋎nf a ∧ x ∈⋎nf b
■

We are now able to defin union:

=SML
declare_infix(300, "∪⋎nf");
=TEX

ⓈHOLCONST
│ $⦏∪⋎nf⦎ : SET⋎nf →  SET⋎nf → SET⋎nf
├──────
│ ∀a b⦁ (a ∪⋎nf b) = (a ⋏c ∩⋎nf b ⋏c)⋏c
■

=SML
declare_infix(300, "\\⋎nf");
=TEX

ⓈHOLCONST
│ $⦏\⋎nf⦎ : SET⋎nf →  SET⋎nf → SET⋎nf
├──────
│ ∀a b⦁ (a \⋎nf b) = a ∩⋎nf (b ⋏c)
■

=SML
declare_infix(300, "Δ⋎nf");
=TEX

ⓈHOLCONST
│ $⦏Δ⋎nf⦎ : SET⋎nf →  SET⋎nf → SET⋎nf
├──────
│ ∀a b⦁ (a Δ⋎nf b) = (b \⋎nf a) ∪⋎nf (a \⋎nf b)
■

=SML
declare_infix(290, "⊆⋎nf");
declare_infix(290, "⊂⋎nf");
=TEX

ⓈHOLCONST
│ $⦏⊆⋎nf⦎ : SET⋎nf →  SET⋎nf → BOOL
├──────
│ ∀a b⦁ (a ⊆⋎nf b) ⇔ ∀x⦁ x ∈⋎nf a ⇒ x ∈⋎nf b
■

ⓈHOLCONST
│ $⦏⊂⋎nf⦎ : SET⋎nf →  SET⋎nf → BOOL
├──────
│ ∀a b⦁ (a ⊂⋎nf b) ⇔ (a ⊆⋎nf b) ∧ ¬ b ⊆⋎nf a
■

Up until now we have used only three axioms ({\it weak\_ext, empty\_set, nand}), now we invoke {\it union} the distributed union axiom.

I show here as a sample, the consistency proof which was necessary in introducing the specification of union.
Normally these proofs are not printed, though they are always present unless the specification can be proven conservative by the proof tool without assistance.
Often, as in this case, the proofs are more complex than might have been expected.

=SML
declare_prefix(310, "⋃⋎nf");

set_goal ([], ⌜∃ $⋃⋎nf:SET⋎nf → SET⋎nf⦁
	∀x⦁ Set (⋃⋎nf x) ∧ (∀y⦁ y ∈⋎nf (⋃⋎nf x) ⇔ ∃z⦁ z ∈⋎nf x ∧ y ∈⋎nf z)⌝);
a (prove_∃_tac THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ union_ax));
a (∃_tac ⌜if ∃s t⦁ t ∈⋎nf x' ∧ s ∈⋎nf t then x else ∅⌝
	THEN CASES_T ⌜∃s t⦁ t ∈⋎nf x' ∧ s ∈⋎nf t⌝
	(fn x => rewrite_tac [x] THEN strip_asm_tac x));
(* *** Goal "1" *** *)
a (asm_rewrite_tac[get_spec ⌜Set⌝]
	THEN REPEAT strip_tac
	THEN ∃_tac ⌜s⌝
	THEN ∃_tac ⌜t⌝
	THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜Set⌝, get_spec ⌜∅⌝]);
save_cs_∃_thm (pop_thm());
=TEX

ⓈHOLCONST
│ $⦏⋃⋎nf⦎ : SET⋎nf →  SET⋎nf
├──────
│ ∀x⦁ Set (⋃⋎nf x) ∧ (∀y⦁ y ∈⋎nf (⋃⋎nf x) ⇔ ∃z⦁ z ∈⋎nf x ∧ y ∈⋎nf z)
■

\subsection{Interim Proof Contexts}

It is now possible to automate elementary proofs, typically of algebraic laws in the theory so far.
To this end we demonstrate (proofs not presented) various theorems which will be useful and integrate these into a `proof context'.

\ignore{
=SML
set_goal([], ⌜∀x y⦁ Set x ∧ Set y ⇒ (x = y ⇔ (∀z⦁ z ∈⋎nf x ⇔ z ∈⋎nf y))⌝);
a (prove_tac [get_spec ⌜Set⌝]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜y'⌝
	THEN POP_ASM_T ante_tac
	THEN rewrite_tac [get_spec ⌜∅⌝]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 1 ⌜y'⌝
	THEN POP_ASM_T ante_tac
	THEN rewrite_tac [get_spec ⌜∅⌝]);
(* *** Goal "3" *** *)
a (LEMMA_T ⌜∃ z⦁ z ∈⋎nf x ∨ z ∈⋎nf y⌝ asm_tac
	THEN1 (∃_tac ⌜y'⌝ THEN REPEAT strip_tac));
a (ALL_FC_T1 fc_⇔_canon asm_rewrite_tac [weak_ext_ax]);
val nfu_f_set_ext_thm = save_pop_thm "set_ext_thm";

set_goal([], ⌜∀x y⦁ Set ∅ ∧ Set V ∧ Set (x ⋏c) ∧ Set (x ∩⋎nf y)
	∧ Set (x ∪⋎nf y) ∧ Set (x \⋎nf y) ∧ Set (x Δ⋎nf y) ∧ Set (⋃⋎nf x)⌝);
a (rewrite_tac (map get_spec [⌜∅⌝, ⌜$⋏c⌝, ⌜V⌝, ⌜$∩⋎nf⌝, ⌜$∪⋎nf⌝,
	⌜$\⋎nf⌝, ⌜$Δ⋎nf⌝, ⌜$⋃⋎nf⌝]));
a (rewrite_tac [get_spec ⌜Set⌝]);
val nfu_f_set_clauses = pop_thm();

set_goal([], ⌜∀x y z⦁
		¬ z ∈⋎nf ∅
	∧	z ∈⋎nf V
	∧	(z ∈⋎nf x ⋏c ⇔ ¬ z ∈⋎nf x)
	∧	(z ∈⋎nf (x ∩⋎nf y) ⇔ z ∈⋎nf x ∧ z ∈⋎nf y)
	∧	(z ∈⋎nf (x ∪⋎nf y) ⇔ z ∈⋎nf x ∨ z ∈⋎nf y)
	∧	(z ∈⋎nf (x \⋎nf y) ⇔ z ∈⋎nf x ∧ ¬ z ∈⋎nf y)
	∧	(z ∈⋎nf (x Δ⋎nf y) ⇔ z ∈⋎nf x ∧ ¬ z ∈⋎nf y ∨ ¬ z ∈⋎nf x ∧ z ∈⋎nf y)
⌝);
a (REPEAT ∀_tac);
a (rewrite_tac (map get_spec [⌜∅⌝, ⌜V⌝, ⌜$⋏c⌝, ⌜$∩⋎nf⌝, ⌜$∪⋎nf⌝, ⌜$\⋎nf⌝, ⌜$Δ⋎nf⌝, ⌜$⋃⋎nf⌝]));
a (prove_tac[]);
val nfu_f_op_ext_clauses1 = pop_thm ();

set_goal([], ⌜∀x y z⦁
		(z ∈⋎nf (⋃⋎nf x) ⇔ ∃ y⦁ y ∈⋎nf x ∧ z ∈⋎nf y)
⌝);
a (REPEAT ∀_tac);
a (rewrite_tac (map get_spec [⌜∅⌝, ⌜V⌝, ⌜$⋏c⌝, ⌜$∩⋎nf⌝, ⌜$∪⋎nf⌝, ⌜$\⋎nf⌝, ⌜$Δ⋎nf⌝, ⌜$⋃⋎nf⌝]));
val nfu_f_op_ext_clauses2 = pop_thm ();
=TEX
}%ignore

The proof and use of theorems about the algebra of sets in nfu is complicated by the presence of urelements in the domain of discourse.
This would naturally suggest that this kind of theorem would involve restricted quantification over just the sets.
This kind of theorem is harder to apply than one involving unrestricted quantification because of the need to prove that the values being manipulated are all sets.
To limit the inconvenience occasioned by these considerations the definitions of the various operations over sets have been written so that they do not care whether their objects are sets or not, but will always yield sets with an extension determined by the extension of the operands.
The result of one of these operations will always be a set, even if the operands are not.

The plan is then that the proof of an equation between expressions begins with the demonstration that the operands are sets, which will usually be trivial, and then proceeds by application of a version of extensionality which is good for all sets.
The subset relations are defined extensionality so they can be expanded without demonstrating that the arguments are sets.

First we prove the version of extensionality which applies to all sets.

=GFT
nfu_f_set_ext_thm =
   ⊢ ∀ x y⦁ Set x ∧ Set y ⇒ (x = y ⇔ (∀ z⦁ z ∈⋎nf x ⇔ z ∈⋎nf y))
=TEX

Then we provide a theorem to assist in proving that expressions do denote sets.

=GFT
nfu_f_set_clauses =
   ⊢ ∀ x y
     ⦁ Set ∅
         ∧ Set V
         ∧ Set (x ⋏c)
         ∧ Set (x ∩⋎nf y)
         ∧ Set (x ∪⋎nf y)
         ∧ Set (x \⋎nf y)
         ∧ Set (x Δ⋎nf y)
         ∧ Set (⋃⋎nf x)
=TEX

Now we need extensional characterisations of the set operators.
These are split into two sets, those which are uncontroversial enough to apply normally, and those which are not.
The latter group in this case consists of clauses which introduce existential quantifiers.

=GFT
nfu_f_op_ext_clauses1 =
   ⊢ ∀ x y z
     ⦁ ¬ z ∈⋎nf ∅
         ∧ z ∈⋎nf V
         ∧ (z ∈⋎nf x ⋏c ⇔ ¬ z ∈⋎nf x)
         ∧ (z ∈⋎nf x ∩⋎nf y ⇔ z ∈⋎nf x ∧ z ∈⋎nf y)
         ∧ (z ∈⋎nf x ∪⋎nf y ⇔ z ∈⋎nf x ∨ z ∈⋎nf y)
         ∧ (z ∈⋎nf x \⋎nf y ⇔ z ∈⋎nf x ∧ ¬ z ∈⋎nf y)
         ∧ (z ∈⋎nf x Δ⋎nf y ⇔ z ∈⋎nf x ∧ ¬ z ∈⋎nf y ∨ ¬ z ∈⋎nf x ∧ z ∈⋎nf y)

nfu_f_op_ext_clauses2 =
   ⊢ ∀ x y z
     ⦁ (z ∈⋎nf (⋃⋎nf x) ⇔ ∃ y⦁ y ∈⋎nf x ∧ z ∈⋎nf y)
=TEX

\ignore{
We now need a bit of programming to deal with the conditions on extensionality of equations.

=SML
fun ⦏nfu_f_eq_ext_conv⦎ tm =
 let	val (lhs, rhs) = dest_eq tm;
	val set = mk_const("Set", mk_ctype ("→", [mk_ctype ("SET⋎nf", []), mk_ctype ("BOOL",[])]));
	val gc = mk_∧ (mk_app(set, lhs), mk_app(set, rhs));
	val set_thm = tac_proof(([], gc), rewrite_tac[nfu_f_set_clauses]);
	val eq_thm = ⇒_elim (list_∀_elim [lhs, rhs] nfu_f_set_ext_thm) set_thm;
 in eq_thm
 end handle _ => fail_conv tm;
=IGN
val tm = ⌜∅ ⋏c = V⌝;
=TEX

=SML
fun nfu_f_prove_conv thms tm = ⇔_t_intro (tac_proof (([],tm),
	REPEAT ∀_tac
	THEN_TRY rewrite_tac thms
	THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY asm_rewrite_tac[]
	THEN_TRY basic_prove_tac thms
));

fun nfu_f_prove_tac thms = 
	REPEAT ∀_tac
	THEN_TRY rewrite_tac thms
	THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY asm_rewrite_tac[]
	THEN_TRY basic_prove_tac thms
;

force_new_pc "'nfu_f1";
add_rw_thms [nfu_f_set_clauses, nfu_f_op_ext_clauses1] "'nfu_f1";
set_sc_eqn_cxt ([(⌜x = y⌝, nfu_f_eq_ext_conv)]) "'nfu_f1";
add_sc_thms [nfu_f_set_clauses, nfu_f_op_ext_clauses1, nfu_f_op_ext_clauses2] "'nfu_f1";
add_st_thms [nfu_f_op_ext_clauses1, nfu_f_op_ext_clauses2] "'nfu_f1";

force_new_pc "'nfu_f2";
set_rw_eqn_cxt ([(⌜x = y⌝, nfu_f_eq_ext_conv)]) "'nfu_f2";
add_rw_thms [get_spec ⌜$⊆⋎nf⌝, nfu_f_op_ext_clauses2] "'nfu_f2";

set_pr_conv nfu_f_prove_conv "'nfu_f2";
set_pr_tac nfu_f_prove_tac "'nfu_f2";

set_merge_pcs ["hol1", "'savedthm_cs_∃_proof", "'nfu_f1", "'nfu_f2"];
=TEX
}%ignore

We are now able to define a `proof context' in which we can prove elementary algebraic equations such as those cited towards the end of Chapter 3 of Holmes \cite{holmes98}.

=IGN
set_merge_pcs ["hol1", "'savedthm_cs_∃_proof", "'nfu_f1", "'nfu_f2"];

val terms = [
⌜A ∩⋎nf B = B ∩⋎nf A⌝,
⌜A ∪⋎nf B = B ∪⋎nf A⌝,
⌜(A ∩⋎nf B) ∩⋎nf C = A ∩⋎nf (B ∩⋎nf C)⌝,
⌜(A ∪⋎nf B) ∪⋎nf C = A ∪⋎nf (B ∪⋎nf C)⌝,
⌜A ∩⋎nf (B ∪⋎nf C) = (A ∩⋎nf B) ∪⋎nf (A ∩⋎nf C)⌝,
⌜A ∪⋎nf (B ∩⋎nf C) = (A ∪⋎nf B) ∩⋎nf (A ∪⋎nf C)⌝,
⌜A ∩⋎nf ∅ = ∅⌝,
⌜A ∪⋎nf V = V⌝,
⌜(A ∪⋎nf B) ⋏c = (A ⋏c) ∩⋎nf (B ⋏c)⌝,
⌜(A ∩⋎nf B) ⋏c = (A ⋏c) ∪⋎nf (B ⋏c)⌝,
⌜(A ⋏c) ∩⋎nf A = ∅⌝,
⌜(A ⋏c) ∪⋎nf A = V⌝,
⌜V ⋏c = ∅⌝,
⌜∅ ⋏c = V⌝,
⌜⋃⋎nf V = V⌝,
⌜⋃⋎nf ∅ = ∅⌝,
⌜∅ ⊆⋎nf A⌝,
⌜A ⊆⋎nf V⌝
];

filter (fn t => not(concl t =$ ⌜T⌝))
	(map (fn t => prove_rule[] t handle _ => t_thm) terms);

filter (fn t => not(t =$ ⌜T⌝)) (map (fn t => (let val thm = prove_rule[] t
	in ⌜T⌝ end handle _ => t)) terms);

prove_rule [] ⌜⋃⋎nf V = V⌝;
prove_rule [] ⌜⋃⋎nf ∅ = ∅⌝;

set_goal([], ⌜⋃⋎nf V = V⌝);
a (prove_tac[]);
a (rewrite_tac[]);
a (conv_tac nfu_f_eq_ext_conv);

a (strip_tac);
a (rewrite_tac[nfu_f_op_ext_clauses1b]);

=TEX

=GFT
val it = [
      ⊢ A ∩⋎nf B = B ∩⋎nf A,
      ⊢ A ∪⋎nf B = B ∪⋎nf A,
      ⊢ (A ∩⋎nf B) ∩⋎nf C = A ∩⋎nf B ∩⋎nf C,
      ⊢ (A ∪⋎nf B) ∪⋎nf C = A ∪⋎nf B ∪⋎nf C,
      ⊢ A ∩⋎nf (B ∪⋎nf C) = A ∩⋎nf B ∪⋎nf A ∩⋎nf C,
      ⊢ A ∪⋎nf B ∩⋎nf C = (A ∪⋎nf B) ∩⋎nf (A ∪⋎nf C)
      ⊢ A ∩⋎nf ∅ = ∅,
      ⊢ A ∪⋎nf V = V,
      ⊢ (A ∪⋎nf B) ⋏c = A ⋏c ∩⋎nf B ⋏c,
      ⊢ (A ∩⋎nf B) ⋏c = A ⋏c ∪⋎nf B ⋏c,
      ⊢ A ⋏c ∩⋎nf A = ∅,
      ⊢ A ⋏c ∪⋎nf A = V,
      ⊢ V ⋏c = ∅,
      ⊢ ∅ ⋏c = V,
      ⊢ ⋃⋎nf ∅ = ∅,
      ⊢ ∅ ⊆⋎nf A,
      ⊢ A ⊆⋎nf V]
: THM list
=TEX

The rules shown by Holmes with a variable on the right rather than an expression are not provable since they are false if that variable denotes a urelement.
They are provable only as conditional on the variable denoting a set.

These results are provable on demand as required and are not therefore stored in our theory, however some of them can be useful in automatic proof so we prove and store those separately and add them to our proof context.

\ignore{
=SML
set_goal([], ⌜
	∀A⦁ V ⋏c = ∅
	∧ ∅ ⋏c = V
	∧ A ∩⋎nf ∅ = ∅
	∧ ∅ ∩⋎nf A = ∅
	∧ (A ⋏c) ∩⋎nf A = ∅
	∧ A ∩⋎nf (A ⋏c) = ∅
	∧ A ∪⋎nf V = V
	∧ V ∪⋎nf A = V
	∧ (A ⋏c) ∪⋎nf A = V
	∧ A ∪⋎nf (A ⋏c) = V
	∧ A \⋎nf A = ∅
	∧ A Δ⋎nf A = ∅
	∧ A Δ⋎nf (A ⋏c) = V
	∧ (A ⋏c) Δ⋎nf A = V
	∧ ⋃⋎nf V = V
	∧ ⋃⋎nf ∅ = ∅
⌝);
a (prove_tac[]);
a (∃_tac ⌜V⌝ THEN rewrite_tac[]);
val nfu_f_∅V_clauses = pop_thm();

add_rw_thms [nfu_f_∅V_clauses] "'nfu_f1";
add_sc_thms [nfu_f_∅V_clauses] "'nfu_f1";
add_st_thms [nfu_f_∅V_clauses] "'nfu_f1";
set_merge_pcs ["hol1", "'savedthm_cs_∃_proof", "'nfu_f1", "'nfu_f2"];
=TEX
}%ignore

=GFT
nfu_f_∅V_clauses =
   ⊢ ∀A⦁ V ⋏c = ∅
	∧ ∅ ⋏c = V
	∧ A ∩⋎nf ∅ = ∅
	∧ ∅ ∩⋎nf A = ∅
	∧ (A ⋏c) ∩⋎nf A = ∅
	∧ A ∩⋎nf (A ⋏c) = ∅
	∧ A ∪⋎nf V = V
	∧ V ∪⋎nf A = V
	∧ (A ⋏c) ∪⋎nf A = V
	∧ A ∪⋎nf (A ⋏c) = V
	∧ A \⋎nf A = ∅
	∧ A Δ⋎nf A = ∅
	∧ A Δ⋎nf (A ⋏c) = V
	∧ (A ⋏c) Δ⋎nf A = V
=TEX

\subsection{Building Finite Structures}

=SML
declare_prefix (320, "ι");
=TEX

\ignore{
=SML
set_goal([],⌜∃ $ι⦁ ∀x⦁ Set (ι x) ∧ ∀y⦁ y ∈⋎nf (ι x) ⇔ y = x⌝);
a (prove_∃_tac THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ unit_ax));
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac [get_spec ⌜Set⌝]);
a (REPEAT strip_tac THEN ∃_tac ⌜x'⌝ THEN strip_tac);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ $⦏ι⦎ : SET⋎nf → SET⋎nf
├──────
│ ∀x⦁ Set (ι x) ∧ ∀y⦁ y ∈⋎nf (ι x) ⇔ y = x
■

\ignore{
=SML
set_goal([], ⌜∀x⦁ Set (ι x)⌝);
a (rewrite_tac[get_spec ⌜$ι⌝]);
val Set_ι_thm = pop_thm();

set_goal([], ⌜∀x y⦁ x ∈⋎nf (ι y) ⇔ x = y⌝);
a (rewrite_tac[get_spec ⌜$ι⌝]);
val ∈_ι_thm = pop_thm();

set_goal([], ⌜∀x y⦁ ι x = ι y ⇔ x = y⌝);
a (REPEAT ∀_tac);
a (lemma_tac ⌜Set (ι x) ∧ Set (ι y)⌝
	THEN1 rewrite_tac [get_spec ⌜$ι⌝]
	THEN ALL_FC_T1 fc_⇔_canon (rewrite_tac) [nfu_f_set_ext_thm]); 
a (REPEAT_N 3 strip_tac THEN_TRY asm_rewrite_tac[]);
a (SPEC_NTH_ASM_T 1 ⌜x⌝ ante_tac);
a (rewrite_tac [∈_ι_thm, get_spec ⌜$ι⌝]);
val ι_eq_thm = pop_thm ();

add_rw_thms [Set_ι_thm, ∈_ι_thm, ι_eq_thm] "'nfu_f2";
add_sc_thms [Set_ι_thm, ∈_ι_thm, ι_eq_thm] "'nfu_f2";
add_st_thms [∈_ι_thm, ι_eq_thm] "'nfu_f2";
set_merge_pcs ["hol1", "'savedthm_cs_∃_proof", "'nfu_f1", "'nfu_f2"];
=TEX
}%ignore

=GFT
	⊢ ∀ x⦁ Set (ι x)
	⊢ ∀ x y⦁ x ∈⋎nf ι y ⇔ x = y
	⊢ ∀ x y⦁ ι x = ι y ⇔ x = y
=TEX


\subsubsection{pairs}

The ordered pair constructor appears in the statement of several axioms, and unless we bundle them all together we will have to give a name to it.

We are now able to introduce by definition an ordered pair constructor.
The axioms ultimately will be incompatible with the ordered pairs being those of the Wiener-Kuratowski construction.
However, this axiomatic constraint which rules them out does not appear until later, and at this point it is possible to introduce ordered pairs using a loose definition which could be interpreted as WK pairs, and hence can be shown consistent using them.

We therefore proceed by first defining unordered and then Wiener-Kuratowski pairs, and then introduce by conservative extension a kind of ordered pair which might be but need not be (and ultimately will be forced not to be) Wiener-Kuratowski.

A pair is the union of two singletons.

ⓈHOLCONST
│ ⦏pair⦎ : SET⋎nf × SET⋎nf → SET⋎nf
├──────
│ ∀x y⦁ pair (x, y) = (ι x) ∪⋎nf (ι y)
■

\ignore{
=SML
val pair_def = get_spec ⌜pair⌝;

set_goal([],⌜∀a b⦁ Set (pair(a, b)) ∧ (∀x⦁ x ∈⋎nf pair(a, b) ⇔ x = a ∨ x = b)⌝);
a (rewrite_tac [pair_def] THEN REPEAT strip_tac);
val pair_thm = pop_thm ();

set_goal([], ⌜∀a b c⦁ ι a = pair(b, c) ⇔ b = a ∧ c = a⌝);
a (REPEAT_N 3 strip_tac);
a (LEMMA_T ⌜Set(ι a) ∧ Set(pair(b, c))⌝ strip_asm_tac
	THEN1 rewrite_tac [get_spec ⌜pair⌝]);
a (ALL_FC_T1 fc_⇔_canon (rewrite_tac)
	[nfu_f_set_ext_thm]);
a (rewrite_tac [∈_ι_thm, pair_thm]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
val ι_eq_pair_thm = pop_thm ();

set_goal([], ⌜∀a b c⦁ pair(b, c) = ι a ⇔ b = a ∧ c = a⌝);
a (REPEAT_N 3 strip_tac);
a (LEMMA_T ⌜pair(b, c) = ι a ⇔ ι a = pair(b, c)⌝ rewrite_thm_tac
	THEN1 (REPEAT strip_tac THEN asm_rewrite_tac[]));
a (rewrite_tac [ι_eq_pair_thm]);
val pair_eq_ι_thm = pop_thm ();

set_goal([], ⌜∀a b c d⦁ pair(a, b) = pair(c, d) ⇔ a = c ∧ b = d ∨ a = d ∧ b = c⌝);
a (REPEAT ∀_tac);
a (lemma_tac ⌜Set(pair(a,b)) ∧ Set(pair(c,d))⌝ THEN1 rewrite_tac[pair_thm]);
a (ALL_FC_T1 fc_⇔_canon rewrite_tac [list_∀_elim [⌜pair(a,b)⌝, ⌜pair(c,d)⌝] nfu_f_set_ext_thm]);
a (rewrite_tac [pair_thm] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 2 ⌜a⌝);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜c⌝);
a (DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[]);
a (asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 3 ante_tac THEN asm_rewrite_tac[]);
a (asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (lemma_tac ⌜¬d=b⌝ THEN1 (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]));
a (spec_nth_asm_tac 3 ⌜d⌝ THEN asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (spec_nth_asm_tac 2 ⌜b⌝ THEN asm_rewrite_tac[]);
val pair_eq_pair_thm = pop_thm ();
=TEX
}%ignore

=GFT
pair_thm =
   ⊢ ∀ a b⦁ Set (pair (a, b)) ∧ (∀ x⦁ x ∈⋎nf pair (a, b) ⇔ x = a ∨ x = b)

ι_eq_pair_thm =
   ⊢ ∀ a b c⦁ ι a = pair (b, c) ⇔ b = a ∧ c = a

pair_eq_ι_thm =
   ⊢ ∀ a b c⦁ pair (b, c) = ι a ⇔ b = a ∧ c = a

pair_eq_pair_thm =
   ⊢ ∀ a b c d⦁ pair (a, b) = pair (c, d) ⇔ a = c ∧ b = d ∨ a = d ∧ b = c

=TEX


ⓈHOLCONST
│ $⦏wkp⦎ : SET⋎nf × SET⋎nf → SET⋎nf
├──────
│ ∀x y⦁ wkp (x, y) = pair (ι x, pair (x, y))
■

\ignore{
=SML
val wkp_def = get_spec ⌜wkp⌝;

set_goal([],⌜∀a b⦁ Set (wkp(a,b)) ∧ ∀x⦁ x ∈⋎nf wkp(a,b) ⇔ x=ι a ∨ x=pair(a, b)⌝);
a (rewrite_tac [wkp_def, pair_thm]);
val wkp_thm = pop_thm ();

set_goal([], ⌜∀a b c d⦁ wkp(a, b) = wkp(c, d) ⇔ a = c ∧ b = d⌝);
a (REPEAT ∀_tac THEN strip_tac THEN strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜Set(wkp(a, b)) ∧ Set(wkp(c, d))⌝ THEN1 rewrite_tac [wkp_thm]);
a (ALL_FC_T1 fc_⇔_canon (rewrite_tac)
	[list_∀_elim [⌜wkp(a, b)⌝, ⌜wkp(c, d)⌝] nfu_f_set_ext_thm]
	THEN asm_rewrite_tac[wkp_thm] THEN strip_tac);
a (SPEC_NTH_ASM_T 1 ⌜ι a⌝ (asm_tac o (rewrite_rule[ι_eq_thm, ι_eq_pair_thm])));
a (lemma_tac ⌜a = c⌝ THEN1 (POP_ASM_T strip_asm_tac THEN asm_rewrite_tac[]));
a (asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 3 ante_tac);
a (asm_rewrite_tac[] THEN strip_tac);
a (SPEC_NTH_ASM_T 1 ⌜pair (d, b)⌝ (ante_tac o (rewrite_rule[ι_eq_thm, ι_eq_pair_thm,
		pair_eq_ι_thm, pair_eq_pair_thm])));
a (cases_tac ⌜d = c⌝ THEN asm_rewrite_tac[]);
a (cases_tac ⌜b = c⌝ THEN asm_rewrite_tac[]);
a (SPEC_NTH_ASM_T 3 ⌜pair (c, b)⌝ (ante_tac o (rewrite_rule[ι_eq_thm, ι_eq_pair_thm,
		pair_eq_ι_thm, pair_eq_pair_thm]))
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (strip_tac THEN asm_rewrite_tac[]);
val wkp_eq_wkp_thm = pop_thm ();
=TEX
} %ignore

The following theorems are proven and used in the introduction of $op$.

=GFT
   ⊢ ∀ a b⦁ Set (wkp (a, b))
         ∧ (∀ x⦁ x ∈⋎nf wkp (a, b) ⇔ x = ι a ∨ x = pair (a, b))

   ⊢ ∀ a b c d⦁ wkp (a, b) = wkp (c, d) ⇔ a = c ∧ b = d
=TEX

Having established that a pair constructor exists using a specific encoding, we can now introduce a new name for a pair constructor which is not tied to this particular coding.
The introduction of this constant involves a consistency proof in which the {\it wkp} is used (script not shown).

\ignore{
=SML
set_goal([], ⌜∃ op: SET⋎nf × SET⋎nf → SET⋎nf⦁ ∀a b c d⦁
	op (a, b) = op(c, d) ⇔ a = c ∧ b = d⌝);
a (∃_tac ⌜wkp⌝ THEN accept_tac wkp_eq_wkp_thm);
save_cs_∃_thm(pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏op⦎ : SET⋎nf × SET⋎nf → SET⋎nf
├──────
│ ∀a b c d⦁ op (a, b) = op (c, d)
│	⇔ a = c ∧ b = d
■

\ignore{
=SML
val op_def = get_spec ⌜op⌝;

set_goal([], ⌜∃ fst: SET⋎nf → SET⋎nf⦁ ∀a b⦁ fst (op (a, b)) = a⌝);
a (∃_tac ⌜λp:SET⋎nf⦁ εa:SET⋎nf⦁ ∃b⦁ p = op(a,b)⌝ THEN rewrite_tac[]);
a (ε_tac ⌜ε a'⦁ ∃ b'⦁ op (a, b) = op (a', b')⌝);
(* *** Goal "1" *** *)
a (∃_tac ⌜a⌝ THEN ∃_tac ⌜b⌝ THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a (REPEAT strip_tac THEN rewrite_tac[op_def ]);
a (ε_tac ⌜ε a''⦁ ∃ b'⦁ a' = a'' ∧ b'' = b'⌝);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜a'⌝ THEN ∃_tac ⌜b''⌝ THEN rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (SYM_ASMS_T rewrite_tac);
save_cs_∃_thm(pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏fst⦎ : SET⋎nf → SET⋎nf
├──────
│ ∀a b⦁ fst (op (a, b)) = a
■

\ignore{
=SML
set_goal([], ⌜∃ snd: SET⋎nf → SET⋎nf⦁ ∀a b⦁ snd (op (a, b)) = b⌝);
a (∃_tac ⌜λp:SET⋎nf⦁ εb:SET⋎nf⦁ ∃a⦁ p = op(a,b)⌝ THEN rewrite_tac[]);
a (ε_tac ⌜ε b'⦁ ∃ a'⦁ op (a, b) = op (a', b')⌝);
(* *** Goal "1" *** *)
a (∃_tac ⌜b⌝ THEN ∃_tac ⌜a⌝ THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a (REPEAT strip_tac THEN rewrite_tac[op_def ]);
a (ε_tac ⌜ε b''⦁ ∃ a'⦁ a' = a'' ∧ b'' = b'⌝);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜b'⌝ THEN ∃_tac ⌜a''⌝ THEN rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (LEMMA_T ⌜(λb''⦁ ∃ a'⦁ a'' = a' ∧ b' = b'') = (λb''⦁∃ a'⦁ a' = a'' ∧ b'' = b')⌝ asm_tac
	THEN1 (strip_tac THEN strip_tac THEN rewrite_tac[] THEN REPEAT strip_tac));
(* *** Goal "2.2.1" *** *)
a (∃_tac ⌜a''⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a (∃_tac ⌜a''⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.3" *** *)
a (asm_rewrite_tac[]);
save_cs_∃_thm(pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏snd⦎ : SET⋎nf → SET⋎nf
├─────
│ ∀a b⦁ snd (op (a, b)) = b
■

First we assert the existence of cartesian products:

=SML
val snd_def = get_spec ⌜snd⌝;
=TEX
\ignore{
=SML
set_goal([], ⌜∀ a b c d⦁
	(ι a = pair (b, c) ⇔ b = a ∧ c = a)
 ∧	(pair (b, c) = ι a ⇔ b = a ∧ c = a)
 ∧	(pair (a, b) = pair (c, d) ⇔ a = c ∧ b = d ∨ a = d ∧ b = c)
 ∧	(wkp (a, b) = wkp (c, d) ⇔ a = c ∧ b = d)
 ∧	(op (a, b) = op (c, d) ⇔ a = c ∧ b = d)
 ∧	(fst (op (a, b)) = a)
 ∧	(snd (op (a, b)) = b)
⌝);
a (REPEAT ∀_tac THEN rewrite_tac[ι_eq_pair_thm, pair_eq_ι_thm, pair_eq_pair_thm, wkp_eq_wkp_thm,
	get_spec ⌜op⌝, get_spec ⌜fst⌝, get_spec ⌜snd⌝]);
val nfu_f_pair_eq_clauses = save_pop_thm "pair_eq_clauses"; 
=TEX
}%ignore

\subsection{Axioms II}

Now that we have ordered pairs we can assert the existence of cartesian products.

=SML
val ×_ax = new_axiom (["×"],
	⌜∀u v⦁ ∃w⦁ ∀x⦁ x ∈⋎nf w ⇔ ∃y z⦁ y ∈⋎nf u ∧ z ∈⋎nf v ∧ x = op (y, z)⌝);
=TEX

The following asserts the existence of the inverse (converse?) of a relation.

=SML
val rel_inv_ax = new_axiom (["rel_inv"],
	⌜∀u⦁ ∃v⦁ ∀w⦁ w ∈⋎nf v ⇔ ∃x y⦁ w = op (x, y) ∧ op(y, x) ∈⋎nf u⌝);
=TEX

Next, the composition of two relations.

=SML
val rel_comp_ax = new_axiom (["rel_comp"],
	⌜∀t u⦁ ∃v⦁ ∀w⦁ w ∈⋎nf v ⇔
	∃x y z⦁ w = op (x, z) ∧ op(x, y) ∈⋎nf t ∧ op(y, z) ∈⋎nf u⌝);
=TEX

The domain of a relation exists.

=SML
val dom_ax = new_axiom (["dom"],
	⌜∀u⦁ ∃v⦁ ∀w⦁ w ∈⋎nf v ⇔ ∃x⦁ op (w, x) ∈⋎nf u⌝);
=TEX

Singleton Images exist.

=SML
val sing_image_ax = new_axiom (["sing_image"],
	⌜∀u⦁ ∃v⦁ ∀w⦁ w ∈⋎nf v ⇔ ∃x y⦁ op(x,y) ∈⋎nf u ∧ w = op(ι x, ι y)⌝);
=TEX

The equality relation exists.

=SML
val eq_ax = new_axiom (["eq"],
	⌜∃v⦁ ∀w⦁ w ∈⋎nf v ⇔ ∃x⦁ w = op (x, x)⌝);
=TEX

The projection relations exist.

=SML
val proj_ax = new_axiom (["proj"],
	⌜∃f s⦁ (∀w⦁ w ∈⋎nf f ⇔ ∃x y⦁ w = op (op (x, y), x))
	∧ (∀w⦁ w ∈⋎nf s ⇔ ∃x y⦁ w = op (op (x, y), y))⌝);
=TEX

We now should have enough axioms for stratified comprehension, and therefore as much as we would need for NF apart from the strengthening of extensionality.


\subsection{Finite Structures Continued}

We now define the cartesian product constructor.

=SML
declare_infix (300, "×⋎nf");
=TEX

\ignore{
=SML
set_goal([], ⌜∃ $×⋎nf⦁ ∀u v⦁ Set (u ×⋎nf v) ∧ ∀x⦁ x ∈⋎nf u ×⋎nf v ⇔ ∃y z⦁ y ∈⋎nf u ∧ z ∈⋎nf v ∧ x = op (y, z)⌝);
a (prove_∃_tac THEN REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim [⌜u'⌝,⌜v'⌝] ×_ax));
a (∃_tac ⌜if ∃z⦁ z ∈⋎nf w then w else ∅⌝
	THEN CASES_T ⌜∃z⦁ z ∈⋎nf w⌝
	(fn q => ((rewrite_tac [q, get_spec⌜Set⌝]) THEN strip_asm_tac q)));
a (REPEAT_N 5 strip_tac);
a (SPEC_NTH_ASM_T 2 ⌜x⌝ (strip_asm_tac o (rewrite_rule[asm_rule⌜∀ z⦁ ¬ z ∈⋎nf w⌝])));
a (spec_nth_asm_tac 1 ⌜y⌝);
a (spec_nth_asm_tac 1 ⌜z⌝ THEN_TRY asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ $⦏×⋎nf⦎ : SET⋎nf → SET⋎nf → SET⋎nf
├──────
│ ∀u v⦁ Set (u ×⋎nf v)
│	∧
│		∀x⦁ x ∈⋎nf u ×⋎nf v
│		⇔
│		∃y z⦁ y ∈⋎nf u ∧ z ∈⋎nf v ∧ x = op (y, z)
■

\subsection{The Theory of Relations}

A relation is a set of ordered pairs.

ⓈHOLCONST
│ ⦏Rel⦎ : SET⋎nf → BOOL
├──────
│ ∀r⦁ Rel r ⇔ ∀x⦁ x ∈⋎nf r ⇒ ∃y z⦁ x = op(y, z)
■

\ignore{
=SML
set_goal([], ⌜Rel ∅⌝);
a (rewrite_tac [get_spec ⌜Rel⌝]);
val Rel_∅_thm = pop_thm ();
=TEX
}%ignore

The universal relation:

ⓈHOLCONST
│ ⦏V⋏2⦎ : SET⋎nf
├──────
│ V⋏2 = V ×⋎nf V
■

The complement of a relation:

=SML
declare_postfix (300, "⋏rc");
=TEX

ⓈHOLCONST
│ $⦏⋏rc⦎ : SET⋎nf → SET⋎nf
├──────
│ ∀R⦁ R ⋏rc = V⋏2 \⋎nf R
■

Every relation has an inverse.

=SML
declare_postfix (320, "⋏-⋏1⋏nf");
=TEX

\ignore{
=SML
set_goal([], ⌜∃ $⋏-⋏1⋏nf⦁ ∀r⦁ Set(r ⋏-⋏1⋏nf)
	∧ ∀x⦁ x ∈⋎nf r ⋏-⋏1⋏nf ⇔ ∃y z⦁ x = op(y, z) ∧ op(z, y) ∈⋎nf r⌝);
a (prove_∃_tac THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜r'⌝ rel_inv_ax));
a (∃_tac ⌜if ∃z⦁ z ∈⋎nf v then v else ∅⌝
	THEN CASES_T ⌜∃z⦁ z ∈⋎nf v⌝
	(fn q => ((rewrite_tac [q, get_spec⌜Set⌝]) THEN strip_asm_tac q)));
a (REPEAT_N 6 strip_tac);
a (SPEC_NTH_ASM_T 2 ⌜x⌝ (strip_asm_tac o (rewrite_rule[asm_rule⌜∀ z⦁ ¬ z ∈⋎nf v⌝])));
a (spec_nth_asm_tac 1 ⌜y⌝);
a (spec_nth_asm_tac 1 ⌜z⌝ THEN_TRY asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ $⦏⋏-⋏1⋏nf⦎ : SET⋎nf → SET⋎nf
├──────
│ ∀r⦁ Set(r ⋏-⋏1⋏nf) ∧ ∀x⦁ x ∈⋎nf r ⋏-⋏1⋏nf ⇔ ∃y z⦁ x = op(y, z) ∧ op(z, y) ∈⋎nf r
■

\ignore{
=SML
set_goal([], ⌜∅ ⋏-⋏1⋏nf = ∅⌝);
a (lemma_tac ⌜Set (∅ ⋏-⋏1⋏nf) ∧ Set ∅⌝ THEN1 rewrite_tac [get_spec ⌜$⋏-⋏1⋏nf⌝, nfu_f_set_clauses]);
a (ALL_FC_T1 fc_⇔_canon rewrite_tac [nfu_f_set_ext_thm]);
a (rewrite_tac [get_spec ⌜$⋏-⋏1⋏nf⌝]);
val rel_inv_∅_thm = pop_thm ();
=TEX
}%ignore

=GFT
rel_inv_∅_thm = ⊢ ∅ ⋏-⋏1⋏nf = ∅
=TEX

Relations can be composed.
Relational composition is also known as relational product.

\ignore{
=SML
declare_infix (300, "⨾⋎nf");
set_goal([], ⌜∃$⨾⋎nf⦁ ∀r s⦁ Set(r ⨾⋎nf s)
	∧ ∀x⦁ x ∈⋎nf r ⨾⋎nf s ⇔ ∃u v w⦁ x = op(u, w) ∧ op(u, v) ∈⋎nf r ∧ op(v, w) ∈⋎nf s⌝);
a (prove_∃_tac THEN REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim [⌜r'⌝, ⌜s'⌝] rel_comp_ax));

a (∃_tac ⌜if ∃z⦁ z ∈⋎nf v then v else ∅⌝
	THEN CASES_T ⌜∃z⦁ z ∈⋎nf v⌝
	(fn q => ((rewrite_tac [q, get_spec⌜Set⌝]) THEN strip_asm_tac q)));
a (REPEAT_N 7 strip_tac);
a (SPEC_NTH_ASM_T 2 ⌜x⌝ (strip_asm_tac o (rewrite_rule[asm_rule⌜∀ z⦁ ¬ z ∈⋎nf v⌝])));
a (spec_nth_asm_tac 1 ⌜u⌝);
a (spec_nth_asm_tac 1 ⌜v'⌝ THEN_TRY asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ $⦏⨾⋎nf⦎ : SET⋎nf → SET⋎nf → SET⋎nf
├──────
│ ∀r s⦁ Set(r ⨾⋎nf s)
│	∧ ∀x⦁ x ∈⋎nf r ⨾⋎nf s
│	  ⇔ ∃u v w⦁ x = op(u, w) ∧ op(u, v) ∈⋎nf r ∧ op(v, w) ∈⋎nf s
■


Powers of relations:

=SML
declare_infix (300, "↾⋏r");
=TEX

ⓈHOLCONST
│ $⦏↾⋏r⦎ : SET⋎nf → ℕ → SET⋎nf
├──────
│ ∀R⦁	R ↾⋏r 0 = V⋏2 ∧
│ ∀n⦁	R ↾⋏r (n + 1) = (R ↾⋏r n) ⨾⋎nf R
■

\ignore{
=SML
set_goal([], ⌜∀R n⦁ Set (R ↾⋏r n)⌝);
a (REPEAT strip_tac);
a (induction_tac ⌜n⌝
	THEN rewrite_tac [get_spec ⌜$↾⋏r⌝, get_spec ⌜V⋏2⌝, get_spec ⌜$×⋎nf⌝,
	get_spec ⌜$⨾⋎nf⌝]);
val nfu_f_set_↾⋏r_thm = pop_thm ();
=TEX
}%ignore


The domain of a relation is a set.

\ignore{
=SML
set_goal([], ⌜∃dom⦁ ∀r⦁ Set(dom r) ∧ ∀x⦁ x ∈⋎nf dom r ⇔ ∃y⦁ op(x, y) ∈⋎nf r⌝);
a (prove_∃_tac THEN REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim [⌜r'⌝] dom_ax));
a (∃_tac ⌜if ∃z⦁ z ∈⋎nf v then v else ∅⌝
	THEN CASES_T ⌜∃z⦁ z ∈⋎nf v⌝
	(fn q => ((rewrite_tac [q, get_spec ⌜Set⌝]) THEN strip_asm_tac q)));
a (REPEAT strip_tac);
a (SPEC_NTH_ASM_T 2 ⌜x⌝ (strip_asm_tac o (rewrite_rule[asm_rule ⌜∀ z⦁ ¬ z ∈⋎nf v⌝])));
a (spec_nth_asm_tac 1 ⌜y⌝);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏dom⦎ : SET⋎nf → SET⋎nf
├──────
│ ∀r⦁ Set(dom r)
│	∧ ∀x⦁ x ∈⋎nf (dom r) ⇔ ∃y⦁ op(x, y) ∈⋎nf r
■

\ignore{
=SML
set_goal([], ⌜dom ∅ = ∅⌝);
a (lemma_tac ⌜Set (dom ∅) ∧ Set ∅⌝
	THEN1 rewrite_tac [get_spec ⌜dom⌝]);
a (ALL_FC_T1 fc_⇔_canon rewrite_tac [nfu_f_set_ext_thm]);
a (rewrite_tac [get_spec⌜dom⌝]);
val dom_∅_thm = pop_thm ();
=TEX
}%ignore

=GFT
dom_∅_thm = ⊢ dom ∅ = ∅
=TEX

So is the range.

ⓈHOLCONST
│ ⦏rng⦎ : SET⋎nf → SET⋎nf
├──────
│ ∀r⦁ rng r = dom (r ⋏-⋏1⋏nf)
■

ⓈHOLCONST
│ ⦏field⦎ : SET⋎nf → SET⋎nf
├──────
│ ∀r⦁ field r = (dom r) ∪⋎nf (rng r)
■

\ignore{
=SML
val rng_def = get_spec ⌜rng⌝;
val field_def = get_spec ⌜field⌝;

set_goal([], ⌜rng ∅ = ∅⌝);
a (rewrite_tac[rng_def, rel_inv_∅_thm, dom_∅_thm]);
val rng_∅_thm = pop_thm ();
=TEX
}%ignore

=GFT
rng_∅_thm = ⊢ rng ∅ = ∅
=TEX


\subsection{Proof Support II}

It is now possible to automate elementary proofs, typically of algebraic laws in the theory so far.
To this end we demonstrate (proofs not presented) various theorems which will be useful and integrate these into a `proof context'.

\ignore{
=SML
set_goal([], ⌜∀x y n⦁ Set ∅ ∧ Set V ∧ Set V⋏2 ∧ Set (x ⋏c) ∧ Set (x ∩⋎nf y)
	∧ Set (x ∪⋎nf y) ∧ Set (x \⋎nf y) ∧ Set (x Δ⋎nf y) ∧ Set (⋃⋎nf x)
	∧ Set (ι x) ∧ Set (pair(x,y)) ∧ Set (wkp(x,y)) ∧ Set (x ×⋎nf y) ∧ Set (x ⋏-⋏1⋏nf)
	∧ Set (x ⨾⋎nf y) ∧ Set (x ↾⋏r n) ∧ Set (dom x) ∧ Set (rng x) ∧ Set (field x)
⌝);
a (REPEAT ∀_tac THEN rewrite_tac (map get_spec [⌜$ι⌝, ⌜pair⌝, ⌜wkp⌝,
	⌜$×⋎nf⌝, ⌜V⋏2⌝, ⌜$⋏-⋏1⋏nf⌝, ⌜$⨾⋎nf⌝, ⌜$↾⋏r⌝, ⌜dom⌝, ⌜rng⌝, ⌜field⌝]));
a (rewrite_tac[nfu_f_set_↾⋏r_thm]);
val nfu_f_set_clauses = save_pop_thm "set_clauses";

set_goal([], ⌜∀w x y z⦁
		¬ z ∈⋎nf ∅
	∧	z ∈⋎nf V
	∧	op(w, x) ∈⋎nf V⋏2
	∧	op(w, x) ∈⋎nf y ↾⋏r 0
	∧	(z ∈⋎nf x ⋏c ⇔ ¬ z ∈⋎nf x)
	∧	(z ∈⋎nf (x ∩⋎nf y) ⇔ z ∈⋎nf x ∧ z ∈⋎nf y)
	∧	(z ∈⋎nf (x ∪⋎nf y) ⇔ z ∈⋎nf x ∨ z ∈⋎nf y)
	∧	(z ∈⋎nf (x \⋎nf y) ⇔ z ∈⋎nf x ∧ ¬ z ∈⋎nf y)
	∧	(z ∈⋎nf (x Δ⋎nf y) ⇔ z ∈⋎nf x ∧ ¬ z ∈⋎nf y ∨ ¬ z ∈⋎nf x ∧ z ∈⋎nf y)
	∧	(z ∈⋎nf (ι x) ⇔ z = x)
	∧	(z ∈⋎nf pair(x, y) ⇔ z = x ∨ z = y)
	∧	(op(w, x) ∈⋎nf y ×⋎nf z ⇔ w ∈⋎nf y ∧ x ∈⋎nf z)
	∧	(op(w, x) ∈⋎nf y ⋏-⋏1⋏nf ⇔ op(x, w) ∈⋎nf y)
⌝);
a (rewrite_tac ((map get_spec [⌜∅⌝, ⌜V⌝, ⌜$⋏c⌝, ⌜$∩⋎nf⌝, ⌜$∪⋎nf⌝, ⌜$\⋎nf⌝, ⌜$Δ⋎nf⌝,
	⌜$ι⌝, ⌜pair⌝, ⌜fst⌝, ⌜snd⌝, ⌜$×⋎nf⌝, ⌜$⋏-⋏1⋏nf⌝, ⌜$↾⋏r⌝]) @[nfu_f_pair_eq_clauses])
	THEN REPEAT strip_tac THEN_TRY all_var_elim_asm_tac);
a (rewrite_tac[get_spec ⌜V⋏2⌝, get_spec ⌜$×⋎nf⌝, nfu_f_pair_eq_clauses]);
a (∃_tac ⌜w⌝ THEN ∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜w⌝ THEN ∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜w⌝ THEN ∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val nfu_f_op_ext_clauses1 = save_pop_thm "op_ext_clauses1";

set_goal([], ⌜∀x y z n⦁
		(x ∈⋎nf (⋃⋎nf y) ⇔ ∃ z⦁ z ∈⋎nf y ∧ x ∈⋎nf z)
	∧	(x ∈⋎nf y ×⋎nf z
		 ⇔ ∃v w⦁ v ∈⋎nf y ∧ w ∈⋎nf z ∧ x = op (v, w))
	∧	(x ∈⋎nf y ⋏-⋏1⋏nf ⇔ ∃v w⦁ x = op(v, w) ∧ op(w, v) ∈⋎nf y)
	∧	(x ∈⋎nf y ⨾⋎nf z ⇔ ∃u v w⦁ x = op(u, w) ∧ op(u, v) ∈⋎nf y ∧ op(v, w) ∈⋎nf z)
	∧	(x ∈⋎nf y ↾⋏r (n + 1) ⇔
			∃u v w⦁ x = op(u, w) ∧ op(u, v) ∈⋎nf y ↾⋏r n ∧ op(v, w) ∈⋎nf y)
	∧	(x ∈⋎nf (dom y) ⇔ ∃u⦁ op(x,u) ∈⋎nf y) 
	∧	(x ∈⋎nf (rng y) ⇔ ∃u⦁ op(u,x) ∈⋎nf y) 
	∧	(x ∈⋎nf (field y) ⇔ ∃u⦁ op(x,u) ∈⋎nf y ∨ op(u,x) ∈⋎nf y) 
⌝);
a (REPEAT ∀_tac);
a (rewrite_tac (map get_spec [⌜$⋃⋎nf⌝, ⌜$×⋎nf⌝, ⌜$⋏-⋏1⋏nf⌝, ⌜$⨾⋎nf⌝, ⌜dom⌝, ⌜rng⌝, ⌜field⌝, ⌜$↾⋏r⌝]));
a (REPEAT strip_tac THEN_TRY all_var_elim_asm_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (all_fc_tac [get_spec ⌜op⌝]);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜u⌝ THEN ∃_tac ⌜x⌝ THEN ∃_tac ⌜u⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (∃_tac ⌜y'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (all_fc_tac [get_spec ⌜op⌝] THEN all_var_elim_asm_tac);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
(* *** Goal "5" *** *)
a (spec_nth_asm_tac 1 ⌜u⌝);
(* *** Goal "6" *** *)
a (∃_tac ⌜u⌝ THEN ∃_tac ⌜x⌝ THEN ∃_tac ⌜u⌝ THEN asm_rewrite_tac[]);
val nfu_f_op_ext_clauses2 = save_pop_thm "op_ext_clauses2";
=TEX
}%ignore

The proof and use of theorems about the algebra of sets in nfu is complicated by the presence of urelements in the domain of discourse.
This would naturally suggest that this kind of theorem would involve restricted quantification over just the sets.
This kind of theorem is harder to apply than one involving unrestricted quantification because of the need to prove that the values being manipulated are all sets.
To limit the inconvenience occasioned by these considerations the definitions of the various operations over sets have been written so that they do not care whether their objects are sets or not, but will always yield sets with an extension determined by the extension of the operands.
The result of one of these operations will always be a set, even if the operands are not.

The plan is then that the proof of an equation between expressions begins with the demonstration that the operands are sets, which will usually be trivial, and then proceeds by application of a version of extensionality which is good for all sets.
The subset relations are defined extensionality so they can be expanded without demonstrating that the arguments are sets.


Then we provide a theorem to assist in proving that expressions do denote sets.

=GFT
nfu_f_set_clauses =
   ⊢ ∀ x y
     ⦁ Set ∅
         ∧ Set V
	∧ Set V⋏2
         ∧ Set (x ⋏c)
         ∧ Set (x ∩⋎nf y)
         ∧ Set (x ∪⋎nf y)
         ∧ Set (x \⋎nf y)
         ∧ Set (x Δ⋎nf y)
         ∧ Set (⋃⋎nf x)
	∧ Set (ι x)
	∧ Set (pair(x,y))
	∧ Set (wkp(x,y))
	∧ Set (x ×⋎nf y)
	∧ Set (x ⋏-⋏1⋏nf)
	∧ Set (x ⨾⋎nf y)
         ∧ Set (x ↾⋏r n)
	∧ Set (dom x)
	∧ Set (rng x)
	∧ Set (field x)
=TEX

Now we need extensional characterisations of the set operators:

=GFT
nfu_f_op_ext_clauses1 =
   ⊢ ∀ w x y z
     ⦁ ¬ z ∈⋎nf ∅
         ∧ z ∈⋎nf V
	∧ op(w, x) ∈⋎nf V⋏2
         ∧ (z ∈⋎nf x ⋏c ⇔ ¬ z ∈⋎nf x)
         ∧ (z ∈⋎nf x ∩⋎nf y ⇔ z ∈⋎nf x ∧ z ∈⋎nf y)
         ∧ (z ∈⋎nf x ∪⋎nf y ⇔ z ∈⋎nf x ∨ z ∈⋎nf y)
         ∧ (z ∈⋎nf x \⋎nf y ⇔ z ∈⋎nf x ∧ ¬ z ∈⋎nf y)
         ∧ (z ∈⋎nf x Δ⋎nf y ⇔ z ∈⋎nf x ∧ ¬ z ∈⋎nf y ∨ ¬ z ∈⋎nf x ∧ z ∈⋎nf y)
	∧ (op(w, x) ∈⋎nf y ×⋎nf z ⇔ w ∈⋎nf y ∧ x ∈⋎nf z)

nfu_f_op_ext_clauses2 =
   ⊢ ∀ x y z
     ⦁ (x ∈⋎nf ⋃⋎nf y ⇔ (∃ z⦁ z ∈⋎nf y ∧ x ∈⋎nf z))
         ∧ (x ∈⋎nf y ×⋎nf z ⇔ (∃ v w⦁ v ∈⋎nf y ∧ w ∈⋎nf z ∧ x = op (v, w)))
         ∧ (x ∈⋎nf y ⋏-⋏1⋏nf ⇔ (∃ v w⦁ x = op (v, w) ∧ op (w, v) ∈⋎nf y))
         ∧ (x ∈⋎nf y ⨾⋎nf z ⇔
		(∃ u v w⦁ x = op (u, w) ∧ op (u, v) ∈⋎nf y ∧ op (v, w) ∈⋎nf z))
	∧ (x ∈⋎nf y ↾⋏r (n + 1) ⇔
		(∃u v w⦁ x = op(u, w) ∧ op(u, v) ∈⋎nf y ↾⋏r n ∧ op(v, w) ∈⋎nf y))
         ∧ (x ∈⋎nf dom y ⇔ (∃ u⦁ op (x, u) ∈⋎nf y))
         ∧ (x ∈⋎nf rng y ⇔ (∃ u⦁ op (u, x) ∈⋎nf y))
         ∧ (x ∈⋎nf field y ⇔ (∃ u⦁ op (x, u) ∈⋎nf y ∨ op (u, x) ∈⋎nf y))

=TEX

\ignore{
We now need a bit of programming to deal with the conditions on extensionality of equations.

=SML
force_new_pc "'nfu_f1";
add_rw_thms [nfu_f_set_clauses, nfu_f_op_ext_clauses1] "'nfu_f1";
set_sc_eqn_cxt ([(⌜x = y⌝, nfu_f_eq_ext_conv)]) "'nfu_f1";
add_sc_thms [nfu_f_set_clauses, nfu_f_op_ext_clauses1, nfu_f_op_ext_clauses2] "'nfu_f1";
add_st_thms [nfu_f_op_ext_clauses1, nfu_f_op_ext_clauses2] "'nfu_f1";

force_new_pc "'nfu_f2";
set_rw_eqn_cxt ([(⌜x = y⌝, nfu_f_eq_ext_conv)]) "'nfu_f2";
add_rw_thms [get_spec ⌜$⊆⋎nf⌝, nfu_f_op_ext_clauses2] "'nfu_f2";

set_pr_conv nfu_f_prove_conv "'nfu_f2";
set_pr_tac nfu_f_prove_tac "'nfu_f2";

set_merge_pcs ["hol1", "'savedthm_cs_∃_proof", "'nfu_f1", "'nfu_f2"];
=TEX
}%ignore

\ignore{
=SML
set_goal([], ⌜∀A⦁
	  V ⋏c = ∅
	∧ ∅ ⋏c = V
	∧ A ∩⋎nf ∅ = ∅
	∧ ∅ ∩⋎nf A = ∅
	∧ (A ⋏c) ∩⋎nf A = ∅
	∧ A ∩⋎nf (A ⋏c) = ∅
	∧ A ∪⋎nf V = V
	∧ V ∪⋎nf A = V
	∧ (A ⋏c) ∪⋎nf A = V
	∧ A ∪⋎nf (A ⋏c) = V
	∧ A \⋎nf A = ∅
	∧ A Δ⋎nf A = ∅
	∧ A Δ⋎nf (A ⋏c) = V
	∧ (A ⋏c) Δ⋎nf A = V
	∧ ⋃⋎nf V = V
	∧ ⋃⋎nf ∅ = ∅
	∧ ∅ ⋏-⋏1⋏nf = ∅
	∧ ∅ ⨾⋎nf x = ∅
	∧ x ⨾⋎nf ∅ = ∅
	∧ dom ∅ = ∅
	∧ rng ∅ = ∅
	∧ field ∅ = ∅
	∧ Rel ∅
⌝);
a (prove_tac [get_spec ⌜Rel⌝]);
a (∃_tac ⌜V⌝ THEN rewrite_tac[]);
val nfu_f_∅V_clauses = save_pop_thm "∅V_clauses";

add_rw_thms [nfu_f_∅V_clauses, nfu_f_pair_eq_clauses] "'nfu_f1";
add_sc_thms [nfu_f_∅V_clauses, nfu_f_pair_eq_clauses] "'nfu_f1";
add_st_thms [nfu_f_∅V_clauses, nfu_f_pair_eq_clauses] "'nfu_f1";
set_merge_pcs ["hol1", "'savedthm_cs_∃_proof", "'nfu_f1", "'nfu_f2"];
=TEX
}%ignore

=GFT
nfu_f_∅V_clauses =
   ⊢ 	∀A⦁ V ⋏c = ∅
	∧ ∅ ⋏c = V
	∧ A ∩⋎nf ∅ = ∅
	∧ ∅ ∩⋎nf A = ∅
	∧ (A ⋏c) ∩⋎nf A = ∅
	∧ A ∩⋎nf (A ⋏c) = ∅
	∧ A ∪⋎nf V = V
	∧ V ∪⋎nf A = V
	∧ (A ⋏c) ∪⋎nf A = V
	∧ A ∪⋎nf (A ⋏c) = V
	∧ A \⋎nf A = ∅
	∧ A Δ⋎nf A = ∅
	∧ A Δ⋎nf (A ⋏c) = V
	∧ (A ⋏c) Δ⋎nf A = V
	∧ ⋃⋎nf V = V
	∧ ⋃⋎nf ∅ = ∅
	∧ ∅ ⋏-⋏1⋏nf = ∅
	∧ ∅ ⨾⋎nf x = ∅
	∧ x ⨾⋎nf ∅ = ∅
	∧ dom ∅ = ∅
	∧ rng ∅ = ∅
	∧ field ∅ = ∅
	∧ Rel ∅
=TEX

\subsection{Stratified Comprehension}

By adopting a finite axiomatisation of NF(U) we have evaded the difficulty of formally expressing in HOL the axiom of stratified comprehension.

The practical issue which arises whether stratified comprehension is an axiom or not, is that of establishing the existence and properties (extension) of sets corresponding to stratified properties.
Whether an higher order axiom of stratified comprehension or a finite first order axiom system is adopted there is some work to required to make stratified comprehension workable.
Ih Holmes's book \cite{holmes98} this appears as a metatheoretic interlude at about this place in the exposition, in which it is proven that the axioms now in place suffice to prove the existence of a set extensionally identical with each property of sets which is expressible as a stratified first order formula.
Once this metatheoretic result is in place, it suffices in an informal treatment to accept the existence of a set once a suitable stratified formula has been exhibited.
In our more rigid mechanically checked system, this method will not suffice.

\subsection{Introducing Functions}

Here I may begin to diverge more from Holmes, since the material on functions does not contribute to the axiom system, and I have in mind the use of functions in the appication of NFU to the construction of category theoretic foundations.

A function is a many-one relation:

ⓈHOLCONST
│ ⦏ManyOne⋎nf⦎ : SET⋎nf → BOOL
├──────
│ ∀r⦁ ManyOne⋎nf r ⇔ ∀x⦁ x ∈⋎nf dom r ⇒
│	∀y z⦁ op(x, y) ∈⋎nf r ∧ op(x, z) ∈⋎nf r ⇒ y = z   
■

Identity functions will prove useful later (though we have yet to prove that they exist):

ⓈHOLCONST
│ ⦏id⦎ : SET⋎nf → SET⋎nf
├──────
│ ∀a x⦁ x ∈⋎nf (id a) = ∃y⦁ y ∈⋎nf a ∧ x = op(y, y)  
■

Function application is an infix suffix {\it u}.

=SML
declare_infix (320, "⋎nf");
=TEX

\ignore{
=IGN
stop;
set_goal([], ⌜∃ $⋎nf⦁ ∀f a v⦁ op(a, v) ∈⋎nf f ⇒ f ⋎nf a = v⌝);
a (prove_∃_tac THEN REPEAT strip_tac);

fun cond_∃_tac t =
 let	val (var, body) = dest_∃ t;
	val strip_⇒	 

set_goal([], ⌜∀p q⦁ (∃x⦁ p x) ⇒ ∃x⦁ q x ⇒ p x⌝);
a (REPEAT strip_tac);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val ∃_⇒_thm = pop_thm();

set_goal([⌜Rel y⌝], ⌜∃x⦁ Rel x⌝);

=TEX
}%ignore

ⓈHOLCONST
│ $⦏⋎nf⦎ : SET⋎nf → SET⋎nf → SET⋎nf
├──────
│ ∀f a v⦁ op(a, v) ∈⋎nf f ⇒ f ⋎nf a = v 
■


\subsection{Cantorian Sets}





\subsection{Strong Extensionality}

Once again, we introduce a new theory for the strongly extensional system,
First of all, we must give the the ML commands to introduce the new theory ``nff'' as a child of the theory ``nfu\_f''.

=SML
open_theory "nfu_f";
force_new_theory "nff";
set_merge_pcs["hol1", "'savedthm_cs_∃_proof", "'nfu_f1", "'nfu_f2"];
=TEX

\ignore{
=SML
set_flag ("pp_use_alias", true);
=IGN
open_theory "nff";
set_merge_pcs["hol1", "'savedthm_cs_∃_proof", "'nfu_f1", "'nfu_f2"];
=TEX
}%ignore

The distinguishing feature of NF is that there are no urelements.
We might as well make this the new axiom.

=SML
val N13_ax = new_axiom (["N13"],
	⌜¬ ∃x⦁ Ur x⌝);
=TEX

This of course means that everything is a set...

\ignore{
=SML
set_goal([], ⌜∀x⦁ Set x⌝);
a (strip_asm_tac (rewrite_rule [get_spec ⌜Ur⌝] N13_ax));
a (asm_rewrite_tac[]);
val nff_Set_thm = save_pop_thm "Set_thm";
=TEX
}%ignore

=GFT
nff_Set_thm =
	⊢ ∀ x⦁ Set x
=TEX

and hence that extensionality is now unconditional:

\ignore{
=SML
val nff_ext_thm = save_thm ("ext_thm", rewrite_rule [nff_Set_thm] nfu_f_set_ext_thm);
=TEX
}%ignore

=GFT
nff_ext_thm = 
	⊢ ∀ x y⦁ x = y ⇔ (∀ z⦁ z ∈⋎nf x ⇔ z ∈⋎nf y)
=TEX

At the elementary level we have so far reached this doesn't make a big difference so we will say no more {\it pro-tem}.

Doesn't make much difference, unless perhaps it actually makes the system inconsistent,

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
\include{nf_h.th}
}  %\let

{\let\Section\section
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{nfu_s.th}
}  %\let

{\let\Section\section
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{nfu_f.th}
}  %\let


\twocolumn[\section{INDEX}\label{index}]

{\small\printindex}

\end{document}
