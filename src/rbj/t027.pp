=IGN
$Id: t027.doc,v 1.7 2012/08/11 21:01:52 rbj Exp $
open_theory "infos";

set_flag ("pp_use_alias", true);

set_merge_pcs ["misc21", "'infos"];
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\usepackage{graphics}
%\ftlinepenalty=9999
\usepackage{A4}

%\def\ExpName{\mbox{{\sf exp}
%\def\Exp#1{\ExpName(#1)}

\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{Infinitary First Order Set Theory}
\makeindex
\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}, bookmarks=false, pdffitwindow=false}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

\author{Roger Bishop Jones}
\date{\ }

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
The abstract syntax and semantics of an infinitary first order set theory.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created: 2008/12/05

Last Change $ $Date: 2012/08/11 21:01:52 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t027.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t027.pdf}

$ $Id: t027.doc,v 1.7 2012/08/11 21:01:52 rbj Exp $ $

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

The idea is to obtain exotic models of set theory using definability in first order set theory as a source of candidate sets.

To ensure that we get all the well-founded sets we start with definability in an infinitary first order set theory ({\it infos}).
Given any membership structure, i.e. a domain of discourse and a membership relation over that domain, each formula of {\it infos} with one free variable will define a subset of the domain of discourse (you may prefer to think of these as classes, since they will often have the same size as the domain).

If we take as our domain of discourse the formulae of {\it infos} having a single free variable, then the semantics of {\it infos} gives rise to a functor which, given one membership relation over that domain will yield another membership relation.
Over this domain the functor can have no fixed point, for we would have a formula for the Russell set.
To obtain a set theory, we must omit some of these potential sets, i.e. we must consisider subsets as potential domains.
Any subset together with a fixed point of the semantic functor will yeild an interpretation of set theory.

It seems clear that some subsets of the formulae of {\it infos} do have fixed points under the semantics of {\it infos}.
For example, a collection of formulae denoting all the well-founded sets, or those denoting well-founded sets or their complements.

It is the purpose of this work to see whether models for rich non-well-founded set theories can be obtained in this way.
The purpose is ultimately to provide a semantic basis for a kind of type theory suitable for ``formalised mathematics in the large'', in which ordinary mathematics is done primarily using well-founded sets and abstract mathematics often involves non-well-founded sets (theories generic over many types).

=SML
open_theory "misc2";
force_new_theory "⦏infos⦎";
force_new_pc ⦏"'infos"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'infos";
set_merge_pcs ["misc21", "'infos"];
=TEX

\section{SYNTAX}

The syntax of infinitary first order set theory is to be encoded as sets in a higher order set theory.

This is (in effect if not in appearance) an ``inductive datatype'' (albeit transfinite) so we should expect the usual kinds of theorems.

Informally these should say:

\begin{enumerate}
\item Syntax is closed under the two constructors.
\item The syntax constructors are injections and have disjoint ranges
\item The ranges of the constructors partition the syntax. 
\item Any syntactic property which is preserved by the constructors (i.e. is true of any construction if it is true of all its syntactic constituents) is true of everything in the syntax (this is an induction principle).
\item A recursion theorem which supports definition of recursive functions over the syntax.
\end{enumerate}

As well as the constructors, discriminators and destructors are defined.

\subsection{Constructors, Discriminators and Destructors}


Preliminary to presenting the inductive definition of the required classes we define the nuts and bolts operations on the required syntactic entities (some of which will be used in the inductive definition).

Note the terminology here.

\begin{description}
\item[constructor]
A function which constructs a complex structure in the abstract syntax from the immediate constituents of that structure.
\item[discrimiator]
A propositional function or predicate which tests for a particular class of entities in the abstract syntax.
This will normally be that class of entities formed using some particular constructor.
\item[descructor]
A function which extracts from a complex entity of the abstract syntax one or more of the immediate constutuents from which it was constructed.
\end{description}

More concisely, a constructor puts together some syntactic entity from its constituents, discriminators distinguist between the different kinds of entity and destructors take them apart.

This is a first order language in which the terms are just variables, and the variables can be arbitrary sets, allowing that there may be very large numbers of them.
We therefore proceed directly to the syntax of formulae.

``Atomic'' formulae are just membership predicates, of which the operands will always be variables.
An atomic formula can therefore be represented in the abstract syntax by an ordered pair, tagged with a zero to distinguish it as am atomic formaula from other kinds of formulae.

The constructor is:

ⓈHOLCONST
│ ⦏MkAf⦎ : GS × GS → GS
├───────────
│ ∀lr⦁ MkAf lr = (Nat⋎g 0) ↦⋎g ((Fst lr) ↦⋎g (Snd lr))
■

A discriminator is:

ⓈHOLCONST
│ ⦏IsAf⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsAf t ⇔ ∃lr⦁ t = MkAf lr
■

And we supply two desctructors, the first returning the set in which membership is asserted:

ⓈHOLCONST
│ ⦏AfSet⦎ : GS → GS
├───────────
│  AfSet = λx⦁ snd(snd x)
■

and the second returning the set which is alleged to be the member:

ⓈHOLCONST
│ ⦏AfMem⦎ : GS → GS
├───────────
│  AfMem = λx⦁ fst(snd x)
■

We have just one way of forming compound formulae, which should be thought of as a generalised infinitary scheffed stroke.

ⓈHOLCONST
│ ⦏MkCf⦎ : GS × GS → GS
├───────────
│ ∀vc⦁ MkCf vc = (Nat⋎g 1) ↦⋎g ((Fst vc) ↦⋎g (Snd vc))
■

The two components of a compound formula are, on the left a set of variables (of any cardinality) and on the right a set of subformulae (also of arbitrary cardinality).
Semantically this compound formula should be thought of as an infinitary existentially generalised NOR, and will be true if under any assignment of values to the bound variables at least one of the constituent formulae comes out false.
This is complicated somewhet in the formal semantics which follows by the adoption of a four truth values, which however is merely a device to facilitate finding two-valued fixed points in the semantics.

The discriminator is:

ⓈHOLCONST
│ ⦏IsCf⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsCf t ⇔ ∃vc⦁ t = MkCf vc
■

and the following two functions are the desctructors:

ⓈHOLCONST
│ ⦏CfVars⦎ : GS → GS
├───────────
│  CfVars = λx⦁ fst(snd x)
■

ⓈHOLCONST
│ ⦏CfForms⦎ : GS → GS
├───────────
│  CfForms = λx⦁ snd(snd x)
■

=GFT
⦏Is_clauses⦎ =
   ⊢ (∀ x⦁ IsAf (MkAf x))
       ∧ (∀ x⦁ ¬ IsAf (MkCf x))
       ∧ (∀ x⦁ ¬ IsCf (MkAf x))
       ∧ (∀ x⦁ IsCf (MkCf x))
=TEX
=GFT
⦏syn_proj_clauses⦎ =
    ⊢ (∀ s m⦁ AfSet (MkAf (s, m)) = s)
       ∧ (∀ s m⦁ AfMem (MkAf (s, m)) = m)
       ∧ (∀ v f⦁ CfVars (MkCf (v, f)) = v)
       ∧ (∀ v f⦁ CfForms (MkCf (v, f)) = f)
=TEX
=GFT
⦏syn_con_inv_fc_clauses⦎ =
   ⊢ ∀ p
     ⦁ (IsAf p ⇒ MkAf (AfMem p, AfSet p) = p)
         ∧ (IsCf p ⇒ MkCf (CfVars p, CfForms p) = p)
=TEX
=GFT
⦏syn_con_eq_clauses⦎ =
   ⊢ ∀p1 p2⦁ (MkAf p1 = MkAf p2 ⇔ p1 = p2) ∧ (MkCf p1 =  MkCf p2 ⇔ p1 = p2)
=TEX
=GFT
⦏syn_con_neq_clauses⦎ =
   ⊢ ∀ x y⦁ ¬ MkAf x = MkCf y
=TEX
=GFT
⦏is_fc_clauses1⦎ =
   ⊢ ∀ x
     ⦁ (IsAf x ⇒ (∃ s m⦁ x = MkAf (s, m)))
         ∧ (IsCf x ⇒ (∃ vars fs⦁ x = MkCf (vars, fs)))
=TEX
=GFT
⦏Is_not_cases⦎ =
   ⊢ ∀ x⦁ ¬ IsAf x ∨ ¬ IsCf x

⦏Is_not_fc_clauses⦎ =
   ⊢ (∀ x⦁ IsAf x ⇒ ¬ IsCf x) ∧ (∀ x⦁ IsCf x ⇒ ¬ IsAf x)
=TEX

\ignore{
=IGN
set_flag("subgoal_package_quiet", true);
=SML

set_goal([], ⌜(∀x⦁ IsAf (MkAf x))
	∧ (∀x⦁ ¬ IsAf (MkCf x))
	∧ (∀x⦁ ¬ IsCf (MkAf x))
	∧ (∀x⦁ IsCf (MkCf x))
	⌝);
a (rewrite_tac [get_spec ⌜IsAf⌝,
	get_spec ⌜MkAf⌝,
	get_spec ⌜IsCf⌝,
	get_spec ⌜MkCf⌝]);
a (strip_tac);
a (∃_tac ⌜x⌝ THEN rewrite_tac[]);
val Is_clauses = save_pop_thm "Is_clauses";

set_goal([], ⌜(∀s m⦁ AfMem (MkAf (m, s)) = m)
	∧	(∀s m⦁ AfSet (MkAf (m, s)) = s)
	∧	(∀v f⦁ CfVars (MkCf (v, f)) = v)
	∧	(∀v f⦁ CfForms (MkCf (v, f)) = f)
⌝);
a (rewrite_tac (map get_spec [
	⌜MkAf⌝, ⌜MkCf⌝,
	⌜AfSet⌝, ⌜AfMem⌝, ⌜CfVars⌝, ⌜CfForms⌝]));
val syn_proj_clauses = save_pop_thm "syn_proj_clauses";

set_goal([], ⌜∀p⦁ (IsAf p ⇒ MkAf (AfMem p, AfSet p) = p)
	∧	(IsCf p ⇒ MkCf (CfVars p, CfForms p) = p)
⌝);
a (rewrite_tac (map get_spec [
	⌜MkAf⌝, ⌜MkCf⌝,
	⌜AfSet⌝, ⌜AfMem⌝, ⌜CfVars⌝, ⌜CfForms⌝, ⌜IsAf⌝, ⌜IsCf⌝])
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[]);
val syn_con_inv_fc_clauses = save_pop_thm "syn_con_inv_fc_clauses";

set_goal([], ⌜∀p1 p2⦁ (MkAf p1 = MkAf p2 ⇔ p1 = p2) ∧ (MkCf p1 =  MkCf p2 ⇔ p1 = p2)⌝);
a (REPEAT ∀_tac THEN once_rewrite_tac [prove_rule [] ⌜∀p⦁ p = (Fst p, Snd p)⌝]
	THEN rewrite_tac (map get_spec [⌜MkAf⌝, ⌜MkCf⌝, ⌜AfSet⌝, ⌜AfMem⌝, ⌜CfVars⌝, ⌜CfForms⌝, ⌜IsAf⌝, ⌜IsCf⌝])
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[]);
val syn_con_eq_clauses = save_pop_thm "syn_con_eq_clauses";

set_goal([], ⌜∀x y⦁ ¬ MkAf x = MkCf y⌝);
a (rewrite_tac (map get_spec [⌜MkAf⌝, ⌜MkCf⌝]));
val syn_con_neq_clauses = save_pop_thm "syn_con_neq_clauses";

add_pc_thms "'infos" [ord_nat_thm, Is_clauses, syn_proj_clauses, syn_con_eq_clauses, syn_con_neq_clauses];
set_merge_pcs ["misc21", "'infos"];

set_goal([], ⌜∀x⦁
	(IsAf x ⇒ ∃s m⦁ x = MkAf (s, m))
∧	(IsCf x ⇒ ∃vars fs⦁ x = MkCf (vars, fs))
⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜IsAf⌝, get_spec ⌜MkAf⌝, get_spec ⌜IsCf⌝, get_spec ⌜MkCf⌝]);
a (REPEAT strip_tac);
a (∃_tac ⌜Fst lr⌝ THEN ∃_tac ⌜Snd lr⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜Fst vc⌝ THEN ∃_tac ⌜Snd vc⌝ THEN asm_rewrite_tac[]);
val is_fc_clauses1 = save_pop_thm "is_fc_clauses1";

set_goal([], ⌜∀x⦁ ¬ IsAf x ∨ ¬ IsCf x⌝);
a (rewrite_tac (map get_spec [⌜IsAf⌝, ⌜IsCf⌝, ⌜MkAf⌝, ⌜MkCf⌝]));
a (REPEAT strip_tac THEN asm_rewrite_tac[]
	THEN contr_tac THEN FC_T (MAP_EVERY ante_tac) [natg_one_one_thm]
	THEN PC_T1 "lin_arith" rewrite_tac[]);
val Is_not_cases = save_pop_thm "Is_not_cases";

set_goal ([], ⌜
	(∀x⦁ IsAf x ⇒ ¬ IsCf x)
∧	(∀x⦁ IsCf x ⇒ ¬ IsAf x)
⌝);
a (rewrite_tac (map get_spec [⌜IsAf⌝, ⌜IsCf⌝, ⌜MkAf⌝, ⌜MkCf⌝]));
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
│ ∀f⦁ MkNot f = MkCf (∅⋎g, Pair⋎g f f)
■

\subsection{The Inductive Definition of Syntax}

This is accomplished by defining the required closure condition (closure under the above constructors for arguments of the right kind) and then taking the intersection of all sets which satisfy the closure condition.

The closure condition is:

ⓈHOLCONST
│ ⦏RepClosed⦎: GS SET → BOOL
├───────────
│ ∀ s⦁ RepClosed s ⇔
│	(∀ s2 m⦁ MkAf (s2, m) ∈ s)
│∧	(∀ vars fs⦁ X⋎g fs ⊆ s ⇒ MkCf (vars, fs) ∈ s)
■

The well-formed syntax is then the smallest set closed under these constructions.

ⓈHOLCONST
│ ⦏Syntax⦎ : GS SET
├───────────
│ Syntax = ⋂{x | RepClosed x}
■

I have contrived to arrange the semantics which follows as a monotone function over a complete partial order, so that when I start to look for fixed points of the semantic functor (to give the membership relation for an intepretation of set theory) I can look at the least and greatest fixed points, and either prove one of the total or otherwise employ them to find a total fixed point.

In this scenario the least and greatest fixed points are dual to each other, and there should be a close correspondence between the proofs, the least fixed point corresponding to an inductive and the greatest to a coinductive definition of membership.

When looking at the syntax, which is of course inductively defined, this dualistic mania made me think perhaps that I should also be working with a coinductive version and this provoked my to define {\it CoSyntax} and replicate some results dual to those proven for the syntax.

I doubt very much that there is any value in this exercise (even if I have got it right), since the pertinent duality flows from the lattice of (four) truth values which I use in the semantics, and this has nothing to do with the syntax.
However, pro-tem I will leave the cosyntax definitions in place.

ⓈHOLCONST
│ ⦏RepOpen⦎: GS SET → BOOL
├───────────
│ ∀ s⦁ RepOpen s ⇔ (∀ vars fs⦁ MkCf (vars, fs) ∈ s ⇒ X⋎g fs ⊆ s)
■

ⓈHOLCONST
│ ⦏CoSyntax⦎ : GS SET
├───────────
│ CoSyntax = ⋃{x | RepOpen x}
■

\subsection{Closure}\label{Closure}

=GFT
⦏repclosed_syntax_lemma⦎ =
	⊢ RepClosed Syntax

⦏repopen_cosyntax_lemma⦎ =
	⊢ RepOpen CoSyntax
=TEX
=GFT
⦏repclosed_syntax_thm⦎ =
	⊢ (∀ s m⦁ MkAf (s, m) ∈ Syntax)
       ∧ (∀ vars fs
       ⦁ (∀ x⦁ x ∈ X⋎g fs ⇒ x ∈ Syntax) ⇒ MkCf (vars, fs) ∈ Syntax)

⦏repopen_cosyntax_thm⦎ =
   ⊢ ∀ vars fs⦁ MkCf (vars, fs) ∈ CoSyntax ⇒ (∀ x⦁ x ∈ X⋎g fs ⇒ x ∈ CoSyntax)
=TEX
=GFT
⦏repclosed_syntax_thm2⦎ =
   ⊢ (∀ s2 m⦁ MkAf (s2, m) ∈ Syntax)
       ∧ (∀ vars fs⦁ (∀ x⦁ x ∈⋎g fs ⇒ x ∈ Syntax) ⇒ MkCf (vars, fs) ∈ Syntax)

⦏repopen_cosyntax_thm2⦎ =
   ⊢ ∀ vars fs⦁ MkCf (vars, fs) ∈ CoSyntax ⇒ (∀ x⦁ x ∈⋎g fs ⇒ x ∈ CoSyntax)
=TEX
=GFT
⦏repclosed_syntax_lemma1⦎ =
	⊢ ∀ s⦁ RepClosed s ⇒ Syntax ⊆ s

⦏repopen_cosyntax_lemma1⦎ =
	⊢ ∀ s⦁ RepOpen s ⇒ s ⊆ CoSyntax
=TEX
=GFT
⦏repclosed_syntax_lemma2⦎ =
	⊢ ∀ p⦁ RepClosed {x|p x} ⇒ (∀ x⦁ x ∈ Syntax ⇒ p x)

⦏repopen_cosyntax_lemma2⦎ =
   ⊢ ∀ p⦁ RepOpen {x|p x} ⇒ (∀ x⦁ p x ⇒ x ∈ CoSyntax)
=TEX

\ignore{
=SML
set_goal([], ⌜RepClosed Syntax⌝);
val _ = a (rewrite_tac (map get_spec [⌜RepClosed⌝])
	THEN strip_tac);
(* *** Goal "1" *** *)
val _ = a (rewrite_tac (map get_spec [⌜RepClosed⌝, ⌜Syntax⌝])
	THEN REPEAT strip_tac THEN asm_fc_tac [] THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
val _ = a (rewrite_tac (map get_spec [ ⌜Syntax⌝])
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
val _ = a (fc_tac [get_spec ⌜RepClosed⌝]);
val _ = a (lemma_tac ⌜∀ x⦁ x ∈ X⋎g fs ⇒ x ∈ s⌝
	THEN1 (REPEAT strip_tac THEN all_asm_fc_tac[]));
val _ = a (all_asm_fc_tac[]);
a (asm_rewrite_tac[]);
val repclosed_syntax_lemma = pop_thm();

set_goal([], ⌜RepOpen CoSyntax⌝);
a (rewrite_tac (map get_spec [⌜RepOpen⌝, ⌜CoSyntax⌝])
	THEN REPEAT strip_tac);
a (all_asm_fc_tac []);
a (∃_tac ⌜s⌝ THEN asm_rewrite_tac[]);
val repopen_cosyntax_lemma = pop_thm();

val repclosed_syntax_thm = save_thm ("repclosed_syntax_thm",
	rewrite_rule [get_spec ⌜RepClosed⌝] repclosed_syntax_lemma);

val repopen_cosyntax_thm = save_thm ("repopen_cosyntax_thm",
	rewrite_rule [get_spec ⌜RepOpen⌝] repopen_cosyntax_lemma);

val repclosed_syntax_thm2 = save_thm ("repclosed_syntax_thm2",
	rewrite_rule [get_spec ⌜X⋎g⌝] repclosed_syntax_thm);

val repopen_cosyntax_thm2 = save_thm ("repopen_cosyntax_thm2",
	rewrite_rule [get_spec ⌜X⋎g⌝] repopen_cosyntax_thm);

local val _ = set_goal([], ⌜∀s⦁ RepClosed s ⇒ Syntax ⊆ s⌝);
val _ = a (rewrite_tac [get_spec ⌜Syntax⌝]
	THEN prove_tac[]);
in val repclosed_syntax_lemma1 = save_pop_thm "repclosed_syntax_lemma1";
end;

set_goal([], ⌜∀s⦁ RepOpen s ⇒ s ⊆ CoSyntax⌝);
a (rewrite_tac [get_spec ⌜CoSyntax⌝]
	THEN prove_tac[]);
val repopen_cosyntax_lemma1 = save_pop_thm "repopen_cosyntax_lemma1";

local val _ = set_goal([], ⌜∀p⦁ RepClosed {x | p x} ⇒ ∀x⦁ x ∈ Syntax ⇒ p x⌝);
val _ = a (rewrite_tac [get_spec ⌜Syntax⌝] THEN REPEAT strip_tac);
val _ = a (asm_fc_tac[]);
in val repclosed_syntax_lemma2 = save_pop_thm "repclosed_syntax_lemma2";
end;

set_goal([], ⌜∀p⦁ RepOpen {x | p x} ⇒ ∀x⦁ p x ⇒ x ∈ CoSyntax⌝);
val _ = a (rewrite_tac [get_spec ⌜CoSyntax⌝] THEN REPEAT strip_tac);
a (∃_tac ⌜{x|p x}⌝ THEN asm_rewrite_tac[]);
val repopen_cosyntax_lemma2 = save_pop_thm "repopen_cosyntax_lemma2";
=TEX
}%ignore

\subsection{Recursion and Induction Principles and Rules}\label{Induction}

We need to be able to define functions by recursion over this syntax.
To do that we need to prove that the syntax of comprehensions is well-founded.
This is itself equivalent to an induction principle, so we can try and derive it using the induction principles already available.

We must first define the relation of priority over the syntax, i.e. the relation between an element of the syntax and its constitutents.

ⓈHOLCONST
│ ⦏ScPrec⦎ : GS REL
├───────────
│ ∀α γ⦁ ScPrec α γ ⇔
│	∃ord fs⦁ α ∈⋎g fs ∧ {α; γ} ⊆ Syntax ∧ γ = MkCf (ord, fs)
■

ⓈHOLCONST
│ ⦏ScPrec2⦎ : GS REL
├───────────
│ ∀α γ⦁ ScPrec2 α γ ⇔
│	∃ord fs⦁ α ∈⋎g fs ∧ γ = MkCf (ord, fs)
■

=GFT
⦏ScPrec_tc_∈_thm⦎ =
	⊢ ∀ x y⦁ ScPrec x y ⇒ tc $∈⋎g x y

⦏well_founded_ScPrec_thm⦎ =
	⊢ well_founded ScPrec
=TEX

\ignore{
=SML
local val _ = set_goal([], ⌜∀x y⦁ ScPrec x y ⇒ tc $∈⋎g x y⌝);
val _ = a (rewrite_tac (map get_spec [⌜ScPrec⌝, ⌜MkCf⌝]));
val _ = a (REPEAT strip_tac THEN asm_rewrite_tac [↦_tc_thm]);
val _ = a (lemma_tac ⌜tc $∈⋎g fs (ord ↦⋎g fs) ∧ tc $∈⋎g (ord ↦⋎g fs) (Nat⋎g 1 ↦⋎g ord ↦⋎g fs)⌝
	THEN1 rewrite_tac [↦_tc_thm]);
val _ = a (all_fc_tac [tc_incr_thm]);
val _ = a (all_fc_tac [tran_tc_thm2]);
val _ = a (all_fc_tac [tran_tc_thm2]);
in val ScPrec_tc_∈_thm = pop_thm();
end;

local val _ = set_goal ([], ⌜well_founded ScPrec⌝);
val _ = a (rewrite_tac [get_spec ⌜well_founded⌝]);
val _ = a (REPEAT strip_tac);
val _ = a (asm_tac (∀_elim ⌜s⌝ gs_cv_ind_thm));
val _ = a (lemma_tac ⌜∀ x⦁ (∀ y⦁ tc $∈⋎g y x ⇒ s y) ⇒ s x⌝
	THEN1 REPEAT strip_tac);
(* *** Goal "1" *** *)
val _ = a (lemma_tac ⌜∀ y⦁ ScPrec y x ⇒ s y⌝
	THEN1 (REPEAT strip_tac THEN all_fc_tac [ScPrec_tc_∈_thm]
		THEN asm_fc_tac []));
val _ = a (asm_fc_tac[]);
(* *** Goal "2" *** *)
val _ = a (asm_fc_tac[]);
val _ = a (asm_rewrite_tac[]);
in val well_founded_ScPrec_thm =  save_pop_thm "well_founded_ScPrec_thm";
end;
=TEX
}%ignore

=GFT
⦏ScPrec2_tc_∈_thm⦎ =
	⊢ ∀ x y⦁ ScPrec2 x y ⇒ tc $∈⋎g x y

⦏well_founded_ScPrec2_thm⦎ =
	⊢ well_founded ScPrec2

⦏well_founded_tcScPrec2_thm⦎ =
	⊢ well_founded (tc ScPrec2)
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y⦁ ScPrec2 x y ⇒ tc $∈⋎g x y⌝);
val _ = a (rewrite_tac (map get_spec [⌜ScPrec2⌝, ⌜MkCf⌝]));
val _ = a (REPEAT strip_tac THEN asm_rewrite_tac [↦_tc_thm]);
val _ = a (lemma_tac ⌜tc $∈⋎g fs (ord ↦⋎g fs) ∧ tc $∈⋎g (ord ↦⋎g fs) (Nat⋎g 1 ↦⋎g ord ↦⋎g fs)⌝
	THEN1 rewrite_tac [↦_tc_thm]);
val _ = a (all_fc_tac [tc_incr_thm]);
val _ = a (all_fc_tac [tran_tc_thm2]);
val _ = a (all_fc_tac [tran_tc_thm2]);
val ScPrec2_tc_∈_thm = pop_thm();

set_goal ([], ⌜well_founded ScPrec2⌝);
val _ = a (rewrite_tac [get_spec ⌜well_founded⌝]);
val _ = a (REPEAT strip_tac);
val _ = a (asm_tac (∀_elim ⌜s⌝ gs_cv_ind_thm));
val _ = a (lemma_tac ⌜∀ x⦁ (∀ y⦁ tc $∈⋎g y x ⇒ s y) ⇒ s x⌝
	THEN1 REPEAT strip_tac);
(* *** Goal "1" *** *)
val _ = a (lemma_tac ⌜∀ y⦁ ScPrec2 y x ⇒ s y⌝
	THEN1 (REPEAT strip_tac THEN all_fc_tac [ScPrec2_tc_∈_thm]
		THEN asm_fc_tac []));
val _ = a (asm_fc_tac[]);
(* *** Goal "2" *** *)
val _ = a (asm_fc_tac[]);
val _ = a (asm_rewrite_tac[]);
val well_founded_ScPrec2_thm =  save_pop_thm "well_founded_ScPrec2_thm";

set_goal([], ⌜well_founded (tc ScPrec2)⌝);
val _ = a (asm_tac well_founded_ScPrec2_thm);
val _ = a (fc_tac [wf_tc_wf_thm]);
val well_founded_tcScPrec2_thm = save_pop_thm ("well_founded_tcScPrec2_thm");
=TEX
}%ignore

=SML
val ⦏SC2_INDUCTION_T⦎ = WFCV_INDUCTION_T well_founded_ScPrec2_thm;
val ⦏sc2_induction_tac⦎ = wfcv_induction_tac well_founded_ScPrec2_thm;
=TEX

The set Syntax gives us the syntactically well-formed phrases of our language.
It will be useful to have some predicates which incorporate well-formedness, which are defined here.

=GFT
⦏syntax_disj_thm⦎ =
   ⊢ ∀ x
     ⦁ x ∈ Syntax
         ⇒ (∃ s m⦁ x = MkAf (s, m))
           ∨ (∃ vars fs⦁ (∀ y⦁ y ∈⋎g fs ⇒ y ∈ Syntax) ∧ x = MkCf (vars, fs))

⦏syntax_cases_thm⦎ =
   ⊢ ∀ x⦁ x ∈ Syntax ⇒ IsAf x ∨ IsCf x

⦏syntax_cases_fc_clauses⦎ =
   ⊢ ∀ x⦁ x ∈ Syntax ⇒ (¬ IsAf x ⇒ IsCf x) ∧ (¬ IsCf x ⇒ IsAf x)
=TEX
=GFT
⦏is_fc_clauses⦎ =
   ⊢ ∀ x
     ⦁ x ∈ Syntax
         ⇒ (IsAf x ⇒ (∃ s m⦁ x = MkAf (s, m)))
           ∧ (IsCf x
             ⇒ (∃ vars fs
             ⦁ (∀ y⦁ y ∈⋎g fs ⇒ y ∈ Syntax) ∧ x = MkCf (vars, fs)))

⦏is_fc_clauses2⦎ =
   ⊢ ∀ x⦁ x ∈ Syntax ⇒ IsCf x ⇒ (∀ y⦁ y ∈⋎g CfForms x ⇒ y ∈ Syntax)
=TEX
=GFT
⦏¬∅⋎g_∈_syntax_lemma⦎ =
   ⊢ ¬ ∅⋎g ∈ Syntax

⦏¬∅⋎g_∈_syntax_lemma2⦎ =
   ⊢ ∀ x⦁ x ∈ Syntax ⇒ ¬ x = ∅⋎g

⦏¬∅⋎g_∈_syntax_lemma3⦎ =
   ⊢ ∀ V x⦁ x ∈ V ∧ V ⊆ Syntax ⇒ ¬ x = ∅⋎g

⦏MkAf_MkCf_¬_∅⋎g_lemma⦎ =
   ⊢ ∀ x y⦁ ¬ MkAf (x, y) = ∅⋎g ∧ ¬ MkCf (x, y) = ∅⋎g

⦏syn_comp_fc_clauses⦎ =
   ⊢ ∀ v f⦁ MkCf (v, f) ∈ Syntax ⇒ (∀ y⦁ y ∈⋎g f ⇒ y ∈ Syntax)

⦏scprec_fc_clauses⦎ =
   ⊢ ∀ α γ vars fs⦁ γ ∈ Syntax ⇒ γ = MkCf (vars, fs) ∧ α ∈⋎g fs ⇒ ScPrec α γ

⦏scprec2_fc_clauses⦎ =
   ⊢ ∀ α γ vars fs⦁ γ = MkCf (vars, fs) ∧ α ∈⋎g fs ⇒ ScPrec2 α γ

⦏scprec_fc_clauses2⦎ =
   ⊢ ∀ t⦁ t ∈ Syntax ⇒ IsCf t ⇒ (∀ f⦁ f ∈⋎g CfForms t ⇒ ScPrec f t)

⦏scprec2_fc_clauses2⦎ =
   ⊢ ∀ t⦁ IsCf t ⇒ (∀ f⦁ f ∈⋎g CfForms t ⇒ ScPrec2 f t)

⦏MkAf_∈_Syntax_lemma⦎ =
   ⊢ ∀ x y⦁ MkAf (x, y) ∈ Syntax
=TEX

\ignore{
=SML
local val _ = set_goal([], ⌜∀x⦁	x ∈ Syntax
⇒	(∃s m⦁ x = MkAf (s, m))
  ∨	(∃vars fs⦁ (∀y⦁ y ∈⋎g fs ⇒ y ∈ Syntax) ∧ x = MkCf (vars, fs))
⌝);
val _ = a (contr_tac);
val _ = a (lemma_tac ⌜RepClosed (Syntax \ {x})⌝
	THEN1 (rewrite_tac [get_spec ⌜RepClosed⌝]
		THEN strip_tac));
(* *** Goal "1" *** *)
val _ = a (strip_tac THEN strip_tac
	THEN rewrite_tac [repclosed_syntax_thm]);
val _ = a (spec_nth_asm_tac 2 ⌜s2⌝);
val _ = a (spec_nth_asm_tac 1 ⌜m⌝);
val _ = a (swap_nth_asm_concl_tac 1 THEN (SYM_ASMS_T rewrite_tac));
(* *** Goal "2" *** *)
val _ = a (REPEAT_N 3 strip_tac);
val _ = a (spec_nth_asm_tac 2 ⌜vars⌝);
val _ = a (DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac [get_spec ⌜X⋎g⌝]
	THEN strip_tac);
val _ = a (lemma_tac ⌜∀ y⦁ y ∈⋎g fs ⇒ y ∈ Syntax⌝
	THEN1 (REPEAT strip_tac THEN all_asm_fc_tac[]));
val _ = a (all_fc_tac [rewrite_rule [get_spec ⌜X⋎g⌝] repclosed_syntax_thm]);
val _ = a (asm_rewrite_tac[]);
val _ = a (spec_nth_asm_tac 4 ⌜fs⌝);
(* *** Goal "2.1" *** *)
val _ = a (asm_fc_tac[]);
(* *** Goal "2.2" *** *)
val _ = a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
val _ = a (asm_tac repclosed_syntax_lemma1);
val _ = a (spec_nth_asm_tac 1 ⌜Syntax \ {x}⌝);
val _ = a (spec_nth_asm_tac 1 ⌜x⌝);
in val syntax_disj_thm = save_pop_thm "syntax_disj_thm";
end;

local val _ = set_goal([], ⌜∀x⦁ x ∈ Syntax ⇒ IsAf x ∨ IsCf x⌝);
val _ = a (REPEAT_N 2 strip_tac THEN fc_tac [syntax_disj_thm]
	THEN asm_rewrite_tac[]);
in val syntax_cases_thm = save_pop_thm "syntax_cases_thm";
end;

set_goal ([], ⌜∀x⦁ x ∈ Syntax ⇒
	(¬ IsAf x ⇒ IsCf x)
∧	(¬ IsCf x ⇒ IsAf x)⌝);
a (strip_tac THEN strip_tac
	THEN FC_T (MAP_EVERY ante_tac) [syntax_cases_thm]
	THEN (rewrite_tac (map get_spec [⌜IsAf⌝, ⌜IsCf⌝])));
a (REPEAT strip_tac THEN asm_fc_tac[]);
a (∃_tac ⌜lr⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜vc⌝ THEN asm_rewrite_tac[]);
val syntax_cases_fc_clauses = save_pop_thm "syntax_cases_fc_clauses";

local val _ = set_goal([], ⌜∀x⦁	x ∈ Syntax
⇒	(IsAf x ⇒ ∃s m⦁ x = MkAf (s, m))
∧	(IsCf x ⇒ ∃vars fs⦁ (∀y⦁ y ∈⋎g fs ⇒ y ∈ Syntax) ∧ x = MkCf (vars, fs))
⌝);
val _ = a (REPEAT_N 2 strip_tac);
val _ = a (asm_tac (syntax_disj_thm));
val _ = a (asm_fc_tac[] THEN asm_rewrite_tac [Is_clauses]);
(* *** Goal "1" *** *)
val _ = a (∃_tac ⌜s⌝ THEN ∃_tac ⌜m⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
val _ = a (∃_tac ⌜vars⌝ THEN ∃_tac ⌜fs⌝ THEN asm_rewrite_tac[]);
in val is_fc_clauses = save_pop_thm "is_fc_clauses";
end;

set_goal([], ⌜∀x y⦁ MkAf (x,y) ∈ Syntax⌝);
a (rewrite_tac [get_spec ⌜Syntax⌝, sets_ext_clauses, ∈_in_clauses, get_spec ⌜RepClosed⌝]
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[]);
val MkAf_∈_Syntax_lemma = save_pop_thm "MkAf_∈_Syntax_lemma";

set_goal([], ⌜¬ ∅⋎g ∈ Syntax⌝);
a (LEMMA_T ⌜∀x⦁ x ∈ Syntax ⇒ ¬ x = ∅⋎g⌝ (fn x => contr_tac THEN fc_tac [x])
	THEN strip_tac);
a (sc2_induction_tac ⌜x⌝ THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜t⌝ syntax_cases_thm)
	THEN (fc_tac [is_fc_clauses]));
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜MkAf⌝]
	THEN strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜MkAf⌝]
	THEN strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (POP_ASM_T discard_tac THEN POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜MkCf⌝]
	THEN strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜MkAf⌝]
	THEN strip_tac THEN asm_rewrite_tac[]);
val ¬∅⋎g_∈_syntax_lemma = save_pop_thm "¬∅⋎g_∈_syntax_lemma";

set_goal([], ⌜∀x⦁ x ∈ Syntax ⇒ ¬ x = ∅⋎g⌝);
a (contr_tac THEN var_elim_nth_asm_tac 1
	THEN POP_ASM_T ante_tac
	THEN rewrite_tac [¬∅⋎g_∈_syntax_lemma]);
val ¬∅⋎g_∈_syntax_lemma2 = save_pop_thm "¬∅⋎g_∈_syntax_lemma2";
 
set_goal([], ⌜∀V x⦁ x ∈ V ∧ V ⊆ Syntax ⇒ ¬ x = ∅⋎g⌝);
a (REPEAT strip_tac
	THEN lemma_tac ⌜x ∈ Syntax⌝ THEN1 PC_T1 "hol1" asm_prove_tac[]
	THEN fc_tac [¬∅⋎g_∈_syntax_lemma2]);
val ¬∅⋎g_∈_syntax_lemma3 = save_pop_thm "¬∅⋎g_∈_syntax_lemma3";

set_goal([], ⌜∀x y⦁ ¬ MkAf (x, y) = ∅⋎g ∧ ¬ MkCf (x, y) = ∅⋎g⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜MkAf⌝, get_spec ⌜MkCf⌝]);
val MkAf_MkCf_¬_∅⋎g_lemma = pop_thm();

add_pc_thms "'infos" [syn_proj_clauses, ¬∅⋎g_∈_syntax_lemma, MkAf_∈_Syntax_lemma, MkAf_MkCf_¬_∅⋎g_lemma];
set_merge_pcs ["misc21", "'infos"];

local val _ = set_goal([], ⌜∀x⦁ x ∈ Syntax
	⇒ (IsCf x ⇒ (∀y⦁ y ∈⋎g (CfForms x) ⇒ y ∈ Syntax))
⌝);
val _ = a (REPEAT strip_tac
	THEN all_fc_tac [is_fc_clauses]
	THEN GET_NTH_ASM_T 1 (var_elim_asm_tac o concl)
	THEN_TRY asm_rewrite_tac[]);
val _ = a (DROP_NTH_ASM_T 2 (asm_tac o (rewrite_rule[]))
	THEN all_asm_fc_tac[]);
in val is_fc_clauses2 = save_pop_thm "is_fc_clauses2";
end;

local val _ = set_goal([], ⌜
	(∀v f⦁ MkCf (v, f) ∈ Syntax ⇒ (∀y⦁ y ∈⋎g f ⇒ y ∈ Syntax))⌝);
val _ = a (REPEAT strip_tac
	THEN FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule []))) [is_fc_clauses2]
	THEN asm_fc_tac[]);
in val syn_comp_fc_clauses = save_pop_thm "syn_comp_fc_clauses";
end;

local val _ = set_goal([], ⌜∀α γ vars fs⦁ γ ∈ Syntax ⇒
		(γ = MkCf (vars, fs) ∧ α ∈⋎g fs) ⇒ ScPrec α γ
⌝);
val _ = a (rewrite_tac [get_spec ⌜ScPrec⌝]);
val _ = a (REPEAT ∀_tac THEN strip_tac THEN strip_tac);
val _ = a (∃_tac ⌜vars⌝ THEN ∃_tac ⌜fs⌝ THEN asm_rewrite_tac[]);
val _ = a (REPEAT strip_tac THEN var_elim_nth_asm_tac 1);
(* *** Goal "1" *** *)
val _ = a (var_elim_nth_asm_tac 2);
val _ = a (fc_tac [syn_comp_fc_clauses]);
val _ = a (asm_fc_tac[]);
(* *** Goal "2" *** *)
val _ = a (var_elim_nth_asm_tac 2);
in val scprec_fc_clauses = save_pop_thm "scprec_fc_clauses";
end;

set_goal([], ⌜∀α γ vars fs⦁ γ = MkCf (vars, fs) ∧ α ∈⋎g fs ⇒ ScPrec2 α γ
⌝);
val _ = a (rewrite_tac [get_spec ⌜ScPrec2⌝]);
val _ = a (REPEAT ∀_tac THEN strip_tac);
val _ = a (∃_tac ⌜vars⌝ THEN ∃_tac ⌜fs⌝ THEN asm_rewrite_tac[]);
val scprec2_fc_clauses = save_pop_thm "scprec2_fc_clauses";

local val _ = set_goal ([], ⌜∀t⦁ t ∈ Syntax ⇒ 
	(IsCf t ⇒ ∀f⦁ f ∈⋎g CfForms t ⇒ ScPrec (f) t)⌝);
val _ = a (REPEAT strip_tac
	THEN all_fc_tac [is_fc_clauses]
	THEN DROP_NTH_ASM_T 3 ante_tac
	THEN asm_rewrite_tac[]
	THEN strip_tac
	THEN all_fc_tac [scprec_fc_clauses]
	THEN POP_ASM_T ante_tac
	THEN_TRY asm_rewrite_tac []);
in val scprec_fc_clauses2 = save_pop_thm "scprec_fc_clauses2";
end;

set_goal ([], ⌜∀t⦁ IsCf t ⇒ ∀f⦁ f ∈⋎g CfForms t ⇒ ScPrec2 f t⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜ScPrec2⌝]);
a (∃_tac ⌜CfVars t⌝ THEN ∃_tac ⌜CfForms t⌝ THEN asm_rewrite_tac[]);
a (ALL_FC_T rewrite_tac [syn_con_inv_fc_clauses]);
val scprec2_fc_clauses2 = save_pop_thm "scprec2_fc_clauses2";
=TEX
}%ignore

Inductive proofs using the well-foundedness of ScPrec are fiddly.
The following induction principle simplifies the proofs.

=GFT
⦏syn_induction_thm⦎ =
   ⊢ ∀ p
     ⦁ (∀ x y⦁ p (MkAf (x, y)))
	∧ (∀ vars fs⦁ (∀f⦁ f ∈⋎g fs ⇒ f ∈ Syntax)
		∧ (∀f⦁ f ∈⋎g fs ⇒ p f) ⇒ p (MkCf (vars, fs)))
         ⇒ (∀ x⦁ x ∈ Syntax ⇒ p x)
=TEX

\ignore{
=SML
set_goal([], ⌜∀p⦁ (∀x y⦁ p (MkAf (x,y)))
	∧ (∀vars fs⦁ (∀f⦁ f ∈⋎g fs ⇒ f ∈ Syntax) ∧ (∀f⦁ f ∈⋎g fs ⇒ p f) ⇒ p (MkCf (vars, fs)))
	⇒ ∀x⦁ x ∈ Syntax ⇒ p x⌝);
a (REPEAT strip_tac);
a (POP_ASM_T ante_tac THEN sc2_induction_tac ⌜x⌝ THEN strip_tac);
a (fc_tac [syntax_cases_thm] THEN fc_tac [is_fc_clauses] THEN asm_rewrite_tac[]);
a (list_spec_nth_asm_tac 7 [⌜vars⌝, ⌜fs⌝] THEN asm_fc_tac[]);
a (lemma_tac ⌜tc ScPrec2 f t⌝ THEN_LIST [bc_tac [tc_incr_thm], all_asm_fc_tac []]);
a (all_fc_tac [scprec2_fc_clauses]);
val syn_induction_thm = save_pop_thm "syn_induction_thm";
=TEX
}%ignore

Using this induction principle an induction tactic is defined as follows:

=SML
fun ⦏infos_induction_tac⦎ t (a,c) = (
	let val l1 = mk_app (mk_λ (t,c), t)
	    and l2 = mk_app (mk_app (mk_const ("∈", ⓣGS → GS SET → BOOL⌝), t),
					mk_const ("Syntax", ⓣGS SET⌝))
	in  let val l3 = mk_∀ (t, mk_⇒ (l2, l1))
	in  LEMMA_T l1 (rewrite_thm_tac o rewrite_rule[])
	THEN DROP_ASM_T l2 ante_tac
	THEN LEMMA_T l3 (rewrite_thm_tac o rewrite_rule[])
	THEN bc_tac [syn_induction_thm]
	THEN rewrite_tac[]
	THEN strip_tac
	end end) (a,c);
=TEX

This tactic expects an argument $t$ of type $TERM$ which is a free variable of type $GS$ whose sole occurrence in the assumptions is in an assumption ⌜ⓜt⌝ ∈ Syntax⌝, and results in two subgoals, one requiring a proof for atomic and the other for compound formulae (with the benefit of the induction hypothesis in the assumptions).

\subsection{Recursion Theorem}\label{Recursion}

The following recursion theorem supports definition by primitive recursion of functions over the syntax.
This version does require (or allow) stipulation of a value for elements which are not part of the syntax (which is sometimes necessary).
The function defined is total over the type GS, but its value is only known for members of {\it Syntax}.

=GFT
⦏sc_recursion_lemma⦎ =
   ⊢ ∀ af cf
     ⦁ ∃ f
       ⦁ (∀ m s⦁ f (MkAf (m, s)) = af m s)
           ∧ (∀ vars forms
           ⦁ f (MkCf (vars, forms)) = cf (FunImage⋎g f forms) vars forms)
=TEX

\ignore{
=SML
set_goal([], ⌜∀af cf⦁ ∃f⦁ (∀m s⦁ f (MkAf (m, s)) = af m s)
	∧ (∀vars forms⦁ f (MkCf (vars, forms)) = cf (FunImage⋎g f forms) vars forms)⌝);
val _ = a (REPEAT strip_tac);
val _ = a (lemma_tac ⌜∃g⦁ g = λf x⦁
		if (∃vars forms⦁ x = MkCf(vars,forms)) then cf (FunImage⋎g f (CfForms x)) (CfVars x) (CfForms x)
		else af (AfMem x) (AfSet x)⌝
	THEN1 prove_∃_tac);
val _ = a (lemma_tac ⌜g respects ScPrec2⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜$respects⌝] THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (cond_cases_tac ⌜∃ vars forms⦁ x = MkCf (vars, forms)⌝);
a (asm_rewrite_tac[get_spec ⌜FunImage⋎g⌝]);
a (LEMMA_T ⌜{x'|∃ y⦁ y ∈⋎g forms ∧ x' = g' y}
             = {x'|∃ y⦁ y ∈⋎g forms ∧ x' = h y}⌝ rewrite_thm_tac
	THEN1 (rewrite_tac [sets_ext_clauses, ∈_in_clauses]
		THEN REPEAT strip_tac));
(* *** Goal "1.1" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
a (lemma_tac ⌜ScPrec2 y x⌝
	THEN1 rewrite_tac [get_spec ⌜ScPrec2⌝]);
(* *** Goal "1.1.1" *** *)
a (∃_tac ⌜vars⌝ THEN ∃_tac ⌜forms⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.1.2" *** *)
a (fc_tac[tc_incr_thm] THEN asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
a (lemma_tac ⌜ScPrec2 y x⌝
	THEN1 rewrite_tac [get_spec ⌜ScPrec2⌝]);
(* *** Goal "1.2.1" *** *)
a (∃_tac ⌜vars⌝ THEN ∃_tac ⌜forms⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2.2" *** *)
a (fc_tac[tc_incr_thm] THEN asm_fc_tac[] THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜fix g⌝);
a (asm_tac well_founded_ScPrec2_thm);
a (all_fc_tac [get_spec ⌜fix⌝]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[] THEN strip_tac);
a (SYM_ASMS_T rewrite_tac THEN REPEAT ∀_tac);
a (LEMMA_T ⌜∃ vars' forms'⦁ vars = vars' ∧ forms = forms'⌝ rewrite_thm_tac);
a (∃_tac ⌜vars⌝ THEN ∃_tac ⌜forms⌝ THEN rewrite_tac[]);
val sc_recursion_lemma = save_pop_thm "sc_recursion_lemma";
=TEX
}%ignore

This gets plugged into proof context {\it 'infos} for use in consistency proofs.

=SML
add_∃_cd_thms [sc_recursion_lemma] "'infos";
set_merge_pcs ["misc21", "'infos"];
=TEX

Definitions of the form supported by the above recursion lemma do not allow sufficient control over the value of a function when applied outside the range of the syntactic constructors.
The following version (if it works) is suitable for cases where this level of control is necessary.

=GFT
⦏sc_recursion_lemma2⦎ =
   ⊢ ∀ af cf ov
     ⦁ ∃ f
       ⦁ (∀ m s⦁ f (MkAf (m, s)) = af m s)
           ∧ (∀ vars forms
           ⦁ f (MkCf (vars, forms)) = cf (FunImage⋎g f forms) vars forms)
           ∧ (∀ x⦁ ¬ IsAf x ∧ ¬ IsCf x ⇒ f x = ov x)
=TEX

\ignore{
=SML
set_goal([], ⌜∀af cf ov⦁ ∃f⦁ (∀m s⦁ f (MkAf (m, s)) = af m s)
	∧ (∀vars forms⦁ f (MkCf (vars, forms)) = cf (FunImage⋎g f forms) vars forms)
	∧ (∀x⦁ (¬ IsAf x ∧ ¬ IsCf x) ⇒ f x = ov x)
⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜∃g⦁ g = λf x⦁
		if (∃vars forms⦁ x = MkCf(vars,forms)) then cf (FunImage⋎g f (CfForms x)) (CfVars x) (CfForms x)
		else if ∃m s⦁ x = MkAf (m, s) then af (AfMem x) (AfSet x) else ov x⌝
	THEN1 prove_∃_tac);
a (lemma_tac ⌜g respects ScPrec2⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜$respects⌝] THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (cond_cases_tac ⌜∃ vars forms⦁ x = MkCf (vars, forms)⌝);
a (asm_rewrite_tac[get_spec ⌜FunImage⋎g⌝]);
a (LEMMA_T ⌜{x'|∃ y⦁ y ∈⋎g forms ∧ x' = g' y}
             = {x'|∃ y⦁ y ∈⋎g forms ∧ x' = h y}⌝ rewrite_thm_tac
	THEN1 (rewrite_tac [sets_ext_clauses, ∈_in_clauses]
		THEN REPEAT strip_tac));
(* *** Goal "1.1" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
a (lemma_tac ⌜ScPrec2 y x⌝
	THEN1 rewrite_tac [get_spec ⌜ScPrec2⌝]);
(* *** Goal "1.1.1" *** *)
a (∃_tac ⌜vars⌝ THEN ∃_tac ⌜forms⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.1.2" *** *)
a (fc_tac[tc_incr_thm] THEN asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
a (lemma_tac ⌜ScPrec2 y x⌝
	THEN1 rewrite_tac [get_spec ⌜ScPrec2⌝]);
(* *** Goal "1.2.1" *** *)
a (∃_tac ⌜vars⌝ THEN ∃_tac ⌜forms⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2.2" *** *)
a (fc_tac[tc_incr_thm] THEN asm_fc_tac[] THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜fix g⌝);
a (asm_tac well_founded_ScPrec2_thm);
a (all_fc_tac [get_spec ⌜fix⌝]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[] THEN strip_tac);
a (SYM_ASMS_T rewrite_tac THEN REPEAT ∧_tac THEN REPEAT ∀_tac);
(* *** Goal "2.1" *** *)
a (LEMMA_T ⌜∃m' s'⦁ m = m' ∧ s = s'⌝ rewrite_thm_tac
	THEN1 prove_∃_tac);
(* *** Goal "2.2" *** *)
a (LEMMA_T ⌜∃ vars' forms'⦁ vars = vars' ∧ forms = forms'⌝ rewrite_thm_tac
	THEN1 prove_∃_tac);
(* *** Goal "2.3" *** *)
a (strip_tac);
a (LEMMA_T ⌜¬ ∃ vars forms⦁ x = MkCf (vars, forms)⌝ rewrite_thm_tac);
(* *** Goal "2.3.1" *** *)
a (contr_tac);
a (swap_nth_asm_concl_tac 2 THEN asm_rewrite_tac[]);
(* *** Goal "2.3.2" *** *)
a (LEMMA_T ⌜¬ ∃ m s⦁ x = MkAf (m, s)⌝ rewrite_thm_tac);
a (swap_nth_asm_concl_tac 2 THEN asm_rewrite_tac[]);
val sc_recursion_lemma2 = pop_thm ();
=TEX
}%ignore


ⓈHOLCONST
│ ⦏MkTrash⦎ : GS → GS
├───────────
│ ∀x⦁ MkTrash x = if IsAf x ∨ IsCf x then ∅⋎g else x
■

=GFT
⦏sc_recursion_lemma3⦎ =
   ⊢ ∀ af cf ov
     ⦁ ∃ f
       ⦁ (∀ m s⦁ f (MkAf (m, s)) = af m s)
           ∧ (∀ vars forms
           ⦁ f (MkCf (vars, forms)) = cf (FunImage⋎g f forms) vars forms)
           ∧ (∀ x⦁ f (MkTrash x) = ov (MkTrash x))
=TEX

\ignore{
=SML
set_goal([], ⌜∀af cf ov⦁ ∃f⦁ (∀m s⦁ f (MkAf (m, s)) = af m s)
	∧ (∀vars forms⦁ f (MkCf (vars, forms)) = cf (FunImage⋎g f forms) vars forms)
	∧ (∀x⦁ f (MkTrash x) = ov (MkTrash x))
⌝);
a (REPEAT strip_tac);
a (rewrite_tac [get_spec ⌜MkTrash⌝]);
a ((strip_asm_tac o (rewrite_rule [])) (list_∀_elim [⌜af⌝, ⌜cf⌝, ⌜λz⦁ if IsAf z ∨ IsCf z then ov ∅⋎g else ov z⌝] sc_recursion_lemma2));
a (∃_tac ⌜f⌝ THEN asm_rewrite_tac []);
a (strip_tac);
a (cond_cases_tac ⌜¬ IsAf x ∧ ¬ IsCf x⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (ALL_ASM_FC_T asm_rewrite_tac []);
(* *** Goal "2" *** *);
a (spec_nth_asm_tac 2 ⌜∅⋎g⌝ THEN fc_tac [syn_con_inv_fc_clauses]);
a (asm_rewrite_tac []);
a (cond_cases_tac ⌜IsAf ∅⋎g ∨ IsCf ∅⋎g⌝);
(* *** Goal "3" *** *)
a (spec_nth_asm_tac 2 ⌜∅⋎g⌝ THEN fc_tac [syn_con_inv_fc_clauses]);
a (asm_rewrite_tac []);
a (cond_cases_tac ⌜IsAf ∅⋎g ∨ IsCf ∅⋎g⌝);
val sc_recursion_lemma3 = save_pop_thm "sc_recursion_lemma3";
=TEX
}%ignore

This also gets plugged into proof context {\it 'infos} for use in consistency proofs.

=SML
add_∃_cd_thms [sc_recursion_lemma3] "'infos";
set_merge_pcs ["misc21", "'infos"];
=TEX

\subsection{Auxiliary Concepts}

Its useful to be able to talk about the free variables in a formula so the definition is given here.

The definition is by recursion over the structure of the syntax.

ⓈHOLCONST
│ ⦏FreeVars⦎ : GS → GS SET
├───────────
│ (∀x y⦁
│	FreeVars (MkAf (x, y)) = {x; y})
│∧ (∀vars forms⦁
│	FreeVars (MkCf (vars, forms)) = ⋃ (FunImage⋎g FreeVars forms) \ (X⋎g vars))
■

The name {\it SetReps} is defined as the set of formulae with exactly one free variable which is the empty set.
These are the candidate representatives for sets, and represent the set coextensive with the property expressed by the formula.
To know what set that is you need to know the domain of discourse (which in the cases of interest here will always be a subset of {\it SetReps}) and the semantics of formulae, which is defined below.

ⓈHOLCONST
│ ⦏SetReps⦎ : GS SET
├───────────
│ SetReps = {x | x ∈ Syntax ∧ ∃y⦁ FreeVars x = {y}}
■

=GFT
⦏setreps_⊆_syntax_lemma⦎ =
	⊢ SetReps ⊆ Syntax

⦏setreps_⊆_syntax_lemma2⦎ =
	⊢ V ⊆ SetReps ⇒ V ⊆ Syntax
=TEX

\ignore{
=SML
set_goal ([], ⌜SetReps ⊆ Syntax⌝);
a (PC_T1 "hol1" prove_tac [get_spec ⌜SetReps⌝]);
val setreps_⊆_syntax_lemma = save_pop_thm "setreps_⊆_syntax_lemma";

set_goal ([], ⌜V ⊆ SetReps ⇒ V ⊆ Syntax⌝);
a (PC_T1 "hol1" prove_tac [get_spec ⌜SetReps⌝]);
val setreps_⊆_syntax_lemma2 = save_pop_thm "setreps_⊆_syntax_lemma2";

set_goal ([], ⌜¬ ∅⋎g ∈ SetReps⌝);
a (ante_tac setreps_⊆_syntax_lemma);
a (rewrite_tac [sets_ext_clauses]
	THEN contr_tac THEN asm_fc_tac[]);
val ¬∅⋎g_∈_setreps_lemma = save_pop_thm "¬∅⋎g_∈_setreps_lemma";

add_pc_thms "'infos" [¬∅⋎g_∈_setreps_lemma];
set_merge_pcs ["misc21", "'infos"];
=TEX
}%ignore


\section{SEMANTICS}

The semantics of infinitary first order logic is given by defining ``truth in an interpretation''.

\subsection{Type Abbreviations}

We consider here some of the value domains which are significant in the semantics.

The following type abbreviations are introduced:

\begin{description}
\item{RV}
Relation Value - this is the type for the meaning of a formula with free variables.
The parameters are the type of the domain of discourse and the type of truth values.
\item{ST}
Structure = a structure is a domain of discourse (a set) together with a binary relation (the membership relation) over that domain.
The membership relation need not (and will not) be boolean.
The parameters are the type of the domain of discourse and the type of truth values.
\end{description}

=SML
declare_infix(300, "∈⋎v");
declare_type_abbrev("⦏RV⦎", ["'a","'b"], ⓣ(GS, 'a)IX → 'b⌝);
declare_type_abbrev("⦏ST⦎", ["'a","'b"], ⓣ'a SET × ('a, 'b)BR⌝);
=TEX

\subsection{Formula Evaluation}

Now we define the evaluation of formulae, i.e. the notion of truth in a structure given a variable assignment.

There are two cases in the syntax, atomic and compound formulae.

The truth values of the atomic formulae (which are all membership claims) are obtained from a structure given the values of the arguments, which are always variables, i.e. to evaluate an atomic formula you look up the values of the arguments in the current context (variable assignment) and then look up the truth value of the membership relation for those arguments in the structure.
Note that this specification is generic in the type of truth values.

ⓈHOLCONST
│ ⦏EvalAf⦎ : 't REL → GS → ('a, 't) ST → ('a, 't) RV
├───────────
│ ∀$≤⋎t (at:GS) (st:('a, 't) ST) (va:(GS, 'a)IX)⦁ EvalAf $≤⋎t at st va =
│	let d = Fst st
│	and rv = Snd st
│	and set = AfSet at
│	and mem = AfMem at
│	in	if mem ∈ IxDom va ∧ set ∈ IxDom va
│		then rv (IxVal va mem) (IxVal va set)
│		else Lub $≤⋎t {}
■

=GFT
⦏EvalAf_MkAf_lemma⦎ =
   ⊢ ∀ ≤⋎t mem set st va
     ⦁ EvalAf ≤⋎t (MkAf (set, mem)) st va
         = (if mem ∈ IxDom va ∧ set ∈ IxDom va
           then Snd st (IxVal va mem) (IxVal va set)
           else Lub ≤⋎t {})
=TEX

\ignore{
=SML
set_goal([], ⌜∀$≤⋎t mem set st va⦁ EvalAf $≤⋎t (MkAf (set, mem)) st va =
	if set ∈ IxDom va ∧ mem ∈ IxDom va
		then Snd st (IxVal va set) (IxVal va mem)
		else Lub $≤⋎t {}⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜EvalAf⌝, let_def]);
val EvalAf_MkAf_lemma = pop_thm ();
=TEX
}%ignore

To evaluate a compound formula you must first evaluate the constituent formulae in every context obtainable by modification of those variables which are bound by the compound formula.
You need only remember the resulting truth values, the compound formulae are in this sense ``truth functional'', and, though this may involve evaluating a very large number of instances of subformulae, it can only yield some subset of the available truth values.

The definition of the truth function depends upon the type of truth values, and is therefore a parameter of the semantics.

The relevant definitions for three and four valued truth types are given here.

=SML
declare_type_abbrev(⦏"CFE"⦎, ["'t"], ⓣ't SET → 't⌝);
=TEX

This function is the core of the semantics of the logic, and captures the truth functional character of first order logic, including the quantifiers even in the infinitary case.
It should be remembered that though I am working here with four truth values, the logic we are formalising is a classical two valued first order logic.
The extra truth values are included to facilitate the discovery of interpretations by making the semantics monotonic and taking least and/or greatest fixed points.

To make this clear I am defining the semantics as a two valued function first so that you can see the intended semantics without the clutter of the extra truth values.
The semantics is for a single compound formula constructor which takes a set of formulae and a set of variables and yields the negation of the (infinitary) conjunction of all the instances of the formulae for every possible valuation of the bound variables.
This function expects the results of evaluating these formulae as a set of truth values, and returns the truth value of the compound formula.

ⓈHOLCONST
│ ⦏EvalCf_bool⦎ : BOOL SET → BOOL
├───────────
│ ∀results⦁ EvalCf_bool results = F ∈ results
■

That looks unbelievably simple doesn't it.

When we generalise this to operate with four truth values, you should think of the truth values as sets of boolean truth values ordered by inclusion, i.e. with the empty set as ``bottom'' and the set of both truth values as ``top''.
Then think of the required evaluation function as arising by mapping the boolean evaluator (\emph{EvalCf\_bool}) over the set of choice sets formed from the set of sets of booleans.

ⓈHOLCONST
│ ⦏LiftEvalCf_bool⦎ : BOOL SET SET → BOOL SET
├───────────
│ ∀results⦁ LiftEvalCf_bool results =
│	{v:BOOL | ∃w f⦁ w = FunImage f results ∧ v = EvalCf_bool w
│		∧ ∀x⦁ x ∈ results ∧ (∃y⦁ y ∈ x) ⇒ (f x) ∈ x}
■

To get the required evaluator we need to modify this to work with type FTV instead of BOOL SET%
\footnote{I ask myself ``Why isn't FTV just BOOL SET?''}.

The conversions are:

ⓈHOLCONST
│ ⦏BoolSet2FTV⦎ : BOOL SET → FTV
├───────────
│ ∀bs⦁ BoolSet2FTV bs =
│	if T ∈ bs
│	then if F ∈ bs then fT else fTrue
│	else if F ∈ bs then fFalse else fB
■

ⓈHOLCONST
│ ⦏FTV2BoolSet⦎ : FTV → BOOL SET
├───────────
│ ∀ftv⦁ FTV2BoolSet ftv =
	{x | (x = T ∧ fTrue ≤⋎t⋎4 ftv) ∨ (x = F ∧ fFalse ≤⋎t⋎4 ftv )}
■

ⓈHOLCONST
│ ⦏EvalCf2_ftv⦎ : FTV CFE
├───────────
│ ∀results⦁ EvalCf2_ftv results =
│	BoolSet2FTV (LiftEvalCf_bool (FunImage FTV2BoolSet results))
■

Deriving the result by that means looked like it would be a bit complicated so here's my guess what the result should be:

ⓈHOLCONST
│ ⦏EvalCf_ftv⦎ : FTV CFE
├───────────
│ ∀results⦁ EvalCf_ftv results =  Lub $≤⋎t⋎4 {t | 
│		(fFalse ∈ results ∨ fT ∈  results) ∧ t = fTrue
│		∨
│		(¬ fFalse ∈ results ∧ ¬ fB ∈ results) ∧ t = fFalse
│		}
■

=GFT
⦏evalcf_ftv_lemma⦎ =
   ⊢ ∀ s
     ⦁ EvalCf_ftv s
         = (if fFalse ∈ s ∨ fT ∈ s
           then if ¬ fFalse ∈ s ∧ ¬ fB ∈ s then fT else fTrue
           else if ¬ fFalse ∈ s ∧ ¬ fB ∈ s
           then fFalse
           else fB)

⦏evalcf_ftv_ft_lemma⦎ =
   ⊢ ∀ s⦁ EvalCf_ftv s = fT ⇔ ¬ fFalse ∈ s ∧ fT ∈ s ∧ ¬ fB ∈ s

⦏evalcf_ftv_ft_lemma1⦎ =
   ⊢ ∀ s⦁ EvalCf_ftv s = fT ⇒ ¬ fFalse ∈ s ∧ fT ∈ s ∧ ¬ fB ∈ s

⦏evalcf_ftv_fb_lemma⦎ =
   ⊢ ∀ s⦁ EvalCf_ftv s = fB ⇔ ¬ fFalse ∈ s ∧ ¬ fT ∈ s ∧ fB ∈ s

⦏evalcf_ftv_fb_lemma1⦎ =
   ⊢ ∀ s⦁ EvalCf_ftv s = fB ⇒ ¬ fFalse ∈ s ∧ ¬ fT ∈ s ∧ fB ∈ s
=TEX

\ignore{
=SML
push_merge_pcs ["misc2", "'infos"];

set_goal([], ⌜∀s⦁ EvalCf_ftv s = if fFalse ∈ s ∨ fT ∈ s
               then if ¬ fFalse ∈ s ∧ ¬ fB ∈ s then fT else fTrue
               else if ¬ fFalse ∈ s ∧ ¬ fB ∈ s
               then fFalse
               else fB⌝);
a (rewrite_tac [get_spec ⌜EvalCf_ftv⌝, ≤⋎t⋎4_lub_thm]);
val evalcf_ftv_lemma = save_pop_thm "evalcf_ftv_lemma";

set_goal([], ⌜∀s⦁ EvalCf_ftv s = fT ⇔ ¬ fFalse ∈ s ∧ fT ∈ s ∧ ¬ fB ∈ s⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜EvalCf_ftv⌝, ≤⋎t⋎4_lub_thm]);
a (cases_tac ⌜fFalse ∈ s⌝ THEN_TRY asm_rewrite_tac[]);
a (cases_tac ⌜fT ∈ s⌝ THEN cases_tac ⌜fB ∈ s⌝ THEN_TRY asm_rewrite_tac[]);
val evalcf_ftv_ft_lemma = save_pop_thm "evalcf_ftv_ft_lemma";

set_goal([], ⌜∀s⦁ EvalCf_ftv s = fT ⇒ ¬ fFalse ∈ s ∧ fT ∈ s ∧ ¬ fB ∈ s⌝);
a (∀_tac THEN rewrite_tac [evalcf_ftv_ft_lemma]);
val evalcf_ftv_ft_lemma1 = save_pop_thm "evalcf_ftv_ft_lemma1";

pop_pc();

set_goal([], ⌜∀s⦁ EvalCf_ftv s = fB ⇔ ¬ fFalse ∈ s ∧ ¬ fT ∈ s ∧ fB ∈ s⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜EvalCf_ftv⌝, ≤⋎t⋎4_lub_thm]);
a (cases_tac ⌜fFalse ∈ s⌝ THEN cases_tac ⌜fT ∈ s⌝ THEN cases_tac ⌜fB ∈ s⌝
	THEN asm_rewrite_tac[]);
val evalcf_ftv_fb_lemma = save_pop_thm "evalcf_ftv_fb_lemma";

set_goal([], ⌜∀s⦁ EvalCf_ftv s = fB ⇒ ¬ fFalse ∈ s ∧ ¬ fT ∈ s ∧ fB ∈ s⌝);
a (∀_tac THEN rewrite_tac [evalcf_ftv_fb_lemma]);
val evalcf_ftv_fb_lemma1 = save_pop_thm "evalcf_ftv_fb_lemma1";

(*
set_goal([], ⌜∀s⦁ EvalCf_ftv s = fB ⇔ fB ∈ s ∧ ¬ fFalse ∈ s ∧ ¬ fT ∈ s⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜EvalCf_ftv⌝]);
a (cond_cases_tac ⌜∀ x⦁ x ∈ s ⇒ x = fTrue⌝);
(* *** Goal "1" *** *)
a (contr_tac THEN asm_fc_tac[]);
(* *** Goal "2" *** *)
a (cond_cases_tac ⌜∀ x⦁ x ∈ s ⇒ x = fTrue ∨ x = fB⌝);
(* *** Goal "2.1" *** *)
a (contr_tac THEN asm_fc_tac[]);
a (var_elim_nth_asm_tac 1);
(* *** Goal "2.2" *** *)
a (cond_cases_tac ⌜fT ∈ s⌝);
a (contr_tac THEN asm_fc_tac[]);
a (REPEAT (POP_ASM_T ante_tac)
	THEN strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm)
	THEN asm_rewrite_tac[]
	THEN contr_tac);
val evalcf_ftv_fb_lemma = save_pop_thm "evalcf_ftv_fb_lemma";
*)
=TEX
}%ignore

This definition shows how the set of truth values of instances of the constituents is obtained from the denotations of the constituent formulae.

ⓈHOLCONST
│ ⦏EvalCf⦎ : 't CFE → GS → ('a, 't) ST → ('a, 't) RV SET → ('a, 't) RV
├───────────
│ ∀etf f⦁ EvalCf etf f = λst rvs va⦁ 
│	let ν = CfVars f
│	and V = Fst st
│	in etf {pb | ∃rv v⦁
│		  rv ∈ rvs
│		∧ IxDom v = X⋎g ν
│		∧ IxRan v ⊆ V
│		∧ pb = rv (IxOverRide va v)}
■

=GFT
EvalCf_MkCf_lemma =
   ⊢ ∀ etf vars forms st rvs va
     ⦁ EvalCf etf (MkCf (vars, forms)) st rvs va
         = etf
           {pb
             |∃ rv v
               ⦁ rv ∈ rvs
                   ∧ IxDom v = X⋎g vars
                   ∧ IxRan v ⊆ Fst st
                   ∧ pb = rv (IxOverRide va v)}
=TEX

\ignore{
=SML
set_goal([], ⌜∀etf vars forms st rvs va⦁ EvalCf etf (MkCf (vars, forms)) st rvs va =
		etf {pb | ∃rv v⦁
│		  rv ∈ rvs
│		∧ IxDom v = X⋎g vars
│		∧ IxRan v ⊆ Fst st
│		∧ pb = rv (IxOverRide va v)}⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜EvalCf⌝, let_def]);
val EvalCf_MkCf_lemma = pop_thm ();

set_merge_pcs ["misc2", "'infos"];
=TEX
}%ignore

Now we define a parameterised functor of which the semantic function is a fixed point.

ⓈHOLCONST
│ ⦏EvalFormFunct⦎ : 't CFE × 't REL × ('a, 't) ST → (GS → ('a, 't) RV)
│	→ (GS → ('a, 't) RV)
├───────────
│ ∀cfe $≤⋎t st⦁ EvalFormFunct (cfe, $≤⋎t, st) = λef f⦁
│	if f ∈ Syntax
│	then if IsAf f
│	     then EvalAf $≤⋎t f st
│	     else
│		let rvs = FunImage ef (X⋎g(CfForms f))
│	     	in  EvalCf cfe f st rvs
│	else εx⦁T
■

The semantics of formulae is then given by:

ⓈHOLCONST
│ ⦏EvalForm⦎ : 't CFE × 't REL × ('a, 't) ST → GS → ('a, 't) RV
├───────────
│ ∀cfe $≤⋎t st⦁ EvalForm (cfe, $≤⋎t, st) = fix (EvalFormFunct (cfe, $≤⋎t, st))
■

To use this definition we need to show that there exists a fixed point, for which we must show that the functor respects some well-founded relation.

=GFT
⦏evalformfunct_respect_thm⦎ =
   ⊢ ∀ cfe ≤⋎t st⦁ EvalFormFunct (cfe, ≤⋎t, st) respects ScPrec

⦏evalformfunct_fixp_lemma⦎ =
   ⊢ ∀ cfe ≤⋎t st
     ⦁ EvalForm (cfe, ≤⋎t, st)
         = EvalFormFunct (cfe, ≤⋎t, st) (EvalForm (cfe, ≤⋎t, st))
=TEX
=GFT
⦏evalformfunct_thm⦎ =
   ⊢ ∀ cfe ≤⋎t st
     ⦁ EvalForm (cfe, ≤⋎t, st)
         = (λ f
         ⦁ if f ∈ Syntax
           then
             if IsAf f
             then EvalAf ≤⋎t f st
             else 
               let rvs = FunImage (EvalForm (cfe, ≤⋎t, st)) (X⋎g (CfForms f))
               in EvalCf cfe f st rvs
           else ε x⦁ T)
=TEX
=GFT
⦏evalformfunct_thm2⦎ =
   ⊢ ∀ cfe ≤⋎t st f
     ⦁ EvalForm (cfe, ≤⋎t, st) f
         = (if f ∈ Syntax
           then
             if IsAf f
             then EvalAf ≤⋎t f st
             else
               (let rvs
                     = FunImage (EvalForm (cfe, ≤⋎t, st)) (X⋎g (CfForms f))
               in EvalCf cfe f st rvs)
           else ε f⦁ T)
=TEX

\ignore{
=SML
local val _ = set_goal([], ⌜∀cfe $≤⋎t st⦁ (EvalFormFunct (cfe, $≤⋎t, st)) respects ScPrec⌝);
val _ = a (rewrite_tac [get_spec ⌜EvalFormFunct⌝, get_spec ⌜$respects⌝]
	THEN REPEAT strip_tac);
val _ = a (cases_tac ⌜IsAf x⌝ THEN asm_rewrite_tac[]);
val _ = a (cases_tac ⌜x ∈ Syntax⌝ THEN asm_rewrite_tac[]);
val _ = a (lemma_tac ⌜FunImage g (X⋎g (CfForms x)) = FunImage h (X⋎g (CfForms x))⌝
	THEN_TRY asm_rewrite_tac[get_spec ⌜X⋎g⌝]);
val _ = a (PC_T1 "hol1" rewrite_tac [get_spec ⌜FunImage⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
val _ = a (fc_tac [syntax_cases_thm]);
val _ = a (all_fc_tac [scprec_fc_clauses2]);
val _ = a (all_asm_fc_tac[tc_incr_thm]);
val _ = a (all_asm_fc_tac[]);
val _ = a (∃_tac ⌜a⌝ THEN asm_rewrite_tac[]);
val _ = a (POP_ASM_T (fn x => rewrite_thm_tac (eq_sym_rule x)));
val _ = a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
val _ = a (fc_tac [syntax_cases_thm]);
val _ = a (all_fc_tac [scprec_fc_clauses2]);
val _ = a (all_asm_fc_tac[tc_incr_thm]);
val _ = a (all_asm_fc_tac[]);
val _ = a (∃_tac ⌜a⌝ THEN asm_rewrite_tac[]);
in val evalformfunct_respect_thm = save_pop_thm "evalformfunct_respect_thm";
end;

local val _ = set_goal([], ⌜∀cfe $≤⋎t st⦁ EvalForm (cfe, $≤⋎t, st) = EvalFormFunct (cfe, $≤⋎t, st) (EvalForm (cfe, $≤⋎t, st))⌝);
val _ = a (asm_tac well_founded_ScPrec_thm);
val _ = a (asm_tac evalformfunct_respect_thm);
val _ = a (REPEAT ∀_tac);
val _ = a (list_spec_nth_asm_tac 1 [⌜cfe⌝, ⌜$≤⋎t⌝, ⌜st⌝]);
val _ = a (all_fc_tac [∀_elim ⌜ScPrec⌝ (∀_elim ⌜EvalFormFunct (cfe, $≤⋎t, st)⌝ (get_spec ⌜fix⌝))]);
val _ = a (rewrite_tac [get_spec ⌜EvalForm⌝]);
val _ = a (asm_rewrite_tac[]);
in val evalformfunct_fixp_lemma = save_pop_thm "evalformfunct_fixp_lemma";
end;

val evalformfunct_thm = save_thm ("evalformfunct_thm",
	rewrite_rule [get_spec ⌜EvalFormFunct⌝] evalformfunct_fixp_lemma);

local val _ = set_goal([], ⌜∀ cfe $≤⋎t st f
     ⦁ EvalForm (cfe, $≤⋎t, st) f
         = if f ∈ Syntax
             then
               if IsAf f
               then EvalAf $≤⋎t f st
               else 
                 let rvs = FunImage (EvalForm (cfe, $≤⋎t, st)) (X⋎g (CfForms f))
                 in EvalCf cfe f st rvs
             else ε f⦁ T⌝);
val _ = a (REPEAT strip_tac THEN rewrite_tac[rewrite_rule [](once_rewrite_rule [ext_thm] evalformfunct_thm)]);
in val evalformfunct_thm2 = save_pop_thm "evalformfunct_thm2";
end;
=TEX
}%ignore

A similar effect can be obtained more concisely as follows:

ⓈHOLCONST
│ ⦏EvalForm2⦎ : 't CFE × 't REL × ('a, 't) ST → GS → ('a, 't) RV
├───────────
│
│ (∀cfe $≤⋎t V rv mem set va⦁ EvalForm2 (cfe, $≤⋎t, (V, rv)) (MkAf (mem, set)) va = 
│	if mem ∈ IxDom va ∧ set ∈ IxDom va
│	then rv (IxVal va mem) (IxVal va set)
│	else Lub $≤⋎t {})
│  ∧
│ (∀cfe $≤⋎t V rv ν forms va⦁ EvalForm2 (cfe, $≤⋎t, (V, rv)) (MkCf (ν, forms)) va =
│	cfe {pb | ∃rv2 v⦁ rv2 ∈ FunImage⋎g (EvalForm2 (cfe, $≤⋎t, (V, rv))) forms
│		∧ IxDom v = X⋎g ν
│		∧ IxRan v ⊆ V
│		∧ pb = rv2 (IxOverRide va v)})
│  ∧
│ (∀cfe $≤⋎t V rv x va⦁ EvalForm2 (cfe, $≤⋎t, (V, rv)) (MkTrash x) va = Lub $≤⋎t {})
■

However the effect is not identical, and this does not stipulate what happens to elements in the domain type of the function (taking this as GS and treating previous arguments as parameters) but not in the set {\it Syntax}.
This might complicate the problem of establishing the monotonicity of the semantics.

=GFT
⦏EvalForm_MkAf_lemma⦎ =
   ⊢ ∀ cfe ≤⋎t st set mem
     ⦁ EvalForm (cfe, ≤⋎t, st) (MkAf (set, mem))
         = EvalAf ≤⋎t (MkAf (set, mem)) st
=TEX

\ignore{
=IGN
set_goal([], ⌜∃EvalForm3⦁ (∀cfe $≤⋎t V rv mem set va⦁ EvalForm3 (cfe, $≤⋎t, (V, rv)) (MkAf (mem, set)) va = 
│	if mem ∈ IxDom va ∧ set ∈ IxDom va
│	then rv (IxVal va mem) (IxVal va set)
│	else Lub $≤⋎t {})
│  ∧
│ (∀cfe $≤⋎t V rv ν forms va⦁ EvalForm3 (cfe, $≤⋎t, (V, rv)) (MkCf (ν, forms)) va =
│	cfe {pb | ∃rv2 v⦁ rv2 ∈ FunImage⋎g (EvalForm2 (cfe, $≤⋎t, (V, rv))) forms
│		∧ IxDom v = X⋎g ν
│		∧ IxRan v ⊆ V
│		∧ pb = rv2 (IxOverRide va v)})
    ∧ ∀cfe $≤⋎t V rv x va⦁ (¬ IsAf x ∧ ¬ IsCf x) ⇒ EvalForm3 (cfe, $≤⋎t, (V, rv)) x va = εy⦁T
⌝);

a (prove_∃_tac);


=SML
add_pc_thms "'infos" [get_spec ⌜EvalForm2⌝];
set_merge_pcs ["misc2", "'infos"];
=TEX

=SML
set_goal([], ⌜∀ cfe $≤⋎t st set mem⦁ EvalForm (cfe, $≤⋎t, st) (MkAf (set, mem)) = EvalAf $≤⋎t (MkAf (set, mem)) st⌝);
a (REPEAT ∀_tac THEN rewrite_tac [evalformfunct_thm2]);
val EvalForm_MkAf_lemma = pop_thm ();
=TEX
}%ignore


=GFT
⦏EvalForm_fT_lemma⦎ =
   ⊢ ∀ V y
     ⦁ y ∈ Syntax
         ⇒ (∀ va
         ⦁ FreeVars y ⊆ IxDom va
               ∧ IxRan va ⊆ V ∪ {∅⋎g}
               ∧ EvalForm (EvalCf_ftv, $≤⋎t⋎4, V ∪ {∅⋎g}, $∈⋎v) y va = fT
             ⇒ (∃ x y⦁ x ∈ V ∪ {∅⋎g} ∧ y ∈ V ∪ {∅⋎g} ∧ x ∈⋎v y = fT))

⦏EvalForm2_fT_lemma⦎ =
   ⊢ ∀ V y
     ⦁ y ∈ Syntax
         ⇒ (∀ va
         ⦁ FreeVars y ⊆ IxDom va
               ∧ IxRan va ⊆ V ∪ {∅⋎g}
               ∧ EvalForm2 (EvalCf_ftv, $≤⋎t⋎4, V ∪ {∅⋎g}, $∈⋎v) y va = fT
             ⇒ (∃ x y⦁ x ∈ V ∪ {∅⋎g} ∧ y ∈ V ∪ {∅⋎g} ∧ x ∈⋎v y = fT))
=TEX
=GFT
⦏EvalForm_fT_lemma2⦎ =
   ⊢ ∀ y
     ⦁ y ∈ Syntax
         ⇒ (∀ va
         ⦁ FreeVars y ⊆ IxDom va
               ∧ IxRan va ⊆ V ∪ {∅⋎g}
               ∧ EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, $∈⋎v) y va = fT
             ⇒ (∃ x y⦁ x ∈ V ∪ {∅⋎g} ∧ y ∈ V ∪ {∅⋎g} ∧ x ∈⋎v y = fT))

⦏EvalForm2_fT_lemma2⦎ =
   ⊢ ∀ V y
     ⦁ y ∈ Syntax
         ⇒ (∀ va
         ⦁ FreeVars y ⊆ IxDom va
               ∧ IxRan va ⊆ V ∪ {∅⋎g}
               ∧ EvalForm2 (EvalCf_ftv, $≤⋎t⋎4, V, $∈⋎v) y va = fT
             ⇒ (∃ x y⦁ x ∈ V ∪ {∅⋎g} ∧ y ∈ V ∪ {∅⋎g} ∧ x ∈⋎v y = fT))
=TEX

\ignore{
=SML
add_pc_thms "'infos" [EvalAf_MkAf_lemma, EvalCf_MkCf_lemma, EvalForm_MkAf_lemma];

push_merge_pcs ["misc2", "'infos"];

set_goal([], ⌜∀V y⦁ y ∈ Syntax ⇒ ∀va⦁ FreeVars y ⊆ IxDom va ∧ IxRan va ⊆ V ∪ {∅⋎g}
	∧ EvalForm (EvalCf_ftv, $≤⋎t⋎4, V ∪ {∅⋎g}, $∈⋎v) y va = fT
	⇒ (∃ x y:GS⦁ x ∈ V ∪ {∅⋎g} ∧ y ∈ V ∪ {∅⋎g} ∧ y ∈⋎v x = fT)⌝);
a (strip_tac THEN strip_tac THEN strip_tac);
a (infos_induction_tac ⌜y⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac THEN DROP_NTH_ASM_T 2 ante_tac
	THEN asm_rewrite_tac[get_spec ⌜FreeVars⌝, get_spec ⌜$⊆⌝, ∈_in_clauses]);
a (strip_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (spec_nth_asm_tac 2 ⌜y⌝);
a (asm_rewrite_tac[]);
a (strip_tac THEN ∃_tac ⌜IxVal va y⌝ THEN ∃_tac ⌜IxVal va x⌝);
a (all_fc_tac[ix_domran_lemma]);
a (PC_T1 "hol1" asm_prove_tac []);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac [evalformfunct_thm2, let_def]);
a (ALL_FC_T (fn x => rewrite_tac (x @ [evalcf_ftv_ft_lemma])) [repclosed_syntax_thm2] THEN strip_tac);
a (DROP_NTH_ASM_T 5 ante_tac
	THEN rewrite_tac [get_spec ⌜FunImage⌝, get_spec ⌜X⋎g⌝]
	THEN strip_tac
	THEN all_asm_fc_tac []);
a (DROP_NTH_ASM_T 5 ante_tac THEN SYM_ASMS_T rewrite_tac);
a (STRIP_T (asm_tac o eq_sym_rule));
a (spec_nth_asm_tac 11 ⌜a⌝);
a (lemma_tac ⌜MkCf(vars, fs) ∈ Syntax⌝
	THEN1 ALL_FC_T rewrite_tac [rewrite_rule [get_spec ⌜X⋎g⌝] repclosed_syntax_thm]);
a (lemma_tac ⌜FreeVars a ⊆ IxDom (IxOverRide va v)
                 ∧ IxRan (IxOverRide va v) ⊆ V ∪ {∅⋎g}⌝
	THEN1 (asm_rewrite_tac []));
(* *** Goal "2.1" *** *)
a (REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a (DROP_NTH_ASM_T 12 (ante_tac o (rewrite_rule [get_spec ⌜FreeVars⌝])));
a (asm_rewrite_tac[get_spec ⌜FunImage⋎g⌝]);
a (PC_T "hol1" contr_tac);
a (spec_nth_asm_tac 4 ⌜x⌝);
a (spec_nth_asm_tac 1 ⌜FreeVars a⌝);
a (spec_nth_asm_tac 1 ⌜a⌝);
(* *** Goal "2.1.2" *** *)
a (asm_tac (list_∀_elim [⌜va⌝, ⌜v⌝] ixoverride_ixran_lemma));
push_goal([], ⌜∀A B C D:GS SET⦁ A ⊆ B ∪ C ∧ B ⊆ D ∧ C ⊆ D ⇒ A ⊆ D⌝);
a (PC_T1 "hol1" rewrite_tac [] THEN REPEAT strip_tac THEN REPEAT (asm_fc_tac []));
a (all_fc_tac [pop_thm()]);
(* *** Goal "2.2" *** *)
a (ALL_ASM_FC_T (MAP_EVERY asm_tac) []);
a ((POP_ASM_T discard_tac) THEN POP_ASM_T ante_tac);
a (PC_T1 "hol1" prove_tac[]);
val EvalForm_fT_lemma = save_pop_thm "EvalForm_fT_lemma";

set_goal([], ⌜∀y⦁ y ∈ Syntax ⇒ ∀va⦁ FreeVars y ⊆ IxDom va ∧ IxRan va ⊆ V ∪ {∅⋎g}
	∧ EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, $∈⋎v) y va = fT
	⇒ (∃ x y⦁ x ∈ V ∪ {∅⋎g} ∧ y ∈ V ∪ {∅⋎g} ∧ y ∈⋎v x = fT)⌝);
a (strip_tac THEN strip_tac);
a (infos_induction_tac ⌜y⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac THEN DROP_NTH_ASM_T 2 ante_tac
	THEN asm_rewrite_tac[get_spec ⌜FreeVars⌝, get_spec ⌜$⊆⌝, ∈_in_clauses]);
a (strip_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (spec_nth_asm_tac 2 ⌜y⌝);
a (asm_rewrite_tac[]);
a (strip_tac THEN ∃_tac ⌜IxVal va y⌝ THEN ∃_tac ⌜IxVal va x⌝
	THEN asm_rewrite_tac[]);
a (all_fc_tac[ix_domran_lemma]);
a (PC_T1 "hol1" asm_prove_tac []);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac [evalformfunct_thm2, let_def]);
a (ALL_FC_T (fn x => rewrite_tac (x @ [evalcf_ftv_ft_lemma])) [repclosed_syntax_thm2] THEN strip_tac);
a (DROP_NTH_ASM_T 5 ante_tac
	THEN rewrite_tac [get_spec ⌜FunImage⌝, get_spec ⌜X⋎g⌝]
	THEN strip_tac
	THEN all_asm_fc_tac []);
a (DROP_NTH_ASM_T 5 ante_tac THEN SYM_ASMS_T rewrite_tac);
a (STRIP_T (asm_tac o eq_sym_rule));
a (spec_nth_asm_tac 11 ⌜a⌝);
a (lemma_tac ⌜MkCf(vars, fs) ∈ Syntax⌝
	THEN1 ALL_FC_T rewrite_tac [rewrite_rule [get_spec ⌜X⋎g⌝] repclosed_syntax_thm]);
a (lemma_tac ⌜FreeVars a ⊆ IxDom (IxOverRide va v)
                 ∧ IxRan (IxOverRide va v) ⊆ V ∪ {∅⋎g}⌝
	THEN1 (asm_rewrite_tac []));
(* *** Goal "2.1" *** *)
a (REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a (DROP_NTH_ASM_T 12 (ante_tac o (rewrite_rule [get_spec ⌜FreeVars⌝])));
a (asm_rewrite_tac[get_spec ⌜FunImage⋎g⌝]);
a (PC_T "hol1" contr_tac);
a (spec_nth_asm_tac 4 ⌜x⌝);
a (spec_nth_asm_tac 1 ⌜FreeVars a⌝);
a (spec_nth_asm_tac 1 ⌜a⌝);
(* *** Goal "2.1.2" *** *)
a (asm_tac (list_∀_elim [⌜va⌝, ⌜v⌝] ixoverride_ixran_lemma));
a (lemma_tac ⌜IxRan v ⊆ V ∪ {∅⋎g}⌝
	THEN1 PC_T "hol1" (GET_ASM_T ⌜IxRan v ⊆ V⌝ ante_tac THEN prove_tac []));
push_goal([], ⌜∀A B C D:GS SET⦁ A ⊆ B ∪ C ∧ B ⊆ D ∧ C ⊆ D ⇒ A ⊆ D⌝);
a (PC_T1 "hol1" rewrite_tac [] THEN REPEAT strip_tac THEN REPEAT (asm_fc_tac []));
a (all_fc_tac [pop_thm()]);
(* *** Goal "2.2" *** *)
a (ALL_ASM_FC_T (MAP_EVERY asm_tac) []);
a ((POP_ASM_T discard_tac) THEN POP_ASM_T ante_tac);
a (PC_T1 "hol1" prove_tac[]);
val EvalForm_fT_lemma2 = save_pop_thm "EvalForm_fT_lemma2";

set_goal([], ⌜∀V y⦁ y ∈ Syntax ⇒ ∀va⦁ FreeVars y ⊆ IxDom va ∧ IxRan va ⊆ V ∪ {∅⋎g}
	∧ EvalForm2 (EvalCf_ftv, $≤⋎t⋎4, V ∪ {∅⋎g}, $∈⋎v) y va = fT
	⇒ (∃ x y:GS⦁ x ∈ V ∪ {∅⋎g} ∧ y ∈ V ∪ {∅⋎g} ∧ x ∈⋎v y = fT)⌝);
a (strip_tac THEN strip_tac THEN strip_tac);
a (infos_induction_tac ⌜y⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac THEN DROP_NTH_ASM_T 2 ante_tac
	THEN asm_rewrite_tac[get_spec ⌜FreeVars⌝, get_spec ⌜$⊆⌝, ∈_in_clauses]);
a (strip_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (spec_nth_asm_tac 2 ⌜y⌝);
a (asm_rewrite_tac[]);
a (strip_tac THEN ∃_tac ⌜IxVal va x⌝ THEN ∃_tac ⌜IxVal va y⌝
	THEN asm_rewrite_tac[]);
a (all_fc_tac[ix_domran_lemma]);
a (PC_T1 "hol1" asm_prove_tac []);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac);
a (ALL_FC_T (fn x => rewrite_tac (x @ [evalcf_ftv_ft_lemma])) [repclosed_syntax_thm2] THEN strip_tac);
a (DROP_NTH_ASM_T 5 ante_tac
	THEN rewrite_tac [get_spec ⌜FunImage⋎g⌝]
	THEN strip_tac
	THEN all_asm_fc_tac []);
a (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[]);
a (STRIP_T (asm_tac o eq_sym_rule));
a (spec_nth_asm_tac 11 ⌜y⌝);
a (lemma_tac ⌜MkCf(vars, fs) ∈ Syntax⌝
	THEN1 ALL_FC_T rewrite_tac [rewrite_rule [get_spec ⌜X⋎g⌝] repclosed_syntax_thm]);
a (lemma_tac ⌜FreeVars y ⊆ IxDom (IxOverRide va v)
                 ∧ IxRan (IxOverRide va v) ⊆ V ∪ {∅⋎g}⌝
	THEN1 (asm_rewrite_tac []));
(* *** Goal "2.1" *** *)
a (REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a (DROP_NTH_ASM_T 12 ante_tac
	THEN rewrite_tac[get_spec ⌜FreeVars⌝, get_spec ⌜FunImage⋎g⌝]);
a (once_rewrite_tac [sets_ext_clauses]);
a (rewrite_tac [∈_in_clauses] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 3 ⌜x⌝);
a (spec_nth_asm_tac 1 ⌜FreeVars y⌝);
a (spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "2.1.2" *** *)
a (asm_tac (list_∀_elim [⌜va⌝, ⌜v⌝] ixoverride_ixran_lemma));
push_goal([], ⌜∀A B C D:GS SET⦁ A ⊆ B ∪ C ∧ B ⊆ D ∧ C ⊆ D ⇒ A ⊆ D⌝);
a (PC_T1 "hol1" rewrite_tac [] THEN REPEAT strip_tac THEN REPEAT (asm_fc_tac []));
a (all_fc_tac [pop_thm()]);
(* *** Goal "2.2" *** *)
a (SPEC_NTH_ASM_T 4 ⌜IxOverRide va v⌝ (accept_tac o (rewrite_rule
	[asm_rule ⌜FreeVars y ⊆ IxDom (IxOverRide va v)⌝,
	asm_rule ⌜IxRan (IxOverRide va v) ⊆ V ∪ {∅⋎g}⌝,
	asm_rule ⌜EvalForm2 (EvalCf_ftv, $≤⋎t⋎4, V ∪ {∅⋎g}, $∈⋎v) y (IxOverRide va v) = fT⌝])));
val EvalForm2_fT_lemma = save_pop_thm "EvalForm2_fT_lemma";

set_goal([], ⌜∀V y⦁ y ∈ Syntax ⇒ ∀va⦁ FreeVars y ⊆ IxDom va ∧ IxRan va ⊆ V ∪ {∅⋎g}
	∧ EvalForm2 (EvalCf_ftv, $≤⋎t⋎4, V, $∈⋎v) y va = fT
	⇒ (∃ x y⦁ x ∈ V ∪ {∅⋎g} ∧ y ∈ V ∪ {∅⋎g} ∧ x ∈⋎v y = fT)⌝);
a (strip_tac THEN strip_tac THEN strip_tac);
a (infos_induction_tac ⌜y⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac THEN DROP_NTH_ASM_T 2 ante_tac
	THEN asm_rewrite_tac[get_spec ⌜FreeVars⌝, get_spec ⌜$⊆⌝, ∈_in_clauses]);
a (strip_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (spec_nth_asm_tac 2 ⌜y⌝);
a (asm_rewrite_tac[]);
a (strip_tac THEN ∃_tac ⌜IxVal va x⌝ THEN ∃_tac ⌜IxVal va y⌝
	THEN asm_rewrite_tac[]);
a (all_fc_tac[ix_domran_lemma]);
a (PC_T1 "hol1" asm_prove_tac []);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac
	THEN ALL_FC_T (fn x => rewrite_tac (x @ [evalcf_ftv_ft_lemma, get_spec ⌜EvalForm2⌝]))
		[repclosed_syntax_thm2] THEN strip_tac);
a (DROP_NTH_ASM_T 5 ante_tac
	THEN rewrite_tac [get_spec ⌜FunImage⋎g⌝]
	THEN strip_tac
	THEN all_asm_fc_tac []);
a (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac []);
a (STRIP_T (asm_tac o eq_sym_rule));
a (spec_nth_asm_tac 11 ⌜y⌝);
a (lemma_tac ⌜MkCf(vars, fs) ∈ Syntax⌝
	THEN1 ALL_FC_T rewrite_tac [rewrite_rule [get_spec ⌜X⋎g⌝] repclosed_syntax_thm]);
a (lemma_tac ⌜FreeVars y ⊆ IxDom (IxOverRide va v)
                 ∧ IxRan (IxOverRide va v) ⊆ V ∪ {∅⋎g}⌝
	THEN1 (asm_rewrite_tac []));
(* *** Goal "2.1" *** *)
a (REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a (DROP_NTH_ASM_T 12 (ante_tac o (rewrite_rule [get_spec ⌜FreeVars⌝])));
a (asm_rewrite_tac[get_spec ⌜FunImage⋎g⌝]);
a (PC_T "hol1" contr_tac);
a (spec_nth_asm_tac 4 ⌜x⌝);
a (spec_nth_asm_tac 1 ⌜FreeVars y⌝);
a (spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "2.1.2" *** *)
a (asm_tac (list_∀_elim [⌜va⌝, ⌜v⌝] ixoverride_ixran_lemma));
a (lemma_tac ⌜IxRan v ⊆ V ∪ {∅⋎g}⌝
	THEN1 PC_T "hol1" (GET_ASM_T ⌜IxRan v ⊆ V⌝ ante_tac THEN prove_tac []));
push_goal([], ⌜∀A B C D:GS SET⦁ A ⊆ B ∪ C ∧ B ⊆ D ∧ C ⊆ D ⇒ A ⊆ D⌝);
a (PC_T1 "hol1" rewrite_tac [] THEN REPEAT strip_tac THEN REPEAT (asm_fc_tac []));
a (all_fc_tac [pop_thm()]);
(* *** Goal "2.2" *** *)
a (ALL_ASM_FC_T (MAP_EVERY asm_tac) []);
a ((POP_ASM_T discard_tac) THEN POP_ASM_T ante_tac);
a (PC_T1 "hol1" prove_tac[]);
val EvalForm2_fT_lemma2 = save_pop_thm "EvalForm2_fT_lemma2";

pop_pc();
=TEX
}%ignore

\section{MONOTONICITY}

\subsection{Equivalence of Membership Relations}

It proves useful in later proofs to have a notion of equivalence over partial membership relations and to obtain here some lemmas about aspects of the semantics which depend upon a prior notion of membership and give the same result for equivalent relations.

ⓈHOLCONST
│ ⦏PmrEq⦎ : 'a SET → ('a, 'b) BR → ('a, 'b) BR → BOOL
├───────────
│ ∀V⦁ PmrEq V = λr1 r2⦁ ∀x y⦁ x ∈ V ∧ y ∈ V ⇒ r1 x y = r2 x y
■

=GFT
⦏PmrEq_EvalForm_lemma⦎ =
   ⊢ ∀ cfe ≤⋎t V W f r1 r2
     ⦁ V ⊆ W ∧ PmrEq W r1 r2
         ⇒ f ∈ Syntax
         ⇒ (∀ z
         ⦁ IxRan z ⊆ W
             ⇒ EvalForm (cfe, ≤⋎t, V, r1) f z
               = EvalForm (cfe, ≤⋎t, V, r2) f z)

⦏PmrEq_EvalForm2_lemma⦎ =
   ⊢ ∀ cfe ≤⋎t V W f r1 r2
     ⦁ V ⊆ W ∧ PmrEq W r1 r2
         ⇒ f ∈ Syntax
         ⇒ (∀ z
         ⦁ IxRan z ⊆ W
             ⇒ EvalForm2 (cfe, ≤⋎t, V, r1) f z
               = EvalForm2 (cfe, ≤⋎t, V, r2) f z)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ cfe ≤⋎t V W f r1 r2⦁ V ⊆ W ∧ PmrEq W r1 r2
	⇒ f ∈ Syntax ⇒ ∀z⦁ IxRan z ⊆ W ⇒ EvalForm (cfe, ≤⋎t, (V, r1)) f z = EvalForm (cfe, ≤⋎t, (V, r2)) f z⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜PmrEq⌝] THEN strip_tac THEN strip_tac);
a (infos_induction_tac ⌜f⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [evalformfunct_thm2, repclosed_syntax_thm, get_spec ⌜EvalAf⌝, let_def]);
a (cond_cases_tac ⌜x ∈ IxDom z ∧ y ∈ IxDom z⌝);
a (DROP_ASM_T ⌜IxRan z ⊆ W⌝ (asm_tac o (rewrite_rule[sets_ext_clauses])));
a (list_spec_nth_asm_tac 4 [⌜IxVal z x⌝, ⌜IxVal z y⌝]);
a (lemma_tac ⌜IxVal z x ∈ W⌝
	THEN1 (fc_tac [ix_domran_lemma] THEN asm_fc_tac[]));
a (lemma_tac ⌜IxVal z y ∈ W⌝
	THEN1 (fc_tac [ix_domran_lemma] THEN asm_fc_tac[]));
(* *** Goal "2" *** *)
a (rewrite_tac [evalformfunct_thm2, let_def]);
a (LEMMA_T ⌜MkCf (vars, fs) ∈ Syntax⌝ rewrite_thm_tac
	THEN1 FC_T rewrite_tac [repclosed_syntax_thm2]);
a (rewrite_tac[get_spec ⌜EvalCf⌝, let_def]);
a (LEMMA_T ⌜{pb
                 |∃ rv v
                   ⦁ rv ∈ FunImage (EvalForm (cfe, ≤⋎t, V, r1)) (X⋎g fs)
                       ∧ IxDom v = X⋎g vars
                       ∧ IxRan v ⊆ V
                       ∧ pb = rv (IxOverRide z v)}
             = {pb
                 |∃ rv v
                   ⦁ rv ∈ FunImage (EvalForm (cfe, ≤⋎t, V, r2)) (X⋎g fs)
                       ∧ IxDom v = X⋎g vars
                       ∧ IxRan v ⊆ V
                       ∧ pb = rv (IxOverRide z v)}⌝ rewrite_thm_tac);
a (rewrite_tac [sets_ext_clauses, ∈_in_clauses]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (DROP_NTH_ASM_T 4 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
a (∃_tac ⌜EvalForm (cfe, ≤⋎t, V, r2) a⌝ THEN ∃_tac ⌜v⌝ THEN asm_rewrite_tac []);
a (SYM_ASMS_T rewrite_tac);
a (DROP_ASM_T ⌜a ∈ X⋎g fs⌝ (asm_tac o (rewrite_rule [get_spec ⌜X⋎g⌝])));
a (asm_fc_tac []);
a (rewrite_tac [get_spec ⌜FunImage⌝] THEN strip_tac);
(* *** Goal "2.1.1" *** *)
a (∃_tac ⌜a⌝ THEN asm_rewrite_tac [get_spec ⌜X⋎g⌝]);
(* *** Goal "2.1.2" *** *)
a (asm_rewrite_tac []);
a (rewrite_tac [eq_sym_rule (asm_rule ⌜EvalForm (cfe, ≤⋎t, V, r1) a = rv⌝ )]);
a (all_asm_fc_tac []);
a (lemma_tac ⌜IxRan (IxOverRide z v) ⊆ W⌝);
a (asm_tac (list_∀_elim [⌜z⌝, ⌜v⌝] ixoverride_ixran_lemma));
a (lemma_tac ⌜IxRan z ∪ IxRan v ⊆ W⌝ THEN1 (PC_T1 "hol1" asm_prove_tac []));
a (all_fc_tac [⊆_trans_thm]);
a (all_asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (DROP_NTH_ASM_T 4 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
a (∃_tac ⌜EvalForm (cfe, ≤⋎t, V, r1) a⌝ THEN ∃_tac ⌜v⌝ THEN asm_rewrite_tac []);
a (SYM_ASMS_T rewrite_tac);
a (DROP_ASM_T ⌜a ∈ X⋎g fs⌝ (asm_tac o (rewrite_rule [get_spec ⌜X⋎g⌝])));
a (asm_fc_tac []);
a (rewrite_tac [get_spec ⌜FunImage⌝] THEN strip_tac);
(* *** Goal "2.2.1" *** *)
a (∃_tac ⌜a⌝ THEN asm_rewrite_tac [get_spec ⌜X⋎g⌝]);
(* *** Goal "2.2.2" *** *)
a (asm_rewrite_tac []);
a (rewrite_tac [eq_sym_rule (asm_rule ⌜EvalForm (cfe, ≤⋎t, V, r2) a = rv⌝ )]);
a (all_asm_fc_tac []);
a (lemma_tac ⌜IxRan (IxOverRide z v) ⊆ W⌝);
a (asm_tac (list_∀_elim [⌜z⌝, ⌜v⌝] ixoverride_ixran_lemma));
a (lemma_tac ⌜IxRan z ∪ IxRan v ⊆ W⌝ THEN1 (PC_T1 "hol1" asm_prove_tac []));
a (all_fc_tac [⊆_trans_thm]);
a (all_asm_fc_tac[]);
a (asm_rewrite_tac[]);
val PmrEq_EvalForm_lemma = save_pop_thm "PmrEq_EvalForm_lemma";

set_goal([], ⌜∀ cfe ≤⋎t V W f r1 r2⦁ V ⊆ W ∧ PmrEq W r1 r2
	⇒ f ∈ Syntax ⇒ ∀z⦁ IxRan z ⊆ W ⇒ EvalForm2 (cfe, ≤⋎t, (V, r1)) f z = EvalForm2 (cfe, ≤⋎t, (V, r2)) f z⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜PmrEq⌝] THEN strip_tac THEN strip_tac);
a (infos_induction_tac ⌜f⌝);
(* *** Goal "1" *** *)
a (strip_tac);
a (cond_cases_tac ⌜x ∈ IxDom z ∧ y ∈ IxDom z⌝);
a (DROP_ASM_T ⌜IxRan z ⊆ W⌝ (asm_tac o (rewrite_rule[sets_ext_clauses])));
a (lemma_tac ⌜IxVal z y ∈ W⌝
	THEN1 (fc_tac [ix_domran_lemma] THEN asm_fc_tac[]));
a (lemma_tac ⌜IxVal z x ∈ W⌝
	THEN1 (fc_tac [ix_domran_lemma] THEN asm_fc_tac[]));
a (list_spec_nth_asm_tac 6 [⌜IxVal z x⌝, ⌜IxVal z y⌝]);
(* *** Goal "2" *** *)
a (REPEAT strip_tac);
a (LEMMA_T ⌜{pb
                 |∃ rv2 v
                   ⦁ rv2 ∈ FunImage⋎g (EvalForm2 (cfe, ≤⋎t, V, r1)) fs
                       ∧ IxDom v = X⋎g vars
                       ∧ IxRan v ⊆ V
                       ∧ pb = rv2 (IxOverRide z v)}
             = {pb
                 |∃ rv2 v
                   ⦁ rv2 ∈ FunImage⋎g (EvalForm2 (cfe, ≤⋎t, V, r2)) fs
                       ∧ IxDom v = X⋎g vars
                       ∧ IxRan v ⊆ V
                       ∧ pb = rv2 (IxOverRide z v)}⌝ rewrite_thm_tac);
a (rewrite_tac [sets_ext_clauses, ∈_in_clauses]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (DROP_NTH_ASM_T 4 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⋎g⌝])));
a (∃_tac ⌜EvalForm2 (cfe, ≤⋎t, V, r2) y⌝ THEN ∃_tac ⌜v⌝
	THEN asm_rewrite_tac [get_spec ⌜FunImage⋎g⌝]
	THEN strip_tac);
(* *** Goal "2.1.1" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac []);
(* *** Goal "2.1.2" *** *)
a (all_asm_fc_tac []);
a (lemma_tac ⌜IxRan (IxOverRide z v) ⊆ W⌝);
(* *** Goal "2.1.2.1" *** *)
a (asm_tac (list_∀_elim [⌜z⌝, ⌜v⌝] ixoverride_ixran_lemma));
a (lemma_tac ⌜IxRan z ∪ IxRan v ⊆ W⌝ THEN1 (PC_T1 "hol1" asm_prove_tac []));
a (all_fc_tac [⊆_trans_thm]);
(* *** Goal "2.1.2.2" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (DROP_NTH_ASM_T 4 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⋎g⌝])));
a (∃_tac ⌜EvalForm2 (cfe, ≤⋎t, V, r1) y⌝ THEN ∃_tac ⌜v⌝
	THEN asm_rewrite_tac [get_spec ⌜FunImage⋎g⌝]
	THEN strip_tac);
(* *** Goal "2.2.1" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac []);
(* *** Goal "2.2.2" *** *)
a (all_asm_fc_tac []);
a (lemma_tac ⌜IxRan (IxOverRide z v) ⊆ W⌝);
(* *** Goal "2.2.2.1" *** *)
a (asm_tac (list_∀_elim [⌜z⌝, ⌜v⌝] ixoverride_ixran_lemma));
a (lemma_tac ⌜IxRan z ∪ IxRan v ⊆ W⌝ THEN1 (PC_T1 "hol1" asm_prove_tac []));
a (all_fc_tac [⊆_trans_thm]);
(* *** Goal "2.2.2.2" *** *)
a (all_asm_fc_tac[]);
a (asm_rewrite_tac[]);
val PmrEq_EvalForm2_lemma = save_pop_thm "PmrEq_EvalForm2_lemma";
=TEX
}%ignore

\subsection{Some Orderings}

To help in the location of fixed points we want a semantics which is monotonic, and therefore define here orderings on these domains relative to which we expect the sematantics to be monotonic.

The ordering on relations derives from the ordering on the truth values, using the operator {\it Pw}.

ⓈHOLCONST
│ ⦏RvO⦎ : ('b → 'b → BOOL) → ('a, 'b) RV → ('a, 'b) RV → BOOL
├───────────
│ ∀r⦁ RvO r = Pw r
■

=GFT
⦏rvo_lubs_exist_thm⦎ =
	⊢ ∀ r⦁ LubsExist r ⇒ LubsExist (RvO r)

⦏rvo_glbs_exist_thm⦎ =
	⊢ ∀ r⦁ GlbsExist r ⇒ GlbsExist (RvO r)
=TEX

\ignore{
=SML
local val _ = set_goal([], ⌜∀r⦁ LubsExist r ⇒ LubsExist (RvO r)⌝);
val _ = a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜RvO⌝]
	THEN REPEAT_N 2 (bc_tac [pw_lubs_exist_thm])
	THEN strip_tac);
in val rvo_lubs_exist_thm = save_pop_thm "rvo_lubs_exist_thm";
end;

local val _ = set_goal([], ⌜∀r⦁ GlbsExist r ⇒ GlbsExist (RvO r)⌝);
val _ = a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜RvO⌝]
	THEN REPEAT_N 2 (bc_tac [pw_glbs_exist_thm])
	THEN strip_tac);
in val rvo_glbs_exist_thm = save_pop_thm "rvo_glbs_exist_thm";
end;
=TEX
}%ignore

ⓈHOLCONST
│ ⦏RvIsO⦎ : ('b → 'b → BOOL) → ('a, 'b) RV IS → ('a, 'b) RV IS → BOOL
├───────────
│ ∀r⦁ RvIsO r = IsEO (RvO r)
■

=GFT
⦏rviso_lubs_exist_thm⦎ =
	⊢ ∀ r⦁ LubsExist r ⇒ LubsExist (RvIsO r)

⦏rviso_glbs_exist_thm⦎ =
	⊢ ∀ r⦁ GlbsExist r ⇒ GlbsExist (RvIsO r)
=TEX

\ignore{
=SML
local val _ = set_goal([], ⌜∀r⦁ LubsExist r ⇒ LubsExist (RvIsO r)⌝);
val _ = a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜RvIsO⌝]
	THEN bc_tac [is_lubs_exist_thm]
	THEN bc_tac [rvo_lubs_exist_thm]
	THEN strip_tac);
in val rviso_lubs_exist_thm = save_pop_thm "rviso_lubs_exist_thm";
end;

local val _ = set_goal([], ⌜∀r⦁ GlbsExist r ⇒ GlbsExist (RvIsO r)⌝);
val _ = a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜RvIsO⌝]
	THEN bc_tac [is_glbs_exist_thm]
	THEN bc_tac [rvo_glbs_exist_thm]
	THEN strip_tac);
in val rviso_glbs_exist_thm = save_pop_thm "rviso_glbs_exist_thm";
end;
=TEX
}%ignore

ⓈHOLCONST
│ ⦏StO⦎ : ('b → 'b → BOOL) → ('a, 'b) ST → ('a, 'b) ST → BOOL
├───────────
│ ∀r⦁ StO r = DerivedOrder Snd (Pw (Pw r))
■

=GFT
⦏sto_lubs_exist_thm⦎ =
	⊢ ∀ r⦁ LubsExist r ⇒ LubsExist (StO r)

⦏sto_glbs_exist_thm⦎ =
	⊢ ∀ r⦁ GlbsExist r ⇒ GlbsExist (StO r)
=TEX

\ignore{
=SML
local val _ = set_goal([], ⌜∀r⦁ LubsExist r ⇒ LubsExist (StO r)⌝);
val _ = a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜StO⌝]
	THEN bc_tac [lubsexist_dosnd_thm]
	THEN bc_tac [pw_lubs_exist_thm]
	THEN bc_tac [pw_lubs_exist_thm]
	THEN strip_tac);
in val sto_lubs_exist_thm = save_pop_thm "sto_lubs_exist_thm";
end;

local val _ = set_goal([], ⌜∀r⦁ GlbsExist r ⇒ GlbsExist (StO r)⌝);
val _ = a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜StO⌝]
	THEN bc_tac [glbsexist_dosnd_thm]
	THEN bc_tac [pw_glbs_exist_thm]
	THEN bc_tac [pw_glbs_exist_thm]
	THEN strip_tac);
in val sto_glbs_exist_thm = save_pop_thm "sto_glbs_exist_thm";
end;
=TEX
}%ignore

We will be looking for fixed points of the semantics and one approach to this is to take greatest of least fixed points over various subdomains of the formulae of this set theory.
This is why we are working with non-standard truth value types, so that we can arrange for the semantics to be monotonic relative to orderings derived from that on the truth values.

In order to prove that the semantics is monotonic, we must first define the partial orderings relative to which the semantics is monotonic, and we must obtain fixpoint theorems for the orderings.

We have at present two cases under consideration, according to whether three or four truth values are adopted.

The three valued case turns out in some respects more complex than the four valued case, because it is necessary to make do with chain completeness and the fixed point theorem is more difficult to prove (though in fact the proof has been completed).
I will therefore progress only the four valued case until I find a reason to further progress the three valued case.

Here is the beginning of the three valued case which I started before.

It is also necessary to prove that these partial orderings are CCPOs (chain complete partial orders), this being the weakest condition for which we have a suitable fixed point theorem.
It is convenient to be slightly more definite, to make the orderings all reflexive, and show that they are reflexive CCPOs (for which we use the term CCRPO).

The following ordering is applicable to partial predicates.

=SML
declare_infix(300, "≤⋎f⋎t⋎3");
=TEX

ⓈHOLCONST
│ $⦏≤⋎f⋎t⋎3⦎ : ('a → TTV) → ('a → TTV) → BOOL
├───────────
│ $≤⋎f⋎t⋎3 = Pw $≤⋎t⋎3
■

=GFT
⦏ccrpou_≤⋎f⋎t⋎3_thm⦎ =
	⊢ CcRpoU $≤⋎f⋎t⋎3
=TEX

\ignore{
=SML
local val _ = set_goal([], ⌜CcRpoU $≤⋎f⋎t⋎3⌝);
val _ = a (rewrite_tac [get_spec ⌜$≤⋎f⋎t⋎3⌝]);
val _ = a (asm_tac ccrpou_≤⋎t⋎3_thm);
val _ = a (fc_tac [pw_ccrpou_thm]);
in val ccrpou_≤⋎f⋎t⋎3_thm = save_pop_thm "ccrpou_≤⋎f⋎t⋎3_thm";
end;
=TEX
}%ignore

Lets now get on with the four valued case.

=SML
declare_infix(300, "≤⋎f⋎t⋎4");
=TEX

ⓈHOLCONST
│ $⦏≤⋎f⋎t⋎4⦎ : ('a → FTV) → ('a → FTV) → BOOL
├───────────
│ $≤⋎f⋎t⋎4 = Pw $≤⋎t⋎4
■

=GFT
⦏≤⋎f⋎t⋎4_crpou_thm⦎ =
	⊢  CRpoU $≤⋎f⋎t⋎4
=TEX

\ignore{
=SML
local val _ = set_goal([], ⌜CRpoU $≤⋎f⋎t⋎4⌝);
val _ = a (rewrite_tac [get_spec ⌜$≤⋎f⋎t⋎4⌝]);
val _ = a (asm_tac ≤⋎t⋎4_crpou_thm);
val _ = a (fc_tac [pw_crpou_thm]);
in val ≤⋎f⋎t⋎4_crpou_thm = save_pop_thm "≤⋎f⋎t⋎4_crpou_thm";
end;
=TEX
}%ignore

We need an ordering over variable assignments relative to membership relations which corresponds to degrees of well-definedness of the sets assigned to variables under the membership relation.

It might be helpful to do this separately for the extension and the essence of the sets, so that's what I propose to do here.

We begin with pre-orderings over {\it SetReps} corresponding to extension.

ⓈHOLCONST
│ ⦏ExtSRO⦎ : GS SET × (GS, FTV)BR → GS → GS → BOOL
├───────────
│ ∀V r⦁ ExtSRO (V, r) = λx y⦁ ∀z⦁ z ∈ V ⇒ r z x ≤⋎t⋎4 r z y
■

and to essences.

ⓈHOLCONST
│ ⦏EssSRO⦎ : GS SET × (GS, FTV)BR → GS → GS → BOOL
├───────────
│ ∀V r⦁ EssSRO (V, r) = λx y⦁ ∀z⦁ z ∈ V ⇒ r x z ≤⋎t⋎4 r y z
■

Though I suspect I may only need:

ⓈHOLCONST
│ ⦏ExsSRO⦎ : GS SET × (GS, FTV)BR → GS → GS → BOOL
├───────────
│ ∀s⦁ ExsSRO s = ConjOrder (ExtSRO s) (EssSRO s)
■

From this we obtain a pre-ordering over variable assignments:

ⓈHOLCONST
│ ⦏ExsVaO⦎ : ('a, GS) IX SET × (GS SET × (GS, FTV)BR)
	→ ('a, GS) IX → ('a, GS) IX → BOOL
├───────────
│ ∀d s⦁ ExsVaO (d, s) = IxO2 (d, (ExsSRO s))
■

The following function is given to determine appropriate sets of indexed sets for use with this ordering.
That is, for any domain V the set of V-valued indexed sets (there is no constraint on the domain for any set can be a variable and we use the indexed sets primarily for variable assignments).

ⓈHOLCONST
│ ⦏V2IxSet⦎ : GS SET → ('a, GS) IX SET
├───────────
│ ∀V⦁ V2IxSet V = {ix | IxRan ix ⊆ V}
■

=GFT
⦏exsvao_ixoverride_lemma⦎ =
   ⊢ ∀ V $∈⋎v x y v
     ⦁ ExsVaO (V2IxSet V, V, $∈⋎v) x y ∧ IxRan v ⊆ V
         ⇒ ExsVaO (V2IxSet V, V, $∈⋎v) (IxOverRide x v) (IxOverRide y v)

⦏exsvao_ixoverride_lemma2⦎ =
   ⊢ ∀ V W $∈⋎v x y v
     ⦁ ExsVaO (V2IxSet V, W, $∈⋎v) x y ∧ IxRan v ⊆ V
         ⇒ ExsVaO (V2IxSet V, W, $∈⋎v) (IxOverRide x v) (IxOverRide y v)
=TEX

\ignore{
=SML
local val _ = set_goal([], ⌜∀V $∈⋎v x y v⦁ ExsVaO (V2IxSet V, V, $∈⋎v) x y ∧ IxRan v ⊆ V 
	⇒ ExsVaO (V2IxSet V, V, $∈⋎v) (IxOverRide x v) (IxOverRide y v)⌝);
val _ = a (REPEAT ∀_tac
	THEN rewrite_tac (map get_spec
	[⌜ExsVaO⌝, ⌜IxO2⌝, ⌜ExsSRO⌝, ⌜ExtSRO⌝, ⌜EssSRO⌝, ⌜ConjOrder⌝, ⌜IxO⌝, ⌜OptO⌝, ⌜Pw⌝, ⌜V2IxSet⌝]));
val _ = a (CASES_T ⌜IxRan x ⊆ V ∧ IxRan y ⊆ V⌝ asm_tac
	THEN asm_rewrite_tac []
	THEN strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
val _ = a (DROP_NTH_ASM_T 4 strip_asm_tac);
val _ = a (LEMMA_T ⌜IxRan (IxOverRide x v) ⊆ V⌝ rewrite_thm_tac);
(* *** Goal "1.1" *** *)
val _ = a (lemma_tac ⌜IxRan (IxOverRide x v) ⊆ IxRan x ∪ IxRan v⌝ 
	THEN1 rewrite_tac [ixoverride_ixran_lemma]);
val _ = a (lemma_tac ⌜IxRan x ∪ IxRan v ⊆ V⌝
	THEN1 (PC_T1 "hol1" asm_prove_tac []));
val _ = a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B C⦁ A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C⌝]);
(* *** Goal "1.2" *** *)
val _ = a (LEMMA_T ⌜IxRan (IxOverRide y v) ⊆ V⌝ rewrite_thm_tac);
(* *** Goal "1.2.1" *** *)
val _ = a (lemma_tac ⌜IxRan (IxOverRide y v) ⊆ IxRan y ∪ IxRan v⌝ 
	THEN1 rewrite_tac [ixoverride_ixran_lemma]);
val _ = a (lemma_tac ⌜IxRan y ∪ IxRan v ⊆ V⌝
	THEN1 (PC_T1 "hol1" asm_prove_tac []));
val _ = a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B C⦁ A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C⌝]);
(* *** Goal "1.2.2" *** *)
val _ = a (strip_tac);
val _ = a (cases_tac ⌜IxOverRide x v x' = Undefined⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2.2.1" *** *)
val _ = a (lemma_tac ⌜IxOverRide y v x' = Undefined ⇒ IxOverRide x v x' = Undefined⌝
	THEN1 rewrite_tac [get_spec ⌜IxOverRide⌝, get_spec ⌜IxUd⌝]);
val _ = a (cases_tac ⌜v x' = Undefined⌝ THEN asm_rewrite_tac[]);
val _ = a (GET_NTH_ASM_T 7 ante_tac THEN rewrite_tac [get_spec ⌜IxDom⌝, sets_ext_clauses]
	THEN contr_tac THEN asm_fc_tac[]);
(* *** Goal "1.2.2.2" *** *)
val _ = a (asm_rewrite_tac[]);
val _ = a (spec_nth_asm_tac 6 ⌜x'⌝);
(* *** Goal "1.2.2.2.1" *** *)
val _ = a (LEMMA_T ⌜IxOverRide x v x' = v x' ∧ IxOverRide y v x' = v x'⌝ rewrite_thm_tac
	THEN1 (cases_tac ⌜v x' = Undefined⌝
		THEN asm_rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxUd⌝]));
val _ = a (DROP_NTH_ASM_T 9 ante_tac THEN rewrite_tac [get_spec ⌜IxDom⌝, sets_ext_clauses]);
val _ = a (strip_tac THEN spec_nth_asm_tac 1 ⌜x'⌝);
(* *** Goal "1.2.2.2.2" *** *)
val _ = a (cases_tac ⌜v x' = Undefined⌝);
(* *** Goal "1.2.2.2.2.1" *** *)
val _ = a (LEMMA_T ⌜IxOverRide x v x' = x x' ∧ IxOverRide y v x' = y x'⌝ rewrite_thm_tac
	THEN1 (asm_rewrite_tac [get_spec ⌜IxOverRide⌝, get_spec ⌜IxUd⌝]));
val _ = a (spec_nth_asm_tac 11 ⌜x'⌝ THEN asm_rewrite_tac []);
(* *** Goal "1.2.2.2.2.2" *** *)
val _ = a (LEMMA_T ⌜IxOverRide x v x' = v x' ∧ IxOverRide y v x' = v x'⌝ rewrite_thm_tac
	THEN1 (asm_rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxUd⌝]));
(* *** Goal "2" *** *)
val _ = a (cases_tac ⌜IxRan (IxOverRide y v) ⊆ V⌝	
	THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
in val exsvao_ixoverride_lemma = save_pop_thm "exsvao_ixoverride_lemma";
end;

set_goal([], ⌜∀V W $∈⋎v x y v⦁ ExsVaO (V2IxSet V, W, $∈⋎v) x y ∧ IxRan v ⊆ V 
	⇒ ExsVaO (V2IxSet V, W, $∈⋎v) (IxOverRide x v) (IxOverRide y v)⌝);
val _ = a (REPEAT ∀_tac
	THEN rewrite_tac (map get_spec
	[⌜ExsVaO⌝, ⌜IxO2⌝, ⌜ExsSRO⌝, ⌜ExtSRO⌝, ⌜EssSRO⌝, ⌜ConjOrder⌝, ⌜IxO⌝, ⌜OptO⌝, ⌜Pw⌝, ⌜V2IxSet⌝]));
val _ = a (CASES_T ⌜IxRan x ⊆ V ∧ IxRan y ⊆ V⌝ asm_tac
	THEN asm_rewrite_tac []
	THEN strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
val _ = a (DROP_NTH_ASM_T 4 strip_asm_tac);
val _ = a (LEMMA_T ⌜IxRan (IxOverRide x v) ⊆ V⌝ rewrite_thm_tac);
(* *** Goal "1.1" *** *)
val _ = a (lemma_tac ⌜IxRan (IxOverRide x v) ⊆ IxRan x ∪ IxRan v⌝ 
	THEN1 rewrite_tac [ixoverride_ixran_lemma]);
val _ = a (lemma_tac ⌜IxRan x ∪ IxRan v ⊆ V⌝
	THEN1 (PC_T1 "hol1" asm_prove_tac []));
val _ = a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B C⦁ A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C⌝]);
(* *** Goal "1.2" *** *)
val _ = a (LEMMA_T ⌜IxRan (IxOverRide y v) ⊆ V⌝ rewrite_thm_tac);
(* *** Goal "1.2.1" *** *)
val _ = a (lemma_tac ⌜IxRan (IxOverRide y v) ⊆ IxRan y ∪ IxRan v⌝ 
	THEN1 rewrite_tac [ixoverride_ixran_lemma]);
val _ = a (lemma_tac ⌜IxRan y ∪ IxRan v ⊆ V⌝
	THEN1 (PC_T1 "hol1" asm_prove_tac []));
val _ = a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B C⦁ A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C⌝]);
(* *** Goal "1.2.2" *** *)
val _ = a (strip_tac);
val _ = a (cases_tac ⌜IxOverRide x v x' = Undefined⌝ THEN asm_rewrite_tac[]);
val _ = a (lemma_tac ⌜IxOverRide y v x' = Undefined ⇒ IxOverRide x v x' = Undefined⌝
	THEN1 rewrite_tac [get_spec ⌜IxOverRide⌝, get_spec ⌜IxUd⌝]);
(* *** Goal "1.2.2.1" *** *)
val _ = a (cases_tac ⌜v x' = Undefined⌝ THEN asm_rewrite_tac[]);
val _ = a (GET_NTH_ASM_T 7 ante_tac THEN rewrite_tac [get_spec ⌜IxDom⌝, sets_ext_clauses]
	THEN contr_tac THEN asm_fc_tac[]);
(* *** Goal "1.2.2.2" *** *)
val _ = a (asm_rewrite_tac[]);
val _ = a (spec_nth_asm_tac 6 ⌜x'⌝);
(* *** Goal "1.2.2.2.1" *** *)
val _ = a (LEMMA_T ⌜IxOverRide x v x' = v x' ∧ IxOverRide y v x' = v x'⌝ rewrite_thm_tac
	THEN1 (cases_tac ⌜v x' = Undefined⌝
		THEN asm_rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxUd⌝]));
val _ = a (DROP_NTH_ASM_T 9 ante_tac THEN rewrite_tac [get_spec ⌜IxDom⌝, sets_ext_clauses]);
val _ = a (strip_tac THEN spec_nth_asm_tac 1 ⌜x'⌝);
(* *** Goal "1.2.2.2.2" *** *)
val _ = a (cases_tac ⌜v x' = Undefined⌝);
(* *** Goal "1.2.2.2.2.1" *** *)
val _ = a (LEMMA_T ⌜IxOverRide x v x' = x x' ∧ IxOverRide y v x' = y x'⌝ rewrite_thm_tac
	THEN1 (asm_rewrite_tac [get_spec ⌜IxOverRide⌝, get_spec ⌜IxUd⌝]));
val _ = a (spec_nth_asm_tac 11 ⌜x'⌝ THEN asm_rewrite_tac []);
(* *** Goal "1.2.2.2.2.2" *** *)
val _ = a (LEMMA_T ⌜IxOverRide x v x' = v x' ∧ IxOverRide y v x' = v x'⌝ rewrite_thm_tac
	THEN1 (asm_rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxUd⌝]));
(* *** Goal "2" *** *)
val _ = a (cases_tac ⌜IxRan (IxOverRide y v) ⊆ V⌝	
	THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
val exsvao_ixoverride_lemma2 = save_pop_thm "exsvao_ixoverride_lemma2";
=TEX
}%ignore

\subsection{Monotonicity Results}

First we prove the monotonicity of {\it EvalForm}.

=GFT
⦏evalcf_ftv_increasing_lemma⦎ =
   ⊢ Increasing (SetO $≤⋎t⋎4) $≤⋎t⋎4 EvalCf_ftv
=TEX

\ignore{
=SML
set_goal([], ⌜Increasing (SetO $≤⋎t⋎4) $≤⋎t⋎4 EvalCf_ftv⌝);
a (rewrite_tac (map get_spec [⌜Increasing⌝]));
a (rewrite_tac [get_spec ⌜EvalCf_ftv⌝]);
a (REPEAT strip_tac THEN bc_tac [rewrite_rule [pure_rewrite_rule [get_spec ⌜CRpoU⌝, get_spec ⌜CRpo⌝] ≤⋎t⋎4_crpou_thm, get_spec ⌜RpoU⌝] 		(∀_elim ⌜$≤⋎t⋎4⌝ (rewrite_rule [get_spec ⌜Increasing⌝] lub_increasing2_lemma))]);
a (rewrite_tac (map get_spec [⌜SetO2⌝]));
a (REPEAT strip_tac THEN var_elim_nth_asm_tac 1);
(* *** Goal "1" *** *)
a (∃_tac ⌜fTrue⌝ THEN rewrite_tac[]);
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [get_spec ⌜SetO⌝])));
a (asm_fc_tac []);
a (REPEAT_N 2 (POP_ASM_T ante_tac));
a (strip_asm_tac (∀_elim ⌜y'⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a (∃_tac ⌜fTrue⌝ THEN rewrite_tac[]);
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [get_spec ⌜SetO⌝])));
a (asm_fc_tac []);
a (REPEAT_N 2 (POP_ASM_T ante_tac));
a (strip_asm_tac (∀_elim ⌜y'⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "3" *** *)
a (∃_tac ⌜fFalse⌝ THEN rewrite_tac[]);
a (DROP_NTH_ASM_T 3 (strip_asm_tac o (rewrite_rule [get_spec ⌜SetO⌝])));
a (contr_tac THEN asm_fc_tac[]);
(* *** Goal "3.1" *** *)
a (REPEAT_N 2 (DROP_NTH_ASM_T 6 ante_tac));
a (REPEAT_N 2 (POP_ASM_T ante_tac));
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "3.2" *** *)
a (REPEAT_N 2 (DROP_NTH_ASM_T 6 ante_tac));
a (REPEAT_N 2 (POP_ASM_T ante_tac));
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[]
	THEN REPEAT strip_tac);
val evalcf_ftv_increasing_lemma = save_pop_thm "evalcf_ftv_increasing_lemma";
=TEX
}%ignore

=GFT
⦏evalaf_increasing_lemma⦎ =
   ⊢ ∀ tr g⦁ CRpoU tr ⇒ Increasing (StO tr) (RvO tr) (EvalAf tr g)
=TEX

\ignore{
=SML
local val _ = set_goal([], ⌜∀ tr g⦁ CRpoU tr ⇒ Increasing (StO tr) (RvO tr) (EvalAf tr g)⌝);
val _ = a (rewrite_tac (map get_spec [⌜Increasing⌝, ⌜EvalAf⌝, ⌜StO⌝, ⌜RvO⌝,
	⌜Pw⌝, ⌜DerivedOrder⌝, ⌜IsEO⌝, ⌜DpoEO⌝, ⌜dpoUdef⌝, ⌜dpoOdef⌝])
	THEN REPEAT strip_tac);
val _ = a (fc_tac [crpou_fc_clauses]);
val _ = a (rewrite_tac [let_def]);
val _ = a (CASES_T ⌜AfMem g ∈ IxDom x' ∧ AfSet g ∈ IxDom x'⌝ asm_rewrite_thm_tac);
in val evalaf_increasing_lemma = pop_thm();
end;
=TEX
}%ignore

To get a monotonicity result for the semantics of first order logic it is necessary to adjust the type of the semantic function.

The function which we wish to be monotonic is the mapping for each fixed domain of discourse and each particular formula, which take a membership structure (an interpretation of set theory over the gived domain) and returns the relation represented by the formula in that context.

The following function accepts one compound argument containing the relevent context and yields a function which we expect to be monotonic:

ⓈHOLCONST
│ ⦏MonoEvalForm⦎ : 't CFE × 't REL × 'a SET × GS → ('a, 't) BR → ('a, 't) RV
├───────────
│ ∀c r s g ris⦁ MonoEvalForm (c, r, s, g) ris = EvalForm (c, r, (s, ris)) g
■

ⓈHOLCONST
│ ⦏MonoEvalForm2⦎ : 't CFE × 't REL × 'a SET × GS → ('a, 't) BR → ('a, 't) RV
├───────────
│ ∀c r s g ris⦁ MonoEvalForm2 (c, r, s, g) ris = EvalForm2 (c, r, (s, ris)) g
■

=GFT
⦏monoevalform_increasing_lemma⦎ =
   ⊢ ∀ c r s g
     ⦁ CRpoU r ∧ Increasing (SetO r) r c
         ⇒ Increasing (Pw (Pw r)) (RvO r) (MonoEvalForm (c, r, s, g))

⦏evalform_increasing_thm⦎ =
   ⊢ ∀ c r s g
     ⦁ CRpoU r ∧ Increasing (SetO r) r c
         ⇒ Increasing (Pw (Pw r)) (RvO r) (λ ris⦁ EvalForm (c, r, s, ris) g)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀c r s g⦁ CRpoU r ∧ Increasing (SetO r) r c
	⇒ Increasing (Pw (Pw r)) (RvO r) (MonoEvalForm (c,r,s,g))⌝);
a (REPEAT strip_tac);
a (sc2_induction_tac ⌜g⌝ THEN_TRY asm_rewrite_tac[]);
a (rewrite_tac ((map get_spec [⌜Increasing⌝, ⌜MonoEvalForm⌝, ⌜RvO⌝, ⌜RvIsO⌝])@[evalformfunct_thm2])
	THEN REPEAT strip_tac);
a (cases_tac ⌜t ∈ Syntax⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
val _ = a (cases_tac ⌜IsAf t⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
val _ = a (fc_tac [inst_type_rule [(ⓣ'a⌝, ⓣ'b⌝), (ⓣ'b⌝, ⓣ'a⌝)] evalaf_increasing_lemma]);
val _ = a (spec_nth_asm_tac 1 ⌜t⌝ THEN fc_tac [get_spec ⌜Increasing⌝]);
val _ = a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec⌜StO⌝,get_spec⌜RvO⌝,
	get_spec ⌜DerivedOrder⌝] THEN strip_tac);
val _ = a (LIST_SPEC_NTH_ASM_T 1 [⌜(s,x)⌝, ⌜(s,y)⌝] ante_tac
	THEN rewrite_tac[]
	THEN strip_tac);
(* *** Goal "1.2" *** *)
val _ = a (rewrite_tac ((map get_spec [⌜Pw⌝, ⌜X⋎g⌝, ⌜EvalCf⌝])@[let_def]));
val _ = a (strip_tac THEN FC_T bc_tac [get_spec ⌜Increasing⌝]);
val _ = a (rewrite_tac [get_spec ⌜SetO⌝] THEN REPEAT strip_tac);
(* *** Goal "1.2.1" *** *)
val _ = a (GET_NTH_ASM_T 4 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
val _ = a (∃_tac ⌜EvalForm (c, r, s, y) a (IxOverRide x' v)⌝
	THEN strip_tac);
(* *** Goal "1.2.1.1" *** *)
val _ = a (∃_tac ⌜EvalForm (c, r, s, y) a⌝);
val _ = a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[get_spec ⌜FunImage⌝]);
val _ = a (∃_tac ⌜a⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2.1.2" *** *)
val _ = a (asm_rewrite_tac[]);
val _ = a (GET_NTH_ASM_T 1 (rewrite_thm_tac o eq_sym_rule));
val _ = a (lemma_tac ⌜tc ScPrec2 a t⌝);
(* *** Goal "1.2.1.2.1" *** *)
val _ = a (fc_tac [syntax_cases_thm]);
val _ = a (all_fc_tac [scprec2_fc_clauses2]);
val _ = a (fc_tac [tc_incr_thm]);
(* *** Goal "1.2.1.2.2" *** *)
val _ = a (all_asm_fc_tac[]);
val _ = a (fc_tac[get_spec ⌜Increasing⌝]);
val _ = a (GET_NTH_ASM_T 1 ante_tac THEN rewrite_tac [get_spec ⌜RvIsO⌝, get_spec ⌜RvO⌝]
	THEN STRIP_T (fn x => fc_tac[x]));
val _ = a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜MonoEvalForm⌝, get_spec ⌜Pw⌝]
	THEN STRIP_T rewrite_thm_tac);
(* *** Goal "1.2.2" *** *)
val _ = a (GET_NTH_ASM_T 4 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
val _ = a (∃_tac ⌜EvalForm (c, r, s, x) a (IxOverRide x' v)⌝
	THEN strip_tac);
(* *** Goal "1.2.2.1" *** *)
val _ = a (∃_tac ⌜EvalForm (c, r, s, x) a⌝);
val _ = a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[get_spec ⌜FunImage⌝]);
val _ = a (∃_tac ⌜a⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2.2.2" *** *)
val _ = a (asm_rewrite_tac[]);
val _ = a (GET_NTH_ASM_T 1 (rewrite_thm_tac o eq_sym_rule));
val _ = a (lemma_tac ⌜tc ScPrec2 a t⌝);
(* *** Goal "1.2.2.2.1" *** *)
val _ = a (fc_tac [syntax_cases_thm]);
val _ = a (all_fc_tac [scprec2_fc_clauses2]);
val _ = a (fc_tac [tc_incr_thm]);
(* *** Goal "1.2.2.2.2" *** *)
val _ = a (all_asm_fc_tac[]);
val _ = a (fc_tac[get_spec ⌜Increasing⌝]);
val _ = a (GET_NTH_ASM_T 1 ante_tac THEN rewrite_tac [get_spec ⌜RvIsO⌝, get_spec ⌜RvO⌝]
	THEN STRIP_T (fn x => fc_tac[x]));
val _ = a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜MonoEvalForm⌝, get_spec ⌜Pw⌝]
	THEN STRIP_T rewrite_thm_tac);
(* *** Goal "2" *** *)
val _ = a (fc_tac [inst_type_rule [(ⓣ'a⌝, ⓣ'b⌝), (ⓣGS → 'b OPT⌝, ⓣ'a⌝)] pw_crpou_thm]);
val _ = a (fc_tac [crpou_fc_clauses] THEN asm_rewrite_tac[]);
val monoevalform_increasing_lemma = pop_thm();
=IGN
stop;

set_goal ([], ⌜∀c r s g⦁ CRpoU r ∧ Increasing (SetO r) r c
	⇒ Increasing (Pw (Pw r)) (RvO r) (MonoEvalForm2 (c,r,s,g))⌝);
a (REPEAT strip_tac);
a (sc2_induction_tac ⌜g⌝ THEN_TRY asm_rewrite_tac[]);
a (rewrite_tac ((map get_spec [⌜Increasing⌝, ⌜MonoEvalForm2⌝, ⌜RvO⌝, ⌜RvIsO⌝, ⌜EvalForm2⌝, ⌜Pw⌝])@[])
	THEN REPEAT strip_tac);
a (cond_cases_tac ⌜t ∈ Syntax⌝);

(* *** Goal "1" *** *)
val _ = a (cases_tac ⌜IsAf t⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
val _ = a (fc_tac [inst_type_rule [(ⓣ'a⌝, ⓣ'b⌝), (ⓣ'b⌝, ⓣ'a⌝)] evalaf_increasing_lemma]);
val _ = a (spec_nth_asm_tac 1 ⌜t⌝ THEN fc_tac [get_spec ⌜Increasing⌝]);
val _ = a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec⌜StO⌝,get_spec⌜RvO⌝,
	get_spec ⌜DerivedOrder⌝] THEN strip_tac);
val _ = a (LIST_SPEC_NTH_ASM_T 1 [⌜(s,x)⌝, ⌜(s,y)⌝] ante_tac
	THEN rewrite_tac[]
	THEN strip_tac);
(* *** Goal "1.2" *** *)
val _ = a (rewrite_tac ((map get_spec [⌜Pw⌝, ⌜X⋎g⌝, ⌜EvalCf⌝])@[let_def]));
val _ = a (strip_tac THEN FC_T bc_tac [get_spec ⌜Increasing⌝]);
val _ = a (rewrite_tac [get_spec ⌜SetO⌝] THEN REPEAT strip_tac);
(* *** Goal "1.2.1" *** *)
val _ = a (GET_NTH_ASM_T 4 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
val _ = a (∃_tac ⌜EvalForm (c, r, s, y) a (IxOverRide x' v)⌝
	THEN strip_tac);
(* *** Goal "1.2.1.1" *** *)
val _ = a (∃_tac ⌜EvalForm (c, r, s, y) a⌝);
val _ = a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[get_spec ⌜FunImage⌝]);
val _ = a (∃_tac ⌜a⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2.1.2" *** *)
val _ = a (asm_rewrite_tac[]);
val _ = a (GET_NTH_ASM_T 1 (rewrite_thm_tac o eq_sym_rule));
val _ = a (lemma_tac ⌜tc ScPrec2 a t⌝);
(* *** Goal "1.2.1.2.1" *** *)
val _ = a (fc_tac [syntax_cases_thm]);
val _ = a (all_fc_tac [scprec2_fc_clauses2]);
val _ = a (fc_tac [tc_incr_thm]);
(* *** Goal "1.2.1.2.2" *** *)
val _ = a (all_asm_fc_tac[]);
val _ = a (fc_tac[get_spec ⌜Increasing⌝]);
val _ = a (GET_NTH_ASM_T 1 ante_tac THEN rewrite_tac [get_spec ⌜RvIsO⌝, get_spec ⌜RvO⌝]
	THEN STRIP_T (fn x => fc_tac[x]));
val _ = a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜MonoEvalForm⌝, get_spec ⌜Pw⌝]
	THEN STRIP_T rewrite_thm_tac);
(* *** Goal "1.2.2" *** *)
val _ = a (GET_NTH_ASM_T 4 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
val _ = a (∃_tac ⌜EvalForm (c, r, s, x) a (IxOverRide x' v)⌝
	THEN strip_tac);
(* *** Goal "1.2.2.1" *** *)
val _ = a (∃_tac ⌜EvalForm (c, r, s, x) a⌝);
val _ = a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[get_spec ⌜FunImage⌝]);
val _ = a (∃_tac ⌜a⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2.2.2" *** *)
val _ = a (asm_rewrite_tac[]);
val _ = a (GET_NTH_ASM_T 1 (rewrite_thm_tac o eq_sym_rule));
val _ = a (lemma_tac ⌜tc ScPrec2 a t⌝);
(* *** Goal "1.2.2.2.1" *** *)
val _ = a (fc_tac [syntax_cases_thm]);
val _ = a (all_fc_tac [scprec2_fc_clauses2]);
val _ = a (fc_tac [tc_incr_thm]);
(* *** Goal "1.2.2.2.2" *** *)
val _ = a (all_asm_fc_tac[]);
val _ = a (fc_tac[get_spec ⌜Increasing⌝]);
val _ = a (GET_NTH_ASM_T 1 ante_tac THEN rewrite_tac [get_spec ⌜RvIsO⌝, get_spec ⌜RvO⌝]
	THEN STRIP_T (fn x => fc_tac[x]));
val _ = a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜MonoEvalForm⌝, get_spec ⌜Pw⌝]
	THEN STRIP_T rewrite_thm_tac);
(* *** Goal "2" *** *)
set_labelled_goal "2";
val _ = a (fc_tac [inst_type_rule [(ⓣ'a⌝, ⓣ'b⌝), (ⓣGS → 'b OPT⌝, ⓣ'a⌝)] pw_crpou_thm]);
val _ = a (fc_tac [crpou_fc_clauses] THEN asm_rewrite_tac[]);
val monoevalform2_increasing_lemma = pop_thm();

local val _ = set_goal([], ⌜∀ c r s g
     ⦁ CRpoU r ∧ Increasing (SetO r) r c
         ⇒ Increasing (Pw (Pw r)) (RvO r) (λris⦁EvalForm (c, r, s, ris) g)⌝);
val _ = a (REPEAT ∀_tac);
val _ = a (lemma_tac ⌜(λris⦁EvalForm (c, r, s, ris) g) = MonoEvalForm (c, r, s, g)⌝
	THEN1 rewrite_tac [ext_thm, get_spec ⌜MonoEvalForm⌝]);
val _ = a (asm_rewrite_tac[monoevalform_increasing_lemma]);
in val evalform_increasing_thm = save_pop_thm "evalform_increasing_thm";
end;

stop;


=TEX
}%ignore

We will also need to prove monotonicity of formula evaluation relative to the extension and essences of the variable assignment providing the context for the evaluation.

=GFT
⦏evalform_increasing_thm2⦎ =
   ⊢ ∀ (V, $∈⋎v) g
     ⦁ V ⊆ Syntax ∧ g ∈ Syntax
         ⇒ Increasing
           (ExsVaO (V2IxSet V, V, $∈⋎v))
           $≤⋎t⋎4
           (EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, $∈⋎v) g)

⦏evalform_increasing_thm3⦎ =
   ⊢ ∀ V $∈⋎v g
     ⦁ V ⊆ Syntax ∧ g ∈ Syntax
         ⇒ Increasing
           (ExsVaO (V2IxSet (V ∪ {∅⋎g}), V ∪ {∅⋎g}, $∈⋎v))
           $≤⋎t⋎4
           (EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, $∈⋎v) g)
=TEX
=GFT
⦏evalform_increasing_thm4⦎ =
   ⊢ ∀ V W $∈⋎v g
     ⦁ V ⊆ W ∧ V ⊆ Syntax ∧ g ∈ Syntax
         ⇒ Increasing
           (ExsVaO (V2IxSet W, W, $∈⋎v))
           $≤⋎t⋎4
           (EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, $∈⋎v) g)
=TEX

\ignore{
=SML
set_goal([], ⌜∀(V, $∈⋎v) g⦁ V ⊆ Syntax ∧ g ∈ Syntax
	⇒ Increasing (ExsVaO (V2IxSet V, (V, $∈⋎v))) $≤⋎t⋎4 (EvalForm (EvalCf_ftv, $≤⋎t⋎4, (V, $∈⋎v)) g)⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$⊆⌝] THEN strip_tac THEN POP_ASM_T ante_tac);
val _ = a (sc2_induction_tac ⌜g⌝);
val _ = a (strip_tac THEN asm_rewrite_tac ((map get_spec [⌜Increasing⌝, ⌜$⊆⌝]) @ [])
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac [evalformfunct_thm2, let_def]);
val _ = a (cases_tac ⌜IsAf t⌝ THEN asm_rewrite_tac[let_def]);
(* *** Goal "1" *** *)
val _ = a (rewrite_tac [get_spec ⌜EvalAf⌝, let_def]);
val _ = a (GET_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule (map get_spec
	[⌜ExsVaO⌝, ⌜IxO2⌝, ⌜ExsSRO⌝, ⌜ExtSRO⌝, ⌜EssSRO⌝, ⌜ConjOrder⌝, ⌜IxO⌝, ⌜OptO⌝, ⌜Pw⌝, ⌜V2IxSet⌝])))
	THEN asm_rewrite_tac[]);
val _ = a (POP_ASM_T ante_tac THEN POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜$⊆⌝] THEN REPEAT strip_tac);
val _ = a (CASES_T ⌜AfMem t ∈ IxDom y ∧ AfSet t ∈ IxDom y⌝ asm_tac THEN asm_rewrite_tac[]);
val _ = a (POP_ASM_T ante_tac THEN (SYM_ASMS_T rewrite_tac)
	THEN rewrite_tac [get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
	THEN strip_tac);
val _ = a (spec_nth_asm_tac 5 ⌜AfMem t⌝);
val _ = a (spec_nth_asm_tac 8 ⌜AfSet t⌝);
val _ = a (rewrite_tac[get_spec ⌜IxVal⌝]);
val _ = a (DROP_NTH_ASM_T 5 discard_tac THEN DROP_NTH_ASM_T 1 discard_tac);
val _ = a (spec_nth_asm_tac 3 ⌜ValueOf (x (AfSet t))⌝
	THEN1 (fc_tac [ix_valueof_ran_lemma] THEN asm_fc_tac[]));
val _ = a (spec_nth_asm_tac 2 ⌜ValueOf (y (AfMem t))⌝
	THEN1 (fc_tac [ix_valueof_ran_lemma] THEN asm_fc_tac[]));
val _ = a (all_fc_tac [≤⋎t⋎4_trans_thm]);
(* *** Goal "2" *** *)
val _ = a (rewrite_tac [get_spec ⌜EvalCf⌝, let_def]);
val _ = a (bc_tac [rewrite_rule [get_spec ⌜Increasing⌝] evalcf_ftv_increasing_lemma]);
val _ = a (rewrite_tac [get_spec ⌜SetO⌝] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
val _ = a (∃_tac ⌜rv (IxOverRide y v)⌝ THEN strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1.1" *** *)
val _ = a (∃_tac ⌜rv⌝ THEN ∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
val _ = a (GET_NTH_ASM_T 6 (strip_asm_tac o (rewrite_rule (map get_spec
	[⌜ExsVaO⌝, ⌜IxO2⌝, ⌜ExsSRO⌝, ⌜ExtSRO⌝, ⌜EssSRO⌝, ⌜ConjOrder⌝, ⌜IxO⌝, ⌜OptO⌝, ⌜Pw⌝, ⌜V2IxSet⌝])))
	THEN_TRY asm_rewrite_tac[]);
val _ = a (DROP_NTH_ASM_T 8 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
val _ = a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [get_spec ⌜X⋎g⌝])));
val _ = a (fc_tac [syntax_cases_fc_clauses]);
val _ = a (lemma_tac ⌜ScPrec2 a t ∧ a ∈ Syntax⌝);
val _ = a (all_fc_tac [is_fc_clauses]);
val _ = a (GET_NTH_ASM_T 4 (asm_tac o (rewrite_rule [asm_rule ⌜t = MkCf (vars, fs)⌝])));
val _ = a (ASM_FC_T rewrite_tac []);
val _ = a (ufc_tac [scprec2_fc_clauses] THEN asm_ufc_tac[]);
(* *** Goal "2.1.2.2" *** *)
val _ = a (lemma_tac ⌜tc ScPrec2 a t⌝ THEN1 fc_tac [tc_incr_thm]);
val _ = a (all_asm_fc_tac[]);
val _ = a (POP_ASM_T ante_tac THEN asm_rewrite_tac[get_spec ⌜Increasing⌝] THEN strip_tac);
val _ = a (LEMMA_T ⌜ExsVaO (V2IxSet V, V, $∈⋎v) (IxOverRide x v) (IxOverRide y v)⌝
	(asm_tac)
	THEN1 (all_fc_tac [exsvao_ixoverride_lemma]));
val _ = a (list_spec_nth_asm_tac 2 [⌜IxOverRide x v⌝, ⌜IxOverRide y v⌝]);
val _ = a (rewrite_tac [eq_sym_rule (asm_rule ⌜EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, $∈⋎v) a = rv⌝)]);
val _ = a strip_tac;
(* *** Goal "2.2" *** *)
val _ = a (∃_tac ⌜rv (IxOverRide x v)⌝ THEN strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.1" *** *)
val _ = a (∃_tac ⌜rv⌝ THEN ∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
val _ = a (GET_NTH_ASM_T 6 (strip_asm_tac o (rewrite_rule (map get_spec
	[⌜ExsVaO⌝, ⌜IxO2⌝, ⌜ExsSRO⌝, ⌜ExtSRO⌝, ⌜EssSRO⌝, ⌜ConjOrder⌝, ⌜IxO⌝, ⌜OptO⌝, ⌜Pw⌝, ⌜V2IxSet⌝])))
	THEN_TRY asm_rewrite_tac[]);
val _ = a (DROP_NTH_ASM_T 8 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
val _ = a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [get_spec ⌜X⋎g⌝])));
val _ = a (fc_tac [syntax_cases_fc_clauses]);
val _ = a (lemma_tac ⌜ScPrec2 a t ∧ a ∈ Syntax⌝);
(* *** Goal "2.2.2.1" *** *)
val _ = a (all_fc_tac [is_fc_clauses]);
val _ = a (GET_NTH_ASM_T 4 (asm_tac o (rewrite_rule [asm_rule ⌜t = MkCf (vars, fs)⌝])));
val _ = a (ASM_FC_T rewrite_tac []);
val _ = a (ufc_tac [scprec2_fc_clauses] THEN asm_ufc_tac[]);
(* *** Goal "2.2.2.2" *** *)
val _ = a (lemma_tac ⌜tc ScPrec2 a t⌝ THEN1 fc_tac [tc_incr_thm]);
val _ = a (all_asm_fc_tac[]);
val _ = a (POP_ASM_T ante_tac THEN asm_rewrite_tac[get_spec ⌜Increasing⌝] THEN strip_tac);
val _ = a (LEMMA_T ⌜ExsVaO (V2IxSet V, V, $∈⋎v) (IxOverRide x v) (IxOverRide y v)⌝
	(asm_tac)
	THEN1 (all_fc_tac [exsvao_ixoverride_lemma]));
val _ = a (list_spec_nth_asm_tac 2 [⌜IxOverRide x v⌝, ⌜IxOverRide y v⌝]);
val _ = a (rewrite_tac [eq_sym_rule (asm_rule ⌜EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, $∈⋎v) a = rv⌝)]);
val _ = a strip_tac;
val evalform_increasing_thm2 = save_pop_thm "evalform_increasing_thm2";

set_goal([], ⌜∀V $∈⋎v g⦁ V ⊆ Syntax ∧ g ∈ Syntax
	⇒ Increasing (ExsVaO (V2IxSet (V ∪ {∅⋎g}), (V ∪ {∅⋎g}, $∈⋎v))) $≤⋎t⋎4 (EvalForm (EvalCf_ftv, $≤⋎t⋎4, (V, $∈⋎v)) g)⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$⊆⌝] THEN strip_tac THEN POP_ASM_T ante_tac);
val _ = a (sc2_induction_tac ⌜g⌝);
val _ = a (strip_tac THEN asm_rewrite_tac ((map get_spec [⌜Increasing⌝, ⌜$⊆⌝]) @ [])
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac [evalformfunct_thm2, let_def]);
val _ = a (cases_tac ⌜IsAf t⌝ THEN asm_rewrite_tac[let_def]);
(* *** Goal "1" *** *)
val _ = a (rewrite_tac [get_spec ⌜EvalAf⌝, let_def]);
val _ = a (GET_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule (map get_spec
	[⌜ExsVaO⌝, ⌜IxO2⌝, ⌜ExsSRO⌝, ⌜ExtSRO⌝, ⌜EssSRO⌝, ⌜ConjOrder⌝, ⌜IxO⌝, ⌜OptO⌝, ⌜Pw⌝, ⌜V2IxSet⌝])))
	THEN asm_rewrite_tac[]);
val _ = a (POP_ASM_T ante_tac THEN POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜$⊆⌝] THEN REPEAT strip_tac);
val _ = a (CASES_T ⌜AfMem t ∈ IxDom y ∧ AfSet t ∈ IxDom y⌝ asm_tac THEN asm_rewrite_tac[]);
val _ = a (POP_ASM_T ante_tac THEN (SYM_ASMS_T rewrite_tac)
	THEN rewrite_tac [get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
	THEN strip_tac);
val _ = a (spec_nth_asm_tac 5 ⌜AfMem t⌝);
val _ = a (spec_nth_asm_tac 8 ⌜AfSet t⌝);
val _ = a (rewrite_tac[get_spec ⌜IxVal⌝]);
val _ = a (DROP_NTH_ASM_T 5 discard_tac THEN DROP_NTH_ASM_T 1 discard_tac);
val _ = a (spec_nth_asm_tac 3 ⌜ValueOf (x (AfSet t))⌝
	THEN1 (fc_tac [ix_valueof_ran_lemma] THEN asm_fc_tac[] THEN asm_fc_tac[]));
val _ = a (spec_nth_asm_tac 2 ⌜ValueOf (y (AfMem t))⌝
	THEN1 (fc_tac [ix_valueof_ran_lemma] THEN asm_fc_tac[] THEN asm_fc_tac[]));
val _ = a (all_fc_tac [≤⋎t⋎4_trans_thm]);
(* *** Goal "2" *** *)
val _ = a (rewrite_tac [get_spec ⌜EvalCf⌝, let_def]);
val _ = a (bc_tac [rewrite_rule [get_spec ⌜Increasing⌝] evalcf_ftv_increasing_lemma]);
val _ = a (rewrite_tac [get_spec ⌜SetO⌝] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
val _ = a (∃_tac ⌜rv (IxOverRide y v)⌝ THEN strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1.1" *** *)
val _ = a (∃_tac ⌜rv⌝ THEN ∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
val _ = a (GET_NTH_ASM_T 6 (strip_asm_tac o (rewrite_rule (map get_spec
	[⌜ExsVaO⌝, ⌜IxO2⌝, ⌜ExsSRO⌝, ⌜ExtSRO⌝, ⌜EssSRO⌝, ⌜ConjOrder⌝, ⌜IxO⌝, ⌜OptO⌝, ⌜Pw⌝, ⌜V2IxSet⌝])))
	THEN_TRY asm_rewrite_tac[]);
val _ = a (DROP_NTH_ASM_T 8 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
val _ = a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [get_spec ⌜X⋎g⌝])));
val _ = a (fc_tac [syntax_cases_fc_clauses]);
val _ = a (lemma_tac ⌜ScPrec2 a t ∧ a ∈ Syntax⌝);
(* *** Goal "2.1.2.1" *** *)
val _ = a (all_fc_tac [is_fc_clauses]);
val _ = a (GET_NTH_ASM_T 4 (asm_tac o (rewrite_rule [asm_rule ⌜t = MkCf (vars, fs)⌝])));
val _ = a (ASM_FC_T rewrite_tac []);
val _ = a (ufc_tac [scprec2_fc_clauses] THEN asm_ufc_tac[]);
(* *** Goal "2.1.2.2" *** *)
val _ = a (lemma_tac ⌜tc ScPrec2 a t⌝ THEN1 fc_tac [tc_incr_thm]);
val _ = a (all_asm_fc_tac[]);
val _ = a (POP_ASM_T ante_tac THEN asm_rewrite_tac[get_spec ⌜Increasing⌝] THEN strip_tac);
a (lemma_tac ⌜IxRan v ⊆ V ∪ {∅⋎g}⌝ THEN1
	(GET_ASM_T ⌜IxRan v ⊆ V⌝ ante_tac THEN PC_T1 "hol1" prove_tac[]));
a (LEMMA_T ⌜ExsVaO (V2IxSet (V ∪ {∅⋎g}), V ∪ {∅⋎g}, $∈⋎v) (IxOverRide x v) (IxOverRide y v)⌝
	(asm_tac) THEN1 (all_fc_tac [exsvao_ixoverride_lemma2]));
val _ = a (list_spec_nth_asm_tac 3 [⌜IxOverRide x v⌝, ⌜IxOverRide y v⌝]);
val _ = a (rewrite_tac [eq_sym_rule (asm_rule ⌜EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, $∈⋎v) a = rv⌝)]);
val _ = a strip_tac;
(* *** Goal "2.2" *** *)
val _ = a (∃_tac ⌜rv (IxOverRide x v)⌝ THEN strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.1" *** *)
val _ = a (∃_tac ⌜rv⌝ THEN ∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
val _ = a (GET_NTH_ASM_T 6 (strip_asm_tac o (rewrite_rule (map get_spec
	[⌜ExsVaO⌝, ⌜IxO2⌝, ⌜ExsSRO⌝, ⌜ExtSRO⌝, ⌜EssSRO⌝, ⌜ConjOrder⌝, ⌜IxO⌝, ⌜OptO⌝, ⌜Pw⌝, ⌜V2IxSet⌝])))
	THEN_TRY asm_rewrite_tac[]);
val _ = a (DROP_NTH_ASM_T 8 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
val _ = a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [get_spec ⌜X⋎g⌝])));
val _ = a (fc_tac [syntax_cases_fc_clauses]);
val _ = a (lemma_tac ⌜ScPrec2 a t ∧ a ∈ Syntax⌝);
val _ = a (all_fc_tac [is_fc_clauses]);
val _ = a (GET_NTH_ASM_T 4 (asm_tac o (rewrite_rule [asm_rule ⌜t = MkCf (vars, fs)⌝])));
val _ = a (ASM_FC_T rewrite_tac []);
val _ = a (ufc_tac [scprec2_fc_clauses] THEN asm_ufc_tac[]);
(* *** Goal "2.2.2.2" *** *)
val _ = a (lemma_tac ⌜tc ScPrec2 a t⌝ THEN1 fc_tac [tc_incr_thm]);
val _ = a (all_asm_fc_tac[]);
val _ = a (POP_ASM_T ante_tac THEN asm_rewrite_tac[get_spec ⌜Increasing⌝] THEN strip_tac);
a (lemma_tac ⌜IxRan v ⊆ V ∪ {∅⋎g}⌝ THEN1
	(GET_ASM_T ⌜IxRan v ⊆ V⌝ ante_tac THEN PC_T1 "hol1" prove_tac[]));
val _ = a (LEMMA_T ⌜ExsVaO (V2IxSet (V ∪ {∅⋎g}), V ∪ {∅⋎g}, $∈⋎v) (IxOverRide x v) (IxOverRide y v)⌝
	(asm_tac)
	THEN1 (all_fc_tac [exsvao_ixoverride_lemma2]));
val _ = a (list_spec_nth_asm_tac 3 [⌜IxOverRide x v⌝, ⌜IxOverRide y v⌝]);
val _ = a (rewrite_tac [eq_sym_rule (asm_rule ⌜EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, $∈⋎v) a = rv⌝)]);
val _ = a strip_tac;
val evalform_increasing_thm3 = save_pop_thm "evalform_increasing_thm3";

set_goal([], ⌜∀V W $∈⋎v g⦁ V ⊆ W ∧ V ⊆ Syntax ∧ g ∈ Syntax
	⇒ Increasing (ExsVaO (V2IxSet W, (W, $∈⋎v))) $≤⋎t⋎4 (EvalForm (EvalCf_ftv, $≤⋎t⋎4, (V, $∈⋎v)) g)⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$⊆⌝] THEN strip_tac THEN POP_ASM_T ante_tac);
val _ = a (sc2_induction_tac ⌜g⌝);
val _ = a (strip_tac THEN asm_rewrite_tac ((map get_spec [⌜Increasing⌝, ⌜$⊆⌝]) @ [])
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac [evalformfunct_thm2, let_def]);
val _ = a (cases_tac ⌜IsAf t⌝ THEN asm_rewrite_tac[let_def]);
(* *** Goal "1" *** *)
val _ = a (rewrite_tac [get_spec ⌜EvalAf⌝, let_def]);
val _ = a (GET_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule (map get_spec
	[⌜ExsVaO⌝, ⌜IxO2⌝, ⌜ExsSRO⌝, ⌜ExtSRO⌝, ⌜EssSRO⌝, ⌜ConjOrder⌝, ⌜IxO⌝, ⌜OptO⌝, ⌜Pw⌝, ⌜V2IxSet⌝])))
	THEN asm_rewrite_tac[]);
val _ = a (POP_ASM_T ante_tac THEN POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜$⊆⌝] THEN REPEAT strip_tac);
val _ = a (CASES_T ⌜AfMem t ∈ IxDom y ∧ AfSet t ∈ IxDom y⌝ asm_tac THEN asm_rewrite_tac[]);
val _ = a (POP_ASM_T ante_tac THEN (SYM_ASMS_T rewrite_tac)
	THEN rewrite_tac [get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
	THEN strip_tac);
val _ = a (spec_nth_asm_tac 5 ⌜AfMem t⌝);
val _ = a (spec_nth_asm_tac 8 ⌜AfSet t⌝);
val _ = a (rewrite_tac[get_spec ⌜IxVal⌝]);
val _ = a (DROP_NTH_ASM_T 5 discard_tac THEN DROP_NTH_ASM_T 1 discard_tac);
val _ = a (spec_nth_asm_tac 3 ⌜ValueOf (x (AfSet t))⌝
	THEN1 (fc_tac [ix_valueof_ran_lemma] THEN asm_fc_tac[] THEN asm_fc_tac[]));
val _ = a (spec_nth_asm_tac 2 ⌜ValueOf (y (AfMem t))⌝
	THEN1 (fc_tac [ix_valueof_ran_lemma] THEN asm_fc_tac[] THEN asm_fc_tac[]));
val _ = a (all_fc_tac [≤⋎t⋎4_trans_thm]);
(* *** Goal "2" *** *)
val _ = a (rewrite_tac [get_spec ⌜EvalCf⌝, let_def]);
val _ = a (bc_tac [rewrite_rule [get_spec ⌜Increasing⌝] evalcf_ftv_increasing_lemma]);
val _ = a (rewrite_tac [get_spec ⌜SetO⌝] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
val _ = a (∃_tac ⌜rv (IxOverRide y v)⌝ THEN strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1.1" *** *)
val _ = a (∃_tac ⌜rv⌝ THEN ∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
val _ = a (GET_NTH_ASM_T 6 (strip_asm_tac o (rewrite_rule (map get_spec
	[⌜ExsVaO⌝, ⌜IxO2⌝, ⌜ExsSRO⌝, ⌜ExtSRO⌝, ⌜EssSRO⌝, ⌜ConjOrder⌝, ⌜IxO⌝, ⌜OptO⌝, ⌜Pw⌝, ⌜V2IxSet⌝])))
	THEN_TRY asm_rewrite_tac[]);
val _ = a (DROP_NTH_ASM_T 8 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
val _ = a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [get_spec ⌜X⋎g⌝])));
val _ = a (fc_tac [syntax_cases_fc_clauses]);
val _ = a (lemma_tac ⌜ScPrec2 a t ∧ a ∈ Syntax⌝);
(* *** Goal "2.1.2.1" *** *)
val _ = a (all_fc_tac [is_fc_clauses]);
val _ = a (GET_NTH_ASM_T 4 (asm_tac o (rewrite_rule [asm_rule ⌜t = MkCf (vars, fs)⌝])));
val _ = a (ASM_FC_T rewrite_tac []);
val _ = a (ufc_tac [scprec2_fc_clauses] THEN asm_ufc_tac[]);
(* *** Goal "2.1.2.2" *** *)
val _ = a (lemma_tac ⌜tc ScPrec2 a t⌝ THEN1 fc_tac [tc_incr_thm]);
val _ = a (all_asm_fc_tac[]);
val _ = a (POP_ASM_T ante_tac THEN asm_rewrite_tac[get_spec ⌜Increasing⌝] THEN strip_tac);
a (lemma_tac ⌜IxRan v ⊆ W⌝ THEN1
	(GET_ASM_T ⌜IxRan v ⊆ V⌝ ante_tac
	THEN GET_ASM_T ⌜∀ x:GS⦁ x ∈ V ⇒ x ∈ W⌝ ante_tac
	THEN PC_T1 "hol1" prove_tac[]));
a (LEMMA_T ⌜ExsVaO (V2IxSet W, W, $∈⋎v) (IxOverRide x v) (IxOverRide y v)⌝
	(asm_tac) THEN1 (all_fc_tac [exsvao_ixoverride_lemma2]));
val _ = a (list_spec_nth_asm_tac 3 [⌜IxOverRide x v⌝, ⌜IxOverRide y v⌝]);
val _ = a (rewrite_tac [eq_sym_rule (asm_rule ⌜EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, $∈⋎v) a = rv⌝)]);
val _ = a strip_tac;
(* *** Goal "2.2" *** *)
val _ = a (∃_tac ⌜rv (IxOverRide x v)⌝ THEN strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.1" *** *)
val _ = a (∃_tac ⌜rv⌝ THEN ∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
val _ = a (GET_NTH_ASM_T 6 (strip_asm_tac o (rewrite_rule (map get_spec
	[⌜ExsVaO⌝, ⌜IxO2⌝, ⌜ExsSRO⌝, ⌜ExtSRO⌝, ⌜EssSRO⌝, ⌜ConjOrder⌝, ⌜IxO⌝, ⌜OptO⌝, ⌜Pw⌝, ⌜V2IxSet⌝])))
	THEN_TRY asm_rewrite_tac[]);
val _ = a (DROP_NTH_ASM_T 8 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
val _ = a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [get_spec ⌜X⋎g⌝])));
val _ = a (fc_tac [syntax_cases_fc_clauses]);
val _ = a (lemma_tac ⌜ScPrec2 a t ∧ a ∈ Syntax⌝);
val _ = a (all_fc_tac [is_fc_clauses]);
val _ = a (GET_NTH_ASM_T 4 (asm_tac o (rewrite_rule [asm_rule ⌜t = MkCf (vars, fs)⌝])));
val _ = a (ASM_FC_T rewrite_tac []);
val _ = a (ufc_tac [scprec2_fc_clauses] THEN asm_ufc_tac[]);
(* *** Goal "2.2.2.2" *** *)
val _ = a (lemma_tac ⌜tc ScPrec2 a t⌝ THEN1 fc_tac [tc_incr_thm]);
val _ = a (all_asm_fc_tac[]);
val _ = a (POP_ASM_T ante_tac THEN asm_rewrite_tac[get_spec ⌜Increasing⌝] THEN strip_tac);
a (lemma_tac ⌜IxRan v ⊆ W⌝ THEN1
	(GET_ASM_T ⌜IxRan v ⊆ V⌝ ante_tac
	THEN GET_ASM_T ⌜∀ x:GS⦁ x ∈ V ⇒ x ∈ W⌝ ante_tac
	THEN PC_T1 "hol1" prove_tac[]));
val _ = a (LEMMA_T ⌜ExsVaO (V2IxSet W, W, $∈⋎v) (IxOverRide x v) (IxOverRide y v)⌝
	(asm_tac)
	THEN1 (all_fc_tac [exsvao_ixoverride_lemma2]));
val _ = a (list_spec_nth_asm_tac 3 [⌜IxOverRide x v⌝, ⌜IxOverRide y v⌝]);
val _ = a (rewrite_tac [eq_sym_rule (asm_rule ⌜EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, $∈⋎v) a = rv⌝)]);
val _ = a strip_tac;
val evalform_increasing_thm4 = save_pop_thm "evalform_increasing_thm4";
=TEX
}%ignore

\section{EXTENSIONALITY}

\subsection{Extension and Essence, Compatibility and OverDefinedness}

The terminology is a bit uncertain here.
These lemmas about the semantics are proven in order to obtain extensionality results for fixed points of the semantic functor.

ⓈHOLCONST
│ ⦏Extension⦎ : (GS, FTV)BR → (GS, FTV)BR
├───────────
│ Extension = CombC
■

We now define a notion of `same extension' over some domain.

Two sets have the same extension over some domain if they have the same members in that domain.

ⓈHOLCONST
│ ⦏SameExt⦎ : GS SET → (GS, FTV)BR → GS → GS → BOOL
├───────────
│ ∀V r⦁ SameExt V r = λx y⦁ ∀z⦁ z ∈ V ⇒ r z x = r z y
■

ⓈHOLCONST
│ ⦏Essence⦎ : (GS, FTV)BR → (GS, FTV)BR
├───────────
│ Essence = CombI
■

Two sets have the same essence over some domain if they are members of the same sets in that domain.

ⓈHOLCONST
│ ⦏SameEss⦎ : GS SET → (GS, FTV)BR → GS → GS → BOOL
├───────────
│ ∀V r⦁ SameEss V r = λx y⦁  ∀z⦁ z ∈ V ⇒ r x z = r y z
■

=GFT
⦏sameext_equiv_thm⦎ =
   ⊢ ∀ V r⦁ Equiv (V, SameExt V r)

⦏sameess_equiv_thm⦎ =
   ⊢ ∀ V r⦁ Equiv (V, SameEss V r)

⦏sameext_refl_lemma⦎ =
   ⊢ ∀ V r x⦁ x ∈ V ⇒ SameExt V r x x

⦏sameess_refl_lemma⦎ =
   ⊢ ∀ V r x⦁ x ∈ V ⇒ SameEss V r x x

⦏sameext_sym_lemma⦎ =
   ⊢ ∀ V r x y⦁ x ∈ V ∧ y ∈ V ⇒ (SameExt V r x y ⇔ SameExt V r y x)

⦏sameess_sym_lemma⦎ =
   ⊢ ∀ V r x y⦁ x ∈ V ∧ y ∈ V ⇒ (SameEss V r x y ⇔ SameEss V r y x)
=TEX

=GFT
⦏evalform_ext_lemma⦎ =
   ⊢ ∀ V r
     ⦁ V ⊆ SetReps
         ⇒ (∀ z
         ⦁ z ∈ Syntax
             ⇒ (∀ x y
             ⦁ IxDom x = IxDom y
                   ∧ FreeVars z ⊆ IxDom x
                   ∧ IxRan x ⊆ V
                   ∧ IxRan y ⊆ V
                   ∧ (∀ v
                   ⦁ v ∈ IxDom x
                       ⇒ SameExt V r (IxVal x v) (IxVal y v)
                         ∧ SameEss V r (IxVal x v) (IxVal y v))
                 ⇒ EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) z x
                   = EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) z y))

=TEX

\ignore{
=SML
local val _ = set_goal ([], ⌜∀V r⦁ Equiv (V, (SameExt V r))⌝);
val _ = a (REPEAT ∀_tac
	THEN rewrite_tac (map get_spec [⌜SameExt⌝, ⌜Equiv⌝, ⌜Refl⌝, ⌜Sym⌝, ⌜Trans⌝])
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]
	THEN asm_rewrite_tac[]);
in val sameext_equiv_thm = save_pop_thm "sameext_equiv_thm";
end;

local val _ = set_goal ([], ⌜∀V r⦁ Equiv (V, (SameEss V r))⌝);
val _ = a (REPEAT ∀_tac
	THEN rewrite_tac (map get_spec [⌜SameEss⌝, ⌜Equiv⌝, ⌜Refl⌝, ⌜Sym⌝, ⌜Trans⌝])
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]
	THEN asm_rewrite_tac[]);
in val sameess_equiv_thm = save_pop_thm "sameess_equiv_thm";
end;

local val _ = set_goal ([], ⌜∀V r x⦁ x ∈ V ⇒ SameExt V r x x⌝);
val _ = a (REPEAT strip_tac);
val _ = a (lemma_tac ⌜Refl (V, SameExt V r)⌝
	THEN1 rewrite_tac [rewrite_rule [get_spec ⌜Equiv⌝] sameext_equiv_thm]);
val _ = a (fc_tac [get_spec ⌜Refl⌝] THEN asm_fc_tac[]);
in val sameext_refl_lemma = save_pop_thm "sameext_refl_lemma";
end;

local val _ = set_goal ([], ⌜∀V r x⦁ x ∈ V ⇒ SameEss V r x x⌝);
val _ = a (REPEAT strip_tac);
val _ = a (lemma_tac ⌜Refl (V, SameEss V r)⌝
	THEN1 rewrite_tac [rewrite_rule [get_spec ⌜Equiv⌝] sameess_equiv_thm]);
val _ = a (fc_tac [get_spec ⌜Refl⌝] THEN asm_fc_tac[]);
in val sameess_refl_lemma = save_pop_thm "sameess_refl_lemma";
end;

local val _ = set_goal ([], ⌜∀V r x y⦁ x ∈ V ∧ y ∈ V ⇒ (SameExt V r x y ⇔ SameExt V r y x)⌝);
val _ = a (REPEAT strip_tac);
val _ = a (lemma_tac ⌜Sym (V, SameExt V r)⌝
	THEN1 rewrite_tac [rewrite_rule [get_spec ⌜Equiv⌝] sameext_equiv_thm]);
val _ = a (fc_tac [get_spec ⌜Sym⌝] THEN all_asm_fc_tac[]);
val _ = a (lemma_tac ⌜Sym (V, SameExt V r)⌝
	THEN1 rewrite_tac [rewrite_rule [get_spec ⌜Equiv⌝] sameext_equiv_thm]);
val _ = a (fc_tac [get_spec ⌜Sym⌝]);
val _ = a (list_spec_nth_asm_tac 1 [⌜y⌝, ⌜x⌝]);
in val sameext_sym_lemma = save_pop_thm "sameext_sym_lemma";
end;

local val _ = set_goal ([], ⌜∀V r x y⦁ x ∈ V ∧ y ∈ V ⇒ (SameEss V r x y ⇔ SameEss V r y x)⌝);
val _ = a (REPEAT strip_tac);
val _ = a (lemma_tac ⌜Sym (V, SameEss V r)⌝
	THEN1 rewrite_tac [rewrite_rule [get_spec ⌜Equiv⌝] sameess_equiv_thm]);
val _ = a (fc_tac [get_spec ⌜Sym⌝] THEN all_asm_fc_tac[]);
val _ = a (lemma_tac ⌜Sym (V, SameEss V r)⌝
	THEN1 rewrite_tac [rewrite_rule [get_spec ⌜Equiv⌝] sameess_equiv_thm]);
val _ = a (fc_tac [get_spec ⌜Sym⌝]);
val _ = a (list_spec_nth_asm_tac 1 [⌜y⌝, ⌜x⌝]);
in val sameess_sym_lemma = save_pop_thm "samess_sym_lemma";
end;
=TEX
}%ignore

Unfortunaately that last lemma is too weak for the purposes for which is was intended.
To obtain a stronger lemma it is necessary to have concepts weaker than {\it SameExt} and {\it SameEss}, as follows:

To obtain a stronger lemma we define the notion of `compatible extension'.

Two sets have compatible extensions over some domain if they do not definitely disagree about what their members are, where a disagreement is definite if at some point either is overdefined or if neither is undefined.
This is defined in terms of compatibility of truth value sets, which is defined in \cite{rbjt025}.

ⓈHOLCONST
│ ⦏CompExt⦎ : GS SET → (GS, FTV)BR → GS → GS → BOOL
├───────────
│ ∀V r⦁ CompExt V r = λx y⦁ ∀z⦁ z ∈ V ⇒ {r z x; r z y} ∈ CompFTV
■

ⓈHOLCONST
│ ⦏CoCompExt⦎ : GS SET → (GS, FTV)BR → GS → GS → BOOL
├───────────
│ ∀V r⦁ CoCompExt V r = λx y⦁ ∀z⦁ z ∈ V ⇒ {r z x; r z y} ∈ CoCompFTV
■

Two sets have compatible essences over some domain if they do not definitely disagree about which sets they are members of.

ⓈHOLCONST
│ ⦏CompEss⦎ : GS SET → (GS, FTV)BR → GS → GS → BOOL
├───────────
│ ∀V r⦁ CompEss V r = λx y⦁ ∀z⦁ z ∈ V ⇒ {r x z; r y z} ∈ CompFTV
■

ⓈHOLCONST
│ ⦏CoCompEss⦎ : GS SET → (GS, FTV)BR → GS → GS → BOOL
├───────────
│ ∀V r⦁ CoCompEss V r = λx y⦁ ∀z⦁ z ∈ V ⇒ {r x z; r y z} ∈ CoCompFTV
■

We also need to be able to talk about relations which are nowhere overdefined.
In fact we need to be able to talk about parts of relations, e.g. particular extensions and essences in these terms.

The following is a property, either of an extension or an essence, which tells you whether it anwhere takes the value {\it fT}.
The property is parameterised by the domain of discourse.

ⓈHOLCONST
│ ⦏OverDefinedL⦎ : GS SET → (GS → FTV) → BOOL
├───────────
│ ∀V xe⦁ OverDefinedL V xe ⇔ ∃y⦁ y ∈ V ∧ xe y = fT
■

=GFT
⦏OverDefinedL_≤⋎t⋎4_lemma⦎ =
   ⊢ ∀ V xe1 xe2
     ⦁ ¬ OverDefinedL V xe1 ∧ PwS V $≤⋎t⋎4 xe2 xe1 ⇒ ¬ OverDefinedL V xe2
=TEX

\ignore{
=SML
set_goal([], ⌜∀V xe1 xe2⦁ ¬ OverDefinedL V xe1 ∧ PwS V $≤⋎t⋎4 xe2 xe1 ⇒ ¬ OverDefinedL V xe2⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜OverDefinedL⌝, get_spec ⌜PwS⌝]
	THEN contr_tac
	THEN asm_fc_tac[]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[ft_fb_thm]
	THEN contr_tac
	THEN asm_fc_tac[]);
val OverDefinedL_≤⋎t⋎4_lemma = save_pop_thm "OverDefinedL_≤⋎t⋎4_lemma";
=TEX
}%ignore

The following property of relations could have been defined in terms of the above, but actually it was defined first and is simpler left as it is.

ⓈHOLCONST
│ ⦏OverDefined⦎ : GS SET → (GS, FTV)BR → BOOL
├───────────
│ ∀V r⦁ OverDefined V r ⇔ ∃x y⦁ x ∈ V ∧ y ∈ V ∧ r x y = fT
■

ⓈHOLCONST
│ ⦏OverDefinedEss⦎ : GS SET → GS SET → (GS, FTV)BR → BOOL
├───────────
│ ∀V W r⦁ OverDefinedEss V W r ⇔ ∃x⦁ x ∈ V ∧ OverDefinedL W (Essence r x) 
■

ⓈHOLCONST
│ ⦏OverDefinedExt⦎ : GS SET → GS SET → (GS, FTV)BR → BOOL
├───────────
│ ∀V W r⦁ OverDefinedExt V W r ⇔ ∃x⦁ x ∈ V ∧ OverDefinedL W (Extension r x) 
■

and the duals:

ⓈHOLCONST
│ ⦏UnderDefinedL⦎ : GS SET → (GS → FTV) → BOOL
├───────────
│ ∀V xe⦁ UnderDefinedL V xe ⇔ ∃y⦁ y ∈ V ∧ xe y = fB
■

ⓈHOLCONST
│ ⦏UnderDefined⦎ : GS SET → (GS, FTV)BR → BOOL
├───────────
│ ∀V r⦁ UnderDefined V r ⇔ ∃x y⦁ x ∈ V ∧ y ∈ V ∧ r x y = fB
■

=GFT
⦏compext_refl_lemma⦎ =
   ⊢ ∀ V r x⦁ ¬ OverDefined V r ⇒ x ∈ V ⇒ CompExt V r x x

⦏cocompext_refl_lemma⦎ =
   ⊢ ∀ V r x⦁ ¬ UnderDefined V r ⇒ x ∈ V ⇒ CoCompExt V r x x
=TEX
=GFT
⦏compess_refl_lemma⦎ =
   ⊢ ∀ V r x⦁ ¬ OverDefined V r ⇒ x ∈ V ⇒ CompEss V r x x

⦏cocompess_refl_lemma⦎ =
   ⊢ ∀ V r x⦁ ¬ UnderDefined V r ⇒ x ∈ V ⇒ CoCompEss V r x x
=TEX
=GFT
⦏compext_sym_lemma⦎ =
   ⊢ ∀ V r
     ⦁ ¬ OverDefined V r
         ⇒ (∀ x y⦁ x ∈ V ∧ y ∈ V ⇒ (CompExt V r x y ⇔ CompExt V r y x))

⦏cocompext_sym_lemma⦎ =
   ⊢ ∀ V r
     ⦁ ¬ UnderDefined V r
         ⇒ (∀ x y⦁ x ∈ V ∧ y ∈ V ⇒ (CoCompExt V r x y ⇔ CoCompExt V r y x))
=TEX
=GFT
⦏compess_sym_lemma⦎ =
   ⊢ ∀ V r
     ⦁ ¬ OverDefined V r
         ⇒ (∀ x y⦁ x ∈ V ∧ y ∈ V ⇒ (CompEss V r x y ⇔ CompEss V r y x))

⦏cocompess_sym_lemma⦎ =
   ⊢ ∀ V r
     ⦁ ¬ UnderDefined V r
         ⇒ (∀ x y⦁ x ∈ V ∧ y ∈ V ⇒ (CoCompEss V r x y ⇔ CoCompEss V r y x))
=TEX

\ignore{
=SML
local val _ = set_goal ([], ⌜∀V r x⦁ ¬ OverDefined V r ⇒ x ∈ V ⇒ CompExt V r x x⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜OverDefined⌝, get_spec ⌜CompExt⌝, get_spec ⌜CompFTV⌝, let_def]
	THEN REPEAT_N 4 strip_tac);
val _ = a (spec_nth_asm_tac 3 ⌜z⌝);
val _ = a (spec_nth_asm_tac 1 ⌜x⌝);
val _ = a (strip_asm_tac (∀_elim ⌜r z x⌝ ftv_cases_thm)
	THEN asm_rewrite_tac[sets_ext_clauses, ∈_in_clauses]);
in val compext_refl_lemma = save_pop_thm "compext_refl_lemma";
end;

local val _ = set_goal ([], ⌜∀V r x⦁ ¬ UnderDefined V r ⇒ x ∈ V ⇒ CoCompExt V r x x⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜UnderDefined⌝, get_spec ⌜CoCompExt⌝, get_spec ⌜CoCompFTV⌝, let_def]
	THEN REPEAT_N 4 strip_tac);
val _ = a (spec_nth_asm_tac 3 ⌜z⌝);
val _ = a (spec_nth_asm_tac 1 ⌜x⌝);
val _ = a (strip_asm_tac (∀_elim ⌜r z x⌝ ftv_cases_thm)
	THEN asm_rewrite_tac[sets_ext_clauses, ∈_in_clauses]);
in val cocompext_refl_lemma = save_pop_thm "cocompext_refl_lemma";
end;

local val _ = set_goal ([], ⌜∀V r x⦁ ¬ OverDefined V r ⇒ x ∈ V ⇒ CompEss V r x x⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜OverDefined⌝, get_spec ⌜CompEss⌝, get_spec ⌜CompFTV⌝, let_def]
	THEN REPEAT_N 4 strip_tac);
val _ = a (spec_nth_asm_tac 3 ⌜x⌝);
val _ = a (spec_nth_asm_tac 1 ⌜z⌝);
val _ = a (strip_asm_tac (∀_elim ⌜r x z⌝ ftv_cases_thm)
	THEN asm_rewrite_tac[sets_ext_clauses, ∈_in_clauses]);
in val compess_refl_lemma = save_pop_thm "compess_refl_lemma";
end;

local val _ = set_goal ([], ⌜∀V r x⦁ ¬ UnderDefined V r ⇒ x ∈ V ⇒ CoCompEss V r x x⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜UnderDefined⌝, get_spec ⌜CoCompEss⌝, get_spec ⌜CoCompFTV⌝, let_def]
	THEN REPEAT_N 4 strip_tac);
val _ = a (spec_nth_asm_tac 3 ⌜x⌝);
val _ = a (spec_nth_asm_tac 1 ⌜z⌝);
val _ = a (strip_asm_tac (∀_elim ⌜r x z⌝ ftv_cases_thm)
	THEN asm_rewrite_tac[sets_ext_clauses, ∈_in_clauses]);
in val cocompess_refl_lemma = save_pop_thm "cocompess_refl_lemma";
end;

set_goal ([], ⌜∀V r⦁ ¬ OverDefined V r ⇒ ∀x y⦁ x ∈ V ∧ y ∈ V ⇒ (CompExt V r x y ⇔ CompExt V r y x)⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜OverDefined⌝]
	THEN REPEAT (⇒_tac ORELSE ∀_tac)
	THEN rewrite_tac [get_spec ⌜CompExt⌝, compftv_lemma, let_def]
	THEN REPEAT_N 6 strip_tac);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 2 ⌜z⌝ THEN contr_tac);
(* *** Goal "2" *** *)
val _ = a (spec_nth_asm_tac 2 ⌜z⌝
	THEN rewrite_tac[∈_in_clauses]
	THEN REPEAT_N 4 (POP_ASM_T rewrite_thm_tac));
(* *** Goal "3" *** *)
a (spec_nth_asm_tac 2 ⌜z⌝ THEN contr_tac);
(* *** Goal "4" *** *)
val _ = a (spec_nth_asm_tac 2 ⌜z⌝
	THEN rewrite_tac[∈_in_clauses]
	THEN REPEAT_N 4 (POP_ASM_T rewrite_thm_tac));
val compext_sym_lemma = save_pop_thm "compext_sym_lemma";

set_goal ([], ⌜∀V r⦁ ¬ UnderDefined V r ⇒ ∀x y⦁ x ∈ V ∧ y ∈ V ⇒ (CoCompExt V r x y ⇔ CoCompExt V r y x)⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜UnderDefined⌝]
	THEN REPEAT (⇒_tac ORELSE ∀_tac)
	THEN rewrite_tac [get_spec ⌜CoCompExt⌝, cocompftv_lemma, let_def]
	THEN REPEAT_N 6 strip_tac);
a (spec_nth_asm_tac 2 ⌜z⌝ THEN contr_tac);
a (spec_nth_asm_tac 2 ⌜z⌝ THEN contr_tac);
a (spec_nth_asm_tac 2 ⌜z⌝ THEN contr_tac);
a (spec_nth_asm_tac 2 ⌜z⌝ THEN contr_tac);
val cocompext_sym_lemma = save_pop_thm "cocompext_sym_lemma";

local val _ = set_goal ([], ⌜∀V r⦁ ¬ OverDefined V r ⇒ ∀x y⦁ x ∈ V ∧ y ∈ V ⇒ (CompEss V r x y ⇔ CompEss V r y x)⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜OverDefined⌝]
	THEN REPEAT (⇒_tac ORELSE ∀_tac)
	THEN rewrite_tac [get_spec ⌜CompEss⌝, let_def]
	THEN contr_tac);
(* *** Goal "1" *** *)
val _ = a (spec_nth_asm_tac 3 ⌜z⌝);
val _ = a (REPEAT_N 2 (POP_ASM_T ante_tac));
val _ = a (LEMMA_T ⌜{r y z; r x z} = {r x z; r y z}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" prove_tac[]);
(* *** Goal "2" *** *)
val _ = a (spec_nth_asm_tac 3 ⌜z⌝);
val _ = a (REPEAT_N 2 (POP_ASM_T ante_tac));
val _ = a (LEMMA_T ⌜{r y z; r x z} = {r x z; r y z}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" prove_tac[]);
in val compess_sym_lemma = save_pop_thm "compess_sym_lemma";
end;

local val _ = set_goal ([], ⌜∀V r⦁ ¬ UnderDefined V r ⇒ ∀x y⦁ x ∈ V ∧ y ∈ V ⇒ (CoCompEss V r x y ⇔ CoCompEss V r y x)⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜UnderDefined⌝]
	THEN REPEAT (⇒_tac ORELSE ∀_tac)
	THEN rewrite_tac [get_spec ⌜CoCompEss⌝, let_def]
	THEN contr_tac);
(* *** Goal "1" *** *)
val _ = a (spec_nth_asm_tac 3 ⌜z⌝);
val _ = a (REPEAT_N 2 (POP_ASM_T ante_tac));
val _ = a (LEMMA_T ⌜{r y z; r x z} = {r x z; r y z}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" prove_tac[]);
(* *** Goal "2" *** *)
val _ = a (spec_nth_asm_tac 3 ⌜z⌝);
val _ = a (REPEAT_N 2 (POP_ASM_T ante_tac));
val _ = a (LEMMA_T ⌜{r y z; r x z} = {r x z; r y z}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" prove_tac[]);
in val cocompess_sym_lemma = save_pop_thm "cocompess_sym_lemma";
end;
=TEX
}%ignore

The following condition expresses the possibility that two set representatives might end up representing the same set after further iterations of the semantic functor in approaching a least fixed point.

This intended for use in proving that a total least fixed point will always be extensional, through a lemma which states that, under certain conditions, elements which are compatible will still have the same extension after one further application of the semantic functor.

To be compatible two elements must have the same essences and extensions, but this does not suffice.
It is also necessary to state that there is no disagreement about whether the element to which they might be refined by iteration of the semantic functor is a member of itself.

ⓈHOLCONST
│ ⦏Compatible⦎ : GS SET → (GS, FTV)BR → GS → GS → BOOL
├───────────
│ ∀V r⦁ Compatible V r = λx y⦁ {r x y; r y x; r x x; r y y} ∈ CompFTV
│		∧ CompEss V r x y ∧ CompExt V r x y 
■

=GFT
⦏Compatible_lemma1⦎ =
   ⊢ ∀ V r x y⦁ Compatible V r x y ⇔ {r x y; r y x; r x x; r y y} ∈ CompFTV
		∧ (∀ z⦁ z ∈ V ⇒
			  {r z x; r z y} ∈ CompFTV
			∧ {r x z; r y z} ∈ CompFTV)
=TEX

\ignore{
=SML
set_goal([], ⌜∀V r x y⦁ Compatible V r x y ⇔
	{r x y; r y x; r x x; r y y} ∈ CompFTV
	∧ ∀z⦁ z ∈ V ⇒ {r z x; r z y} ∈ CompFTV ∧ {r x z; r y z} ∈ CompFTV⌝);
a (REPEAT ∀_tac THEN rewrite_tac (map get_spec [⌜Compatible⌝, ⌜CompEss⌝, ⌜CompExt⌝])
	THEN REPEAT strip_tac
	THEN asm_fc_tac []
	THEN_TRY asm_rewrite_tac []);
val Compatible_lemma1 = save_pop_thm "Compatible_lemma1";

=IGN
set_flag("subgoal_package_quiet", false);

set_goal([], ⌜∀V r x y⦁ Increasing $≤⋎ (λs⦁ ¬ s ∈ CompFTV)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [Compatible_lemma1]
	THEN REPEAT strip_tac);

=TEX
}%ignore


\section{PROOF CONTEXTS}

=SML
(* add_pc_thms "'infos" [evalcf_ftv_ft_lemma, evalcf_ftv_fb_lemma]; *)

(* add_pc_thms "'infos" [get_spec ⌜Extension⌝, get_spec ⌜Essence⌝]; *)
commit_pc "'infos";

force_new_pc "⦏infos⦎";
merge_pcs ["misc2", "'infos"] "infos";
commit_pc "infos";

force_new_pc "⦏infos1⦎";
merge_pcs ["misc21", "'infos"] "infos1";
commit_pc "infos1";
=TEX

=SML
set_flag ("subgoal_package_quiet", false);
=TEX

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{infos.th}
%\include{sfp.th}
}  %\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
