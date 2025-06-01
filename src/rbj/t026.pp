=IGN
$Id: t026.doc,v 1.20 2012/08/11 21:01:52 rbj Exp $
open_theory "ifos";

set_flag ("pp_use_alias", true);

set_merge_pcs ["misc21", "'ifos"];
=TEX
\documentclass[11pt,a4paper]{article}
%\usepackage{latexsym}
%\usepackage{ProofPower}
\usepackage{rbj}
\usepackage{graphics}
%\ftlinepenalty=9999
\usepackage{A4}

%\def\ExpName{\mbox{{\sf exp}
%\def\Exp#1{\ExpName(#1)}

\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{Infinitarily Definable Sets}
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
This is my third approach to set theory conceived as a maximal consistent theory of comprehension.
It differs from the previous attempt (in t024) by simplification of the treatment of infinitary logic, allowing only a single binary relation.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created: 2008/07/11

Last Change $ $Date: 2012/08/11 21:01:52 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t026.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t026.pdf}

$ $Id: t026.doc,v 1.20 2012/08/11 21:01:52 rbj Exp $ $

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

The idea is to obtain exotic models of set theory using definability in first order set theory as a source of candidate sets.

To ensure that we get all the well-founded sets we start with definability in infinitary first order set theory ({\it ifos}).
Given any membership structure, i.e. a domain of discourse and a membership relation over that domain, each formula of {\it ifos} with one free variable will define a subset of the domain of discourse (you may prefer to think of these as classes, since in the domains we work with they will mostly have very large size).

If we take as our domain of discourse the formulae of {\it ifos}, then the semantics of {\it ifos} provides a functor which given one membership relation over that domain will yield another membership relation.
If this functor had a fixed point then it would provide a rich interpretation of {\it ifos}.
Over the entire set of formulae of {\it ifos} there can be no such fixed point, for the resulting interpretation would include paradoxical collections such as the Russell set.

It seems clear however that some subsets of the formulae of {\it ifos} do have fixed points under the semantics of {\it ifos}.
For example, the formulae denoting well-founded sets, or those denoting well-founded sets or their complements.

It is the purpose of this work to see whether obtain models for rich non-well-founded set theories can be obtained in this way.

\section{INFINITARY SET THEORY}

=SML
open_theory "misc2";
force_new_theory "⦏ifos⦎";
force_new_pc ⦏"'ifos"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'ifos";
set_merge_pcs ["misc21", "'ifos"];
=TEX

\subsection{Syntax}

\subsubsection{Constructors, Discriminators and Destructors}

Preliminary to presenting the inductive definition of the required classes we define the nuts and bolts operations on the required syntactic entities (some of which will be used in the inductive definition).

A constructor puts together some syntactic entity from its constituents, discriminators distinguist between the different kinds of entity and destructors take them apart.

``Atomic'' formulae are just membership predicates.
So its just an ordered pair of `terms' (and in our case that just means variable names)  tagged with a zero.

ⓈHOLCONST
│ ⦏MkAf⦎ : GS × GS → GS
├───────────
│ ∀lr⦁ MkAf lr = (Nat⋎g 0) ↦⋎g ((Fst lr) ↦⋎g (Snd lr))
■

ⓈHOLCONST
│ ⦏IsAf⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsAf t ⇔ fst t = (Nat⋎g 0)
■

ⓈHOLCONST
│ ⦏AfSet⦎ : GS → GS
├───────────
│  AfSet = λx⦁ fst(snd x)
■

ⓈHOLCONST
│ ⦏AfMem⦎ : GS → GS
├───────────
│  AfMem = λx⦁ snd(snd x)
■

ⓈHOLCONST
│ ⦏MkCf⦎ : GS × GS → GS
├───────────
│ ∀vc⦁ MkCf vc = (Nat⋎g 1) ↦⋎g ((Fst vc) ↦⋎g (Snd vc))
■

ⓈHOLCONST
│ ⦏IsCf⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsCf t ⇔ fst t = (Nat⋎g 1)
■

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

⦏Is_not_fc_clauses⦎ =
   ⊢ (∀ x⦁ IsAf x ⇒ ¬ IsCf x) ∧ (∀ x⦁ IsCf x ⇒ ¬ IsAf x)
=TEX

\ignore{
=SML
set_flag("subgoal_package_quiet", true);

set_goal([], ⌜(∀x⦁ IsAf (MkAf x))
	∧ (∀x⦁ ¬ IsAf (MkCf x))
	∧ (∀x⦁ ¬ IsCf (MkAf x))
	∧ (∀x⦁ IsCf (MkCf x))
	⌝);
a (rewrite_tac [get_spec ⌜IsAf⌝,
	get_spec ⌜MkAf⌝,
	get_spec ⌜IsCf⌝,
	get_spec ⌜MkCf⌝]);
val Is_clauses = pop_thm();

add_pc_thms "'ifos" (map get_spec [] @ [ord_nat_thm, Is_clauses]);
set_merge_pcs ["misc21", "'ifos"];

set_goal ([], ⌜
	(∀x⦁ IsAf x ⇒ ¬ IsCf x)
∧	(∀x⦁ IsCf x ⇒ ¬ IsAf x)
⌝);
a (rewrite_tac (map get_spec [⌜IsAf⌝, ⌜IsCf⌝]));
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

\subsubsection{The Inductive Definition of Syntax}

This is accomplished by defining the required closure condition (closure under the above constructors for arguments of the right kind) and then taking the intersection of all sets which satisfy the closure condition.

The closure condition is:

ⓈHOLCONST
│ ⦏RepClosed⦎: GS SET → BOOL
├───────────
│ ∀ s⦁ RepClosed s ⇔
│	(∀ s2 m⦁ MkAf (s2, m) ∈ s)
│∧	(∀ vars fs⦁ X⋎g fs ⊆ s ⇒ MkCf (vars, fs) ∈ s)
■

The dual concept is also used:

ⓈHOLCONST
│ ⦏RepOpen⦎: GS SET → BOOL
├───────────
│ ∀ s⦁ RepOpen s ⇔ (∀ vars fs⦁ MkCf (vars, fs) ∈ s ⇒ X⋎g fs ⊆ s)
■

The well-formed syntax is then the smallest set closed under these constructions.

ⓈHOLCONST
│ ⦏Syntax⦎ : GS SET
├───────────
│ Syntax = ⋂{x | RepClosed x}
■

The dual probably isn't useful but I've put it in for symmetry.

ⓈHOLCONST
│ ⦏CoSyntax⦎ : GS SET
├───────────
│ CoSyntax = ⋃{x | RepOpen x}
■

=GFT
⦏syntax_⊆_repclosed_thm⦎ =
   ⊢ ∀ s⦁ RepClosed s ⇒ Syntax ⊆ s

⦏repopen_⊆_cosyntax_thm⦎ =
   ⊢ ∀ s⦁ RepOpen s ⇒ s ⊆ CoSyntax
=TEX

\ignore{
=SML
local val _ = set_goal([], ⌜∀s⦁ RepClosed s ⇒ Syntax ⊆ s⌝);
val _ = a (rewrite_tac [get_spec ⌜Syntax⌝]
	THEN REPEAT strip_tac THEN asm_fc_tac[]);
in val syntax_⊆_repclosed_thm = pop_thm();
end;

local val _ = set_goal([], ⌜∀s⦁ RepOpen s ⇒ s ⊆ CoSyntax⌝);
val _ = a (rewrite_tac [get_spec ⌜CoSyntax⌝]
	THEN REPEAT strip_tac);
val _ = a (∃_tac ⌜s⌝ THEN contr_tac);
in val repopen_⊆_cosyntax_thm = pop_thm();
end;
=TEX
}%ignore

This is an ``inductive datatype'' so we should expect the usual kinds of theorems.

Informally these should say:

\begin{itemize}
\item Syntax is closed under the two constructors.
\item The syntax constructors are injections, have disjoint ranges, and partition the syntax. 
\item Any syntactic property which is preserved by the constructors (i.e. is true of any construction if it is true of all its syntactic constituents) is true of everything in syntax (this is an induction principle).
\item A recursion theorem which supports definition of primitive recursive functions over the syntax.
\end{itemize}

=GFT
⦏repclosed_syntax_lemma⦎ =
	⊢ RepClosed Syntax

⦏repclosed_syntax_thm⦎ =
	⊢ (∀ s m⦁ MkAf (s, m) ∈ Syntax)
       ∧ (∀ vars fs
       ⦁ (∀ x⦁ x ∈ X⋎g fs ⇒ x ∈ Syntax) ⇒ MkCf (vars, fs) ∈ Syntax)

⦏repclosed_syntax_thm2⦎ =
   ⊢ (∀ s2 m⦁ MkAf (s2, m) ∈ Syntax)
       ∧ (∀ vars fs⦁ (∀ x⦁ x ∈⋎g fs ⇒ x ∈ Syntax) ⇒ MkCf (vars, fs) ∈ Syntax)

⦏repclosed_syntax_lemma1⦎ =
	⊢ ∀ s⦁ RepClosed s ⇒ Syntax ⊆ s

⦏repclosed_syntax_lemma2⦎ =
	⊢ ∀ p⦁ RepClosed {x|p x} ⇒ (∀ x⦁ x ∈ Syntax ⇒ p x)
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

val repclosed_syntax_thm = save_thm ("repclosed_syntax_thm",
	rewrite_rule [get_spec ⌜RepClosed⌝] repclosed_syntax_lemma);

val repclosed_syntax_thm2 = save_thm ("repclosed_syntax_thm2",
	rewrite_rule [get_spec ⌜X⋎g⌝] repclosed_syntax_thm);

local val _ = set_goal([], ⌜∀s⦁ RepClosed s ⇒ Syntax ⊆ s⌝);
val _ = a (rewrite_tac [get_spec ⌜Syntax⌝]
	THEN prove_tac[]);
in val repclosed_syntax_lemma1 = save_pop_thm "repclosed_syntax_lemma1";
end;

local val _ = set_goal([], ⌜∀p⦁ RepClosed {x | p x} ⇒ ∀x⦁ x ∈ Syntax ⇒ p x⌝);
val _ = a (rewrite_tac [get_spec ⌜Syntax⌝] THEN REPEAT strip_tac);
val _ = a (asm_fc_tac[]);
in val repclosed_syntax_lemma2 = save_pop_thm "repclosed_syntax_lemma2";
end;
=TEX
}%ignore

\subsubsection{Recursion and Induction Principles and Rules}

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

⦏well_founded_tcScPrec_thm⦎ =
	⊢ well_founded (tc ScPrec)
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

local val _ = set_goal([], ⌜well_founded (tc ScPrec)⌝);
val _ = a (asm_tac well_founded_ScPrec_thm);
val _ = a (fc_tac [wf_tc_wf_thm]);
in val well_founded_tcScPrec_thm = save_pop_thm ("well_founded_tcScPrec_thm");
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
val ⦏SC_INDUCTION_T⦎ = WFCV_INDUCTION_T well_founded_ScPrec_thm;
val ⦏sc_induction_tac⦎ = wfcv_induction_tac well_founded_ScPrec_thm;
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

⦏syn_proj_clauses⦎ =
    ⊢ (∀ s m⦁ AfSet (MkAf (s, m)) = s)
       ∧ (∀ s m⦁ AfMem (MkAf (s, m)) = m)
       ∧ (∀ v f⦁ CfVars (MkCf (v, f)) = v)
       ∧ (∀ v f⦁ CfForms (MkCf (v, f)) = f)

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

⦏syn_con_neq_clauses⦎ =
   ⊢ ∀ x y⦁ ¬ MkAf x = MkCf y

⦏syn_comp_fc_clauses⦎ =
   ⊢ ∀ v f⦁ MkCf (v, f) ∈ Syntax ⇒ (∀ y⦁ y ∈⋎g f ⇒ y ∈ Syntax)

⦏scprec_fc_clauses⦎ =
   ⊢ ∀ α γ vars fs⦁ γ ∈ Syntax ⇒ γ = MkCf (vars, fs) ∧ α ∈⋎g fs ⇒ ScPrec α γ

⦏scprec2_fc_clauses⦎ =
   ⊢ ∀ α γ vars fs⦁ γ = MkCf (vars, fs) ∧ α ∈⋎g fs ⇒ ScPrec2 α γ

⦏scprec_fc_clauses2⦎ =
   ⊢ ∀ t⦁ t ∈ Syntax ⇒ IsCf t ⇒ (∀ f⦁ f ∈⋎g CfForms t ⇒ ScPrec f t)

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

local val _ = set_goal ([], ⌜∀x⦁ x ∈ Syntax ⇒
	(¬ IsAf x ⇒ IsCf x)
∧	(¬ IsCf x ⇒ IsAf x)⌝);
val _ = a (strip_tac THEN strip_tac
	THEN FC_T (MAP_EVERY ante_tac) [syntax_cases_thm]
	THEN (rewrite_tac (map get_spec [⌜IsAf⌝, ⌜IsCf⌝])));
val _ = a (REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]
	THEN contr_tac THEN FC_T (MAP_EVERY ante_tac) [natg_one_one_thm]
	THEN_TRY PC_T1 "lin_arith" rewrite_tac[]);
in val syntax_cases_fc_clauses = save_pop_thm "syntax_cases_fc_clauses";
end;

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

=IGN
set_goal([], ⌜∀x⦁
	(IsAf x ⇒ ∃s m⦁ x = MkAf (s, m))
∧	(IsCf x ⇒ ∃vars fs⦁ x = MkCf (vars, fs))
⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜IsAf⌝, get_spec ⌜MkAf⌝]);
val _ = a (asm_tac (syntax_disj_thm));
val _ = a (asm_fc_tac[] THEN asm_rewrite_tac [Is_clauses]);
(* *** Goal "1" *** *)
val _ = a (∃_tac ⌜s⌝ THEN ∃_tac ⌜m⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
val _ = a (∃_tac ⌜vars⌝ THEN ∃_tac ⌜fs⌝ THEN asm_rewrite_tac[]);
in val is_fc_clauses1 = save_pop_thm "is_fc_clauses1";
end;

=SML
set_goal([], ⌜¬ ∅⋎g ∈ Syntax⌝);
a (LEMMA_T ⌜∀x⦁ x ∈ Syntax ⇒ ¬ x = ∅⋎g⌝ (fn x => contr_tac THEN fc_tac [x])
	THEN strip_tac);
a (sc_induction_tac ⌜x⌝ THEN strip_tac);
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

local val _ = set_goal([], ⌜(∀s m⦁ AfSet (MkAf (s, m)) = s)
	∧	(∀s m⦁ AfMem (MkAf (s, m)) = m)
	∧	(∀v f⦁ CfVars (MkCf (v, f)) = v)
	∧	(∀v f⦁ CfForms (MkCf (v, f)) = f)
⌝);
val _ = a (rewrite_tac (map get_spec [
	⌜MkAf⌝, ⌜MkCf⌝,
	⌜AfSet⌝, ⌜AfMem⌝, ⌜CfVars⌝, ⌜CfForms⌝]));
in val syn_proj_clauses = save_pop_thm "syn_proj_clauses";
end;

add_pc_thms "'ifos" [syn_proj_clauses, ¬∅⋎g_∈_syntax_lemma, MkAf_∈_Syntax_lemma];
set_merge_pcs ["misc21", "'ifos"];

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

local val _ = set_goal([], ⌜∀x y⦁ ¬ MkAf x = MkCf y⌝);
val _ = a (rewrite_tac (map get_spec [⌜MkAf⌝, ⌜MkCf⌝]));
in val syn_con_neq_clauses = save_pop_thm "syn_con_neq_clauses";
end;

add_pc_thms "'ifos" [syn_con_neq_clauses];
set_merge_pcs ["misc21", "'ifos"];

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

=IGN
set_goal ([], ⌜∀t⦁ IsCf t ⇒ ∀f⦁ f ∈⋎g CfForms t ⇒ ScPrec f t⌝);
val _ = a (REPEAT strip_tac
	THEN all_fc_tac [is_fc_clauses]
	THEN all_fc_tac [scprec2_fc_clauses]
	THEN POP_ASM_T ante_tac
	THEN_TRY asm_rewrite_tac []);
val scprec_fc_clauses2 = save_pop_thm "scprec2_fc_clauses2";
=TEX

The following recursion theorem supports definition by primitive recursion of functions over the syntax.
}%ignore

=GFT
sc_recursion_lemma =
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
		else af (AfSet x) (AfMem x)⌝
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
a (LEMMA_T ⌜∃ vars' forms'⦁ MkCf (vars, forms) = MkCf (vars', forms')⌝ rewrite_thm_tac);
a (∃_tac ⌜vars⌝ THEN ∃_tac ⌜forms⌝ THEN rewrite_tac[]);
val sc_recursion_lemma = save_pop_thm "sc_recursion_lemma";
=TEX
}%ignore

This gets plugged into proof context {\it 'ifos} for use in consistency proofs.

=SML
add_∃_cd_thms [sc_recursion_lemma] "'ifos";
set_merge_pcs ["misc21", "'ifos"];
=TEX


ⓈHOLCONST
│ ⦏FreeVars2⦎ : GS → GS SET
├───────────
│ (∀x y⦁
│	FreeVars2 (MkAf (x, y)) = {x; y})
│∧ (∀vars forms⦁
│	FreeVars2 (MkCf (vars, forms)) = ⋃ (FunImage⋎g FreeVars2 forms) \ (X⋎g vars))
■

Inductive proofs using the well-foundedness of ScPrec are fiddley.
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
a (POP_ASM_T ante_tac THEN sc_induction_tac ⌜x⌝ THEN strip_tac);
a (fc_tac [syntax_cases_thm] THEN fc_tac [is_fc_clauses] THEN asm_rewrite_tac[]);
a (list_spec_nth_asm_tac 7 [⌜vars⌝, ⌜fs⌝] THEN asm_fc_tac[]);
a (lemma_tac ⌜tc ScPrec f t⌝ THEN_LIST [bc_tac [tc_incr_thm], all_asm_fc_tac []]);
a (all_fc_tac [scprec_fc_clauses]);
val syn_induction_thm = save_pop_thm "syn_induction_thm";
=TEX
}%ignore

Using this induction principle an induction tactic is defined as follows:

=SML
fun ⦏ifos_induction_tac⦎ t (a,c) = (
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

\subsubsection{Auxiliary Concepts}

Its useful to be able to talk about the free variables in a formula so the definition is given here.

The definition is by recursion over the structure of the syntax.
This is acheived by defining a functor of which the required function is a fixed point.

ⓈHOLCONST
│ ⦏FreeVarsFunct⦎ : (GS → GS SET) → (GS → GS SET)
├───────────
│ FreeVarsFunct = λfv f⦁
│	if f ∈ Syntax
│	then if IsAf f
│	     then {AfMem f; AfSet f}
│	     else ⋃ (FunImage⋎g fv (CfForms f)) \ (X⋎g (CfVars f))
│	else εx⦁T
■

ⓈHOLCONST
│ ⦏FreeVars⦎ : (GS → GS SET)
├───────────
│ FreeVars = fix FreeVarsFunct
■

=GFT
⦏freevarsfunct_respect_thm⦎ =
	⊢ FreeVarsFunct respects ScPrec

⦏freevarsfunct_fixp_lemma⦎ =
	⊢ FreeVars = FreeVarsFunct FreeVars
=TEX
=GFT
⦏freevarsfunct_thm⦎ =
   ⊢ FreeVars
       = (λ f
       ⦁ if f ∈ Syntax
         then
           if IsAf f
           then {AfMem f; AfSet f}
           else ⋃ (FunImage⋎g FreeVars (CfForms f)) \ X⋎g (CfVars f)
         else ε x⦁ T)
=TEX
=GFT
⦏freevarsfunct_thm2⦎ =
   ⊢ ∀ f
     ⦁ FreeVars f
         = (if f ∈ Syntax
           then
             if IsAf f
             then {AfMem f; AfSet f}
             else ⋃ (FunImage⋎g FreeVars (CfForms f)) \ X⋎g (CfVars f)
           else ε x⦁ T)
=TEX

\ignore{
=SML
push_merge_pcs ["misc2", "'ifos"];

local val _ = set_goal([], ⌜FreeVarsFunct respects ScPrec⌝);
val _ = a (rewrite_tac [get_spec ⌜FreeVarsFunct⌝, get_spec ⌜$respects⌝, get_spec ⌜ScPrec⌝]
	THEN REPEAT strip_tac);
val _ = a (cases_tac ⌜x ∈ Syntax⌝ THEN asm_rewrite_tac []);
val _ = a (fc_tac [syntax_cases_thm] THEN asm_rewrite_tac [get_spec ⌜FunImage⋎g⌝]);
val _ = a (fc_tac [Is_not_fc_clauses] THEN asm_rewrite_tac[]);
val _ = a (once_rewrite_tac [sets_ext_clauses]);
val _ = a (strip_tac THEN rewrite_tac[∈_in_clauses]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
val _ = a (∃_tac ⌜s⌝ THEN asm_rewrite_tac[]);
val _ = a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
val _ = a (lemma_tac ⌜tc ScPrec y x⌝
	THEN1 (all_fc_tac [scprec_fc_clauses2]
		THEN all_fc_tac [tc_incr_thm]));
val _ = a (asm_fc_tac []);
(* *** Goal "2" *** *)
val _ = a (∃_tac ⌜s⌝ THEN asm_rewrite_tac[]);
val _ = a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
val _ = a (lemma_tac ⌜tc ScPrec y x⌝
	THEN1 (all_fc_tac [scprec_fc_clauses2]
		THEN all_fc_tac [tc_incr_thm]));
val _ = a (asm_fc_tac []);
val _ = a (asm_rewrite_tac[]);
in val freevarsfunct_respect_thm = save_pop_thm "freevarsfunct_respect_thm";
end;

local val _ = set_goal([], ⌜FreeVars = FreeVarsFunct FreeVars⌝);
val _ = a (asm_tac well_founded_ScPrec_thm);
val _ = a (asm_tac freevarsfunct_respect_thm);
val _ = a (all_fc_tac [∀_elim ⌜ScPrec⌝ (∀_elim ⌜FreeVarsFunct⌝ (get_spec ⌜fix⌝))]);
val _ = a (rewrite_tac [get_spec ⌜FreeVars⌝]);
val _ = a (asm_rewrite_tac[]);
in val freevarsfunct_fixp_lemma = save_pop_thm "freevarsfunct_fixp_lemma";
end;

val freevarsfunct_thm = save_thm ("freevarsfunct_thm",
	rewrite_rule [get_spec ⌜FreeVarsFunct⌝] freevarsfunct_fixp_lemma);

local val _ = set_goal([], ⌜∀ f
     ⦁ FreeVars f
         = if f ∈ Syntax
│	then if IsAf f
│	     then {AfMem f; AfSet f}
│	     else ⋃ (FunImage⋎g FreeVars (CfForms f)) \ X⋎g (CfVars f)
│	else εx⦁T⌝);
val _ = a (REPEAT strip_tac THEN rewrite_tac[rewrite_rule [](once_rewrite_rule [ext_thm] freevarsfunct_thm)]);
in val freevarsfunct_thm2 = save_pop_thm "freevarsfunct_thm2";
end;

pop_pc();
=TEX
}%ignore

The name {\it SetReps} is defined as the set of formulae with exactly one free variable which is the empty set.
These are the candidate representatives for sets, and represent the set coextensive with the property expressed by the formula.
To know what set that is you need to know the domain of discourse (which in the cases of interest here will always be a subset of {\it SetReps}) and the semantics of formulae, which is defined below.

ⓈHOLCONST
│ ⦏SetReps⦎ : GS SET
├───────────
│ SetReps = {x | x ∈ Syntax ∧ FreeVars x = {∅⋎g}}
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

add_pc_thms "'ifos" [¬∅⋎g_∈_setreps_lemma];
set_merge_pcs ["misc21", "'ifos"];
=TEX
}%ignore


\subsection{Semantics}

The semantics of infinitary first order logic is given by defining ``truth in an interpretation''.

\subsubsection{Type Abbreviations}

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

\subsubsection{Formula Evaluation}

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
	if mem ∈ IxDom va ∧ set ∈ IxDom va
		then Snd st (IxVal va mem) (IxVal va set)
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

This one is probably now history, but I'm not ready to delete it yet!

ⓈHOLCONST
│ ⦏EvalCf_tf3⦎ : TTV CFE
├───────────
│ ∀results⦁ EvalCf_tf3 results = 
│	if results ⊆ {pTrue} then pFalse
│		else if (pFalse) ∈ results then pTrue
│		else pU
■

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
Then think of the required evaluation function as arising by mapping the boolean evaluator above over the set of choice sets formed from the set of sets of booleans.

ⓈHOLCONST
│ ⦏LiftEvalCf_bool⦎ : BOOL SET SET → BOOL SET
├───────────
│ ∀results⦁ LiftEvalCf_bool results =
	{v:BOOL | ∃w f⦁ w = FunImage f results ∧ v = EvalCf_bool w
		∧ ∀x⦁ x ∈ results ∧ (∃y⦁ y ∈ x) ⇒ (f x) ∈ x}
■

To get the required evaluator we need to modify this to work with type FTV instead of BOOL SET.

The conversions are:

ⓈHOLCONST
│ ⦏BoolSet2FTV⦎ : BOOL SET → FTV
├───────────
│ ∀bs⦁ BoolSet2FTV bs =
│	if T ∈ bs
│	then if F ∈ bs then fT else fTrue
│	else if F ∈ bs then fFalse	else fB
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
push_merge_pcs ["misc2", "'ifos"];

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

set_merge_pcs ["misc2", "'ifos"];
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


=GFT
⦏EvalForm_MkAf_lemma⦎ =
   ⊢ ∀ cfe ≤⋎t st set mem
     ⦁ EvalForm (cfe, ≤⋎t, st) (MkAf (set, mem))
         = EvalAf ≤⋎t (MkAf (set, mem)) st
=TEX

\ignore{
=SML

(*
I would do this but that it messes up proofs I don't want to meddle with.

add_pc_thms "'ifos" [EvalAf_MkAf_lemma, EvalCf_MkCf_lemma];
set_merge_pcs ["misc2", "'ifos"];
*)

set_goal([], ⌜∀ cfe $≤⋎t st set mem⦁ EvalForm (cfe, $≤⋎t, st) (MkAf (set, mem)) = EvalAf $≤⋎t (MkAf (set, mem)) st⌝);
a (REPEAT ∀_tac THEN rewrite_tac [evalformfunct_thm2]);
val EvalForm_MkAf_lemma = pop_thm ();

=IGN
set_goal([], ⌜∀ cfe $≤⋎t st vars forms⦁ EvalForm (cfe, $≤⋎t, st) (MkCf (vars, forms)) = EvalCf cfe (MkCf (set, mem)) st ⌝);
a (REPEAT ∀_tac THEN rewrite_tac [evalformfunct_thm2]);
val EvalForm_MkCf_lemma = pop_thm ();
=TEX
}%ignore


=GFT
⦏EvalForm_fT_lemma⦎ =
   ⊢ ∀ y
     ⦁ y ∈ Syntax
         ⇒ (∀ va
         ⦁ FreeVars y ⊆ IxDom va
               ∧ IxRan va ⊆ V ∪ {∅⋎g}
               ∧ EvalForm (EvalCf_ftv, $≤⋎t⋎4, V ∪ {∅⋎g}, $∈⋎v) y va = fT
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
=TEX

\ignore{
=SML
add_pc_thms "'ifos" [EvalAf_MkAf_lemma, EvalCf_MkCf_lemma, EvalForm_MkAf_lemma];

push_merge_pcs ["misc2", "'ifos"];

set_goal([], ⌜∀y⦁ y ∈ Syntax ⇒ ∀va⦁ FreeVars y ⊆ IxDom va ∧ IxRan va ⊆ V ∪ {∅⋎g}
	∧ EvalForm (EvalCf_ftv, $≤⋎t⋎4, V ∪ {∅⋎g}, $∈⋎v) y va = fT
	⇒ (∃ x y:GS⦁ x ∈ V ∪ {∅⋎g} ∧ y ∈ V ∪ {∅⋎g} ∧ x ∈⋎v y = fT)⌝);
a (strip_tac THEN strip_tac);
a (ifos_induction_tac ⌜y⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac THEN DROP_NTH_ASM_T 2 ante_tac
	THEN asm_rewrite_tac[freevarsfunct_thm2, get_spec ⌜$⊆⌝, ∈_in_clauses]);
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
a (REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a (DROP_NTH_ASM_T 12 (ante_tac o (rewrite_rule [freevarsfunct_thm2])));
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
	⇒ (∃ x y⦁ x ∈ V ∪ {∅⋎g} ∧ y ∈ V ∪ {∅⋎g} ∧ x ∈⋎v y = fT)⌝);
a (strip_tac THEN strip_tac);
a (ifos_induction_tac ⌜y⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac THEN DROP_NTH_ASM_T 2 ante_tac
	THEN asm_rewrite_tac[freevarsfunct_thm2, get_spec ⌜$⊆⌝, ∈_in_clauses]);
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
a (DROP_NTH_ASM_T 12 (ante_tac o (rewrite_rule [freevarsfunct_thm2])));
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

pop_pc();
=TEX
}%ignore


\subsubsection{Equivalence of Membership Relations}

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
=TEX

\ignore{
=SML
set_goal([], ⌜∀ cfe ≤⋎t V W f r1 r2⦁ V ⊆ W ∧ PmrEq W r1 r2
	⇒ f ∈ Syntax ⇒ ∀z⦁ IxRan z ⊆ W ⇒ EvalForm (cfe, ≤⋎t, (V, r1)) f z = EvalForm (cfe, ≤⋎t, (V, r2)) f z⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜PmrEq⌝] THEN strip_tac THEN strip_tac);
a (ifos_induction_tac ⌜f⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [evalformfunct_thm2, repclosed_syntax_thm, get_spec ⌜EvalAf⌝, let_def]);
a (cond_cases_tac ⌜y ∈ IxDom z ∧ x ∈ IxDom z⌝);
a (DROP_ASM_T ⌜IxRan z ⊆ W⌝ (asm_tac o (rewrite_rule[sets_ext_clauses])));
a (list_spec_nth_asm_tac 4 [⌜IxVal z y⌝, ⌜IxVal z x⌝]);
a (lemma_tac ⌜IxVal z y ∈ W⌝
	THEN1 (fc_tac [ix_domran_lemma] THEN asm_fc_tac[]));
a (lemma_tac ⌜IxVal z x ∈ W⌝
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

=IGN

set_goal([], ⌜∀ cfe ≤⋎t V W f r1 r2⦁ V ⊆ W ∧ PmrEq W r1 r2
	⇒ f ∈ Syntax ⇒ ∀z⦁ IxRan z ⊆ W ⇒ EvalForm (cfe, ≤⋎t, (V, r1)) f z = EvalForm (cfe, ≤⋎t, (V, r2)) f z⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜PmrEq⌝] THEN strip_tac);
a (LEMMA_T ⌜∀f⦁ f ∈ Syntax ⇒ (λf⦁ ∀z⦁ IxRan z ⊆ W ⇒ EvalForm (cfe, ≤⋎t, (V, r1)) f z = EvalForm (cfe, ≤⋎t, (V, r2)) f z) f⌝
	(rewrite_thm_tac o rewrite_rule[]));
a (bc_tac [syn_induction_thm] THEN rewrite_tac[]);
(* *** Goal "1" *** *)
a (∀_tac THEN rewrite_tac [evalformfunct_thm2, repclosed_syntax_thm, get_spec ⌜EvalAf⌝, let_def]
	THEN strip_tac);
a (cond_cases_tac ⌜y ∈ IxDom z ∧ x ∈ IxDom z⌝);
a (DROP_ASM_T ⌜IxRan z ⊆ W⌝ (asm_tac o (rewrite_rule[sets_ext_clauses])));
a (list_spec_nth_asm_tac 4 [⌜IxVal z y⌝, ⌜IxVal z x⌝]);
a (lemma_tac ⌜IxVal z y ∈ W⌝
	THEN1 (fc_tac [ix_domran_lemma] THEN asm_fc_tac[]));
a (lemma_tac ⌜IxVal z x ∈ W⌝
	THEN1 (fc_tac [ix_domran_lemma] THEN asm_fc_tac[]));
(* *** Goal "2" *** *)
a (REPEAT strip_tac);
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
=TEX
}%ignore

\subsubsection{Some Orderings}

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
│ ⦏$≤⋎f⋎t⋎3⦎ : ('a → TTV) → ('a → TTV) → BOOL
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
│ ⦏$≤⋎f⋎t⋎4⦎ : ('a → FTV) → ('a → FTV) → BOOL
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

\subsubsection{Monotonicity Results}

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
local val _ = set_goal ([], ⌜∀c r s g⦁ CRpoU r ∧ Increasing (SetO r) r c
	⇒ Increasing (Pw (Pw r)) (RvO r) (MonoEvalForm (c,r,s,g))⌝);
val _ = a (REPEAT strip_tac);
val _ = a (sc_induction_tac ⌜g⌝ THEN_TRY asm_rewrite_tac[]);
val _ = a (rewrite_tac ((map get_spec [⌜Increasing⌝, ⌜MonoEvalForm⌝, ⌜RvO⌝, ⌜RvIsO⌝])@[evalformfunct_thm2])
	THEN REPEAT strip_tac);
val _ = a (cases_tac ⌜t ∈ Syntax⌝ THEN asm_rewrite_tac[]);
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
val _ = a (lemma_tac ⌜tc ScPrec a t⌝);
(* *** Goal "1.2.1.2.1" *** *)
val _ = a (fc_tac [scprec_fc_clauses]);
val _ = a (fc_tac [syntax_cases_thm]);
val _ = a (all_fc_tac [is_fc_clauses2]);
val _ = a (all_fc_tac [scprec_fc_clauses2]);
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
val _ = a (lemma_tac ⌜tc ScPrec a t⌝);
(* *** Goal "1.2.2.2.1" *** *)
val _ = a (fc_tac [syntax_cases_thm]);
val _ = a (fc_tac [scprec_fc_clauses]);
val _ = a (all_fc_tac [is_fc_clauses2]);
val _ = a (all_fc_tac [scprec_fc_clauses2]);
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
in val monoevalform_increasing_lemma = pop_thm();
end;

local val _ = set_goal([], ⌜∀ c r s g
     ⦁ CRpoU r ∧ Increasing (SetO r) r c
         ⇒ Increasing (Pw (Pw r)) (RvO r) (λris⦁EvalForm (c, r, s, ris) g)⌝);
val _ = a (REPEAT ∀_tac);
val _ = a (lemma_tac ⌜(λris⦁EvalForm (c, r, s, ris) g) = MonoEvalForm (c, r, s, g)⌝
	THEN1 rewrite_tac [ext_thm, get_spec ⌜MonoEvalForm⌝]);
val _ = a (asm_rewrite_tac[monoevalform_increasing_lemma]);
in val evalform_increasing_thm = save_pop_thm "evalform_increasing_thm";
end;
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
local val _ = set_goal([], ⌜∀(V, $∈⋎v) g⦁ V ⊆ Syntax ∧ g ∈ Syntax
	⇒ Increasing (ExsVaO (V2IxSet V, (V, $∈⋎v))) $≤⋎t⋎4 (EvalForm (EvalCf_ftv, $≤⋎t⋎4, (V, $∈⋎v)) g)⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$⊆⌝] THEN strip_tac THEN POP_ASM_T ante_tac);
val _ = a (sc_induction_tac ⌜g⌝);
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
val _ = a (lemma_tac ⌜ScPrec a t ∧ a ∈ Syntax⌝);
val _ = a (all_fc_tac [is_fc_clauses]);
val _ = a (GET_NTH_ASM_T 4 (asm_tac o (rewrite_rule [asm_rule ⌜t = MkCf (vars, fs)⌝])));
val _ = a (ASM_FC_T rewrite_tac []);
val _ = a (ufc_tac [scprec_fc_clauses] THEN asm_ufc_tac[]);
val _ = a (asm_fc_tac[]);
(* *** Goal "2.1.2.2" *** *)
val _ = a (lemma_tac ⌜tc ScPrec a t⌝ THEN1 fc_tac [tc_incr_thm]);
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
val _ = a (lemma_tac ⌜ScPrec a t ∧ a ∈ Syntax⌝);
val _ = a (all_fc_tac [is_fc_clauses]);
val _ = a (GET_NTH_ASM_T 4 (asm_tac o (rewrite_rule [asm_rule ⌜t = MkCf (vars, fs)⌝])));
val _ = a (ASM_FC_T rewrite_tac []);
val _ = a (ufc_tac [scprec_fc_clauses] THEN asm_ufc_tac[]);
val _ = a (asm_fc_tac[]);
(* *** Goal "2.2.2.2" *** *)
val _ = a (lemma_tac ⌜tc ScPrec a t⌝ THEN1 fc_tac [tc_incr_thm]);
val _ = a (all_asm_fc_tac[]);
val _ = a (POP_ASM_T ante_tac THEN asm_rewrite_tac[get_spec ⌜Increasing⌝] THEN strip_tac);
val _ = a (LEMMA_T ⌜ExsVaO (V2IxSet V, V, $∈⋎v) (IxOverRide x v) (IxOverRide y v)⌝
	(asm_tac)
	THEN1 (all_fc_tac [exsvao_ixoverride_lemma]));
val _ = a (list_spec_nth_asm_tac 2 [⌜IxOverRide x v⌝, ⌜IxOverRide y v⌝]);
val _ = a (rewrite_tac [eq_sym_rule (asm_rule ⌜EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, $∈⋎v) a = rv⌝)]);
val _ = a strip_tac;
in val evalform_increasing_thm2 = save_pop_thm "evalform_increasing_thm2";
end;

set_goal([], ⌜∀V $∈⋎v g⦁ V ⊆ Syntax ∧ g ∈ Syntax
	⇒ Increasing (ExsVaO (V2IxSet (V ∪ {∅⋎g}), (V ∪ {∅⋎g}, $∈⋎v))) $≤⋎t⋎4 (EvalForm (EvalCf_ftv, $≤⋎t⋎4, (V, $∈⋎v)) g)⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$⊆⌝] THEN strip_tac THEN POP_ASM_T ante_tac);
val _ = a (sc_induction_tac ⌜g⌝);
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
val _ = a (lemma_tac ⌜ScPrec a t ∧ a ∈ Syntax⌝);
(* *** Goal "2.1.2.1" *** *)
val _ = a (all_fc_tac [is_fc_clauses]);
val _ = a (GET_NTH_ASM_T 4 (asm_tac o (rewrite_rule [asm_rule ⌜t = MkCf (vars, fs)⌝])));
val _ = a (ASM_FC_T rewrite_tac []);
val _ = a (ufc_tac [scprec_fc_clauses] THEN asm_ufc_tac[]);
val _ = a (asm_fc_tac[]);
(* *** Goal "2.1.2.2" *** *)
val _ = a (lemma_tac ⌜tc ScPrec a t⌝ THEN1 fc_tac [tc_incr_thm]);
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
val _ = a (lemma_tac ⌜ScPrec a t ∧ a ∈ Syntax⌝);
val _ = a (all_fc_tac [is_fc_clauses]);
val _ = a (GET_NTH_ASM_T 4 (asm_tac o (rewrite_rule [asm_rule ⌜t = MkCf (vars, fs)⌝])));
val _ = a (ASM_FC_T rewrite_tac []);
val _ = a (ufc_tac [scprec_fc_clauses] THEN asm_ufc_tac[]);
val _ = a (asm_fc_tac[]);
(* *** Goal "2.2.2.2" *** *)
val _ = a (lemma_tac ⌜tc ScPrec a t⌝ THEN1 fc_tac [tc_incr_thm]);
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
val _ = a (sc_induction_tac ⌜g⌝);
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
val _ = a (lemma_tac ⌜ScPrec a t ∧ a ∈ Syntax⌝);
(* *** Goal "2.1.2.1" *** *)
val _ = a (all_fc_tac [is_fc_clauses]);
val _ = a (GET_NTH_ASM_T 4 (asm_tac o (rewrite_rule [asm_rule ⌜t = MkCf (vars, fs)⌝])));
val _ = a (ASM_FC_T rewrite_tac []);
val _ = a (ufc_tac [scprec_fc_clauses] THEN asm_ufc_tac[]);
val _ = a (asm_fc_tac[]);
(* *** Goal "2.1.2.2" *** *)
val _ = a (lemma_tac ⌜tc ScPrec a t⌝ THEN1 fc_tac [tc_incr_thm]);
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
val _ = a (lemma_tac ⌜ScPrec a t ∧ a ∈ Syntax⌝);
val _ = a (all_fc_tac [is_fc_clauses]);
val _ = a (GET_NTH_ASM_T 4 (asm_tac o (rewrite_rule [asm_rule ⌜t = MkCf (vars, fs)⌝])));
val _ = a (ASM_FC_T rewrite_tac []);
val _ = a (ufc_tac [scprec_fc_clauses] THEN asm_ufc_tac[]);
val _ = a (asm_fc_tac[]);
(* *** Goal "2.2.2.2" *** *)
val _ = a (lemma_tac ⌜tc ScPrec a t⌝ THEN1 fc_tac [tc_incr_thm]);
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

\subsubsection{Extension and Essence, Compatibility and OverDefinedness}

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

=IGN
(* This one was broken by the correction to EvalCf. *)

local val _ = set_goal([], ⌜∀V r⦁ V ⊆ SetReps ⇒ ∀z⦁ z ∈ Syntax ⇒ ∀x y⦁
		IxDom x = IxDom y ∧ FreeVars z ⊆ IxDom x ∧ IxRan x ⊆ V ∧ IxRan y ⊆ V
		∧ (∀v⦁ v ∈ IxDom x ⇒ SameExt V r (IxVal x v) (IxVal y v) ∧ SameEss V r (IxVal x v) (IxVal y v))
		⇒	EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) z x
			= EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) z y⌝);
val _ = a (REPEAT_N 4 strip_tac);
val _ = a (sc_induction_tac ⌜z⌝);
val _ = a (REPEAT_N 3 strip_tac THEN rewrite_tac [get_spec ⌜SameExt⌝, get_spec ⌜SameEss⌝, evalformfunct_thm2]
	THEN REPEAT strip_tac);
val _ = a (asm_rewrite_tac[let_def]);
val _ = a (fc_tac [syntax_cases_thm]
	THEN fc_tac[Is_not_fc_clauses]
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
val _ = a (asm_rewrite_tac [get_spec ⌜EvalAf⌝, let_def]);
val _ = a (CASES_T ⌜AfMem t ∈ IxDom y ∧ AfSet t ∈ IxDom y⌝ (fn x => rewrite_thm_tac x THEN asm_tac x));
val _ = a (POP_ASM_T strip_asm_tac);
val _ = a (DROP_NTH_ASM_T 5 (asm_tac o (rewrite_rule[asm_rule ⌜IxDom x = IxDom y⌝])));
val _ = a (asm_fc_tac[]);
val _ = a (lemma_tac ⌜IxVal x (AfMem t) ∈ V ∧ IxVal x (AfSet t) ∈ V ∧ IxVal y (AfMem t) ∈ V ∧ IxVal y (AfSet t) ∈ V⌝
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
val _ = a (GET_NTH_ASM_T 11 (fn x => bc_tac [rewrite_rule [sets_ext_clauses] x]));
val _ = a (bc_tac [ix_domran_lemma] THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
val _ = a (GET_NTH_ASM_T 11 (fn x => bc_tac [rewrite_rule [sets_ext_clauses] x]));
val _ = a (bc_tac [ix_domran_lemma] THEN asm_rewrite_tac[]);
(* *** Goal "1.3" *** *)
val _ = a (GET_NTH_ASM_T 10 (fn x => bc_tac [rewrite_rule [sets_ext_clauses] x]));
val _ = a (bc_tac [ix_domran_lemma] THEN asm_rewrite_tac[]);
(* *** Goal "1.4" *** *)
val _ = a (GET_NTH_ASM_T 10 (fn x => bc_tac [rewrite_rule [sets_ext_clauses] x]));
val _ = a (bc_tac [ix_domran_lemma] THEN asm_rewrite_tac[]);
(* *** Goal "1.5" *** *)
val _ = a (asm_fc_tac[] THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
val _ = a (rewrite_tac [get_spec ⌜EvalCf⌝, let_def]);
val _ = a (LEMMA_T ⌜{pb
                 |∃ rv v
                   ⦁ rv ∈ FunImage (EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r)) (X⋎g (CfForms t))
                       ∧ IxDom v = X⋎g (CfVars t)
                       ∧ IxRan v ⊆ V
                       ∧ pb = rv (IxOverRide x v)}
             =
               {pb
                 |∃ rv v
                   ⦁ rv ∈ FunImage (EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r)) (X⋎g (CfForms t))
                       ∧ IxDom v = X⋎g (CfVars t)
                       ∧ IxRan v ⊆ V
                       ∧ pb = rv (IxOverRide y v)}
	⇒ EvalCf_ftv
               {pb
                 |∃ rv v
                   ⦁ rv ∈ FunImage (EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r)) (X⋎g (CfForms t))
                       ∧ IxDom v = X⋎g (CfVars t)
                       ∧ IxRan v ⊆ V
                       ∧ pb = rv (IxOverRide x v)}
             = EvalCf_ftv
               {pb
                 |∃ rv v
                   ⦁ rv ∈ FunImage (EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r)) (X⋎g (CfForms t))
                       ∧ IxDom v = X⋎g (CfVars t)
                       ∧ IxRan v ⊆ V
                       ∧ pb = rv (IxOverRide y v)}⌝ (fn x => bc_tac [x])
	THEN1 (STRIP_T rewrite_thm_tac));
val _ = a (PC_T "hol1" strip_tac THEN ∀_tac THEN rewrite_tac[]);
val _ = a (REPEAT strip_tac);
(* *** Goal "2.1" *** *)
val _ = a (∃_tac ⌜rv⌝ THEN ∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
val _ = a (GET_NTH_ASM_T 4 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
val _ = a (DROP_NTH_ASM_T 3 discard_tac);
val _ = a (SYM_ASMS_T rewrite_tac);
val _ = a (DROP_NTH_ASM_T 2 (asm_tac o (rewrite_rule [get_spec ⌜X⋎g⌝])));
val _ = a (all_fc_tac [scprec_fc_clauses2]);
val _ = a (all_fc_tac [is_fc_clauses2]);
val _ = a (lemma_tac ⌜tc ScPrec a t⌝ THEN1 fc_tac [tc_incr_thm]);
val _ = a (lemma_tac ⌜∀ v⦁ v ∈ IxDom x
                         ⇒ SameExt V r (IxVal x v) (IxVal y v)
                           ∧ SameEss V r (IxVal x v) (IxVal y v)⌝
	THEN1 (strip_tac
		THEN rewrite_tac [get_spec ⌜SameExt⌝, get_spec ⌜SameEss⌝]
		THEN strip_tac));
(* *** Goal "2.1.1" *** *)
val _ = a (spec_nth_asm_tac 12 ⌜v'⌝);
val _ = a (REPEAT strip_tac THEN asm_fc_tac[]);
(* *** Goal "2.1.2" *** *)
val _ = a (spec_nth_asm_tac 18 ⌜a⌝);
val _ = a (list_spec_nth_asm_tac 1 [⌜IxOverRide x v⌝, ⌜IxOverRide y v⌝]
	THEN swap_nth_asm_concl_tac 1);
(* *** Goal "2.1.2.1" *** *)
val _ = a (asm_rewrite_tac[]);
(* *** Goal "2.1.2.2" *** *)
val _ = a (asm_rewrite_tac[]);
val _ = a (bc_tac [list_∀_elim [⌜FreeVars a⌝, ⌜X⋎g (CfVars t) ∪ FreeVars t⌝, ⌜IxDom y ∪ X⋎g (CfVars t)⌝] ⊆_trans_thm]);
(* *** Goal "2.1.2.2.1" *** *)
val _ = a (asm_rewrite_tac[∀_elim ⌜t⌝ freevarsfunct_thm2]);
val _ = a (rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B⦁ A ∪ (B \ A) = A ∪ B⌝]);
val _ = a (lemma_tac ⌜FreeVars a ∈ FunImage⋎g FreeVars (CfForms t)⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜FunImage⋎g⌝]
		THEN ∃_tac ⌜a⌝
		THEN asm_rewrite_tac[]));
val _ = a (lemma_tac ⌜FreeVars a ⊆ ⋃ (FunImage⋎g FreeVars (CfForms t))⌝
	THEN1 (fc_tac [pc_rule1 "hol1" prove_rule [] ⌜∀x B⦁ x ∈ B ⇒ x ⊆ ⋃ B⌝]));
val _ = a (ALL_FC_T rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜∀x B C⦁ x ⊆ B ⇒ x ⊆ C ∪ B⌝]);
(* *** Goal "2.1.2.2.2" *** *)
val _ = a (DROP_NTH_ASM_T 17 ante_tac
	THEN asm_rewrite_tac[]
	THEN PC_T1 "hol1" prove_tac[]);
(* *** Goal "2.1.2.3" *** *)
val _ = a (bc_tac [list_∀_elim [⌜IxRan (IxOverRide x v)⌝, ⌜IxRan x ∪ IxRan v⌝, ⌜V⌝] ⊆_trans_thm]);
val _ = a (rewrite_tac[ixoverride_ixran_lemma]);
val _ = a (DROP_NTH_ASM_T 9 ante_tac
	THEN DROP_NTH_ASM_T 15 ante_tac
	THEN PC_T1 "hol1" prove_tac[]);
(* *** Goal "2.1.2.4" *** *)
val _ = a (bc_tac [list_∀_elim [⌜IxRan (IxOverRide y v)⌝, ⌜IxRan y ∪ IxRan v⌝, ⌜V⌝] ⊆_trans_thm]);
val _ = a (rewrite_tac[ixoverride_ixran_lemma]);
val _ = a (DROP_NTH_ASM_T 9 ante_tac
	THEN DROP_NTH_ASM_T 14 ante_tac
	THEN PC_T1 "hol1" prove_tac[]);
(* *** Goal "2.1.2.5" *** *)
val _ = a (DROP_NTH_ASM_T 2 (ante_tac o (rewrite_rule [∈_in_clauses])));
val _ = a (once_rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B⦁ A ∨ B ⇔ B ∨ (A ∧ ¬ B)⌝]
	THEN strip_tac);
(* *** Goal "2.1.2.5.1" *** *)
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide x v) v') = IxVal v v'⌝ rewrite_thm_tac
	THEN1 (POP_ASM_T ante_tac
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide y v) v') = IxVal v v'⌝ rewrite_thm_tac
	THEN1 (POP_ASM_T (ante_tac)
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (all_asm_fc_tac[]);
(* *** Goal "2.1.2.5.2" *** *)
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide x v) v') = IxVal v v'⌝ rewrite_thm_tac
	THEN1 (REPEAT_N 1 (POP_ASM_T ante_tac)
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide y v) v') = IxVal v v'⌝ rewrite_thm_tac
	THEN1 (REPEAT_N 1 (POP_ASM_T (ante_tac o (rewrite_rule[asm_rule ⌜IxDom x = IxDom y⌝])))
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (LEMMA_T ⌜IxVal v v' ∈ V⌝ (fn x =>
	asm_tac x
	THEN strip_asm_tac (list_∀_elim [⌜V⌝, ⌜r⌝, ⌜IxVal v v'⌝] sameext_refl_lemma)));
val _ = a (fc_tac [ix_domran_lemma]);
val _ = a (GET_ASM_T ⌜IxRan v ⊆ V⌝ ante_tac);
val _ = a (rewrite_tac [sets_ext_clauses] THEN strip_tac THEN asm_fc_tac[]);
(* *** Goal "2.1.2.6" *** *)
val _ = a (DROP_NTH_ASM_T 2 (ante_tac o (rewrite_rule [∈_in_clauses])));
val _ = a (once_rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B⦁ A ∨ B ⇔ B ∨ (A ∧ ¬ B)⌝]
	THEN strip_tac);
(* *** Goal "2.1.2.6.1" *** *)
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide x v) v') = IxVal x v'⌝ rewrite_thm_tac
	THEN1 (POP_ASM_T ante_tac
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide y v) v') = IxVal y v'⌝ rewrite_thm_tac
	THEN1 (POP_ASM_T (ante_tac o (rewrite_rule[asm_rule ⌜IxDom x = IxDom y⌝]))
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (all_asm_fc_tac[]);
(* *** Goal "2.1.2.6.2" *** *)
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide x v) v') = IxVal v v'⌝ rewrite_thm_tac
	THEN1 (REPEAT_N 1 (POP_ASM_T ante_tac)
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide y v) v') = IxVal v v'⌝ rewrite_thm_tac
	THEN1 (REPEAT_N 1 (POP_ASM_T (ante_tac o (rewrite_rule[asm_rule ⌜IxDom x = IxDom y⌝])))
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (LEMMA_T ⌜IxVal v v' ∈ V⌝ (fn x =>
	asm_tac x
	THEN strip_asm_tac (list_∀_elim [⌜V⌝, ⌜r⌝, ⌜IxVal v v'⌝] sameess_refl_lemma)));
val _ = a (fc_tac [ix_domran_lemma]);
val _ = a (GET_ASM_T ⌜IxRan v ⊆ V⌝ ante_tac);
val _ = a (rewrite_tac [sets_ext_clauses] THEN strip_tac THEN asm_fc_tac[]);
(* *** Goal "2.2" *** *)
val _ = a (∃_tac ⌜rv⌝ THEN ∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
val _ = a (GET_NTH_ASM_T 4 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
val _ = a (DROP_NTH_ASM_T 3 discard_tac);
val _ = a (SYM_ASMS_T rewrite_tac);
val _ = a (DROP_NTH_ASM_T 2 (asm_tac o (rewrite_rule [get_spec ⌜X⋎g⌝])));
val _ = a (all_fc_tac [scprec_fc_clauses2]);
val _ = a (all_fc_tac [is_fc_clauses2]);
val _ = a (lemma_tac ⌜tc ScPrec a t⌝ THEN1 fc_tac [tc_incr_thm]);
val _ = a (lemma_tac ⌜∀ v⦁ v ∈ IxDom x
                         ⇒ SameExt V r (IxVal x v) (IxVal y v)
                           ∧ SameEss V r (IxVal x v) (IxVal y v)⌝
	THEN1 (strip_tac
		THEN rewrite_tac [get_spec ⌜SameExt⌝, get_spec ⌜SameEss⌝]
		THEN strip_tac));
(* *** Goal "2.2.1" *** *)
val _ = a (spec_nth_asm_tac 12 ⌜v'⌝);
val _ = a (REPEAT strip_tac THEN asm_fc_tac[]);
(* *** Goal "2.2.2" *** *)
val _ = a (spec_nth_asm_tac 18 ⌜a⌝);
val _ = a (list_spec_nth_asm_tac 1 [⌜IxOverRide y v⌝, ⌜IxOverRide x v⌝]
	THEN swap_nth_asm_concl_tac 1);
(* *** Goal "2.2.2.1" *** *)
val _ = a (asm_rewrite_tac[]);
(* *** Goal "2.2.2.2" *** *)
val _ = a (asm_rewrite_tac[]);
val _ = a (bc_tac [list_∀_elim [⌜FreeVars a⌝, ⌜X⋎g (CfVars t) ∪ FreeVars t⌝, ⌜X⋎g (CfVars t) ∪ IxDom x⌝] ⊆_trans_thm]);
(* *** Goal "2.2.2.2.1" *** *)
val _ = a (asm_rewrite_tac[∀_elim ⌜t⌝ freevarsfunct_thm2]);
val _ = a (rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B⦁ A ∪ (B \ A) = A ∪ B⌝]);
val _ = a (lemma_tac ⌜FreeVars a ∈ FunImage⋎g FreeVars (CfForms t)⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜FunImage⋎g⌝]
		THEN ∃_tac ⌜a⌝
		THEN asm_rewrite_tac[]));
val _ = a (lemma_tac ⌜FreeVars a ⊆ ⋃ (FunImage⋎g FreeVars (CfForms t))⌝
	THEN1 (fc_tac [pc_rule1 "hol1" prove_rule [] ⌜∀x B⦁ x ∈ B ⇒ x ⊆ ⋃ B⌝]));
val _ = a (ALL_FC_T rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜∀x B C⦁ x ⊆ B ⇒ x ⊆ C ∪ B⌝]);
(* *** Goal "2.2.2.2.2" *** *)
val _ = a (DROP_NTH_ASM_T 17 ante_tac
	THEN asm_rewrite_tac[]
	THEN PC_T1 "hol1" prove_tac[]);
(* *** Goal "2.2.2.3" *** *)
val _ = a (bc_tac [list_∀_elim [⌜IxRan (IxOverRide y v)⌝, ⌜IxRan v ∪ IxRan y⌝, ⌜V⌝] ⊆_trans_thm]);
val _ = a (rewrite_tac[ixoverride_ixran_lemma]);
val _ = a (DROP_NTH_ASM_T 9 ante_tac
	THEN DROP_NTH_ASM_T 14 ante_tac
	THEN PC_T1 "hol1" prove_tac[]);
(* *** Goal "2.2.2.4" *** *)
val _ = a (bc_tac [list_∀_elim [⌜IxRan (IxOverRide x v)⌝, ⌜IxRan v ∪ IxRan x⌝, ⌜V⌝] ⊆_trans_thm]);
val _ = a (rewrite_tac[ixoverride_ixran_lemma]);
val _ = a (DROP_NTH_ASM_T 9 ante_tac
	THEN DROP_NTH_ASM_T 15 ante_tac
	THEN PC_T1 "hol1" prove_tac[]);
(* *** Goal "2.2.2.5" *** *)
val _ = a (DROP_NTH_ASM_T 2 (ante_tac o (rewrite_rule [∈_in_clauses])));
val _ = a (once_rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B⦁ A ∨ B ⇔ B ∨ (A ∧ ¬ B)⌝]
	THEN strip_tac);
(* *** Goal "2.2.2.5.1" *** *)
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide y v) v') = IxVal y v'⌝ rewrite_thm_tac
	THEN1 (POP_ASM_T ante_tac
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide x v) v') = IxVal x v'⌝ rewrite_thm_tac
	THEN1 (POP_ASM_T (ante_tac o (rewrite_rule[eq_sym_rule (asm_rule ⌜IxDom x = IxDom y⌝)]))
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (POP_ASM_T (asm_tac o (rewrite_rule[eq_sym_rule (asm_rule ⌜IxDom x = IxDom y⌝)]))
	THEN all_asm_fc_tac[]);
val _ = a (lemma_tac ⌜IxVal y v' ∈ V ∧ IxVal x v' ∈ V⌝);
val _ = a (lemma_tac ⌜v' ∈ IxDom y⌝ THEN1 rewrite_tac[eq_sym_rule (asm_rule ⌜IxDom x = IxDom y⌝), asm_rule ⌜v' ∈ IxDom x⌝]);
val _ = a (lemma_tac ⌜IxVal y v' ∈ IxRan y ∧ IxVal x v' ∈ IxRan x⌝
	THEN1 (fc_tac [ix_domran_lemma] THEN contr_tac));
val _ = a (GET_NTH_ASM_T 21 ante_tac THEN GET_NTH_ASM_T 22 ante_tac
	THEN rewrite_tac [sets_ext_clauses]
	THEN STRIP_T (fn x => fc_tac [x])
	THEN STRIP_T (fn x => fc_tac [x])
	THEN contr_tac);
val _ = a (strip_asm_tac (list_∀_elim [⌜V⌝, ⌜r⌝, ⌜IxVal y v'⌝, ⌜IxVal x v'⌝] sameext_sym_lemma));
(* *** Goal "2.2.2.5.2" *** *)
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide y v) v') = IxVal v v'⌝ rewrite_thm_tac
	THEN1 (REPEAT_N 1 (POP_ASM_T ante_tac)
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide x v) v') = IxVal v v'⌝ rewrite_thm_tac
	THEN1 (REPEAT_N 1 (POP_ASM_T (ante_tac o (rewrite_rule[eq_sym_rule (asm_rule ⌜IxDom x = IxDom y⌝)])))
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (LEMMA_T ⌜IxVal v v' ∈ V⌝ (fn x =>
	asm_tac x
	THEN strip_asm_tac (list_∀_elim [⌜V⌝, ⌜r⌝, ⌜IxVal v v'⌝] sameext_refl_lemma)));
val _ = a (fc_tac [ix_domran_lemma]);
val _ = a (GET_ASM_T ⌜IxRan v ⊆ V⌝ ante_tac);
val _ = a (rewrite_tac [sets_ext_clauses] THEN strip_tac THEN asm_fc_tac[]);
(* *** Goal "2.2.2.6" *** *)
val _ = a (DROP_NTH_ASM_T 2 (ante_tac o (rewrite_rule [∈_in_clauses])));
val _ = a (once_rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B⦁ A ∨ B ⇔ B ∨ (A ∧ ¬ B)⌝]
	THEN strip_tac);
(* *** Goal "2.2.2.6.1" *** *)
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide y v) v') = IxVal y v'⌝ rewrite_thm_tac
	THEN1 (POP_ASM_T ante_tac
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide x v) v') = IxVal x v'⌝ rewrite_thm_tac
	THEN1 (POP_ASM_T (ante_tac o (rewrite_rule[eq_sym_rule(asm_rule ⌜IxDom x = IxDom y⌝)]))
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (POP_ASM_T (asm_tac o (rewrite_rule [eq_sym_rule(asm_rule ⌜IxDom x = IxDom y⌝)])));
val _ = a (all_asm_fc_tac[]);
val _ = a (LEMMA_T ⌜IxVal y v' ∈ V ∧ IxVal x v' ∈ V⌝ (fn x =>
	strip_asm_tac (rewrite_rule [x] (list_∀_elim [⌜V⌝, ⌜r⌝, ⌜IxVal y v'⌝, ⌜IxVal x v'⌝] sameess_sym_lemma))));
val _ = a (GET_NTH_ASM_T 3 (asm_tac o (rewrite_rule [asm_rule ⌜IxDom x = IxDom y⌝])));
val _ = a (fc_tac [ix_domran_lemma]);
val _ = a (GET_ASM_T ⌜IxRan x ⊆ V⌝ ante_tac);
val _ = a (rewrite_tac [sets_ext_clauses] THEN STRIP_T (fn x => fc_tac[x]));
val _ = a (GET_ASM_T ⌜IxRan y ⊆ V⌝ ante_tac);
val _ = a (rewrite_tac [sets_ext_clauses] THEN STRIP_T (fn x => fc_tac[x]));
val _ = a (contr_tac);
(* *** Goal "2.2.2.6.2" *** *)
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide y v) v') = IxVal v v'⌝ rewrite_thm_tac
	THEN1 (REPEAT_N 1 (POP_ASM_T ante_tac)
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (LEMMA_T ⌜(IxVal (IxOverRide x v) v') = IxVal v v'⌝ rewrite_thm_tac
	THEN1 (REPEAT_N 1 (POP_ASM_T (ante_tac o (rewrite_rule[eq_sym_rule (asm_rule ⌜IxDom x = IxDom y⌝)])))
		THEN rewrite_tac[get_spec ⌜IxOverRide⌝, get_spec ⌜IxVal⌝, get_spec ⌜IxUd⌝,
			get_spec ⌜IxDom⌝, get_spec ⌜IsDefined⌝]
		THEN STRIP_T rewrite_thm_tac));
val _ = a (LEMMA_T ⌜IxVal v v' ∈ V⌝ (fn x =>
	asm_tac x
	THEN strip_asm_tac (list_∀_elim [⌜V⌝, ⌜r⌝, ⌜IxVal v v'⌝] sameess_refl_lemma)));
val _ = a (fc_tac [ix_domran_lemma]);
val _ = a (GET_ASM_T ⌜IxRan v ⊆ V⌝ ante_tac);
val _ = a (rewrite_tac [sets_ext_clauses] THEN strip_tac THEN asm_fc_tac[]);
in val evalform_ext_lemma = save_pop_thm "evalform_ext_lemma";
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



\subsubsection{Proof Contexts}

=SML
(* add_pc_thms "'ifos" [evalcf_ftv_ft_lemma, evalcf_ftv_fb_lemma]; *)

(* add_pc_thms "'ifos" [get_spec ⌜Extension⌝, get_spec ⌜Essence⌝]; *)
commit_pc "'ifos";

force_new_pc "⦏ifos⦎";
merge_pcs ["misc2", "'ifos"] "ifos";
commit_pc "ifos";

force_new_pc "⦏ifos1⦎";
merge_pcs ["misc21", "'ifos"] "ifos1";
commit_pc "ifos1";
=TEX

\newpage
\section{SEMANTIC FIXED POINTS}

We now look for fixed points of the semantics of infinitary set theory.

=SML
open_theory "ifos";
new_parent "membership";
force_new_theory "⦏sfp⦎";
force_new_pc ⦏"'sfp"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'sfp";
set_merge_pcs ["misc21", "'ifos", "'sfp"];
=TEX

\subsection{The Semantic Functor}

First we use the semantics above to define a functor which transforms membership relations.

The input membership relation is that in the membership structure relative to which the semantics is defined.

The output membership relation is obtained by considering the sets determined by formulae whose sole free variable is the empty set.
Thus. under this resulting membership relation, (which will be a four-valued relation) the truth value of the claim that {\it m} is a member of {\it s} (where {\it m} and {\it s} are elements of the domain of discourse, which is sets coding formulae of infinitary first order set theory) is the value under the semantics for the formulae coded by {\it s} in the context of the variable assignment in which only the variable coded by the empty set is assigned a value and that value is {\it t}.

The following function creates a variable assignment with just a value for the empty set.

ⓈHOLCONST
│ ⦏Param_∅⦎ : GS → (GS, GS) IX
├───────────
│ ∀p⦁ Param_∅ p = λx⦁ if x = ∅⋎g then Value p else Undefined
■

=GFT
⦏ixdom_param_∅_lemma⦎ =
   ⊢ ∀ x⦁ IxDom (Param_∅ x) = {∅⋎g}

⦏ixran_param_∅_lemma⦎ =
   ⊢ ∀ x⦁ IxRan (Param_∅ x) = {x}

⦏ixval_param_∅_lemma⦎ =
   ⊢ ∀ x⦁ IxVal (Param_∅ x) ∅⋎g = x

⦏param_∅_undefined_lemma⦎ =
   ⊢ ∀ x y⦁ Param_∅ x y = Undefined ⇔ ¬ y = ∅⋎g
=TEX
=GFT
⦏Param_∅_Increasing_lemma⦎ =
   ⊢ ∀ V r
     ⦁ Increasing (V ◁⋎o ExsSRO (V, r)) (ExsVaO (V2IxSet V, V, r)) Param_∅

⦏Param_∅_Increasing_lemma2⦎ =
   ⊢ ∀ V W r
     ⦁ Increasing (W ◁⋎o ExsSRO (V, r)) (ExsVaO (V2IxSet W, V, r)) Param_∅
=TEX

\ignore{
=SML
local val _ = set_goal([], ⌜∀x⦁ IxDom (Param_∅ x) = {∅⋎g}⌝);
val _ = a (rewrite_tac [get_spec ⌜IxDom⌝, get_spec ⌜Param_∅⌝, sets_ext_clauses]);
val _ = a (REPEAT ∀_tac);
val _ = a (cases_tac ⌜x' = ∅⋎g⌝ THEN asm_rewrite_tac[]);
in val ixdom_param_∅_lemma = save_pop_thm "ixdom_param_∅_lemma";
end;

local val _ = set_goal([], ⌜∀x⦁ IxRan (Param_∅ x) = {x}⌝);
val _ = a (rewrite_tac [get_spec ⌜IxRan⌝, get_spec ⌜Param_∅⌝, sets_ext_clauses]);
val _ = a (REPEAT strip_tac);
(* *** Goal "1" *** *)
val _ = a (POP_ASM_T ante_tac THEN cases_tac ⌜α = ∅⋎g⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
val _ = a (∃_tac ⌜∅⋎g⌝ THEN asm_rewrite_tac[]);
in val ixran_param_∅_lemma = save_pop_thm "ixran_param_∅_lemma";
end;

local val _ = set_goal([], ⌜∀x⦁ IxVal (Param_∅ x) ∅⋎g = x⌝);
val _ = a (rewrite_tac [get_spec ⌜IxVal⌝, get_spec ⌜Param_∅⌝, sets_ext_clauses]);
in val ixval_param_∅_lemma = save_pop_thm "ixval_param_∅_lemma";
end;

local val _ = set_goal([], ⌜∀x⦁ ValueOf (Param_∅ x ∅⋎g) = x⌝);
val _ = a (rewrite_tac [get_spec ⌜Param_∅⌝]);
in val valueof_param_∅_lemma = save_pop_thm "valueof_param_∅_lemma";
end;

local val _ = set_goal([], ⌜∀x y⦁ Param_∅ x y = Undefined ⇔ ¬ y = ∅⋎g⌝);
val _ = a (rewrite_tac [get_spec ⌜Param_∅⌝]);
val _ = a (REPEAT ∀_tac);
val _ = a (cases_tac ⌜y = ∅⋎g⌝ THEN asm_rewrite_tac[]);
in val param_∅_undefined_lemma = save_pop_thm "param_∅_undefined_lemma";
end;

add_pc_thms "'sfp" (map get_spec [] @ [ixdom_param_∅_lemma, ixran_param_∅_lemma, ixval_param_∅_lemma,
	valueof_param_∅_lemma, param_∅_undefined_lemma]);

set_merge_pcs ["misc2", "'ifos", "'sfp"];

set_goal([], ⌜∀V r⦁ Increasing (V ◁⋎o ExsSRO (V, r)) (ExsVaO (V2IxSet V, (V, r))) Param_∅⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac (map get_spec [⌜Increasing⌝, ⌜$◁⋎o⌝, ⌜ExsVaO⌝, ⌜IxO2⌝, ⌜IxO⌝, ⌜Pw⌝, ⌜OptO⌝, ⌜V2IxSet⌝])
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
a (var_elim_nth_asm_tac 4);
val Param_∅_Increasing_lemma = save_pop_thm "Param_∅_Increasing_lemma";

set_goal([], ⌜∀V W r⦁ Increasing (W ◁⋎o ExsSRO (V, r)) (ExsVaO (V2IxSet W, (V, r))) Param_∅⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac (map get_spec [⌜Increasing⌝, ⌜$◁⋎o⌝, ⌜ExsVaO⌝, ⌜IxO2⌝, ⌜IxO⌝, ⌜Pw⌝, ⌜OptO⌝, ⌜V2IxSet⌝])
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]
	THEN_TRY PC_T1 "hol1" asm_prove_tac[]);
val Param_∅_Increasing_lemma2 = save_pop_thm "Param_∅_Increasing_lemma2";
=TEX
}%ignore

The ``semantic functor'', a parameterised partial relation transformation, is then defined thus:

ⓈHOLCONST
│ ⦏Sf⦎: GS SET → (GS, FTV) BR → (GS, FTV) BR
├─────────
│ ∀ d $∈⋎v⦁ Sf d $∈⋎v =
│	λm s⦁ EvalForm (EvalCf_ftv, $≤⋎t⋎4, (d, $∈⋎v)) s (Param_∅ m)
■

It is easily shown to be monotonic.

=GFT
⦏sf_increasing_thm⦎ =
   ⊢ ∀ d⦁ Increasing $≤⋎∈ $≤⋎∈ (Sf d)
=TEX

\ignore{
=SML
set_merge_pcs ["misc21", "'ifos", "'sfp"];
set_goal([], ⌜∀d⦁ Increasing $≤⋎∈ $≤⋎∈ (Sf d)⌝);
a (strip_tac THEN LEMMA_T
	⌜Sf d = (λr m s⦁ r s (Param_∅ m)) o (λ$∈⋎v⦁ EvalForm (EvalCf_ftv, $≤⋎t⋎4, (d, $∈⋎v)))⌝
	rewrite_thm_tac
	THEN1 rewrite_tac [get_spec ⌜Sf⌝]);
a (bc_tac [increasing_funcomp_thm]);
a (∃_tac ⌜Pw (Pw $≤⋎t⋎4)⌝ THEN strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜Increasing⌝, get_spec ⌜$≤⋎∈⌝]);
a (REPEAT strip_tac);
a (asm_tac ≤⋎t⋎4_crpou_thm);
a (asm_tac evalcf_ftv_increasing_lemma);
a (ALL_FC_T (MAP_EVERY (fn t => fc_tac [(rewrite_rule
	[get_spec ⌜Increasing⌝, get_spec ⌜RvO⌝] t)])) [evalform_increasing_thm]);
a (POP_ASM_T (asm_tac o (rewrite_rule [get_spec ⌜Pw⌝])));
a (asm_rewrite_tac [get_spec ⌜Pw⌝]);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜Increasing⌝, get_spec ⌜$≤⋎∈⌝, get_spec ⌜Pw⌝, get_spec ⌜Param_∅⌝]
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[]);
val sf_increasing_thm = save_pop_thm "sf_increasing_thm";

add_pc_thms "'sfp" (map get_spec [] @ [sf_increasing_thm]);
set_merge_pcs ["misc21", "'ifos", "'sfp"];
=TEX
}%ignore

We need to show that the essences of objects after application of the semantic functor depend only on their extension and essence before application of the functor.
One way of expressing this is by stating that the identity function is an order morphism of between two distinct orderings of our syntax.
The orderings are respectively:

\begin{itemize}
\item the ordering of syntactic objects according to their extension and essence relative to some membership relation $\$∈⋎v$
\item the ordering of the objects according to their essence in the relation obtained when the semantic functor is applied to $\$∈⋎v$.
\end{itemize}

When the details are worked out we get:

=GFT
⦏essence_exstentional_lemma⦎ =
   ⊢ ∀ V W $∈⋎v
     ⦁ V ⊆ W ∧ V ⊆ Syntax
         ⇒ Increasing
           (V ◁⋎o ExsSRO (W, $∈⋎v))
           (EssSRO (V, Sf V $∈⋎v))
           CombI

⦏essence_exstentional_lemma2⦎ =
   ⊢ ∀ V W $∈⋎v
     ⦁ V ⊆ W ∧ V ⊆ Syntax
         ⇒ Increasing
           (W ◁⋎o ExsSRO (W, $∈⋎v))
           (EssSRO (V, Sf V $∈⋎v))
           CombI
=TEX

\ignore{
=SML
set_merge_pcs ["misc2", "'ifos", "'sfp"];

set_goal([], ⌜∀V W $∈⋎v⦁ V ⊆ W ∧ V ⊆ Syntax ⇒ Increasing (V ◁⋎o ExsSRO (W, $∈⋎v)) (EssSRO (V, Sf V $∈⋎v)) CombI⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜Increasing⌝, get_spec ⌜ExsSRO⌝, get_spec ⌜EssSRO⌝, get_spec ⌜ExtSRO⌝,
			get_spec ⌜ConjOrder⌝, get_spec ⌜Sf⌝, get_spec ⌜$◁⋎o⌝]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (lemma_tac ⌜ExsVaO (V2IxSet W, W, $∈⋎v) (Param_∅ x) (Param_∅ y)⌝);
(* *** Goal "1" *** *)
a (asm_rewrite_tac [get_spec ⌜Increasing⌝, get_spec ⌜ExsVaO⌝, get_spec ⌜IxO2⌝, get_spec ⌜ConjOrder⌝,
		get_spec ⌜IxO⌝, get_spec ⌜IxO2⌝, get_spec ⌜V2IxSet⌝, get_spec ⌜Pw⌝, get_spec ⌜OptO⌝,
		get_spec ⌜ExsSRO⌝, get_spec ⌜ExtSRO⌝, get_spec ⌜EssSRO⌝]);
a (LEMMA_T ⌜x ∈ W ∧ y ∈ W⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" asm_prove_tac[]);
a (strip_tac THEN cond_cases_tac ⌜x' = ∅⋎g⌝);
a (REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜z ∈ Syntax⌝ THEN1 PC_T1 "hol1" asm_prove_tac[]);
a (all_fc_tac [rewrite_rule [get_spec ⌜Increasing⌝] evalform_increasing_thm4]);
val essence_exstentional_lemma = save_pop_thm "essence_exstentional_lemma";

set_goal([], ⌜∀V W $∈⋎v⦁ V ⊆ W ∧ V ⊆ Syntax ⇒ Increasing (W ◁⋎o ExsSRO (W, $∈⋎v)) (EssSRO (V, Sf V $∈⋎v)) CombI⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜Increasing⌝, get_spec ⌜ExsSRO⌝, get_spec ⌜EssSRO⌝, get_spec ⌜ExtSRO⌝,
			get_spec ⌜ConjOrder⌝, get_spec ⌜Sf⌝, get_spec ⌜$◁⋎o⌝]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (lemma_tac ⌜ExsVaO (V2IxSet W, W, $∈⋎v) (Param_∅ x) (Param_∅ y)⌝);
(* *** Goal "1" *** *)
a (asm_rewrite_tac [get_spec ⌜Increasing⌝, get_spec ⌜ExsVaO⌝, get_spec ⌜IxO2⌝, get_spec ⌜ConjOrder⌝,
		get_spec ⌜IxO⌝, get_spec ⌜IxO2⌝, get_spec ⌜V2IxSet⌝, get_spec ⌜Pw⌝, get_spec ⌜OptO⌝,
		get_spec ⌜ExsSRO⌝, get_spec ⌜ExtSRO⌝, get_spec ⌜EssSRO⌝]);
a (strip_tac THEN cond_cases_tac ⌜x' = ∅⋎g⌝);
a (REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜z ∈ Syntax⌝ THEN1 PC_T1 "hol1" asm_prove_tac[]);
a (all_fc_tac [rewrite_rule [get_spec ⌜Increasing⌝] evalform_increasing_thm4]);
val essence_exstentional_lemma2 = save_pop_thm "essence_exstentional_lemma2";

set_merge_pcs ["misc21", "'ifos", "'sfp"];
=TEX
}%ignore

Note that the orders between the identity function is here proven to be a morphism are not restricted to the syntax of infinitary set theory, but cover the whole type GS, and this fact will be essential to some of the subsequent proofs, since we will make special use of $⌜∅⋎g⌝$ as an extra pseudo-set.

\subsection{Properties of Fixed Points}

The first property of interest concerns the conditions under which a fixed point of the semantic functor yields an extensional model of set theory.

I suppose we might start by saying what a fixed point is:

ⓈHOLCONST
│ ⦏SFFixp⦎ : GS SET → (GS, FTV)BR → BOOL
├───────────
│ ∀d r⦁ SFFixp d r ⇔ Sf d r = r
■

I am interested in interpretations of classical two-valued set theory and therefore will consider mainly fixed points which are total over the domain.

ⓈHOLCONST
│ ⦏TotalOver⦎ : 'a SET → ('a, FTV)BR → BOOL
├───────────
│ ∀ V r⦁ TotalOver V r ⇔ ∀x y⦁
│	if x ∈ V ∧ y ∈ V
│	then r x y = fTrue ∨ r x y = fFalse
│	else T
■

=GFT
⦏totover_lemma⦎ =
   ⊢ ∀ V r
     ⦁ TotalOver V r
         ⇒ (∀ x y⦁ x ∈ V ∧ y ∈ V ⇒ r x y = fTrue ∨ r x y = fFalse)

⦏totover_true_lemma⦎ =
   ⊢ ∀ V r
     ⦁ TotalOver V r
         ⇒ (∀ x y⦁ x ∈ V ∧ y ∈ V ⇒ (fTrue ≤⋎t⋎4 r x y ⇔ r x y = fTrue))

⦏totover_false_lemma⦎ =
  ⊢ ∀ V r
     ⦁ TotalOver V r
         ⇒ (∀ x y⦁ x ∈ V ∧ y ∈ V ⇒ (fFalse ≤⋎t⋎4 r x y ⇔ r x y = fFalse))
=TEX

\ignore{
=SML
set_goal([], ⌜∀V r⦁ TotalOver V r ⇒ ∀x y⦁ x ∈ V ∧ y ∈ V ⇒ r x y = fTrue ∨ r x y = fFalse⌝);
a (rewrite_tac [get_spec ⌜TotalOver⌝] THEN REPEAT_N 6 strip_tac);
a (LIST_SPEC_NTH_ASM_T 3 [⌜x⌝,⌜y⌝] ante_tac THEN rewrite_tac[asm_rule ⌜x ∈ V⌝, asm_rule ⌜y ∈ V⌝]);
val totover_lemma = save_pop_thm "totover_lemma";

local val _ = set_goal([], ⌜∀V r⦁ TotalOver V r ⇒ ∀x y⦁ x ∈ V ∧ y ∈ V ⇒ (fTrue ≤⋎t⋎4 r x y ⇔ r x y = fTrue)⌝);
val _ = a (rewrite_tac [get_spec ⌜TotalOver⌝] THEN REPEAT_N 6 strip_tac);
val _ = a (LIST_SPEC_NTH_ASM_T 3 [⌜x⌝,⌜y⌝] ante_tac THEN rewrite_tac[asm_rule ⌜x ∈ V⌝, asm_rule ⌜y ∈ V⌝]);
val _ = a (strip_tac THEN asm_rewrite_tac[]);
in val totover_true_lemma = save_pop_thm "totover_true_lemma";
end;

local val _ = set_goal([], ⌜∀V r⦁ TotalOver V r ⇒ ∀x y⦁ x ∈ V ∧ y ∈ V ⇒ (fFalse ≤⋎t⋎4 r x y ⇔ r x y = fFalse)⌝);
val _ = a (rewrite_tac [get_spec ⌜TotalOver⌝] THEN REPEAT_N 6 strip_tac);
val _ = a (LIST_SPEC_NTH_ASM_T 3 [⌜x⌝,⌜y⌝] ante_tac THEN rewrite_tac[asm_rule ⌜x ∈ V⌝, asm_rule ⌜y ∈ V⌝]);
val _ = a (strip_tac THEN asm_rewrite_tac[]);
in val totover_false_lemma = save_pop_thm "totover_false_lemma";
end;
=TEX
}%ignore

If a relationship is total over some domain we can convert it to a boolean relation, without loss of information (provided we remember the domain).

ⓈHOLCONST
│ ⦏BoolRel⦎ : ('a, FTV)BR → ('a, BOOL)BR
├───────────
│ ∀ r:('a, FTV)BR⦁ BoolRel r = λx y⦁ fTrue ≤⋎t⋎4 r x y
■

=GFT
=TEX

\ignore{
This one probably isn't going to be useful.

 ⓈHOLCONST
│ ⦏EqRel⦎ : 'a SET → ('a, FTV)BR → ('a, FTV)BR
├───────────
│ ∀ V r⦁ EqRel V r = λx y⦁
│	if x ∈ V ∧ y ∈ V
│	then
│	Lub $≤⋎t⋎4 {t |
│		(x = y ∨ ∀z⦁ z ∈ V ⇒
│				fTrue ≤⋎t⋎4 r x z ∧ fTrue ≤⋎t⋎4 r y z
│				∨ fFalse ≤⋎t⋎4 r x z ∧ fFalse ≤⋎t⋎4 r y z)
│		∧ t = fTrue
│	∨	(∃z⦁ z ∈ V ∧
│				(fTrue ≤⋎t⋎4 r x z ∧ fFalse ≤⋎t⋎4 r y z
│				∨ fFalse ≤⋎t⋎4 r x z ∧ fTrue ≤⋎t⋎4 r y z))
│		∧ t = fFalse
│	}
│	else fB
 ■

=GFT
⦏eqrel_ftrue_lemma⦎ =
   ⊢ ∀ V r x y
     ⦁ fTrue ≤⋎t⋎4 EqRel V r x y
         = (x ∈ V ∧ y ∈ V ∧
	   (x = y
             ∨ (∀ z⦁ z ∈ V
                 ⇒ fTrue ≤⋎t⋎4 r x z ∧ fTrue ≤⋎t⋎4 r y z
                   ∨ fFalse ≤⋎t⋎4 r x z ∧ fFalse ≤⋎t⋎4 r y z)))

⦏eqrel_refl_lemma⦎ =
   ⊢ ∀ V pr x⦁ x ∈ V ⇒ fTrue ≤⋎t⋎4 EqRel V pr x x
=TEX
=GFT
⦏eqrel_sym_lemma⦎ =
   ⊢ ∀ V pr x y
     ⦁ x ∈ V ∧ y ∈ V ∧ fTrue ≤⋎t⋎4 EqRel V pr x y
         ⇒ fTrue ≤⋎t⋎4 EqRel V pr y x

⦏eqrel_boolrel_lemma⦎ =
   ⊢ ∀ V r
     ⦁ TotalOver V r
         ⇒ (∀ x y
         ⦁ x ∈ V ∧ y ∈ V
             ⇒ (BoolRel (EqRel V r) x y
               ⇔ (∀ z⦁ z ∈ V ⇒ (BoolRel r x z ⇔ BoolRel r y z))))
=TEX

\ignore{
=IGN
local val _ = set_goal ([], ⌜∀ V r x y⦁ fTrue ≤⋎t⋎4 EqRel V r x y
	⇔ x ∈ V ∧ y ∈ V
	∧ (x = y ∨ (∀z⦁ z ∈ V ⇒	fTrue ≤⋎t⋎4 r x z ∧ fTrue ≤⋎t⋎4 r y z
			∨ fFalse ≤⋎t⋎4 r x z ∧ fFalse ≤⋎t⋎4 r y z))⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜EqRel⌝]);
val _ = a (cases_tac ⌜x∈V⌝ THEN cases_tac ⌜y∈V⌝ THEN asm_rewrite_tac[≤⋎t⋎4_lub_islub_lemma]);
val _ = a (CASES_T ⌜x = y ∨ (∀ z⦁ z ∈ V ⇒ fTrue ≤⋎t⋎4 r x z ∧ fTrue ≤⋎t⋎4 r y z ∨ fFalse ≤⋎t⋎4 r x z ∧ fFalse ≤⋎t⋎4 r y z)⌝ asm_tac
	THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
val _ = a (LEMMA_T ⌜fTrue ∈ {t
                 |t = fTrue
                     ∨ (∃ z⦁ z ∈ V ∧ (fTrue ≤⋎t⋎4 r x z ∧ fFalse ≤⋎t⋎4 r y z ∨ fFalse ≤⋎t⋎4 r x z ∧ fTrue ≤⋎t⋎4 r y z))
                       ∧ t = fFalse} ⌝ asm_tac
	THEN1 rewrite_tac[]);
val _ = a (asm_tac ≤⋎t⋎4_lubs_exist_thm);
val _ = a (fc_tac [less_lub_lemma]);
val _ = a (asm_fc_tac[]);
(* *** Goal "2" *** *)
val _ = a (LEMMA_T ⌜{t
                   |(∃ z⦁ z ∈ V ∧ (fTrue ≤⋎t⋎4 r x z ∧ fFalse ≤⋎t⋎4 r y z ∨ fFalse ≤⋎t⋎4 r x z ∧ fTrue ≤⋎t⋎4 r y z))
                       ∧ t = fFalse} ⊆ {fFalse}⌝ asm_tac
	THEN1 (PC_T1 "hol1" rewrite_tac[] THEN REPEAT strip_tac));
val _ = a (strip_asm_tac (list_∀_elim
	[⌜{t
             |(∃ z⦁ z ∈ V ∧ (fTrue ≤⋎t⋎4 r x z ∧ fFalse ≤⋎t⋎4 r y z ∨ fFalse ≤⋎t⋎4 r x z ∧ fTrue ≤⋎t⋎4 r y z)) ∧ t = fFalse}⌝,
	⌜{fFalse}⌝] (hd(ufc_rule [lub_sub_lemma] [≤⋎t⋎4_lubs_exist_thm]))));
val _ = a (contr_tac);
val _ = a (all_asm_fc_tac [≤⋎t⋎4_trans_thm]);
val _ = a (POP_ASM_T ante_tac);
val _ = a (asm_tac (list_∀_elim [⌜{fFalse}⌝] (hd(ufc_rule [lub_lub_lemma2] [≤⋎t⋎4_lubs_exist_thm]))));
val _ = a (fc_tac [get_spec ⌜IsLub⌝]);
val _ = a (LEMMA_T ⌜IsUb $≤⋎t⋎4 {fFalse} fFalse⌝ asm_tac THEN1 rewrite_tac[]);
val _ = a (asm_fc_tac[]);
val _ = a (strip_tac THEN all_asm_fc_tac [≤⋎t⋎4_trans_thm]);
in val eqrel_ftrue_lemma = save_pop_thm "eqrel_ftrue_lemma";
end;

local val _ = set_goal ([], ⌜∀V pr x⦁ x ∈ V ⇒ fTrue ≤⋎t⋎4 EqRel V pr x x⌝);
val _ = a (rewrite_tac [eqrel_ftrue_lemma]);
in val eqrel_refl_lemma = pop_thm();
end;

local val _ = set_goal ([], ⌜∀V pr x y⦁ x ∈ V ∧ y ∈ V ∧ fTrue ≤⋎t⋎4 EqRel V pr x y ⇒ fTrue ≤⋎t⋎4 EqRel V pr y x⌝);
val _ = a (rewrite_tac [eqrel_ftrue_lemma]
	THEN REPEAT strip_tac 
	THEN (asm_fc_tac[])
	THEN_TRY asm_rewrite_tac[]
	THEN var_elim_asm_tac ⌜x = y⌝);
in val eqrel_sym_lemma = pop_thm();
end;

local val _ = set_goal([], ⌜∀V r⦁ TotalOver V r ⇒ ∀x y⦁ x ∈ V ∧ y ∈ V ⇒
	(BoolRel (EqRel V r) x y ⇔ ∀z⦁ z ∈ V ⇒ (BoolRel r x z ⇔ BoolRel r y z))⌝);
val _ = a (rewrite_tac [get_spec ⌜BoolRel⌝, eqrel_ftrue_lemma]);
val _ = a (REPEAT_N 6 strip_tac THEN asm_rewrite_tac[]);
val _ = a (cases_tac ⌜x=y⌝ THEN asm_rewrite_tac[]);
val _ = a (fc_tac [get_spec ⌜TotalOver⌝]);
val _ = a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
val _ = a (spec_nth_asm_tac 3 ⌜z⌝ THEN_TRY asm_rewrite_tac[]);
val _ = a (POP_ASM_T discard_tac THEN REPEAT_N 2 (POP_ASM_T ante_tac));
val _ = a (list_spec_nth_asm_tac 3 [⌜x⌝, ⌜z⌝] THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2" *** *)
val _ = a (spec_nth_asm_tac 3 ⌜z⌝ THEN_TRY asm_rewrite_tac[]);
val _ = a (POP_ASM_T ante_tac THEN POP_ASM_T discard_tac THEN POP_ASM_T ante_tac);
val _ = a (list_spec_nth_asm_tac 3 [⌜y⌝, ⌜z⌝] THEN_TRY asm_rewrite_tac[]);
(* *** Goal "3" *** *)
val _ = a (POP_ASM_T ante_tac);
val _ = a (list_spec_nth_asm_tac 3 [⌜x⌝, ⌜z⌝] THEN_TRY asm_rewrite_tac[]);
(* *** Goal "4" *** *)
val _ = a (POP_ASM_T ante_tac);
val _ = a (SPEC_NTH_ASM_T 2 ⌜z⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
val _ = a (list_spec_nth_asm_tac 3 [⌜y⌝, ⌜z⌝] THEN_TRY asm_rewrite_tac[]);
(* *** Goal "5" *** *)
val _ = a (POP_ASM_T ante_tac);
val _ = a (SPEC_NTH_ASM_T 2 ⌜z⌝ (rewrite_thm_tac o eq_sym_rule o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
val _ = a (list_spec_nth_asm_tac 3 [⌜x⌝, ⌜z⌝] THEN_TRY asm_rewrite_tac[]);
(* *** Goal "6" *** *)
val _ = a (POP_ASM_T ante_tac);
val _ = a (list_spec_nth_asm_tac 3 [⌜y⌝, ⌜z⌝] THEN_TRY asm_rewrite_tac[]);
in val eqrel_boolrel_lemma = save_pop_thm "eqrel_boolrel_lemma";
end;
=TEX
}%ignore

It turns out that {\it EqRel} is not transitive, and so its probably not going to be much use.
It not clear that reformulation is required, since the equality relation can be defined as a function on the boolean version of a total fixed point, so there may be no need for a partial version.
When I wrote it I thought it would figure in the reasoning about the required properties of total fixed points, but that was probably a mistake.

}%ignore

Having chosen representatives for sets which are not canonical, we will be taking a quotient to eliminate redundancy.
Two complementary concepts are useful in this, the {\it extension} of a set (which is the collection of its members) and the {\it essence} of a set (which is the collection of things of which it is a member).

These concepts don't work out very tidily when we are dealing with partial membership relationships.
It seems easier not to formally define them but to define the relationships between two representatives whose extensions and essences are the same.

We now provide two ways of defining an equality relation over a boolean membership relationship.

The first is the obvious definition for set theoretic equality, two sets being equal if they have the same extension.

ⓈHOLCONST
│ ⦏BEqRel⦎ : GS SET → (GS, BOOL)BR → (GS, BOOL)BR
├───────────
│ ∀V r⦁ BEqRel V r = λx y⦁ ∀z⦁ z ∈ V ⇒ (r z x ⇔ r z y)
■

The second is a stricter definition, two sets are equivalent if they have the same extension and the same essence,

ⓈHOLCONST
│ ⦏BEqqRel⦎ : GS SET → (GS, BOOL)BR → (GS, BOOL)BR
├───────────
│ ∀V r⦁ BEqqRel V r = λx y⦁ ∀z⦁ z ∈ V ⇒ (r z x ⇔ r z y) ∧ (r x z ⇔ r y z)
■

=GFT
⦏BEqqRel_exs_lemma⦎ =
   ⊢ ∀ V r x y⦁ x ∈ V ∧ y ∈ V ∧ BEqqRel V r x y ⇒ r x x = r y y ∧ r x y = r y x
=TEX

\ignore{
=SML
set_goal([], ⌜∀V r x y⦁ x ∈ V ∧ y ∈ V ∧ BEqqRel V r x y ⇒ (r x x ⇔ r y y) ∧ (r x y ⇔ r y x)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜BEqqRel⌝] THEN strip_tac);
a (SPEC_NTH_ASM_T 1 ⌜x⌝ (STRIP_THM_THEN asm_tac o (rewrite_rule [asm_rule ⌜x ∈ V⌝])));
a (SPEC_NTH_ASM_T 3 ⌜y⌝ (STRIP_THM_THEN asm_tac o (rewrite_rule [asm_rule ⌜y ∈ V⌝])));
a (asm_rewrite_tac[]);
val BEqqRel_exs_lemma = save_pop_thm "BEqqRel_exs_lemma";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏BoolEqRel⦎ : GS SET → (GS, FTV)BR → (GS, BOOL)BR
├───────────
│ ∀V r⦁ BoolEqRel V r = BEqRel V (BoolRel r)
■

ⓈHOLCONST
│ ⦏BoolEqqRel⦎ : GS SET → (GS, FTV)BR → (GS, BOOL)BR
├───────────
│ ∀V r⦁ BoolEqqRel V r = BEqqRel V (BoolRel r)
■

=GFT
⦏beqrel_equiv_lemma⦎ =
	⊢ ∀ V r⦁ Equiv (V, BEqRel V r)

⦏beqqrel_equiv_lemma⦎ =
	⊢ ∀ V r⦁ Equiv (V, BEqqRel V r)

⦏booleqrel_equiv_lemma⦎ =
	⊢ ∀ V r⦁ Equiv (V, BoolEqRel V r)

⦏booleqqrel_equiv_lemma⦎ =
	⊢ ∀ V r⦁ Equiv (V, BoolEqqRel V r)
=TEX

\ignore{
=SML
local val _ = set_goal([], ⌜∀V r⦁ Equiv (V, BEqRel V r)⌝);
val _ = a (rewrite_tac[get_spec ⌜Equiv⌝, get_spec ⌜BEqRel⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
val _ = a (rewrite_tac [get_spec ⌜Refl⌝] THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
val _ = a (rewrite_tac [get_spec ⌜Sym⌝] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
val _ = a (SPEC_NTH_ASM_T 3 ⌜z⌝ (asm_rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
(* *** Goal "2.2" *** *)
val _ = a (POP_ASM_T ante_tac THEN (SPEC_NTH_ASM_T 2 ⌜z⌝ (asm_rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝]))));
(* *** Goal "3" *** *)
val _ = a (rewrite_tac [get_spec ⌜Trans⌝] THEN REPEAT strip_tac);
(* *** Goal "3.1" *** *)
val _ = a (SPEC_NTH_ASM_T 4 ⌜z'⌝ (asm_tac o (rewrite_rule [asm_rule ⌜z' ∈ V⌝])));
val _ = a (SPEC_NTH_ASM_T 4 ⌜z'⌝ (asm_tac o (rewrite_rule [asm_rule ⌜z' ∈ V⌝])));
val _ = a (SYM_ASMS_T rewrite_tac);
(* *** Goal "3.2" *** *)
val _ = a (SPEC_NTH_ASM_T 4 ⌜z'⌝ (asm_tac o (rewrite_rule [asm_rule ⌜z' ∈ V⌝])));
val _ = a (SPEC_NTH_ASM_T 4 ⌜z'⌝ (asm_tac o (rewrite_rule [asm_rule ⌜z' ∈ V⌝])));
val _ = a (asm_rewrite_tac []);
in val beqrel_equiv_lemma = save_pop_thm "beqrel_equiv_lemma";
end;

local val _ = set_goal([], ⌜∀V r⦁ Equiv (V, BEqqRel V r)⌝);
val _ = a (rewrite_tac[get_spec ⌜Equiv⌝, get_spec ⌜BEqqRel⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
val _ = a (rewrite_tac [get_spec ⌜Refl⌝] THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
val _ = a (rewrite_tac [get_spec ⌜Sym⌝] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
val _ = a (SPEC_NTH_ASM_T 3 ⌜z⌝ (asm_rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
(* *** Goal "2.2" *** *)
val _ = a (POP_ASM_T ante_tac THEN (SPEC_NTH_ASM_T 2 ⌜z⌝ (asm_rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝]))));
(* *** Goal "2.3" *** *)
val _ = a (POP_ASM_T ante_tac THEN (SPEC_NTH_ASM_T 2 ⌜z⌝ (asm_rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝]))));
(* *** Goal "2.4" *** *)
val _ = a (POP_ASM_T ante_tac THEN (SPEC_NTH_ASM_T 2 ⌜z⌝ (asm_rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝]))));
(* *** Goal "3" *** *)
val _ = a (rewrite_tac [get_spec ⌜Trans⌝] THEN REPEAT strip_tac);
(* *** Goal "3.1" *** *)
val _ = a (SPEC_NTH_ASM_T 4 ⌜z'⌝ (asm_tac o (rewrite_rule [asm_rule ⌜z' ∈ V⌝])));
val _ = a (SPEC_NTH_ASM_T 4 ⌜z'⌝ (asm_tac o (rewrite_rule [asm_rule ⌜z' ∈ V⌝])));
val _ = a (SYM_ASMS_T rewrite_tac);
(* *** Goal "3.2" *** *)
val _ = a (SPEC_NTH_ASM_T 4 ⌜z'⌝ (asm_tac o (rewrite_rule [asm_rule ⌜z' ∈ V⌝])));
val _ = a (SPEC_NTH_ASM_T 4 ⌜z'⌝ (asm_tac o (rewrite_rule [asm_rule ⌜z' ∈ V⌝])));
val _ = a (asm_rewrite_tac []);
(* *** Goal "3.3" *** *)
val _ = a (POP_ASM_T ante_tac);
val _ = a (SPEC_NTH_ASM_T 3 ⌜z'⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z' ∈ V⌝])));
val _ = a (SPEC_NTH_ASM_T 2 ⌜z'⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z' ∈ V⌝])));
(* *** Goal "3.3" *** *)
val _ = a (POP_ASM_T ante_tac);
val _ = a (SPEC_NTH_ASM_T 3 ⌜z'⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z' ∈ V⌝])));
val _ = a (SPEC_NTH_ASM_T 2 ⌜z'⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z' ∈ V⌝])));
in val beqqrel_equiv_lemma = save_pop_thm "beqqrel_equiv_lemma";
end;

local val _ = set_goal([], ⌜∀V r⦁ Equiv (V, BoolEqRel V r)⌝);
val _ = a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜BoolEqRel⌝, beqrel_equiv_lemma]);
in val booleqrel_equiv_lemma = save_pop_thm "booleqrel_equiv_lemma";
end;

local val _ = set_goal([], ⌜∀V r⦁ Equiv (V, BoolEqqRel V r)⌝);
val _ = a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜BoolEqqRel⌝, beqqrel_equiv_lemma]);
in val booleqqrel_equiv_lemma = save_pop_thm "booleqqrel_equiv_lemma";
end;
=TEX
}%ignore

The notation for sets we are using here is not canonical so each set has multiple representatives and we do not have extensionality.
However, we can hope to be able to obtain an extensional interpretation by taking a quotient relative to extensional equality.
The following condition suffices for this to be possible.

What this says is that whenever two sets are not the members of all the same sets then they do not have the same members.

ⓈHOLCONST
│ ⦏PreExtensional⦎ : GS SET → (GS, FTV)BR → BOOL
├───────────
│ ∀d r⦁ PreExtensional d r ⇔ ¬ OverDefined d r ∧ ∀x y⦁ x ∈ d ∧ y ∈ d
│				⇒ (∃z⦁ z ∈ d ∧ IsLub $≤⋎t⋎4 {r x z; r y z} fT)
│				⇒ (∃z⦁ z ∈ d ∧ IsLub $≤⋎t⋎4 {r z x; r z y} fT)
■

However, that turns out a tad too strong (we need this to be a sufficient property to ensure that a total least fixed point is extensional, but it must be preserved by the semantic functor, and that one probably isn't).

ⓈHOLCONST
│ ⦏PreExtensional2⦎ : GS SET → (GS, FTV)BR → BOOL
├───────────
│ ∀d r⦁ PreExtensional2 d r ⇔ ¬ OverDefined d r ∧ ∀x y⦁ x ∈ d ∧ y ∈ d
│				⇒ (∃z⦁ z ∈ d ∧ IsLub $≤⋎t⋎4 {r x z; r y z} fT)
│				⇒ (∃z⦁ z ∈ d ∧ IsLub $≤⋎t⋎4 {r z x; r z y} fT)
│				∨ Lub $≤⋎t⋎4 {r x x; r y y} = fT
│				∨ Lub $≤⋎t⋎4 {r x y; r y x} = fT
■

ⓈHOLCONST
│ ⦏PreExtensional3⦎ : GS SET → (GS, FTV)BR → BOOL
├───────────
│ ∀d r⦁ PreExtensional3 d r ⇔ ¬ OverDefined d r ∧ ∀x y⦁ x ∈ d ∧ y ∈ d
│				⇒ (∃z⦁ z ∈ d ∧ ¬ {r x z; r y z} ∈ CompFTV)
│				⇒ (∃z⦁ z ∈ d ∧ ¬ {r z x; r z y} ∈ CompFTV)
│				∨ ¬ {r x x; r y y} ∈ CompFTV
│				∨ ¬ {r x y; r y x} ∈ CompFTV
■

It is useful in the present context to have the following result:



=GFT
=TEX

\ignore{
=IGN
set_flag ("subgoal_package_quiet", false);

set_goal([], ⌜∀V r⦁ TotalOver V r ∧ PreExtensional3 V r ⇒ PreExtensional V r⌝);
a (REPEAT ∀_tac THEN rewrite_tac (map get_spec [⌜PreExtensional⌝, ⌜PreExtensional3⌝])
	THEN REPEAT strip_tac
	THEN fc_tac [totover_lemma]);
a (fc_tac [rewrite_rule [] (list_∀_elim [⌜{r x z; r y z}⌝, ⌜$≤⋎t⋎4⌝] islub_lub_lemma)]);
a (list_spec_nth_asm_tac 7 [⌜x⌝, ⌜y⌝]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜z⌝);
(* *** Goal "2" *** *)
a (∃_tac ⌜z'⌝
	THEN asm_rewrite_tac [rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝] lea_islub_lub_lemma)]);
(* *** Goal "3" *** *)

a (LIST_SPEC_NTH_ASM_T 7 [⌜x⌝, ⌜y⌝]
	(ante_tac o (rewrite_rule [asm_rule ⌜x ∈ V⌝, asm_rule ⌜y ∈ V⌝, asm_rule ⌜¬ {r x z; r y z} ∈ CompFTV⌝])));
a (rewrite_tac [prove_rule [] ⌜∀A B C⦁ A ⇒ B ∨ ¬ C ⇔ A ⇒ B ∨ ( ¬B ∧ ¬C)⌝]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜z⌝);
(* *** Goal "2" *** *)
a (∃_tac ⌜z'⌝
	THEN asm_rewrite_tac [rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝] lea_islub_lub_lemma)]);
(* *** Goal "3" *** *)

a (asm_rewrite_tac [rewrite_rule [] (list_∀_elim [⌜{r z' x; r z' y}⌝, ⌜$≤⋎t⋎4⌝] islub_lub_lemma)]);


=TEX
}%ignore

There is a corresponding property over the boolean version of a total partial relation.

ⓈHOLCONST
│ ⦏TotExtensional⦎ : GS SET → (GS, BOOL)BR → BOOL
├───────────
│ ∀d r⦁ TotExtensional d r ⇔ ∀x y⦁ x ∈ d ∧ y ∈ d
│				⇒ (∃z⦁ z ∈ d ∧ ¬(r x z ⇔ r y z))
│				⇒ (∃z⦁ z ∈ d ∧ ¬(r z x ⇔ r z y))
■

and a weakened version:

ⓈHOLCONST
│ ⦏TotExtensional2⦎ : GS SET → (GS, BOOL)BR → BOOL
├───────────
│ ∀d r⦁ TotExtensional2 d r ⇔ ∀x y⦁ x ∈ d ∧ y ∈ d
│				⇒ (∃z⦁ z ∈ d ∧ ¬(r x z ⇔ r y z))
│				⇒ (∃z⦁ z ∈ d ∧ ¬(r z x ⇔ r z y))
│				∨ ¬(r x x ⇔ r y y)
│				∨ ¬(r x y ⇔ r y x)
■

=GFT
⦏pre_tot_ext_lemma⦎ =
   ⊢ ∀ V pr
     ⦁ PreExtensional V pr ∧ TotalOver V pr ⇒ TotExtensional V (BoolRel pr)
=TEX

\ignore{
=SML
local val _ = set_goal ([], ⌜∀V pr⦁ PreExtensional V pr ∧ TotalOver V pr ⇒ TotExtensional V (BoolRel pr)⌝);
val _ = a (rewrite_tac (map get_spec [⌜PreExtensional⌝, ⌜TotExtensional⌝, ⌜BoolRel⌝])
	THEN REPEAT_N 6 strip_tac);
val _ = a (STRIP_T (STRIP_THM_THEN (STRIP_THM_THEN asm_tac)) THEN POP_ASM_T ante_tac);
val _ = a (strip_asm_tac (list_∀_elim [⌜V⌝, ⌜pr⌝]  totover_true_lemma));
val _ = a (LIST_SPEC_NTH_ASM_T 1 [⌜x⌝, ⌜z⌝] (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝, asm_rule ⌜x ∈ V⌝])));
val _ = a (LIST_SPEC_NTH_ASM_T 1 [⌜y⌝, ⌜z⌝] (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝, asm_rule ⌜y ∈ V⌝])));
val _ = a (STRIP_T asm_tac);
val _ = a (list_spec_nth_asm_tac 7 [⌜x⌝, ⌜y⌝]);
(* *** Goal "1" *** *)
val _ = a (spec_nth_asm_tac 1 ⌜z⌝);
val _ = a (swap_nth_asm_concl_tac 1);
val _ = a (LEMMA_T ⌜{pr x z; pr y z} = {fFalse; fTrue}⌝ rewrite_thm_tac
	THEN1 (asm_rewrite_tac[] THEN strip_tac));
val _ = a (fc_tac [get_spec ⌜TotalOver⌝]);
val _ = a (list_spec_nth_asm_tac 1 [⌜x⌝, ⌜z⌝]);
(* *** Goal "1.1" *** *)
val _ = a (list_spec_nth_asm_tac 2 [⌜y⌝, ⌜z⌝]);
(* *** Goal "1.1.1" *** *)
val _ = a (GET_NTH_ASM_T 6 strip_asm_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.1.2" *** *)
val _ = a (asm_rewrite_tac[] THEN contr_tac);
(* *** Goal "1.2" *** *)
val _ = a (list_spec_nth_asm_tac 2 [⌜y⌝, ⌜z⌝]);
(* *** Goal "1.2.1" *** *)
val _ = a (asm_rewrite_tac[] THEN contr_tac);
(* *** Goal "1.2.2" *** *)
val _ = a (swap_nth_asm_concl_tac 6 THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
val _ = a (∃_tac ⌜z'⌝ THEN asm_rewrite_tac[]);
val _ = a (SWAP_NTH_ASM_CONCL_T 1 (STRIP_THM_THEN asm_tac));
val _ = a (fc_tac [get_spec ⌜TotalOver⌝]);
val _ = a (list_spec_nth_asm_tac 1 [⌜z'⌝, ⌜x⌝]);
(* *** Goal "2.1" *** *)
val _ = a (list_spec_nth_asm_tac 2 [⌜z'⌝, ⌜y⌝]);
(* *** Goal "2.1.1" *** *)
val _ = a (asm_rewrite_tac[]);
val _ = a (rewrite_tac[get_spec ⌜IsLub⌝] THEN strip_tac);
val _ = a (∃_tac ⌜fTrue⌝ THEN REPEAT strip_tac THEN rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
val _ = a (swap_nth_asm_concl_tac 4 THEN asm_rewrite_tac[]); 
(* *** Goal "2.2" *** *)
val _ = a (list_spec_nth_asm_tac 2 [⌜z'⌝, ⌜y⌝]);
(* *** Goal "2.2.1" *** *)
val _ = a (swap_nth_asm_concl_tac 4 THEN asm_rewrite_tac[]); 
(* *** Goal "2.2.2" *** *)
val _ = a (asm_rewrite_tac[]);
val _ = a (rewrite_tac[get_spec ⌜IsLub⌝] THEN strip_tac);
val _ = a (∃_tac ⌜fFalse⌝ THEN REPEAT strip_tac THEN rewrite_tac[]);
in val pre_tot_ext_lemma = save_pop_thm "pre_tot_ext_lemma";
end;
=TEX
}%ignore

=GFT
⦏pre2_tot_ext_lemma⦎ =
   ⊢ ∀ V pr
     ⦁ PreExtensional2 V pr ∧ TotalOver V pr ⇒ TotExtensional2 V (BoolRel pr)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀V pr⦁ PreExtensional2 V pr ∧ TotalOver V pr ⇒ TotExtensional2 V (BoolRel pr)⌝);
val _ = a (rewrite_tac (map get_spec [⌜PreExtensional2⌝, ⌜TotExtensional2⌝, ⌜BoolRel⌝])
	THEN REPEAT_N 6 strip_tac);
val _ = a (STRIP_T (STRIP_THM_THEN (STRIP_THM_THEN asm_tac)) THEN POP_ASM_T ante_tac);
val _ = a (strip_asm_tac (list_∀_elim [⌜V⌝, ⌜pr⌝]  totover_true_lemma));
val _ = a (LIST_SPEC_NTH_ASM_T 1 [⌜x⌝, ⌜z⌝] (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝, asm_rule ⌜x ∈ V⌝])));
val _ = a (LIST_SPEC_NTH_ASM_T 1 [⌜y⌝, ⌜z⌝] (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝, asm_rule ⌜y ∈ V⌝])));
val _ = a (LIST_SPEC_NTH_ASM_T 1 [⌜x⌝, ⌜x⌝] (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝, asm_rule ⌜x ∈ V⌝])));
val _ = a (LIST_SPEC_NTH_ASM_T 1 [⌜y⌝, ⌜y⌝] (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝, asm_rule ⌜y ∈ V⌝])));
val _ = a (LIST_SPEC_NTH_ASM_T 1 [⌜x⌝, ⌜y⌝] (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜y ∈ V⌝, asm_rule ⌜x ∈ V⌝])));
val _ = a (LIST_SPEC_NTH_ASM_T 1 [⌜y⌝, ⌜x⌝] (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜x ∈ V⌝, asm_rule ⌜y ∈ V⌝])));
val _ = a (STRIP_T asm_tac);
a (rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜∀A B C⦁ A ∨ ¬ B ∨ ¬ C ⇔ B ⇒ C ⇒ A⌝]);
a (REPEAT (STRIP_T asm_tac));
val _ = a (list_spec_nth_asm_tac 9 [⌜x⌝, ⌜y⌝]);
(* *** Goal "1" *** *)
val _ = a (spec_nth_asm_tac 1 ⌜z⌝);
val _ = a (swap_nth_asm_concl_tac 1);
val _ = a (LEMMA_T ⌜{pr x z; pr y z} = {fFalse; fTrue}⌝ rewrite_thm_tac
	THEN1 (asm_rewrite_tac[] THEN strip_tac));
val _ = a (fc_tac [get_spec ⌜TotalOver⌝]);
val _ = a (list_spec_nth_asm_tac 1 [⌜x⌝, ⌜z⌝]);
(* *** Goal "1.1" *** *)
val _ = a (list_spec_nth_asm_tac 2 [⌜y⌝, ⌜z⌝]);
(* *** Goal "1.1.1" *** *)
val _ = a (GET_NTH_ASM_T 8 strip_asm_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.1.2" *** *)
val _ = a (asm_rewrite_tac[] THEN contr_tac);
(* *** Goal "1.2" *** *)
val _ = a (list_spec_nth_asm_tac 2 [⌜y⌝, ⌜z⌝]);
(* *** Goal "1.2.1" *** *)
val _ = a (asm_rewrite_tac[] THEN contr_tac);
(* *** Goal "1.2.2" *** *)
val _ = a (swap_nth_asm_concl_tac 8 THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
val _ = a (∃_tac ⌜z'⌝ THEN asm_rewrite_tac[]);
val _ = a (SWAP_NTH_ASM_CONCL_T 1 (STRIP_THM_THEN asm_tac));
val _ = a (fc_tac [get_spec ⌜TotalOver⌝]);
val _ = a (list_spec_nth_asm_tac 1 [⌜z'⌝, ⌜x⌝]);
(* *** Goal "2.1" *** *)
val _ = a (list_spec_nth_asm_tac 2 [⌜z'⌝, ⌜y⌝]);
(* *** Goal "2.1.1" *** *)
val _ = a (asm_rewrite_tac[]);
val _ = a (rewrite_tac[get_spec ⌜IsLub⌝] THEN strip_tac);
val _ = a (∃_tac ⌜fTrue⌝ THEN REPEAT strip_tac THEN rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
val _ = a (swap_nth_asm_concl_tac 4 THEN asm_rewrite_tac[]); 
(* *** Goal "2.2" *** *)
val _ = a (list_spec_nth_asm_tac 2 [⌜z'⌝, ⌜y⌝]);
(* *** Goal "2.2.1" *** *)
val _ = a (swap_nth_asm_concl_tac 4 THEN asm_rewrite_tac[]); 
(* *** Goal "2.2.2" *** *)
val _ = a (asm_rewrite_tac[]);
val _ = a (rewrite_tac[get_spec ⌜IsLub⌝] THEN strip_tac);
val _ = a (∃_tac ⌜fFalse⌝ THEN REPEAT strip_tac THEN rewrite_tac[]);
(* *** Goal "3" *** *)
a (swap_nth_asm_concl_tac 1);
a (fc_tac [totover_lemma]);
a (list_spec_nth_asm_tac 1 [⌜x⌝, ⌜x⌝]
	THEN list_spec_nth_asm_tac 2 [⌜y⌝, ⌜y⌝]
	THEN asm_rewrite_tac[]
	THEN (DROP_NTH_ASM_T 6 ante_tac)
	THEN asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (swap_nth_asm_concl_tac 1);
a (fc_tac [totover_lemma]);
a (list_spec_nth_asm_tac 1 [⌜x⌝, ⌜y⌝]
	THEN list_spec_nth_asm_tac 2 [⌜y⌝, ⌜x⌝]
	THEN (DROP_NTH_ASM_T 5 ante_tac)
	THEN asm_rewrite_tac[]);
val pre2_tot_ext_lemma = save_pop_thm "pre2_tot_ext_lemma";
=TEX
}%ignore

If a membership relation is total and pre-extensional over some domain, then we can obtain from it an extensional boolean membership structure whose domain is equivalence classes under co-extensionality of the original domain.

I will be looking to establish reasonable conditions under which the fixed points of the semantic functor will be {\it PreExtensional}, but first I need to establish that {\it PreExtensional}ity suffices for a fixedpoint of the semantic functor to yield and extensional interpretation of first order set theory.

\ignore{
=IGN
local val _ = set_goal([], ⌜∀V r⦁ TotalOver V r ∧ PreExtensional V r ⇒ Equiv (V, BoolRel r)⌝);
val _ = a (PC_T1 "hol1" rewrite_tac [get_spec ⌜TotalOver⌝, get_spec ⌜BoolRel⌝, get_spec ⌜Equiv⌝, get_spec ⌜PreExtensional⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
val _ = a (rewrite_tac [get_spec ⌜Refl⌝, eqrel_refl_lemma] THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
val _ = a (rewrite_tac [get_spec ⌜Sym⌝] THEN REPEAT strip_tac);
val _ = a (POP_ASM_T ante_tac);
val _ = a (ALL_FC_T rewrite_tac [eqrel_sym_lemma]);
(* *** Goal "3" *** *)
val _ = a (rewrite_tac [get_spec ⌜Trans⌝] THEN REPEAT strip_tac);
val _ = a (all_asm_fc_tac [eqrel_trans_lemma]);
in val eqrel_equiv_lemma = pop_thm();
end;
=TEX
}%ignore

My first shot at constructing a structure from a total fixed point used co-extensionality as equality, which is OK provided that the fixed point is pre-extensional, in which case the resulting structure is extensional.
This is it:

ⓈHOLCONST
│ ⦏MSfromSFF⦎ : GS SET × (GS, FTV) BR → GS SET SET × (GS SET, BOOL) BR
├───────────
│ ∀ (V:GS SET) (r:(GS, FTV) BR)⦁ MSfromSFF (V, r) =
│	let $∈⋎v = BoolRel r
│	and $=⋎v = BEqRel V (BoolRel r)
│	in (QuotientSet V $=⋎v, λs t⦁ ∀x y⦁ x ∈ s ∧ y ∈ t ⇒ x ∈⋎v y)		 
■

However, it now seems to me better to define the structure with an equality relation which is stricter if the membership relation is not pre-extensional.
The result is the same if it is pre-extensional (conjecture) but the advantage is that if it is not we still  get a sensible membership structure (though not an extensional one).

Put another way, this corrects a defect in the first version, that it doesn't work for non-extensional fixed points.
In order to get a good structure from a fixed point which is not pre-extensional, you have to regard two sets as distinct if they are not members of the same sets, even if they have the same extension.
The result is that the axiom of extensionality will not hold unqualified.
Admitting this possibility is a good idea since the kind of type structure I have in mind will probably be a model for stratified comprehension, and may not be compatible with full extensionality.

ⓈHOLCONST
│ ⦏MSfromSFF2⦎ : GS SET × (GS, FTV) BR → GS SET SET × (GS SET, BOOL) BR
├───────────
│ ∀ (V:GS SET) (r:(GS, FTV) BR)⦁ MSfromSFF2 (V, r) =
│	let $∈⋎v = BoolRel r
│	and $=⋎v = BEqqRel V (BoolRel r)
│	in (QuotientSet V $=⋎v, λs t⦁ ∀x y⦁ x ∈ s ∧ y ∈ t ⇒ x ∈⋎v y)		 
■

=GFT
⦏equivclass_mem_lemma⦎ =
   ⊢ ∀ V r x
     ⦁ x ∈ EquivClass (V, BEqRel V (BoolRel r)) z
         ⇔ x ∈ V ∧ (∀ y⦁ y ∈ V ⇒ (BoolRel r y x ⇔ BoolRel r y z))

⦏equivclass_mem_lemma2⦎ =
   ⊢ ∀ V r x⦁ x ∈ EquivClass (V, BEqqRel V (BoolRel r)) z
         ⇔ x ∈ V ∧ (∀ y⦁ y ∈ V
               ⇒ (BoolRel r y x ⇔ BoolRel r y z)
                 ∧ (BoolRel r x y ⇔ BoolRel r z y))
=TEX
=GFT
⦏rep_independence_lemma⦎ =
   ⊢ ∀ V r⦁ TotalOver V r ⇒ (∀ s t⦁ s ∈ V ∧ t ∈ V ⇒
		(let u = EquivClass (V, BoolEqqRel V r) s
		and v = EquivClass (V, BoolEqqRel V r) t
		in (∀ x y⦁ x ∈ u ∧ y ∈ v ⇒ BoolRel r x y)
		    ⇔ (∃ x y⦁ x ∈ u ∧ y ∈ v ∧ BoolRel r x y)))
=TEX
=GFT
⦏totpre_rep_independence_lemma⦎ =
   ⊢ ∀ V r⦁ TotalOver V r ∧ PreExtensional V r
         ⇒ (∀ s t⦁ s ∈ V ∧ t ∈ V
             ⇒ (let u = EquivClass (V, BoolEqRel V r) s
               and v = EquivClass (V, BoolEqRel V r) t
             in (∀ x y⦁ x ∈ u ∧ y ∈ v ⇒ BoolRel r x y)
               ⇔ (∃ x y⦁ x ∈ u ∧ y ∈ v ∧ BoolRel r x y)))
=TEX
=GFT
⦏totpre_rep_independence_lemma2⦎ =
   ⊢ ∀ V r⦁ TotalOver V r ∧ PreExtensional V r
         ⇒ (∀ s t u v
         ⦁ s ∈ V
               ∧ t ∈ V
               ∧ u ∈ V
               ∧ v ∈ V
               ∧ BoolEqRel V r s u
               ∧ BoolEqRel V r t v
             ⇒ (BoolRel r s t ⇔ BoolRel r u v))
=TEX
=GFT
⦏rep_independence_lemma2⦎ =
   ⊢ ∀ V r
     ⦁ TotalOver V r
         ⇒ (∀ s t u v
         ⦁ s ∈ V
               ∧ t ∈ V
               ∧ u ∈ V
               ∧ v ∈ V
               ∧ BoolEqqRel V r s u
               ∧ BoolEqqRel V r t v
             ⇒ (BoolRel r s t ⇔ BoolRel r u v))
=TEX
=GFT
⦏eq_eq_eqq_lemma⦎ =
   ⊢ ∀ V r
     ⦁ TotalOver V r ∧ PreExtensional V r
         ⇒ (∀ x y
         ⦁ x ∈ V ∧ y ∈ V
             ⇒ (BEqRel V (BoolRel r) x y ⇔ BEqqRel V (BoolRel r) x y))

⦏msfromsff_eq_lemma⦎ =
   ⊢ ∀ V r
     ⦁ TotalOver V r ∧ PreExtensional V r
         ⇒ MSfromSFF (V, r) = MSfromSFF2 (V, r)

⦏preext_ext_lemma⦎ =
   ⊢ ∀ V r
     ⦁ TotalOver V r ∧ PreExtensional V r ⇒ extensional (MSfromSFF (V, r))

⦏preext_ext_lemma2⦎ =
   ⊢ ∀ V r
     ⦁ TotalOver V r ∧ PreExtensional V r ⇒ extensional (MSfromSFF2 (V, r))
=TEX

\ignore{
=SML
set_merge_pcs ["misc21", "'ifos", "'sfp"];

local val _ = set_goal([],⌜∀V r x⦁ x ∈ EquivClass (V, BEqRel V (BoolRel r)) z ⇔ x ∈ V ∧ ∀y⦁ y ∈ V ⇒ (BoolRel r y x ⇔ BoolRel r y z)⌝);
val _ = a (rewrite_tac [get_spec ⌜EquivClass⌝, get_spec ⌜BEqRel⌝]);
val _ = a (REPEAT_N 9 strip_tac THEN_TRY asm_rewrite_tac[]
	THEN (ASM_FC_T1 fc_⇔_canon (rewrite_tac) []));
in val equivclass_mem_lemma = save_pop_thm "equivclass_mem_lemma";
end;

local val _ = set_goal([],⌜∀V r x⦁ x ∈ EquivClass (V, BEqqRel V (BoolRel r)) z ⇔
	x ∈ V ∧ ∀y⦁ y ∈ V ⇒ (BoolRel r y x ⇔ BoolRel r y z) ∧ (BoolRel r x y ⇔ BoolRel r z y)⌝);
val _ = a (rewrite_tac [get_spec ⌜EquivClass⌝, get_spec ⌜BEqqRel⌝]);
val _ = a (REPEAT_N 9 strip_tac THEN_TRY asm_rewrite_tac[]
	THEN (ASM_FC_T1 fc_⇔_canon (rewrite_tac) []));
in val equivclass_mem_lemma2 = save_pop_thm "equivclass_mem_lemma2";
end;

local val _ = set_goal([],⌜∀V r⦁ TotalOver V r ⇒ ∀s t⦁ s ∈ V ∧ t ∈ V ⇒
	let u = EquivClass (V, BoolEqqRel V r) s
	and v = EquivClass (V, BoolEqqRel V r) t
	in	((∀x y⦁ x ∈ u ∧ y ∈ v ⇒ BoolRel r x y) ⇔ (∃x y⦁ x ∈ u ∧ y ∈ v ∧ BoolRel r x y))⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜BoolEqqRel⌝, get_spec ⌜EquivClass⌝, let_def]
	THEN REPEAT_N 6 strip_tac);
(* *** Goal "1" *** *)
val _ = a (strip_tac);
val _ = a (∃_tac ⌜s⌝ THEN ∃_tac ⌜t⌝ THEN asm_rewrite_tac[]);
val _ = a (asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqqrel_equiv_lemma));
val _ = a (ufc_tac [get_spec ⌜Equiv⌝]);
val _ = a (ufc_tac [get_spec ⌜Refl⌝]);
val _ = a (list_spec_nth_asm_tac 6 [⌜s⌝, ⌜t⌝]
	THEN_TRY (all_asm_fc_tac [])
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2" *** *)
val _ = a (REPEAT strip_tac);
val _ = a (lemma_tac ⌜BEqqRel V (BoolRel r) x' x''⌝);
(* *** Goal "2.1" *** *)
val _ = a (lemma_tac ⌜BEqqRel V (BoolRel r) x' s⌝
	THEN1 (asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqqrel_equiv_lemma)
		THEN (fc_tac [get_spec ⌜Equiv⌝])
		THEN (fc_tac [get_spec ⌜Sym⌝])
		THEN (all_asm_fc_tac[])));
val _ = a ((asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqqrel_equiv_lemma)
		THEN (fc_tac [get_spec ⌜Equiv⌝])
		THEN (fc_tac [get_spec ⌜Trans⌝])
		THEN (list_spec_nth_asm_tac 1 [⌜x'⌝, ⌜s⌝, ⌜x''⌝])));
(* *** Goal "2.2" *** *)
val _ = a (lemma_tac ⌜BoolRel r x' y'⌝);
(* *** Goal "2.2.1" *** *)
val _ = a (lemma_tac ⌜BEqqRel V (BoolRel r) y y'⌝);
(* *** Goal "2.2.1.1" *** *)
val _ = a (lemma_tac ⌜BEqqRel V (BoolRel r) y t⌝
	THEN1 (asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqqrel_equiv_lemma)
		THEN (fc_tac [get_spec ⌜Equiv⌝])
		THEN (fc_tac [get_spec ⌜Sym⌝])
		THEN (all_asm_fc_tac[])));
val _ = a (lemma_tac ⌜BEqqRel V (BoolRel r) y y'⌝
	THEN1 (asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqqrel_equiv_lemma)
		THEN (fc_tac [get_spec ⌜Equiv⌝])
		THEN (fc_tac [get_spec ⌜Trans⌝])
		THEN (list_spec_nth_asm_tac 1 [⌜y⌝, ⌜t⌝, ⌜y'⌝])));
val _ = a (POP_ASM_T (asm_tac o (rewrite_rule[get_spec ⌜BEqqRel⌝])));
val _ = a (swap_nth_asm_concl_tac 7);
val _ = a (SPEC_NTH_ASM_T 2 ⌜x'⌝ (asm_rewrite_thm_tac o (rewrite_rule[asm_rule ⌜x' ∈ V⌝])));
(* *** Goal "2.2.2" *** *)
val _ = a (lemma_tac ⌜BEqqRel V (BoolRel r) y t⌝
	THEN1 (asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqqrel_equiv_lemma)
		THEN (fc_tac [get_spec ⌜Equiv⌝])
		THEN (fc_tac [get_spec ⌜Sym⌝])
		THEN (list_spec_nth_asm_tac 1 [⌜t⌝, ⌜y⌝])));
val _ = a (lemma_tac ⌜BEqqRel V (BoolRel r) y y'⌝
	THEN1 (asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqqrel_equiv_lemma)
		THEN (fc_tac [get_spec ⌜Equiv⌝])
		THEN (fc_tac [get_spec ⌜Trans⌝])
		THEN (list_spec_nth_asm_tac 1 [⌜y⌝, ⌜t⌝, ⌜y'⌝])));
val _ = a (POP_ASM_T (asm_tac o (rewrite_rule[get_spec ⌜BEqqRel⌝])));
val _ = a (swap_nth_asm_concl_tac 9);
val _ = a (SPEC_NTH_ASM_T 2 ⌜x'⌝ (rewrite_thm_tac o (rewrite_rule[asm_rule ⌜x' ∈ V⌝])));
val _ = a (DROP_NTH_ASM_T 5 (asm_tac o (rewrite_rule[get_spec ⌜BEqqRel⌝])));
val _ = a (SPEC_NTH_ASM_T 1 ⌜y'⌝ (rewrite_thm_tac o (rewrite_rule[asm_rule ⌜y' ∈ V⌝])));
val _ = a contr_tac;
in val rep_independence_lemma = save_pop_thm "rep_independence_lemma";
end;

local val _ = set_goal([],⌜∀V r⦁ TotalOver V r ∧ PreExtensional V r ⇒ ∀s t⦁ s ∈ V ∧ t ∈ V ⇒
	let u = EquivClass (V, BoolEqRel V r) s
	and v = EquivClass (V, BoolEqRel V r) t
	in	((∀x y⦁ x ∈ u ∧ y ∈ v ⇒ BoolRel r x y) ⇔ (∃x y⦁ x ∈ u ∧ y ∈ v ∧ BoolRel r x y))⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜BoolEqRel⌝, get_spec ⌜EquivClass⌝, let_def]
	THEN REPEAT_N 6 strip_tac);
(* *** Goal "1" *** *)
val _ = a (strip_tac);
val _ = a (∃_tac ⌜s⌝ THEN ∃_tac ⌜t⌝ THEN asm_rewrite_tac[]);
val _ = a (asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqrel_equiv_lemma));
val _ = a (ufc_tac [get_spec ⌜Equiv⌝]);
val _ = a (ufc_tac [get_spec ⌜Refl⌝]);
val _ = a (list_spec_nth_asm_tac 6 [⌜s⌝, ⌜t⌝]
	THEN_TRY (all_asm_fc_tac [])
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2" *** *)
val _ = a (REPEAT strip_tac);
val _ = a (lemma_tac ⌜BEqRel V (BoolRel r) x' x''⌝);
(* *** Goal "2.1" *** *)
val _ = a (lemma_tac ⌜BEqRel V (BoolRel r) x' s⌝
	THEN1 (asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqrel_equiv_lemma)
		THEN (fc_tac [get_spec ⌜Equiv⌝])
		THEN (fc_tac [get_spec ⌜Sym⌝])
		THEN (all_asm_fc_tac[])));
val _ = a ((asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqrel_equiv_lemma)
		THEN (fc_tac [get_spec ⌜Equiv⌝])
		THEN (fc_tac [get_spec ⌜Trans⌝])
		THEN (list_spec_nth_asm_tac 1 [⌜x'⌝, ⌜s⌝, ⌜x''⌝])));
(* *** Goal "2.2" *** *)
val _ = a (lemma_tac ⌜BoolRel r x' y'⌝);
(* *** Goal "2.2.1" *** *)
val _ = a (lemma_tac ⌜BEqRel V (BoolRel r) y y'⌝);
val _ = a (lemma_tac ⌜BEqRel V (BoolRel r) y t⌝
	THEN1 (asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqrel_equiv_lemma)
		THEN (fc_tac [get_spec ⌜Equiv⌝])
		THEN (fc_tac [get_spec ⌜Sym⌝])
		THEN (all_asm_fc_tac[])));
val _ = a (lemma_tac ⌜BEqRel V (BoolRel r) y y'⌝
	THEN1 (asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqrel_equiv_lemma)
		THEN (fc_tac [get_spec ⌜Equiv⌝])
		THEN (fc_tac [get_spec ⌜Trans⌝])
		THEN (list_spec_nth_asm_tac 1 [⌜y⌝, ⌜t⌝, ⌜y'⌝])));
val _ = a (FC_T (MAP_EVERY(asm_tac o (rewrite_rule[]))) [get_spec ⌜BEqRel⌝]);
val _ = a (spec_nth_asm_tac 1 ⌜x'⌝);
(* *** Goal "2.2.2" *** *)
val _ = a (fc_tac [pre_tot_ext_lemma]);
val _ = a (asm_tac (rewrite_rule [asm_rule ⌜TotExtensional V (BoolRel r)⌝] (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] (get_spec ⌜TotExtensional⌝))));
val _ = a (list_spec_nth_asm_tac 1 [⌜x'⌝, ⌜x''⌝]);
(* *** Goal "2.2.2.1" *** *)
val _ = a (spec_nth_asm_tac 1 ⌜y'⌝);
(* *** Goal "2.2.2.2" *** *)
val _ = a (FC_T (MAP_EVERY (asm_tac o (rewrite_rule []))) [get_spec ⌜BEqRel⌝]);
val _ = a (spec_nth_asm_tac 1 ⌜z⌝);
(* *** Goal "2.2.2.3" *** *)
val _ = a (FC_T (MAP_EVERY (asm_tac o (rewrite_rule []))) [get_spec ⌜BEqRel⌝]);
val _ = a (spec_nth_asm_tac 1 ⌜z⌝);
in val totpre_rep_independence_lemma = save_pop_thm "totpre_rep_independence_lemma";
end;

local val _ = set_goal([],⌜∀V r⦁ TotalOver V r ∧ PreExtensional V r ⇒	
	∀s t u v⦁ s ∈ V ∧ t ∈ V ∧ u ∈ V ∧ v ∈ V ∧ BoolEqRel V r s u ∧ BoolEqRel V r t v
	⇒ (BoolRel r s t ⇔ BoolRel r u v)⌝);
val _ = a (REPEAT_N 8 strip_tac);
val _ = a (strip_asm_tac (list_∀_elim [⌜V⌝, ⌜r⌝] totpre_rep_independence_lemma));
val _ = a (list_spec_nth_asm_tac 1 [⌜s⌝, ⌜t⌝]);
val _ = a (POP_ASM_T ante_tac
	THEN rewrite_tac [let_def, get_spec ⌜EquivClass⌝]);
val _ = a (STRIP_T asm_tac THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
val _ = a (lemma_tac ⌜BoolEqRel V r s s ∧ BoolEqRel V r t t⌝
	THEN1 (asm_tac booleqrel_equiv_lemma
		THEN ufc_tac [get_spec ⌜Equiv⌝]
		THEN ufc_tac [get_spec ⌜Refl⌝]
		THEN ALL_ASM_FC_T rewrite_tac []));
val _ = a (LEMMA_T  ⌜(∃ x' y
             ⦁ (x' ∈ V ∧ BoolEqRel V r s x') ∧ (y ∈ V ∧ BoolEqRel V r t y) ∧ BoolRel r x' y)⌝
	(asm_tac o (rewrite_rule [eq_sym_rule (asm_rule
	⌜(∀ x' y⦁ (x' ∈ V ∧ BoolEqRel V r s x') ∧ y ∈ V ∧ BoolEqRel V r t y ⇒ BoolRel r x' y)
             ⇔ (∃ x' y
             ⦁ (x' ∈ V ∧ BoolEqRel V r s x') ∧ (y ∈ V ∧ BoolEqRel V r t y) ∧ BoolRel r x' y)⌝)]))
	THEN1 (∃_tac ⌜s⌝ THEN ∃_tac ⌜t⌝ THEN asm_rewrite_tac[]));
val _ = a (list_spec_nth_asm_tac 1 [⌜u⌝, ⌜v⌝]);
(* *** Goal "2" *** *)
val _ = a (lemma_tac ⌜BoolEqRel V r s s ∧ BoolEqRel V r t t⌝
	THEN1 (asm_tac booleqrel_equiv_lemma
		THEN ufc_tac [get_spec ⌜Equiv⌝]
		THEN ufc_tac [get_spec ⌜Refl⌝]
		THEN ALL_ASM_FC_T rewrite_tac []));
val _ = a (LEMMA_T  ⌜(∃ x' y
             ⦁ (x' ∈ V ∧ BoolEqRel V r s x') ∧ (y ∈ V ∧ BoolEqRel V r t y) ∧ BoolRel r x' y)⌝
	(asm_tac o (rewrite_rule [eq_sym_rule (asm_rule
	⌜(∀ x' y⦁ (x' ∈ V ∧ BoolEqRel V r s x') ∧ y ∈ V ∧ BoolEqRel V r t y ⇒ BoolRel r x' y)
             ⇔ (∃ x' y
             ⦁ (x' ∈ V ∧ BoolEqRel V r s x') ∧ (y ∈ V ∧ BoolEqRel V r t y) ∧ BoolRel r x' y)⌝)]))
	THEN1 (∃_tac ⌜u⌝ THEN ∃_tac ⌜v⌝ THEN asm_rewrite_tac[]));
val _ = a (list_spec_nth_asm_tac 1 [⌜s⌝, ⌜t⌝]);
in val totpre_rep_independence_lemma2 = save_pop_thm "totpre_rep_independence_lemma2";
end;

=IGN
set_flag("subgoal_package_quiet", false);
stop;

set_goal([],⌜∀V r⦁ TotalOver V r ∧ PreExtensional2 V r ⇒ ∀s t⦁ s ∈ V ∧ t ∈ V ⇒
	let u = EquivClass (V, BoolEqRel V r) s
	and v = EquivClass (V, BoolEqRel V r) t
	in	((∀x y⦁ x ∈ u ∧ y ∈ v ⇒ BoolRel r x y) ⇔ (∃x y⦁ x ∈ u ∧ y ∈ v ∧ BoolRel r x y))⌝);
a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜BoolEqRel⌝, get_spec ⌜EquivClass⌝, let_def]
	THEN REPEAT_N 6 strip_tac);
(* *** Goal "1" *** *)
a (strip_tac);
a (∃_tac ⌜s⌝ THEN ∃_tac ⌜t⌝ THEN asm_rewrite_tac[]);
a (asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqrel_equiv_lemma));
a (ufc_tac [get_spec ⌜Equiv⌝]);
a (ufc_tac [get_spec ⌜Refl⌝]);
a (list_spec_nth_asm_tac 6 [⌜s⌝, ⌜t⌝]
	THEN_TRY (all_asm_fc_tac [])
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (REPEAT strip_tac);
a (lemma_tac ⌜BEqRel V (BoolRel r) x' x''⌝);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜BEqRel V (BoolRel r) x' s⌝
	THEN1 (asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqrel_equiv_lemma)
		THEN (fc_tac [get_spec ⌜Equiv⌝])
		THEN (fc_tac [get_spec ⌜Sym⌝])
		THEN (all_asm_fc_tac[])));
a ((asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqrel_equiv_lemma)
		THEN (fc_tac [get_spec ⌜Equiv⌝])
		THEN (fc_tac [get_spec ⌜Trans⌝])
		THEN (list_spec_nth_asm_tac 1 [⌜x'⌝, ⌜s⌝, ⌜x''⌝])));
(* *** Goal "2.2" *** *)
a (lemma_tac ⌜BoolRel r x' y'⌝);
(* *** Goal "2.2.1" *** *)
a (lemma_tac ⌜BEqRel V (BoolRel r) y y'⌝);
a (lemma_tac ⌜BEqRel V (BoolRel r) y t⌝
	THEN1 (asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqrel_equiv_lemma)
		THEN (fc_tac [get_spec ⌜Equiv⌝])
		THEN (fc_tac [get_spec ⌜Sym⌝])
		THEN (all_asm_fc_tac[])));
a (lemma_tac ⌜BEqRel V (BoolRel r) y y'⌝
	THEN1 (asm_tac (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] beqrel_equiv_lemma)
		THEN (fc_tac [get_spec ⌜Equiv⌝])
		THEN (fc_tac [get_spec ⌜Trans⌝])
		THEN (list_spec_nth_asm_tac 1 [⌜y⌝, ⌜t⌝, ⌜y'⌝])));
a (FC_T (MAP_EVERY(asm_tac o (rewrite_rule[]))) [get_spec ⌜BEqRel⌝]);
a (spec_nth_asm_tac 1 ⌜x'⌝);
(* *** Goal "2.2.2" *** *)
a (fc_tac [pre2_tot_ext_lemma]);
a (asm_tac (rewrite_rule [asm_rule ⌜TotExtensional2 V (BoolRel r)⌝] (list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] (get_spec ⌜TotExtensional2⌝))));
a (list_spec_nth_asm_tac 1 [⌜x'⌝, ⌜x''⌝]);
(* *** Goal "2.2.2.1" *** *)
a (spec_nth_asm_tac 1 ⌜y'⌝);
(* *** Goal "2.2.2.2" *** *)
a (FC_T (MAP_EVERY (asm_tac o (rewrite_rule []))) [get_spec ⌜BEqRel⌝]);
a (spec_nth_asm_tac 1 ⌜z⌝);
(* *** Goal "2.2.2.3" *** *)
a (FC_T (MAP_EVERY (asm_tac o (rewrite_rule []))) [get_spec ⌜BEqRel⌝]);
a (spec_nth_asm_tac 1 ⌜z⌝);
(* *** Goal "2.2.2.4" *** *)
a (FC_T (MAP_EVERY (asm_tac o (rewrite_rule []))) [get_spec ⌜BEqRel⌝]);
a (spec_nth_asm_tac 1 ⌜x'⌝);
a (spec_nth_asm_tac 2 ⌜x''⌝);

(* *** Goal "2.2.2.5" *** *)

val totpre2_rep_independence_lemma = save_pop_thm "totpre2_rep_independence_lemma";

local val _ = set_goal([],⌜∀V r⦁ TotalOver V r ∧ PreExtensional2 V r ⇒	
	∀s t u v⦁ s ∈ V ∧ t ∈ V ∧ u ∈ V ∧ v ∈ V ∧ BoolEqRel V r s u ∧ BoolEqRel V r t v
	⇒ (BoolRel r s t ⇔ BoolRel r u v)⌝);
val _ = a (REPEAT_N 8 strip_tac);
val _ = a (strip_asm_tac (list_∀_elim [⌜V⌝, ⌜r⌝] totpre_rep_independence_lemma));
val _ = a (list_spec_nth_asm_tac 1 [⌜s⌝, ⌜t⌝]);
val _ = a (POP_ASM_T ante_tac
	THEN rewrite_tac [let_def, get_spec ⌜EquivClass⌝]);
val _ = a (STRIP_T asm_tac THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
val _ = a (lemma_tac ⌜BoolEqRel V r s s ∧ BoolEqRel V r t t⌝
	THEN1 (asm_tac booleqrel_equiv_lemma
		THEN ufc_tac [get_spec ⌜Equiv⌝]
		THEN ufc_tac [get_spec ⌜Refl⌝]
		THEN ALL_ASM_FC_T rewrite_tac []));
val _ = a (LEMMA_T  ⌜(∃ x' y
             ⦁ (x' ∈ V ∧ BoolEqRel V r s x') ∧ (y ∈ V ∧ BoolEqRel V r t y) ∧ BoolRel r x' y)⌝
	(asm_tac o (rewrite_rule [eq_sym_rule (asm_rule
	⌜(∀ x' y⦁ (x' ∈ V ∧ BoolEqRel V r s x') ∧ y ∈ V ∧ BoolEqRel V r t y ⇒ BoolRel r x' y)
             ⇔ (∃ x' y
             ⦁ (x' ∈ V ∧ BoolEqRel V r s x') ∧ (y ∈ V ∧ BoolEqRel V r t y) ∧ BoolRel r x' y)⌝)]))
	THEN1 (∃_tac ⌜s⌝ THEN ∃_tac ⌜t⌝ THEN asm_rewrite_tac[]));
val _ = a (list_spec_nth_asm_tac 1 [⌜u⌝, ⌜v⌝]);
(* *** Goal "2" *** *)
val _ = a (lemma_tac ⌜BoolEqRel V r s s ∧ BoolEqRel V r t t⌝
	THEN1 (asm_tac booleqrel_equiv_lemma
		THEN ufc_tac [get_spec ⌜Equiv⌝]
		THEN ufc_tac [get_spec ⌜Refl⌝]
		THEN ALL_ASM_FC_T rewrite_tac []));
val _ = a (LEMMA_T  ⌜(∃ x' y
             ⦁ (x' ∈ V ∧ BoolEqRel V r s x') ∧ (y ∈ V ∧ BoolEqRel V r t y) ∧ BoolRel r x' y)⌝
	(asm_tac o (rewrite_rule [eq_sym_rule (asm_rule
	⌜(∀ x' y⦁ (x' ∈ V ∧ BoolEqRel V r s x') ∧ y ∈ V ∧ BoolEqRel V r t y ⇒ BoolRel r x' y)
             ⇔ (∃ x' y
             ⦁ (x' ∈ V ∧ BoolEqRel V r s x') ∧ (y ∈ V ∧ BoolEqRel V r t y) ∧ BoolRel r x' y)⌝)]))
	THEN1 (∃_tac ⌜u⌝ THEN ∃_tac ⌜v⌝ THEN asm_rewrite_tac[]));
val _ = a (list_spec_nth_asm_tac 1 [⌜s⌝, ⌜t⌝]);
in val totpre2_rep_independence_lemma2 = save_pop_thm "totpre2_rep_independence_lemma2";
end;

=SML

local val _ = set_goal([],⌜∀V r⦁ TotalOver V r ⇒	
	∀s t u v⦁ s ∈ V ∧ t ∈ V ∧ u ∈ V ∧ v ∈ V ∧ BoolEqqRel V r s u ∧ BoolEqqRel V r t v
	⇒ (BoolRel r s t ⇔ BoolRel r u v)⌝);
val _ = a (REPEAT_N 8 strip_tac);
val _ = a (strip_asm_tac (list_∀_elim [⌜V⌝, ⌜r⌝] rep_independence_lemma));
val _ = a (list_spec_nth_asm_tac 1 [⌜s⌝, ⌜t⌝]);
val _ = a (POP_ASM_T ante_tac
	THEN rewrite_tac [let_def, get_spec ⌜EquivClass⌝]);
val _ = a (STRIP_T asm_tac THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
val _ = a (lemma_tac ⌜BoolEqqRel V r s s ∧ BoolEqqRel V r t t⌝
	THEN1 (asm_tac booleqqrel_equiv_lemma
		THEN ufc_tac [get_spec ⌜Equiv⌝]
		THEN ufc_tac [get_spec ⌜Refl⌝]
		THEN ALL_ASM_FC_T rewrite_tac []));
val _ = a (LEMMA_T  ⌜(∃ x' y
             ⦁ (x' ∈ V ∧ BoolEqqRel V r s x') ∧ (y ∈ V ∧ BoolEqqRel V r t y) ∧ BoolRel r x' y)⌝
	(asm_tac o (rewrite_rule [eq_sym_rule (asm_rule
	⌜(∀ x' y⦁ (x' ∈ V ∧ BoolEqqRel V r s x') ∧ y ∈ V ∧ BoolEqqRel V r t y ⇒ BoolRel r x' y)
             ⇔ (∃ x' y
             ⦁ (x' ∈ V ∧ BoolEqqRel V r s x') ∧ (y ∈ V ∧ BoolEqqRel V r t y) ∧ BoolRel r x' y)⌝)]))
	THEN1 (∃_tac ⌜s⌝ THEN ∃_tac ⌜t⌝ THEN asm_rewrite_tac[]));
val _ = a (list_spec_nth_asm_tac 1 [⌜u⌝, ⌜v⌝]);
(* *** Goal "2" *** *)
val _ = a (lemma_tac ⌜BoolEqqRel V r s s ∧ BoolEqqRel V r t t⌝
	THEN1 (asm_tac booleqqrel_equiv_lemma
		THEN ufc_tac [get_spec ⌜Equiv⌝]
		THEN ufc_tac [get_spec ⌜Refl⌝]
		THEN ALL_ASM_FC_T rewrite_tac []));
val _ = a (LEMMA_T  ⌜(∃ x' y
             ⦁ (x' ∈ V ∧ BoolEqqRel V r s x') ∧ (y ∈ V ∧ BoolEqqRel V r t y) ∧ BoolRel r x' y)⌝
	(asm_tac o (rewrite_rule [eq_sym_rule (asm_rule
	⌜(∀ x' y⦁ (x' ∈ V ∧ BoolEqqRel V r s x') ∧ y ∈ V ∧ BoolEqqRel V r t y ⇒ BoolRel r x' y)
             ⇔ (∃ x' y
             ⦁ (x' ∈ V ∧ BoolEqqRel V r s x') ∧ (y ∈ V ∧ BoolEqqRel V r t y) ∧ BoolRel r x' y)⌝)]))
	THEN1 (∃_tac ⌜u⌝ THEN ∃_tac ⌜v⌝ THEN asm_rewrite_tac[]));
val _ = a (list_spec_nth_asm_tac 1 [⌜s⌝, ⌜t⌝]);
in val rep_independence_lemma2 = save_pop_thm "rep_independence_lemma2";
end;

set_merge_pcs ["misc2", "'ifos", "'sfp"];

local val _ = set_goal([],⌜∀V r⦁ TotalOver V r ∧ PreExtensional V r ⇒ extensional (MSfromSFF (V,r))⌝);
val _ = a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜extensional⌝, get_spec ⌜MSfromSFF⌝, let_def]
	THEN REPEAT_N 7 strip_tac
	THEN_TRY asm_rewrite_tac[]);
val _ = a (GET_NTH_ASM_T 3 (strip_asm_tac o (rewrite_rule [get_spec ⌜QuotientSet⌝])));
val _ = a (GET_NTH_ASM_T 4 (strip_asm_tac o (rewrite_rule [get_spec ⌜QuotientSet⌝])));
val _ = a (asm_rewrite_tac[]);
val _ = a (lemma_tac ⌜Equiv (V, BEqRel V (BoolRel r))⌝ THEN1 rewrite_tac[beqrel_equiv_lemma]);
val _ = a (FC_T1 (fc_⇔_canon)
	(MAP_EVERY (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜x ∈ V⌝, asm_rule ⌜x' ∈ V⌝]) o (list_∀_elim [⌜x⌝, ⌜x'⌝])))
	[equiv_class_eq_thm]);
val _ = a (rewrite_tac [get_spec ⌜BEqRel⌝]);
val _ = a (strip_tac THEN strip_tac);
val _ = a (lemma_tac ⌜EquivClass (V, BEqRel V (BoolRel r)) z ∈ V / BEqRel V (BoolRel r)⌝
	THEN1 (rewrite_tac [get_spec ⌜QuotientSet⌝]
		THEN ∃_tac ⌜z⌝
		THEN asm_rewrite_tac[]));
val _ = a (SPEC_NTH_ASM_T 8 ⌜EquivClass (V, BEqRel V (BoolRel r)) z⌝ 
	(strip_asm_tac o (rewrite_rule[asm_rule ⌜EquivClass (V, BEqRel V (BoolRel r)) z ∈ V / BEqRel V (BoolRel r)⌝])));
(* *** Goal "1" *** *)
val _ = a (lemma_tac ⌜BoolEqRel V r z x'' ∧ BoolEqRel V r x y⌝
	THEN1 strip_tac);
(* *** Goal "1.1" *** *)
val _ = a (DROP_NTH_ASM_T 6 ante_tac
	THEN rewrite_tac [get_spec ⌜EquivClass⌝]
	THEN strip_tac
	THEN asm_rewrite_tac [get_spec ⌜BoolEqRel⌝]);
(* *** Goal "1.2" *** *)
val _ = a (DROP_NTH_ASM_T 5 ante_tac
	THEN asm_rewrite_tac [get_spec ⌜EquivClass⌝]
	THEN strip_tac
	THEN asm_rewrite_tac [get_spec ⌜BoolEqRel⌝]);
(* *** Goal "1.3" *** *)
val _ = a (LEMMA_T ⌜BoolRel r z x ⇔ BoolRel r x'' y⌝ asm_rewrite_thm_tac);
(* *** Goal "1.3.1" *** *)
val _ = a (strip_asm_tac (list_∀_elim [⌜V⌝, ⌜r⌝] totpre_rep_independence_lemma2));
val _ = a (lemma_tac ⌜x'' ∈ V⌝
	THEN1 (DROP_NTH_ASM_T 9 ante_tac THEN rewrite_tac[get_spec ⌜EquivClass⌝] THEN contr_tac));
val _ = a (lemma_tac ⌜y ∈ V⌝
	THEN1 (DROP_NTH_ASM_T 9 ante_tac THEN asm_rewrite_tac[get_spec ⌜EquivClass⌝] THEN contr_tac));
val _ = a (list_spec_nth_asm_tac 3 [⌜z⌝, ⌜x⌝, ⌜x''⌝, ⌜y⌝]);
val _ = a (contr_tac);
(* *** Goal "1.3.2" *** *)
val _ = a (LEMMA_T ⌜BoolRel r z x' ⇔ BoolRel r x''' y'⌝ asm_rewrite_thm_tac);
val _ = a (lemma_tac ⌜x''' ∈ V⌝
	THEN1 (DROP_NTH_ASM_T 5 ante_tac THEN rewrite_tac[get_spec ⌜EquivClass⌝] THEN contr_tac));
val _ = a (lemma_tac ⌜y' ∈ V⌝
	THEN1 (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[get_spec ⌜EquivClass⌝] THEN contr_tac));
val _ = a (strip_asm_tac (list_∀_elim [⌜V⌝, ⌜r⌝] totpre_rep_independence_lemma2));
val _ = a (lemma_tac ⌜BoolEqRel V r x' y'⌝
	THEN1 (DROP_NTH_ASM_T 7 ante_tac
		THEN asm_rewrite_tac [get_spec ⌜EquivClass⌝, get_spec ⌜BoolEqRel⌝]));
val _ = a (lemma_tac ⌜BoolEqRel V r z x'''⌝
	THEN1 (DROP_NTH_ASM_T 9 ante_tac
		THEN asm_rewrite_tac [get_spec ⌜EquivClass⌝, get_spec ⌜BoolEqRel⌝]));
val _ = a (list_spec_nth_asm_tac 3 [⌜z⌝, ⌜x'⌝, ⌜x'''⌝, ⌜y'⌝]);
val _ = a (contr_tac);
(* *** Goal "2" *** *)
val _ = a (all_asm_fc_tac[]);
(* *** Goal "3" *** *)
val _ = a (all_asm_fc_tac[]);
(* *** Goal "4" *** *)
val _ = a (lemma_tac ⌜z ∈ EquivClass (V, BEqRel V (BoolRel r)) z⌝
	THEN1 (rewrite_tac [get_spec ⌜EquivClass⌝, get_spec ⌜BEqRel⌝] THEN strip_tac));
val _ = a (lemma_tac ⌜x ∈ s⌝
	THEN1 (asm_rewrite_tac[get_spec ⌜EquivClass⌝]
		THEN fc_tac [get_spec ⌜Equiv⌝]
		THEN fc_tac [get_spec ⌜Refl⌝]
		THEN ALL_ASM_FC_T rewrite_tac []));
val _ = a (lemma_tac ⌜x' ∈ t⌝
	THEN1 (asm_rewrite_tac[get_spec ⌜EquivClass⌝]
		THEN fc_tac [get_spec ⌜Equiv⌝]
		THEN fc_tac [get_spec ⌜Refl⌝]
		THEN ALL_ASM_FC_T rewrite_tac []));
val _ = a (ALL_ASM_FC_T rewrite_tac []);
in val preext_ext_lemma = save_pop_thm "preext_ext_lemma";
end;

=IGN
set_flag("subgoal_package_quiet", false);
stop;

set_goal([],⌜∀V r⦁ TotalOver V r ∧ PreExtensional2 V r ⇒ extensional (MSfromSFF (V,r))⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜extensional⌝, get_spec ⌜MSfromSFF⌝, let_def]
	THEN REPEAT_N 7 strip_tac
	THEN_TRY asm_rewrite_tac[]);
a (GET_NTH_ASM_T 3 (strip_asm_tac o (rewrite_rule [get_spec ⌜QuotientSet⌝])));
a (GET_NTH_ASM_T 4 (strip_asm_tac o (rewrite_rule [get_spec ⌜QuotientSet⌝])));
a (asm_rewrite_tac[]);
a (lemma_tac ⌜Equiv (V, BEqRel V (BoolRel r))⌝ THEN1 rewrite_tac[beqrel_equiv_lemma]);
a (FC_T1 (fc_⇔_canon)
	(MAP_EVERY (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜x ∈ V⌝, asm_rule ⌜x' ∈ V⌝]) o (list_∀_elim [⌜x⌝, ⌜x'⌝])))
	[equiv_class_eq_thm]);
a (rewrite_tac [get_spec ⌜BEqRel⌝]);
a (strip_tac THEN strip_tac);
a (lemma_tac ⌜EquivClass (V, BEqRel V (BoolRel r)) z ∈ V / BEqRel V (BoolRel r)⌝
	THEN1 (rewrite_tac [get_spec ⌜QuotientSet⌝]
		THEN ∃_tac ⌜z⌝
		THEN asm_rewrite_tac[]));
a (SPEC_NTH_ASM_T 8 ⌜EquivClass (V, BEqRel V (BoolRel r)) z⌝ 
	(strip_asm_tac o (rewrite_rule[asm_rule ⌜EquivClass (V, BEqRel V (BoolRel r)) z ∈ V / BEqRel V (BoolRel r)⌝])));
(* *** Goal "1" *** *)
a (lemma_tac ⌜BoolEqRel V r z x'' ∧ BoolEqRel V r x y⌝
	THEN1 strip_tac);
(* *** Goal "1.1" *** *)
a (DROP_NTH_ASM_T 6 ante_tac
	THEN rewrite_tac [get_spec ⌜EquivClass⌝]
	THEN strip_tac
	THEN asm_rewrite_tac [get_spec ⌜BoolEqRel⌝]);
(* *** Goal "1.2" *** *)
a (DROP_NTH_ASM_T 5 ante_tac
	THEN asm_rewrite_tac [get_spec ⌜EquivClass⌝]
	THEN strip_tac
	THEN asm_rewrite_tac [get_spec ⌜BoolEqRel⌝]);
(* *** Goal "1.3" *** *)
a (LEMMA_T ⌜BoolRel r z x ⇔ BoolRel r x'' y⌝ asm_rewrite_thm_tac);
(* *** Goal "1.3.1" *** *)

a (strip_asm_tac (list_∀_elim [⌜V⌝, ⌜r⌝] totpre_rep_independence_lemma2));
a (lemma_tac ⌜x'' ∈ V⌝
	THEN1 (DROP_NTH_ASM_T 9 ante_tac THEN rewrite_tac[get_spec ⌜EquivClass⌝] THEN contr_tac));
a (lemma_tac ⌜y ∈ V⌝
	THEN1 (DROP_NTH_ASM_T 9 ante_tac THEN asm_rewrite_tac[get_spec ⌜EquivClass⌝] THEN contr_tac));
val _ = a (list_spec_nth_asm_tac 3 [⌜z⌝, ⌜x⌝, ⌜x''⌝, ⌜y⌝]);
val _ = a (contr_tac);
(* *** Goal "1.3.2" *** *)
val _ = a (LEMMA_T ⌜BoolRel r z x' ⇔ BoolRel r x''' y'⌝ asm_rewrite_thm_tac);
val _ = a (lemma_tac ⌜x''' ∈ V⌝
	THEN1 (DROP_NTH_ASM_T 5 ante_tac THEN rewrite_tac[get_spec ⌜EquivClass⌝] THEN contr_tac));
val _ = a (lemma_tac ⌜y' ∈ V⌝
	THEN1 (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[get_spec ⌜EquivClass⌝] THEN contr_tac));
val _ = a (strip_asm_tac (list_∀_elim [⌜V⌝, ⌜r⌝] totpre_rep_independence_lemma2));
val _ = a (lemma_tac ⌜BoolEqRel V r x' y'⌝
	THEN1 (DROP_NTH_ASM_T 7 ante_tac
		THEN asm_rewrite_tac [get_spec ⌜EquivClass⌝, get_spec ⌜BoolEqRel⌝]));
val _ = a (lemma_tac ⌜BoolEqRel V r z x'''⌝
	THEN1 (DROP_NTH_ASM_T 9 ante_tac
		THEN asm_rewrite_tac [get_spec ⌜EquivClass⌝, get_spec ⌜BoolEqRel⌝]));
val _ = a (list_spec_nth_asm_tac 3 [⌜z⌝, ⌜x'⌝, ⌜x'''⌝, ⌜y'⌝]);
val _ = a (contr_tac);
(* *** Goal "2" *** *)
val _ = a (all_asm_fc_tac[]);
(* *** Goal "3" *** *)
val _ = a (all_asm_fc_tac[]);
(* *** Goal "4" *** *)
val _ = a (lemma_tac ⌜z ∈ EquivClass (V, BEqRel V (BoolRel r)) z⌝
	THEN1 (rewrite_tac [get_spec ⌜EquivClass⌝, get_spec ⌜BEqRel⌝] THEN strip_tac));
val _ = a (lemma_tac ⌜x ∈ s⌝
	THEN1 (asm_rewrite_tac[get_spec ⌜EquivClass⌝]
		THEN fc_tac [get_spec ⌜Equiv⌝]
		THEN fc_tac [get_spec ⌜Refl⌝]
		THEN ALL_ASM_FC_T rewrite_tac []));
val _ = a (lemma_tac ⌜x' ∈ t⌝
	THEN1 (asm_rewrite_tac[get_spec ⌜EquivClass⌝]
		THEN fc_tac [get_spec ⌜Equiv⌝]
		THEN fc_tac [get_spec ⌜Refl⌝]
		THEN ALL_ASM_FC_T rewrite_tac []));
val _ = a (ALL_ASM_FC_T rewrite_tac []);
in val preext2_ext_lemma = save_pop_thm "preext2_ext_lemma";
end;

=SML

local val _ = set_goal([], ⌜∀V r⦁ TotalOver V r ∧ PreExtensional V r ⇒
	∀x y⦁ x ∈ V ∧ y ∈ V ⇒ (BEqRel V (BoolRel r) x y ⇔ BEqqRel V (BoolRel r) x y)⌝);
val _ = a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜BEqRel⌝, get_spec ⌜BEqqRel⌝, let_def]
	THEN REPEAT_N 4 strip_tac
	THEN_TRY asm_rewrite_tac[ext_thm]
	THEN REPEAT_N 5 strip_tac);
(* *** Goal "1" *** *)
val _ = a (LEMMA_T ⌜BoolRel r z x ⇔ BoolRel r z y⌝ asm_tac
	THEN1 ASM_FC_T1 fc_⇔_canon rewrite_tac []
	THEN asm_rewrite_tac[]);
val _ = a (fc_tac [pre_tot_ext_lemma]);
val _ = a (asm_tac (rewrite_rule [asm_rule ⌜TotExtensional V (BoolRel r)⌝]
	(list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] (get_spec ⌜TotExtensional⌝))));
val _ = a (list_spec_nth_asm_tac 1 [⌜x⌝, ⌜y⌝]);
(* *** Goal "1.1" *** *)
val _ = a (SPEC_NTH_ASM_T 1 ⌜z⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
(* *** Goal "1.2" *** *)
val _ = a (asm_fc_tac[]);
(* *** Goal "1.3" *** *)
val _ = a (spec_nth_asm_tac 8 ⌜z'⌝);
(* *** Goal "2" *** *)
val _ = a (SPEC_NTH_ASM_T 2 ⌜z⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
in val eq_eq_eqq_lemma = save_pop_thm "eq_eq_eqq_lemma";
end;

=IGN
set_flag ("subgoal_package_quiet", false);
stop;

set_goal([], ⌜∀V r⦁ TotalOver V r ∧ PreExtensional2 V r ⇒
	∀x y⦁ x ∈ V ∧ y ∈ V ⇒ (BEqRel V (BoolRel r) x y ⇔ BEqqRel V (BoolRel r) x y)⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜BEqRel⌝, get_spec ⌜BEqqRel⌝, let_def]
	THEN REPEAT_N 4 strip_tac
	THEN_TRY asm_rewrite_tac[ext_thm]
	THEN REPEAT_N 5 strip_tac);
(* *** Goal "1" *** *)
a (LEMMA_T ⌜BoolRel r z x ⇔ BoolRel r z y⌝ asm_tac
	THEN1 ASM_FC_T1 fc_⇔_canon rewrite_tac []
	THEN asm_rewrite_tac[]);
a (fc_tac [pre2_tot_ext_lemma]);
a (asm_tac (rewrite_rule [asm_rule ⌜TotExtensional2 V (BoolRel r)⌝]
	(list_∀_elim [⌜V⌝, ⌜BoolRel r⌝] (get_spec ⌜TotExtensional2⌝))));
a (list_spec_nth_asm_tac 1 [⌜x⌝, ⌜y⌝]);
(* *** Goal "1.1" *** *)
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
(* *** Goal "1.2" *** *)
a (asm_fc_tac[]);
(* *** Goal "1.3" *** *)
a (spec_nth_asm_tac 8 ⌜z'⌝);
(* *** Goal "2" *** *)
val _ = a (SPEC_NTH_ASM_T 2 ⌜z⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
in val eq_eq_eqq_lemma2 = save_pop_thm "eq_eq_eqq_lemma2";

=SML
local val _ = set_goal([], ⌜∀V r⦁ TotalOver V r ∧ PreExtensional V r ⇒ MSfromSFF (V,r) = MSfromSFF2 (V,r)⌝);
val _ = a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜MSfromSFF⌝, get_spec ⌜MSfromSFF2⌝, let_def, get_spec ⌜QuotientSet⌝,
			get_spec ⌜EquivClass⌝, sets_ext_clauses]
	THEN strip_tac THEN strip_tac
	THEN_TRY asm_rewrite_tac[]);
val _ = a (strip_asm_tac (list_∀_elim [⌜V⌝, ⌜r⌝] eq_eq_eqq_lemma));
val _ = a (REPEAT strip_tac);
(* *** Goal "1" *** *)
val _ = a (∃_tac ⌜x'⌝ THEN asm_rewrite_tac[]);
val _ = a (REPEAT strip_tac);
(* *** Goal "1.1" *** *)
val _ = a (list_spec_nth_asm_tac 5 [⌜x'⌝, ⌜x''⌝]);
(* *** Goal "1.2" *** *)
val _ = a (list_spec_nth_asm_tac 5 [⌜x'⌝, ⌜x''⌝]);
(* *** Goal "2" *** *)
val _ = a (∃_tac ⌜x'⌝ THEN asm_rewrite_tac[]);
val _ = a (REPEAT strip_tac);
(* *** Goal "1.1" *** *)
val _ = a (list_spec_nth_asm_tac 5 [⌜x'⌝, ⌜x''⌝]);
(* *** Goal "1.2" *** *)
val _ = a (list_spec_nth_asm_tac 5 [⌜x'⌝, ⌜x''⌝]);
in val msfromsff_eq_lemma = save_pop_thm "msfromsff_eq_lemma";
end;

=IGN
set_flag("subgoal_package_quiet", false);
stop;

set_goal([], ⌜∀V r⦁ TotalOver V r ∧ PreExtensional2 V r ⇒ MSfromSFF (V,r) = MSfromSFF2 (V,r)⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜MSfromSFF⌝, get_spec ⌜MSfromSFF2⌝, let_def, get_spec ⌜QuotientSet⌝,
			get_spec ⌜EquivClass⌝, sets_ext_clauses]
	THEN strip_tac THEN strip_tac
	THEN_TRY asm_rewrite_tac[]);

a (strip_asm_tac (list_∀_elim [⌜V⌝, ⌜r⌝] eq_eq_eqq_lemma));
val _ = a (REPEAT strip_tac);
(* *** Goal "1" *** *)
val _ = a (∃_tac ⌜x'⌝ THEN asm_rewrite_tac[]);
val _ = a (REPEAT strip_tac);
(* *** Goal "1.1" *** *)
val _ = a (list_spec_nth_asm_tac 5 [⌜x'⌝, ⌜x''⌝]);
(* *** Goal "1.2" *** *)
val _ = a (list_spec_nth_asm_tac 5 [⌜x'⌝, ⌜x''⌝]);
(* *** Goal "2" *** *)
val _ = a (∃_tac ⌜x'⌝ THEN asm_rewrite_tac[]);
val _ = a (REPEAT strip_tac);
(* *** Goal "1.1" *** *)
val _ = a (list_spec_nth_asm_tac 5 [⌜x'⌝, ⌜x''⌝]);
(* *** Goal "1.2" *** *)
val _ = a (list_spec_nth_asm_tac 5 [⌜x'⌝, ⌜x''⌝]);
in val msfromsff_eq_lemma = save_pop_thm "msfromsff_eq_lemma";
end;

=SML
local val _ = set_goal([],⌜∀V r⦁ TotalOver V r ∧ PreExtensional V r ⇒ extensional (MSfromSFF2 (V,r))⌝);
val _ = a (REPEAT strip_tac
	THEN all_fc_tac [msfromsff_eq_lemma, preext_ext_lemma]
	THEN POP_ASM_T ante_tac
	THEN asm_rewrite_tac []);
in val preext_ext_lemma2 = save_pop_thm "preext_ext_lemma2";
end;
=TEX
}%ignore

\subsection{Properties of the Semantic Functor}

I hope to prove that least fixed points of the semantic functor are always pre-extensional.
If they are also total the resulting interpretation will be extensional.
I'm also interested in the dual of this result, for greatest fixed points.

A semantic functor is extensional over some domain if any two sets which have the same extension and the same essence over that domain  in the input relation have the same essence in the result of applying the functor. 

ⓈHOLCONST
│ ⦏ExtSem⦎ : GS SET → (GS SET → (GS, FTV)BR → (GS, FTV)BR) → BOOL
├───────────
│ ∀V f⦁ ExtSem V f ⇔ ∀r⦁ ∀x y⦁ x ∈ V ∧ y ∈ V
│	∧ SameExt V r x y ∧ SameEss V r x y
│	⇒ SameEss V (f V r) x y 
■

=GFT
⦏extsem_sf_thm⦎ =
   ⊢ ∀ V⦁ V ⊆ SetReps ⇒ ExtSem V Sf
=TEX

\ignore{
=SML
set_goal([], ⌜∀V⦁ V ⊆ SetReps ⇒ ExtSem V Sf⌝);
val _ = a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜ExtSem⌝, get_spec ⌜Sf⌝]
	THEN REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜SameEss⌝]
	THEN REPEAT strip_tac);
val _ = a (asm_tac (rewrite_rule [get_spec ⌜Increasing⌝] evalform_increasing_thm2));
val _ = a (lemma_tac ⌜V ⊆ Syntax⌝
	THEN1 (DROP_NTH_ASM_T 7 ante_tac
		THEN PC_T1 "hol1" prove_tac [get_spec ⌜SetReps⌝]));
val _ = a (lemma_tac ⌜z ∈ Syntax⌝
	THEN1 (DROP_NTH_ASM_T 3 ante_tac THEN POP_ASM_T ante_tac
		THEN PC_T1 "hol1" prove_tac [get_spec ⌜SetReps⌝]));
val _ = a (list_spec_nth_asm_tac 3 [⌜(V, r)⌝, ⌜z⌝]);
val _ = a (lemma_tac ⌜ExsVaO (V2IxSet V, V, r) (Param_∅ x) (Param_∅ y)⌝
	THEN1 (rewrite_tac ([] @ (map get_spec [⌜ExsVaO⌝, ⌜IxO2⌝, ⌜ExsSRO⌝, ⌜V2IxSet⌝, ⌜ConjOrder⌝, ⌜IxO⌝,
		⌜ExtSRO⌝, ⌜EssSRO⌝, ⌜Pw⌝, ⌜OptO⌝]))));
val _ = a (asm_rewrite_tac []);
val _ = a (∀_tac);
val _ = a (cases_tac ⌜x' = ∅⋎g⌝ THEN asm_rewrite_tac[]);
val _ = a (REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
val _ = a (GET_NTH_ASM_T 9 (strip_asm_tac o (rewrite_rule [get_spec ⌜SameExt⌝])));
val _ = a (GET_NTH_ASM_T 9 (strip_asm_tac o (rewrite_rule [get_spec ⌜SameEss⌝])));
val _ = a (spec_nth_asm_tac 2 ⌜z'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
val _ = a (GET_NTH_ASM_T 9 (strip_asm_tac o (rewrite_rule [get_spec ⌜SameExt⌝])));
val _ = a (GET_NTH_ASM_T 9 (strip_asm_tac o (rewrite_rule [get_spec ⌜SameEss⌝])));
val _ = a (spec_nth_asm_tac 1 ⌜z'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
val _ = a (all_asm_fc_tac[]);
val _ = a (lemma_tac ⌜ExsVaO (V2IxSet V, V, r) (Param_∅ y) (Param_∅ x)⌝
	THEN1 (rewrite_tac ([] @ (map get_spec [⌜ExsVaO⌝, ⌜IxO2⌝, ⌜ExsSRO⌝, ⌜V2IxSet⌝, ⌜ConjOrder⌝, ⌜IxO⌝,
		⌜ExtSRO⌝, ⌜EssSRO⌝, ⌜Pw⌝, ⌜OptO⌝]))));
(* *** Goal "2.1" *** *)
val _ = a (asm_rewrite_tac []);
val _ = a (∀_tac);
val _ = a (cases_tac ⌜x' = ∅⋎g⌝ THEN asm_rewrite_tac[]);
val _ = a (REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.1.1" *** *)
val _ = a (GET_NTH_ASM_T 11 (strip_asm_tac o (rewrite_rule [get_spec ⌜SameExt⌝])));
val _ = a (GET_NTH_ASM_T 11 (strip_asm_tac o (rewrite_rule [get_spec ⌜SameEss⌝])));
val _ = a (spec_nth_asm_tac 2 ⌜z'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
val _ = a (GET_NTH_ASM_T 11 (strip_asm_tac o (rewrite_rule [get_spec ⌜SameExt⌝])));
val _ = a (GET_NTH_ASM_T 11 (strip_asm_tac o (rewrite_rule [get_spec ⌜SameEss⌝])));
val _ = a (spec_nth_asm_tac 1 ⌜z'⌝ THEN asm_rewrite_tac[]);
val _ = a (all_asm_fc_tac []);
val _ = a (all_asm_fc_tac [≤⋎t⋎4_antisym_thm]);
val extsem_sf_thm = save_pop_thm "extsem_sf_thm";
=TEX
}%ignore

{\it ExtSem} turns out to be too weak.
The following works with compatibility of extension and essence rather than identity.

ⓈHOLCONST
│ ⦏CompExtSem⦎ : GS SET → (GS SET → (GS, FTV)BR → (GS, FTV)BR) → BOOL
├───────────
│ ∀V f⦁ CompExtSem V f ⇔ ∀r⦁ ¬ OverDefined V r ⇒
│	∀x y⦁ x ∈ V ∧ y ∈ V ∧ Compatible V r x y
│	⇒ CompEss V (f V r) x y 
■

That too is not enough.
This one might do the trick.

ⓈHOLCONST
│ ⦏CompExtSem2⦎ : GS SET → (GS SET → (GS, FTV)BR → (GS, FTV)BR) → BOOL
├───────────
│ ∀V f⦁ CompExtSem2 V f ⇔ ∀r⦁ ¬ OverDefined V r ⇒
│	∀x y⦁ x ∈ V ∧ y ∈ V ∧ Compatible V r x y
│	⇒ CompEss V (f V r) x y ∧ {r x x; r x y; r y x; r y y} ∈ CompFTV
■

To prove that the semantic functor has this property is a bit harder than the proof for {\it ExtSem}.

\subsubsection{Extending Partial Membership Structures}

The idea of compatibility is that from what we know two elements could turn out to have the same extension or essence when all undefined values are refined to definite values by repeated application of the semantic functor.
Hence, if two elements are compatible (and not overdefined) then there is some other possible extension or essence which refines both (and is not overdefined).
If we apply the semantic functor to something having that extension or essence then, because the semantic functor is monotonic and the computation of essence is extensional (depends on the extension and intension of the elements but does not refer to their syntactic structure), we will get something whose essence is an upper bound of the essences of the two compatible elements.
Hence the two elements have compatible essences after the application of the semantic functor.

There is an awkwardness in this plan because the semantic functor applies to a partial membership relationship, not to arbitrary essences and extensions.
It may be that it will suffice to talk hypothetically. ``if there was an element which was a not overdefined upper bound for the an arbitrary pair of compatible element then its extension after application of the semantic functor would be an upper bound for the extensions of the two elements in the image of the semantic functor, which would suffice to show that they are compatible''.

To carry through this plan we need a lemma to the effect that compatibility of not overdefined elements is equivalent to the existence of a not overdefined upper bound for the elements.
We do this in two parts, showing the existence separately of not overdefined upper bounds on extensions and essences.
It looks like there will be {\it least} upper bounds, but I don't think that I need to prove the stronger result.

=GFT
⦏compext_lemma1⦎ =
   ⊢ ∀ V
     ⦁ V ⊆ SetReps
         ⇒ (∀ r x y
             ⦁ x ∈ V ∧ y ∈ V
                 ⇒ (CompExt V r x y
                   ⇔ (∃ xt
                   ⦁ ¬ OverDefinedL V xt
                       ∧ IsUb
                         (PwS V $≤⋎t⋎4)
                         {Extension r x; Extension r y}
                         xt)))
=TEX

=GFT
⦏compext_lemma1b⦎ =
   ⊢ ∀ V
     ⦁ V ⊆ Syntax
         ⇒ (∀ r x y
         ⦁ x ∈ V ∧ y ∈ V
             ⇒ (CompExt V r x y
               ⇔ (∃ xt
               ⦁ ¬ OverDefinedL V xt
                   ∧ IsUb (PwS V $≤⋎t⋎4) {Extension r x; Extension r y} xt)))
=TEX


\ignore{
=SML
set_goal([], ⌜∀V⦁ V ⊆ SetReps ⇒ ∀r x y⦁ x ∈ V ∧ y ∈ V ⇒
	(CompExt V r x y
	⇔ ∃ xt⦁ ¬ OverDefinedL V xt
	   ∧ IsUb (PwS V $≤⋎t⋎4)
		{Extension r x; Extension r y}
		xt)⌝);
a (REPEAT_N 6 strip_tac
	THEN rewrite_tac ([∈_in_clauses]@(map get_spec [⌜CompExt⌝, ⌜OverDefinedL⌝, ⌜Extension⌝, ⌜IsUb⌝, ⌜PwS⌝]))
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜λv⦁ Lub $≤⋎t⋎4 {r v x; r v y}⌝ THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (swap_nth_asm_concl_tac 1);
a (spec_nth_asm_tac 2 ⌜y'⌝);
(* *** Goal "1.2" *** *)
a (spec_nth_asm_tac 3 ⌜x''⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜CompFTV⌝, sets_ext_clauses, ∈_in_clauses]
	THEN strip_tac THEN asm_rewrite_tac[]
	THEN (accept_tac (rewrite_rule [∈_in_clauses] (list_∀_elim [⌜r x'' x⌝, ⌜{r x'' x; r x'' y}⌝]
	(rewrite_rule [] (∀_elim ⌜$≤⋎t⋎4⌝ less_lub_lemma))))));
(* *** Goal "1.3" *** *)
a (spec_nth_asm_tac 3 ⌜x''⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜CompFTV⌝, sets_ext_clauses, ∈_in_clauses]
	THEN strip_tac THEN asm_rewrite_tac[]
	THEN (accept_tac (rewrite_rule [∈_in_clauses] (list_∀_elim [⌜r x'' y⌝, ⌜{r x'' x; r x'' y}⌝]
	(rewrite_rule [] (∀_elim ⌜$≤⋎t⋎4⌝ less_lub_lemma))))));
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜λv⦁ r v x⌝);
(* *** Goal "2.1" *** *)
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule[get_spec ⌜CombC⌝])));
(* *** Goal "2.2" *** *)
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (strip_asm_tac o (rewrite_rule [])));
a (spec_nth_asm_tac 4 ⌜λv⦁ r v y⌝);
(* *** Goal "2.2.1" *** *)
a (DROP_NTH_ASM_T 1 (strip_asm_tac o (rewrite_rule[get_spec ⌜CombC⌝])));
(* *** Goal "2.2.2" *** *)
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (strip_asm_tac o (rewrite_rule [])));
a (spec_nth_asm_tac 7 ⌜z⌝);
a (rewrite_tac[get_spec ⌜CompFTV⌝]);
a (POP_ASM_T ante_tac);
a (DROP_NTH_ASM_T 1 ante_tac THEN DROP_NTH_ASM_T 2 ante_tac);
a (strip_asm_tac (∀_elim ⌜xt z⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[∈_in_clauses]
	THEN strip_asm_tac (∀_elim ⌜r z x⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[∈_in_clauses]
	THEN strip_asm_tac (∀_elim ⌜r z y⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[∈_in_clauses]);
(* *** Goal "2.2.2.1" *** *)
a (rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜{fTrue; fB} = {fB; fTrue}⌝]);
(* *** Goal "2.2.2.2" *** *)
a (rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜{fFalse; fB} = {fB; fFalse}⌝]);
val compext_lemma1 = save_pop_thm "compext_lemma1";

set_goal([], ⌜∀V⦁ V ⊆ Syntax ⇒ ∀r x y⦁ x ∈ V ∧ y ∈ V ⇒
	(CompExt V r x y
	⇔ ∃ xt⦁ ¬ OverDefinedL V xt
	   ∧ IsUb (PwS V $≤⋎t⋎4)
		{Extension r x; Extension r y}
		xt)⌝);
a (REPEAT_N 6 strip_tac
	THEN rewrite_tac ([∈_in_clauses]@(map get_spec [⌜CompExt⌝, ⌜OverDefinedL⌝, ⌜Extension⌝, ⌜IsUb⌝, ⌜PwS⌝]))
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜λv⦁ Lub $≤⋎t⋎4 {r v x; r v y}⌝ THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (swap_nth_asm_concl_tac 1);
a (spec_nth_asm_tac 2 ⌜y'⌝);
(* *** Goal "1.2" *** *)
a (spec_nth_asm_tac 3 ⌜x''⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜CompFTV⌝, sets_ext_clauses, ∈_in_clauses]
	THEN strip_tac THEN asm_rewrite_tac[]
	THEN (accept_tac (rewrite_rule [∈_in_clauses] (list_∀_elim [⌜r x'' x⌝, ⌜{r x'' x; r x'' y}⌝]
	(rewrite_rule [] (∀_elim ⌜$≤⋎t⋎4⌝ less_lub_lemma))))));
(* *** Goal "1.3" *** *)
a (spec_nth_asm_tac 3 ⌜x''⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜CompFTV⌝, sets_ext_clauses, ∈_in_clauses]
	THEN strip_tac THEN asm_rewrite_tac[]
	THEN (accept_tac (rewrite_rule [∈_in_clauses] (list_∀_elim [⌜r x'' y⌝, ⌜{r x'' x; r x'' y}⌝]
	(rewrite_rule [] (∀_elim ⌜$≤⋎t⋎4⌝ less_lub_lemma))))));
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜λv⦁ r v x⌝);
(* *** Goal "2.1" *** *)
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule[get_spec ⌜CombC⌝])));
(* *** Goal "2.2" *** *)
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (strip_asm_tac o (rewrite_rule [])));
a (spec_nth_asm_tac 4 ⌜λv⦁ r v y⌝);
(* *** Goal "2.2.1" *** *)
a (DROP_NTH_ASM_T 1 (strip_asm_tac o (rewrite_rule[get_spec ⌜CombC⌝])));
(* *** Goal "2.2.2" *** *)
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (strip_asm_tac o (rewrite_rule [])));
a (spec_nth_asm_tac 7 ⌜z⌝);
a (rewrite_tac[get_spec ⌜CompFTV⌝]);
a (POP_ASM_T ante_tac);
a (DROP_NTH_ASM_T 1 ante_tac THEN DROP_NTH_ASM_T 2 ante_tac);
a (strip_asm_tac (∀_elim ⌜xt z⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[∈_in_clauses]
	THEN strip_asm_tac (∀_elim ⌜r z x⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[∈_in_clauses]
	THEN strip_asm_tac (∀_elim ⌜r z y⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[∈_in_clauses]);
(* *** Goal "2.2.2.1" *** *)
a (rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜{fTrue; fB} = {fB; fTrue}⌝]);
(* *** Goal "2.2.2.2" *** *)
a (rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜{fFalse; fB} = {fB; fFalse}⌝]);
val compext_lemma1b = save_pop_thm "compext_lemma1b";
=TEX
}%ignore

=GFT
⦏compext_lemma2⦎ =
   ⊢ ∀ V
     ⦁ V ⊆ SetReps
         ⇒ (∀ $∈⋎v x y
         ⦁ x ∈ V ∧ y ∈ V
             ⇒ CompExt V $∈⋎v x y
               = (∃ xt
               ⦁ ¬ OverDefinedL V xt
                   ∧ IsLub
                     (PwS V $≤⋎t⋎4)
                     {Extension $∈⋎v x; Extension $∈⋎v y}
                     xt))
=TEX
=GFT
⦏compext_lemma2b⦎ =
   ⊢ ∀ V
     ⦁ V ⊆ Syntax
         ⇒ (∀ $∈⋎v x y
         ⦁ x ∈ V ∧ y ∈ V
             ⇒ (CompExt V $∈⋎v x y
               ⇔ (∃ xt
               ⦁ ¬ OverDefinedL V xt
                   ∧ IsLub
                     (PwS V $≤⋎t⋎4)
                     {Extension $∈⋎v x; Extension $∈⋎v y}
                     xt)))
=TEX

\ignore{
=SML
set_goal([], ⌜∀V⦁ V ⊆ SetReps ⇒ ∀$∈⋎v x y⦁ x ∈ V ∧ y ∈ V ⇒ (CompExt V $∈⋎v x y
	⇔ ∃ xt⦁ ¬ OverDefinedL V xt
	   ∧ IsLub (PwS V $≤⋎t⋎4)
		{Extension $∈⋎v x; Extension $∈⋎v y}
		xt)⌝);
a (REPEAT strip_tac THEN all_fc_tac [compext_lemma1]);
(* *** Goal "1" *** *)
a (asm_tac (rewrite_rule [get_spec ⌜LubsExist⌝] (list_∀_elim [⌜V⌝, ⌜$≤⋎t⋎4⌝] pws_lubs_exist_thm)));
a (spec_nth_asm_tac 1 ⌜{Extension $∈⋎v x; Extension $∈⋎v y}⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac []);
a (fc_tac [get_spec ⌜IsLub⌝, OverDefinedL_≤⋎t⋎4_lemma]);
a (asm_fc_tac[]);
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (strip_asm_tac (list_∀_elim [⌜V⌝] compext_lemma1));
a (LIST_SPEC_NTH_ASM_T 1 [⌜$∈⋎v⌝, ⌜x⌝, ⌜y⌝]
	(rewrite_thm_tac o (rewrite_rule [asm_rule ⌜x ∈ V⌝, asm_rule ⌜y ∈ V⌝])));
a (fc_tac [get_spec ⌜IsLub⌝]);
a (∃_tac ⌜xt⌝ THEN asm_rewrite_tac[]);
val compext_lemma2 = save_pop_thm "compext_lemma2";

set_goal([], ⌜∀V⦁ V ⊆ Syntax ⇒ ∀$∈⋎v x y⦁ x ∈ V ∧ y ∈ V ⇒ (CompExt V $∈⋎v x y
	⇔ ∃ xt⦁ ¬ OverDefinedL V xt
	   ∧ IsLub (PwS V $≤⋎t⋎4)
		{Extension $∈⋎v x; Extension $∈⋎v y}
		xt)⌝);
a (REPEAT strip_tac THEN all_fc_tac [compext_lemma1b]);
(* *** Goal "1" *** *)
a (asm_tac (rewrite_rule [get_spec ⌜LubsExist⌝] (list_∀_elim [⌜V⌝, ⌜$≤⋎t⋎4⌝] pws_lubs_exist_thm)));
a (spec_nth_asm_tac 1 ⌜{Extension $∈⋎v x; Extension $∈⋎v y}⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac []);
a (fc_tac [get_spec ⌜IsLub⌝, OverDefinedL_≤⋎t⋎4_lemma]);
a (asm_fc_tac[]);
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (strip_asm_tac (list_∀_elim [⌜V⌝] compext_lemma1b));
a (LIST_SPEC_NTH_ASM_T 1 [⌜$∈⋎v⌝, ⌜x⌝, ⌜y⌝]
	(rewrite_thm_tac o (rewrite_rule [asm_rule ⌜x ∈ V⌝, asm_rule ⌜y ∈ V⌝])));
a (fc_tac [get_spec ⌜IsLub⌝]);
a (∃_tac ⌜xt⌝ THEN asm_rewrite_tac[]);
val compext_lemma2b = save_pop_thm "compext_lemma2b";
=TEX
}%ignore

=GFT
⦏compess_lemma1⦎ =
   ⊢ ∀ V
     ⦁ V ⊆ SetReps
         ⇒ (∀ r x y
             ⦁ x ∈ V ∧ y ∈ V
                 ⇒ (CompEss V r x y
                   ⇔ (∃ es
                   ⦁ ¬ OverDefinedL V es
                       ∧ IsUb
                         (PwS V $≤⋎t⋎4)
                         {Essence r x; Essence r y}
                         es)))
=TEX   
=GFT
⦏compess_lemma1b⦎ =
   ⊢ ∀ V
     ⦁ V ⊆ Syntax
         ⇒ (∀ r x y
         ⦁ x ∈ V ∧ y ∈ V
             ⇒ (CompEss V r x y
               ⇔ (∃ es
               ⦁ ¬ OverDefinedL V es
                   ∧ IsUb (PwS V $≤⋎t⋎4) {Essence r x; Essence r y} es)))
=TEX

\ignore{
=SML
set_goal([], ⌜∀V⦁ V ⊆ SetReps ⇒ ∀r x y⦁ x ∈ V ∧ y ∈ V ⇒ (CompEss V r x y
	⇔ ∃ es⦁ ¬ OverDefinedL V es
	   ∧ IsUb (PwS V $≤⋎t⋎4)
		{Essence r x; Essence r y}
		es)⌝);
a (REPEAT_N 6 strip_tac
	THEN rewrite_tac ([∈_in_clauses]@(map get_spec [⌜CompEss⌝, ⌜OverDefinedL⌝, ⌜Essence⌝, ⌜IsUb⌝, ⌜PwS⌝]))
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜λv⦁ Lub $≤⋎t⋎4 {r x v; r y v}⌝ THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (swap_nth_asm_concl_tac 1);
a (spec_nth_asm_tac 2 ⌜y'⌝);
(* *** Goal "1.2" *** *)
a (spec_nth_asm_tac 3 ⌜x''⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜CompFTV⌝, sets_ext_clauses, ∈_in_clauses]
	THEN strip_tac THEN asm_rewrite_tac[]
	THEN (accept_tac (rewrite_rule [∈_in_clauses] (list_∀_elim [⌜r x x''⌝, ⌜{r x x''; r y x''}⌝]
	(rewrite_rule [] (∀_elim ⌜$≤⋎t⋎4⌝ less_lub_lemma))))));
(* *** Goal "1.3" *** *)
a (spec_nth_asm_tac 3 ⌜x''⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜CompFTV⌝, sets_ext_clauses, ∈_in_clauses]
	THEN strip_tac THEN asm_rewrite_tac[]
	THEN (accept_tac (rewrite_rule [∈_in_clauses] (list_∀_elim [⌜r y x''⌝, ⌜{r x x''; r y x''}⌝]
	(rewrite_rule [] (∀_elim ⌜$≤⋎t⋎4⌝ less_lub_lemma))))));
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜λv⦁ r x v⌝);
(* *** Goal "2.1" *** *)
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule[ext_thm])));
(* *** Goal "2.2" *** *)
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (strip_asm_tac o (rewrite_rule [])));
a (spec_nth_asm_tac 4 ⌜λv⦁ r y v⌝);
(* *** Goal "2.2.1" *** *)
a (DROP_NTH_ASM_T 1 (strip_asm_tac o (rewrite_rule[ext_thm])));
(* *** Goal "2.2.2" *** *)
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (strip_asm_tac o (rewrite_rule [])));
a (spec_nth_asm_tac 7 ⌜z⌝);
a (rewrite_tac[get_spec ⌜CompFTV⌝]);
a (POP_ASM_T ante_tac);
a (DROP_NTH_ASM_T 1 ante_tac THEN DROP_NTH_ASM_T 2 ante_tac);
a (strip_asm_tac (∀_elim ⌜es z⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[∈_in_clauses]
	THEN strip_asm_tac (∀_elim ⌜r x z⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[∈_in_clauses]
	THEN strip_asm_tac (∀_elim ⌜r y z⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[∈_in_clauses]);
(* *** Goal "2.2.2.1" *** *)
a (rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜{fTrue; fB} = {fB; fTrue}⌝]);
(* *** Goal "2.2.2.2" *** *)
a (rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜{fFalse; fB} = {fB; fFalse}⌝]);
val compess_lemma1 = save_pop_thm "compess_lemma1";
=TEX
=SML
set_goal([], ⌜∀V⦁ V ⊆ Syntax ⇒ ∀r x y⦁ x ∈ V ∧ y ∈ V ⇒ (CompEss V r x y
	⇔ ∃ es⦁ ¬ OverDefinedL V es
	   ∧ IsUb (PwS V $≤⋎t⋎4)
		{Essence r x; Essence r y}
		es)⌝);
a (REPEAT_N 6 strip_tac
	THEN rewrite_tac ([∈_in_clauses]@(map get_spec [⌜CompEss⌝, ⌜OverDefinedL⌝, ⌜Essence⌝, ⌜IsUb⌝, ⌜PwS⌝]))
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜λv⦁ Lub $≤⋎t⋎4 {r x v; r y v}⌝ THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (swap_nth_asm_concl_tac 1);
a (spec_nth_asm_tac 2 ⌜y'⌝);
(* *** Goal "1.2" *** *)
a (spec_nth_asm_tac 3 ⌜x''⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜CompFTV⌝, sets_ext_clauses, ∈_in_clauses]
	THEN strip_tac THEN asm_rewrite_tac[]
	THEN (accept_tac (rewrite_rule [∈_in_clauses] (list_∀_elim [⌜r x x''⌝, ⌜{r x x''; r y x''}⌝]
	(rewrite_rule [] (∀_elim ⌜$≤⋎t⋎4⌝ less_lub_lemma))))));
(* *** Goal "1.3" *** *)
a (spec_nth_asm_tac 3 ⌜x''⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜CompFTV⌝, sets_ext_clauses, ∈_in_clauses]
	THEN strip_tac THEN asm_rewrite_tac[]
	THEN (accept_tac (rewrite_rule [∈_in_clauses] (list_∀_elim [⌜r y x''⌝, ⌜{r x x''; r y x''}⌝]
	(rewrite_rule [] (∀_elim ⌜$≤⋎t⋎4⌝ less_lub_lemma))))));
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜λv⦁ r x v⌝);
(* *** Goal "2.1" *** *)
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule[ext_thm])));
(* *** Goal "2.2" *** *)
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (strip_asm_tac o (rewrite_rule [])));
a (spec_nth_asm_tac 4 ⌜λv⦁ r y v⌝);
(* *** Goal "2.2.1" *** *)
a (DROP_NTH_ASM_T 1 (strip_asm_tac o (rewrite_rule[ext_thm])));
(* *** Goal "2.2.2" *** *)
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (strip_asm_tac o (rewrite_rule [])));
a (spec_nth_asm_tac 7 ⌜z⌝);
a (rewrite_tac[get_spec ⌜CompFTV⌝]);
a (POP_ASM_T ante_tac);
a (DROP_NTH_ASM_T 1 ante_tac THEN DROP_NTH_ASM_T 2 ante_tac);
a (strip_asm_tac (∀_elim ⌜es z⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[∈_in_clauses]
	THEN strip_asm_tac (∀_elim ⌜r x z⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[∈_in_clauses]
	THEN strip_asm_tac (∀_elim ⌜r y z⌝ ftv_cases_thm)
	THEN_TRY asm_rewrite_tac[∈_in_clauses]);
(* *** Goal "2.2.2.1" *** *)
a (rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜{fTrue; fB} = {fB; fTrue}⌝]);
(* *** Goal "2.2.2.2" *** *)
a (rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜{fFalse; fB} = {fB; fFalse}⌝]);
val compess_lemma1b = save_pop_thm "compess_lemma1b";
=TEX
}%ignore

=GFT
⦏compess_lemma2⦎ =
   ⊢ ∀ V
     ⦁ V ⊆ SetReps
         ⇒ (∀ $∈⋎v x y
         ⦁ x ∈ V ∧ y ∈ V
             ⇒ CompEss V $∈⋎v x y
               = (∃ es
               ⦁ ¬ OverDefinedL V es
                   ∧ IsLub
                     (PwS V $≤⋎t⋎4)
                     {Essence $∈⋎v x; Essence $∈⋎v y}
                     es))
=TEX

\ignore{
=SML
set_goal([], ⌜∀V⦁ V ⊆ SetReps ⇒ ∀$∈⋎v x y⦁ x ∈ V ∧ y ∈ V ⇒ (CompEss V $∈⋎v x y
	⇔ ∃ es⦁ ¬ OverDefinedL V es
	   ∧ IsLub (PwS V $≤⋎t⋎4)
		{Essence $∈⋎v x; Essence $∈⋎v y}
		es)⌝);
a (REPEAT strip_tac THEN all_fc_tac [compess_lemma1]);
(* *** Goal "1" *** *)
a (asm_tac (rewrite_rule [get_spec ⌜LubsExist⌝] (list_∀_elim [⌜V⌝, ⌜$≤⋎t⋎4⌝] pws_lubs_exist_thm)));
a (spec_nth_asm_tac 1 ⌜{Essence $∈⋎v x; Essence $∈⋎v y}⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac []);
a (fc_tac [get_spec ⌜IsLub⌝, OverDefinedL_≤⋎t⋎4_lemma]);
a (asm_fc_tac[]);
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (strip_asm_tac (list_∀_elim [⌜V⌝] compess_lemma1));
a (LIST_SPEC_NTH_ASM_T 1 [⌜$∈⋎v⌝, ⌜x⌝, ⌜y⌝]
	(rewrite_thm_tac o (rewrite_rule [asm_rule ⌜x ∈ V⌝, asm_rule ⌜y ∈ V⌝])));
a (fc_tac [get_spec ⌜IsLub⌝]);
a (∃_tac ⌜es⌝ THEN asm_rewrite_tac[]);
val compess_lemma2 = save_pop_thm "compess_lemma2";
=TEX
}%ignore

=GFT
⦏compess_lemma2b⦎ =
   ⊢ ∀ V
     ⦁ V ⊆ Syntax
         ⇒ (∀ $∈⋎v x y
         ⦁ x ∈ V ∧ y ∈ V
             ⇒ (CompEss V $∈⋎v x y
               ⇔ (∃ es
               ⦁ ¬ OverDefinedL V es
                   ∧ IsLub
                     (PwS V $≤⋎t⋎4)
                     {Essence $∈⋎v x; Essence $∈⋎v y}
                     es)))
=TEX
\ignore{
=SML
set_goal([], ⌜∀V⦁ V ⊆ Syntax ⇒ ∀$∈⋎v x y⦁ x ∈ V ∧ y ∈ V ⇒ (CompEss V $∈⋎v x y
	⇔ ∃ es⦁ ¬ OverDefinedL V es
	   ∧ IsLub (PwS V $≤⋎t⋎4)
		{Essence $∈⋎v x; Essence $∈⋎v y}
		es)⌝);
a (REPEAT strip_tac THEN all_fc_tac [compess_lemma1b]);
(* *** Goal "1" *** *)
a (asm_tac (rewrite_rule [get_spec ⌜LubsExist⌝] (list_∀_elim [⌜V⌝, ⌜$≤⋎t⋎4⌝] pws_lubs_exist_thm)));
a (spec_nth_asm_tac 1 ⌜{Essence $∈⋎v x; Essence $∈⋎v y}⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac []);
a (fc_tac [get_spec ⌜IsLub⌝, OverDefinedL_≤⋎t⋎4_lemma]);
a (asm_fc_tac[]);
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (strip_asm_tac (list_∀_elim [⌜V⌝] compess_lemma1b));
a (LIST_SPEC_NTH_ASM_T 1 [⌜$∈⋎v⌝, ⌜x⌝, ⌜y⌝]
	(rewrite_thm_tac o (rewrite_rule [asm_rule ⌜x ∈ V⌝, asm_rule ⌜y ∈ V⌝])));
a (fc_tac [get_spec ⌜IsLub⌝]);
a (∃_tac ⌜es⌝ THEN asm_rewrite_tac[]);
val compess_lemma2b = save_pop_thm "compess_lemma2b";
=TEX
}%ignore

If there were a setrep {\it z} whose extension and essence were upper bounds for two setsreps {\it x} and {\it y} which have compatible and not overdefined extension and essences, then we could use the image of {\it z} under the semantics to show that the imagss of {\it x} and {\it y} have compatible essences.
Unfortunately there need not be any such setrep.

The proof plan, for showing that the compatible elements {\it x} and {\it y} will map to elements whose essences are compatible, is to add an extra element into the interpretation we are working with which has the required extensions and essences (not overdefined upper bounds of those of {\it x} and {\it y}).

In order to define the required extension I first use the above two lemmas to define (loosely) functions which yield not-overdefined upper bounds for extensions and essences.


\ignore{
=SML
set_goal([], ⌜∃ExtUb⦁
	∀(V, $∈⋎v) x y⦁ V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V ∧ CompExt V $∈⋎v x y ⇒
	let xt = ExtUb (V, $∈⋎v) x y
	in ¬ OverDefinedL V xt
                       ∧ IsUb
                         (PwS V $≤⋎t⋎4)
                         {Extension $∈⋎v x; Extension $∈⋎v y}
                         xt⌝);
a (prove_∃_tac THEN REPEAT strip_tac (* THEN rewrite_tac [let_def] *) );
a (strip_asm_tac compext_lemma1);
a (spec_nth_asm_tac 1 ⌜Fst x'⌝ THEN_TRY asm_rewrite_tac[]);
a (spec_nth_asm_tac 1 ⌜Snd x'⌝ THEN_TRY asm_rewrite_tac[]);
a (list_spec_nth_asm_tac  1 [⌜x''⌝, ⌜y'⌝] THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜xt⌝);
(* *** Goal "2" *** *)
a (∃_tac ⌜xt⌝ THEN asm_rewrite_tac[]); 
val _ = save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏ExtUb⦎ : GS SET × (GS, FTV)BR → GS → GS → (GS → BOOL DPO)
├───────────
│ ∀(V, $∈⋎v) x y⦁
	V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V ∧ CompExt V $∈⋎v x y ⇒
	let xt = ExtUb (V, $∈⋎v) x y
	in ¬ OverDefinedL V xt
                       ∧ IsUb
                         (PwS V $≤⋎t⋎4)
                         {Extension $∈⋎v x; Extension $∈⋎v y}
                         xt
■

\ignore{
=SML
set_goal([], ⌜∃ExtUb2⦁
	∀(V, $∈⋎v) x y⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ CompExt V $∈⋎v x y ⇒
	let xt = ExtUb2 (V, $∈⋎v) x y
	in ¬ OverDefinedL V xt
                       ∧ IsUb
                         (PwS V $≤⋎t⋎4)
                         {Extension $∈⋎v x; Extension $∈⋎v y}
                         xt⌝);
a (prove_∃_tac THEN REPEAT strip_tac (* THEN rewrite_tac [let_def] *) );
a (strip_asm_tac compext_lemma1b);
a (spec_nth_asm_tac 1 ⌜Fst x'⌝ THEN_TRY asm_rewrite_tac[]);
a (spec_nth_asm_tac 1 ⌜Snd x'⌝ THEN_TRY asm_rewrite_tac[]);
a (list_spec_nth_asm_tac  1 [⌜x''⌝, ⌜y'⌝] THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜xt⌝);
(* *** Goal "2" *** *)
a (∃_tac ⌜xt⌝ THEN asm_rewrite_tac[]); 
val _ = save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏ExtUb2⦎ : GS SET × (GS, FTV)BR → GS → GS → (GS → BOOL DPO)
├───────────
│ ∀(V, $∈⋎v) x y⦁
	V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ CompExt V $∈⋎v x y ⇒
	let xt = ExtUb2 (V, $∈⋎v) x y
	in ¬ OverDefinedL V xt
                       ∧ IsUb
                         (PwS V $≤⋎t⋎4)
                         {Extension $∈⋎v x; Extension $∈⋎v y}
                         xt
■

\ignore{
=SML
set_goal([], ⌜∃ExtLub⦁
	∀(V, $∈⋎v) x y⦁ V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V ∧ CompExt V $∈⋎v x y ⇒
	let xt = ExtLub (V, $∈⋎v) x y
	in ¬ OverDefinedL V xt
                       ∧ IsLub
                         (PwS V $≤⋎t⋎4)
                         {Extension $∈⋎v x; Extension $∈⋎v y}
                         xt⌝);
a (prove_∃_tac THEN REPEAT strip_tac (* THEN rewrite_tac [let_def] *));
a (strip_asm_tac compext_lemma2);
a (spec_nth_asm_tac 1 ⌜Fst x'⌝ THEN_TRY asm_rewrite_tac[]);
a (spec_nth_asm_tac 1 ⌜Snd x'⌝ THEN_TRY asm_rewrite_tac[]);
a (list_spec_nth_asm_tac  1 [⌜x''⌝, ⌜y'⌝] THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜xt⌝);
(* *** Goal "2" *** *)
a (∃_tac ⌜xt⌝ THEN asm_rewrite_tac[]); 
val _ = save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏ExtLub⦎ : GS SET × (GS, FTV)BR → GS → GS → (GS → BOOL DPO)
├───────────
│ ∀(V, $∈⋎v) x y⦁
	V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V ∧ CompExt V $∈⋎v x y ⇒
	let xt = ExtLub (V, $∈⋎v) x y
	in ¬ OverDefinedL V xt
                       ∧ IsLub
                         (PwS V $≤⋎t⋎4)
                         {Extension $∈⋎v x; Extension $∈⋎v y}
                         xt
■

\ignore{
=SML
set_goal([], ⌜∃ExtLub2⦁
	∀(V, $∈⋎v) x y⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ CompExt V $∈⋎v x y ⇒
	let xt = ExtLub2 (V, $∈⋎v) x y
	in ¬ OverDefinedL V xt
                       ∧ IsLub
                         (PwS V $≤⋎t⋎4)
                         {Extension $∈⋎v x; Extension $∈⋎v y}
                         xt⌝);
a (prove_∃_tac THEN REPEAT strip_tac (* THEN rewrite_tac [let_def] *));
a (strip_asm_tac compext_lemma2b);
a (spec_nth_asm_tac 1 ⌜Fst x'⌝ THEN_TRY asm_rewrite_tac[]);
a (spec_nth_asm_tac 1 ⌜Snd x'⌝ THEN_TRY asm_rewrite_tac[]);
a (list_spec_nth_asm_tac  1 [⌜x''⌝, ⌜y'⌝] THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜xt⌝);
(* *** Goal "2" *** *)
a (∃_tac ⌜xt⌝ THEN asm_rewrite_tac[]); 
val _ = save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏ExtLub2⦎ : GS SET × (GS, FTV)BR → GS → GS → (GS → BOOL DPO)
├───────────
│ ∀(V, $∈⋎v) x y⦁
	V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ CompExt V $∈⋎v x y ⇒
	let xt = ExtLub2 (V, $∈⋎v) x y
	in ¬ OverDefinedL V xt
                       ∧ IsLub
                         (PwS V $≤⋎t⋎4)
                         {Extension $∈⋎v x; Extension $∈⋎v y}
                         xt
■

=GFT
⦏ExtUb_lemma1⦎ =
   ⊢ ∀ (V, $∈⋎v) x y
     ⦁ V ⊆ SetReps
           ∧ x ∈ V
           ∧ y ∈ V
           ∧ CompExt V $∈⋎v x y
         ⇒ ¬ OverDefinedL V (ExtUb (V, $∈⋎v) x y)
           ∧ (∀ z⦁ z ∈ V ⇒ (z ∈⋎v x) ≤⋎t⋎4 ExtUb (V, $∈⋎v) x y z
		∧ (z ∈⋎v y) ≤⋎t⋎4 ExtUb (V, $∈⋎v) x y z)
=TEX

\ignore{
=SML
set_goal([], ⌜∀(V, $∈⋎v) x y⦁
	V ⊆ SetReps ∧ ¬ OverDefined V $∈⋎v ∧ x ∈ V ∧ y ∈ V ∧ CompExt V $∈⋎v x y ⇒
	¬ OverDefinedL V (ExtUb (V, $∈⋎v) x y)
	∧ ∀z⦁ z ∈ V ⇒ (z ∈⋎v x) ≤⋎t⋎4 ExtUb (V, $∈⋎v) x y z
		∧ (z ∈⋎v y) ≤⋎t⋎4 ExtUb (V, $∈⋎v) x y z⌝);
a (REPEAT_N 7 strip_tac THEN all_asm_fc_tac [rewrite_rule [let_def] (get_spec ⌜ExtUb⌝)]);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜IsUb⌝, get_spec ⌜PwS⌝, ∈_in_clauses, get_spec ⌜Extension⌝]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜CombC $∈⋎v x⌝);
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (strip_asm_tac o (rewrite_rule [])));
a (spec_nth_asm_tac 2 ⌜CombC $∈⋎v y⌝);
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (strip_asm_tac o (rewrite_rule [])));
val ExtUb_lemma1 = save_pop_thm "ExtUb_lemma1";
=TEX
}%ignore

=GFT
⦏ExtLub_lemma1⦎ =
   ⊢ ∀(V, $∈⋎v) x y⦁
	V ⊆ SetReps ∧ ¬ OverDefined V $∈⋎v ∧ x ∈ V ∧ y ∈ V ∧ CompExt V $∈⋎v x y ⇒
	¬ OverDefinedL V (ExtLub (V, $∈⋎v) x y)
	∧ ∀z⦁ z ∈ V ⇒ (z ∈⋎v x) ≤⋎t⋎4 ExtLub (V, $∈⋎v) x y z
		∧ (z ∈⋎v y) ≤⋎t⋎4 ExtLub (V, $∈⋎v) x y z
=TEX

\ignore{
=SML
set_goal([], ⌜∀(V, $∈⋎v) x y⦁
	V ⊆ SetReps ∧ ¬ OverDefined V $∈⋎v ∧ x ∈ V ∧ y ∈ V ∧ CompExt V $∈⋎v x y ⇒
	¬ OverDefinedL V (ExtLub (V, $∈⋎v) x y)
	∧ ∀z⦁ z ∈ V ⇒ (z ∈⋎v x) ≤⋎t⋎4 ExtLub (V, $∈⋎v) x y z
		∧ (z ∈⋎v y) ≤⋎t⋎4 ExtLub (V, $∈⋎v) x y z⌝);
a (REPEAT_N 6 strip_tac THEN all_asm_fc_tac [rewrite_rule [let_def] (get_spec ⌜ExtLub⌝)]);
a (asm_rewrite_tac[] THEN strip_tac THEN strip_tac);
a (DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac [get_spec ⌜IsUb⌝, get_spec ⌜IsLub⌝, get_spec ⌜PwS⌝, ∈_in_clauses, get_spec ⌜Extension⌝]
	THEN strip_tac);
a (spec_nth_asm_tac 2 ⌜CombC $∈⋎v x⌝);
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
a (spec_nth_asm_tac 3 ⌜CombC $∈⋎v y⌝);
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
val ExtLub_lemma1 = save_pop_thm "ExtLub_lemma1";
=TEX
}%ignore

=GFT
⦏ExtLub2_lemma1⦎ =
   ⊢ ∀ (V, $∈⋎v) x y
     ⦁ V ⊆ Syntax ∧ ¬ OverDefined V $∈⋎v ∧ x ∈ V ∧ y ∈ V ∧ CompExt V $∈⋎v x y
         ⇒ ¬ OverDefinedL V (ExtLub2 (V, $∈⋎v) x y)
           ∧ (∀ z
           ⦁ z ∈ V
               ⇒ (z ∈⋎v x) ≤⋎t⋎4 ExtLub2 (V, $∈⋎v) x y z
                 ∧ (z ∈⋎v y) ≤⋎t⋎4 ExtLub2 (V, $∈⋎v) x y z)
=TEX

\ignore{
=SML
set_goal([], ⌜∀(V, $∈⋎v) x y⦁
	V ⊆ Syntax ∧ ¬ OverDefined V $∈⋎v ∧ x ∈ V ∧ y ∈ V ∧ CompExt V $∈⋎v x y ⇒
	¬ OverDefinedL V (ExtLub2 (V, $∈⋎v) x y)
	∧ ∀z⦁ z ∈ V ⇒ (z ∈⋎v x) ≤⋎t⋎4 ExtLub2 (V, $∈⋎v) x y z
		∧ (z ∈⋎v y) ≤⋎t⋎4 ExtLub2 (V, $∈⋎v) x y z⌝);
a (REPEAT_N 6 strip_tac THEN all_asm_fc_tac [rewrite_rule [let_def] (get_spec ⌜ExtLub2⌝)]);
a (asm_rewrite_tac[] THEN strip_tac THEN strip_tac);
a (DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac [get_spec ⌜IsUb⌝, get_spec ⌜IsLub⌝, get_spec ⌜PwS⌝, ∈_in_clauses, get_spec ⌜Extension⌝]
	THEN strip_tac);
a (spec_nth_asm_tac 2 ⌜CombC $∈⋎v x⌝);
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
a (spec_nth_asm_tac 3 ⌜CombC $∈⋎v y⌝);
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
val ExtLub2_lemma1 = save_pop_thm "ExtLub2_lemma1";
=TEX
}%ignore

\ignore{
=SML
set_goal([], ⌜∃EssUb⦁
	∀(V, $∈⋎v) x y⦁ V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V ∧ CompEss V $∈⋎v x y ⇒
	let es = EssUb (V, $∈⋎v) x y
	in ¬ OverDefinedL V es
                       ∧ IsUb
                         (PwS V $≤⋎t⋎4)
                         {Essence $∈⋎v x; Essence $∈⋎v y}
                         es⌝);
a (prove_∃_tac THEN REPEAT strip_tac (* THEN rewrite_tac [let_def] *) );
a (strip_asm_tac compess_lemma1);
a (spec_nth_asm_tac 1 ⌜Fst x'⌝ THEN_TRY asm_rewrite_tac[]);
a (spec_nth_asm_tac 1 ⌜Snd x'⌝ THEN_TRY asm_rewrite_tac[]);
a (list_spec_nth_asm_tac  1 [⌜x''⌝, ⌜y'⌝] THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜es⌝);
(* *** Goal "2" *** *)
a (∃_tac ⌜es⌝ THEN asm_rewrite_tac[]); 
val _ = save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏EssUb⦎ : GS SET × (GS, FTV)BR → GS → GS → (GS → BOOL DPO)
├───────────
│ ∀(V, $∈⋎v) x y⦁
	V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V ∧ CompEss V $∈⋎v x y ⇒
	let es = EssUb (V, $∈⋎v) x y
	in ¬ OverDefinedL V es
                       ∧ IsUb
                         (PwS V $≤⋎t⋎4)
                         {Essence $∈⋎v x; Essence $∈⋎v y}
                         es
■

=GFT
⦏EssUb_lemma1⦎ =
   ⊢ ∀ (V, $∈⋎v) x y
     ⦁ V ⊆ SetReps
           ∧ x ∈ V
           ∧ y ∈ V
           ∧ CompEss V $∈⋎v x y
         ⇒ ¬ OverDefinedL V (EssUb (V, $∈⋎v) x y)
           ∧ (∀ z
           ⦁ z ∈ V
               ⇒ (x ∈⋎v z) ≤⋎t⋎4 EssUb (V, $∈⋎v) x y z
                 ∧ (y ∈⋎v z) ≤⋎t⋎4 EssUb (V, $∈⋎v) x y z)
=TEX

\ignore{
=SML
set_goal([], ⌜∀(V, $∈⋎v) x y⦁
	V ⊆ SetReps ∧ ¬ OverDefined V $∈⋎v ∧ x ∈ V ∧ y ∈ V ∧ CompEss V $∈⋎v x y ⇒
	¬ OverDefinedL V (EssUb (V, $∈⋎v) x y)
	∧ ∀z⦁ z ∈ V ⇒ (x ∈⋎v z) ≤⋎t⋎4 EssUb (V, $∈⋎v) x y z
		∧ (y ∈⋎v z) ≤⋎t⋎4 EssUb (V, $∈⋎v) x y z⌝);
a (REPEAT_N 7 strip_tac THEN all_asm_fc_tac [rewrite_rule [let_def] (get_spec ⌜EssUb⌝)]);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜IsUb⌝, get_spec ⌜PwS⌝, ∈_in_clauses, get_spec ⌜Essence⌝]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜$∈⋎v x⌝);
a (spec_nth_asm_tac 1 ⌜z⌝);
a (spec_nth_asm_tac 2 ⌜$∈⋎v y⌝);
a (spec_nth_asm_tac 1 ⌜z⌝);
val EssUb_lemma1 = save_pop_thm "EssUb_lemma1";
=TEX
}%ignore

\ignore{
=SML
set_goal([], ⌜∃EssLub⦁
	∀(V, $∈⋎v) x y⦁ V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V ∧ CompEss V $∈⋎v x y ⇒
	let es = EssLub (V, $∈⋎v) x y
	in ¬ OverDefinedL V es
                       ∧ IsLub
                         (PwS V $≤⋎t⋎4)
                         {Essence $∈⋎v x; Essence $∈⋎v y}
                         es⌝);
a (prove_∃_tac THEN REPEAT strip_tac (* THEN rewrite_tac [let_def] *) );
a (strip_asm_tac compess_lemma2);
a (spec_nth_asm_tac 1 ⌜Fst x'⌝ THEN_TRY asm_rewrite_tac[]);
a (spec_nth_asm_tac 1 ⌜Snd x'⌝ THEN_TRY asm_rewrite_tac[]);
a (list_spec_nth_asm_tac  1 [⌜x''⌝, ⌜y'⌝] THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜es⌝);
(* *** Goal "2" *** *)
a (∃_tac ⌜es⌝ THEN asm_rewrite_tac[]); 
val _ = save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏EssLub⦎ : GS SET × (GS, FTV)BR → GS → GS → (GS → BOOL DPO)
├───────────
│ ∀(V, $∈⋎v) x y⦁
	V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V ∧ CompEss V $∈⋎v x y ⇒
	let es = EssLub (V, $∈⋎v) x y
	in ¬ OverDefinedL V es
                       ∧ IsLub
                         (PwS V $≤⋎t⋎4)
                         {Essence $∈⋎v x; Essence $∈⋎v y}
                         es
■

\ignore{
=SML
set_goal([], ⌜∃EssLub2⦁
	∀(V, $∈⋎v) x y⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ CompEss V $∈⋎v x y ⇒
	let es = EssLub2 (V, $∈⋎v) x y
	in ¬ OverDefinedL V es
                       ∧ IsLub
                         (PwS V $≤⋎t⋎4)
                         {Essence $∈⋎v x; Essence $∈⋎v y}
                         es⌝);
a (prove_∃_tac THEN REPEAT strip_tac (* THEN rewrite_tac [let_def] *) );
a (strip_asm_tac compess_lemma2b);
a (spec_nth_asm_tac 1 ⌜Fst x'⌝ THEN_TRY asm_rewrite_tac[]);
a (spec_nth_asm_tac 1 ⌜Snd x'⌝ THEN_TRY asm_rewrite_tac[]);
a (list_spec_nth_asm_tac  1 [⌜x''⌝, ⌜y'⌝] THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜es⌝);
(* *** Goal "2" *** *)
a (∃_tac ⌜es⌝ THEN asm_rewrite_tac[]); 
val _ = save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏EssLub2⦎ : GS SET × (GS, FTV)BR → GS → GS → (GS → BOOL DPO)
├───────────
│ ∀(V, $∈⋎v) x y⦁
	V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ CompEss V $∈⋎v x y ⇒
	let es = EssLub2 (V, $∈⋎v) x y
	in ¬ OverDefinedL V es
                       ∧ IsLub
                         (PwS V $≤⋎t⋎4)
                         {Essence $∈⋎v x; Essence $∈⋎v y}
                         es
■

=GFT
⦏EssLub_lemma1⦎ =
   ⊢ ∀(V, $∈⋎v) x y⦁
	V ⊆ SetReps ∧ ¬ OverDefined V $∈⋎v ∧ x ∈ V ∧ y ∈ V ∧ CompEss V $∈⋎v x y ⇒
	¬ OverDefinedL V (EssLub (V, $∈⋎v) x y)
	∧ ∀z⦁ z ∈ V ⇒ (x ∈⋎v z) ≤⋎t⋎4 EssLub (V, $∈⋎v) x y z
		∧ (y ∈⋎v z) ≤⋎t⋎4 EssLub (V, $∈⋎v) x y z
=TEX

\ignore{
=SML
set_goal([], ⌜∀(V, $∈⋎v) x y⦁
	V ⊆ SetReps ∧ ¬ OverDefined V $∈⋎v ∧ x ∈ V ∧ y ∈ V ∧ CompEss V $∈⋎v x y ⇒
	¬ OverDefinedL V (EssLub (V, $∈⋎v) x y)
	∧ ∀z⦁ z ∈ V ⇒ (x ∈⋎v z) ≤⋎t⋎4 EssLub (V, $∈⋎v) x y z
		∧ (y ∈⋎v z) ≤⋎t⋎4 EssLub (V, $∈⋎v) x y z⌝);
a (REPEAT_N 6 strip_tac THEN all_asm_fc_tac [rewrite_rule [let_def] (get_spec ⌜EssLub⌝)]);
a (asm_rewrite_tac[] THEN strip_tac THEN strip_tac);
a (DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac [get_spec ⌜IsUb⌝, get_spec ⌜IsLub⌝, get_spec ⌜PwS⌝, ∈_in_clauses, get_spec ⌜Essence⌝]
	THEN strip_tac);
a (spec_nth_asm_tac 2 ⌜$∈⋎v x⌝);
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
a (spec_nth_asm_tac 3 ⌜$∈⋎v y⌝);
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
val EssLub_lemma1 = save_pop_thm "EssLub_lemma1";
=TEX
}%ignore

=GFT
⦏EssLub_lemma1⦎ =
   ⊢ ∀ (V, $∈⋎v) x y
     ⦁ V ⊆ Syntax ∧ ¬ OverDefined V $∈⋎v ∧ x ∈ V ∧ y ∈ V ∧ CompEss V $∈⋎v x y
         ⇒ ¬ OverDefinedL V (EssLub2 (V, $∈⋎v) x y)
           ∧ (∀ z
           ⦁ z ∈ V
               ⇒ (x ∈⋎v z) ≤⋎t⋎4 EssLub2 (V, $∈⋎v) x y z
                 ∧ (y ∈⋎v z) ≤⋎t⋎4 EssLub2 (V, $∈⋎v) x y z)
=TEX

\ignore{
=SML
set_goal([], ⌜∀(V, $∈⋎v) x y⦁
	V ⊆ Syntax ∧ ¬ OverDefined V $∈⋎v ∧ x ∈ V ∧ y ∈ V ∧ CompEss V $∈⋎v x y ⇒
	¬ OverDefinedL V (EssLub2 (V, $∈⋎v) x y)
	∧ ∀z⦁ z ∈ V ⇒ (x ∈⋎v z) ≤⋎t⋎4 EssLub2 (V, $∈⋎v) x y z
		∧ (y ∈⋎v z) ≤⋎t⋎4 EssLub2 (V, $∈⋎v) x y z⌝);
a (REPEAT_N 6 strip_tac THEN all_asm_fc_tac [rewrite_rule [let_def] (get_spec ⌜EssLub2⌝)]);
a (asm_rewrite_tac[] THEN strip_tac THEN strip_tac);
a (DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac [get_spec ⌜IsUb⌝, get_spec ⌜IsLub⌝, get_spec ⌜PwS⌝, ∈_in_clauses, get_spec ⌜Essence⌝]
	THEN strip_tac);
a (spec_nth_asm_tac 2 ⌜$∈⋎v x⌝);
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
a (spec_nth_asm_tac 3 ⌜$∈⋎v y⌝);
a (SPEC_NTH_ASM_T 1 ⌜z⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
val EssLub_lemma1b = save_pop_thm "EssLub_lemma1b";
=TEX
}%ignore

The required extension to the membership relation is defined as follows:

ⓈHOLCONST
│ ⦏MsExtend⦎ : GS SET × (GS, FTV)BR → GS → GS → (GS, FTV)BR
├───────────
│ ∀(V, $∈⋎v) x y⦁ MsExtend (V, $∈⋎v) x y =
│	let xt = ExtUb (V, $∈⋎v) x y
│	and es = EssUb (V, $∈⋎v) x y
│	in (λx' y'⦁
│		if x' = ∅⋎g
│		then if y' = ∅⋎g then Lub $≤⋎t⋎4 {x ∈⋎v x; y ∈⋎v x; x ∈⋎v y; y ∈⋎v y} else es y'
│		else if y' = ∅⋎g then xt x' else x' ∈⋎v y')
■

ⓈHOLCONST
│ ⦏MsExtend2⦎ : GS SET × (GS, FTV)BR → GS → GS → (GS, FTV)BR
├───────────
│ ∀(V, $∈⋎v) x y⦁ MsExtend2 (V, $∈⋎v) x y =
│	let xt = ExtLub2 (V, $∈⋎v) x y
│	and es = EssLub2 (V, $∈⋎v) x y
│	in (λx' y'⦁
│		if x' = ∅⋎g
│		then if y' = ∅⋎g then Lub $≤⋎t⋎4 {x ∈⋎v x; y ∈⋎v x; x ∈⋎v y; y ∈⋎v y} else es y'
│		else if y' = ∅⋎g then xt x' else x' ∈⋎v y')
■

\subsubsection{Properties of Extensions}

First that these extensions are the same over the original domain as the unextended relation.

=GFT
⦏PmrEq_MsExtend_lemma1⦎ =
   ⊢ ∀ (V, $∈⋎v) x y⦁ V ⊆ Syntax ⇒ PmrEq V r (MsExtend (V, r) x y)

⦏PmrEq_MsExtend_lemma2⦎ =
   ⊢ ∀ (V, $∈⋎v) x y⦁ V ⊆ Syntax ⇒ PmrEq V (MsExtend (V, r) x y) r

⦏PmrEq_MsExtend2_lemma2⦎ =
   ⊢ ∀ (V, $∈⋎v) x y⦁ V ⊆ Syntax ⇒ PmrEq V (MsExtend2 (V, r) x y) r
=TEX

\ignore{
=SML
set_goal([], ⌜∀(V, r) x y⦁ V ⊆ Syntax ⇒ PmrEq V r (MsExtend (V, r) x y)⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜PmrEq⌝, get_spec ⌜MsExtend⌝, let_def]
	THEN REPEAT strip_tac);
a (ALL_FC_T rewrite_tac [¬∅⋎g_∈_syntax_lemma3]);
val PmrEq_MsExtend_lemma1 = save_pop_thm "PmrEq_MsExtend_lemma1";

set_goal([], ⌜∀(V, r) x y⦁ V ⊆ Syntax ⇒ PmrEq V (MsExtend (V, r) x y) r⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜PmrEq⌝, get_spec ⌜MsExtend⌝, let_def]
	THEN REPEAT strip_tac);
a (ALL_FC_T rewrite_tac [¬∅⋎g_∈_syntax_lemma3]);
val PmrEq_MsExtend_lemma2 = save_pop_thm "PmrEq_MsExtend_lemma2";

set_goal([], ⌜∀(V, r) x y⦁ V ⊆ Syntax ⇒ PmrEq V (MsExtend2 (V, r) x y) r⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜PmrEq⌝, get_spec ⌜MsExtend2⌝, let_def]
	THEN REPEAT strip_tac);
a (ALL_FC_T rewrite_tac [¬∅⋎g_∈_syntax_lemma3]);
val PmrEq_MsExtend2_lemma2 = save_pop_thm "PmrEq_MsExtend2_lemma2";
=TEX
}%ignore

The evaluation of formulae using the extended relation gives the same results if the stiplulated domain of quantification remains the same.
(I don't know why I did not obtain more general results than these, though these particular ones suffice to show that the resulting essences of the two elements determining an extension, after application of the semantic functor, are unaffected by the extension to the structure.)

=GFT
⦏EvalForm_MsExtend_lemma1⦎ =
   ⊢ ∀ (V, r) x y z
     ⦁ V ⊆ Syntax ∧ y ∈ V ∧ z ∈ V
         ⇒ EvalForm
             (EvalCf_ftv, $≤⋎t⋎4, V, MsExtend (V, r) x y)
             z
             (Param_∅ y)
           = EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) z (Param_∅ y)
=TEX

=GFT
⦏EvalForm_MsExtend2_lemma1⦎ =
   ⊢ ∀ (V, r) x y z
     ⦁ V ⊆ Syntax ∧ y ∈ V ∧ z ∈ V
         ⇒ EvalForm
             (EvalCf_ftv, $≤⋎t⋎4, V, MsExtend2 (V, r) x y)
             z
             (Param_∅ y)
           = EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) z (Param_∅ y)
=TEX

=GFT
⦏EvalForm_MsExtend_lemma2⦎ =
   ⊢ ∀ (V, r) x y z
     ⦁ V ⊆ Syntax ∧ x ∈ V ∧ z ∈ V
         ⇒ EvalForm
             (EvalCf_ftv, $≤⋎t⋎4, V, MsExtend (V, r) x y)
             z
             (Param_∅ x)
           = EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) z (Param_∅ x)
=TEX

=GFT
⦏EvalForm_MsExtend2_lemma2⦎ =
   ⊢ ∀ (V, r) x y z
     ⦁ V ⊆ Syntax ∧ x ∈ V ∧ z ∈ V
         ⇒ EvalForm
             (EvalCf_ftv, $≤⋎t⋎4, V, MsExtend2 (V, r) x y)
             z
             (Param_∅ x)
           = EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) z (Param_∅ x)
=TEX

=GFT
⦏EvalForm_MsExtend2_lemma3⦎ =
   ⊢ ∀ (V, $∈⋎v) x y v w
     ⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ v ∈ V ∧ w ∈ V
         ⇒ EvalForm
             (EvalCf_ftv, $≤⋎t⋎4, V, MsExtend2 (V, r) x y)
             v
             (Param_∅ w)
           = EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) v (Param_∅ w)
=TEX

\ignore{
=SML
set_goal([], ⌜∀(V, $∈⋎v) x y z⦁ V ⊆ Syntax ∧ y ∈ V ∧ z ∈ V
	   ⇒ EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, MsExtend (V, r) x y) z (Param_∅ y)
	     = EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) z (Param_∅ y)⌝);
a (REPEAT strip_tac);
a (fc_tac [PmrEq_MsExtend_lemma2]);
a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜V ⊆ Syntax ∧ z ∈ V ⇒ z ∈ Syntax⌝]);
a (lemma_tac ⌜IxRan (Param_∅ y) ⊆ V⌝ THEN1 (asm_prove_tac[sets_ext_clauses]));
a (ALL_UFC_T (MAP_EVERY asm_tac) [rewrite_rule [] (list_∀_elim [⌜EvalCf_ftv⌝, ⌜$≤⋎t⋎4⌝, ⌜V⌝, ⌜V⌝,
	⌜z⌝, ⌜MsExtend (V, r) x y⌝, ⌜r⌝] PmrEq_EvalForm_lemma)]);
a (asm_rewrite_tac[]);
val EvalForm_MsExtend_lemma1 = save_pop_thm "EvalForm_MsExtend_lemma1";

set_goal([], ⌜∀(V, $∈⋎v) x y z⦁ V ⊆ Syntax ∧ y ∈ V ∧ z ∈ V
	   ⇒ EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, MsExtend2 (V, r) x y) z (Param_∅ y)
	     = EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) z (Param_∅ y)⌝);
a (REPEAT strip_tac);
a (fc_tac [PmrEq_MsExtend2_lemma2]);
a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜V ⊆ Syntax ∧ z ∈ V ⇒ z ∈ Syntax⌝]);
a (lemma_tac ⌜IxRan (Param_∅ y) ⊆ V⌝ THEN1 (asm_prove_tac[sets_ext_clauses]));
a (ALL_UFC_T (MAP_EVERY asm_tac) [rewrite_rule [] (list_∀_elim [⌜EvalCf_ftv⌝, ⌜$≤⋎t⋎4⌝, ⌜V⌝, ⌜V⌝,
	⌜z⌝, ⌜MsExtend2 (V, r) x y⌝, ⌜r⌝] PmrEq_EvalForm_lemma)]);
a (asm_rewrite_tac[]);
val EvalForm_MsExtend2_lemma1 = save_pop_thm "EvalForm_MsExtend2_lemma1";

set_goal([], ⌜∀(V, $∈⋎v) x y z⦁ V ⊆ Syntax ∧ x ∈ V ∧ z ∈ V
	   ⇒ EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, MsExtend (V, r) x y) z (Param_∅ x)
	     = EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) z (Param_∅ x)⌝);
a (REPEAT strip_tac);
a (fc_tac [PmrEq_MsExtend_lemma2]);
a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜V ⊆ Syntax ∧ z ∈ V ⇒ z ∈ Syntax⌝]);
a (lemma_tac ⌜IxRan (Param_∅ x) ⊆ V⌝ THEN1 (asm_prove_tac[sets_ext_clauses]));
a (ALL_UFC_T (MAP_EVERY asm_tac) [rewrite_rule [] (list_∀_elim [⌜EvalCf_ftv⌝, ⌜$≤⋎t⋎4⌝, ⌜V⌝, ⌜V⌝,
	⌜z⌝, ⌜MsExtend (V, r) x y⌝, ⌜r⌝] PmrEq_EvalForm_lemma)]);
a (asm_rewrite_tac[]);
val EvalForm_MsExtend_lemma2 = save_pop_thm "EvalForm_MsExtend_lemma2";

set_goal([], ⌜∀(V, $∈⋎v) x y z⦁ V ⊆ Syntax ∧ x ∈ V ∧ z ∈ V
	   ⇒ EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, MsExtend2 (V, r) x y) z (Param_∅ x)
	     = EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) z (Param_∅ x)⌝);
a (REPEAT strip_tac);
a (fc_tac [PmrEq_MsExtend2_lemma2]);
a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜V ⊆ Syntax ∧ z ∈ V ⇒ z ∈ Syntax⌝]);
a (lemma_tac ⌜IxRan (Param_∅ x) ⊆ V⌝ THEN1 (asm_prove_tac[sets_ext_clauses]));
a (ALL_UFC_T (MAP_EVERY asm_tac) [rewrite_rule [] (list_∀_elim [⌜EvalCf_ftv⌝, ⌜$≤⋎t⋎4⌝, ⌜V⌝, ⌜V⌝,
	⌜z⌝, ⌜MsExtend2 (V, r) x y⌝, ⌜r⌝] PmrEq_EvalForm_lemma)]);
a (asm_rewrite_tac[]);
val EvalForm_MsExtend2_lemma2 = save_pop_thm "EvalForm_MsExtend2_lemma2";

set_goal([], ⌜∀(V, $∈⋎v) x y v w⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ v ∈ V ∧ w ∈ V
	   ⇒ EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, MsExtend2 (V, r) x y) v (Param_∅ w)
	     = EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) v (Param_∅ w)⌝);
a (REPEAT strip_tac);
a (fc_tac [PmrEq_MsExtend2_lemma2]);
a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜V ⊆ Syntax ∧ z ∈ V ⇒ z ∈ Syntax⌝]);
a (lemma_tac ⌜IxRan (Param_∅ w) ⊆ V⌝ THEN1 (asm_prove_tac[sets_ext_clauses]));
a (ALL_UFC_T (MAP_EVERY asm_tac) [rewrite_rule [] (list_∀_elim [⌜EvalCf_ftv⌝, ⌜$≤⋎t⋎4⌝, ⌜V⌝, ⌜V⌝,
	⌜v⌝, ⌜MsExtend2 (V, r) x y⌝, ⌜r⌝] PmrEq_EvalForm_lemma)]);
a (asm_rewrite_tac[]);
val EvalForm_MsExtend2_lemma3 = save_pop_thm "EvalForm_MsExtend2_lemma3";
=TEX
}%ignore

=GFT
⦏Sf_MsExtend2_lemma1⦎ =
   ⊢ ∀ (V, $∈⋎v) x y z
     ⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ v ∈ V ∧ w ∈ V
         ⇒ Sf V (MsExtend2 (V, $∈⋎v) x y) v w
           = Sf V $∈⋎v v w
=TEX

\ignore{
=SML
set_goal ([], ⌜∀(V, $∈⋎v) x y v w⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ v ∈ V ∧ w ∈ V
	   ⇒ Sf V (MsExtend2 (V, $∈⋎v) x y) v w
	     = Sf V $∈⋎v v w⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜Sf⌝]);
a (fc_tac [EvalForm_MsExtend2_lemma3]);
a (list_spec_nth_asm_tac 1 [⌜x⌝, ⌜y⌝, ⌜w⌝, ⌜v⌝, ⌜$∈⋎v⌝]);
val Sf_MsExtend2_lemma1 = save_pop_thm "Sf_MsExtend2_lemma1";
=TEX
}%ignore

The following lemmas tell us some obvious facts about the value assigned to the empty set.

=GFT
⦏MsExtend2_∅⋎g_Lub_lemma1⦎ =
   ⊢ ∀ (V, r) x y z
     ⦁ V ⊆ Syntax ∧ CompExt V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V
         ⇒ MsExtend2 (V, r) x y z ∅⋎g
           = Lub $≤⋎t⋎4 {MsExtend2 (V, r) x y z x; MsExtend2 (V, r) x y z y}
=TEX

\ignore{
=SML
set_goal([], ⌜∀ (V, r) x y z⦁ V ⊆ Syntax ∧ CompExt V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V
	⇒ MsExtend2 (V, r) x y z ∅⋎g = Lub $≤⋎t⋎4 {MsExtend2 (V, r) x y z x; MsExtend2 (V, r) x y z y}⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜MsExtend2⌝, let_def, ext_thm]);
a (all_fc_tac [¬∅⋎g_∈_syntax_lemma3] THEN asm_rewrite_tac[]);
a (ALL_FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule [let_def]))) [get_spec ⌜ExtLub2⌝]);
a (POP_ASM_T ante_tac THEN rewrite_tac [pws_islub_lemma3] THEN REPEAT strip_tac);
a (SPEC_NTH_ASM_T 1 ⌜z⌝ ante_tac);
a (LEMMA_T ⌜{w|∃ g⦁ g ∈ {Extension r x; Extension r y} ∧ w = g z} = {r z x; r z y}⌝ rewrite_thm_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜Extension⌝, sets_ext_clauses, ∈_in_clauses, ext_thm]
	THEN REPEAT_N 4 strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a (∃_tac ⌜CombC r x⌝ THEN rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜CombC r y⌝ THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a (strip_tac);
a (fc_tac [lub_lub_lemma, lub_unique_lemma]);
a (strip_asm_tac (list_∀_elim [⌜{r z x; r z y}⌝, ⌜$≤⋎t⋎4⌝] lub_unique_lemma));
a (all_asm_fc_tac[]);
val MsExtend2_∅⋎g_Lub_lemma1 = save_pop_thm "MsExtend2_∅⋎g_Lub_lemma1";
=TEX
}%ignore


=GFT
⦏MsExtend2_∅⋎g_Lub_lemma2⦎ =
   ⊢ ∀ (V, r) x y z
     ⦁ V ⊆ Syntax ∧ CompExt V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V
         ⇒ MsExtend2 (V, r) x y ∅⋎g z
           = Lub $≤⋎t⋎4 {MsExtend2 (V, r) x y x z; MsExtend2 (V, r) x y y z}
=TEX

\ignore{
=SML
set_goal([], ⌜∀ (V, r) x y z⦁ V ⊆ Syntax ∧ CompEss V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V
	⇒ MsExtend2 (V, r) x y ∅⋎g z = Lub $≤⋎t⋎4 {MsExtend2 (V, r) x y x z; MsExtend2 (V, r) x y y z}⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜MsExtend2⌝, let_def, ext_thm]);
a (all_fc_tac [¬∅⋎g_∈_syntax_lemma3] THEN asm_rewrite_tac[]);
a (ALL_FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule [let_def]))) [get_spec ⌜EssLub2⌝]);
a (POP_ASM_T ante_tac THEN rewrite_tac [pws_islub_lemma3] THEN REPEAT strip_tac);
a (SPEC_NTH_ASM_T 1 ⌜z⌝ ante_tac);
a (LEMMA_T ⌜{w|∃ g⦁ g ∈ {Essence r x; Essence r y} ∧ w = g z} = {r x z; r y z}⌝ rewrite_thm_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜Essence⌝, sets_ext_clauses, ∈_in_clauses, ext_thm]
	THEN REPEAT_N 4 strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a (∃_tac ⌜r x⌝ THEN rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜r y⌝ THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a (strip_tac);
a (fc_tac [lub_lub_lemma, lub_unique_lemma]);
a (strip_asm_tac (list_∀_elim [⌜{r x z; r y z}⌝, ⌜$≤⋎t⋎4⌝] lub_unique_lemma));
a (all_asm_fc_tac[]);
val MsExtend2_∅⋎g_Lub_lemma2 = save_pop_thm "MsExtend2_∅⋎g_Lub_lemma2";
=TEX
}%ignore

=GFT
⦏MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma1⦎ =
   ⊢ ∀ (V, r) x y z
     ⦁ V ⊆ Syntax ∧ CompEss V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V
         ⇒ MsExtend2 (V, r) x y x z ≤⋎t⋎4 MsExtend2 (V, r) x y ∅⋎g z
=TEX

\ignore{
=SML
set_goal([], ⌜∀ (V, r) x y z⦁ V ⊆ Syntax ∧ CompEss V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V
	⇒ MsExtend2 (V, r) x y x z ≤⋎t⋎4 MsExtend2 (V, r) x y ∅⋎g z⌝);
a (REPEAT strip_tac THEN all_fc_tac [MsExtend2_∅⋎g_Lub_lemma2]);
a (asm_tac (rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝, ⌜{MsExtend2 (V, r) x y x z; MsExtend2 (V, r) x y y z}⌝] lub_lub_lemma2)));
a (UFC_T (MAP_EVERY (asm_tac o rewrite_rule [∈_in_clauses])) [lub_ub_lemma1]);
a (spec_nth_asm_tac 1 ⌜MsExtend2 (V, r) x y x z⌝);
a (asm_rewrite_tac[]);
val MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma1 = save_pop_thm "MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma1";
=TEX
}%ignore

=GFT
⦏MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma1b⦎ =
   ⊢ ∀ (V, r) x y z
     ⦁ V ⊆ Syntax ∧ Compatible V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V ∪ {∅⋎g}
         ⇒ MsExtend2 (V, r) x y x z ≤⋎t⋎4 MsExtend2 (V, r) x y ∅⋎g z
=TEX

\ignore{
=SML
set_goal([], ⌜∀ (V, r) x y z⦁ V ⊆ Syntax ∧ Compatible V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V ∪ {∅⋎g}
	⇒ MsExtend2 (V, r) x y x z ≤⋎t⋎4 MsExtend2 (V, r) x y ∅⋎g z⌝);
a (rewrite_tac [get_spec ⌜Compatible⌝] THEN REPEAT strip_tac THEN all_fc_tac [MsExtend2_∅⋎g_Lub_lemma2]);
(* *** Goal "1" *** *)
a (asm_tac (rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝, ⌜{MsExtend2 (V, r) x y x z; MsExtend2 (V, r) x y y z}⌝] lub_lub_lemma2)));
a (UFC_T (MAP_EVERY (asm_tac o rewrite_rule [∈_in_clauses])) [lub_ub_lemma1]);
a (spec_nth_asm_tac 1 ⌜MsExtend2 (V, r) x y x z⌝);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac [get_spec ⌜MsExtend2⌝, let_def]);
a (cond_cases_tac ⌜x = ∅⋎g⌝);
a (all_fc_tac [rewrite_rule [let_def] (get_spec ⌜ExtLub2⌝)]);
a (fc_tac [get_spec ⌜IsLub⌝]);
a (lemma_tac ⌜IsUb (PwS V $≤⋎t⋎4) {Extension r x; Extension r y} (λz⦁ Lub $≤⋎t⋎4 {r z x; r y x; r z y; r y y})⌝);
(* *** Goal "2.1" *** *)
a (rewrite_tac ((map get_spec [⌜IsUb⌝, ⌜PwS⌝])@ [∈_in_clauses]));
a (REPEAT strip_tac THEN asm_rewrite_tac [get_spec ⌜Extension⌝]);
(* *** Goal "2.1.1" *** *)
a (rewrite_tac [rewrite_rule [] (list_∀_elim [⌜r x'' x⌝, ⌜{r x'' x; r y x; r x'' y; r y y}⌝]
	(rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝] less_lub_lemma)))]);
(* *** Goal "2.1.2" *** *)
a (rewrite_tac [rewrite_rule [] (list_∀_elim [⌜r x'' y⌝, ⌜{r x'' x; r y x; r x'' y; r y y}⌝]
	(rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝] less_lub_lemma)))]);
(* *** Goal "2.2" *** *)
a (all_asm_fc_tac []);
a (POP_ASM_T discard_tac THEN POP_ASM_T ante_tac);
a (rewrite_tac [get_spec ⌜PwS⌝]);
a (REPEAT strip_tac THEN all_asm_fc_tac[]);
val MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma1b = save_pop_thm "MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma1b";
=TEX
}%ignore

=GFT
⦏MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma1⦎ =
   ⊢ ∀ (V, r) x y z
     ⦁ V ⊆ Syntax ∧ CompEss V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V
         ⇒ MsExtend2 (V, r) x y y z ≤⋎t⋎4 MsExtend2 (V, r) x y ∅⋎g z
=TEX

\ignore{
=SML
set_goal([], ⌜∀ (V, r) x y z⦁ V ⊆ Syntax ∧ CompEss V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V
	⇒ MsExtend2 (V, r) x y y z ≤⋎t⋎4 MsExtend2 (V, r) x y ∅⋎g z⌝);
a (REPEAT strip_tac THEN all_fc_tac [MsExtend2_∅⋎g_Lub_lemma2]);
a (asm_tac (rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝, ⌜{MsExtend2 (V, r) x y y z; MsExtend2 (V, r) x y x z}⌝] lub_lub_lemma2)));
a (UFC_T (MAP_EVERY (asm_tac o rewrite_rule [∈_in_clauses])) [lub_ub_lemma1]);
a (spec_nth_asm_tac 1 ⌜MsExtend2 (V, r) x y y z⌝);
a (asm_rewrite_tac[]);
a (LEMMA_T ⌜{MsExtend2 (V, r) x y x z; MsExtend2 (V, r) x y y z} = {MsExtend2 (V, r) x y y z; MsExtend2 (V, r) x y x z}⌝
	asm_rewrite_thm_tac
	THEN1 PC_T1 "hol1" prove_tac[]);
val MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma1 = save_pop_thm "MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma1";
=TEX
}%ignore

=IGN
⦏MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma1b⦎ =
   ⊢ ∀ (V, r) x y z
     ⦁ V ⊆ Syntax ∧ Compatible V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V ∪ {∅⋎g}
         ⇒ MsExtend2 (V, r) x y y z ≤⋎t⋎4 MsExtend2 (V, r) x y ∅⋎g z
=TEX

\ignore{
=IGN
set_goal([], ⌜∀ (V, r) x y z⦁ V ⊆ Syntax ∧ Compess V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V ∪ {∅⋎g}
	⇒ MsExtend2 (V, r) x y y z ≤⋎t⋎4 MsExtend2 (V, r) x y ∅⋎g z⌝);
a (REPEAT strip_tac THEN all_fc_tac [MsExtend2_∅⋎g_Lub_lemma2]);
(* *** Goal "1" *** *)
a (asm_tac (rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝, ⌜{MsExtend2 (V, r) x y x z; MsExtend2 (V, r) x y y z}⌝] lub_lub_lemma2)));
a (UFC_T (MAP_EVERY (asm_tac o rewrite_rule [∈_in_clauses])) [lub_ub_lemma1]);
a (spec_nth_asm_tac 1 ⌜MsExtend2 (V, r) x y y z⌝);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac [get_spec ⌜MsExtend2⌝, let_def]);
a (cond_cases_tac ⌜y = ∅⋎g⌝);
a (all_fc_tac [rewrite_rule [let_def] (get_spec ⌜ExtLub2⌝)]);
a (fc_tac [get_spec ⌜IsLub⌝]);
a (lemma_tac ⌜IsUb (PwS V $≤⋎t⋎4) {Extension r x; Extension r y} (λz⦁ Lub $≤⋎t⋎4 {r x x; r z x; r x y; r z y})⌝);
(* *** Goal "2.1" *** *)
a (rewrite_tac ((map get_spec [⌜IsUb⌝, ⌜PwS⌝])@ [∈_in_clauses]));
a (REPEAT strip_tac THEN asm_rewrite_tac [get_spec ⌜Extension⌝]);
(* *** Goal "2.1.1" *** *)
a (rewrite_tac [rewrite_rule [] (list_∀_elim [⌜r x'' x⌝, ⌜{r x x; r x'' x; r x y; r x'' y}⌝]
	(rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝] less_lub_lemma)))]);
(* *** Goal "2.1.2" *** *)
a (rewrite_tac [rewrite_rule [] (list_∀_elim [⌜r x'' y⌝, ⌜{r x x; r x'' x; r x y; r x'' y}⌝]
	(rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝] less_lub_lemma)))]);
(* *** Goal "2.2" *** *)
a (all_asm_fc_tac []);
a (POP_ASM_T discard_tac THEN POP_ASM_T ante_tac);
a (rewrite_tac [get_spec ⌜PwS⌝]);
a (REPEAT strip_tac THEN all_asm_fc_tac[]);
val MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma1b = save_pop_thm "MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma1b";
=TEX
}%ignore

=GFT
⦏MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma1b⦎ =
   ⊢ ∀ (V, r) x y z
     ⦁ V ⊆ Syntax ∧ Compatible V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V ∪ {∅⋎g}
         ⇒ MsExtend2 (V, r) x y y z ≤⋎t⋎4 MsExtend2 (V, r) x y ∅⋎g z
=TEX

\ignore{
=SML
set_goal([], ⌜∀ (V, r) x y z⦁ V ⊆ Syntax ∧ Compatible V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V ∪ {∅⋎g}
	⇒ MsExtend2 (V, r) x y y z ≤⋎t⋎4 MsExtend2 (V, r) x y ∅⋎g z⌝);
a (rewrite_tac [get_spec ⌜Compatible⌝] THEN REPEAT strip_tac THEN all_fc_tac [MsExtend2_∅⋎g_Lub_lemma2]);
(* *** Goal "1" *** *)
a (asm_tac (rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝, ⌜{MsExtend2 (V, r) x y x z; MsExtend2 (V, r) x y y z}⌝] lub_lub_lemma2)));
a (UFC_T (MAP_EVERY (asm_tac o rewrite_rule [∈_in_clauses])) [lub_ub_lemma1]);
a (spec_nth_asm_tac 1 ⌜MsExtend2 (V, r) x y y z⌝);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac [get_spec ⌜MsExtend2⌝, let_def]);
a (cond_cases_tac ⌜y = ∅⋎g⌝);
a (all_fc_tac [rewrite_rule [let_def] (get_spec ⌜ExtLub2⌝)]);
a (fc_tac [get_spec ⌜IsLub⌝]);
a (lemma_tac ⌜IsUb (PwS V $≤⋎t⋎4) {Extension r x; Extension r y} (λz⦁ Lub $≤⋎t⋎4 {r x x; r z x; r x y; r z y})⌝);
(* *** Goal "2.1" *** *)
a (rewrite_tac ((map get_spec [⌜IsUb⌝, ⌜PwS⌝])@ [∈_in_clauses]));
a (REPEAT strip_tac THEN asm_rewrite_tac [get_spec ⌜Extension⌝]);
(* *** Goal "2.1.1" *** *)
a (rewrite_tac [rewrite_rule [] (list_∀_elim [⌜r x'' x⌝, ⌜{r x x; r x'' x; r x y; r x'' y}⌝]
	(rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝] less_lub_lemma)))]);
(* *** Goal "2.1.2" *** *)
a (rewrite_tac [rewrite_rule [] (list_∀_elim [⌜r x'' y⌝, ⌜{r x x; r x'' x; r x y; r x'' y}⌝]
	(rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝] less_lub_lemma)))]);
(* *** Goal "2.2" *** *)
a (all_asm_fc_tac []);
a (POP_ASM_T discard_tac THEN POP_ASM_T ante_tac);
a (rewrite_tac [get_spec ⌜PwS⌝]);
a (REPEAT strip_tac THEN all_asm_fc_tac[]);
val MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma1b = save_pop_thm "MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma1b";
=TEX
}%ignore

=GFT
⦏MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma2⦎ =
   ⊢ ∀ (V, r) x y z
     ⦁ V ⊆ Syntax ∧ CompExt V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V
         ⇒ MsExtend2 (V, r) x y z x ≤⋎t⋎4 MsExtend2 (V, r) x y z ∅⋎g
=TEX

\ignore{
=SML
set_goal([], ⌜∀ (V, r) x y z⦁ V ⊆ Syntax ∧ CompExt V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V
	⇒ MsExtend2 (V, r) x y z x ≤⋎t⋎4 MsExtend2 (V, r) x y z ∅⋎g⌝);
a (REPEAT strip_tac THEN all_fc_tac [MsExtend2_∅⋎g_Lub_lemma1]);
a (asm_tac (rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝, ⌜{MsExtend2 (V, r) x y z x; MsExtend2 (V, r) x y z y}⌝] lub_lub_lemma2)));
a (UFC_T (MAP_EVERY (asm_tac o rewrite_rule [∈_in_clauses])) [lub_ub_lemma1]);
a (spec_nth_asm_tac 1 ⌜MsExtend2 (V, r) x y z x⌝);
a (asm_rewrite_tac[]);
val MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma2 = save_pop_thm "MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma2";
=TEX
}%ignore

=GFT
⦏MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma2⦎ =
   ⊢ ∀ (V, r) x y z
     ⦁ V ⊆ Syntax ∧ CompExt V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V
         ⇒ MsExtend2 (V, r) x y z y ≤⋎t⋎4 MsExtend2 (V, r) x y z ∅⋎g
=TEX

\ignore{
=SML
set_goal([], ⌜∀ (V, r) x y z⦁ V ⊆ Syntax ∧ CompExt V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V
	⇒ MsExtend2 (V, r) x y z y ≤⋎t⋎4 MsExtend2 (V, r) x y z ∅⋎g⌝);
a (REPEAT strip_tac THEN all_fc_tac [MsExtend2_∅⋎g_Lub_lemma1]);
a (asm_tac (rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝, ⌜{MsExtend2 (V, r) x y z x; MsExtend2 (V, r) x y z y}⌝] lub_lub_lemma2)));
a (UFC_T (MAP_EVERY (asm_tac o rewrite_rule [∈_in_clauses])) [lub_ub_lemma1]);
a (spec_nth_asm_tac 1 ⌜MsExtend2 (V, r) x y z y⌝);
a (asm_rewrite_tac[]);
val MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma2 = save_pop_thm "MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma2";
=TEX
}%ignore

=GFT
⦏MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma2b⦎ =
   ⊢ ∀ (V, r) x y z
     ⦁ V ⊆ Syntax
           ∧ CompEss V r x y
           ∧ CompExt V r x y
           ∧ x ∈ V
           ∧ y ∈ V
           ∧ z ∈ V ∪ {∅⋎g}
         ⇒ MsExtend2 (V, r) x y z x ≤⋎t⋎4 MsExtend2 (V, r) x y z ∅⋎g
=TEX

\ignore{
=SML
set_goal([], ⌜∀ (V, r) x y z⦁ V ⊆ Syntax ∧ CompEss V r x y ∧ CompExt V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V ∪ {∅⋎g}
	⇒ MsExtend2 (V, r) x y z x ≤⋎t⋎4 MsExtend2 (V, r) x y z ∅⋎g⌝);
a (REPEAT strip_tac THEN all_fc_tac [MsExtend2_∅⋎g_Lub_lemma1]);
(* *** Goal "1" *** *)
a (asm_tac (rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝, ⌜{MsExtend2 (V, r) x y z x; MsExtend2 (V, r) x y z y}⌝] lub_lub_lemma2)));
a (UFC_T (MAP_EVERY (asm_tac o rewrite_rule [∈_in_clauses])) [lub_ub_lemma1]);
a (spec_nth_asm_tac 1 ⌜MsExtend2 (V, r) x y z x⌝);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[get_spec ⌜MsExtend2⌝, let_def]);
a (cond_cases_tac ⌜x = ∅⋎g⌝);
a (ALL_FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule [let_def]))) [get_spec ⌜EssLub2⌝]);
a (fc_tac [get_spec ⌜IsLub⌝]);
a (lemma_tac ⌜IsUb (PwS V $≤⋎t⋎4) {Essence r x; Essence r y} (λz⦁ Lub $≤⋎t⋎4 {r x z; r y z; r x y; r y y})⌝);
(* *** Goal "2.1" *** *)
a (rewrite_tac ((map get_spec [⌜IsUb⌝, ⌜PwS⌝])@ [∈_in_clauses]));
a (REPEAT strip_tac THEN asm_rewrite_tac [get_spec ⌜Essence⌝]);
(* *** Goal "2.1.1" *** *)
a (rewrite_tac [rewrite_rule [] (list_∀_elim [⌜r x x''⌝, ⌜{r x x''; r y x''; r x y; r y y}⌝]
	(rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝] less_lub_lemma)))]);
(* *** Goal "2.1.2" *** *)
a (rewrite_tac [rewrite_rule [] (list_∀_elim [⌜r y x''⌝, ⌜{r x x''; r y x''; r x y; r y y}⌝]
	(rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝] less_lub_lemma)))]);
(* *** Goal "2.2" *** *)
a (all_asm_fc_tac []);
a (POP_ASM_T discard_tac THEN POP_ASM_T ante_tac);
a (rewrite_tac [get_spec ⌜PwS⌝]);
a (REPEAT strip_tac THEN all_asm_fc_tac[]);
val MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma2b = save_pop_thm "MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma2b";
=TEX
}%ignore

=GFT
⦏MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma2b⦎ =
   ⊢ ∀ (V, r) x y z
     ⦁ V ⊆ Syntax
           ∧ CompEss V r x y
           ∧ CompExt V r x y
           ∧ x ∈ V
           ∧ y ∈ V
           ∧ z ∈ V ∪ {∅⋎g}
         ⇒ MsExtend2 (V, r) x y z y ≤⋎t⋎4 MsExtend2 (V, r) x y z ∅⋎g
=TEX

\ignore{
=SML
set_goal([], ⌜∀ (V, r) x y z⦁ V ⊆ Syntax ∧ CompEss V r x y ∧ CompExt V r x y ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V ∪ {∅⋎g}
	⇒ MsExtend2 (V, r) x y z y ≤⋎t⋎4 MsExtend2 (V, r) x y z ∅⋎g⌝);
a (REPEAT strip_tac THEN all_fc_tac [MsExtend2_∅⋎g_Lub_lemma1]);
(* *** Goal "1" *** *)
a (asm_tac (rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝, ⌜{MsExtend2 (V, r) x y z x; MsExtend2 (V, r) x y z y}⌝] lub_lub_lemma2)));
a (UFC_T (MAP_EVERY (asm_tac o rewrite_rule [∈_in_clauses])) [lub_ub_lemma1]);
a (spec_nth_asm_tac 1 ⌜MsExtend2 (V, r) x y z y⌝);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[get_spec ⌜MsExtend2⌝, let_def]);
a (cond_cases_tac ⌜y = ∅⋎g⌝);
a (ALL_FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule [let_def]))) [get_spec ⌜EssLub2⌝]);
a (fc_tac [get_spec ⌜IsLub⌝]);
a (lemma_tac ⌜IsUb (PwS V $≤⋎t⋎4) {Essence r x; Essence r y} (λz⦁ Lub $≤⋎t⋎4 {r x x; r y x; r x z; r y z})⌝);
(* *** Goal "2.1" *** *)
a (rewrite_tac ((map get_spec [⌜IsUb⌝, ⌜PwS⌝])@ [∈_in_clauses]));
a (REPEAT strip_tac THEN asm_rewrite_tac [get_spec ⌜Essence⌝]);
(* *** Goal "2.1.1" *** *)
a (rewrite_tac [rewrite_rule [] (list_∀_elim [⌜r x x''⌝, ⌜{r x x; r y x; r x x''; r y x''}⌝]
	(rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝] less_lub_lemma)))]);
(* *** Goal "2.1.2" *** *)
a (rewrite_tac [rewrite_rule [] (list_∀_elim [⌜r y x''⌝, ⌜{r x x; r y x; r x x''; r y x''}⌝]
	(rewrite_rule [] (list_∀_elim [⌜$≤⋎t⋎4⌝] less_lub_lemma)))]);
(* *** Goal "2.2" *** *)
a (all_asm_fc_tac []);
a (POP_ASM_T discard_tac THEN POP_ASM_T ante_tac);
a (rewrite_tac [get_spec ⌜PwS⌝]);
a (REPEAT strip_tac THEN all_asm_fc_tac[]);
val MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma2b = save_pop_thm "MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma2b";
=TEX
}%ignore

The extended structure is not anywhere overdefined.
Lemma4 subsumes all the others but was not true for my first definition of the extension, which is why I proved the earlier more restricted results.

=GFT
⦏MsExtend_¬OverDefined_lemma⦎ =
   ⊢ ∀ (V, $∈⋎v) x y
     ⦁ V ⊆ Syntax
           ∧ ¬ OverDefined V $∈⋎v
           ∧ CompEss V $∈⋎v x y
           ∧ CompExt V $∈⋎v x y
         ⇒ ¬ OverDefined V (MsExtend (V, $∈⋎v) x y)
=TEX

=GFT
⦏MsExtend2_¬OverDefined_lemma⦎ =
   ⊢ ∀ (V, $∈⋎v) x y
     ⦁ V ⊆ Syntax
           ∧ ¬ OverDefined V $∈⋎v
           ∧ CompEss V $∈⋎v x y
           ∧ CompExt V $∈⋎v x y
         ⇒ ¬ OverDefined V (MsExtend2 (V, $∈⋎v) x y)
=TEX

=GFT
⦏MsExtend_¬OverDefined_lemma2⦎ =
   ⊢ ∀ (V, $∈⋎v) x y
     ⦁ V ⊆ SetReps
           ∧ x ∈ V
           ∧ y ∈ V
           ∧ ¬ OverDefined V $∈⋎v
           ∧ CompEss V $∈⋎v x y
           ∧ CompExt V $∈⋎v x y
         ⇒ (∀ v⦁ v ∈ V ⇒ ¬ MsExtend (V, $∈⋎v) x y v ∅⋎g = fT)
=TEX

=GFT
⦏MsExtend2_¬OverDefined_lemma2⦎ =
   ⊢ ∀ (V, $∈⋎v) x y
     ⦁ V ⊆ SetReps
           ∧ x ∈ V
           ∧ y ∈ V
           ∧ ¬ OverDefined V $∈⋎v
           ∧ CompEss V $∈⋎v x y
           ∧ CompExt V $∈⋎v x y
         ⇒ (∀ v⦁ v ∈ V ⇒ ¬ MsExtend2 (V, $∈⋎v) x y v ∅⋎g = fT)
=TEX

=GFT
⦏MsExtend2_¬OverDefined_lemma2⦎ =
   ⊢ ∀ (V, $∈⋎v) x y
     ⦁ V ⊆ Syntax
           ∧ x ∈ V
           ∧ y ∈ V
           ∧ ¬ OverDefined V $∈⋎v
           ∧ CompEss V $∈⋎v x y
           ∧ CompExt V $∈⋎v x y
         ⇒ (∀ v⦁ v ∈ V ⇒ ¬ MsExtend2 (V, $∈⋎v) x y v ∅⋎g = fT)
=TEX

=GFT
⦏MsExtend_¬OverDefined_lemma3⦎ =
   ⊢ ∀ (V, $∈⋎v) x y
     ⦁ V ⊆ SetReps
           ∧ x ∈ V
           ∧ y ∈ V
           ∧ ¬ OverDefined V $∈⋎v
           ∧ CompEss V $∈⋎v x y
           ∧ CompExt V $∈⋎v x y
         ⇒ (∀ v⦁ v ∈ V ⇒ ¬ MsExtend (V, $∈⋎v) x y ∅⋎g v = fT)
=TEX

=GFT
⦏MsExtend2_¬OverDefined_lemma3⦎ =
   ⊢ ∀ (V, $∈⋎v) x y
     ⦁ V ⊆ Syntax
           ∧ x ∈ V
           ∧ y ∈ V
           ∧ ¬ OverDefined V $∈⋎v
           ∧ CompEss V $∈⋎v x y
           ∧ CompExt V $∈⋎v x y
         ⇒ (∀ v⦁ v ∈ V ⇒ ¬ MsExtend2 (V, $∈⋎v) x y ∅⋎g v = fT)
=TEX

=GFT
⦏MsExtend_¬OverDefined_lemma4⦎ =
   ⊢ ∀ (V, $∈⋎v) x y
     ⦁ V ⊆ SetReps
           ∧ x ∈ V
           ∧ y ∈ V
           ∧ ¬ OverDefined V $∈⋎v
           ∧ Compatible V $∈⋎v x y
         ⇒ ¬ OverDefined (V ∪ {∅⋎g}) (MsExtend (V, $∈⋎v) x y)
=TEX

=GFT
⦏MsExtend2_¬OverDefined_lemma4⦎ =
   ⊢ ∀ (V, $∈⋎v) x y
     ⦁ V ⊆ Syntax
           ∧ x ∈ V
           ∧ y ∈ V
           ∧ ¬ OverDefined V $∈⋎v
           ∧ Compatible V $∈⋎v x y
         ⇒ ¬ OverDefined (V ∪ {∅⋎g}) (MsExtend2 (V, $∈⋎v) x y)
=TEX

\ignore{
=SML
set_goal([], ⌜∀(V, $∈⋎v) x y⦁ V ⊆ Syntax ∧ ¬ OverDefined V $∈⋎v ∧ CompEss V $∈⋎v x y ∧ CompExt V $∈⋎v x y
	⇒ ¬ OverDefined V (MsExtend (V, $∈⋎v) x y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜MsExtend⌝, get_spec ⌜OverDefined⌝, let_def]
	THEN REPEAT strip_tac
	THEN swap_nth_asm_concl_tac 1);
a (ALL_FC_T rewrite_tac [¬∅⋎g_∈_syntax_lemma3]);
a (spec_nth_asm_tac 5 ⌜x'⌝);
a (spec_nth_asm_tac 1 ⌜y'⌝);
val MsExtend_¬OverDefined_lemma = save_pop_thm "MsExtend_¬OverDefined_lemma";

set_goal([], ⌜∀(V, $∈⋎v) x y⦁ V ⊆ Syntax ∧ ¬ OverDefined V $∈⋎v ∧ CompEss V $∈⋎v x y ∧ CompExt V $∈⋎v x y
	⇒ ¬ OverDefined V (MsExtend2 (V, $∈⋎v) x y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜MsExtend2⌝, get_spec ⌜OverDefined⌝, let_def]
	THEN REPEAT strip_tac
	THEN swap_nth_asm_concl_tac 1);
a (ALL_FC_T rewrite_tac [¬∅⋎g_∈_syntax_lemma3]);
a (spec_nth_asm_tac 5 ⌜x'⌝);
a (spec_nth_asm_tac 1 ⌜y'⌝);
val MsExtend2_¬OverDefined_lemma = save_pop_thm "MsExtend2_¬OverDefined_lemma";

set_goal([], ⌜∀(V, $∈⋎v) x y⦁ V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V ∧ ¬ OverDefined V $∈⋎v ∧ CompEss V $∈⋎v x y ∧ CompExt V $∈⋎v x y
	⇒ ∀v⦁ v ∈ V ⇒ ¬ (MsExtend (V, $∈⋎v) x y) v ∅⋎g = fT⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜MsExtend⌝, let_def]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜V ⊆ Syntax⌝
	THEN1 (asm_tac setreps_⊆_syntax_lemma THEN all_fc_tac [⊆_trans_thm]));
a (lemma_tac ⌜¬ v = ∅⋎g⌝ THEN1 fc_tac [¬∅⋎g_∈_syntax_lemma3]
	THEN asm_rewrite_tac[]);
a (ALL_FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule [let_def]))) [get_spec ⌜ExtUb⌝]);
a (swap_nth_asm_concl_tac 2 THEN asm_rewrite_tac [get_spec ⌜OverDefinedL⌝ ]); 
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
val MsExtend_¬OverDefined_lemma2 = save_pop_thm "MsExtend_¬OverDefined_lemma2";

set_goal([], ⌜∀(V, $∈⋎v) x y⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ ¬ OverDefined V $∈⋎v ∧ CompEss V $∈⋎v x y ∧ CompExt V $∈⋎v x y
	⇒ ∀v⦁ v ∈ V ⇒ ¬ (MsExtend2 (V, $∈⋎v) x y) v ∅⋎g = fT⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜MsExtend2⌝, let_def]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜¬ v = ∅⋎g⌝ THEN1 fc_tac [¬∅⋎g_∈_syntax_lemma3]
	THEN asm_rewrite_tac[]);
a (ALL_FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule [let_def]))) [get_spec ⌜ExtLub2⌝]);
a (swap_nth_asm_concl_tac 2 THEN asm_rewrite_tac [get_spec ⌜OverDefinedL⌝ ]); 
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
val MsExtend2_¬OverDefined_lemma2 = save_pop_thm "MsExtend2_¬OverDefined_lemma2";

set_goal([], ⌜∀(V, $∈⋎v) x y⦁ V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V
	∧ ¬ OverDefined V $∈⋎v ∧ CompEss V $∈⋎v x y ∧ CompExt V $∈⋎v x y
	⇒ ∀v⦁ v ∈ V ⇒ ¬ (MsExtend (V, $∈⋎v) x y) ∅⋎g v = fT⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜MsExtend⌝, let_def]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜V ⊆ Syntax⌝
	THEN1 (asm_tac setreps_⊆_syntax_lemma THEN all_fc_tac [⊆_trans_thm]));
a (lemma_tac ⌜¬ v = ∅⋎g⌝ THEN1 fc_tac [¬∅⋎g_∈_syntax_lemma3]
	THEN asm_rewrite_tac[]);
a (ALL_FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule [let_def]))) [get_spec ⌜EssUb⌝]);
a (swap_nth_asm_concl_tac 2 THEN asm_rewrite_tac [get_spec ⌜OverDefinedL⌝ ]); 
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
val MsExtend_¬OverDefined_lemma3 = save_pop_thm "MsExtend_¬OverDefined_lemma3";

set_goal([], ⌜∀(V, $∈⋎v) x y⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V
	∧ ¬ OverDefined V $∈⋎v ∧ CompEss V $∈⋎v x y ∧ CompExt V $∈⋎v x y
	⇒ ∀v⦁ v ∈ V ⇒ ¬ (MsExtend2 (V, $∈⋎v) x y) ∅⋎g v = fT⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜MsExtend2⌝, let_def]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜¬ v = ∅⋎g⌝ THEN1 fc_tac [¬∅⋎g_∈_syntax_lemma3]
	THEN asm_rewrite_tac[]);
a (ALL_FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule [let_def]))) [get_spec ⌜EssLub2⌝]);
a (swap_nth_asm_concl_tac 2 THEN asm_rewrite_tac [get_spec ⌜OverDefinedL⌝ ]); 
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
val MsExtend2_¬OverDefined_lemma3 = save_pop_thm "MsExtend2_¬OverDefined_lemma3";

set_goal([], ⌜∀(V, $∈⋎v) x y⦁ V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V
	∧ ¬ OverDefined V $∈⋎v ∧ Compatible V $∈⋎v x y
	⇒ ¬ OverDefined (V ∪ {∅⋎g}) (MsExtend (V, $∈⋎v) x y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜Compatible⌝, get_spec ⌜MsExtend⌝, let_def]
	THEN REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜OverDefined⌝]
	THEN REPEAT_N 4 strip_tac);
a (cond_cases_tac ⌜x' = ∅⋎g⌝ THEN cond_cases_tac ⌜y' = ∅⋎g⌝);
(* *** Goal "1" *** *)
a (LEMMA_T ⌜{x ∈⋎v x; y ∈⋎v x; x ∈⋎v y; y ∈⋎v y} = {x ∈⋎v y; y ∈⋎v x; x ∈⋎v x; y ∈⋎v y}⌝ asm_rewrite_thm_tac
	THEN1 PC_T1 "hol1" prove_tac []);
(* *** Goal "2" *** *)
a (ALL_FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule [let_def]))) [get_spec ⌜EssUb⌝]);
a (GET_NTH_ASM_T 2 ante_tac THEN rewrite_tac [get_spec ⌜OverDefinedL⌝]
	THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜y'⌝ THEN asm_rewrite_tac [∈_in_clauses]);
(* *** Goal "3" *** *)
a (ALL_FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule [let_def]))) [get_spec ⌜ExtUb⌝]);
a (GET_NTH_ASM_T 2 ante_tac THEN rewrite_tac [get_spec ⌜OverDefinedL⌝]
	THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜x'⌝ THEN asm_rewrite_tac [∈_in_clauses]);
(* *** Goal "4" *** *)
a (GET_NTH_ASM_T 6 ante_tac THEN rewrite_tac [get_spec ⌜OverDefined⌝]
	THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜x'⌝);
a (spec_nth_asm_tac 1 ⌜y'⌝ THEN_TRY asm_rewrite_tac [∈_in_clauses]);
val MsExtend_¬OverDefined_lemma4 = save_pop_thm "MsExtend_¬OverDefined_lemma4";

set_goal([], ⌜∀(V, $∈⋎v) x y⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V
	∧ ¬ OverDefined V $∈⋎v ∧ Compatible V $∈⋎v x y
	⇒ ¬ OverDefined (V ∪ {∅⋎g}) (MsExtend2 (V, $∈⋎v) x y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜Compatible⌝, get_spec ⌜MsExtend2⌝, let_def]
	THEN REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜OverDefined⌝]
	THEN REPEAT_N 4 strip_tac);
a (cond_cases_tac ⌜x' = ∅⋎g⌝ THEN cond_cases_tac ⌜y' = ∅⋎g⌝);
(* *** Goal "1" *** *)
a (LEMMA_T ⌜{x ∈⋎v x; y ∈⋎v x; x ∈⋎v y; y ∈⋎v y} = {x ∈⋎v y; y ∈⋎v x; x ∈⋎v x; y ∈⋎v y}⌝ asm_rewrite_thm_tac
	THEN1 PC_T1 "hol1" prove_tac []);
(* *** Goal "2" *** *)
a (ALL_FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule [let_def]))) [get_spec ⌜EssLub2⌝]);
a (GET_NTH_ASM_T 2 ante_tac THEN rewrite_tac [get_spec ⌜OverDefinedL⌝]
	THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜y'⌝ THEN asm_rewrite_tac [∈_in_clauses]);
(* *** Goal "3" *** *)
a (ALL_FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule [let_def]))) [get_spec ⌜ExtLub2⌝]);
a (GET_NTH_ASM_T 2 ante_tac THEN rewrite_tac [get_spec ⌜OverDefinedL⌝]
	THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜x'⌝ THEN asm_rewrite_tac [∈_in_clauses]);
(* *** Goal "4" *** *)
a (GET_NTH_ASM_T 6 ante_tac THEN rewrite_tac [get_spec ⌜OverDefined⌝]
	THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜x'⌝);
a (spec_nth_asm_tac 1 ⌜y'⌝ THEN_TRY asm_rewrite_tac [∈_in_clauses]);
val MsExtend2_¬OverDefined_lemma4 = save_pop_thm "MsExtend2_¬OverDefined_lemma4";
=IGN
set_flag ("subgoal_package_quiet", false);

=TEX
}%ignore

=GFT

=TEX

\ignore{
=IGN
set_flag ("subgoal_package_quiet", false);

set_goal([], ⌜∀ V x y z⦁ V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V ∧ Compatible V r x y
              ⇒ ExsSRO (V ∪ {∅⋎g}, MsExtend2 (V, r) x y) x ∅⋎g⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜ExsVaO⌝, get_spec ⌜IxO2⌝, get_spec ⌜V2IxSet⌝, get_spec ⌜ExsSRO⌝, get_spec ⌜MsExtend2⌝]
	THEN REPEAT strip_tac);
a (rewrite_tac [get_spec ⌜Compatible⌝, get_spec ⌜ExsVaO⌝, get_spec ⌜ConjOrder⌝, get_spec ⌜ExtSRO⌝,
			get_spec ⌜EssSRO⌝, get_spec ⌜IxO⌝, get_spec ⌜Pw⌝, get_spec ⌜OptO⌝, let_def]);
a (rewrite_tac [∀_∧_out_lemma] THEN strip_tac);
a (COND_CASES_T ⌜x' ∈ V ∪ {∅⋎g}⌝ asm_tac);
a (fc_tac [rewrite_rule [ext_thm] (get_spec ⌜Compatible⌝)]);
a (cond_cases_tac ⌜x' = ∅⋎g⌝ THEN cond_cases_tac ⌜x = ∅⋎g⌝ THEN strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [get_spec ⌜EssUb⌝]); 
a (rewrite_tac[get_spec ⌜EssUb⌝]); 
a (step_strip_tac);


set_goal([], ⌜∀ V x y z⦁ V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V ∧ Compatible V r x y
              ⇒ ExsVaO (V2IxSet (V ∪ {∅⋎g}), V ∪ {∅⋎g}, MsExtend (V, r) x y) (Param_∅ x) (Param_∅ ∅⋎g)⌝);

a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜ExsVaO⌝, get_spec ⌜IxO2⌝, get_spec ⌜V2IxSet⌝, get_spec ⌜ExsSRO⌝, get_spec ⌜MsExtend⌝]
	THEN REPEAT strip_tac);

a (rewrite_tac [get_spec ⌜Compatible⌝, get_spec ⌜ExsVaO⌝, get_spec ⌜ConjOrder⌝, get_spec ⌜ExtSRO⌝,
			get_spec ⌜EssSRO⌝, get_spec ⌜IxO⌝, get_spec ⌜Pw⌝, get_spec ⌜OptO⌝, let_def]);
a (rewrite_tac [prove_rule [] ⌜∀p q⦁ $∀ p ∧ $∀ q ⇔ $∀ λx⦁ p x ∧ q x⌝]):

pc_rule1 "hol1" prove_rule [] ⌜∀p q:'a → BOOL⦁ $∀ p ∧ $∀ q ⇔ $∀ λx⦁ p x ∧ q x⌝;




		get_spec ⌜Compatible⌝, get_spec ⌜ExsVaO⌝, get_spec ⌜IxO2⌝, get_spec ⌜IxO⌝, get_spec ⌜Pw⌝,
		get_spec ⌜V2IxSet⌝, get_spec ⌜ExsSRO⌝, get_spec ⌜MsExtend⌝, get_spec ⌜OptO⌝, get_spec ⌜ConjOrder⌝

=TEX
}%ignore


\subsubsection{Strictness-like Properties}

A function is strict if is maps bottom to bottom.

A weaker notion we call ``weak strictness'' and name {\it WkStrict} which is the property of preserving ``UnderDefined''ness.
This is formulated for semantic functors.

ⓈHOLCONST
│ ⦏WkStrict⦎ : GS SET → (GS SET → (GS, FTV)BR → (GS, FTV)BR) → BOOL
├───────────
│ ∀V f⦁ WkStrict V f ⇔ ∀r⦁ UnderDefined V r ⇒ UnderDefined V (f V r)
■

The dual concept is:

ⓈHOLCONST
│ ⦏CoWkStrict⦎ : GS SET → (GS SET → (GS, FTV)BR → (GS, FTV)BR) → BOOL
├───────────
│ ∀V f⦁ CoWkStrict V f ⇔ ∀r⦁ OverDefined V r ⇒ OverDefined V (f V r)
■

Their "converses" are:

ⓈHOLCONST
│ ⦏ConWkStrict⦎ : GS SET → (GS SET → (GS, FTV)BR → (GS, FTV)BR) → BOOL
├───────────
│ ∀V f⦁ ConWkStrict V f ⇔ ∀r⦁ UnderDefined V (f V r) ⇒ UnderDefined V r
■

=GFT
⦏ConWkStrictSf_lemma⦎ =
   ⊢ ∀ V⦁ V ⊆ SetReps ⇒ ConWkStrict V Sf
=TEX

\ignore{
=SML
set_goal ([], ⌜∀V⦁ V ⊆ SetReps ⇒ ConWkStrict V Sf⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜ConWkStrict⌝, get_spec ⌜Sf⌝,  get_spec ⌜UnderDefined⌝]);
a (PC_T "hol1" (REPEAT strip_tac) THEN POP_ASM_T ante_tac);
a (asm_fc_tac[]);
a (DROP_NTH_ASM_T 3 discard_tac);
a (DROP_NTH_ASM_T 2 discard_tac);
a (lemma_tac ⌜IxRan (Param_∅ x) ⊆ V⌝
	THEN1 (rewrite_tac[sets_ext_clauses] THEN strip_tac THEN strip_tac
	THEN var_elim_nth_asm_tac 1));
a (DROP_NTH_ASM_T 3 ante_tac);
a (lemma_tac ⌜FreeVars y = {∅⋎g}⌝
	THEN1 (GET_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [get_spec ⌜SetReps⌝]))));
a (lemma_tac ⌜FreeVars y ⊆ IxDom (Param_∅ x)⌝
	THEN1 (asm_rewrite_tac [ixdom_param_∅_lemma]));
a (LEMMA_T ⌜∀v⦁ IxRan v ⊆ V ∧ FreeVars y ⊆ IxDom v
             ⇒ EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) y v = fB
             ⇒ (∃ x y⦁ x ∈ V ∧ y ∈ V ∧ r x y = fB)⌝
	(rewrite_thm_tac
		o (rewrite_rule [asm_rule ⌜IxRan (Param_∅ x) ⊆ V⌝, asm_rule ⌜FreeVars y ⊆ IxDom (Param_∅ x)⌝])
		o (∀_elim ⌜Param_∅ x⌝)));
a (DROP_ASM_T ⌜y ∈ SetReps⌝ (strip_asm_tac o (rewrite_rule [get_spec ⌜SetReps⌝])));
a (POP_ASM_T ante_tac);
a (REPEAT_N 3 (POP_ASM_T discard_tac) THEN sc_induction_tac ⌜y⌝);
a (REPEAT_N 3 strip_tac THEN asm_rewrite_tac[evalformfunct_thm2]);
a (cases_tac ⌜IsAf t⌝ THEN asm_rewrite_tac[let_def]);
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜EvalAf⌝, let_def]);
a (cond_cases_tac ⌜AfMem t ∈ IxDom v ∧ AfSet t ∈ IxDom v⌝);
(* *** Goal "1.1" *** *)
a (all_fc_tac [ix_domran_lemma]);
a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜∀x y z⦁ x ∈ y ∧ y ⊆ z ⇒ x ∈ z⌝]);
a (strip_tac THEN ∃_tac ⌜IxVal v (AfMem t)⌝ THEN ∃_tac ⌜IxVal v (AfSet t)⌝ THEN asm_rewrite_tac []);
(* *** Goal "1.2" *** *)
a (GET_ASM_T ⌜FreeVars t ⊆ IxDom v⌝ (strip_asm_tac o (rewrite_rule
	[freevarsfunct_thm2, asm_rule ⌜t ∈ Syntax⌝, asm_rule ⌜IsAf t⌝, get_spec ⌜$⊆⌝, ∈_in_clauses])));
a (spec_nth_asm_tac 1 ⌜AfMem t⌝);
(* *** Goal "1.3" *** *)
a (GET_ASM_T ⌜FreeVars t ⊆ IxDom v⌝ (strip_asm_tac o (rewrite_rule
	[freevarsfunct_thm2, asm_rule ⌜t ∈ Syntax⌝, asm_rule ⌜IsAf t⌝, get_spec ⌜$⊆⌝, ∈_in_clauses])));
a (spec_nth_asm_tac 1 ⌜AfSet t⌝);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜EvalCf⌝, let_def, evalcf_ftv_fb_lemma] THEN strip_tac);
a (DROP_NTH_ASM_T 4 ante_tac THEN rewrite_tac [get_spec ⌜FunImage⌝] THEN strip_tac);
a (lemma_tac ⌜tc ScPrec a t ∧ a ∈ Syntax⌝ THEN1 REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (bc_tac [tc_incr_thm]);
a (DROP_NTH_ASM_T 2 (asm_tac o (rewrite_rule [get_spec ⌜X⋎g⌝])));
a (lemma_tac ⌜IsCf t⌝ THEN1 fc_tac[syntax_cases_thm]);
a (all_asm_fc_tac [scprec_fc_clauses2]);
(* *** Goal "2.2" *** *)
a (lemma_tac ⌜IsCf t⌝ THEN1 fc_tac[syntax_cases_thm]);
a (FC_T (MAP_EVERY (strip_asm_tac o (try (rewrite_rule [asm_rule ⌜IsCf t⌝, asm_rule ⌜¬ IsAf t⌝])))) [∀_elim ⌜t⌝ is_fc_clauses]);
a (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[get_spec ⌜X⋎g⌝] THEN strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.3" *** *)
a (DROP_NTH_ASM_T 5 (ante_tac o eq_sym_rule));
a (GET_NTH_ASM_T 3 (rewrite_thm_tac o eq_sym_rule) THEN strip_tac);
a (list_spec_nth_asm_tac 14 [⌜a⌝]);
a (lemma_tac ⌜IxRan (IxOverRide v v') ⊆ V⌝);
(* *** Goal "2.3.1" *** *)
a (lemma_tac ⌜IxRan (IxOverRide v v') ⊆ IxRan v ∪ IxRan v'⌝ 
	THEN1 (rewrite_tac [ixoverride_ixran_lemma]));
a (lemma_tac ⌜IxRan v ∪ IxRan v' ⊆ V⌝
	THEN1 (asm_rewrite_tac [
		pc_rule1 "hol1" prove_rule [] ⌜∀A B C⦁ A ∪ B ⊆ C ⇔ A ⊆ C ∧ B ⊆ C⌝]));
a (all_asm_fc_tac [⊆_trans_thm]);
(* *** Goal "2.3.2" *** *)
a (lemma_tac ⌜FreeVars a ⊆ IxDom (IxOverRide v v')⌝
	THEN1 (rewrite_tac [ixoverride_ixdom_lemma, sets_ext_clauses, ∈_in_clauses]
		THEN REPEAT_N 2 strip_tac));
(* *** Goal "2.3.2.1" *** *)
a (GET_ASM_T ⌜FreeVars t ⊆ IxDom v⌝ (strip_asm_tac o (rewrite_rule
	[freevarsfunct_thm2, asm_rule ⌜t ∈ Syntax⌝, asm_rule ⌜¬ IsAf t⌝, sets_ext_clauses, ∈_in_clauses]))); 
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "2.3.2.1.1" *** *)
a (spec_nth_asm_tac 1 ⌜FreeVars a⌝
	THEN POP_ASM_T ante_tac
	THEN asm_rewrite_tac[get_spec ⌜FunImage⋎g⌝]
	THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜a⌝);
a (DROP_NTH_ASM_T 12 ante_tac THEN asm_rewrite_tac [get_spec ⌜X⋎g⌝]);
(* *** Goal "2.3.2.1.2" *** *)
a (POP_ASM_T ante_tac THEN SYM_ASMS_T rewrite_tac THEN contr_tac);
(* *** Goal "2.3.2.1.3" *** *)
a (contr_tac);
(* *** Goal "2.3.2.2" *** *)
a (all_asm_fc_tac[]);
a (∃_tac ⌜x⌝ THEN ∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
val ConWkStrictSf_lemma = save_pop_thm "ConWkStrictSf_lemma";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏ConCoWkStrict⦎ : GS SET → (GS SET → (GS, FTV)BR → (GS, FTV)BR) → BOOL
├───────────
│ ∀V f⦁ ConCoWkStrict V f ⇔ ∀r⦁ OverDefined V (f V r) ⇒ OverDefined V r
■

=GFT
⦏ConCoWkStrictSf_lemma⦎ =
   ⊢ ∀ V⦁ V ⊆ Syntax ⇒ ConCoWkStrict V Sf
=TEX

\ignore{
=SML
set_goal ([], ⌜∀V⦁ V ⊆ Syntax ⇒ ConCoWkStrict V Sf⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜ConCoWkStrict⌝, get_spec ⌜Sf⌝,  get_spec ⌜OverDefined⌝]);
a (PC_T "hol1" (REPEAT strip_tac) THEN POP_ASM_T ante_tac);
a (asm_fc_tac[]);
a (DROP_NTH_ASM_T 3 discard_tac);
a (DROP_NTH_ASM_T 2 discard_tac);
a (lemma_tac ⌜IxRan (Param_∅ x) ⊆ V⌝
	THEN1 (rewrite_tac[sets_ext_clauses] THEN strip_tac THEN strip_tac
	THEN var_elim_nth_asm_tac 1));
a (DROP_NTH_ASM_T 3 ante_tac);
a (LEMMA_T ⌜∀v⦁ IxRan v ⊆ V
             ⇒ EvalForm (EvalCf_ftv, $≤⋎t⋎4, V, r) y v = fT
             ⇒ (∃ x y⦁ x ∈ V ∧ y ∈ V ∧ r x y = fT)⌝
	(rewrite_thm_tac
		o (rewrite_rule [asm_rule ⌜IxRan (Param_∅ x) ⊆ V⌝])
		o (∀_elim ⌜Param_∅ x⌝)));
a (POP_ASM_T discard_tac THEN POP_ASM_T ante_tac THEN sc_induction_tac ⌜y⌝);
a (REPEAT_N 3 strip_tac THEN asm_rewrite_tac[evalformfunct_thm2]);
a (cases_tac ⌜IsAf t⌝ THEN asm_rewrite_tac[let_def]);
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜EvalAf⌝, let_def]);
a (cond_cases_tac ⌜AfMem t ∈ IxDom v ∧ AfSet t ∈ IxDom v⌝);
a (all_fc_tac [ix_domran_lemma]);
a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜∀x y z⦁ x ∈ y ∧ y ⊆ z ⇒ x ∈ z⌝]);
a (strip_tac THEN ∃_tac ⌜IxVal v (AfMem t)⌝ THEN ∃_tac ⌜IxVal v (AfSet t)⌝ THEN asm_rewrite_tac []);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜EvalCf⌝, let_def, evalcf_ftv_ft_lemma] THEN strip_tac);
a (DROP_NTH_ASM_T 5 ante_tac THEN rewrite_tac [get_spec ⌜FunImage⌝] THEN strip_tac);
a (lemma_tac ⌜tc ScPrec a t ∧ a ∈ Syntax⌝
	THEN1 REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (bc_tac [tc_incr_thm]);
a (DROP_NTH_ASM_T 2 (asm_tac o (rewrite_rule [get_spec ⌜X⋎g⌝])));
a (lemma_tac ⌜IsCf t⌝ THEN1 fc_tac[syntax_cases_thm]);
a (all_asm_fc_tac [scprec_fc_clauses2]);
(* *** Goal "2.2" *** *)
a (lemma_tac ⌜IsCf t⌝ THEN1 fc_tac[syntax_cases_thm]);
a (FC_T (MAP_EVERY (strip_asm_tac o (try (rewrite_rule [asm_rule ⌜IsCf t⌝, asm_rule ⌜¬ IsAf t⌝])))) [∀_elim ⌜t⌝ is_fc_clauses]);
a (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[get_spec ⌜X⋎g⌝] THEN strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.3" *** *)
a (DROP_NTH_ASM_T 6 (ante_tac o eq_sym_rule));
a (GET_NTH_ASM_T 3 (rewrite_thm_tac o eq_sym_rule) THEN strip_tac);
a (list_spec_nth_asm_tac 13 [⌜a⌝]);
a (lemma_tac ⌜IxRan (IxOverRide v v') ⊆ V⌝);
(* *** Goal "2.3.1" *** *)
a (lemma_tac ⌜IxRan (IxOverRide v v') ⊆ IxRan v ∪ IxRan v'⌝ 
	THEN1 (rewrite_tac [ixoverride_ixran_lemma]));
a (lemma_tac ⌜IxRan v ∪ IxRan v' ⊆ V⌝
	THEN1 (asm_rewrite_tac [
		pc_rule1 "hol1" prove_rule [] ⌜∀A B C⦁ A ∪ B ⊆ C ⇔ A ⊆ C ∧ B ⊆ C⌝]));
a (all_asm_fc_tac [⊆_trans_thm]);
(* *** Goal "2.3.2" *** *)
a (all_asm_fc_tac[]);
a (∃_tac ⌜x⌝ THEN ∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
val ConCoWkStrictSf_lemma = save_pop_thm "ConCoWkStrictSf_lemma";
=TEX
}%ignore

=GFT
⦏ODE_SF_lemma⦎ =
   ⊢ ∀ V $∈⋎v
     ⦁ V ⊆ SetReps
           ∧ OverDefinedEss (V ∪ {∅⋎g}) V (Sf (V ∪ {∅⋎g}) $∈⋎v)
         ⇒ OverDefined (V ∪ {∅⋎g}) $∈⋎v

⦏ODE_SF_lemma2⦎ =
   ⊢ ∀ V $∈⋎v
     ⦁ V ⊆ SetReps ∧ OverDefinedEss (V ∪ {∅⋎g}) V (Sf V $∈⋎v)
         ⇒ OverDefined (V ∪ {∅⋎g}) $∈⋎v
=TEX

\ignore{
=SML
set_goal ([], ⌜∀V $∈⋎v⦁ V ⊆ SetReps ∧ OverDefinedEss (V ∪ {∅⋎g}) V (Sf (V ∪ {∅⋎g}) $∈⋎v) 
	⇒ OverDefined (V ∪ {∅⋎g}) $∈⋎v⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜Sf⌝,  get_spec ⌜OverDefinedEss⌝, get_spec ⌜Essence⌝,
	get_spec ⌜OverDefinedL⌝, get_spec ⌜OverDefined⌝, let_def]
	THEN PC_T "predicates" (REPEAT strip_tac));
a (lemma_tac ⌜y ∈ SetReps⌝
	THEN1 (PC_T1 "hol1" asm_prove_tac[]));
a (lemma_tac ⌜y ∈ Syntax⌝ THEN1 (asm_tac setreps_⊆_syntax_lemma THEN PC_T1 "hol1" asm_prove_tac []));
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [get_spec ⌜SetReps⌝])));
a (lemma_tac ⌜FreeVars y ⊆ IxDom (Param_∅ x)⌝
	THEN1 asm_rewrite_tac [ixdom_param_∅_lemma]);
a (lemma_tac ⌜IxRan (Param_∅ x) ⊆ V ∪ {∅⋎g}⌝
	THEN1 (PC_T1 "hol1" asm_prove_tac [ixran_param_∅_lemma]));
a (ALL_FC_T (MAP_EVERY ante_tac) [EvalForm_fT_lemma]);
a (PC_T1 "hol1" prove_tac[]);
val ODE_SF_lemma = save_pop_thm "ODE_SF_lemma";

set_goal ([], ⌜∀V $∈⋎v⦁ V ⊆ SetReps ∧ OverDefinedEss (V ∪ {∅⋎g}) V (Sf V $∈⋎v) 
	⇒ OverDefined (V ∪ {∅⋎g}) $∈⋎v⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜Sf⌝,  get_spec ⌜OverDefinedEss⌝, get_spec ⌜Essence⌝,
	get_spec ⌜OverDefinedL⌝, get_spec ⌜OverDefined⌝, let_def]
	THEN PC_T "predicates" (REPEAT strip_tac));
a (lemma_tac ⌜y ∈ SetReps⌝
	THEN1 (PC_T1 "hol1" asm_prove_tac[]));
a (lemma_tac ⌜y ∈ Syntax⌝ THEN1 (asm_tac setreps_⊆_syntax_lemma THEN PC_T1 "hol1" asm_prove_tac []));
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [get_spec ⌜SetReps⌝])));
a (lemma_tac ⌜FreeVars y ⊆ IxDom (Param_∅ x)⌝
	THEN1 asm_rewrite_tac [ixdom_param_∅_lemma]);
a (lemma_tac ⌜IxRan (Param_∅ x) ⊆ V ∪ {∅⋎g}⌝
	THEN1 (PC_T1 "hol1" asm_prove_tac [ixran_param_∅_lemma]));
a (ALL_FC_T (MAP_EVERY ante_tac) [EvalForm_fT_lemma2]);
a (PC_T1 "hol1" prove_tac[]);
val ODE_SF_lemma2 = save_pop_thm "ODE_SF_lemma2";
=TEX
}%ignore

=IGN
 ⓈHOLCONST
│ ⦏ConCoWkStrictEss⦎ : GS SET → GS SET → (GS SET → (GS, FTV)BR → (GS, FTV)BR) → BOOL
├───────────
│ ∀V W f⦁ ConCoWkStrictEss V W f ⇔
	∀r x y⦁ x ∈ V ∧ y ∈ V ∧ OverDefinedEss V W (f V (MsExt V r x y))
		⇒ OverDefinedEss V W (MsExt V r x y)
 ■

=GFT
⦏ODE_SF_MsExtend2_lemma⦎ =
   ⊢ ∀ V r x y
     ⦁ V ⊆ SetReps
           ∧ x ∈ V
           ∧ y ∈ V
           ∧ Compatible V r x y
           ∧ OverDefinedEss
             (V ∪ {∅⋎g})
             V
             (Sf (V ∪ {∅⋎g}) (MsExtend2 (V, r) x y))
         ⇒ OverDefined V r

⦏ODE_SF_MsExtend2_lemma2⦎ =
   ⊢ ∀ V r x y
     ⦁ V ⊆ SetReps
           ∧ x ∈ V
           ∧ y ∈ V
           ∧ Compatible V r x y
           ∧ OverDefinedEss
             (V ∪ {∅⋎g})
             V
             (Sf V (MsExtend2 (V, r) x y))
         ⇒ OverDefined V r
=TEX

\ignore{
=SML
set_goal([], ⌜∀ V r x y⦁
		V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V ∧ Compatible V r x y
		∧ OverDefinedEss (V ∪ {∅⋎g}) V (Sf (V ∪ {∅⋎g}) (MsExtend2 (V, r) x y))
                 ⇒ OverDefined V r⌝);
a (REPEAT strip_tac);
a (all_fc_tac [ODE_SF_lemma]);
a (swap_nth_asm_concl_tac 1);
a (lemma_tac ⌜V ⊆ Syntax⌝ THEN1 (asm_tac setreps_⊆_syntax_lemma THEN all_fc_tac [⊆_trans_thm]));
a (all_fc_tac [MsExtend2_¬OverDefined_lemma4]);
val ODE_SF_MsExtend2_lemma = save_pop_thm "ODE_SF_MsExtend2_lemma";

set_goal([], ⌜∀ V r x y⦁
		V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V ∧ Compatible V r x y
		∧ OverDefinedEss (V ∪ {∅⋎g}) V (Sf V (MsExtend2 (V, r) x y))
                 ⇒ OverDefined V r⌝);
a (REPEAT strip_tac);
a (all_fc_tac [ODE_SF_lemma2]);
a (swap_nth_asm_concl_tac 1);
a (lemma_tac ⌜V ⊆ Syntax⌝ THEN1 (asm_tac setreps_⊆_syntax_lemma THEN all_fc_tac [⊆_trans_thm]));
a (all_fc_tac [MsExtend2_¬OverDefined_lemma4]);
val ODE_SF_MsExtend2_lemma2 = save_pop_thm "ODE_SF_MsExtend2_lemma2";
=TEX
}%ignore

=GFT
⦏ExsSRO_MsExtend2_lemma1⦎ =
   ⊢ ∀ V r x y
     ⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ Compatible V r x y
         ⇒ ExsSRO (V, MsExtend2 (V, r) x y) x ∅⋎g
           ∧ ExsSRO (V, MsExtend2 (V, r) x y) y ∅⋎g
=TEX

\ignore{
=SML
set_goal([], ⌜∀ V r x y⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ Compatible V r x y
	⇒ ExsSRO (V, MsExtend2 (V, r) x y) x ∅⋎g
	∧ ExsSRO (V, MsExtend2 (V, r) x y) y ∅⋎g ⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac(map get_spec
		[⌜ExsSRO⌝, ⌜ExtSRO⌝, ⌜EssSRO⌝, ⌜ConjOrder⌝, ⌜Compatible⌝])
	THEN REPEAT_N 1 strip_tac);
a (rewrite_tac [∀_∧_out_lemma] THEN strip_tac);
a (rewrite_tac [prove_rule [] ⌜∀A B C D E⦁ ((A ⇒ B) ∧ (A ⇒ C)) ∧ (A ⇒ D) ∧ (A ⇒ E) ⇔ (A ⇒ B ∧ C ∧ D ∧ E)⌝]);
a (STRIP_T asm_tac);
a (MAP_EVERY strip_asm_tac (map (list_∀_elim [⌜(V, r)⌝, ⌜x⌝, ⌜y⌝, ⌜x'⌝])
		[MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma1,
		MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma1,
		MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma2,
		MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma2]));
a contr_tac;
val ExsSRO_MsExtend2_lemma1 = save_pop_thm "ExsSRO_MsExtend2_lemma1";
=TEX
}%ignore

=GFT
⦏ExsSRO_MsExtend2_lemma2⦎ =
   ⊢ ∀ V r x y
     ⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ Compatible V r x y
         ⇒ ExsSRO (V ∪ {∅⋎g}, MsExtend2 (V, r) x y) x ∅⋎g
           ∧ ExsSRO (V ∪ {∅⋎g}, MsExtend2 (V, r) x y) y ∅⋎g
=TEX

\ignore{
=SML
set_goal([], ⌜∀ V r x y⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ Compatible V r x y
	⇒ ExsSRO (V ∪ {∅⋎g}, MsExtend2 (V, r) x y) x ∅⋎g
	∧ ExsSRO (V ∪ {∅⋎g}, MsExtend2 (V, r) x y) y ∅⋎g ⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac(map get_spec
		[⌜ExsSRO⌝, ⌜ExtSRO⌝, ⌜EssSRO⌝, ⌜ConjOrder⌝])
	THEN REPEAT_N 1 strip_tac);
a (GET_NTH_ASM_T 1 (strip_asm_tac o (rewrite_rule [get_spec ⌜Compatible⌝])));
a (rewrite_tac [∀_∧_out_lemma] THEN strip_tac);
a (rewrite_tac [prove_rule [] ⌜∀A B C D E⦁ ((A ⇒ B) ∧ (A ⇒ C)) ∧ (A ⇒ D) ∧ (A ⇒ E) ⇔ (A ⇒ B ∧ C ∧ D ∧ E)⌝]);
a (STRIP_T asm_tac);
a (MAP_EVERY (PC_T1 "predicates" strip_asm_tac) (map (list_∀_elim [⌜(V, r)⌝, ⌜x⌝, ⌜y⌝, ⌜x'⌝])
		[MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma1b,
		MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma1b,
		MsExtend2_x_≤⋎t⋎4_∅⋎g_lemma2b,
		MsExtend2_y_≤⋎t⋎4_∅⋎g_lemma2b]));
a contr_tac;
val ExsSRO_MsExtend2_lemma2 = save_pop_thm "ExsSRO_MsExtend2_lemma2";
=TEX
}%ignore

=GFT
⦏Compatibility_lemma1⦎ =
   ⊢ ∀ V $∈⋎v x y
     ⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ Compatible V $∈⋎v x y
         ⇒ EssSRO (V, Sf V (MsExtend2 (V, $∈⋎v) x y)) x ∅⋎g
           ∧ EssSRO (V, Sf V (MsExtend2 (V, $∈⋎v) x y)) y ∅⋎g
=TEX

\ignore{
=SML
set_goal ([], ⌜∀ V $∈⋎v x y⦁ V ⊆ Syntax ∧ x ∈ V ∧ y ∈ V ∧ Compatible V $∈⋎v x y
	⇒ EssSRO (V, Sf V (MsExtend2 (V, $∈⋎v) x y)) x ∅⋎g
	∧ EssSRO (V, Sf V (MsExtend2 (V, $∈⋎v) x y)) y ∅⋎g⌝);
a (REPEAT_N 5 strip_tac THEN all_fc_tac [ExsSRO_MsExtend2_lemma2]);
a (lemma_tac ⌜V ⊆ V ∪ {∅⋎g}⌝ THEN1 (PC_T1 "hol1" prove_tac []));
a (lemma_tac ⌜((V ∪ {∅⋎g}) ◁⋎o ExsSRO (V ∪ {∅⋎g}, MsExtend2 (V, $∈⋎v) x y)) x ∅⋎g⌝
	THEN1 asm_rewrite_tac [get_spec ⌜$◁⋎o⌝, ∈_in_clauses]);
a (lemma_tac ⌜((V ∪ {∅⋎g}) ◁⋎o ExsSRO (V ∪ {∅⋎g}, MsExtend2 (V, $∈⋎v) x y)) y ∅⋎g⌝
	THEN1 asm_rewrite_tac [get_spec ⌜$◁⋎o⌝, ∈_in_clauses]);
a (all_fc_tac [rewrite_rule [get_spec ⌜Increasing⌝] essence_exstentional_lemma2]);
a (contr_tac);
val Compatibility_lemma1 = save_pop_thm "Compatibility_lemma1";
=TEX
}%ignore

=GFT
⦏Compatibility_lemma2⦎ =
   ⊢ ∀ V $∈⋎v x y
     ⦁ V ⊆ SetReps
           ∧ x ∈ V
           ∧ y ∈ V
           ∧ Compatible V $∈⋎v x y
           ∧ ¬ OverDefined V $∈⋎v
         ⇒ CompEss V (Sf V $∈⋎v) x y
=TEX

\ignore{
=SML
set_goal ([], ⌜∀ V $∈⋎v x y⦁ V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V ∧ Compatible V $∈⋎v x y ∧ ¬ OverDefined V $∈⋎v
	⇒ CompEss V (Sf V $∈⋎v) x y⌝);
a (REPEAT_N 5 strip_tac);
a (fc_tac [setreps_⊆_syntax_lemma2]);
a (rewrite_tac [get_spec ⌜CompEss⌝, get_spec ⌜$◁⋎o⌝, get_spec ⌜ExsSRO⌝, ∈_in_clauses, get_spec ⌜ConjOrder⌝]
	THEN all_fc_tac [Compatibility_lemma1]
	THEN REPEAT strip_tac);
a (REPEAT_N 2 (DROP_NTH_ASM_T 2 ante_tac) THEN rewrite_tac [get_spec ⌜EssSRO⌝]
	THEN REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim [⌜(V, $∈⋎v)⌝, ⌜x⌝, ⌜y⌝, ⌜x⌝, ⌜z⌝] Sf_MsExtend2_lemma1));
a (strip_asm_tac (list_∀_elim [⌜(V, $∈⋎v)⌝, ⌜x⌝, ⌜y⌝, ⌜y⌝, ⌜z⌝] Sf_MsExtend2_lemma1));
a (REPEAT_N 2 (spec_nth_asm_tac 4 ⌜z⌝));
a (REPEAT_N 2 (POP_ASM_T ante_tac));
a (asm_rewrite_tac[] THEN REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim  [⌜V⌝, ⌜$∈⋎v⌝, ⌜x⌝, ⌜y⌝] ODE_SF_MsExtend2_lemma2));
a (POP_ASM_T (strip_asm_tac o (rewrite_rule [get_spec ⌜OverDefinedEss⌝, get_spec ⌜OverDefinedL⌝, get_spec ⌜Essence⌝])));
a (spec_nth_asm_tac 1 ⌜∅⋎g⌝);
a (spec_nth_asm_tac 1 ⌜z⌝);
a (DROP_NTH_ASM_T 1 ante_tac
	THEN DROP_NTH_ASM_T 3 ante_tac
	THEN DROP_NTH_ASM_T 3 ante_tac
	THEN strip_asm_tac (∀_elim ⌜Sf V (MsExtend2 (V, $∈⋎v) x y) ∅⋎g z⌝ ftv_cases_thm)
	THEN asm_rewrite_tac[]
	THEN strip_asm_tac (∀_elim ⌜Sf V $∈⋎v x z⌝ ftv_cases_thm)
	THEN asm_rewrite_tac[]
	THEN strip_asm_tac (∀_elim ⌜Sf V $∈⋎v y z⌝ ftv_cases_thm)
	THEN asm_rewrite_tac[]
	THEN rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜∀x⦁ {x; fB} = {fB; x}⌝]);
val Compatibility_lemma2 = save_pop_thm "Compatibility_lemma2";
=TEX
}%ignore

=GFT
⦏Compatibility_lemma3⦎ =
   ⊢ ∀ V $∈⋎v x y
     ⦁ V ⊆ SetReps
           ∧ x ∈ V
           ∧ y ∈ V
           ∧ Compatible V $∈⋎v x y
           ∧ ¬ OverDefined V $∈⋎v
         ⇒ let r = (Sf V $∈⋎v) in {r x y; r y x; r x x; r y y} ∈ CompFTV
=TEX

\ignore{
=IGN
set_flag("subgoal_package_quiet", false);

stop;

set_goal ([], ⌜∀ V $∈⋎v x y⦁ V ⊆ SetReps ∧ x ∈ V ∧ y ∈ V ∧ Compatible V $∈⋎v x y ∧ ¬ OverDefined V $∈⋎v
	⇒ let r = (Sf V $∈⋎v) in {r x y; r y x; r x x; r y y} ∈ CompFTV⌝);
a (REPEAT_N 5 strip_tac);
a (fc_tac [setreps_⊆_syntax_lemma2]);
a (rewrite_tac [get_spec ⌜CompEss⌝, get_spec ⌜$◁⋎o⌝, get_spec ⌜ExsSRO⌝, ∈_in_clauses, get_spec ⌜ConjOrder⌝]
	THEN all_fc_tac [Compatibility_lemma1]
	THEN REPEAT strip_tac);
a (REPEAT_N 2 (DROP_NTH_ASM_T 2 ante_tac) THEN rewrite_tac [get_spec ⌜EssSRO⌝]
	THEN REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim [⌜(V, $∈⋎v)⌝, ⌜x⌝, ⌜y⌝, ⌜x⌝, ⌜z⌝] Sf_MsExtend2_lemma1));
a (strip_asm_tac (list_∀_elim [⌜(V, $∈⋎v)⌝, ⌜x⌝, ⌜y⌝, ⌜y⌝, ⌜z⌝] Sf_MsExtend2_lemma1));
a (REPEAT_N 2 (spec_nth_asm_tac 4 ⌜z⌝));
a (REPEAT_N 2 (POP_ASM_T ante_tac));
a (asm_rewrite_tac[] THEN REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim  [⌜V⌝, ⌜$∈⋎v⌝, ⌜x⌝, ⌜y⌝] ODE_SF_MsExtend2_lemma2));
a (POP_ASM_T (strip_asm_tac o (rewrite_rule [get_spec ⌜OverDefinedEss⌝, get_spec ⌜OverDefinedL⌝, get_spec ⌜Essence⌝])));
a (spec_nth_asm_tac 1 ⌜∅⋎g⌝);
a (spec_nth_asm_tac 1 ⌜z⌝);
a (DROP_NTH_ASM_T 1 ante_tac
	THEN DROP_NTH_ASM_T 3 ante_tac
	THEN DROP_NTH_ASM_T 3 ante_tac
	THEN strip_asm_tac (∀_elim ⌜Sf V (MsExtend2 (V, $∈⋎v) x y) ∅⋎g z⌝ ftv_cases_thm)
	THEN asm_rewrite_tac[]
	THEN strip_asm_tac (∀_elim ⌜Sf V $∈⋎v x z⌝ ftv_cases_thm)
	THEN asm_rewrite_tac[]
	THEN strip_asm_tac (∀_elim ⌜Sf V $∈⋎v y z⌝ ftv_cases_thm)
	THEN asm_rewrite_tac[]
	THEN rewrite_tac [pc_rule1 "hol1" prove_rule [] ⌜∀x⦁ {x; fB} = {fB; x}⌝]);
val Compatibility_lemma3 = save_pop_thm "Compatibility_lemma3";
=TEX
}%ignore

=GFT
⦏CompExtSem_Sf_thm⦎ =
	⊢ ∀ V⦁ V ⊆ SetReps ⇒ CompExtSem V Sf
=TEX

\ignore{
=SML
set_goal ([], ⌜∀ V⦁ V ⊆ SetReps ⇒ CompExtSem V Sf⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜CompExtSem⌝] THEN REPEAT strip_tac);
a (lemma_tac ⌜V ⊆ V ∪ {∅⋎g}⌝ THEN1 PC_T1 "hol1" prove_tac[]);
a (all_fc_tac [Compatibility_lemma2]);
val CompExtSem_Sf_thm = save_pop_thm "CompExtSem_Sf_thm";
=TEX
}%ignore

=GFT
=TEX

\ignore{
=IGN
set_flag("subgoal_package_quiet", false);

stop;

set_goal ([], ⌜∀ V⦁ V ⊆ SetReps ⇒ CompExtSem2 V Sf⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜CompExtSem2⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜V ⊆ V ∪ {∅⋎g}⌝ THEN1 PC_T1 "hol1" prove_tac[]);
a (all_fc_tac [Compatibility_lemma2]);
(* *** Goal "2" *** *)

val CompExtSem2_Sf_thm = save_pop_thm "CompExtSem2_Sf_thm";


=IGN
set_goal([], ⌜∀V r⦁ V ⊆ SetReps ∧ PreExtensional2 V r ⇒ PreExtensional2 V (Sf V r)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜PreExtensional2⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜V ⊆ Syntax⌝ THEN1 (PC_T1 "hol1" asm_prove_tac [get_spec ⌜SetReps⌝]));
a (swap_nth_asm_concl_tac 3
	THEN all_fc_tac [rewrite_rule [get_spec ⌜ConCoWkStrict⌝] ConCoWkStrictSf_lemma]);
(* *** Goal "2" *** *)
a (contr_tac);
a (asm_tac (rewrite_rule [get_spec ⌜CompExtSem⌝, get_spec ⌜Compatible⌝] (CompExtSem_Sf_thm)));
a (list_spec_nth_asm_tac 1 [⌜V⌝]);
a (list_spec_nth_asm_tac 1 [⌜r⌝]);
a (REPEAT_N 2 (DROP_NTH_ASM_T 2 discard_tac));
a (lemma_tac ⌜{r x y; r y x; r x x; r y y} ∈ CompFTV⌝


a (list_spec_nth_asm_tac 1 [⌜x⌝, ⌜y⌝]);
(* *** Goal "2.1" *** *)
a (swap_nth_asm_concl_tac 1);

=TEX
}%ignore

\subsection{Properties of SfChains}

Properties of least fixed points of the semantic functor are in part obtained by induction over the relevant FChain (see \cite{rbjt007} for the theory of $FChains$).
Since inductive proofs yeild properties shared by all the members of the FChain, and its best to prove them of the FChain so that their full force can be used in subsequent inductive proofs.

First abbreviated notation for the FChains generated by the semantic functor.

ⓈHOLCONST
│ ⦏SfChain⦎ : GS SET → (GS, FTV)BR SET
├───────────
│ ∀V⦁ SfChain V = FChainU (Sf V) $≤⋎∈
■

For inductive reasoning about $SfChain$s the general induction theorem for fchains is specialised to the chains generated by the semantic functor.

=GFT
⦏sfchain_induction_thm⦎ =
   ⊢ ∀ V p
     ⦁ V ⊆ SetReps
           ∧ (∀ x⦁ x ∈ SfChain V ∧ (∀ y⦁ y ∈ SfChain V ∧ y ≤⋎∈ x ⇒ p y)
               ⇒ p (Sf V x))
           ∧ (∀ x⦁ x ∈ SfChain V
                 ∧ x = Lub $≤⋎∈ {y|y ∈ SfChain V ∧ y ≤⋎∈ x ∧ ¬ x ≤⋎∈ y}
                 ∧ (∀ y⦁ y ∈ SfChain V ∧ y ≤⋎∈ x ∧ ¬ x ≤⋎∈ y ⇒ p y)
               ⇒ p x)
         ⇒ (∀ x⦁ x ∈ SfChain V ⇒ p x)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀V p⦁ V ⊆ SetReps 
           ∧ (∀ x
           ⦁ x ∈ SfChain V
                 ∧ (∀ y⦁ y ∈ SfChain V ∧ y ≤⋎∈ x ⇒ p y)
               ⇒ p (Sf V x))
           ∧ (∀ x
           ⦁ x ∈ SfChain V
                 ∧ x = Lub $≤⋎∈ {y|y ∈ SfChain V ∧ y ≤⋎∈ x ∧ ¬ x ≤⋎∈ y}
                 ∧ (∀ y⦁ y ∈ SfChain V ∧ y ≤⋎∈ x ∧ ¬ x ≤⋎∈ y ⇒ p y)
               ⇒ p x)
         ⇒ (∀ x⦁ x ∈ SfChain V ⇒ p x)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜SfChain⌝]
	THEN REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim [⌜$≤⋎∈⌝,⌜Sf V⌝,⌜p⌝] fchainu_induction_thm4));
(* *** Goal "1" *** *)
a (swap_nth_asm_concl_tac 1);
a (bc_tac [crpou_ccrpou_lemma]);
a (rewrite_tac[crpou_≤⋎∈_thm]);
(* *** Goal "2" *** *)
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac [get_spec ⌜Sf⌝, sf_increasing_thm]);
(* *** Goal "3" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "4" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "5" *** *)
a (all_asm_fc_tac[]);
val sfchain_induction_thm = save_pop_thm "sfchain_induction_thm";
=TEX
}%ignore

It will be convenient to have a tactic to facilitate this kind of induction.

The following tactic does not expect an argument, but expects the conclusion of the goal to be an implication of which the antecedent asserts that the induction variable is a member of the relevant $SfChain$.

=SML
fun ⦏sfchain_induction_tac⦎ (a,c) =
	let val (l1, l2) = dest_⇒ c
	in let val (_, [v, _]) = strip_app l1
	in let val l3 = mk_∀ (v, mk_⇒ (l1, mk_app (mk_λ (v, l2), v)))
	in
		LEMMA_T l3 (rewrite_thm_tac o (rewrite_rule []))
		THEN bc_tac [sfchain_induction_thm]
		THEN REPEAT strip_tac THEN_TRY rewrite_tac[]
	end end end (a,c);
=TEX

This kind of inductive proof requires reasoning about the least upper bounds of subsets of $SfChain$s for which the following lemmas will be helpful.

=GFT
=TEX

\ignore{
=IGN
set_goal([], ⌜∀V X⦁ X ⊆ SfChain V ∧ x = Lub $≤⋎∈ X
	⇒ ∀v w z⦁ v ∈ V ∧ w ∈ V ∧ z ≤⋎t⋎4 x v w ⇒ ∃y⦁ y ∈ X ∧ z ≤⋎t⋎4 y v w⌝);
a (contr_tac);
a (lemma_tac ⌜IsLub $≤⋎∈ X (Lub $≤⋎∈ X)⌝
	THEN1 (bc_tac [lub_lub_lemma2] THEN rewrite_tac[]));
a (fc_tac [get_spec ⌜IsLub⌝]);
a (
a 

type_of ⌜SfChain V⌝;
type_of ⌜Lub $≤⋎∈⌝;

=TEX
}%ignore

Some general properties of $FChains$ are specialised to $SfChain$s for convenience of application.

=GFT
⦏sfchain_mono_thm⦎ =
   ⊢ ∀ V x⦁ x ∈ SfChain V ⇒ x ≤⋎∈ Sf V x)

⦏sfchain_linear_lemma⦎ =
   ⊢ ∀ V⦁ LinearOrder (SfChain V, $≤⋎∈)

⦏sfsubchain_linear_lemma⦎ =
   ⊢ ∀ V X⦁ X ⊆ SfChain V ⇒ LinearOrder (X, $≤⋎∈)
=TEX

\ignore{
=SML
set_goal([], ⌜∀V x⦁ x ∈ SfChain V ⇒ x ≤⋎∈ (Sf V x)⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜SfChain⌝]
	THEN REPEAT strip_tac);
a (fc_tac [rewrite_rule [ccrpou_≤⋎∈_thm, sf_increasing_thm] (list_∀_elim [⌜$≤⋎∈⌝, ⌜Sf V⌝] ccrpou_fchainu_lemma1)]);
val sfchain_mono_thm = save_pop_thm "sfchain_mono_thm";

set_goal([], ⌜∀V⦁ LinearOrder (SfChain V, $≤⋎∈)⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜SfChain⌝]);
a (accept_tac (rewrite_rule [] (list_∀_elim [⌜$≤⋎∈⌝, ⌜Sf V⌝] ccrpou_fchainu_linear_lemma)));
val sfchain_linear_lemma = save_pop_thm "sfchain_linear_lemma";

set_goal([], ⌜∀V X⦁ X ⊆ SfChain V ⇒ LinearOrder (X, $≤⋎∈)⌝);
a (REPEAT strip_tac
	THEN bc_tac [subrel_linear_order_thm]);
a (∃_tac ⌜SfChain V⌝ THEN asm_rewrite_tac [sfchain_linear_lemma]);
val sfsubchain_linear_lemma = save_pop_thm "sfsubchain_linear_lemma";

add_pc_thms "'sfp" (map get_spec [] @ [sfchain_linear_lemma]);
set_merge_pcs ["misc2", "'ifos", "'sfp"];
=TEX
}%ignore

The following properties of $SfChain$s are needed to prove that least fixed points are ``pre-extensional''.


The first property we consider is that of non-overdefinedness.

=GFT
⦏sfchain_¬overdefined_lemma⦎ =
   ⊢ ∀ V⦁ V ⊆ SetReps ⇒ (∀ x⦁ x ∈ SfChain V ⇒ ¬ OverDefined V x)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀V⦁ V ⊆ SetReps ⇒ ∀x⦁ x ∈ SfChain V ⇒ ¬ OverDefined V x⌝);
a (REPEAT strip_tac);
a (POP_ASM_T ante_tac);
a (sfchain_induction_tac);
(* *** Goal "1" *** *)
a (fc_tac [setreps_⊆_syntax_lemma2]);
a (fc_tac [ConCoWkStrictSf_lemma]);
a (fc_tac [get_spec ⌜ConCoWkStrict⌝]);
a (contr_tac THEN all_asm_fc_tac []);
a (spec_nth_asm_tac 6 ⌜x⌝);
(* *** Goal "1.1" *** *)
a (asm_tac crpou_≤⋎∈_thm);
a (all_asm_fc_tac [crpou_fc_clauses]);
a (DROP_NTH_ASM_T 3 ante_tac THEN rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜OverDefined⌝] THEN contr_tac);
a (DROP_NTH_ASM_T 5 (ante_tac o (rewrite_rule [≤⋎∈_lub_thm])));
a (asm_rewrite_tac [ext_thm] THEN strip_tac);
a (∃_tac ⌜x'⌝ THEN strip_tac);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac [] THEN contr_tac);
a (lemma_tac ⌜LinearOrder ({w|∃ g⦁ (g ∈ SfChain V ∧ g ≤⋎∈ x ∧ ¬ x ≤⋎∈ g) ∧ w = g x' y}, $≤⋎t⋎4)⌝);
(* *** Goal "2.1" *** *)
a (LEMMA_T ⌜{w|∃ g⦁ (g ∈ SfChain V ∧ g ≤⋎∈ x ∧ ¬ x ≤⋎∈ g) ∧ w = g x' y}
		= FunImage (λf⦁ f x' y) {g | g ∈ SfChain V ∧ g ≤⋎∈ x ∧ ¬ x ≤⋎∈ g}⌝ rewrite_thm_tac
	THEN1 rewrite_tac [get_spec ⌜FunImage⌝] THEN PC_T1 "hol1" prove_tac[]);
(* *** Goal "2.1.1" *** *)
a (∃_tac ⌜g⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
a (∃_tac ⌜a⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.3" *** *)
a (bc_tac [linear_funimage_thm]);
a (∃_tac ⌜$≤⋎∈⌝ THEN asm_rewrite_tac [≤⋎∈_increasing_pointwise_thm]);
a (bc_tac [sfsubchain_linear_lemma]);
a (∃_tac ⌜V⌝ THEN rewrite_tac [sets_ext_clauses]
	THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a (fc_tac [≤⋎t⋎4_lin_lub_lemma2]);
a (spec_nth_asm_tac 10 ⌜g⌝);
a (POP_ASM_T (ante_tac o (rewrite_rule[])));
a (asm_rewrite_tac [get_spec ⌜OverDefined⌝]);
a (∃_tac ⌜x'⌝ THEN ∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
val sfchain_¬overdefined_lemma = save_pop_thm "sfchain_¬overdefined_lemma";
=TEX
}%ignore

Now we derive the properties of $SfChain$s which follow from the $CompExtSem$ property of the semantic functor.

=GFT
=TEX

\ignore{
=IGN
set_flag ("subgoal_package_quiet", false);
stop;

set_goal([], ⌜∀V⦁ V ⊆ SetReps
	⇒ ∀r1 r2⦁ r1 ≤⋎∈ r2
	⇒ ∀x y⦁ x ∈ SfChain ∧ y ∈ SfChain
	⇒ ¬ CompExt V r1 x y
	⇒ ¬ CompExt V r2 x y

⌝);

set_goal([], ⌜∀V⦁ ⊆ SetReps
	⇒ ∀x y⦁ x ∈ SfChain ∧ y ∈ SfChain
	⇒ CompExt V r x y ∧ {r x x, r x y, r y y, r y x} ∈ CompFTV
	⇒ CompEss V r x y⌝);

set_goal ([], ⌜∀V⦁ V ⊆ SetReps ⇒ ∀x⦁ x ∈ SfChain V ⇒ PreExtensional2 V x⌝);
a (REPEAT strip_tac);
a (POP_ASM_T ante_tac);
a (sfchain_induction_tac);
(* *** Goal "1" *** *)

=TEX
}%ignore

=SML
set_flag ("subgoal_package_quiet", false);
=TEX

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{ifos.th}
\include{sfp.th}
}  %\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
