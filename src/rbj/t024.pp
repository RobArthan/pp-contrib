=IGN
$Id: t024.doc,v 1.19 2012/08/11 21:01:52 rbj Exp $
open_theory "ifol";
set_merge_pcs ["hol1", "'GS1", "'misc1", "'misc2", "'ifol"];
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\usepackage{A4}

%\def\ExpName{\mbox{{\sf exp}
%\def\Exp#1{\ExpName(#1)}

\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{Infinitarily Definable Non-Well-Founded Sets}
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
This paper is my second approach to set theory conceived as a maximal consistent theory of set comprehension.
The principle innovation in this version is to simplify the syntax by removing comprehension, so that the syntactic category of term is no longer required.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created: 2006/11/29

Last Change $ $Date: 2012/08/11 21:01:52 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t021.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t021.pdf}

$ $Id: t024.doc,v 1.19 2012/08/11 21:01:52 rbj Exp $ $

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

See t021 for previous discussion.
I will put something better here if it works out.

\section{INFINITARY LOGIC}

=SML
open_theory "misc2";
force_new_theory "⦏ifol⦎";
force_new_pc "⦏'ifol⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'ifol";
set_merge_pcs ["hol1", "'GS1", "'misc1", "'misc2", "'ifol"];
=TEX

\subsection{Syntax}

\subsubsection{Constructors, Discriminators and Destructors}

Preliminary to presenting the inductive definition of the required classes we define the nuts and bolts operations on the required syntactic entities (some of which will be used in the inductive definition).

A constructor puts together some syntactic entity from its constituents, discriminators distinguist between the different kinds of entity and destructors take them apart.

``Atomic'' formulae consist of a relation name together with an indexed collection of arguments.
The relation name may be any set.
The indexed set of arguments is any set which is a function, i.e. a many-one relation represented as a set of (Wiener-Kuratovski) ordered pairs.
The distinction between atomic and compound formulae is made by tagging the former with the ordinal zero and the latter with the ordinal 1, a tagged value in this  case being an ordered pair of which the left element is the tag and the right element is the value.

ⓈHOLCONST
│ ⦏MkAf⦎ : GS × GS → GS
├───────────
│ ∀lr⦁ MkAf lr = (Nat⋎g 0) ↦⋎g ((Fst lr) ↦⋎g (Snd lr))
■

ⓈHOLCONST
│ ⦏IsAf⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsAf t = fst t = (Nat⋎g 0)
■

ⓈHOLCONST
│ ⦏AfRel⦎ : GS → GS
├───────────
│  AfRel = λx⦁ fst(snd x)
■

ⓈHOLCONST
│ ⦏AfPars⦎ : GS → GS
├───────────
│  AfPars = λx⦁ snd(snd x)
■

ⓈHOLCONST
│ ⦏MkCf⦎ : GS × GS → GS
├───────────
│ ∀vc⦁ MkCf vc = (Nat⋎g 1) ↦⋎g ((Fst vc) ↦⋎g (Snd vc))
■

ⓈHOLCONST
│ ⦏IsCf⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsCf t = fst t = (Nat⋎g 1)
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

add_pc_thms "'ifol" (map get_spec [] @ [ord_nat_thm, Is_clauses]);
set_merge_pcs ["hol1", "'GS1", "'misc1", "'misc2", "'ifol"];

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
│	(∀ n is⦁ fun is ⇒ MkAf (n, is) ∈ s)
│∧	(∀ vars fs⦁ X⋎g fs ⊆ s ⇒ MkCf (vars, fs) ∈ s)
■

The well-formed syntax is then the smallest set closed under these constructions.

ⓈHOLCONST
│ ⦏Syntax⦎ : GS SET
├───────────
│ Syntax = ⋂{x | RepClosed x}
■

=GFT
⦏syntax_⊆_repclosed_thm⦎ =
	⊢ ∀ s⦁ RepClosed s ⇒ Syntax ⊆ s
=TEX

\ignore{
=SML
set_goal([], ⌜∀s⦁ RepClosed s ⇒ Syntax ⊆ s⌝);
a (rewrite_tac [get_spec ⌜Syntax⌝]
	THEN REPEAT strip_tac THEN asm_fc_tac[]);
val syntax_⊆_repclosed_thm = pop_thm ();
=TEX
}%ignore

This is an ``inductive datatype'' so we should expect the usual kinds of theorems.

Informally these should say:

\begin{itemize}
\item Syntax is closed under the two constructors.
\item The syntax constructors are injections, have disjoint ranges, and partition the syntax. 
\item Any syntactic property which is preserved by the constructors (i.e. is true of any construction if it is true of all its syntactic constituents) is true of everything in syntax (this is an induction principle).
\end{itemize}

=GFT
⦏repclosed_syntax_lemma⦎ =
	⊢ RepClosed Syntax

⦏repclosed_syntax_thm⦎ =
	⊢ (∀ n is⦁ fun is ⇒ MkAf (n, is) ∈ Syntax)
       ∧ (∀ vars fs
       ⦁ (∀ x⦁ x ∈ X⋎g fs ⇒ x ∈ Syntax) ⇒ MkCf (vars, fs) ∈ Syntax)

⦏repclosed_syntax_lemma1⦎ =
	⊢ ∀ s⦁ RepClosed s ⇒ Syntax ⊆ s

⦏repclosed_syntax_lemma2⦎ =
	⊢ ∀ p⦁ RepClosed {x|p x} ⇒ (∀ x⦁ x ∈ Syntax ⇒ p x)
=TEX

\ignore{
=SML
set_goal([], ⌜RepClosed Syntax⌝);
a (rewrite_tac (map get_spec [⌜RepClosed⌝])
	THEN strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac (map get_spec [⌜RepClosed⌝, ⌜Syntax⌝])
	THEN REPEAT strip_tac THEN asm_fc_tac [] THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (rewrite_tac (map get_spec [ ⌜Syntax⌝])
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
a (fc_tac [get_spec ⌜RepClosed⌝]);
a (lemma_tac ⌜∀ x⦁ x ∈ X⋎g fs ⇒ x ∈ s⌝
	THEN1 (REPEAT strip_tac THEN all_asm_fc_tac[]));
a (all_asm_fc_tac[]);
a (asm_rewrite_tac[]);
val repclosed_syntax_lemma = pop_thm ();

val repclosed_syntax_thm = save_thm ("repclosed_syntax_thm",
	rewrite_rule [get_spec ⌜RepClosed⌝] repclosed_syntax_lemma);

set_goal([], ⌜∀s⦁ RepClosed s ⇒ Syntax ⊆ s⌝);
a (rewrite_tac [get_spec ⌜Syntax⌝]
	THEN prove_tac[]);
val repclosed_syntax_lemma1 = save_pop_thm "repclosed_syntax_lemma1";

set_goal([], ⌜∀p⦁ RepClosed {x | p x} ⇒ ∀x⦁ x ∈ Syntax ⇒ p x⌝);
a (rewrite_tac [get_spec ⌜Syntax⌝] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
val repclosed_syntax_lemma2 = save_pop_thm "repclosed_syntax_lemma2";
=TEX
}%ignore

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
set_goal([], ⌜∀x y⦁ ScPrec x y ⇒ tc $∈⋎g x y⌝);
a (rewrite_tac (map get_spec [⌜ScPrec⌝, ⌜MkCf⌝]));
a (REPEAT strip_tac THEN asm_rewrite_tac [↦_tc_thm]);
a (lemma_tac ⌜tc $∈⋎g fs (ord ↦⋎g fs) ∧ tc $∈⋎g (ord ↦⋎g fs) (Nat⋎g 1 ↦⋎g ord ↦⋎g fs)⌝
	THEN1 rewrite_tac [↦_tc_thm]);
a (all_fc_tac [tc_incr_thm]);
a (all_fc_tac [tran_tc_thm2]);
a (all_fc_tac [tran_tc_thm2]);
val ScPrec_tc_∈_thm = pop_thm ();

set_goal ([], ⌜well_founded ScPrec⌝);
a (rewrite_tac [get_spec ⌜well_founded⌝]);
a (REPEAT strip_tac);
a (asm_tac (∀_elim ⌜s⌝ gs_cv_ind_thm));
a (lemma_tac ⌜∀ x⦁ (∀ y⦁ tc $∈⋎g y x ⇒ s y) ⇒ s x⌝
	THEN1 REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜∀ y⦁ ScPrec y x ⇒ s y⌝
	THEN1 (REPEAT strip_tac THEN all_fc_tac [ScPrec_tc_∈_thm]
		THEN asm_fc_tac []));
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (asm_fc_tac[]);
a (asm_rewrite_tac[]);
val well_founded_ScPrec_thm =  save_pop_thm "well_founded_ScPrec_thm";

set_goal([], ⌜well_founded (tc ScPrec)⌝);
a (asm_tac well_founded_ScPrec_thm);
a (fc_tac [wf_tc_wf_thm]);
val well_founded_tcScPrec_thm = save_pop_thm ("well_founded_tcScPrec_thm");
=TEX

}%ignore

=SML
val ⦏SC_INDUCTION_T⦎ = WFCV_INDUCTION_T well_founded_ScPrec_thm;
val ⦏sc_induction_tac⦎ = wfcv_induction_tac well_founded_ScPrec_thm;
=TEX

The set Syntax gives us the syntactically well-formed phrases of our language.
It will be useful to have some predicates which incorporate well-formedness, which are defined here.

=GFT
⦏syntax_disj_thm⦎ =
   ⊢ ∀ x
     ⦁ x ∈ Syntax
         ⇒ (∃ r pars⦁ fun pars ∧ x = MkAf (r, pars))
           ∨ (∃ vars fs⦁ (∀ y⦁ y ∈⋎g fs ⇒ y ∈ Syntax) ∧ x = MkCf (vars, fs))

⦏syntax_cases_thm⦎ =
   ⊢ ∀ x⦁ x ∈ Syntax ⇒ IsAf x ∨ IsCf x

⦏is_fc_clauses⦎ =
   ⊢ ∀ x
     ⦁ x ∈ Syntax
         ⇒ (IsAf x ⇒ (∃ r pars⦁ fun pars ∧ x = MkAf (r, pars)))
           ∧ (IsCf x
             ⇒ (∃ vars fs
             ⦁ (∀ y⦁ y ∈⋎g fs ⇒ y ∈ Syntax) ∧ x = MkCf (vars, fs)))

⦏syn_proj_clauses⦎ =
    ⊢ (∀ l r⦁ AfRel (MkAf (l, r)) = l)
       ∧ (∀ l r⦁ AfPars (MkAf (l, r)) = r)
       ∧ (∀ v f⦁ CfVars (MkCf (v, f)) = v)
       ∧ (∀ v f⦁ CfForms (MkCf (v, f)) = f)

⦏is_fc_clauses2⦎ =
   ⊢ ∀ x⦁ x ∈ Syntax ⇒ IsCf x ⇒ (∀ y⦁ y ∈⋎g CfForms x ⇒ y ∈ Syntax)

⦏stn_con_neq_clauses⦎ =
   ⊢ ∀ x y⦁ ¬ MkAf x = MkCf y

⦏syn_comp_fc_clauses⦎ =
   ⊢ ∀ v f⦁ MkCf (v, f) ∈ Syntax ⇒ (∀ y⦁ y ∈⋎g f ⇒ y ∈ Syntax)

⦏scprec_fc_clauses⦎ =
   ⊢ ∀ α γ vars fs⦁ γ ∈ Syntax ⇒ γ = MkCf (vars, fs) ∧ α ∈⋎g fs ⇒ ScPrec α γ

⦏scprec_fc_clauses2⦎ =
   ⊢ ∀ t⦁ t ∈ Syntax ⇒ IsCf t ⇒ (∀ f⦁ f ∈⋎g CfForms t ⇒ ScPrec f t)
=TEX

\ignore{
=SML
set_goal([], ⌜∀x⦁	x ∈ Syntax
⇒	(∃r pars⦁ fun pars ∧ x = MkAf (r,pars))
  ∨	(∃vars fs⦁ (∀y⦁ y ∈⋎g fs ⇒ y ∈ Syntax) ∧ x = MkCf (vars, fs))
⌝);
a (contr_tac);
a (lemma_tac ⌜RepClosed (Syntax \ {x})⌝
	THEN1 (rewrite_tac [get_spec ⌜RepClosed⌝]
		THEN strip_tac));
(* *** Goal "1" *** *)
a (strip_tac THEN strip_tac THEN strip_tac
	THEN all_fc_tac [repclosed_syntax_thm]
	THEN_TRY asm_rewrite_tac[]);
a (spec_nth_asm_tac 4 ⌜n⌝);
a (spec_nth_asm_tac 1 ⌜is⌝ THEN1 asm_fc_tac[]);
a (swap_nth_asm_concl_tac 1 THEN (SYM_ASMS_T rewrite_tac));
(* *** Goal "2" *** *)
a (REPEAT_N 3 strip_tac);
a (spec_nth_asm_tac 2 ⌜vars⌝);
a (DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac [get_spec ⌜X⋎g⌝]
	THEN strip_tac);
a (lemma_tac ⌜∀ y⦁ y ∈⋎g fs ⇒ y ∈ Syntax⌝
	THEN1 (REPEAT strip_tac THEN all_asm_fc_tac[]));
a (all_fc_tac [rewrite_rule [get_spec ⌜X⋎g⌝] repclosed_syntax_thm]);
a (asm_rewrite_tac[]);
a (spec_nth_asm_tac 4 ⌜fs⌝);
(* *** Goal "2.1" *** *)
a (asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (asm_tac repclosed_syntax_lemma1);
a (spec_nth_asm_tac 1 ⌜Syntax \ {x}⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
val syntax_disj_thm = save_pop_thm "syntax_disj_thm";

set_goal([], ⌜∀x⦁ x ∈ Syntax ⇒ IsAf x ∨ IsCf x⌝);
a (REPEAT_N 2 strip_tac THEN fc_tac [syntax_disj_thm]
	THEN asm_rewrite_tac[]);
val syntax_cases_thm = save_pop_thm "syntax_cases_thm";

set_goal([], ⌜∀x⦁	x ∈ Syntax
⇒	(IsAf x ⇒ ∃r pars⦁ fun pars ∧ x = MkAf (r, pars))
∧	(IsCf x ⇒ ∃vars fs⦁ (∀y⦁ y ∈⋎g fs ⇒ y ∈ Syntax) ∧ x = MkCf (vars, fs))
⌝);
a (REPEAT_N 2 strip_tac);
a (asm_tac (syntax_disj_thm));
a (asm_fc_tac[] THEN asm_rewrite_tac [Is_clauses]);
(* *** Goal "1" *** *)
a (∃_tac ⌜r⌝ THEN ∃_tac ⌜pars⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜vars⌝ THEN ∃_tac ⌜fs⌝ THEN asm_rewrite_tac[]);
val is_fc_clauses = save_pop_thm "is_fc_clauses";

set_goal([], ⌜(∀l r⦁ AfRel (MkAf (l, r)) = l)
	∧	(∀l r⦁ AfPars (MkAf (l, r)) = r)
	∧	(∀v f⦁ CfVars (MkCf (v, f)) = v)
	∧	(∀v f⦁ CfForms (MkCf (v, f)) = f)
⌝);
a (rewrite_tac (map get_spec [
	⌜MkAf⌝, ⌜MkCf⌝,
	⌜AfRel⌝, ⌜AfPars⌝, ⌜CfVars⌝, ⌜CfForms⌝]));
val syn_proj_clauses = save_pop_thm "syn_proj_clauses";

add_pc_thms "'ifol" [syn_proj_clauses];
set_merge_pcs ["hol1", "'GS1", "'misc1", "'misc2", "'ifol"];

set_goal([], ⌜∀x⦁	x ∈ Syntax
⇒	(IsCf x ⇒ (∀y⦁ y ∈⋎g (CfForms x) ⇒ y ∈ Syntax))
⌝);
a (REPEAT strip_tac
	THEN all_fc_tac [is_fc_clauses]
	THEN GET_NTH_ASM_T 1 (var_elim_asm_tac o concl)
	THEN_TRY asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 2 (asm_tac o (rewrite_rule[]))
	THEN all_asm_fc_tac[]);
val is_fc_clauses2 = save_pop_thm "is_fc_clauses2";

set_goal([], ⌜∀x y⦁ ¬ MkAf x = MkCf y⌝);
a (rewrite_tac (map get_spec [⌜MkAf⌝, ⌜MkCf⌝]));
val syn_con_neq_clauses = save_pop_thm "syn_con_neq_clauses";

add_pc_thms "'ifol" [syn_con_neq_clauses];
set_merge_pcs ["hol1", "'GS1", "'misc1", "'misc2", "'ifol"];

set_goal([], ⌜
	(∀v f⦁ MkCf (v, f) ∈ Syntax ⇒ (∀y⦁ y ∈⋎g f ⇒ y ∈ Syntax))⌝);
a (REPEAT strip_tac
	THEN FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule []))) [is_fc_clauses2]
	THEN asm_fc_tac[]);
val syn_comp_fc_clauses = save_pop_thm "syn_comp_fc_clauses";

set_goal([], ⌜∀α γ vars fs⦁ γ ∈ Syntax ⇒
		(γ = MkCf (vars, fs) ∧ α ∈⋎g fs) ⇒ ScPrec α γ
⌝);
a (rewrite_tac [get_spec ⌜ScPrec⌝]);
a (REPEAT ∀_tac THEN strip_tac THEN strip_tac);
a (∃_tac ⌜vars⌝ THEN ∃_tac ⌜fs⌝ THEN asm_rewrite_tac[]);
a (REPEAT strip_tac THEN var_elim_nth_asm_tac 1);
(* *** Goal "1" *** *)
a (var_elim_nth_asm_tac 2);
a (fc_tac [syn_comp_fc_clauses]);
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (var_elim_nth_asm_tac 2);
val scprec_fc_clauses = save_pop_thm "scprec_fc_clauses";

set_goal ([], ⌜∀t⦁ t ∈ Syntax ⇒ 
	(IsCf t ⇒ ∀f⦁ f ∈⋎g CfForms t ⇒ ScPrec (f) t)⌝);
a (REPEAT strip_tac
	THEN all_fc_tac [is_fc_clauses]
	THEN DROP_NTH_ASM_T 3 ante_tac
	THEN asm_rewrite_tac[]
	THEN strip_tac
	THEN all_fc_tac [scprec_fc_clauses]
	THEN POP_ASM_T ante_tac
	THEN_TRY asm_rewrite_tac []);
val scprec_fc_clauses2 = save_pop_thm "scprec_fc_clauses2";
=TEX
}%ignore

\subsection{Semantics}

The semantics of infinitary first order logic is given by defining ``truth in an interpretation''.

\subsubsection{Domains}

We consider here some of the value domains which are significant in the semantics.

The following type abbreviations are introduced:

\begin{description}
\item{RV}
Relation Value - the arguments to a relation can be represented by indexed sets (think of the indices as parameter names), and a relation is then a truth valued function over these indexed sets (a set of indexed sets won't do because we have three truth values).
Note that relations need not have a definite arity, and the function representing a relation must be total over the entire type of indexed sets.
There are questions about how best ordinary n-ary relations should be represented, one obvious choice would be to make the truth value undefined for any indexed sets which do not have exactly the right number of numerical indices.
\item{ST}
Structure = a structure is a domain of disccourse (a set) together with an indexed set of relations over that domain.
Ordinals are used for relation names as well as for variable names (no ambiguity arises) and a collection of relations can therefore be modelled in the same way as a relation valued variable assignment.
\end{description}

=SML
declare_type_abbrev("⦏RV⦎", ["'a","'b"], ⓣ'a IS → 'b⌝);
declare_type_abbrev("⦏ST⦎", ["'a","'b"], ⓣ'a SET × ('a, 'b) RV IS⌝);
=TEX

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
set_goal([], ⌜∀r⦁ LubsExist r ⇒ LubsExist (RvO r)⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜RvO⌝]
	THEN bc_tac [pw_lubs_exist_thm]
	THEN strip_tac);
val rvo_lubs_exist_thm = save_pop_thm "rvo_lubs_exist_thm";

set_goal([], ⌜∀r⦁ GlbsExist r ⇒ GlbsExist (RvO r)⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜RvO⌝]
	THEN bc_tac [pw_glbs_exist_thm]
	THEN strip_tac);
val rvo_glbs_exist_thm = save_pop_thm "rvo_glbs_exist_thm";
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
set_goal([], ⌜∀r⦁ LubsExist r ⇒ LubsExist (RvIsO r)⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜RvIsO⌝]
	THEN bc_tac [is_lubs_exist_thm]
	THEN bc_tac [rvo_lubs_exist_thm]
	THEN strip_tac);
val rviso_lubs_exist_thm = save_pop_thm "rviso_lubs_exist_thm";

set_goal([], ⌜∀r⦁ GlbsExist r ⇒ GlbsExist (RvIsO r)⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜RvIsO⌝]
	THEN bc_tac [is_glbs_exist_thm]
	THEN bc_tac [rvo_glbs_exist_thm]
	THEN strip_tac);
val rviso_glbs_exist_thm = save_pop_thm "rviso_glbs_exist_thm";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏StO⦎ : ('b → 'b → BOOL) → ('a, 'b) ST → ('a, 'b) ST → BOOL
├───────────
│ ∀r⦁ StO r = DerivedOrder Snd (IsEO (RvO r))
■

=GFT
⦏sto_lubs_exist_thm⦎ =
	⊢ ∀ r⦁ LubsExist r ⇒ LubsExist (StO r)

⦏sto_glbs_exist_thm⦎ =
	⊢ ∀ r⦁ GlbsExist r ⇒ GlbsExist (StO r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ LubsExist r ⇒ LubsExist (StO r)⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜StO⌝]
	THEN bc_tac [lubsexist_dosnd_thm]
	THEN bc_tac [is_lubs_exist_thm]
	THEN bc_tac [rvo_lubs_exist_thm]
	THEN strip_tac);
val sto_lubs_exist_thm = save_pop_thm "sto_lubs_exist_thm";

set_goal([], ⌜∀r⦁ GlbsExist r ⇒ GlbsExist (StO r)⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜StO⌝]
	THEN bc_tac [glbsexist_dosnd_thm]
	THEN bc_tac [is_glbs_exist_thm]
	THEN bc_tac [rvo_glbs_exist_thm]
	THEN strip_tac);
val sto_glbs_exist_thm = save_pop_thm "sto_glbs_exist_thm";
=TEX
}%ignore

\ignore{
[not in use]

 ⓈHOLCONST
│ ⦏StrictFun⦎ : ('a → 'b) DPO → 'a DPO → 'b DPO
├───────────
│ ∀f⦁ StrictFun f = λx⦁
	if dpoUdef f
	then dpoB
	else
		if dpoOdef f
		then dpoT
		else
			if dpoUdef x
			then dpoB
			else
				if dpoOdef x
				then dpoT
				else dpoE (dpoV f (dpoV x))
 ■
}%ignore

\subsubsection{Manipulating Valuations}

In this syntax, by contrast with that in \cite{rbjt021}, we do not require variables to be ordinals, they may be arbitrary sets, since no steps are necessary to avoid variable capture.
There was no need even in \cite{rbjt021}, the use of a transfinite version of DeBriujn indices was a hang over from the PolySets where something of the kind really was needed.

This function is used in the evaluation of atomic formulae.
Given a set of indices (the names of actual parameters to an atomic formula, which are always variables) and an indexed set (the values of the variables) this function returns an indexed set which contains the values for the actual parameters to the relation.

ⓈHOLCONST
│ ⦏VarComp⦎ : GS → 'a IS → 'a IS
├───────────
│ ∀m is⦁ VarComp m is = 
│	λv⦁ if v ∈⋎g dom m then is (m ⋎g v) else dpoB
■

\subsubsection{Formula Evaluation}

Now we define the evaluation of formulae, i.e. the notion of truth in a structure given a variable assignment.

There are two cases in the syntax, atomic and compound formulae.
The truth values of the atomic formulae are obtained from an infinitary structure given the values of the arguments, which are always variables, i.e. to evaluate an atomic formula you look up the values of the arguments in the current context (variable assignment) and then look up the truth value of the stipulated relation for those arguments in the structure.

ⓈHOLCONST
│ ⦏EvalAf⦎ : 't REL → GS → ('a, 't) ST → ('a, 't) RV
├───────────
│ ∀$≤⋎t (at:GS) (st:('a, 't) ST) (va:'a IS)⦁ EvalAf $≤⋎t at st va =
│	let r = AfRel at
│	and pars = AfPars at
│	in 
│		let rv = (Snd st) r
│		in
│			if dpoUdef rv
│			then Lub $≤⋎t {}
│			else
│				if dpoOdef rv
│				then Glb $≤⋎t {}
│				else (dpoV rv) (VarComp pars va)
■

To evaluate a compound formula you must first evaluate the constituent formulae in every context obtable by modification of the variables bound by the compound formula.
You need only remember the resulting truth values, the compound formulae are in this sense ``truth functional'', and, though this may involve evaluating a very large number of instances of subformulae, it can only yield some subset of
=INLINEFT
{pTrue, pFalse, pU}
=TEX
.

The following definition shows how the truth values of the constituents of a compound formula then determines the truth value of the compound formula.

=SML
declare_type_abbrev("⦏CFE⦎", ["'t"], ⓣ't SET → 't⌝);
=TEX

ⓈHOLCONST
│ ⦏EvalCf_tf3⦎ : TTV CFE
├───────────
│ ∀results⦁ EvalCf_tf3 results = 
│	if results ⊆ {pTrue} then pFalse
│		else if (pFalse) ∈ results then pTrue
│		else pU
■

ⓈHOLCONST
│ ⦏EvalCf_tf4⦎ : FTV CFE
├───────────
│ ∀results⦁ EvalCf_tf4 results = 
│	if results ⊆ {fTrue} then fFalse
│		else if results ⊆ {fTrue; fB} then fB
│		else if fT ∈ results then fT else fTrue
■



This definition shows how the set of truth values of instances of the constituents is obtained from the denotations of the constituent formulae.

ⓈHOLCONST
│ ⦏EvalCf⦎ : 't CFE → GS → ('a, 't) ST → ('a, 't) RV SET → ('a, 't) RV
├───────────
│ ∀etf f⦁ EvalCf etf f = λst rvs va⦁ 
│	let ν = CfVars f
│	and V = Fst st
│	in etf {pb | ∃rv v⦁
│		  rv ∈ rvs
│		∧ IsDom v = X⋎g ν
│		∧ IsRan v ⊆ V
│		∧ pb = rv (IsOverRide v va)}
■

Now we define a parameterised functor of which the semantic function is a fixed point.

ⓈHOLCONST
│ ⦏EvalFormFunct⦎ : 't CFE × 't REL × ('a, 't) ST → (GS → ('a, 't) RV) → (GS → ('a, 't) RV)
├───────────
│ ∀cfe $≤⋎t st⦁ EvalFormFunct (cfe, $≤⋎t, st) = λef f⦁
│	if f ∈ Syntax
│	then if IsAf f
│	     then EvalAf $≤⋎t f st
│	     else
│		if IsCf f
│		then let rvs = FunImage ef (X⋎g(CfForms f))
│		     in  EvalCf cfe f st rvs
│		else εx⦁T
│	else εx⦁T
■

ⓈHOLCONST
│ ⦏EvalForm⦎ : 't CFE × 't REL × ('a, 't) ST → GS → ('a, 't) RV
├───────────
│ ∀cfe $≤⋎t st⦁ EvalForm (cfe, $≤⋎t, st) = fix (EvalFormFunct (cfe, $≤⋎t, st))
■

To use this definition we need to show that there exists a fixed point, for which we must show that the functor respects some well-founded relation.

=GFT
⦏evalformfunct_respect_thm⦎ =
   ⊢ ∀ (V, r)⦁ EvalFormFunct (V, r) respects ScPrec

⦏evalformfunct_fixp_lemma⦎ =
   ⊢ ∀ st⦁ EvalForm st = EvalFormFunct st (EvalForm st)

⦏evalformfunct_thm⦎ =
   ⊢ ∀ st
     ⦁ EvalForm st
         = (λ f
         ⦁ if f ∈ Syntax
           then
             if IsAf f
             then EvalAf f st
             else if IsCf f
             then
               let rvs = FunImage (EvalForm st) (X⋎g (CfForms f))
               in EvalCf f st rvs
             else ε x⦁ T
           else ε x⦁ T)

⦏evalformfunct_thm2⦎ =
   ⊢ ∀ st f
     ⦁ EvalForm st f
         = (if f ∈ Syntax
           then
             if IsAf f
             then EvalAf f st
             else if IsCf f
             then
               let rvs = FunImage (EvalForm st) (X⋎g (CfForms f))
               in EvalCf f st rvs
             else ε f⦁ T
           else ε f⦁ T)
=TEX

\ignore{
=SML
set_merge_pcs ["hol", "'GS1", "'misc1", "'misc2", "'ifol"];

set_goal([], ⌜∀cfe $≤⋎t st⦁ (EvalFormFunct (cfe, $≤⋎t, st)) respects ScPrec⌝);
a (rewrite_tac [get_spec ⌜EvalFormFunct⌝, get_spec ⌜$respects⌝]
	THEN REPEAT strip_tac);
a (cases_tac ⌜IsAf x⌝ THEN asm_rewrite_tac[]);
a (cases_tac ⌜IsCf x⌝ THEN asm_rewrite_tac[]);
a (cases_tac ⌜x ∈ Syntax⌝ THEN asm_rewrite_tac[]);
a (lemma_tac ⌜FunImage g (X⋎g (CfForms x)) = FunImage h (X⋎g (CfForms x))⌝
	THEN_TRY asm_rewrite_tac[get_spec ⌜X⋎g⌝]);
a (PC_T1 "hol1" rewrite_tac [get_spec ⌜FunImage⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [scprec_fc_clauses2]);
a (all_asm_fc_tac[tc_incr_thm]);
a (all_asm_fc_tac[]);
a (∃_tac ⌜a⌝ THEN asm_rewrite_tac[]);
a (POP_ASM_T (fn x => rewrite_thm_tac (eq_sym_rule x)));
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac [scprec_fc_clauses2]);
a (all_asm_fc_tac[tc_incr_thm]);
a (all_asm_fc_tac[]);
a (∃_tac ⌜a⌝ THEN asm_rewrite_tac[]);
val evalformfunct_respect_thm = save_pop_thm "evalformfunct_respect_thm";

set_goal([], ⌜∀cfe $≤⋎t st⦁ EvalForm (cfe, $≤⋎t, st) = EvalFormFunct (cfe, $≤⋎t, st) (EvalForm (cfe, $≤⋎t, st))⌝);
a (asm_tac well_founded_ScPrec_thm);
a (asm_tac evalformfunct_respect_thm);
a (REPEAT ∀_tac);
a (list_spec_nth_asm_tac 1 [⌜cfe⌝, ⌜$≤⋎t⌝, ⌜st⌝]);
a (all_fc_tac [∀_elim ⌜ScPrec⌝ (∀_elim ⌜EvalFormFunct (cfe, $≤⋎t, st)⌝ (get_spec ⌜fix⌝))]);
a (rewrite_tac [get_spec ⌜EvalForm⌝]);
a (asm_rewrite_tac[]);
val evalformfunct_fixp_lemma = save_pop_thm "evalformfunct_fixp_lemma";

val evalformfunct_thm = save_thm ("evalformfunct_thm",
	rewrite_rule [get_spec ⌜EvalFormFunct⌝] evalformfunct_fixp_lemma);

set_goal([], ⌜∀ cfe $≤⋎t st f
     ⦁ EvalForm (cfe, $≤⋎t, st) f
         = if f ∈ Syntax
             then
               if IsAf f
               then EvalAf $≤⋎t f st
               else if IsCf f
               then
                 let rvs = FunImage (EvalForm (cfe, $≤⋎t, st)) (X⋎g (CfForms f))
                 in EvalCf cfe f st rvs
               else ε f⦁ T
             else ε f⦁ T⌝);
a (REPEAT strip_tac THEN rewrite_tac[rewrite_rule [](once_rewrite_rule [ext_thm] evalformfunct_thm)]);
val evalformfunct_thm2 = save_pop_thm "evalformfunct_thm2";
=TEX
}%ignore

\subsubsection{Some Orderings}

In order to prove that the semantics is monotonic, we must first define the partial orderings relative to which the semantics is monotonic, and we must obtain fixpoint theorems for the orderings.

We have at present two cases under consideration, according to whether three or four truth values are adopted.

The three valued case turns out in some respects more complex than the four valued case, because it is necessary to make do with chain completeness and the fixed point theorem is more difficult to prove.
I will therefore progress only the four valued case until I find a reason to further progress the three valued case.

Here is the beginning of the three valued case which I started before.

It is also necessary to prove that these partial orderings are CCPOs (chain complete partial orders), this being the weakest condition for which we have a suitable fixed point theorem.
It is convenient to be slightly more definite, to make the orderings all reflexive, and show that they are reflexive CCPOs (for which we use the term CCRPO).

The following ordering is applicable to partial relations.

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
set_goal([], ⌜CcRpoU $≤⋎f⋎t⋎3⌝);
a (rewrite_tac [get_spec ⌜$≤⋎f⋎t⋎3⌝]);
a (asm_tac ccrpou_≤⋎t⋎3_thm);
a (fc_tac [pw_ccrpou_thm]);
val ccrpou_≤⋎f⋎t⋎3_thm = save_pop_thm "ccrpou_≤⋎f⋎t⋎3_thm";
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
⦏ccrpou_≤⋎f⋎t⋎4_thm⦎ =
	⊢  $≤⋎f⋎t⋎4
=TEX

\ignore{
=IGN
set_goal([], ⌜CcRpoU $≤⋎f⋎t⋎3⌝);
a (rewrite_tac [get_spec ⌜$≤⋎f⋎t⋎3⌝]);
a (asm_tac ccrpou_≤⋎t⋎3_thm);
a (fc_tac [pw_ccrpou_thm]);
val ccrpou_≤⋎f⋎t⋎3_thm = save_pop_thm "ccrpou_≤⋎f⋎t⋎3_thm";
=TEX
}%ignore


=GFT
⦏evalcf_tf4_increasing_lemma⦎ =
   ⊢ Increasing (SetO $≤⋎t⋎4) $≤⋎t⋎4 EvalCf_tf4
=TEX

\ignore{
=SML
set_goal([], ⌜Increasing (SetO $≤⋎t⋎4) $≤⋎t⋎4 EvalCf_tf4⌝);
a (rewrite_tac (map get_spec [⌜Increasing⌝, ⌜SetO⌝, ⌜$≤⋎t⋎4⌝, ⌜EvalCf_tf4⌝]));
a (REPEAT_N 3 strip_tac THEN_TRY asm_rewrite_tac[]);
a (cases_tac ⌜y ⊆ {fTrue}⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (cases_tac ⌜x ⊆ {fTrue}⌝ THEN_TRY asm_rewrite_tac[]);
a (POP_ASM_T (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (all_asm_fc_tac[]);
(* *** Goal "1.1" *** *)
a (var_elim_asm_tac ⌜x' = y'⌝);
a (DROP_NTH_ASM_T 4 (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (all_asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a (var_elim_asm_tac ⌜x' = fB⌝ THEN_TRY asm_rewrite_tac[]);
a (cases_tac ⌜x ⊆ {fTrue; fB}⌝ THEN_TRY asm_rewrite_tac[]);
a (POP_ASM_T (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm)
	THEN	var_elim_nth_asm_tac 1);
(* *** Goal "1.2.1" *** *)
a (spec_nth_asm_tac 9 ⌜fFalse⌝);
(* *** Goal "1.2.1.1" *** *)
a (lemma_tac ⌜fFalse ∈ y⌝
	THEN1 (asm_rewrite_tac[]));
a (DROP_NTH_ASM_T 10 (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (all_asm_fc_tac[]);
(* *** Goal "1.2.1.2" *** *)
a (lemma_tac ⌜fT ∈ y⌝
	THEN1 (SYM_ASMS_T rewrite_tac));
a (DROP_NTH_ASM_T 10 (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (all_asm_fc_tac[]);
(* *** Goal "1.2.2" *** *)
a (spec_nth_asm_tac 9 ⌜fT⌝);
(* *** Goal "1.2.2.1" *** *)
a (lemma_tac ⌜fT ∈ y⌝
	THEN1 (asm_rewrite_tac[]));
a (DROP_NTH_ASM_T 10 (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (all_asm_fc_tac[]);
(* *** Goal "1.2.2.2" *** *)
a (lemma_tac ⌜fT ∈ y⌝
	THEN1 (SYM_ASMS_T rewrite_tac));
a (DROP_NTH_ASM_T 10 (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (all_asm_fc_tac[]);
(* *** Goal "1.3" *** *)
a (var_elim_asm_tac ⌜y' = fT⌝ THEN_TRY asm_rewrite_tac[]);
a (cases_tac ⌜x ⊆ {fTrue; fB}⌝ THEN_TRY asm_rewrite_tac[]);
a (POP_ASM_T (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (strip_asm_tac (∀_elim ⌜x''⌝ ftv_cases_thm)
	THEN	var_elim_nth_asm_tac 1);
(* *** Goal "1.3.1" *** *)
a (spec_nth_asm_tac 9 ⌜fFalse⌝);
(* *** Goal "1.3.1.1" *** *)
a (lemma_tac ⌜fFalse ∈ y⌝
	THEN1 (asm_rewrite_tac[]));
a (DROP_NTH_ASM_T 10 (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (all_asm_fc_tac[]);
(* *** Goal "1.3.1.2" *** *)
a (DROP_NTH_ASM_T 9 (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (all_asm_fc_tac[]);
(* *** Goal "1.3.2" *** *)
a (DROP_NTH_ASM_T 7 (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (cases_tac ⌜x ⊆ {fTrue}⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (cases_tac ⌜y ⊆ {fTrue; fB}⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1.1" *** *)
a (lemma_tac ⌜fB ∈ y⌝
	THEN1 (GET_NTH_ASM_T 1 ante_tac
		THEN GET_NTH_ASM_T 3 ante_tac
		THEN PC_T1 "hol1" rewrite_tac[]
		THEN REPEAT strip_tac
		THEN asm_fc_tac[]
		THEN var_elim_nth_asm_tac 1));
a (spec_nth_asm_tac 5 ⌜fB⌝);
(* *** Goal "2.1.1.1" *** *)
a (DROP_NTH_ASM_T 5 (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (var_elim_nth_asm_tac 2 THEN asm_fc_tac []);
(* *** Goal "2.1.2" *** *)
a (cases_tac ⌜fT ∈ y⌝ THEN asm_rewrite_tac[]);
a (lemma_tac ⌜fFalse ∈ y⌝);
(* *** Goal "2.1.2.1" *** *)
a (GET_NTH_ASM_T 2 ante_tac THEN (PC_T1 "hol1" rewrite_tac[])
	THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm)
	THEN	var_elim_nth_asm_tac 1);
(* *** Goal "2.1.2.2" *** *)
a (spec_nth_asm_tac 6 ⌜fFalse⌝);
(* *** Goal "2.1.2.2.1" *** *)
a (GET_NTH_ASM_T 6 ante_tac THEN (PC_T1 "hol1" rewrite_tac[])
	THEN contr_tac);
a (var_elim_nth_asm_tac 2
	THEN all_asm_fc_tac[]);
(* *** Goal "2.1.2.2.2" *** *)
a (var_elim_nth_asm_tac 1);
a (DROP_NTH_ASM_T 5 (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (cases_tac ⌜y ⊆ {fTrue; fB}⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.1" *** *)
a (lemma_tac ⌜fB ∈ y⌝
	THEN1 (GET_NTH_ASM_T 1 ante_tac
		THEN GET_NTH_ASM_T 3 ante_tac
		THEN PC_T1 "hol1" rewrite_tac[]
		THEN REPEAT strip_tac
		THEN asm_fc_tac[]
		THEN var_elim_nth_asm_tac 1));
a (cases_tac ⌜x ⊆ {fTrue; fB}⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.1.1" *** *)
a (DROP_NTH_ASM_T 1 (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm)
	THEN	var_elim_nth_asm_tac 1);
a (spec_nth_asm_tac 9 ⌜fFalse⌝);
(* *** Goal "2.2.1.1.1" *** *)
a (lemma_tac ⌜fFalse ∈ y⌝
	THEN1 asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 8 (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (spec_nth_asm_tac 1 ⌜fFalse⌝);
(* *** Goal "2.2.1.1.2" *** *)
a (var_elim_nth_asm_tac 1);
a (DROP_NTH_ASM_T 6 (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (spec_nth_asm_tac 1 ⌜fT⌝);
(* *** Goal "2.2.1.2" *** *)
a (DROP_NTH_ASM_T 5 (strip_asm_tac o (pc_rule1 "hol1" rewrite_rule[])));
a (spec_nth_asm_tac 1 ⌜fT⌝);
a (spec_nth_asm_tac 10 ⌜fT⌝);
(* *** Goal "2.2.1.2.1" *** *)
a (DROP_NTH_ASM_T 3 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.1.2.2" *** *)
a (DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a (cases_tac ⌜x ⊆ {fTrue; fB}⌝ THEN_TRY asm_rewrite_tac[]);
a (cases_tac ⌜fT ∈ y⌝ THEN_TRY asm_rewrite_tac[]);
a (cases_tac ⌜fT ∈ x⌝ THEN_TRY asm_rewrite_tac[]);
a (spec_nth_asm_tac 8 ⌜fT⌝);
(* *** Goal "2.2.2.1" *** *)
a (DROP_NTH_ASM_T 4 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2" *** *)
a (DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[]);
val evalcf_tf4_increasing_lemma = pop_thm ();
=TEX
}%ignore


\subsubsection{Monotonicity}

=GFT
⦏evalaf_increasing_lemma⦎ =
   ⊢ ∀ tr g⦁ CRpoU tr ⇒ Increasing (StO tr) (RvO tr) (EvalAf tr g)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ tr g⦁ CRpoU tr ⇒ Increasing (StO tr) (RvO tr) (EvalAf tr g)⌝);
a (rewrite_tac (map get_spec [⌜Increasing⌝, ⌜EvalAf⌝, ⌜StO⌝, ⌜RvO⌝,
	⌜Pw⌝, ⌜DerivedOrder⌝, ⌜IsEO⌝, ⌜DpoEO⌝, ⌜dpoUdef⌝, ⌜dpoOdef⌝])
	THEN REPEAT strip_tac);
a (rewrite_tac [let_def]);
a (spec_nth_asm_tac 1 ⌜AfRel g⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (fc_tac [crpou_lub_glb_∅_lemma] THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [crpou_lub_glb_∅_lemma] THEN_TRY asm_rewrite_tac[]);
val evalaf_increasing_lemma = pop_thm();
=TEX
}%ignore

To get a monontonicity result for the semantics of first order logic it is necessary to adjust the type of the semantic function.

The function which we wish to be monotonic is the mappings for each fixed domain of discourse and each particular formula, which take an indexed set of relations (corresponding to some interpretation over the gived domain) and return the relation represented by the formulae in that context.

The following function accepts one compound argument containing the relevent context and yields a function which we expect to be monotonic:

ⓈHOLCONST
│ ⦏MonoEvalForm⦎ : 't CFE × 't REL × 'a SET × GS → ('a, 't) RV IS → ('a, 't) RV
├───────────
│ ∀c r s g ris⦁ MonoEvalForm (c, r, s, g) ris = EvalForm (c, r, (s, ris)) g
■

=GFT
⦏monoevalform_increasing_lemma⦎ =
   ⊢ ∀ c r s g
     ⦁ CRpoU r ∧ Increasing (SetO r) r c
         ⇒ Increasing (RvIsO r) (RvO r) (MonoEvalForm (c, r, s, g))

⦏evalform_increasing_thm⦎ =
   ⊢ ∀ c r s g
     ⦁ CRpoU r ∧ Increasing (SetO r) r c
         ⇒ Increasing (RvIsO r) (RvO r) (λ ris⦁ EvalForm (c, r, s, ris) g)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀c r s g⦁ CRpoU r ∧ Increasing (SetO r) r c
	⇒ Increasing (RvIsO r) (RvO r) (MonoEvalForm (c,r,s,g))⌝);
a (REPEAT strip_tac);
a (sc_induction_tac ⌜g⌝ THEN_TRY asm_rewrite_tac[]);
a (rewrite_tac ((map get_spec [⌜Increasing⌝, ⌜MonoEvalForm⌝, ⌜RvO⌝, ⌜RvIsO⌝])@[evalformfunct_thm2])
	THEN REPEAT strip_tac);
a (cases_tac ⌜t ∈ Syntax⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (cases_tac ⌜IsAf t⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a (fc_tac [inst_type_rule [(ⓣ'a⌝, ⓣ'b⌝), (ⓣ'b⌝, ⓣ'a⌝)] evalaf_increasing_lemma]);
a (spec_nth_asm_tac 1 ⌜t⌝ THEN fc_tac [get_spec ⌜Increasing⌝]);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec⌜StO⌝,get_spec⌜RvO⌝,
	get_spec ⌜DerivedOrder⌝] THEN strip_tac);
a (LIST_SPEC_NTH_ASM_T 1 [⌜(s,x)⌝, ⌜(s,y)⌝] ante_tac
	THEN rewrite_tac[]
	THEN strip_tac);
(* *** Goal "1.2" *** *)
a (cases_tac ⌜IsCf t⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2.1" *** *)
a (rewrite_tac ((map get_spec [⌜Pw⌝, ⌜X⋎g⌝, ⌜EvalCf⌝])@[let_def]));
a (strip_tac THEN FC_T bc_tac [get_spec ⌜Increasing⌝]);
a (rewrite_tac [get_spec ⌜SetO⌝] THEN REPEAT strip_tac);
(* *** Goal "1.2.1.1" *** *)
a (GET_NTH_ASM_T 4 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
a (∃_tac ⌜EvalForm (c, r, s, y) a (IsOverRide v x')⌝
	THEN strip_tac);
(* *** Goal "1.2.1.1.1" *** *)
a (∃_tac ⌜EvalForm (c, r, s, y) a⌝);
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[get_spec ⌜FunImage⌝]);
a (∃_tac ⌜a⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2.1.1.2" *** *)
a (asm_rewrite_tac[]);
a (GET_NTH_ASM_T 1 (rewrite_thm_tac o eq_sym_rule));
a (lemma_tac ⌜tc ScPrec a t⌝);
(* *** Goal "1.2.1.1.2.1" *** *)
a (fc_tac [scprec_fc_clauses]);
a (all_fc_tac [is_fc_clauses2]);
a (all_fc_tac [scprec_fc_clauses2]);
a (fc_tac [tc_incr_thm]);
(* *** Goal "1.2.1.1.2.2" *** *)
a (all_asm_fc_tac[]);
a (fc_tac[get_spec ⌜Increasing⌝]);
a (GET_NTH_ASM_T 1 ante_tac THEN rewrite_tac [get_spec ⌜RvIsO⌝, get_spec ⌜RvO⌝]
	THEN STRIP_T (fn x => fc_tac[x]));
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜MonoEvalForm⌝, get_spec ⌜Pw⌝]
	THEN STRIP_T rewrite_thm_tac);
(* *** Goal "1.2.1.2" *** *)
a (GET_NTH_ASM_T 4 (strip_asm_tac o (rewrite_rule [get_spec ⌜FunImage⌝])));
a (∃_tac ⌜EvalForm (c, r, s, x) a (IsOverRide v x')⌝
	THEN strip_tac);
(* *** Goal "1.2.1.2.1" *** *)
a (∃_tac ⌜EvalForm (c, r, s, x) a⌝);
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[get_spec ⌜FunImage⌝]);
a (∃_tac ⌜a⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2.1.2.2" *** *)
a (asm_rewrite_tac[]);
a (GET_NTH_ASM_T 1 (rewrite_thm_tac o eq_sym_rule));
a (lemma_tac ⌜tc ScPrec a t⌝);
(* *** Goal "1.2.1.2.2.1" *** *)
a (fc_tac [scprec_fc_clauses]);
a (all_fc_tac [is_fc_clauses2]);
a (all_fc_tac [scprec_fc_clauses2]);
a (fc_tac [tc_incr_thm]);
(* *** Goal "1.2.1.2.2.2" *** *)
a (all_asm_fc_tac[]);
a (fc_tac[get_spec ⌜Increasing⌝]);
a (GET_NTH_ASM_T 1 ante_tac THEN rewrite_tac [get_spec ⌜RvIsO⌝, get_spec ⌜RvO⌝]
	THEN STRIP_T (fn x => fc_tac[x]));
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜MonoEvalForm⌝, get_spec ⌜Pw⌝]
	THEN STRIP_T rewrite_thm_tac);
(* *** Goal "1.2.2" *** *)
a (fc_tac [inst_type_rule [(ⓣ'a⌝, ⓣ'b⌝), (ⓣGS → 'b DPO⌝, ⓣ'a⌝)] pw_crpou_thm]);
a (fc_tac [crpou_fc_clauses] THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [inst_type_rule [(ⓣ'a⌝, ⓣ'b⌝), (ⓣGS → 'b DPO⌝, ⓣ'a⌝)] pw_crpou_thm]);
a (fc_tac [crpou_fc_clauses] THEN asm_rewrite_tac[]);
val monoevalform_increasing_lemma = pop_thm ();

set_goal([], ⌜∀ c r s g
     ⦁ CRpoU r ∧ Increasing (SetO r) r c
         ⇒ Increasing (RvIsO r) (RvO r) (λris⦁EvalForm (c, r, s, ris) g)⌝);
a (REPEAT ∀_tac);
a (lemma_tac ⌜(λris⦁EvalForm (c, r, s, ris) g) = MonoEvalForm (c, r, s, g)⌝
	THEN1 rewrite_tac [ext_thm, get_spec ⌜MonoEvalForm⌝]);
a (asm_rewrite_tac[monoevalform_increasing_lemma]);
val evalform_increasing_thm = save_pop_thm "evalform_increasing_thm";
=TEX
}%ignore

\newpage
\section{SET THEORY}

We now narrow our interest to just one theory, set theory.
This will be treated using the above formalisation of infinitary logic, and will be the infinitary language with just two binary relations, equality and membership.

We consider set theory as the theory of extensions.
The `naive' approach to this is the theory with equality and membership which has equality and extensionality axioms and the principle of set comprehension, according to which to every formula with one free variable there is a set whose extension is those elements for which the formula will be true if the free variable denotes that element.
This theory unfortunately is inconsistent, but, more than one century after this discovery we still have neither a wholly satisfactory explanation of why this is the case, nor a theory which can be argued to be a maximal consistent weakening of that ontological principle.
Of course, there may be no such theory, but it is our purpose here to look further into this matter.

This will be done by looking for maximal subsets of the infinitarily definable properties which can be realised in a consistent set theory.
The definition of infinitary first order logic above stipulated a class of properties relative to some give relational structure, and tells us the meaning of these formulae.
We will be seeking subsets of the formulae which provide an interpretation of set theory.

This will be done by formulating the semantics of set theory as a functor operating on the relational structure for which the existence of a fixed point determines the required interpretation.

We are seeking a functor which when supplied with membership and equality relations will deliver new relationships at least as detailed as the original (they are partial relationships).
This is what we now define.

We define a functor which takes a relational structure containing a membership and an equality relation, over a domain which is some unspecified subset of the formulae of infinitary logic defined above, and computes a new similar structure.
The new structure will be that of the sets infinitarily definable in the first structure by formulae in the domain of discourse.
This functor may be view as the giving a semantics to the language of infinitary first order set theory, which is does by adding the the semantics of the logic above, an account of the meaning of the membership and equality relations.
This account is recursive and is therefore expressed as a functor, and will be well-defined only if the functor has a fixed point.
The functor will be monotone and will therefore have a fixed point, but this will be in general a pair of partial relations, and we will be seeking particular subsets of the language for which there is a definite fixed point such that the relations are everywhere either true or false.
From such a definite fixed point an interpretation of the classical two-valued set theory may be constructed.

\subsection{Packing and Unpacking Relationship Pairs}

The format of a structure, as used in the specification of infinitary logic above, supports arbitrary structures as indexed sets.
The definitions in this section provide for conversion between indexed sets and pairs of relationships.

=SML
declare_type_abbrev ("PR", ["'a", "'b"], ⓣ('a, 'b) BR × ('a, 'b) BR⌝);
=TEX


ⓈHOLCONST
│ ⦏PackBinRel⦎: ('a, 't DPO) BR → ('a, 't DPO) RV
├─────────
│ ∀ r⦁ PackBinRel r = λisp: 'a IS⦁
│	if IsDom isp = {Nat⋎g 0; Nat⋎g 1} ∧ IsOd isp = {}
│	then r (dpoV (isp (Nat⋎g 0))) (dpoV (isp (Nat⋎g 1)))
│	else if IsOd isp = {} then dpoB else dpoT
■

For the monotonicity proof it is useful to define the following ordering over binary relations:

ⓈHOLCONST
│ ⦏BrO⦎: ('t, BOOL) BR → (('a,'t) BR, BOOL)BR
├───────────
│ ∀ r⦁ BrO r = Pw (Pw r)
■

=GFT
⦏packbinrel_increasing_lemma⦎ =
   ⊢ ∀ r⦁ Rpo (Universe, r) ⇒ Increasing (BrO r) (RvO r) PackBinRel
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ RpoU r ⇒ RpoU (BrO r)⌝);
a (rewrite_tac[get_spec ⌜BrO⌝] THEN REPEAT strip_tac);
a (bc_tac [pw_rpou_lemma]);
a (bc_tac [pw_rpou_lemma]);
a (strip_tac);
val bro_rpou_lemma = pop_thm();

set_goal([], ⌜∀r⦁ Rpo (Universe, r) ⇒ Increasing (BrO r) (RvO r) PackBinRel⌝);
a (rewrite_tac [get_spec ⌜Increasing⌝, get_spec ⌜PackBinRel⌝, get_spec ⌜Pw⌝,
	get_spec ⌜RvO⌝, get_spec ⌜BrO⌝]
	THEN REPEAT strip_tac);
a (fc_tac [rpou_fc_clauses]);
a (cases_tac ⌜IsDom x' = {Nat⋎g 0; Nat⋎g 1} ∧ IsOd x' = {}⌝
	THEN_TRY asm_rewrite_tac[]);
val packbinrel_increasing_lemma = pop_thm ();
=TEX
}%ignore

ⓈHOLCONST
│ ⦏UnpackBinRel⦎ : ('a, 't) RV → ('a, 't) BR
├───────────
│ ∀ rv⦁ UnpackBinRel rv = λx y⦁ rv
│	(λp⦁
│		if p = Nat⋎g 0
│		then dpoE x
│		else
│			if p = Nat⋎g 1
│			then dpoE y
│			else dpoB)
■

=GFT
⦏unpackbinrel_increasing_lemma⦎ =
   ⊢ ∀ r⦁ Increasing (RvO r) (BrO r) UnpackBinRel
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ Increasing (RvO r) (BrO r) UnpackBinRel⌝);
a (rewrite_tac [get_spec ⌜Increasing⌝, get_spec ⌜UnpackBinRel⌝, get_spec ⌜Pw⌝,
	get_spec ⌜RvO⌝, get_spec ⌜BrO⌝]
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[]);
val unpackbinrel_increasing_lemma = pop_thm ();
=TEX
}%ignore


ⓈHOLCONST
│ ⦏PackRelPair⦎ : ('a, 't DPO) PR → ('a, 't DPO) RV IS
├───────────
│ ∀rp⦁ PackRelPair rp =
│	let ($=⋎v, $∈⋎v) = rp in
│	λrn⦁
│	if rn = Nat⋎g 0 then dpoE (PackBinRel $=⋎v)
│	else if rn = Nat⋎g 1 then dpoE (PackBinRel $=⋎v)
│	else dpoB
■

Here is the relevant ordering on pairs of binary relations:

ⓈHOLCONST
│ ⦏PbrO⦎: ('t, BOOL)BR → (('a, 't) PR, BOOL) BR
├───────────
│ ∀ r⦁ PbrO r = PrO (BrO r) (BrO r)
■

=GFT
⦏pbro_crpou_thm⦎ =
   ⊢ ∀ r⦁ CRpoU r ⇒ CRpoU (PbrO r)crpou_increasing_lfp_lemma2 =
   ⊢ ∀ r f⦁ CRpoU r ∧ Increasing r r f ⇒ IsLfp r f (Lfp⋎c r f)

⦏pbro_≤⋎t⋎4_crpou_thm⦎ =
   ⊢ CRpoU (PbrO $≤⋎t⋎4)

⦏packrelpair_increasing_lemma⦎ =
   ⊢ ∀ r
     ⦁ Rpo (Universe, r)
         ⇒ Increasing (PbrO r) (RvIsO r) PackRelPair
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ CRpoU r ⇒ CRpoU (PbrO r)⌝);
a (rewrite_tac [get_spec ⌜PbrO⌝, get_spec ⌜BrO⌝] THEN REPEAT strip_tac);
a (bc_tac [pro_crpou_thm]);
a (bc_tac [pw_crpou_thm]);
a (bc_tac [pw_crpou_thm]);
a strip_tac;
val pbro_crpou_thm = save_pop_thm "pbro_crpou_thm";

set_goal([], ⌜CRpoU (PbrO $≤⋎t⋎4)⌝);
a (bc_tac [pbro_crpou_thm]);
a (accept_tac ≤⋎t⋎4_crpou_thm);
val pbro_≤⋎t⋎4_crpou_thm = save_pop_thm "pbro_≤⋎t⋎4_crpou_thm";

set_goal([], ⌜∀r⦁ Rpo (Universe, r)
	⇒ Increasing (PbrO r) (RvIsO r) PackRelPair⌝);
a (rewrite_tac [get_spec ⌜Increasing⌝, get_spec ⌜PackRelPair⌝, get_spec ⌜Pw⌝, let_def,
	get_spec ⌜PbrO⌝, get_spec ⌜BrO⌝,
	get_spec ⌜RvIsO⌝, get_spec ⌜PrO⌝, get_spec ⌜IsEO⌝, get_spec ⌜DpoEO⌝, get_spec ⌜RvO⌝]
	THEN REPEAT_N 7 strip_tac);
a (cases_tac ⌜x' = Nat⋎g 0⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜PackBinRel (Fst x)⌝ THEN ∃_tac ⌜PackBinRel (Fst y)⌝
	THEN asm_rewrite_tac[get_spec ⌜PackBinRel⌝]
	THEN strip_tac);
a (cases_tac ⌜IsDom x'' = {Nat⋎g 0; Nat⋎g 1} ∧ IsOd x'' = {}⌝
	THEN asm_rewrite_tac[]
	THEN (FC_T rewrite_tac [rpou_fc_clauses]));
(* *** Goal "2" *** *)
a (REPEAT strip_tac);
a (∃_tac ⌜dpoV (if x' = Nat⋎g 1 then dpoE (PackBinRel (Fst x)) else dpoB)⌝
	THEN ∃_tac ⌜dpoV (if x' = Nat⋎g 1 then dpoE (PackBinRel (Fst y)) else dpoB)⌝);
a (lemma_tac ⌜x' = Nat⋎g 1⌝
	THEN1 (DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[get_spec ⌜dpoUdef⌝]
		THEN once_rewrite_tac [prove_rule [] ⌜∀A B⦁ ¬ A ⇒ B ⇔ ¬ B ⇒ A⌝]
		THEN strip_tac
		THEN_TRY asm_rewrite_tac[])
	THEN asm_rewrite_tac[]
	THEN strip_tac);
a (FC_T (MAP_EVERY ante_tac) [packbinrel_increasing_lemma]);
a (rewrite_tac[get_spec ⌜Increasing⌝, get_spec ⌜Pw⌝, get_spec ⌜RvO⌝, get_spec ⌜BrO⌝]);
a (strip_tac);
a (asm_fc_tac[] THEN asm_rewrite_tac[]);
val packrelpair_increasing_lemma = pop_thm ();
=TEX
}%ignore


ⓈHOLCONST
│ ⦏UnpackRelPair⦎ : ('a, 't DPO) RV IS → ('a, 't DPO) PR
├───────────
│ ∀rvis:('a, 't DPO) RV IS⦁ UnpackRelPair rvis =
│	let f = (λn⦁
│			if dpoOdef (rvis n)
│			then (λ x y⦁ dpoT)
│			else
│				if dpoUdef (rvis n)
│				then (λx y⦁ dpoB)
│				else UnpackBinRel (dpoV (rvis n)))
│	in (f (Nat⋎g 0), f (Nat⋎g 1))
■

=GFT
⦏unpackrelpair_increasing_lemma⦎ =
   ⊢ Increasing (RvIsO Dpo) (PbrO Dpo) UnpackRelPair
=TEX

\ignore{
=SML
set_goal([], ⌜Increasing (RvIsO Dpo) (PbrO Dpo) UnpackRelPair⌝);
a (rewrite_tac [get_spec ⌜RvIsO⌝, get_spec ⌜Increasing⌝, get_spec ⌜UnpackRelPair⌝, get_spec ⌜PbrO⌝,
	get_spec ⌜IsEO⌝, get_spec ⌜PrO⌝, get_spec ⌜DpoEO⌝, get_spec ⌜Pw⌝, let_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (cases_tac ⌜dpoOdef (x (Nat⋎g 0))⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a (cases_tac ⌜dpoOdef (y (Nat⋎g 0))⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.1.1" *** *)
a (asm_tac (inst_type_rule [(ⓣ'b⌝, ⓣ'a⌝)] dpo_rpou_lemma));
a (fc_tac [bro_rpou_lemma]);
a (lemma_tac ⌜∀ x:'a → 'a → 'b DPO⦁ BrO Dpo x x⌝ THEN1 fc_tac [rpou_fc_clauses2]);
a (asm_rewrite_tac[]);
(* *** Goal "1.1.2" *** *)
a (lemma_tac ⌜¬ dpoUdef (x (Nat⋎g 0))⌝
	THEN1 (GET_NTH_ASM_T 2 ante_tac
		THEN rewrite_tac[get_spec ⌜dpoUdef⌝, get_spec ⌜dpoOdef⌝]
		THEN STRIP_T rewrite_thm_tac));
a (spec_nth_asm_tac 4 ⌜Nat⋎g 0⌝);
a (DROP_NTH_ASM_T 6 ante_tac THEN asm_rewrite_tac[get_spec ⌜dpoOdef⌝]);
(* *** Goal "1.2" *** *)
a (cases_tac ⌜dpoOdef (y (Nat⋎g 0))⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2.1" *** *)
a (rewrite_tac (map get_spec [⌜BrO⌝, ⌜Pw⌝, ⌜Dpo⌝]));
(* *** Goal "1.2.2" *** *)
a (cases_tac ⌜dpoUdef (x (Nat⋎g 0))⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2.2.1" *** *)
a (rewrite_tac (map get_spec [⌜BrO⌝, ⌜Pw⌝, ⌜Dpo⌝]));
(* *** Goal "1.2.2.2" *** *)
a (spec_nth_asm_tac 4 ⌜Nat⋎g 0⌝);
a (asm_rewrite_tac (map get_spec [⌜BrO⌝, ⌜Pw⌝, ⌜Dpo⌝]));
a (FC_T (MAP_EVERY ante_tac) [
rewrite_rule (map get_spec [⌜Increasing⌝, ⌜BrO⌝, ⌜Pw⌝, ⌜Dpo⌝]) unpackbinrel_increasing_lemma]);
a (rewrite_tac [get_spec ⌜Dpo⌝]);
(* *** Goal "2" *** *)
a (cases_tac ⌜dpoOdef (x (Nat⋎g 1))⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (cases_tac ⌜dpoOdef (y (Nat⋎g 1))⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.1" *** *)
a (asm_tac (inst_type_rule [(ⓣ'b⌝, ⓣ'a⌝)] dpo_rpou_lemma));
a (fc_tac [bro_rpou_lemma]);
a (fc_tac [rpou_fc_clauses2] THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
a (lemma_tac ⌜¬ dpoUdef (x (Nat⋎g 1))⌝
	THEN1 (GET_NTH_ASM_T 2 ante_tac
		THEN rewrite_tac[get_spec ⌜dpoUdef⌝, get_spec ⌜dpoOdef⌝]
		THEN STRIP_T rewrite_thm_tac));
a (spec_nth_asm_tac 4 ⌜Nat⋎g 1⌝);
a (DROP_NTH_ASM_T 6 ante_tac THEN asm_rewrite_tac[get_spec ⌜dpoOdef⌝]);
(* *** Goal "2.2" *** *)
a (cases_tac ⌜dpoOdef (y (Nat⋎g 1))⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.1" *** *)
a (rewrite_tac (map get_spec [⌜BrO⌝, ⌜Pw⌝, ⌜Dpo⌝]));
(* *** Goal "2.2.2" *** *)
a (cases_tac ⌜dpoUdef (x (Nat⋎g 1))⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.1" *** *)
a (rewrite_tac (map get_spec [⌜BrO⌝, ⌜Pw⌝, ⌜Dpo⌝]));
(* *** Goal "2.2.2.2" *** *)
a (spec_nth_asm_tac 4 ⌜Nat⋎g 1⌝);
a (asm_rewrite_tac (map get_spec [⌜BrO⌝, ⌜Pw⌝, ⌜Dpo⌝]));
a (FC_T (MAP_EVERY ante_tac) [
rewrite_rule (map get_spec [⌜Increasing⌝, ⌜BrO⌝, ⌜Pw⌝, ⌜Dpo⌝]) unpackbinrel_increasing_lemma]);
a (rewrite_tac [get_spec ⌜Dpo⌝]);
val unpackbinrel_increasing_lemma = pop_thm();
=TEX
}%ignore

\subsection{Recasting of EvalForm}

We now recast {\it EvalForm} for the special case that the structure relative to which formulae are evaluated is a pair of binary relations.

ⓈHOLCONST
│ ⦏EvalFormPr⦎ : ('t DPO) CFE × ('t DPO) REL × 'a SET × GS
│			→ ('a, 't DPO) PR → ('a, 't DPO) RV
├───────────
│ ∀p⦁ EvalFormPr p = (MonoEvalForm p) o PackRelPair
■

=GFT
evalformpr_increasing_thm =
   ⊢ ∀ c r s g
     ⦁ CRpoU r ∧ Increasing (SetO r) r c
         ⇒ Increasing (PbrO r) (RvO r) (EvalFormPr (c, r, s, g))
=TEX

\ignore{
=SML
set_goal([], ⌜∀c r (s:'b SET) g⦁ CRpoU r ∧ Increasing (SetO r) r c
	⇒ Increasing (PbrO r) (RvO r) (EvalFormPr (c, r, s, g))⌝);
a (rewrite_tac (map get_spec [⌜EvalFormPr⌝]) THEN REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim [⌜c⌝, ⌜r⌝, ⌜s⌝, ⌜g⌝] monoevalform_increasing_lemma));
a (lemma_tac ⌜Rpo (Universe, r)⌝ 
	THEN1 (fc_tac [get_spec ⌜CRpoU⌝]
		THEN fc_tac [get_spec ⌜RpoU⌝]));
a (all_fc_tac [inst_type_rule [(ⓣ'a⌝, ⓣ'b⌝), (ⓣ'b⌝, ⓣ'a⌝)] packrelpair_increasing_lemma]);
a (strip_asm_tac (list_∀_elim [⌜PbrO r⌝, ⌜RvIsO r⌝, ⌜RvO r⌝] increasing_funcomp_thm));
a (asm_fc_tac[]);
a (asm_fc_tac[]);
val evalformpr_increasing_thm = save_pop_thm "evalformpr_increasing_thm";
=TEX
}%ignore

\subsection{Membership and Equality}

ⓈHOLCONST
│ ⦏ParamZero⦎ : GS → GS IS
├───────────
│ ∀p⦁ ParamZero p = λx⦁ if x = Nat⋎g 0 then dpoE p else dpoB
■

All the above material is generic in the type of truth values.
The following material is specific to particular sets of truth values.

=SML
declare_infix (301, "⦏∈⋎v⦎");
declare_infix (301, "⦏=⋎v⦎");
=TEX

In the following definitions, we are working with four truth values, which may be thought of as true. false, neither or both.
So that the definitions are monotonic, the criteria for truth and falsity are given independently so that it may be possible for both truth values to apply.

ⓈHOLCONST
│ ⦏MemRel⦎ : GS SET → (GS, FTV) PR → (GS, FTV) BR
├───────────
│ ∀ V (pr: (GS, FTV) PR)⦁ MemRel V pr =
	   let ($=⋎v, $∈⋎v) = pr
	   in λv w⦁
		if v ∈ V ∧ w ∈ V
		then EvalFormPr (EvalCf_tf4, $≤⋎t⋎4, V, w) pr (ParamZero v)
		else fB
■

=GFT
⦏memrel_increasing_lemma⦎ =
   ⊢ ∀ V⦁ Increasing (PbrO $≤⋎t⋎4) (BrO $≤⋎t⋎4) (MemRel V)

⦏memrel_increasing_lemma2⦎ =
   ⊢ ∀ V x y⦁ PbrO $≤⋎t⋎4 x y ⇒ BrO $≤⋎t⋎4 (MemRel V x) (MemRel V y)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ V⦁ Increasing (PbrO $≤⋎t⋎4) (BrO $≤⋎t⋎4) (MemRel V)⌝);
a (rewrite_tac ((map get_spec [⌜Increasing⌝, ⌜MemRel⌝, ⌜BrO⌝, ⌜Pw⌝])@[let_def])
	THEN REPEAT strip_tac);
a (CASES_T ⌜x' ∈ V ∧ x'' ∈ V⌝ rewrite_thm_tac);
a (asm_tac ≤⋎t⋎4_crpou_thm);
a (asm_tac evalcf_tf4_increasing_lemma);
a (strip_asm_tac (list_∀_elim [⌜EvalCf_tf4⌝, ⌜$≤⋎t⋎4⌝, ⌜V⌝, ⌜x''⌝]
	(evalformpr_increasing_thm)));
a (POP_ASM_T ante_tac THEN rewrite_tac (map get_spec [⌜Increasing⌝, ⌜RvO⌝, ⌜Pw⌝])
	THEN strip_tac);
a (ALL_ASM_FC_T rewrite_tac []);
val memrel_increasing_lemma = pop_thm ();

val memrel_increasing_lemma2 = rewrite_rule [get_spec ⌜Increasing⌝] memrel_increasing_lemma;

=IGN
set_goal([], ⌜∀V pr⦁ let mem = MemRel V pr in
	∀z x y⦁ x ∈ V ∧ y ∈ V ∧ z ∈ V
	∧ (∀v⦁ v ∈ V ⇒ (fTrue ≤⋎t⋎4 (Snd pr) v x ⇔ fTrue ≤⋎t⋎4 (Snd pr) v y))
	∧ fTrue ≤⋎t⋎4 mem x z
	⇒ fTrue ≤⋎t⋎4 mem y z⌝);
a (REPEAT ∀_tac THEN rewrite_tac [let_def] THEN ∀_tac );
a (sc_induction_tac ⌜z⌝);
a (rewrite_tac ((map get_spec [⌜MemRel⌝, ⌜EvalFormPr⌝, ⌜MonoEvalForm⌝])
		@[let_def, evalformfunct_thm2]));
a (REPEAT strip_tac);
val memrel_extensional_lemma = pop_thm();
=TEX
}%ignore

ⓈHOLCONST
│ ⦏EqRel⦎ : GS SET → (GS, FTV) BR → (GS, FTV) BR
├───────────
│ ∀ V  $∈⋎v⦁ EqRel V $∈⋎v = (λv w⦁ Lub $≤⋎t⋎4 {t | 
	v = w ∧ t = fTrue
	∨ (∃x⦁ x ∈ V ∧ (fTrue ≤⋎t⋎4 x ∈⋎v v ∧ fFalse ≤⋎t⋎4 x ∈⋎v w
				∨ fFalse ≤⋎t⋎4 x ∈⋎v v ∧ fTrue ≤⋎t⋎4 x ∈⋎v w))
		∧ t = fFalse
	∨ (∀x⦁ (x ∈ V ⇒ fTrue ≤⋎t⋎4 x ∈⋎v v ∧ fTrue ≤⋎t⋎4 x ∈⋎v w
				∨ fFalse ≤⋎t⋎4 x ∈⋎v v ∧ fFalse ≤⋎t⋎4 x ∈⋎v w)
		∧ t = fTrue)
	})
■

=GFT
⦏eqrel_increasing_lemma⦎ =
   ⊢ ∀ V⦁ Increasing (BrO $≤⋎t⋎4) (BrO $≤⋎t⋎4) (EqRel V)

⦏eqrel_increasing_lemma2⦎ =
   ⊢ ∀ V x y⦁ BrO $≤⋎t⋎4 x y ⇒ BrO $≤⋎t⋎4 (EqRel V x) (EqRel V y)

⦏eqrel_refl_lemma⦎ =
   ⊢ ∀ V pr x⦁ x ∈ V ⇒ EqRel V pr x x = fTrue

⦏eqrel_sym_lemma⦎ =
   ⊢ ∀ V pr x y⦁ x ∈ V ∧ y ∈ V ⇒ EqRel V pr x y = EqRel V pr y x

⦏eqrel_ftrue_lemma⦎ =
   ⊢ ∀ V pr x y
     ⦁ x ∈ V ∧ y ∈ V
         ⇒ (EqRel V pr x y = fTrue
           ⇔ x = y
             ∨ (∀ z
             ⦁ z ∈ V
                 ⇒ Snd pr z x = fTrue ∧ Snd pr z y = fTrue
                   ∨ Snd pr z x = fFalse ∧ Snd pr z y = fFalse))

⦏eqrel_trans_lemma⦎ =
   ⊢ ∀ V pr x y z
     ⦁ x ∈ V ∧ y ∈ V ∧ z ∈ V
         ⇒ EqRel V pr x y = fTrue ∧ EqRel V pr y z = fTrue
         ⇒ EqRel V pr x z = fTrue

⦏eqrel2_increasing_lemma⦎ =
   ⊢ ∀ V⦁ Increasing (BrO $≤⋎t⋎4) (BrO $≤⋎t⋎4) (EqRel2 V)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ V⦁ Increasing (BrO $≤⋎t⋎4) (BrO $≤⋎t⋎4) (EqRel V)⌝);
a (rewrite_tac ((map get_spec [⌜Increasing⌝, ⌜EqRel⌝, ⌜BrO⌝, ⌜Pw⌝])@[let_def])
	THEN REPEAT strip_tac);
a (asm_tac ≤⋎t⋎4_crpou_thm);
a (fc_tac [lub_increasing2_lemma3]);
a (bc_tac [asm_rule ⌜∀ x y⦁ SetO2 $≤⋎t⋎4 x y ⇒ Lub $≤⋎t⋎4 x ≤⋎t⋎4 Lub $≤⋎t⋎4 y⌝]);
a (rewrite_tac [get_spec ⌜SetO2⌝] THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜fTrue⌝ THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜fFalse⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a (lemma_tac ⌜fTrue ≤⋎t⋎4 y x'''' x'⌝
	THEN1 (list_spec_nth_asm_tac 7 [⌜x''''⌝, ⌜x'⌝] THEN all_asm_fc_tac [≤⋎t⋎4_trans_thm]));
a (lemma_tac ⌜fFalse ≤⋎t⋎4 y x'''' x''⌝
	THEN1 (list_spec_nth_asm_tac 8 [⌜x''''⌝, ⌜x''⌝] THEN all_asm_fc_tac [≤⋎t⋎4_trans_thm]));
a (∃_tac ⌜x''''⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (∃_tac ⌜fFalse⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a (lemma_tac ⌜fTrue ≤⋎t⋎4 y x'''' x''⌝
	THEN1 (list_spec_nth_asm_tac 7 [⌜x''''⌝, ⌜x''⌝] THEN all_asm_fc_tac [≤⋎t⋎4_trans_thm]));
a (lemma_tac ⌜fFalse ≤⋎t⋎4 y x'''' x'⌝
	THEN1 (list_spec_nth_asm_tac 8 [⌜x''''⌝, ⌜x'⌝] THEN all_asm_fc_tac [≤⋎t⋎4_trans_thm]));
a (∃_tac ⌜x''''⌝ THEN asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (∃_tac ⌜fTrue⌝ THEN asm_rewrite_tac[]);
a (cases_tac ⌜x' = x''⌝ THEN asm_rewrite_tac[]);
a (REPEAT_N 2 strip_tac);
a (spec_nth_asm_tac 3 ⌜x''''⌝);
(* *** Goal "4.1" *** *)
a (lemma_tac ⌜fTrue ≤⋎t⋎4 y x'''' x'⌝
	THEN1 (list_spec_nth_asm_tac 9 [⌜x''''⌝, ⌜x'⌝] THEN all_asm_fc_tac [≤⋎t⋎4_trans_thm]));
a (lemma_tac ⌜fTrue ≤⋎t⋎4 y x'''' x''⌝
	THEN1 (list_spec_nth_asm_tac 10 [⌜x''''⌝, ⌜x''⌝] THEN all_asm_fc_tac [≤⋎t⋎4_trans_thm]));
a (asm_rewrite_tac[]);
(* *** Goal "4.2" *** *)
a (lemma_tac ⌜fFalse ≤⋎t⋎4 y x'''' x'⌝
	THEN1 (list_spec_nth_asm_tac 9 [⌜x''''⌝, ⌜x'⌝] THEN all_asm_fc_tac [≤⋎t⋎4_trans_thm]));
a (lemma_tac ⌜fFalse ≤⋎t⋎4 y x'''' x''⌝
	THEN1 (list_spec_nth_asm_tac 10 [⌜x''''⌝, ⌜x''⌝] THEN all_asm_fc_tac [≤⋎t⋎4_trans_thm]));
a (asm_rewrite_tac[]);
val eqrel_increasing_lemma = pop_thm ();

val eqrel_increasing_lemma2 = rewrite_rule [get_spec ⌜Increasing⌝] eqrel_increasing_lemma;

=IGN
set_goal ([], ⌜∀V pr x⦁ x ∈ V ⇒ fTrue ≤⋎t⋎4 EqRel V pr x x⌝);
a (rewrite_tac [get_spec ⌜EqRel⌝, let_def] THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
val eqrel_refl_lemma = pop_thm ();

set_goal ([], ⌜∀V pr x y⦁ x ∈ V ∧ y ∈ V ⇒ EqRel V pr x y = EqRel V pr y x⌝);
a (rewrite_tac [get_spec ⌜EqRel⌝, let_def] THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
a (cases_tac ⌜x = y⌝ THEN_TRY asm_rewrite_tac[]);
a (SYM_ASMS_T rewrite_tac);
a (rewrite_tac [prove_rule []
	⌜∀x'⦁(Snd pr x' y = fT ∨ Snd pr x' x = fT) = (Snd pr x' x = fT ∨ Snd pr x' y = fT)⌝]);
a (rewrite_tac [prove_rule []
	⌜∀x'⦁ (Snd pr x' x = fTrue ∧ Snd pr x' y = fFalse
                       ∨ Snd pr x' y = fTrue ∧ Snd pr x' x = fFalse)
	⇔ (Snd pr x' y = fTrue ∧ Snd pr x' x = fFalse
                       ∨ Snd pr x' x = fTrue ∧ Snd pr x' y = fFalse)⌝]);
a (rewrite_tac [prove_rule []
	⌜∀x'⦁ (Snd pr x' x = fB ∨ Snd pr x' y = fB)
	⇔ (Snd pr x' y = fB ∨ Snd pr x' x = fB)⌝]);
val eqrel_sym_lemma = pop_thm ();

set_goal ([], ⌜∀V pr x y⦁ x ∈ V ∧ y ∈ V ⇒ (EqRel V pr x y = fTrue ⇔
	x = y ∨ ∀z⦁ z ∈ V ⇒
		Snd pr z x = fTrue ∧ Snd pr z y = fTrue
		∨ Snd pr z x = fFalse ∧ Snd pr z y = fFalse)⌝);
a (rewrite_tac [get_spec ⌜EqRel⌝, let_def] THEN REPEAT ∀_tac THEN strip_tac);
a (cases_tac ⌜x = y⌝ THEN asm_rewrite_tac[]);
a (CASES_T ⌜∃ x'⦁ x' ∈ V ∧ (Snd pr x' x = fT ∨ Snd pr x' y = fT)⌝ asm_tac
	THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (REPEAT strip_tac);
a (POP_ASM_T (STRIP_THM_THEN asm_tac));
a (∃_tac ⌜x'⌝
	THEN POP_ASM_T strip_asm_tac
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (CASES_T ⌜∃ x'
                   ⦁ x' ∈ V
                       ∧ (Snd pr x' x = fTrue ∧ Snd pr x' y = fFalse
                         ∨ Snd pr x' y = fTrue ∧ Snd pr x' x = fFalse)⌝ asm_tac
	THEN asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (POP_ASM_T (STRIP_THM_THEN asm_tac));
a (strip_tac THEN ∃_tac ⌜x'⌝
	THEN POP_ASM_T strip_asm_tac
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (CASES_T ⌜∃ x'⦁ x' ∈ V ∧ (Snd pr x' x = fB ∨ Snd pr x' y = fB)⌝ asm_tac
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2.1" *** *)
a (POP_ASM_T (STRIP_THM_THEN asm_tac));
a (strip_tac THEN ∃_tac ⌜x'⌝
	THEN POP_ASM_T strip_asm_tac
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a (REPEAT ∀_tac);
a (REPEAT_N 3 (DROP_NTH_ASM_T 3 strip_asm_tac));
a (strip_tac);
a (spec_nth_asm_tac 4 ⌜z⌝);
a (spec_nth_asm_tac 4 ⌜z⌝);
a (SPEC_NTH_ASM_T 7 ⌜z⌝ ante_tac THEN rewrite_tac [asm_rule ⌜z ∈ V⌝]);
a (ante_tac (∀_elim ⌜Snd pr z x⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
a (ante_tac (∀_elim ⌜Snd pr z y⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
a (prove_tac[]);
val eqrel_ftrue_lemma = pop_thm();

set_goal ([], ⌜∀V pr x y z⦁
	x ∈ V ∧ y ∈ V ∧ z ∈ V
	⇒ EqRel V pr x y = fTrue ∧ EqRel V pr y z = fTrue
	⇒ EqRel V pr x z = fTrue⌝);
a (REPEAT ∀_tac THEN strip_tac);
a (rewrite_tac [rewrite_rule [asm_rule ⌜x ∈ V⌝, asm_rule ⌜y ∈ V⌝]
	(list_∀_elim [⌜V⌝, ⌜pr⌝, ⌜x⌝, ⌜y⌝] eqrel_ftrue_lemma)]);
a (rewrite_tac [rewrite_rule [asm_rule ⌜z ∈ V⌝, asm_rule ⌜y ∈ V⌝]
	(list_∀_elim [⌜V⌝, ⌜pr⌝, ⌜y⌝, ⌜z⌝] eqrel_ftrue_lemma)]);
a (rewrite_tac [rewrite_rule [asm_rule ⌜z ∈ V⌝, asm_rule ⌜x ∈ V⌝]
	(list_∀_elim [⌜V⌝, ⌜pr⌝, ⌜x⌝, ⌜z⌝] eqrel_ftrue_lemma)]);
a (strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (REPEAT_N 4 strip_tac THEN var_elim_nth_asm_tac 3);
a (SPEC_NTH_ASM_T 3 ⌜z'⌝ ante_tac THEN rewrite_tac [asm_rule ⌜z' ∈ V⌝]);
(* *** Goal "2" *** *)
a (REPEAT_N 4 strip_tac);
a (SPEC_NTH_ASM_T 3 ⌜z'⌝ ante_tac THEN rewrite_tac [asm_rule ⌜z' ∈ V⌝]);
a (SPEC_NTH_ASM_T 4 ⌜z'⌝ ante_tac THEN rewrite_tac [asm_rule ⌜z' ∈ V⌝]);
a (prove_tac[]);
(* *** Goal "2.1" *** *)
a (DROP_NTH_ASM_T 11 ante_tac THEN rewrite_tac [asm_rule ⌜Snd pr z' y = fFalse⌝]);
(* *** Goal "2.2" *** *)
a (DROP_NTH_ASM_T 11 ante_tac THEN rewrite_tac [asm_rule ⌜Snd pr z' y = fTrue⌝]);
val eqrel_trans_lemma = pop_thm ();
=TEX
}%ignore


\subsection{The Semantic Functor}

We now define a monotone functor of which, we hope, total fixed points yeild interpretations of the first order language of set theory.

ⓈHOLCONST
│ ⦏SemanticFunctor⦎ : GS SET → (GS, FTV) PR → (GS, FTV) PR
├───────────
│ ∀ V⦁ SemanticFunctor V = λ($=⋎v, $∈⋎v)⦁ (EqRel V $∈⋎v, MemRel V ($=⋎v, $∈⋎v))
■

=GFT
⦏semanticfunctor_increasing_thm⦎ =
   ⊢ ∀ V⦁ Increasing (PbrO $≤⋎t⋎4) (PbrO $≤⋎t⋎4) (SemanticFunctor V)

⦏sf_lfp_lemma1⦎ =
   ⊢ ∀ V
     ⦁ IsLfp
         (PbrO $≤⋎t⋎4)
         (SemanticFunctor V)
         (Lfp⋎c (PbrO $≤⋎t⋎4) (SemanticFunctor V))

⦏sf_gfp_lemma1⦎ =
   ⊢ ∀ V
     ⦁ IsGfp
         (PbrO $≤⋎t⋎4)
         (SemanticFunctor V)
         (Gfp⋎c (PbrO $≤⋎t⋎4) (SemanticFunctor V))
=TEX

\ignore{
=IGN
set_goal([], ⌜∀V⦁ Increasing (PbrO $≤⋎t⋎4) (PbrO $≤⋎t⋎4) (SemanticFunctor V)⌝);
a (rewrite_tac [get_spec ⌜SemanticFunctor⌝]
	THEN strip_tac THEN bc_tac [increasing_funcomp_thm]);
a (∃_tac ⌜PbrO $≤⋎t⋎4⌝ THEN rewrite_tac [get_spec ⌜PbrO⌝] THEN strip_tac);
(* *** Goal "1" *** *)
a (bc_tac [funright_increasing_thm]);
a (rewrite_tac [rewrite_rule [get_spec ⌜PbrO⌝] memrel_increasing_lemma]);
(* *** Goal "2" *** *)
a (bc_tac [funleft_increasing_thm]);
a (rewrite_tac [rewrite_rule [get_spec ⌜PbrO⌝] exteqmem_increasing_lemma]);
val semanticfunctor_increasing_thm = save_pop_thm "semanticfunctor_increasing_thm";

set_goal([], ⌜∀V⦁ IsLfp (PbrO $≤⋎t⋎4) (SemanticFunctor V)
			(Lfp⋎c (PbrO $≤⋎t⋎4) (SemanticFunctor V))⌝);
a (strip_tac THEN bc_tac [crpou_increasing_lfp_lemma2]
	THEN rewrite_tac [pbro_≤⋎t⋎4_crpou_thm, semanticfunctor_increasing_thm]);
val sf_lfp_lemma1 = pop_thm ();

set_goal([], ⌜∀V⦁ IsGfp (PbrO $≤⋎t⋎4) (SemanticFunctor V)
			(Gfp⋎c (PbrO $≤⋎t⋎4) (SemanticFunctor V))⌝);
a (strip_tac THEN bc_tac [crpou_increasing_gfp_lemma2]
	THEN rewrite_tac [pbro_≤⋎t⋎4_crpou_thm, semanticfunctor_increasing_thm]);
val sf_gfp_lemma1 = pop_thm ();
=TEX
}%ignore

\section{INFINITARILY DEFINABLE MEMBERSHIP STRUCTURES}

We are now able to identify and analyse a large class of interpretations of set theory.

Every fixedpoint of the semantic functor which is total, i.e. in which the equality and membership relations over the domain (the V parameter to the semantic functor) gives only true and false (not underdefined or overdefined) yields a membership structure in the usual sense, and this structure is extensional (i.e. satisfies the axiom of extensionality).

In order to define this class of structures it is necessary to prove some facts about total fixedpoints of the semantic functor.
We need to know first that the equality relation in such a fixed point will be an equivalence relation (the equivalence classes will be the elements in the domain of the structure).
This enables us to define the class of structures, and our next objective is to prove that they are indeed extensional.

From there we intend to proceed by identifying consistent constraints on the fixed points which effectively place lower bounds on the richness of the ontology and permit the proof of progressively stronger ontological principles, which may be thought of as an axiomatisation of a strong non-well-founded set theory.
In this way we seek to approach a maximal theory of comprehension, i.e. of sets construed as the extensions of properties.

First we define the notion of a total fixed point of the semantic functor, and then prove various properties of these fized points.

ⓈHOLCONST
│ ⦏TotalOver⦎ : 'a SET → ('a, FTV)BR → BOOL
├───────────
│ ∀ V r⦁ TotalOver V r ⇔ ∀x y⦁
│	if x ∈ V ∧ y ∈ V
│	then r x y = fTrue ∨ r x y = fFalse
│	else r x y = fB
■

=GFT
=TEX

\ignore{
=IGN
set_goal([], ⌜∀V⦁ Upward r f ⇒ ∀x⦁ TotalOver V (f x) ⇒ ⌝);

set_goal([], ⌜∀V pr⦁ TotalOver V (ExtMem V pr) ⇒
	∀x y⦁ x ∈ V ∧ y ∈ V ⇒
		(ExtMem V x y ⇔ )⌝);


=TEX
}%ignore

ⓈHOLCONST
│ ⦏PrTotalOver⦎ : 'a SET → ('a, FTV)PR → BOOL
├───────────
│ ∀ V pr⦁ PrTotalOver V pr ⇔ TotalOver V (Fst pr) ∧ TotalOver V (Snd pr)
■

=GFT
=TEX

\ignore{
=IGN
=TEX
}%ignore

ⓈHOLCONST
│ ⦏SFFixp⦎ : GS SET × (GS, FTV)PR → BOOL
├───────────
│ ∀p⦁ SFFixp p = SemanticFunctor (Fst p) (Snd p) = (Snd p)
■

=GFT
=TEX

ⓈHOLCONST
│ ⦏BoolRel⦎ : (GS, FTV)BR → (GS, BOOL)BR
├───────────
│ ∀r⦁ BoolRel r = λx y⦁ r x y = fTrue
■

=GFT (not proven)
⦏eqrel_equiv_lemma⦎ =
   ⊢ ∀ V pr⦁ TotalOver V (EqRel V pr) ⇒ Equiv (V, BoolRel (EqRel V pr))
=TEX

\ignore{
=IGN
set_goal([], ⌜∀V pr⦁ TotalOver V (EqRel V pr) ⇒ Equiv (V, BoolRel (EqRel V pr))⌝);
a (PC_T1 "hol1" rewrite_tac [get_spec ⌜TotalOver⌝, get_spec ⌜BoolRel⌝, get_spec ⌜Equiv⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜Refl⌝, eqrel_refl_lemma]);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜Sym⌝] THEN REPEAT strip_tac);
a (POP_ASM_T ante_tac);
a (ALL_FC_T rewrite_tac [eqrel_sym_lemma]);
(* *** Goal "3" *** *)
a (rewrite_tac [get_spec ⌜Trans⌝] THEN REPEAT strip_tac);
a (all_asm_fc_tac [eqrel_trans_lemma]);
val eqrel_equiv_lemma = pop_thm ();
=IGN

set_goal([], ⌜∀V r $=⋎v⦁ PrTotalOver V ($=⋎v, r) ∧ Equiv (V, BoolRel $=⋎v)
	⇒ ((BoolRel (ExtMem V ($=⋎v, r))) Respects (BoolRel $=⋎v)) V⌝);
a (rewrite_tac (map get_spec [⌜PrTotalOver⌝, ⌜TotalOver⌝, ⌜$Respects⌝, ⌜ExtMem⌝, ⌜BoolRel⌝]));
a (REPEAT strip_tac);
a (asm_rewrite_tac [ext_thm, let_def]);
a (strip_tac);
a (LEMMA_T ⌜{t
                     |x' ∈ V
                         ∧ (∃ v w
                         ⦁ v ∈ V
                             ∧ w ∈ V
                             ∧ fTrue ≤⋎t⋎4 v =⋎v x
                             ∧ fTrue ≤⋎t⋎4 w =⋎v x'
                             ∧ t ≤⋎t⋎4 r v w)}
  =
{t
                     |x' ∈ V
                         ∧ (∃ v w
                         ⦁ v ∈ V
                             ∧ w ∈ V
                             ∧ fTrue ≤⋎t⋎4 v =⋎v y
                             ∧ fTrue ≤⋎t⋎4 w =⋎v x'
                             ∧ t ≤⋎t⋎4 r v w)}⌝ rewrite_thm_tac);
a (rewrite_tac [sets_ext_clauses]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜v⌝ THEN ∃_tac ⌜w⌝ THEN asm_rewrite_tac[]);

a (LEMMA_T ⌜⌝
=TEX
}%ignore

=GFT
⦏eqrel_totalmem_extensional_lemma⦎ =
   ⊢ ∀ V $=⋎v $∈⋎v
     ⦁ TotalOver V $∈⋎v
         ⇒ (∀ x y
         ⦁ x ∈ V ∧ y ∈ V
             ⇒ EqRel V ($=⋎v, $∈⋎v) x y
               = (if ∀ z⦁ z ∈ V ⇒ z ∈⋎v x = z ∈⋎v y then fTrue else fFalse))
=TEX

\ignore{
=IGN
set_goal([], ⌜∀V $=⋎v $∈⋎v⦁ TotalOver V $∈⋎v ⇒
	∀x y⦁ x ∈ V ∧ y ∈ V ⇒ EqRel V ($=⋎v, $∈⋎v) x y =
		if ∀z⦁ z ∈ V ⇒ z ∈⋎v x = z ∈⋎v y
		then fTrue
		else fFalse⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜EqRel⌝,
	get_spec ⌜PrTotalOver⌝, let_def]
	THEN REPEAT strip_tac);
a (asm_tac (rewrite_rule [get_spec ⌜TotalOver⌝] (asm_rule ⌜TotalOver V $∈⋎v⌝)));
a (cases_tac ⌜x=y⌝ THEN_TRY asm_rewrite_tac[]);
a (LEMMA_T ⌜¬ ∃ x'⦁ x' ∈ V ∧ (x' ∈⋎v x = fT ∨ x' ∈⋎v y = fT)⌝ rewrite_thm_tac
	THEN1 REPEAT_N 3 strip_tac);
(* *** Goal "1" *** *)
a strip_tac;
a (cases_tac ⌜x' ∈ V⌝ THEN asm_rewrite_tac[]);
a (LIST_SPEC_NTH_ASM_T 3 [⌜x'⌝, ⌜y⌝]
		(strip_asm_tac o (rewrite_rule [asm_rule ⌜x' ∈ V⌝, asm_rule ⌜y ∈ V⌝]))
	THEN asm_rewrite_tac[]
	THEN LIST_SPEC_NTH_ASM_T 4 [⌜x'⌝, ⌜x⌝]
		(strip_asm_tac o (rewrite_rule [asm_rule ⌜x' ∈ V⌝, asm_rule ⌜x ∈ V⌝]))
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (CASES_T ⌜∀ z⦁ z ∈ V ⇒ z ∈⋎v x = z ∈⋎v y⌝
	(fn x => TRY (rewrite_thm_tac x) THEN strip_asm_tac x));
(* *** Goal "2.1" *** *)
a (LEMMA_T ⌜¬ ∃ x'⦁ x' ∈ V ∧ (x' ∈⋎v x = fB ∨ x' ∈⋎v y = fB)⌝ rewrite_thm_tac
	THEN1 REPEAT_N 4 strip_tac);
(* *** Goal "2.1.1" *** *)
a (cases_tac ⌜x' ∈ V⌝ THEN asm_rewrite_tac[]);
a (LIST_SPEC_NTH_ASM_T 4 [⌜x'⌝, ⌜y⌝]
		(strip_asm_tac o (rewrite_rule [asm_rule ⌜x' ∈ V⌝, asm_rule ⌜y ∈ V⌝]))
	THEN asm_rewrite_tac[]
	THEN LIST_SPEC_NTH_ASM_T 5 [⌜x'⌝, ⌜x⌝]
		(strip_asm_tac o (rewrite_rule [asm_rule ⌜x' ∈ V⌝, asm_rule ⌜x ∈ V⌝]))
	THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
a (LEMMA_T ⌜¬∃ x'
                 ⦁ x' ∈ V
                     ∧ (x' ∈⋎v x = fTrue ∧ x' ∈⋎v y = fFalse
                       ∨ x' ∈⋎v y = fTrue ∧ x' ∈⋎v x = fFalse)⌝
	rewrite_thm_tac);
a (REPEAT_N 3 strip_tac);
a (cases_tac ⌜x' ∈ V⌝ THEN asm_rewrite_tac[]);
a (SPEC_NTH_ASM_T 2 ⌜x'⌝
		(strip_asm_tac o (rewrite_rule [asm_rule ⌜x' ∈ V⌝, asm_rule ⌜y ∈ V⌝]))
	THEN asm_rewrite_tac[]);
a (LIST_SPEC_NTH_ASM_T 5 [⌜x'⌝, ⌜y⌝]
		(strip_asm_tac o (rewrite_rule [asm_rule ⌜x' ∈ V⌝, asm_rule ⌜y ∈ V⌝]))
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (LEMMA_T ⌜¬ ∃ x'⦁ x' ∈ V ∧ (x' ∈⋎v x = fB ∨ x' ∈⋎v y = fB)⌝ rewrite_thm_tac
	THEN1 REPEAT_N 3 strip_tac);
(* *** Goal "2.2.1" *** *)
a strip_tac;
a (cases_tac ⌜x' ∈ V⌝ THEN asm_rewrite_tac[]);
a (LIST_SPEC_NTH_ASM_T 5 [⌜x'⌝, ⌜y⌝]
		(strip_asm_tac o (rewrite_rule [asm_rule ⌜x' ∈ V⌝, asm_rule ⌜y ∈ V⌝]))
	THEN asm_rewrite_tac[]
	THEN LIST_SPEC_NTH_ASM_T 6 [⌜x'⌝, ⌜x⌝]
		(strip_asm_tac o (rewrite_rule [asm_rule ⌜x' ∈ V⌝, asm_rule ⌜x ∈ V⌝]))
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a (LEMMA_T ⌜∃ x'
                 ⦁ x' ∈ V
                     ∧ (x' ∈⋎v x = fTrue ∧ x' ∈⋎v y = fFalse
                       ∨ x' ∈⋎v y = fTrue ∧ x' ∈⋎v x = fFalse)⌝
	rewrite_thm_tac);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
a (LIST_SPEC_NTH_ASM_T 4 [⌜z⌝, ⌜y⌝]
		(strip_asm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝, asm_rule ⌜y ∈ V⌝]))
	THEN asm_rewrite_tac[]
	THEN LIST_SPEC_NTH_ASM_T 5 [⌜z⌝, ⌜x⌝]
		(strip_asm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝, asm_rule ⌜x ∈ V⌝]))
	THEN asm_rewrite_tac[]
	THEN (DROP_ASM_T ⌜¬ z ∈⋎v x = z ∈⋎v y⌝ ante_tac)
	THEN asm_rewrite_tac[]);
val eqrel_totalmem_extensional_lemma = pop_thm ();
=IGN

set_goal([], ⌜∀V $=⋎v $∈⋎v⦁ PrTotalOver V ($=⋎v, $∈⋎v) ⇒
	∀x y v  w⦁ x ∈ V ∧ y ∈ V ∧ v ∈ V ∧ w ∈ V ∧ fTrue ≤⋎t⋎4 x =⋎v v ∧ fTrue ≤⋎t⋎4 y =⋎v w
		⇒ (fTrue ≤⋎t⋎4 ExtMem V ($=⋎v, $∈⋎v) x y ⇔ fTrue ≤⋎t⋎4 ExtMem V ($=⋎v, $∈⋎v) v w)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜ExtMem⌝,
	get_spec ⌜PrTotalOver⌝, let_def]
	THEN REPEAT_N 6 strip_tac);
(* *** Goal "1" *** *)
a (asm_tac (rewrite_rule [get_spec ⌜TotalOver⌝] (asm_rule ⌜TotalOver V $∈⋎v⌝)));
a (cases_tac ⌜x=y⌝ THEN_TRY asm_rewrite_tac[]);
a (LEMMA_T ⌜¬ ∃ x'⦁ x' ∈ V ∧ (x' ∈⋎v x = fT ∨ x' ∈⋎v y = fT)⌝ rewrite_thm_tac
	THEN1 REPEAT_N 3 strip_tac);
(* *** Goal "1" *** *)
a strip_tac;
a (cases_tac ⌜x' ∈ V⌝ THEN asm_rewrite_tac[]);
a (list_spec_nth_asm_tac 3 [⌜x'⌝, ⌜y⌝]
	THEN asm_rewrite_tac[]
	THEN list_spec_nth_asm_tac 4 [⌜x'⌝, ⌜x⌝]
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (CASES_T ⌜∀ z⦁ z ∈ V ⇒ z ∈⋎v x = z ∈⋎v y⌝
	(fn x => TRY (rewrite_thm_tac x) THEN strip_asm_tac x));
(* *** Goal "2.1" *** *)
a (LEMMA_T ⌜¬ ∃ x'⦁ x' ∈ V ∧ (x' ∈⋎v x = fB ∨ x' ∈⋎v y = fB)⌝ rewrite_thm_tac
	THEN1 REPEAT_N 4 strip_tac);
(* *** Goal "2.1.1" *** *)
a (cases_tac ⌜x' ∈ V⌝ THEN asm_rewrite_tac[]);
a (list_spec_nth_asm_tac 4 [⌜x'⌝, ⌜x⌝]
	THEN asm_rewrite_tac []
	THEN list_spec_nth_asm_tac 5 [⌜x'⌝, ⌜y⌝]
	THEN asm_rewrite_tac []);
(* *** Goal "2.1.2" *** *)
a (LEMMA_T ⌜¬∃ x'
                 ⦁ x' ∈ V
                     ∧ (x' ∈⋎v x = fTrue ∧ x' ∈⋎v y = fFalse
                       ∨ x' ∈⋎v y = fTrue ∧ x' ∈⋎v x = fFalse)⌝
	rewrite_thm_tac);
a (REPEAT_N 3 strip_tac);
a (cases_tac ⌜x' ∈ V⌝ THEN asm_rewrite_tac[]);
a (spec_nth_asm_tac 2 ⌜x'⌝ THEN asm_rewrite_tac[]);
a (list_spec_nth_asm_tac 5 [⌜x'⌝, ⌜y⌝] THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (LEMMA_T ⌜¬ ∃ x'⦁ x' ∈ V ∧ (x' ∈⋎v x = fB ∨ x' ∈⋎v y = fB)⌝ rewrite_thm_tac
	THEN1 REPEAT_N 3 strip_tac);
(* *** Goal "2.2.1" *** *)
a strip_tac;
a (cases_tac ⌜x' ∈ V⌝ THEN asm_rewrite_tac[]);
a (list_spec_nth_asm_tac 5 [⌜x'⌝, ⌜y⌝]
	THEN asm_rewrite_tac[]
	THEN list_spec_nth_asm_tac 6 [⌜x'⌝, ⌜x⌝]
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a (LEMMA_T ⌜∃ x'
                 ⦁ x' ∈ V
                     ∧ (x' ∈⋎v x = fTrue ∧ x' ∈⋎v y = fFalse
                       ∨ x' ∈⋎v y = fTrue ∧ x' ∈⋎v x = fFalse)⌝
	rewrite_thm_tac);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
a (list_spec_nth_asm_tac 4 [⌜z⌝, ⌜y⌝]
	THEN asm_rewrite_tac[]
	THEN list_spec_nth_asm_tac 5 [⌜z⌝, ⌜x⌝]
	THEN asm_rewrite_tac[]
	THEN (DROP_ASM_T ⌜¬ z ∈⋎v x = z ∈⋎v y⌝ ante_tac)
	THEN asm_rewrite_tac[]);
val eqrel_totalmem_extensional_lemma = pop_thm ();
=TEX
}%ignore

ⓈHOLCONST
│ ⦏SFTotalFixp⦎ : GS SET × (GS, FTV)PR → BOOL
├───────────
│ ∀p⦁ SFTotalFixp p ⇔ SFFixp p ∧ PrTotalOver (Fst p) (Snd p)
■

=GFT
=TEX

\ignore{
=IGN
set_goal([], ⌜⌝);


=TEX
}%ignore

\subsubsection{Extensionality of Equality}

For our purposes it is helpful to define the following notion of extensionality which applies to functions which operate on four-valued membership relations and yield four-valued relations.

The idea is that a function is extensional if its value for any pair of elements depends only on the extension of the two elements.
Since we are working with four truth values, the extensions under consideration are not sets, they are four-valued characteristic functions.
However, if the characteristic functions yield the undefined truth value anywhere in the domain under consideration, they are not really knowm to be equal so we require that these characteristic functions are everywhere defined (or overdefined).


ⓈHOLCONST
│ ⦏FtvExtensional⦎ : 'a SET → (('a, FTV) BR → ('a, FTV) BR) → BOOL
├───────────
│ ∀ V f⦁ FtvExtensional V f = ∀$∈⋎v x y z⦁ x ∈ V ∧ y ∈ V ∧ z ∈ V
│	∧ TotalOver V $∈⋎v ∧ (∀v⦁ v ∈ V ⇒ v ∈⋎v x = v ∈⋎v y)
│	⇒ f $∈⋎v x z = f $∈⋎v y z ∧ f $∈⋎v z x = f $∈⋎v z y
■

We now show that {\it EqRel} is in this sense extensional.

=GFT
⦏eqrel_ftvextensional_lemma⦎ =
   ⊢ ∀ V $=⋎v⦁ FtvExtensional V (λ $∈⋎v⦁ EqRel V ($=⋎v, $∈⋎v))
=TEX

\ignore{
=IGN
set_goal([], ⌜∀V $=⋎v⦁ FtvExtensional V (λ$∈⋎v⦁ EqRel V ($=⋎v, $∈⋎v))⌝);
a (rewrite_tac [get_spec ⌜FtvExtensional⌝, let_def]
	THEN REPEAT_N 8 strip_tac);
(* *** Goal "1" *** *)
a (strip_asm_tac (list_∀_elim [⌜V⌝, ⌜$=⋎v⌝, ⌜$∈⋎v⌝] eqrel_totalmem_extensional_lemma));
a (list_spec_nth_asm_tac 1 [⌜x⌝, ⌜z⌝]);
a (list_spec_nth_asm_tac 2 [⌜y⌝, ⌜z⌝]);
a (asm_rewrite_tac[]);
a (CASES_T ⌜∀ z'⦁ z' ∈ V ⇒ z' ∈⋎v x = z' ∈⋎v z⌝ asm_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a (LEMMA_T ⌜∀ z'⦁ z' ∈ V ⇒ z' ∈⋎v y = z' ∈⋎v z⌝ rewrite_thm_tac
	THEN1 REPEAT strip_tac THEN ASM_FC_T (fn tl => TRY (rewrite_tac tl)) []);
a (spec_nth_asm_tac 2 ⌜z'⌝ THEN POP_ASM_T ante_tac);
a (spec_nth_asm_tac 6 ⌜z'⌝ THEN POP_ASM_T rewrite_thm_tac);
(* *** Goal "1.2" *** *)
a (LEMMA_T ⌜¬ ∀ z'⦁ z' ∈ V ⇒ z' ∈⋎v y = z' ∈⋎v z⌝ rewrite_thm_tac
	THEN1 REPEAT strip_tac THEN ASM_FC_T (fn tl => TRY (rewrite_tac tl)) []);
a (POP_ASM_T strip_asm_tac);
a (∃_tac ⌜z'⌝ THEN asm_rewrite_tac[]);
a (swap_nth_asm_concl_tac 1);
a (spec_nth_asm_tac 6 ⌜z'⌝ THEN asm_rewrite_tac []);
(* *** Goal "2" *** *)
a (strip_asm_tac (list_∀_elim [⌜V⌝, ⌜$=⋎v⌝, ⌜$∈⋎v⌝] eqrel_totalmem_extensional_lemma));
a (list_spec_nth_asm_tac 1 [⌜z⌝, ⌜x⌝]);
a (list_spec_nth_asm_tac 2 [⌜z⌝, ⌜y⌝]);
a (asm_rewrite_tac[]);
a (CASES_T ⌜∀ z'⦁ z' ∈ V ⇒ z' ∈⋎v z = z' ∈⋎v x⌝ asm_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (LEMMA_T ⌜∀ z'⦁ z' ∈ V ⇒ z' ∈⋎v z = z' ∈⋎v y⌝ rewrite_thm_tac
	THEN1 REPEAT strip_tac THEN ASM_FC_T (fn tl => TRY (rewrite_tac tl)) []);
(* *** Goal "2.2" *** *)
a (LEMMA_T ⌜¬ ∀ z'⦁ z' ∈ V ⇒ z' ∈⋎v z = z' ∈⋎v y⌝ rewrite_thm_tac
	THEN1 REPEAT strip_tac THEN ASM_FC_T (fn tl => TRY (rewrite_tac tl)) []);
a (POP_ASM_T strip_asm_tac);
a (∃_tac ⌜z'⌝ THEN asm_rewrite_tac[]);
a (swap_nth_asm_concl_tac 1);
a (spec_nth_asm_tac 6 ⌜z'⌝ THEN asm_rewrite_tac []);
val eqrel_ftvextensional_lemma = pop_thm ();
=TEX
}%ignore


=GFT
⦏totalfixp_extensional_lemma⦎ =
   ⊢ ∀ V eq mem $=⋎v $∈⋎v
     ⦁ SFTotalFixp (V, eq, mem)
         ⇒ (let $=⋎v = BoolRel eq and $∈⋎v = BoolRel mem
         in ∀ x y
         ⦁ x ∈ V ∧ y ∈ V ⇒ (x =⋎v y ⇔ (∀ z⦁ z ∈ V ⇒ (z ∈⋎v x ⇔ z ∈⋎v y))))
=TEX

\ignore{
=IGN
set_goal([], ⌜∀V eq mem⦁ SFTotalFixp (V, eq, mem) ⇒
	let $=⋎v = BoolRel eq and $∈⋎v = BoolRel mem
	in ∀x y⦁ x ∈ V ∧ y ∈ V ⇒ (x =⋎v y ⇒ ∀z⦁ z ∈ V ⇒ (z ∈⋎v x ⇔ z ∈⋎v y))⌝);


set_goal([], ⌜∀V eq mem⦁ SFTotalFixp (V, eq, mem) ⇒
	let $=⋎v = BoolRel eq and $∈⋎v = BoolRel mem
	in ∀x y⦁ x ∈ V ∧ y ∈ V ⇒ (x =⋎v y ⇔ ∀z⦁ z ∈ V ⇒ (z ∈⋎v x ⇔ z ∈⋎v y))⌝);
a (rewrite_tac (map get_spec [⌜SFTotalFixp⌝, ⌜BoolRel⌝, ⌜SFFixp⌝, ⌜SemanticFunctor⌝,
	⌜FunLeft⌝, ⌜FunRight⌝]));
a (rewrite_tac [let_def]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (ante_tac (list_∀_elim [⌜V⌝, ⌜(eq, mem)⌝, ⌜x'⌝, ⌜y⌝] eqrel_ftrue_lemma));
a (asm_rewrite_tac[]);
a (strip_tac);
(* *** Goal "1.1" *** *)
a (var_elim_asm_tac ⌜x' = y⌝);
(* *** Goal "1.2" *** *)
a (SPEC_NTH_ASM_T 1 ⌜z⌝ ante_tac);
a (rewrite_tac[]);
a (strip_tac);
a (DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (ante_tac (list_∀_elim [⌜V⌝, ⌜(eq, mem)⌝, ⌜x'⌝, ⌜y⌝] eqrel_ftrue_lemma));
a (asm_rewrite_tac[]);
a (strip_tac);
(* *** Goal "2.1" *** *)
a (var_elim_asm_tac ⌜x' = y⌝);
(* *** Goal "2.2" *** *)
a (SPEC_NTH_ASM_T 1 ⌜z⌝ ante_tac);
a (rewrite_tac[]);
a (strip_tac);
a (DROP_NTH_ASM_T 1 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (ante_tac (list_∀_elim [⌜V⌝, ⌜(eq, mem)⌝, ⌜x'⌝, ⌜y⌝] eqrel_ftrue_lemma));
a (asm_rewrite_tac[]);
a (STRIP_T rewrite_thm_tac);
a (REPEAT_N 4 strip_tac);
a (fc_tac [get_spec ⌜PrTotalOver⌝]);
a (fc_tac [get_spec ⌜TotalOver⌝]);
a (SPEC_NTH_ASM_T 7 ⌜z⌝ (rewrite_thm_tac o (rewrite_rule [asm_rule ⌜z ∈ V⌝])));
a (DROP_NTH_ASM_T 2 (asm_tac o (rewrite_rule[])));
a (lemma_tac ⌜mem z y = fFalse ∨ mem z y = fTrue⌝
	THEN1 (LIST_SPEC_NTH_ASM_T 1 [⌜z⌝, ⌜y⌝] ante_tac
		THEN rewrite_tac [asm_rule ⌜z ∈ V⌝, asm_rule ⌜y ∈ V⌝]
		THEN prove_tac[])
	THEN asm_rewrite_tac[]);
a (lemma_tac ⌜mem z x' = fFalse ∨ mem z x' = fTrue⌝
	THEN1 (LIST_SPEC_NTH_ASM_T 2 [⌜z⌝, ⌜x'⌝] ante_tac
		THEN rewrite_tac [asm_rule ⌜z ∈ V⌝, asm_rule ⌜x' ∈ V⌝]
		THEN prove_tac[])
	THEN asm_rewrite_tac[]);
a (all_asm_fc_tac[]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
val totalfixp_extensional_lemma = save_pop_thm "totalfixp_extensional_lemma";

=IGN
set_goal([], ⌜∀V eq mem $=⋎v $∈⋎v⦁ SFTotalFixp (V, eq, mem) ⇒
	let $=⋎v = BoolRel eq and $∈⋎v = BoolRel mem
	in ∀x y⦁ x ∈ V ∧ y ∈ V ⇒ (x =⋎v y ⇒ ∀z⦁ z ∈ V ⇒ (x ∈⋎v z ⇔ y ∈⋎v z))⌝);
a (rewrite_tac (map get_spec [⌜SFTotalFixp⌝, ⌜BoolRel⌝, ⌜SFFixp⌝, ⌜SemanticFunctor⌝,
	⌜FunLeft⌝, ⌜FunRight⌝, ⌜ExtEqMem⌝, ⌜ExtMem⌝]));
a (rewrite_tac [let_def]);
a (REPEAT_N 4 strip_tac);
a (DROP_NTH_ASM_T 2 (asm_tac o (rewrite_rule[asm_rule ⌜EqRel V (eq, mem) = eq⌝])));
(* *** Goal "1" *** *)
a (ante_tac (list_∀_elim [⌜V⌝, ⌜(eq, mem)⌝, ⌜x'⌝, ⌜y⌝] eqrel_ftrue_lemma));
a (asm_rewrite_tac[]);
a (strip_tac);
(* *** Goal "1.1" *** *)
a (var_elim_asm_tac ⌜x' = y⌝);
(* *** Goal "1.2" *** *)
a (SPEC_NTH_ASM_T 1 ⌜z⌝ ante_tac);
a (rewrite_tac[]);
a (strip_tac);
(* *** Goal "1.2.1" *** *)
a (DROP_NTH_ASM_T 3 (asm_tac o (rewrite_rule[])));

=TEX
}%ignore

ⓈHOLCONST
│ ⦏MSfromSFF⦎ : GS SET × (GS, FTV) PR → GS SET SET × (GS SET, BOOL) BR
├───────────
│ ∀ (V:GS SET) (pr:(GS, FTV) PR)⦁ MSfromSFF (V, pr) =
│	let ($=⋎v, $∈⋎v) = (BoolRel (Fst pr), BoolRel (Snd pr)) in
│	(QuotientSet V $=⋎v, λs t⦁ ∀x y⦁ x ∈ s ∧ y ∈ t ⇒ x ∈⋎v y)		 
■


=SML
new_parent "membership";
=TEX

\ignore{
=IGN
set_goal([], ⌜∀(V, $=⋎v, $∈⋎v)⦁ SFFixp (V, ($=⋎v, $∈⋎v)) ∧ PrTotalOver V ($=⋎v, $∈⋎v)
		⇒ extensional (MSfromSFF (V, ($=⋎v, $∈⋎v)))⌝);
a (rewrite_tac [let_def, get_spec ⌜SFFixp⌝, get_spec ⌜MSfromSFF⌝, get_spec ⌜extensional⌝,
	get_spec ⌜BoolRel⌝, get_spec ⌜PrTotalOver⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (var_elim_asm_tac ⌜s = t⌝);
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (var_elim_asm_tac ⌜s = t⌝);
a (all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a (DROP_NTH_ASM_T 5 ante_tac THEN rewrite_tac [sets_ext_clauses] THEN strip_tac);
a (DROP_NTH_ASM_T 5 ante_tac THEN rewrite_tac [sets_ext_clauses] THEN strip_tac);
a (strip_tac);
a (swap_nth_asm_concl_tac 6);
a (rewrite_tac (map get_spec [⌜SemanticFunctor⌝, ⌜FunLeft⌝, ⌜FunRight⌝, ⌜MemRel⌝, ⌜EqRel⌝]));
eqrel_ftrue_lemma;

=TEX
}%ignore


\subsubsection{Proof Contexts}

=SML
add_pc_thms "'ifol" [];
commit_pc "'ifol";

force_new_pc "⦏ifol⦎";
merge_pcs ["hol", "'GS1", "'misc1", "'misc2", "'ifol"] "ifol";
commit_pc "ifol";

force_new_pc "⦏ifol1⦎";
merge_pcs ["hol1", "'GS1", "'misc1", "'misc2", "'ifol"] "ifol1";
commit_pc "ifol1";
=TEX

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{ifol.th}
}  %\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
