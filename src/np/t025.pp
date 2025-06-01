=IGN
$Id: t025.doc,v 1.18 2011/10/25 09:10:46 rbj Exp $
open_theory "ifol";
set_merge_pcs ["rbjmisc", "'GS1", "'misc2", "'ifol"];
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

\title{More Miscellanea (misc1, misc2)}
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
This theory is for miscellanea which cannot be put in theory ``rbjmisc'' because of dependencies on other theories.
It consists primarily of things required in the documents on non well-founded set theories, but not specific to that work, which make use of galactic set theory or fixed point theory.
Since I moved my non-well-founded foundational work back from set theory to combinatory logic using version of well-founded set theory with urelements it has been necessary to replicate those definitions required which depend upon well-founded set theory in the context of this other version of well founded set theory.
For that reason this document is in the process of being restructured as three theories, one of material which does not depend on the well founded set theory, and one for materials dependent respectively on each of the two versions of well-founded set theory.
These are the theories misc1, and misc2.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created: 2008/07/11

Last Change $ $Date: 2011/10/25 09:10:46 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t025.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t025.pdf}

$ $Id: t025.doc,v 1.18 2011/10/25 09:10:46 rbj Exp $ $

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

This was originally material which used to be in t024 and is moved here so that it can also be used in t026.

It should only contain material which cannot be put in ``rbjmisc'' because it depends on other theories, at this point GS or GSU and fixp.
Some of it should therefore be moved up to ``rbjmisc''.

Two theories are created $misc1$ and $misc2$.

$misc2$ depends on GS and $misc1$.
Ultimately all that does not depend GS should migrate upwards into misc1, but this process has not yet been completed.

=SML
open_theory "rbjmisc";
force_new_theory "⦏misc1⦎";
new_parent "fixp";
force_new_pc "⦏'misc1⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'misc1";
set_merge_pcs ["rbjmisc", "'misc1"];
=TEX

\section{DISCRETE PARTIAL ORDERS}

=SML
new_type_defn (["DPO"], "DPO", ["'a"],
	tac_proof (([], ⌜∃x:'a+BOOL⦁ (λy⦁T) x⌝), ∃_tac ⌜InR T⌝ THEN prove_tac []));
=TEX

=IGN
declare_type_abbrev("⦏DPO⦎", ["'a"], ⓣ'a + BOOL⌝);
=TEX


\ignore{
=SML
set_goal([], ⌜∃ absDPO (repDPO: 'a DPO → 'a + BOOL)
         ⦁ (∀ a⦁ absDPO (repDPO a) = a) ∧ (∀ r⦁ repDPO (absDPO r) = r)⌝);
a (strip_asm_tac (get_defn "-" "DPO"));
a (fc_tac [type_lemmas_thm2]);
a (∃_tac ⌜abs⌝ THEN ∃_tac ⌜rep⌝ THEN asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 2 (rewrite_thm_tac o (rewrite_rule[])));
save_cs_∃_thm (pop_thm());
=TEX
}%

ⓈHOLCONST
│ ⦏absDPO⦎: 'a + BOOL → 'a DPO;
│ ⦏repDPO⦎: 'a DPO → 'a + BOOL
├───────────
│   (∀ a⦁ absDPO (repDPO a) = a)
│ ∧ (∀ r⦁ repDPO (absDPO r) = r)
■

=GFT
one_one_DPO_lemma =
	⊢ OneOne repDPO ∧ OneOne absDPO 
=TEX

\ignore{
=SML
set_goal([], ⌜OneOne (repDPO: 'a DPO → 'a + BOOL) ∧ OneOne (absDPO: 'a + BOOL → 'a DPO)⌝);
a (strip_asm_tac (get_spec ⌜repDPO⌝));
a (rewrite_tac[get_spec ⌜OneOne⌝]);
a (fc_tac [type_defn_lemma1] THEN asm_rewrite_tac[]);
val one_one_DPO_lemma = save_pop_thm "one_one_DPO_lemma";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏dpoB⦎ : 'a DPO
├───────────
│ dpoB = absDPO(InR F)
■

ⓈHOLCONST
│ ⦏dpoT⦎ : 'a DPO
├───────────
│ dpoT = absDPO(InR T)
■

ⓈHOLCONST
│ ⦏dpoE⦎ : 'a → 'a DPO
├───────────
│ ∀e⦁ dpoE e = absDPO(InL e)
■

ⓈHOLCONST
│ ⦏dpoV⦎ : 'a DPO → 'a
├───────────
│ ∀x⦁ dpoV x = OutL (repDPO x)
■

ⓈHOLCONST
│ ⦏dpoUdef⦎ : 'a DPO → BOOL
├───────────
│ ∀x⦁ dpoUdef x ⇔ x = dpoB
■

ⓈHOLCONST
│ ⦏dpoOdef⦎ : 'a DPO → BOOL
├───────────
│ ∀x⦁ dpoOdef x ⇔ x = dpoT
■

=GFT
⦏dpo_distinct_clauses⦎ =
   ⊢ ¬ dpoT = dpoB
       ∧ ¬ dpoB = dpoT
       ∧ (∀ e
       ⦁ ¬ dpoE e = dpoT
           ∧ ¬ dpoE e = dpoB
           ∧ ¬ dpoT = dpoE e
           ∧ ¬ dpoB = dpoE e)

⦏dpoe_inj_thm⦎ =
	⊢ ∀ e f⦁ (dpoE e = dpoE f) = e = f

⦏dpoe_inj_lemma⦎ =
	⊢ ∀ e f⦁ (dpoE e = dpoE f) = e = f

⦏dpove_lemma1⦎ =
	⊢ ∀ e⦁ dpoV (dpoE e) = e

⦏dpodef_lemma1⦎ =
   ⊢ dpoUdef dpoB
       ∧ dpoOdef dpoT
       ∧ ¬ dpoUdef dpoT
       ∧ ¬ dpoOdef dpoB
       ∧ (∀ e⦁ ¬ dpoUdef (dpoE e) ∧ ¬ dpoOdef (dpoE e))

⦏dpo_cases_thm⦎ =
	⊢ ∀ x⦁ x = dpoB ∨ x = dpoT ∨ (∃ e⦁ x = dpoE e)

⦏dpoev_lemma1⦎ =
	⊢ ∀ x⦁ ¬ dpoUdef x ∧ ¬ dpoOdef x ⇒ dpoE (dpoV x) = x

⦏dpo_rpou_lemma⦎ =
	⊢ RpoU Dpo

⦏dpo_glbs_exist_thm⦎ =
	⊢ GlbsExist Dpo

⦏dpo_lubs_exist_thm⦎ =
	⊢ LubsExist Dpo
=TEX

\ignore{
=SML
set_goal([], ⌜¬ dpoT = (dpoB:'a DPO)
	∧ ¬ dpoB = (dpoT:'a DPO)
	∧ (∀e:'a⦁ ¬ dpoE e = dpoT
		∧ ¬ dpoE e = dpoB
		∧ ¬ dpoT = dpoE e
		∧ ¬ dpoB = dpoE e)⌝);
a (rewrite_tac (map get_spec [⌜dpoT⌝, ⌜dpoB⌝, ⌜dpoE⌝]));
a (strip_asm_tac (get_spec ⌜absDPO⌝));
a (strip_asm_tac one_one_DPO_lemma);
a (fc_tac [oneone_contrapos_lemma]);
a (lemma_tac ⌜¬ InR T = InR F:'a + BOOL⌝ THEN1 rewrite_tac[]);
a (ASM_FC_T rewrite_tac []);
a (POP_ASM_T discard_tac);
a (lemma_tac ⌜¬ InR F = InR T:'a + BOOL⌝ THEN1 rewrite_tac[]);
a (ASM_FC_T rewrite_tac []);
a (strip_tac);
a (POP_ASM_T discard_tac);
a (lemma_tac ⌜¬ InL e = InR T:'a + BOOL⌝ THEN1 rewrite_tac[]);
a (ASM_FC_T rewrite_tac []);
a (POP_ASM_T discard_tac);
a (lemma_tac ⌜¬ InL e = InR F:'a + BOOL⌝ THEN1 rewrite_tac[]);
a (ASM_FC_T rewrite_tac []);
a (POP_ASM_T discard_tac);
a (lemma_tac ⌜¬ InR T = InL e:'a + BOOL⌝ THEN1 rewrite_tac[]);
a (ASM_FC_T rewrite_tac []);
a (POP_ASM_T discard_tac);
a (lemma_tac ⌜¬ InR F = InL e:'a + BOOL⌝ THEN1 rewrite_tac[]);
a (ASM_FC_T rewrite_tac []);
val dpo_distinct_clauses = save_pop_thm "dpo_distinct_clauses";

add_pc_thms "'misc1" [dpo_distinct_clauses, get_spec ⌜absDPO⌝];
set_merge_pcs ["rbjmisc1", "'misc1"];

set_goal([], ⌜(∀e f:'a⦁ ¬ e = f ⇒ ¬ dpoE e = dpoE f)
	∧ (∀e f:'a⦁ dpoE e = dpoE f ⇒ e = f)⌝);
a (rewrite_tac (map get_spec [⌜dpoE⌝]));
a (lemma_tac ⌜∀ e f⦁ ¬ e = f ⇒ ¬ absDPO (InL e) = absDPO (InL f)⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (contr_tac);
a (LEMMA_T ⌜repDPO(absDPO(InL (e:'a))) = repDPO(absDPO(InL f))⌝ (strip_asm_tac o (rewrite_rule[]))
	THEN1 (pure_rewrite_tac[asm_rule ⌜absDPO (InL (e:'a)) = absDPO (InL f)⌝]
		THEN rewrite_tac[]));
(* *** Goal "2" *** *)
a (contr_tac THEN asm_fc_tac[]);
val dpo_distinct_fc_clauses = pop_thm ();

set_goal([], ⌜∀e f⦁ dpoE e = dpoE f ⇔ e = f⌝);
a (REPEAT strip_tac THEN_TRY all_asm_fc_tac [dpo_distinct_fc_clauses]
	THEN asm_rewrite_tac[]);
val dpoe_inj_lemma = save_pop_thm "dpoe_inj_lemma";

add_pc_thms "'misc1" [dpoe_inj_lemma];
set_merge_pcs ["rbjmisc1", "'misc1"];

set_goal([], ⌜∀x⦁ x = dpoB ∨ x = dpoT ∨ (∃e⦁ x = dpoE e)⌝);
a (rewrite_tac [get_spec ⌜dpoB⌝, get_spec ⌜dpoT⌝, get_spec ⌜dpoE⌝]
	THEN REPEAT strip_tac);
a (strip_asm_tac (∀_elim ⌜repDPO x⌝ sum_cases_thm));
(* *** Goal "1" *** *)
a (∃_tac ⌜y⌝ THEN (SYM_ASMS_T rewrite_tac));
(* *** Goal "2" *** *)
a (strip_asm_tac (one_one_DPO_lemma));
a (fc_tac [oneone_contrapos_lemma]);
a (ASM_FC_T (MAP_EVERY (ante_tac)) []);
a (cases_tac ⌜z⌝ THEN_TRY asm_rewrite_tac[]);
val dpo_cases_thm = save_pop_thm "dpo_cases_thm";

set_goal([], ⌜∀e⦁ dpoV(dpoE e) = e⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜dpoE⌝, get_spec ⌜dpoV⌝]
	THEN asm_rewrite_tac[]);
val dpove_lemma1 = save_pop_thm "dpove_lemma1";

add_pc_thms "'misc1" [dpove_lemma1];
set_merge_pcs ["rbjmisc1", "'misc1"];

set_goal([], ⌜dpoUdef dpoB ∧ dpoOdef dpoT
	∧ ¬ dpoUdef dpoT ∧ ¬ dpoOdef dpoB
	∧ ∀e⦁ ¬ dpoUdef (dpoE e) ∧ ¬ dpoOdef (dpoE e)⌝);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac [get_spec ⌜dpoUdef⌝, get_spec ⌜dpoOdef⌝]);
val dpodef_lemma1 = save_pop_thm "dpodef_lemma1";

add_pc_thms "'misc1" [dpodef_lemma1];
set_merge_pcs ["rbjmisc1", "'misc1"];

set_goal([], ⌜∀x⦁ ¬ dpoUdef x ∧ ¬ dpoOdef x ⇒ dpoE(dpoV x) = x⌝);
a (REPEAT ∀_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ dpo_cases_thm) THEN_TRY asm_rewrite_tac[]);
val dpoev_lemma1 = save_pop_thm "dpoev_lemma1";
=TEX
}%ignore

\ignore{
=SML
add_pc_thms "'misc1" (map get_spec [⌜IsDefined⌝, ⌜ValueOf⌝] @ [value_not_undefined_lemma, value_oneone_lemma]);
set_merge_pcs ["rbjmisc1", "'misc1"];
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Dpo⦎ : 'a DPO → 'a DPO → BOOL
├───────────
│ ∀x y⦁ Dpo x y ⇔ x = y ∨ x = dpoB ∨ y = dpoT
■

\ignore{
=SML
set_goal([], ⌜RpoU Dpo⌝);
a (rewrite_tac (map get_spec [⌜RpoU⌝, ⌜Rpo⌝, ⌜Refl⌝, ⌜PartialOrder⌝, ⌜Trans⌝, ⌜Antisym⌝, ⌜Dpo⌝])
	THEN contr_tac
	THEN_TRY var_elim_nth_asm_tac 1
	THEN_TRY rewrite_tac [dpo_distinct_clauses]
	THEN_TRY all_var_elim_asm_tac);
val dpo_rpou_lemma = save_pop_thm "dpo_rpou_lemma";

set_goal([], ⌜GlbsExist Dpo⌝);
a (rewrite_tac [get_spec ⌜GlbsExist⌝, get_spec ⌜IsGlb⌝, get_spec ⌜IsLb⌝, get_spec ⌜Dpo⌝]
	THEN REPEAT strip_tac);
a (cases_tac ⌜dpoB ∈ s⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜dpoB⌝ THEN_TRY asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜dpoB⌝);
(* *** Goal "2" *** *)
a (PC_T1 "hol" cases_tac ⌜s = {dpoT}⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜dpoT⌝ THEN asm_rewrite_tac []
	THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a (PC_T1 "hol" cases_tac ⌜s = {}⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.1" *** *)
a (∃_tac ⌜dpoT⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a (PC_T1 "hol" cases_tac ⌜∃e⦁ s = {dpoE e} ⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.2.1" *** *)
a (∃_tac ⌜dpoE e⌝ THEN_TRY asm_rewrite_tac[]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.2.1.1" *** *)
a (DROP_ASM_T ⌜¬ dpoE e = x⌝ ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.1.2" *** *)
a (spec_nth_asm_tac 2 ⌜dpoE e⌝);
(* *** Goal "2.2.2.2" *** *)
a (cases_tac ⌜∃f g⦁ ¬ f = g ∧ dpoE f ∈ s ∧ dpoE g ∈ s⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.1" *** *)
a (∃_tac ⌜dpoB⌝ THEN_TRY asm_rewrite_tac[]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (spec_nth_asm_tac 1 ⌜dpoE f⌝);
a (spec_nth_asm_tac 2 ⌜dpoE g⌝);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2" *** *)
a (cases_tac ⌜∃h⦁ dpoE h ∈ s⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2.1" *** *)
a (∃_tac ⌜dpoE h⌝ THEN_TRY asm_rewrite_tac[]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2.1.1" *** *)
a (asm_fc_tac[]);
a (LEMMA_T ⌜s = {dpoE h; dpoT}⌝ asm_tac
	THEN1 (asm_rewrite_tac [] THEN strip_tac));
(* *** Goal "2.2.2.2.2.1.1.1" *** *)
a (strip_asm_tac (∀_elim ⌜x'⌝ dpo_cases_thm)
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2.1.1.1.1" *** *)
a (lemma_tac ⌜x = dpoT⌝
	THEN1 (strip_asm_tac (∀_elim ⌜x⌝ dpo_cases_thm)
		THEN_TRY asm_rewrite_tac[]));
(* *** Goal "2.2.2.2.2.1.1.1.1.1" *** *)
a (var_elim_asm_tac ⌜x = dpoB⌝);
(* *** Goal "2.2.2.2.2.1.1.1.1.2" *** *)
a (var_elim_asm_tac ⌜x = dpoE e⌝);
a (var_elim_asm_tac ⌜x' = dpoT⌝);
a (all_asm_fc_tac[]);
a (var_elim_asm_tac ⌜e = h⌝);
(* *** Goal "2.2.2.2.2.1.1.1.1.3" *** *)
a (var_elim_asm_tac ⌜x = dpoT⌝);
(* *** Goal "2.2.2.2.2.1.1.1.2" *** *)
a (var_elim_asm_tac ⌜x' = dpoE e⌝);
a (REPEAT strip_tac);
(* *** Goal "2.2.2.2.2.1.1.1.2.1" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "2.2.2.2.2.1.1.1.2.2" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2.1.1.2" *** *)
a (var_elim_asm_tac ⌜s = {dpoE h; dpoT}⌝);
(* *** Goal "2.2.2.2.2.1.1.2.1" *** *)
a (DROP_ASM_T ⌜¬ dpoE h = x⌝ ante_tac
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2.1.1.2.2" *** *)
a (DROP_ASM_T ⌜¬ dpoE h = x⌝ ante_tac
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2.1.2" *** *)
a (spec_nth_asm_tac 2 ⌜dpoE h⌝);
(* *** Goal "2.2.2.2.2.2" *** *)
a (swap_nth_asm_concl_tac 4
	THEN rewrite_tac[]
	THEN contr_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ dpo_cases_thm));
(* *** Goal "2.2.2.2.2.2.1" *** *)
a (var_elim_asm_tac ⌜x = dpoB⌝);
(* *** Goal "2.2.2.2.2.2.2" *** *)
a (var_elim_asm_tac ⌜x = dpoT⌝);
a (DROP_NTH_ASM_T 6 ante_tac
	THEN asm_rewrite_tac[]
	THEN contr_tac);
(* *** Goal "2.2.2.2.2.2.2.1" *** *)
a (strip_asm_tac (∀_elim ⌜x⌝ dpo_cases_thm));
(* *** Goal "2.2.2.2.2.2.2.1.1" *** *)
a (var_elim_asm_tac ⌜x = dpoB⌝);
(* *** Goal "2.2.2.2.2.2.2.1.2" *** *)
a (var_elim_asm_tac ⌜x = dpoE e⌝);
a (all_asm_fc_tac[]);
(* *** Goal "2.2.2.2.2.2.2.2" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2.2.3" *** *)
a (var_elim_asm_tac ⌜x = dpoE e⌝);
a (all_asm_fc_tac[]);
val dpo_glbs_exist_thm = save_pop_thm "dpo_glbs_exist_thm";

set_goal([], ⌜LubsExist Dpo⌝);
a (rewrite_tac [get_spec ⌜LubsExist⌝, get_spec ⌜IsLub⌝, get_spec ⌜IsUb⌝, get_spec ⌜Dpo⌝]
	THEN REPEAT strip_tac);
a (cases_tac ⌜dpoT ∈ s⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜dpoT⌝ THEN_TRY asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜dpoT⌝);
(* *** Goal "2" *** *)
a (PC_T1 "hol" cases_tac ⌜s = {dpoB}⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜dpoB⌝ THEN asm_rewrite_tac []
	THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a (PC_T1 "hol" cases_tac ⌜s = {}⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.1" *** *)
a (∃_tac ⌜dpoB⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a (PC_T1 "hol" cases_tac ⌜∃f⦁ s = {dpoE f} ⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.2.1" *** *)
a (∃_tac ⌜dpoE f⌝ THEN_TRY asm_rewrite_tac[]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (spec_nth_asm_tac 2 ⌜dpoE f⌝);
(* *** Goal "2.2.2.2" *** *)
a (cases_tac ⌜∃f g⦁ ¬ f = g ∧ dpoE f ∈ s ∧ dpoE g ∈ s⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.1" *** *)
a (∃_tac ⌜dpoT⌝ THEN_TRY asm_rewrite_tac[]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (spec_nth_asm_tac 2 ⌜dpoE f⌝);
a (spec_nth_asm_tac 3 ⌜dpoE g⌝);
a (POP_ASM_T ante_tac THEN SYM_ASMS_T rewrite_tac);
(* *** Goal "2.2.2.2.2" *** *)
a (cases_tac ⌜∃h⦁ dpoE h ∈ s⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2.1" *** *)
a (∃_tac ⌜dpoE h⌝ THEN_TRY asm_rewrite_tac[]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2.1.1" *** *)
a (asm_fc_tac[]);
a (LEMMA_T ⌜s = {dpoE h; dpoB}⌝ asm_tac
	THEN1 (asm_rewrite_tac [] THEN strip_tac));
(* *** Goal "2.2.2.2.2.1.1.1" *** *)
a (strip_asm_tac (∀_elim ⌜x'⌝ dpo_cases_thm)
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.2.2.2.1.1.1.1" *** *)
a (lemma_tac ⌜x = dpoB⌝
	THEN1 (strip_asm_tac (∀_elim ⌜x⌝ dpo_cases_thm)
		THEN_TRY asm_rewrite_tac[]));
(* *** Goal "2.2.2.2.2.1.1.1.1.1" *** *)
a (var_elim_asm_tac ⌜x = dpoT⌝);
(* *** Goal "2.2.2.2.2.1.1.1.1.2" *** *)
a (var_elim_asm_tac ⌜x = dpoE e⌝);
a (var_elim_asm_tac ⌜x' = dpoB⌝);
a (all_asm_fc_tac[]);
a (var_elim_asm_tac ⌜e = h⌝);
(* *** Goal "2.2.2.2.2.1.1.1.1.3" *** *)
a (var_elim_asm_tac ⌜x = dpoB⌝);
(* *** Goal "2.2.2.2.2.1.1.1.2" *** *)
a (var_elim_asm_tac ⌜x' = dpoE e⌝);
a (REPEAT strip_tac);
(* *** Goal "2.2.2.2.2.1.1.1.2.1" *** *)
a (all_asm_fc_tac[]);
a (var_elim_asm_tac ⌜e = h⌝);
(* *** Goal "2.2.2.2.2.1.1.2" *** *)
a (var_elim_asm_tac ⌜s = {dpoE h; dpoB}⌝);
(* *** Goal "2.2.2.2.2.1.2" *** *)
a (spec_nth_asm_tac 2 ⌜dpoE h⌝);
(* *** Goal "2.2.2.2.2.2" *** *)
a (swap_nth_asm_concl_tac 4
	THEN rewrite_tac[]
	THEN contr_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ dpo_cases_thm));
(* *** Goal "2.2.2.2.2.2.1" *** *)
a (var_elim_asm_tac ⌜x = dpoB⌝);
a (DROP_NTH_ASM_T 6 ante_tac
	THEN asm_rewrite_tac[]
	THEN contr_tac);
(* *** Goal "2.2.2.2.2.2.1.1" *** *)
a (strip_asm_tac (∀_elim ⌜x⌝ dpo_cases_thm));
(* *** Goal "2.2.2.2.2.2.1.1.1" *** *)
a (var_elim_asm_tac ⌜x = dpoT⌝);
(* *** Goal "2.2.2.2.2.2.1.1.2" *** *)
a (var_elim_asm_tac ⌜x = dpoE e⌝);
a (all_asm_fc_tac[]);
(* *** Goal "2.2.2.2.2.2.1.2" *** *)
a (var_elim_asm_tac ⌜x = dpoB⌝);
(* *** Goal "2.2.2.2.2.2.2" *** *)
a (var_elim_asm_tac ⌜x = dpoT⌝);
(* *** Goal "2.2.2.2.2.2.3" *** *)
a (var_elim_asm_tac ⌜x = dpoE e⌝);
a (all_asm_fc_tac[]);
val dpo_lubs_exist_thm = save_pop_thm "dpo_lubs_exist_thm";
=TEX
}%ignore

\section{TRUTH VALUES}

I am uncertain at this point whether to work with three or four truth values, so both of these are provided for here.

\subsection{Three Valued}

=SML
declare_type_abbrev("⦏TTV⦎", [], ⓣBOOL OPT⌝);
=TEX

ⓈHOLCONST
│ ⦏pTrue⦎ : TTV
├───────────
│ pTrue = Value T
■

ⓈHOLCONST
│ ⦏pFalse⦎ : TTV
├───────────
│ pFalse = Value F
■

ⓈHOLCONST
│ ⦏pU⦎ : TTV
├───────────
│ pU = Undefined
■

=GFT
⦏tv_cases_thm⦎ =
	⊢ ∀ x⦁ x = pTrue ∨ x = pFalse ∨ x = pU

⦏tv_distinct_clauses⦎ =
	⊢ ¬ pTrue = pFalse
             ∧ ¬ pTrue = pU
             ∧ ¬ pFalse = pTrue
             ∧ ¬ pFalse = pU
             ∧ ¬ pU = pTrue
             ∧ ¬ pU = pFalse
=TEX

\ignore{
=SML
set_merge_pcs ["rbjmisc", "'misc1"];

set_goal([], ⌜∀x⦁ x = pTrue ∨ x = pFalse ∨ x = pU⌝);
a (rewrite_tac (map get_spec [⌜pTrue⌝, ⌜pFalse⌝, ⌜pU⌝]) THEN prove_tac[]);
a (ante_tac (∀_elim ⌜x⌝ opt_cases_thm));
a (PC_T "hol" strip_tac);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac);
a (LEMMA_T ⌜y = T ∨ y = F⌝ (STRIP_THM_THEN asm_tac) THEN1 prove_tac[]
	THEN var_elim_nth_asm_tac 1
	THEN strip_tac);
val tv_cases_thm = save_pop_thm "tv_cases_thm";

set_goal([], ⌜¬ pTrue = pFalse
	∧ ¬ pTrue = pU
	∧ ¬ pFalse = pTrue
	∧ ¬ pFalse = pU
	∧ ¬ pU = pTrue
	∧ ¬ pU = pFalse
⌝);
a (rewrite_tac (map get_spec [⌜pTrue⌝, ⌜pFalse⌝, ⌜pU⌝]));
val tv_distinct_clauses = save_pop_thm "tv_distinct_clauses";

add_pc_thms "'misc1" (map get_spec [] @ [tv_distinct_clauses]);
set_merge_pcs ["rbjmisc", "'misc1"];
=TEX
}%ignore

=SML
declare_infix(300, "≤⋎t⋎3");
=TEX

=SML
declare_type_abbrev ("REL", ["'a"], ⓣ'a → 'a → BOOL⌝);
=TEX

First an ordering on the ``truth values'' is defined.

ⓈHOLCONST
│ ⦏$≤⋎t⋎3⦎ : TTV REL
├───────────
│ ∀ t1 t2⦁ 
│	t1 ≤⋎t⋎3 t2 ⇔ t1 = t2 ∨ t1 = pU	
■

=GFT
⦏≤⋎t⋎3_refl_thm⦎ =
	⊢ ∀ x⦁ x ≤⋎t⋎3 x

⦏≤⋎t⋎3_trans_thm⦎ =
	⊢ ∀ x y z⦁ x ≤⋎t⋎3 y ∧ y ≤⋎t⋎3 z ⇒ x ≤⋎t⋎3 z

⦏≤⋎t⋎3_antisym_thm⦎ =
	⊢ ∀ x y⦁ x ≤⋎t⋎3 y ∧ y ≤⋎t⋎3 x ⇒ x = y

⦏≤⋎t⋎3_partialorder_thm⦎ =
	⊢ ∀ Y⦁ PartialOrder (Y, $≤⋎t⋎3)

⦏≤⋎t⋎3_clauses⦎ =
   ⊢ pU ≤⋎t⋎3 pTrue
       ∧ pU ≤⋎t⋎3 pFalse
       ∧ ¬ pTrue ≤⋎t⋎3 pU
       ∧ ¬ pFalse ≤⋎t⋎3 pU
       ∧ ¬ pFalse ≤⋎t⋎3 pTrue
       ∧ ¬ pTrue ≤⋎t⋎3 pFalse

⦏lin_≤⋎t⋎3_lemma⦎ =
   ⊢ ∀ Y⦁ LinearOrder (Y, $≤⋎t⋎3) ⇔ ¬ pTrue ∈ Y ∨ ¬ pFalse ∈ Y

⦏lin_≤⋎t⋎3_cases_lemma⦎ =
   ⊢ ∀ Y
     ⦁ LinearOrder (Y, $≤⋎t⋎3)
         ⇔ Y = {}
           ∨ Y = {pU}
           ∨ Y = {pTrue}
           ∨ Y = {pFalse}
           ∨ Y = {pU; pTrue}
           ∨ Y = {pU; pFalse}

⦏≤⋎t⋎3_isub_cases_lemma⦎ =
   ⊢ ∀ Y
     ⦁ IsUb $≤⋎t⋎3 {} = (λ x⦁ T)
         ∧ IsUb $≤⋎t⋎3 {pU} = (λ x⦁ T)
         ∧ IsUb $≤⋎t⋎3 {pTrue} = (λ x⦁ x = pTrue)
         ∧ IsUb $≤⋎t⋎3 {pFalse} = (λ x⦁ x = pFalse)
         ∧ IsUb $≤⋎t⋎3 {pU; pTrue} = (λ x⦁ x = pTrue)
         ∧ IsUb $≤⋎t⋎3 {pU; pFalse} = (λ x⦁ x = pFalse)

⦏≤⋎t⋎3_islub_clauses⦎ =
   ⊢ ∀ Y
     ⦁ IsLub $≤⋎t⋎3 {} pU
         ∧ IsLub $≤⋎t⋎3 {pU} pU
         ∧ IsLub $≤⋎t⋎3 {pTrue} pTrue
         ∧ IsLub $≤⋎t⋎3 {pFalse} pFalse
         ∧ IsLub $≤⋎t⋎3 {pU; pTrue} pTrue
         ∧ IsLub $≤⋎t⋎3 {pU; pFalse} pFalse

⦏chaincomplete_≤⋎t⋎3_kemma⦎ =
	⊢ ChainComplete (Universe, $≤⋎t⋎3)

⦏ccrpou_≤⋎t⋎3_thm⦎ =
	⊢ CcRpoU $≤⋎t⋎3
=TEX

\ignore{
=SML
set_goal([], ⌜∀x⦁ x ≤⋎t⋎3 x⌝);
a (rewrite_tac [get_spec ⌜$≤⋎t⋎3⌝]);
val ≤⋎t⋎3_refl_thm = save_pop_thm "≤⋎t⋎3_refl_thm";

set_goal([], ⌜∀x y z⦁ x ≤⋎t⋎3 y ∧ y ≤⋎t⋎3 z ⇒ x ≤⋎t⋎3 z⌝);
a (rewrite_tac [get_spec ⌜$≤⋎t⋎3⌝]
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
a (all_var_elim_asm_tac);
val ≤⋎t⋎3_trans_thm = save_pop_thm "≤⋎t⋎3_trans_thm";

set_goal([], ⌜∀x y⦁ x ≤⋎t⋎3 y ∧ y ≤⋎t⋎3 x ⇒ x = y⌝);
a (rewrite_tac [get_spec ⌜$≤⋎t⋎3⌝]
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
val ≤⋎t⋎3_antisym_thm = save_pop_thm "≤⋎t⋎3_antisym_thm";

set_goal([], ⌜(∀x⦁ pU ≤⋎t⋎3 x)
	∧ ¬ pTrue ≤⋎t⋎3 pU
	∧ ¬ pFalse ≤⋎t⋎3 pU
	∧ ¬ pFalse ≤⋎t⋎3 pTrue
	∧ ¬ pTrue ≤⋎t⋎3 pFalse⌝);
a (rewrite_tac [get_spec ⌜$≤⋎t⋎3⌝] THEN prove_tac[]);
val ≤⋎t⋎3_clauses = save_pop_thm "≤⋎t⋎3_clauses";

add_pc_thms "'misc1" (map get_spec [] @ [≤⋎t⋎3_refl_thm, ≤⋎t⋎3_clauses]);
set_merge_pcs ["rbjmisc", "'misc1"];

set_goal([], ⌜∀Y⦁ PartialOrder (Y, $≤⋎t⋎3)⌝);
a (rewrite_tac (map get_spec [⌜PartialOrder⌝, ⌜Antisym⌝, ⌜Trans⌝])
	THEN contr_tac);
a (all_fc_tac [≤⋎t⋎3_antisym_thm]);
a (all_fc_tac [≤⋎t⋎3_trans_thm]);
val ≤⋎t⋎3_partialorder_thm = save_pop_thm "≤⋎t⋎3_partialorder_thm";

set_goal([], ⌜∀Y⦁ LinearOrder (Y, $≤⋎t⋎3) ⇔ ¬ pTrue ∈ Y ∨ ¬ pFalse ∈ Y⌝);
a (rewrite_tac [get_spec ⌜LinearOrder⌝, get_spec ⌜Trich⌝, ≤⋎t⋎3_partialorder_thm]
	THEN contr_tac);
(* *** Goal "1" *** *)
a (REPEAT (asm_fc_tac[]));
(* *** Goal "2" *** *)
a (strip_asm_tac (list_∀_elim [⌜x⌝] tv_cases_thm)
	THEN asm_prove_tac[]);
a (strip_asm_tac (list_∀_elim [⌜y⌝] tv_cases_thm)
	THEN asm_prove_tac[]);
(* *** Goal "3" *** *)
a (strip_asm_tac (list_∀_elim [⌜x⌝] tv_cases_thm)
	THEN asm_prove_tac[]);
a (strip_asm_tac (list_∀_elim [⌜y⌝] tv_cases_thm)
	THEN asm_prove_tac[]);
val lin_≤⋎t⋎3_lemma = save_pop_thm "lin_≤⋎t⋎3_lemma";

set_merge_pcs ["rbjmisc", "'misc1"];

set_goal([], ⌜∀Y⦁ LinearOrder (Y, $≤⋎t⋎3) ⇔
	  Y = {}
	∨ Y = {pU} ∨ Y = {pTrue} ∨ Y = {pFalse}
	∨ Y = {pU; pTrue} ∨ Y = {pU; pFalse}⌝);
a (rewrite_tac [lin_≤⋎t⋎3_lemma] THEN REPEAT ∀_tac);
a (		cases_tac ⌜pTrue ∈ Y⌝
	THEN	cases_tac ⌜pFalse ∈ Y⌝
	THEN	cases_tac ⌜pU ∈ Y⌝
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (contr_tac THEN var_elim_nth_asm_tac 1);
(* *** Goal "2" *** *)
a (contr_tac THEN var_elim_nth_asm_tac 1);
(* *** Goal "3" *** *)
set_merge_pcs ["rbjmisc1", "'misc1"];
a (LEMMA_T ⌜Y = {pU; pTrue}⌝ asm_tac
	THEN1 (asm_rewrite_tac[]
		THEN ∀_tac
		THEN (strip_asm_tac (∀_elim ⌜x:TTV⌝ tv_cases_thm)
		THEN asm_rewrite_tac[]))
	THEN asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (LEMMA_T ⌜Y = {pTrue}⌝ asm_tac
	THEN1 (asm_rewrite_tac[]
		THEN ∀_tac
		THEN (strip_asm_tac (∀_elim ⌜x:TTV⌝ tv_cases_thm)
		THEN asm_rewrite_tac[]))
	THEN asm_rewrite_tac[]);
(* *** Goal "5" *** *)
a (LEMMA_T ⌜Y = {pU; pFalse}⌝ asm_tac
	THEN1 (asm_rewrite_tac[]
		THEN ∀_tac
		THEN (strip_asm_tac (∀_elim ⌜x:TTV⌝ tv_cases_thm)
		THEN asm_rewrite_tac[]))
	THEN asm_rewrite_tac[]);
(* *** Goal "6" *** *)
a (LEMMA_T ⌜Y = {pFalse}⌝ asm_tac
	THEN1 (asm_rewrite_tac[]
		THEN ∀_tac
		THEN (strip_asm_tac (∀_elim ⌜x:TTV⌝ tv_cases_thm)
		THEN asm_rewrite_tac[]))
	THEN asm_rewrite_tac[]);
(* *** Goal "7" *** *)
a (LEMMA_T ⌜Y = {pU}⌝ asm_tac
	THEN1 (asm_rewrite_tac[]
		THEN ∀_tac
		THEN (strip_asm_tac (∀_elim ⌜x:TTV⌝ tv_cases_thm)
		THEN asm_rewrite_tac[]))
	THEN asm_rewrite_tac[]);
(* *** Goal "8" *** *)
a (LEMMA_T ⌜Y = {}⌝ asm_tac
	THEN1 (asm_rewrite_tac[]
		THEN ∀_tac
		THEN (strip_asm_tac (∀_elim ⌜x:TTV⌝ tv_cases_thm)
		THEN asm_rewrite_tac[]))
	THEN asm_rewrite_tac[]);
val lin_≤⋎t⋎3_cases_lemma = pop_thm ();

set_goal([], ⌜∀Y⦁ 
	  IsUb $≤⋎t⋎3 {} = (λx⦁ T)
	∧ IsUb $≤⋎t⋎3 {pU} = (λx⦁ T) ∧ IsUb $≤⋎t⋎3 {pTrue} = (λx⦁ x = pTrue) ∧ IsUb $≤⋎t⋎3 {pFalse} = (λx⦁ x = pFalse)
	∧ IsUb $≤⋎t⋎3 {pU; pTrue} = (λx⦁ x = pTrue) ∧ IsUb $≤⋎t⋎3 {pU; pFalse} = (λx⦁ x = pFalse)⌝);
a (rewrite_tac [get_spec ⌜IsUb⌝]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜pTrue⌝);
a (strip_asm_tac (∀_elim ⌜x⌝ tv_cases_thm) THEN_TRY asm_rewrite_tac[]
	THEN var_elim_nth_asm_tac 1);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 1 ⌜pFalse⌝);
a (strip_asm_tac (∀_elim ⌜x⌝ tv_cases_thm) THEN_TRY asm_rewrite_tac[]
	THEN var_elim_nth_asm_tac 1);
(* *** Goal "3" *** *)
a (spec_nth_asm_tac 1 ⌜pTrue⌝);
a (strip_asm_tac (∀_elim ⌜x⌝ tv_cases_thm) THEN_TRY asm_rewrite_tac[]
	THEN var_elim_nth_asm_tac 1);
(* *** Goal "4" *** *)
a (spec_nth_asm_tac 1 ⌜pFalse⌝);
a (strip_asm_tac (∀_elim ⌜x⌝ tv_cases_thm) THEN_TRY asm_rewrite_tac[]
	THEN var_elim_nth_asm_tac 1);
val ≤⋎t⋎3_isub_cases_lemma = pop_thm ();

set_goal([], ⌜∀Y⦁ 
	  IsLub $≤⋎t⋎3 {} pU
	∧ IsLub $≤⋎t⋎3 {pU} pU ∧ IsLub $≤⋎t⋎3 {pTrue} pTrue ∧ IsLub $≤⋎t⋎3 {pFalse} pFalse
	∧ IsLub $≤⋎t⋎3 {pU; pTrue} pTrue ∧ IsLub $≤⋎t⋎3 {pU; pFalse} pFalse⌝);
a (rewrite_tac [get_spec ⌜IsLub⌝]);
a (rewrite_tac [≤⋎t⋎3_isub_cases_lemma]);
a (REPEAT strip_tac THEN asm_rewrite_tac[]);
val ≤⋎t⋎3_islub_clauses = pop_thm ();

set_merge_pcs ["rbjmisc", "'misc1"];

set_goal([], ⌜ChainComplete (Universe, $≤⋎t⋎3)⌝);
a (rewrite_tac (map get_spec [⌜ChainComplete⌝]));
a (rewrite_tac [lin_≤⋎t⋎3_cases_lemma]);
a (REPEAT strip_tac THEN asm_rewrite_tac[]);
a (∃_tac ⌜pU⌝ THEN rewrite_tac [≤⋎t⋎3_islub_clauses]);
a (∃_tac ⌜pU⌝ THEN rewrite_tac [≤⋎t⋎3_islub_clauses]);
a (∃_tac ⌜pTrue⌝ THEN rewrite_tac [≤⋎t⋎3_islub_clauses]);
a (∃_tac ⌜pFalse⌝ THEN rewrite_tac [≤⋎t⋎3_islub_clauses]);
a (∃_tac ⌜pTrue⌝ THEN rewrite_tac [≤⋎t⋎3_islub_clauses]);
a (∃_tac ⌜pFalse⌝ THEN rewrite_tac [≤⋎t⋎3_islub_clauses]);
val chaincomplete_≤⋎t⋎3_kemma = pop_thm ();

set_goal([], ⌜CcRpoU $≤⋎t⋎3⌝);
a (rewrite_tac (map get_spec [⌜CcRpoU⌝, ⌜CcRpo⌝, ⌜Rpo⌝, ⌜Refl⌝]
	@ [≤⋎t⋎3_partialorder_thm, chaincomplete_≤⋎t⋎3_kemma]));
val ccrpou_≤⋎t⋎3_thm = save_pop_thm "ccrpou_≤⋎t⋎3_thm";
=TEX
}%ignore

\subsection{Four Valued}

=SML
declare_type_abbrev("⦏FTV⦎", [], ⓣBOOL DPO⌝);
=TEX

ⓈHOLCONST
│ ⦏fTrue⦎ : FTV
├───────────
│ fTrue = dpoE T
■

ⓈHOLCONST
│ ⦏fFalse⦎ : FTV
├───────────
│ fFalse = dpoE F
■

ⓈHOLCONST
│ ⦏fB⦎ : FTV
├───────────
│ fB = dpoB
■

ⓈHOLCONST
│ ⦏fT⦎ : FTV
├───────────
│ fT = dpoT
■

=GFT
⦏ftv_cases_thm⦎ =
	⊢ ∀ x⦁ x = fTrue ∨ x = fFalse ∨ x = fB ∨ x = fT
⦏ftv_distinct_clauses⦎ =
	⊢ ¬ fTrue = fFalse
       ∧ ¬ fTrue = fB
       ∧ ¬ fTrue = fT
       ∧ ¬ fFalse = fTrue
       ∧ ¬ fFalse = fB
       ∧ ¬ fFalse = fT
       ∧ ¬ fB = fTrue
       ∧ ¬ fB = fFalse
       ∧ ¬ fB = fT
       ∧ ¬ fT = fTrue
       ∧ ¬ fT = fFalse
       ∧ ¬ fT = fB

⦏ftvs_cases_thm⦎ =
   ⊢ ∀ x
     ⦁ x = {}
         ∨ x = {fB}
         ∨ x = {fFalse}
         ∨ x = {fTrue}
         ∨ x = {fT}
         ∨ x = {fB; fFalse}
         ∨ x = {fB; fTrue}
         ∨ x = {fB; fT}
         ∨ x = {fFalse; fTrue}
         ∨ x = {fFalse; fT}
         ∨ x = {fTrue; fT}
         ∨ x = {fB; fFalse; fTrue}
         ∨ x = {fB; fFalse; fT}
         ∨ x = {fB; fTrue; fT}
         ∨ x = {fFalse; fTrue; fT}
         ∨ x = {fB; fFalse; fTrue; fT}
=TEX

\ignore{
=SML
set_merge_pcs ["rbjmisc1", "'misc1"];

set_goal([], ⌜∀x⦁ x = fTrue ∨ x = fFalse ∨ x = fB ∨ x = fT⌝);
a (rewrite_tac (map get_spec [⌜fTrue⌝, ⌜fFalse⌝, ⌜fB⌝, ⌜fT⌝]) THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ dpo_cases_thm)
	THEN asm_rewrite_tac[]);
a (cases_tac ⌜e⌝ THEN asm_rewrite_tac[]);
val ftv_cases_thm = save_pop_thm "ftv_cases_thm";

set_goal([], ⌜¬ fTrue = fFalse
	∧ ¬ fTrue = fB
	∧ ¬ fTrue = fT
	∧ ¬ fFalse = fTrue
	∧ ¬ fFalse = fB
	∧ ¬ fFalse = fT
	∧ ¬ fB = fTrue
	∧ ¬ fB = fFalse
	∧ ¬ fB = fT
	∧ ¬ fT = fTrue
	∧ ¬ fT = fFalse
	∧ ¬ fT = fB
⌝);
a (LEMMA_T ⌜¬ F = T⌝ asm_tac THEN1 prove_tac[]);
a (fc_tac [dpo_distinct_fc_clauses]);
a (rewrite_tac (map get_spec [⌜fTrue⌝, ⌜fFalse⌝, ⌜fB⌝, ⌜fT⌝]) THEN prove_tac[dpo_distinct_clauses]);
val ftv_distinct_clauses = save_pop_thm "ftv_distinct_clauses";

add_pc_thms "'misc1" (map get_spec [] @ [ftv_distinct_clauses]);
set_merge_pcs ["rbjmisc1", "'misc1"];

set_goal([], ⌜∀x⦁
	x = {}
	∨ x = {fB}
	∨ x = {fFalse}
	∨ x = {fTrue}
	∨ x = {fT}
	∨ x = {fB; fFalse}
	∨ x = {fB; fTrue}
	∨ x = {fB; fT}
	∨ x = {fFalse; fTrue}
	∨ x = {fFalse; fT}
	∨ x = {fTrue; fT}
	∨ x = {fB; fFalse; fTrue}
	∨ x = {fB; fFalse; fT}
	∨ x = {fB; fTrue; fT}
	∨ x = {fFalse; fTrue; fT}
	∨ x = {fB; fFalse; fTrue; fT}
⌝);
a (	strip_tac);
a (	cases_tac ⌜fTrue ∈ x⌝
	THEN	cases_tac ⌜fFalse ∈ x⌝
	THEN	cases_tac ⌜fB ∈ x⌝
	THEN	cases_tac ⌜fT ∈ x⌝);
(* *** Goal "1" *** *)
a (LEMMA_T  ⌜x = {fB; fFalse; fTrue; fT}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (LEMMA_T  ⌜x = {fB; fFalse; fTrue}⌝ (PC_T1 "hol1" rewrite_thm_tac)
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (LEMMA_T  ⌜x = {fFalse; fTrue; fT}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (LEMMA_T  ⌜x = {fFalse; fTrue}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
(* *** Goal "5" *** *)
a (LEMMA_T  ⌜x = {fB; fTrue; fT}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
(* *** Goal "6" *** *)
a (LEMMA_T  ⌜x = {fB; fTrue}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
(* *** Goal "7" *** *)
a (LEMMA_T  ⌜x = {fTrue; fT}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
(* *** Goal "8" *** *)
a (LEMMA_T  ⌜x = {fTrue}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
(* *** Goal "9" *** *)
a (LEMMA_T  ⌜x = {fB; fFalse; fT}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
(* *** Goal "10" *** *)
a (LEMMA_T  ⌜x = {fB; fFalse}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
(* *** Goal "11" *** *)
a (LEMMA_T  ⌜x = {fFalse; fT}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
(* *** Goal "12" *** *)
a (LEMMA_T  ⌜x = {fFalse}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
(* *** Goal "13" *** *)
a (LEMMA_T  ⌜x = {fB; fT}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
(* *** Goal "14" *** *)
a (LEMMA_T  ⌜x = {fB}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
(* *** Goal "15" *** *)
a (LEMMA_T  ⌜x = {fT}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
(* *** Goal "16" *** *)
a (LEMMA_T  ⌜x = {}⌝ rewrite_thm_tac
	THEN1 PC_T1 "hol1" rewrite_tac[]
		THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜x'⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
val ftvs_cases_thm = save_pop_thm "ftvs_cases_thm";
=TEX
}%ignore

=SML
declare_infix(300, "≤⋎t⋎4");
=TEX

Now an ordering on these truth values is defined.

ⓈHOLCONST
│ ⦏$≤⋎t⋎4⦎ : FTV REL
├───────────
│ ∀ t1 t2⦁ 
│	t1 ≤⋎t⋎4 t2 ⇔ t1 = t2 ∨ t1 = fB ∨ t2 = fT
■

=GFT
⦏≤⋎t⋎4_dpo_thm⦎ =
	⊢ $≤⋎t⋎4 = Dpo

⦏≤⋎t⋎4_refl_thm⦎ =
	⊢ ∀ x⦁ x ≤⋎t⋎4 x

⦏≤⋎t⋎4_trans_thm⦎ =
	⊢ ∀ x y z⦁ x ≤⋎t⋎4 y ∧ y ≤⋎t⋎4 z ⇒ x ≤⋎t⋎4 z

⦏≤⋎t⋎4_antisym_thm⦎ =
	⊢ ∀ x y⦁ x ≤⋎t⋎4 y ∧ y ≤⋎t⋎4 x ⇒ x = y

⦏≤⋎t⋎4_antisym_thm2⦎ =
	⊢ Antisym (Universe, $≤⋎t⋎4)

⦏ft_fb_thm⦎ =
	⊢ ∀ x⦁ (fT ≤⋎t⋎4 x ⇔ x = fT) ∧ (x ≤⋎t⋎4 fB ⇔ x = fB)

⦏≤⋎t⋎4_partialorder_thm⦎ =
	⊢ ∀ Y⦁ PartialOrder (Y, $≤⋎t⋎4)

⦏≤⋎t⋎4_lin_lemma⦎ =
	⊢ ∀ Y⦁ LinearOrder (Y, $≤⋎t⋎4) = (¬ fTrue ∈ Y ∨ ¬ fFalse ∈ Y)

⦏≤⋎t⋎4_clauses⦎ =
   ⊢ (∀ x⦁ fB ≤⋎t⋎4 x)
       ∧ (∀ x⦁ x ≤⋎t⋎4 fT)
       ∧ ¬ fTrue ≤⋎t⋎4 fB
       ∧ ¬ fFalse ≤⋎t⋎4 fB
       ∧ ¬ fT ≤⋎t⋎4 fB
       ∧ ¬ fFalse ≤⋎t⋎4 fTrue
       ∧ ¬ fT ≤⋎t⋎4 fTrue
       ∧ ¬ fTrue ≤⋎t⋎4 fFalse
       ∧ ¬ fT ≤⋎t⋎4 fFalse

⦏≤⋎t⋎4_lin_cases_lemma⦎ =
   ⊢ ∀ Y
     ⦁ LinearOrder (Y, $≤⋎t⋎4)
         = (Y = {}
           ∨ Y = {fB}
           ∨ Y = {fTrue}
           ∨ Y = {fFalse}
           ∨ Y = {fT}
           ∨ Y = {fB; fTrue}
           ∨ Y = {fB; fFalse}
           ∨ Y = {fB; fT}
           ∨ Y = {fTrue; fT}
           ∨ Y = {fFalse; fT}
           ∨ Y = {fB; fTrue; fT}
           ∨ Y = {fB; fFalse; fT})

⦏gt_false_true_lemma⦎ =
   ⊢ ∀ x⦁ fFalse ≤⋎t⋎4 x ∧ fTrue ≤⋎t⋎4 x ⇒ x = fT

⦏lt_false_true_lemma⦎ =
   ⊢ ∀ x⦁ x ≤⋎t⋎4 fFalse ∧ x ≤⋎t⋎4 fTrue ⇒ x = fB

⦏gt_ft_lemma⦎ =
   ⊢ ∀ x⦁ fT ≤⋎t⋎4 x ⇒ x = fT

⦏lt_fb_lemma⦎ =
   ⊢ ∀ x⦁ x ≤⋎t⋎4 fB ⇒ x = fB

⦏sg_ftrue_lemma⦎ =
   ⊢ ∀ x⦁ fTrue ≤⋎t⋎4 x ∧ ¬ x = fTrue ⇒ x = fT

⦏sl_ftrue_lemma⦎ =
   ⊢ ∀ x⦁ x ≤⋎t⋎4 fTrue ∧ ¬ x = fTrue ⇒ x = fB

⦏sg_ffalse_lemma⦎ =
   ⊢ ∀ x⦁ fFalse ≤⋎t⋎4 x ∧ ¬ x = fFalse ⇒ x = fT

⦏sl_ffalse_lemma⦎ =
   ⊢ ∀ x⦁ x ≤⋎t⋎4 fFalse ∧ ¬ x = fFalse ⇒ x = fB

⦏eq_ft_fc_clauses⦎ =
   ⊢ ∀ x
     ⦁ fFalse ≤⋎t⋎4 x ∧ ¬ x = fFalse
           ∨ fTrue ≤⋎t⋎4 x ∧ ¬ x = fTrue
           ∨ fT ≤⋎t⋎4 x
           ∨ fFalse ≤⋎t⋎4 x ∧ fTrue ≤⋎t⋎4 x
         ⇒ x = fT

⦏eq_fb_fc_clauses⦎ =
   ⊢ ∀ x
     ⦁ x ≤⋎t⋎4 fFalse ∧ ¬ x = fFalse
           ∨ x ≤⋎t⋎4 fTrue ∧ ¬ x = fTrue
           ∨ x ≤⋎t⋎4 fB
           ∨ x ≤⋎t⋎4 fTrue ∧ x ≤⋎t⋎4 fFalse
         ⇒ x = fB
⦏≤⋎t⋎4_isub_clauses⦎ =
   ⊢ (∀x⦁ IsUb {x} x)
	∧ IsUb $≤⋎t⋎4 {} = (λ x⦁ T)
         ∧ IsUb $≤⋎t⋎4 {fB} = (λ x⦁ T)
         ∧ IsUb $≤⋎t⋎4 {fTrue} = (λ x⦁ x = fTrue ∨ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fFalse} = (λ x⦁ x = fFalse ∨ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fB; fTrue} = (λ x⦁ x = fTrue ∨ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fB; fFalse} = (λ x⦁ x = fFalse ∨ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fFalse; fTrue} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fB; fFalse; fTrue} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fT} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fB; fT} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fFalse; fT} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fTrue; fT} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fB; fFalse; fT} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fB; fTrue; fT} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fB; fFalse; fTrue; fT} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fFalse; fTrue; fT} = (λ x⦁ x = fT)

⦏≤⋎t⋎4_islb_clauses⦎ =
   ⊢ (∀ x⦁ IsLb $≤⋎t⋎4 {x} x)
       ∧ IsLb $≤⋎t⋎4 {} = (λ x⦁ T)
       ∧ IsLb $≤⋎t⋎4 {fB} = (λ x⦁ x = fB)
       ∧ IsLb $≤⋎t⋎4 {fTrue} = (λ x⦁ x = fTrue ∨ x = fB)
       ∧ IsLb $≤⋎t⋎4 {fFalse} = (λ x⦁ x = fFalse ∨ x = fB)
       ∧ IsLb $≤⋎t⋎4 {fB; fTrue} = (λ x⦁ x = fB)
       ∧ IsLb $≤⋎t⋎4 {fB; fFalse} = (λ x⦁ x = fB)
       ∧ IsLb $≤⋎t⋎4 {fFalse; fTrue} = (λ x⦁ x = fB)
       ∧ IsLb $≤⋎t⋎4 {fB; fFalse; fTrue} = (λ x⦁ x = fB)
       ∧ IsLb $≤⋎t⋎4 {fT} = (λ x⦁ T)
       ∧ IsLb $≤⋎t⋎4 {fB; fT} = (λ x⦁ x = fB)
       ∧ IsLb $≤⋎t⋎4 {fFalse; fT} = (λ x⦁ x = fFalse ∨ x = fB)
       ∧ IsLb $≤⋎t⋎4 {fTrue; fT} = (λ x⦁ x = fTrue ∨ x = fB)
       ∧ IsLb $≤⋎t⋎4 {fB; fFalse; fT} = (λ x⦁ x = fB)
       ∧ IsLb $≤⋎t⋎4 {fB; fTrue; fT} = (λ x⦁ x = fB)
       ∧ IsLb $≤⋎t⋎4 {fB; fFalse; fTrue; fT} = (λ x⦁ x = fB)
       ∧ IsLb $≤⋎t⋎4 {fFalse; fTrue; fT} = (λ x⦁ x = fB)

⦏≤⋎t⋎4_islub_clauses⦎ =
   ⊢ (∀x⦁ IsLub $≤⋎t⋎4 {x} x)
         ∧ IsLub $≤⋎t⋎4 {} fB
         ∧ IsLub $≤⋎t⋎4 {fB; fTrue} fTrue
         ∧ IsLub $≤⋎t⋎4 {fB; fFalse} fFalse
         ∧ IsLub $≤⋎t⋎4 {fFalse; fTrue} fT
         ∧ IsLub $≤⋎t⋎4 {fB; fFalse; fTrue} fT
         ∧ IsLub $≤⋎t⋎4 {fB; fT} fT
         ∧ IsLub $≤⋎t⋎4 {fB; fTrue; fT} fT
         ∧ IsLub $≤⋎t⋎4 {fB; fFalse; fT} fT
         ∧ IsLub $≤⋎t⋎4 {fB; fTrue; fFalse; fT} fT
         ∧ IsLub $≤⋎t⋎4 {fTrue; fT} fT
         ∧ IsLub $≤⋎t⋎4 {fFalse; fT} fT
         ∧ IsLub $≤⋎t⋎4 {fTrue; fFalse; fT} fT

⦏≤⋎t⋎4_isglb_clauses⦎ =
   ⊢ (∀ x⦁ IsGlb $≤⋎t⋎4 {x} x)
       ∧ IsGlb $≤⋎t⋎4 {} fT
       ∧ IsGlb $≤⋎t⋎4 {fB; fFalse} fB
       ∧ IsGlb $≤⋎t⋎4 {fB; fTrue} fB
       ∧ IsGlb $≤⋎t⋎4 {fFalse; fTrue} fB
       ∧ IsGlb $≤⋎t⋎4 {fB; fFalse; fTrue} fB
       ∧ IsGlb $≤⋎t⋎4 {fB; fT} fB
       ∧ IsGlb $≤⋎t⋎4 {fB; fFalse; fT} fB
       ∧ IsGlb $≤⋎t⋎4 {fB; fTrue; fT} fB
       ∧ IsGlb $≤⋎t⋎4 {fB; fFalse; fTrue; fT} fB
       ∧ IsGlb $≤⋎t⋎4 {fFalse; fT} fFalse
       ∧ IsGlb $≤⋎t⋎4 {fTrue; fT} fTrue
       ∧ IsGlb $≤⋎t⋎4 {fFalse; fTrue; fT} fB

⦏≤⋎t⋎4_lin_cases_lemma⦎ =
   ⊢ ∀ Y
     ⦁ LinearOrder (Y, $≤⋎t⋎4)
         ⇔ Y = {}
           ∨ Y = {fB}
           ∨ Y = {fTrue}
           ∨ Y = {fFalse}
           ∨ Y = {fT}
           ∨ Y = {fB; fTrue}
           ∨ Y = {fB; fFalse}
           ∨ Y = {fB; fT}
           ∨ Y = {fTrue; fT}
           ∨ Y = {fFalse; fT}
           ∨ Y = {fB; fTrue; fT}
           ∨ Y = {fB; fFalse; fT}

⦏≤⋎t⋎4_glbs_exist_thm⦎ =
	⊢ GlbsExist $≤⋎t⋎4

⦏≤⋎t⋎4_lubs_exist_thm⦎ =
	⊢ LubsExist $≤⋎t⋎4

⦏≤⋎t⋎4_lub_islub_lemma⦎ =
   ⊢ ∀ s e⦁ Lub $≤⋎t⋎4 s = e ⇔ IsLub $≤⋎t⋎4 s e
=TEX

\ignore{
=SML
set_goal([], ⌜$≤⋎t⋎4 = Dpo⌝);
a (rewrite_tac (map get_spec [⌜$≤⋎t⋎4⌝, ⌜Dpo⌝, ⌜fB⌝, ⌜fT⌝, ⌜fTrue⌝, ⌜fFalse⌝])
	THEN REPEAT strip_tac);
val ≤⋎t⋎4_dpo_thm = save_pop_thm "≤⋎t⋎4_dpo_thm";

set_goal([], ⌜∀x⦁ x ≤⋎t⋎4 x⌝);
a (rewrite_tac [get_spec ⌜$≤⋎t⋎4⌝]);
val ≤⋎t⋎4_refl_thm = save_pop_thm "≤⋎t⋎4_refl_thm";

set_goal([], ⌜∀x y z⦁ x ≤⋎t⋎4 y ∧ y ≤⋎t⋎4 z ⇒ x ≤⋎t⋎4 z⌝);
a (rewrite_tac [get_spec ⌜$≤⋎t⋎4⌝]
	THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY asm_rewrite_tac[]);
val ≤⋎t⋎4_trans_thm = save_pop_thm "≤⋎t⋎4_trans_thm";

set_goal([], ⌜∀x y⦁ x ≤⋎t⋎4 y ∧ y ≤⋎t⋎4 x ⇒ x = y⌝);
a (rewrite_tac [get_spec ⌜$≤⋎t⋎4⌝]
	THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY asm_rewrite_tac[]);
val ≤⋎t⋎4_antisym_thm = save_pop_thm "≤⋎t⋎4_antisym_thm";

set_goal([], ⌜Antisym (Universe, $≤⋎t⋎4)⌝);
a (rewrite_tac[get_spec ⌜Antisym⌝]
	THEN contr_tac
	THEN all_fc_tac [≤⋎t⋎4_antisym_thm]);
val ≤⋎t⋎4_antisym_thm2 = save_pop_thm "≤⋎t⋎4_antisym_thm2";

set_goal([], ⌜(∀x⦁ fB ≤⋎t⋎4 x)
	∧ (∀x⦁ x ≤⋎t⋎4 fT)
	∧ ¬ fTrue ≤⋎t⋎4 fB
	∧ ¬ fFalse ≤⋎t⋎4 fB
	∧ ¬ fT ≤⋎t⋎4 fB
	∧ ¬ fFalse ≤⋎t⋎4 fTrue
	∧ ¬ fT ≤⋎t⋎4 fTrue
	∧ ¬ fTrue ≤⋎t⋎4 fFalse
	∧ ¬ fT ≤⋎t⋎4 fFalse⌝);
a (rewrite_tac [get_spec ⌜$≤⋎t⋎4⌝] THEN prove_tac[]);
val ≤⋎t⋎4_clauses = pop_thm ();

set_goal ([], ⌜∀x⦁ (fT ≤⋎t⋎4 x ⇔ x = fT) ∧ (x ≤⋎t⋎4 fB ⇔ x = fB)⌝);
a (prove_tac [get_spec ⌜$≤⋎t⋎4⌝]);
val ft_fb_thm = save_pop_thm "ft_fb_thm";

add_pc_thms "'misc1" (map get_spec [] @ [≤⋎t⋎4_refl_thm, ≤⋎t⋎4_clauses, ≤⋎t⋎4_antisym_thm2]);
set_merge_pcs ["rbjmisc", "'misc1"];

set_goal([], ⌜∀Y⦁ PartialOrder (Y, $≤⋎t⋎4)⌝);
a (rewrite_tac (map get_spec [⌜PartialOrder⌝, ⌜Antisym⌝, ⌜Trans⌝])
	THEN contr_tac);
a (all_fc_tac [≤⋎t⋎4_antisym_thm]);
a (all_fc_tac [≤⋎t⋎4_trans_thm]);
val ≤⋎t⋎4_partialorder_thm = save_pop_thm "≤⋎t⋎4_partialorder_thm";

set_goal([], ⌜∀Y⦁ LinearOrder (Y, $≤⋎t⋎4) ⇔ ¬ fTrue ∈ Y ∨ ¬ fFalse ∈ Y⌝);
a (rewrite_tac [get_spec ⌜LinearOrder⌝, get_spec ⌜Trich⌝, ≤⋎t⋎4_partialorder_thm]
	THEN contr_tac);
(* *** Goal "1" *** *)
a (REPEAT (asm_fc_tac[]));
(* *** Goal "2" *** *)
a (strip_asm_tac (list_∀_elim [⌜x⌝] ftv_cases_thm)
	THEN asm_prove_tac[]);
a (strip_asm_tac (list_∀_elim [⌜y⌝] ftv_cases_thm)
	THEN asm_prove_tac[]);
(* *** Goal "3" *** *)
a (strip_asm_tac (list_∀_elim [⌜x⌝] ftv_cases_thm)
	THEN asm_prove_tac[]);
a (strip_asm_tac (list_∀_elim [⌜y⌝] ftv_cases_thm)
	THEN asm_prove_tac[]);
val ≤⋎t⋎4_lin_lemma = save_pop_thm "≤⋎t⋎4_lin_lemma";

add_pc_thms1 "'misc1" (map get_spec [] @ [≤⋎t⋎4_partialorder_thm]);
set_merge_pcs ["rbjmisc", "'misc1"];

set_goal([], ⌜∀Y⦁ LinearOrder (Y, $≤⋎t⋎4) ⇔
	  Y = {}
	∨ Y = {fB} ∨ Y = {fTrue} ∨ Y = {fFalse} ∨ Y = {fT}
	∨ Y = {fB; fTrue} ∨ Y = {fB; fFalse} ∨ Y = {fB; fT}
	∨ Y = {fTrue; fT} ∨ Y = {fFalse; fT}
	∨ Y = {fB; fTrue; fT} ∨ Y = {fB; fFalse; fT}
⌝);
a (rewrite_tac [≤⋎t⋎4_lin_lemma] THEN REPEAT ∀_tac);
a (strip_asm_tac (∀_elim ⌜Y⌝ ftvs_cases_thm)
	THEN asm_rewrite_tac[]
	THEN_TRY (conv_tac (MAP_C false_enum_eq_conv))
	THEN_TRY PC_T1 "hol1" prove_tac[ftv_distinct_clauses]);
val ≤⋎t⋎4_lin_cases_lemma = pop_thm ();

set_goal([], ⌜∀x⦁ fFalse ≤⋎t⋎4 x ∧ fTrue ≤⋎t⋎4 x ⇒ x = fT⌝);
a (∀_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
val gt_false_true_lemma = pop_thm ();

set_goal([], ⌜∀x⦁ x ≤⋎t⋎4 fFalse ∧ x ≤⋎t⋎4 fTrue ⇒ x = fB⌝);
a (∀_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
val lt_false_true_lemma = pop_thm ();

set_goal([], ⌜∀x⦁ fT ≤⋎t⋎4 x ⇒ x = fT⌝);
a (∀_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
val gt_ft_lemma = pop_thm ();

set_goal([], ⌜∀x⦁ x ≤⋎t⋎4 fB ⇒ x = fB⌝);
a (∀_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
val lt_fb_lemma = pop_thm ();

set_goal([], ⌜∀x⦁ x ≤⋎t⋎4 fB ⇒ x = fB⌝);
a (∀_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
val lt_fb_lemma = pop_thm ();

set_goal([], ⌜∀x⦁ fTrue ≤⋎t⋎4 x ∧ ¬ x = fTrue ⇒ x = fT⌝);
a (∀_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
val sg_ftrue_lemma = pop_thm ();

set_goal([], ⌜∀x⦁ x ≤⋎t⋎4 fTrue ∧ ¬ x = fTrue ⇒ x = fB⌝);
a (∀_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
val sl_ftrue_lemma = pop_thm ();

set_goal([], ⌜∀x⦁ fFalse ≤⋎t⋎4 x ∧ ¬ x = fFalse ⇒ x = fT⌝);
a (∀_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
val sg_ffalse_lemma = pop_thm ();

set_goal([], ⌜∀x⦁ x ≤⋎t⋎4 fFalse ∧ ¬ x = fFalse ⇒ x = fB⌝);
a (∀_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ ftv_cases_thm) THEN asm_rewrite_tac[]);
val sl_ffalse_lemma = pop_thm ();

set_goal([], ⌜∀x⦁ (fFalse ≤⋎t⋎4 x ∧ ¬ x = fFalse
		∨ fTrue ≤⋎t⋎4 x ∧ ¬ x = fTrue
		∨ fT ≤⋎t⋎4 x
		∨ fFalse ≤⋎t⋎4 x ∧ fTrue ≤⋎t⋎4 x) ⇒ x = fT⌝);
a (REPEAT strip_tac THEN fc_tac [sg_ffalse_lemma, sg_ftrue_lemma, gt_ft_lemma, gt_false_true_lemma]);
val eq_ft_fc_clauses = save_pop_thm "eq_ft_fc_clauses";

set_goal([], ⌜∀x⦁ ( x ≤⋎t⋎4 fFalse ∧ ¬ x = fFalse
		∨ x ≤⋎t⋎4 fTrue ∧ ¬ x = fTrue
		∨ x ≤⋎t⋎4 fB
		∨ x ≤⋎t⋎4 fTrue ∧ x ≤⋎t⋎4 fFalse) ⇒ x = fB⌝);
a (REPEAT strip_tac THEN fc_tac [sl_ffalse_lemma, sl_ftrue_lemma, lt_fb_lemma, lt_false_true_lemma]);
val eq_fb_fc_clauses = save_pop_thm "eq_fb_fc_clauses";

set_merge_pcs ["rbjmisc1", "'misc1"];

set_goal([], ⌜(∀x⦁ IsUb $≤⋎t⋎4 {x} x)
	∧ IsUb $≤⋎t⋎4 {} = (λ x⦁ T)
         ∧ IsUb $≤⋎t⋎4 {fB} = (λ x⦁ T)
         ∧ IsUb $≤⋎t⋎4 {fTrue} = (λ x⦁ x = fTrue ∨ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fFalse} = (λ x⦁ x = fFalse ∨ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fB; fTrue} = (λ x⦁ x = fTrue ∨ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fB; fFalse} = (λ x⦁ x = fFalse ∨ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fFalse; fTrue} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fB; fFalse; fTrue} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fT} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fB; fT} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fFalse; fT} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fTrue; fT} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fB; fFalse; fT} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fB; fTrue; fT} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fB; fFalse; fTrue; fT} = (λ x⦁ x = fT)
         ∧ IsUb $≤⋎t⋎4 {fFalse; fTrue; fT} = (λ x⦁ x = fT)⌝);
a (rewrite_tac[get_spec ⌜IsUb⌝]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]
	THEN_TRY (spec_nth_asm_tac 1 ⌜fT⌝ THEN fc_tac[gt_ft_lemma]));
a ((spec_nth_asm_tac 2 ⌜fTrue⌝) THEN fc_tac [eq_ft_fc_clauses]);
a ((spec_nth_asm_tac 2 ⌜fFalse⌝) THEN fc_tac [eq_ft_fc_clauses]);
a ((spec_nth_asm_tac 2 ⌜fTrue⌝) THEN fc_tac [eq_ft_fc_clauses]);
a ((spec_nth_asm_tac 2 ⌜fFalse⌝) THEN fc_tac [eq_ft_fc_clauses]);
a ((spec_nth_asm_tac 3 ⌜fFalse⌝) THEN fc_tac [eq_ft_fc_clauses]);
a ((spec_nth_asm_tac 6 ⌜fTrue⌝));
a ((spec_nth_asm_tac 4 ⌜fTrue⌝)
	THEN (spec_nth_asm_tac 5 ⌜fFalse⌝)
	THEN fc_tac [eq_ft_fc_clauses]);
val ≤⋎t⋎4_isub_clauses = pop_thm ();

set_goal([], ⌜(∀x⦁ IsLb $≤⋎t⋎4 {x} x)
	∧ IsLb $≤⋎t⋎4 {} = (λ x⦁ T)
         ∧ IsLb $≤⋎t⋎4 {fB} = (λ x⦁ x = fB)
         ∧ IsLb $≤⋎t⋎4 {fTrue} = (λ x⦁ x = fTrue ∨ x = fB)
         ∧ IsLb $≤⋎t⋎4 {fFalse} = (λ x⦁ x = fFalse ∨ x = fB)
         ∧ IsLb $≤⋎t⋎4 {fB; fTrue} = (λ x⦁ x = fB)
         ∧ IsLb $≤⋎t⋎4 {fB; fFalse} = (λ x⦁ x = fB)
         ∧ IsLb $≤⋎t⋎4 {fFalse; fTrue} = (λ x⦁ x = fB)
         ∧ IsLb $≤⋎t⋎4 {fB; fFalse; fTrue} = (λ x⦁ x = fB)
         ∧ IsLb $≤⋎t⋎4 {fT} = (λ x⦁ T)
         ∧ IsLb $≤⋎t⋎4 {fB; fT} = (λ x⦁ x = fB)
         ∧ IsLb $≤⋎t⋎4 {fFalse; fT} = (λ x⦁ x = fFalse ∨ x = fB)
         ∧ IsLb $≤⋎t⋎4 {fTrue; fT} = (λ x⦁ x = fTrue ∨ x = fB)
         ∧ IsLb $≤⋎t⋎4 {fB; fFalse; fT} = (λ x⦁ x = fB)
         ∧ IsLb $≤⋎t⋎4 {fB; fTrue; fT} = (λ x⦁ x = fB)
         ∧ IsLb $≤⋎t⋎4 {fB; fFalse; fTrue; fT} = (λ x⦁ x = fB)
         ∧ IsLb $≤⋎t⋎4 {fFalse; fTrue; fT} = (λ x⦁ x = fB)⌝);
a (rewrite_tac[get_spec ⌜IsLb⌝]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]
	THEN_TRY (spec_nth_asm_tac 1 ⌜fB⌝ THEN fc_tac[lt_fb_lemma]));
a ((spec_nth_asm_tac 2 ⌜fTrue⌝) THEN fc_tac [eq_fb_fc_clauses]);
a ((spec_nth_asm_tac 2 ⌜fFalse⌝) THEN fc_tac [eq_fb_fc_clauses]);
a ((spec_nth_asm_tac 3 ⌜fTrue⌝) THEN (spec_nth_asm_tac 4 ⌜fFalse⌝)
	THEN fc_tac [eq_fb_fc_clauses]);
a ((spec_nth_asm_tac 2 ⌜fFalse⌝) THEN fc_tac [eq_fb_fc_clauses]);
a ((spec_nth_asm_tac 2 ⌜fTrue⌝) THEN fc_tac [eq_fb_fc_clauses]);
a ((spec_nth_asm_tac 4 ⌜fTrue⌝)
	THEN (spec_nth_asm_tac 5 ⌜fFalse⌝)
	THEN fc_tac [eq_fb_fc_clauses]);
val ≤⋎t⋎4_islb_clauses = pop_thm ();

push_extend_pc "'mmp1";

set_goal([], ⌜(∀x⦁ IsLub $≤⋎t⋎4 {x} x)
         ∧ IsLub $≤⋎t⋎4 {} fB
         ∧ IsLub $≤⋎t⋎4 {fB; fFalse} fFalse
         ∧ IsLub $≤⋎t⋎4 {fB; fTrue} fTrue
         ∧ IsLub $≤⋎t⋎4 {fFalse; fTrue} fT
         ∧ IsLub $≤⋎t⋎4 {fB; fFalse; fTrue} fT
         ∧ IsLub $≤⋎t⋎4 {fB; fT} fT
         ∧ IsLub $≤⋎t⋎4 {fB; fFalse; fT} fT
         ∧ IsLub $≤⋎t⋎4 {fB; fTrue; fT} fT
         ∧ IsLub $≤⋎t⋎4 {fB; fFalse; fTrue; fT} fT
         ∧ IsLub $≤⋎t⋎4 {fFalse; fT} fT
         ∧ IsLub $≤⋎t⋎4 {fTrue; fT} fT
         ∧ IsLub $≤⋎t⋎4 {fFalse; fTrue; fT} fT⌝);
a (rewrite_tac [get_spec ⌜IsLub⌝, ≤⋎t⋎4_isub_clauses]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[≤⋎t⋎4_isub_clauses]);
a (fc_tac [get_spec ⌜IsUb⌝]);
val ≤⋎t⋎4_islub_clauses = pop_thm ();

set_goal([], ⌜(∀x⦁ IsGlb $≤⋎t⋎4 {x} x)
         ∧ IsGlb $≤⋎t⋎4 {} fT
         ∧ IsGlb $≤⋎t⋎4 {fB; fFalse} fB
         ∧ IsGlb $≤⋎t⋎4 {fB; fTrue} fB
         ∧ IsGlb $≤⋎t⋎4 {fFalse; fTrue} fB
         ∧ IsGlb $≤⋎t⋎4 {fB; fFalse; fTrue} fB
         ∧ IsGlb $≤⋎t⋎4 {fB; fT} fB
         ∧ IsGlb $≤⋎t⋎4 {fB; fFalse; fT} fB
         ∧ IsGlb $≤⋎t⋎4 {fB; fTrue; fT} fB
         ∧ IsGlb $≤⋎t⋎4 {fB; fFalse; fTrue; fT} fB
         ∧ IsGlb $≤⋎t⋎4 {fFalse; fT} fFalse
         ∧ IsGlb $≤⋎t⋎4 {fTrue; fT} fTrue
         ∧ IsGlb $≤⋎t⋎4 {fFalse; fTrue; fT} fB⌝);
a (rewrite_tac [get_spec ⌜IsGlb⌝, ≤⋎t⋎4_islb_clauses]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[≤⋎t⋎4_islb_clauses]);
a (fc_tac [get_spec ⌜IsLb⌝]);
val ≤⋎t⋎4_isglb_clauses = pop_thm ();

set_goal([], ⌜GlbsExist $≤⋎t⋎4⌝);
a (rewrite_tac[≤⋎t⋎4_dpo_thm, dpo_glbs_exist_thm]);
val ≤⋎t⋎4_glbs_exist_thm = save_pop_thm "≤⋎t⋎4_glbs_exist_thm";

set_goal([], ⌜LubsExist $≤⋎t⋎4⌝);
a (rewrite_tac[≤⋎t⋎4_dpo_thm, dpo_lubs_exist_thm]);
val ≤⋎t⋎4_lubs_exist_thm = save_pop_thm "≤⋎t⋎4_lubs_exist_thm";

set_goal([], ⌜∀s e⦁ Lub $≤⋎t⋎4 s = e ⇔ IsLub $≤⋎t⋎4 s e⌝);
a (REPEAT ∀_tac);
a (asm_tac ≤⋎t⋎4_lubs_exist_thm);
a (fc_tac [lub_lub_lemma2]);
pop_pc();
a (strip_asm_tac (prove_rule [] ⌜PartialOrder (Universe, $≤⋎t⋎4)⌝));
push_extend_pc "'mmp1";
a (fc_tac [get_spec ⌜PartialOrder⌝]);
a (fc_tac [lub_unique_lemma]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (SPEC_NTH_ASM_T 4 ⌜s⌝ ante_tac
	THEN rewrite_tac[asm_rule (⌜Lub $≤⋎t⋎4 s = e⌝)]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 4 ⌜s⌝);
a (all_fc_tac [rewrite_rule [] (list_∀_elim [⌜s⌝, ⌜$≤⋎t⋎4⌝] lub_unique_lemma)]);
val ≤⋎t⋎4_lub_islub_lemma = save_pop_thm "≤⋎t⋎4_lub_islub_lemma";

set_goal([], ⌜CRpoU $≤⋎t⋎4⌝);
a (rewrite_tac [get_spec ⌜CRpoU⌝, get_spec ⌜RpoU⌝,
	≤⋎t⋎4_glbs_exist_thm, ≤⋎t⋎4_lubs_exist_thm, get_spec ⌜Rpo⌝,
	≤⋎t⋎4_partialorder_thm, get_spec ⌜Refl⌝]);
val ≤⋎t⋎4_crpou_thm = save_pop_thm "≤⋎t⋎4_crpou_thm";

pop_pc();

add_pc_thms "'misc1" (map get_spec [] @ [≤⋎t⋎4_isub_clauses, ≤⋎t⋎4_islub_clauses, ≤⋎t⋎4_islb_clauses, ≤⋎t⋎4_isglb_clauses]);
add_pc_thms1 "'misc1" (map get_spec [] @ [≤⋎t⋎4_lubs_exist_thm, ≤⋎t⋎4_glbs_exist_thm, ≤⋎t⋎4_crpou_thm]);
set_merge_pcs ["rbjmisc", "'misc1"];
=TEX
}%ignore

=GFT
⦏≤⋎t⋎4_lub_clauses⦎ =
   ⊢ Lub $≤⋎t⋎4 {} = fB
       ∧ Lub $≤⋎t⋎4 {fT} = fT
       ∧ Lub $≤⋎t⋎4 {fTrue} = fTrue
       ∧ Lub $≤⋎t⋎4 {fTrue; fT} = fT
       ∧ Lub $≤⋎t⋎4 {fFalse} = fFalse
       ∧ Lub $≤⋎t⋎4 {fFalse; fT} = fT
       ∧ Lub $≤⋎t⋎4 {fFalse; fTrue} = fT
       ∧ Lub $≤⋎t⋎4 {fFalse; fTrue; fT} = fT
       ∧ Lub $≤⋎t⋎4 {fB} = fB
       ∧ Lub $≤⋎t⋎4 {fB; fT} = fT
       ∧ Lub $≤⋎t⋎4 {fB; fTrue} = fTrue
       ∧ Lub $≤⋎t⋎4 {fB; fTrue; fT} = fT
       ∧ Lub $≤⋎t⋎4 {fB; fFalse} = fFalse
       ∧ Lub $≤⋎t⋎4 {fB; fFalse; fT} = fT
       ∧ Lub $≤⋎t⋎4 {fB; fFalse; fTrue} = fT
       ∧ Lub $≤⋎t⋎4 {fB; fFalse; fTrue; fT} = fT

⦏≤⋎t⋎4_lub_thm⦎ =
   ⊢ ∀ s
     ⦁ Lub $≤⋎t⋎4 s
         = (if fT ∈ s
           then fT
           else if fTrue ∈ s
           then if fFalse ∈ s then fT else fTrue
           else if fFalse ∈ s
           then fFalse
           else fB)

⦏≤⋎t⋎4_glb_clauses⦎ =
   ⊢ Glb $≤⋎t⋎4 {} = fT
       ∧ Glb $≤⋎t⋎4 {fT} = fT
       ∧ Glb $≤⋎t⋎4 {fTrue} = fTrue
       ∧ Glb $≤⋎t⋎4 {fTrue; fT} = fTrue
       ∧ Glb $≤⋎t⋎4 {fFalse} = fFalse
       ∧ Glb $≤⋎t⋎4 {fFalse; fT} = fFalse
       ∧ Glb $≤⋎t⋎4 {fFalse; fTrue} = fB
       ∧ Glb $≤⋎t⋎4 {fFalse; fTrue; fT} = fB
       ∧ Glb $≤⋎t⋎4 {fB} = fB
       ∧ Glb $≤⋎t⋎4 {fB; fT} = fB
       ∧ Glb $≤⋎t⋎4 {fB; fTrue} = fB
       ∧ Glb $≤⋎t⋎4 {fB; fTrue; fT} = fB
       ∧ Glb $≤⋎t⋎4 {fB; fFalse} = fB
       ∧ Glb $≤⋎t⋎4 {fB; fFalse; fT} = fB
       ∧ Glb $≤⋎t⋎4 {fB; fFalse; fTrue} = fB
       ∧ Glb $≤⋎t⋎4 {fB; fFalse; fTrue; fT}
=TEX

\ignore{
=SML
set_goal([], ⌜Lub $≤⋎t⋎4 {} = fB
	∧ Lub $≤⋎t⋎4 {fT} = fT
	∧ Lub $≤⋎t⋎4 {fTrue} = fTrue
	∧ Lub $≤⋎t⋎4 {fTrue; fT} = fT
	∧ Lub $≤⋎t⋎4 {fFalse} = fFalse
	∧ Lub $≤⋎t⋎4 {fFalse; fT} = fT
	∧ Lub $≤⋎t⋎4 {fFalse; fTrue} = fT
	∧ Lub $≤⋎t⋎4 {fFalse; fTrue; fT} = fT
	∧ Lub $≤⋎t⋎4 {fB} = fB
	∧ Lub $≤⋎t⋎4 {fB; fT} = fT
	∧ Lub $≤⋎t⋎4 {fB; fTrue} = fTrue
	∧ Lub $≤⋎t⋎4 {fB; fTrue; fT} = fT
	∧ Lub $≤⋎t⋎4 {fB; fFalse} = fFalse
	∧ Lub $≤⋎t⋎4 {fB; fFalse; fT} = fT
	∧ Lub $≤⋎t⋎4 {fB; fFalse; fTrue} = fT
	∧ Lub $≤⋎t⋎4 {fB; fFalse; fTrue; fT} = fT⌝);
a (asm_tac ≤⋎t⋎4_crpou_thm THEN fc_tac [islub_lub_crpou_lemma]);
a (MAP_EVERY asm_tac (strip_∧_rule ≤⋎t⋎4_islub_clauses));
a (ASM_UFC_T rewrite_tac []); 
val ≤⋎t⋎4_lub_clauses = save_pop_thm "≤⋎t⋎4_lub_clauses";

set_goal([], ⌜∀s⦁ Lub $≤⋎t⋎4 s =
	if fT ∈ s
	then	fT
	else	if fTrue ∈ s
		then	if fFalse ∈ s
			then fT
			else fTrue 
		else 	if fFalse ∈ s
			then fFalse
			else fB⌝);
a (strip_tac);
a (strip_asm_tac (∀_elim ⌜s⌝ ftvs_cases_thm)
	THEN asm_rewrite_tac [≤⋎t⋎4_lub_clauses, ∈_in_clauses]);
val ≤⋎t⋎4_lub_thm = save_pop_thm "≤⋎t⋎4_lub_thm";

set_goal([], ⌜Glb $≤⋎t⋎4 {} = fT
	∧ Glb $≤⋎t⋎4 {fT} = fT
	∧ Glb $≤⋎t⋎4 {fTrue} = fTrue
	∧ Glb $≤⋎t⋎4 {fTrue; fT} = fTrue
	∧ Glb $≤⋎t⋎4 {fFalse} = fFalse
	∧ Glb $≤⋎t⋎4 {fFalse; fT} = fFalse
	∧ Glb $≤⋎t⋎4 {fFalse; fTrue} = fB
	∧ Glb $≤⋎t⋎4 {fFalse; fTrue; fT} = fB
	∧ Glb $≤⋎t⋎4 {fB} = fB
	∧ Glb $≤⋎t⋎4 {fB; fT} = fB
	∧ Glb $≤⋎t⋎4 {fB; fTrue} = fB
	∧ Glb $≤⋎t⋎4 {fB; fTrue; fT} = fB
	∧ Glb $≤⋎t⋎4 {fB; fFalse} = fB
	∧ Glb $≤⋎t⋎4 {fB; fFalse; fT} = fB
	∧ Glb $≤⋎t⋎4 {fB; fFalse; fTrue} = fB
	∧ Glb $≤⋎t⋎4 {fB; fFalse; fTrue; fT} = fB⌝);
a (asm_tac ≤⋎t⋎4_crpou_thm THEN fc_tac [isglb_glb_crpou_lemma]);
a (MAP_EVERY asm_tac (strip_∧_rule ≤⋎t⋎4_isglb_clauses));
a (ASM_UFC_T rewrite_tac []); 
val ≤⋎t⋎4_glb_clauses = save_pop_thm "≤⋎t⋎4_glb_clauses";

add_pc_thms "'misc1" (map get_spec [] @ [≤⋎t⋎4_lub_clauses, ≤⋎t⋎4_glb_clauses]);
set_merge_pcs ["rbjmisc", "'misc1"];
=TEX
}%ignore

The following definitions expresses compatibility of truth values.
This is useful when trying to obtain a boolean valued function as a total least fixed point of a monotonic four valued function.

I first define a notion of compatibility between truth values.

ⓈHOLCONST
│ ⦏CompFTV⦎ : FTV SET SET
├───────────
│ CompFTV = {{}; {fB}; {fFalse}; {fTrue}; {fB; fFalse}; {fB; fTrue}}
■

and its dual:

ⓈHOLCONST
│ ⦏CoCompFTV⦎ : FTV SET SET
├───────────
│ CoCompFTV = {{}; {fT}; {fFalse}; {fTrue}; {fFalse; fT}; {fTrue; fT}}
■

=GFT
⦏compftv_lemma⦎ =
   ⊢ ∀ s
     ⦁ s ∈ CompFTV ⇔ ¬ fT ∈ s ∧ (¬ fTrue ∈ s ∨ ¬ fFalse ∈ s)

⦏cocompftv_lemma⦎ =
   ⊢ ∀ s
     ⦁ s ∈ CoCompFTV ⇔ ¬ fB ∈ s ∧ (¬ fTrue ∈ s ∨ ¬ fFalse ∈ s)
=TEX
=GFT
⦏CompFTV_∈_clauses⦎ =
   ⊢ {} ∈ CompFTV
       ∧ {fB} ∈ CompFTV
       ∧ {fFalse} ∈ CompFTV
       ∧ {fTrue} ∈ CompFTV
       ∧ ¬ {fT} ∈ CompFTV
       ∧ {fB; fFalse} ∈ CompFTV
       ∧ {fB; fTrue} ∈ CompFTV
       ∧ ¬ {fB; fT} ∈ CompFTV
       ∧ ¬ {fFalse; fTrue} ∈ CompFTV
       ∧ ¬ {fFalse; fT} ∈ CompFTV
       ∧ ¬ {fTrue; fT} ∈ CompFTV
       ∧ ¬ {fB; fFalse; fTrue} ∈ CompFTV
       ∧ ¬ {fB; fFalse; fT} ∈ CompFTV
       ∧ ¬ {fB; fTrue; fT} ∈ CompFTV
       ∧ ¬ {fFalse; fTrue; fT} ∈ CompFTV
       ∧ ¬ {fB; fFalse; fTrue; fT} ∈ CompFTV
=GFT
⦏CompFTV_Lub_lemma⦎ =
   ⊢ ∀ s⦁ s ∈ CompFTV ⇔ ¬ Lub $≤⋎t⋎4 s = fT

⦏Lub_CompFTV_lemma⦎ =
   ⊢ ∀ s⦁ Lub $≤⋎t⋎4 s = fT ⇔ ¬ s ∈ CompFTV
=TEX
=GFT
⦏CoCompFTV_Lub_lemma⦎ =
   ⊢ ∀ s⦁ s ∈ CoCompFTV ⇔ ¬ Glb $≤⋎t⋎4 s = fB

⦏Glb_CoCompFTV_lemma⦎ =
   ⊢ ∀ s⦁ Glb $≤⋎t⋎4 s = fB ⇔ ¬ s ∈ CoCompFTV
=TEX

\ignore{
=SML
set_goal([], ⌜∀s⦁ s ∈ CompFTV ⇔ ¬ fT ∈ s ∧ (¬ fTrue ∈ s ∨ ¬ fFalse ∈ s)⌝);
a (∀_tac THEN rewrite_tac[get_spec ⌜CompFTV⌝, ∈_in_clauses]
	THEN strip_tac THEN strip_tac);
a (strip_tac THEN asm_rewrite_tac[∈_in_clauses]);
a (strip_asm_tac (∀_elim ⌜s⌝ ftvs_cases_thm)
	THEN asm_rewrite_tac[]);
val compftv_lemma = save_pop_thm "compftv_lemma";

set_goal([], ⌜∀s⦁ s ∈ CoCompFTV ⇔ ¬ fB ∈ s ∧ (¬ fTrue ∈ s ∨ ¬ fFalse ∈ s)⌝);
a (∀_tac THEN rewrite_tac[get_spec ⌜CoCompFTV⌝, ∈_in_clauses]
	THEN REPEAT_N 2 strip_tac);
a (strip_tac THEN asm_rewrite_tac[∈_in_clauses]);
a (strip_asm_tac (∀_elim ⌜s⌝ ftvs_cases_thm)
	THEN asm_rewrite_tac[]);
val cocompftv_lemma = save_pop_thm "cocompftv_lemma";

set_goal([], ⌜{} ∈ CompFTV
         ∧ {fB} ∈ CompFTV
         ∧ {fFalse} ∈ CompFTV
         ∧ {fTrue} ∈ CompFTV
         ∧ ¬ {fT} ∈ CompFTV
         ∧ {fB; fFalse} ∈ CompFTV
         ∧ {fB; fTrue} ∈ CompFTV
         ∧ ¬ {fB; fT} ∈ CompFTV
         ∧ ¬ {fFalse; fTrue} ∈ CompFTV
         ∧ ¬ {fFalse; fT} ∈ CompFTV
         ∧ ¬ {fTrue; fT} ∈ CompFTV
         ∧ ¬ {fB; fFalse; fTrue} ∈ CompFTV
         ∧ ¬ {fB; fFalse; fT} ∈ CompFTV
         ∧ ¬ {fB; fTrue; fT} ∈ CompFTV
         ∧ ¬ {fFalse; fTrue; fT} ∈ CompFTV
         ∧ ¬ {fB; fFalse; fTrue; fT} ∈ CompFTV⌝);
a (rewrite_tac [get_spec ⌜CompFTV⌝, ∈_in_clauses]
	THEN_TRY false_enum_eq_tac
	THEN rewrite_tac[]);
val CompFTV_∈_clauses = pop_thm ();

set_goal([], ⌜{} ∈ CoCompFTV
         ∧ ¬ {fB} ∈ CoCompFTV
         ∧ {fFalse} ∈ CoCompFTV
         ∧ {fTrue} ∈ CoCompFTV
         ∧ {fT} ∈ CoCompFTV
         ∧ ¬ {fB; fFalse} ∈ CoCompFTV
         ∧ ¬ {fB; fTrue} ∈ CoCompFTV
         ∧ ¬ {fB; fT} ∈ CoCompFTV
         ∧ ¬ {fFalse; fTrue} ∈ CoCompFTV
         ∧ {fFalse; fT} ∈ CoCompFTV
         ∧ {fTrue; fT} ∈ CoCompFTV
         ∧ ¬ {fB; fFalse; fTrue} ∈ CoCompFTV
         ∧ ¬ {fB; fFalse; fT} ∈ CoCompFTV
         ∧ ¬ {fB; fTrue; fT} ∈ CoCompFTV
         ∧ ¬ {fFalse; fTrue; fT} ∈ CoCompFTV
         ∧ ¬ {fB; fFalse; fTrue; fT} ∈ CoCompFTV⌝);
a (rewrite_tac [get_spec ⌜CoCompFTV⌝, ∈_in_clauses]
	THEN_TRY false_enum_eq_tac
	THEN rewrite_tac[]);
val CoCompFTV_∈_clauses = pop_thm ();

set_goal([], ⌜∀s⦁ s ∈ CompFTV ⇔ ¬ Lub $≤⋎t⋎4 s = fT⌝);
a (strip_tac);
a (strip_asm_tac (∀_elim ⌜s⌝ ftvs_cases_thm)
	THEN asm_rewrite_tac [CompFTV_∈_clauses]);
val CompFTV_Lub_lemma = save_pop_thm "CompFTV_Lub_lemma";

set_goal([], ⌜∀s⦁ Lub $≤⋎t⋎4 s = fT ⇔ ¬ s ∈ CompFTV⌝);
a (strip_tac THEN rewrite_tac [CompFTV_Lub_lemma]);
val Lub_CompFTV_lemma = save_pop_thm "Lub_CompFTV_lemma";

set_goal([], ⌜∀s⦁ s ∈ CoCompFTV ⇔ ¬ Glb $≤⋎t⋎4 s = fB⌝);
a (strip_tac);
a (strip_asm_tac (∀_elim ⌜s⌝ ftvs_cases_thm)
	THEN asm_rewrite_tac [CoCompFTV_∈_clauses]);
val CoCompFTV_Glb_lemma = save_pop_thm "CoCompFTV_Glb_lemma";

set_goal([], ⌜∀s⦁ Glb $≤⋎t⋎4 s = fB ⇔ ¬ s ∈ CoCompFTV⌝);
a (strip_tac THEN rewrite_tac [CoCompFTV_Glb_lemma]);
val Glb_CoCompFTV_lemma = save_pop_thm "Glb_CoCompFTV_lemma";

add_pc_thms "'misc1" (map get_spec [] @ [CompFTV_∈_clauses, CoCompFTV_∈_clauses, Lub_CompFTV_lemma, Glb_CoCompFTV_lemma]);
set_merge_pcs ["rbjmisc", "'misc1"];
=TEX
}%ignore

=GFT
⦏≤⋎t⋎4_lin_lub_lemma⦎ =
   ⊢ ∀ X⦁ LinearOrder (X, $≤⋎t⋎4) ⇒ fT ≤⋎t⋎4 Lub $≤⋎t⋎4 X = fT ∈ X

⦏≤⋎t⋎4_lin_lub_lemma2⦎ =
   ⊢ ∀ X⦁ LinearOrder (X, $≤⋎t⋎4) ⇒ (fT = Lub $≤⋎t⋎4 X) = fT ∈ X

⦏≤⋎t⋎4_lin_glb_lemma⦎ =
   ⊢ ∀ X⦁ LinearOrder (X, $≤⋎t⋎4) ⇒ Glb $≤⋎t⋎4 X ≤⋎t⋎4 fB = fB ∈ X

⦏≤⋎t⋎4_lin_glb_lemma2⦎ =
   ⊢ ∀ X⦁ LinearOrder (X, $≤⋎t⋎4) ⇒ (Glb $≤⋎t⋎4 X = fB) = fB ∈ X 
=TEX

\ignore{
=SML
set_goal ([], ⌜∀X⦁ LinearOrder (X, $≤⋎t⋎4) ⇒ (fT ≤⋎t⋎4 Lub $≤⋎t⋎4 X ⇔ fT ∈ X)⌝);
a (REPEAT_N 2 strip_tac);
a (fc_tac [≤⋎t⋎4_lin_cases_lemma]
	THEN asm_rewrite_tac[]
	THEN contr_tac);
val ≤⋎t⋎4_lin_lub_lemma = save_pop_thm "≤⋎t⋎4_lin_lub_lemma";

set_goal ([], ⌜∀X⦁ LinearOrder (X, $≤⋎t⋎4) ⇒ (fT = Lub $≤⋎t⋎4 X ⇔ fT ∈ X)⌝);
a (REPEAT_N 2 strip_tac);
a (fc_tac [≤⋎t⋎4_lin_cases_lemma]
	THEN asm_rewrite_tac[]
	THEN contr_tac);
val ≤⋎t⋎4_lin_lub_lemma2 = save_pop_thm "≤⋎t⋎4_lin_lub_lemma2";

set_goal ([], ⌜∀X⦁ LinearOrder (X, $≤⋎t⋎4) ⇒ (Glb $≤⋎t⋎4 X ≤⋎t⋎4 fB ⇔ fB ∈ X)⌝);
a (REPEAT_N 2 strip_tac);
a (fc_tac [≤⋎t⋎4_lin_cases_lemma]
	THEN asm_rewrite_tac[]
	THEN contr_tac);
val ≤⋎t⋎4_lin_glb_lemma = save_pop_thm "≤⋎t⋎4_lin_glb_lemma";

set_goal ([], ⌜∀X⦁ LinearOrder (X, $≤⋎t⋎4) ⇒ (Glb $≤⋎t⋎4 X = fB ⇔ fB ∈ X)⌝);
a (REPEAT_N 2 strip_tac);
a (fc_tac [≤⋎t⋎4_lin_cases_lemma]
	THEN asm_rewrite_tac[]
	THEN contr_tac);
val ≤⋎t⋎4_lin_glb_lemma2 = save_pop_thm "≤⋎t⋎4_lin_glb_lemma2";
=TEX
}%ignore

\section{ORDERS AND PRE-ORDERS}

\subsection{Domain Restriction}

The following operator restricts a reflexive partial order to some subdomain of the type over which it is defined.

=SML
declare_infix(300, "◁⋎o");
=TEX

ⓈHOLCONST
│ ⦏$◁⋎o⦎: 'a SET → ('a → 'a → BOOL) → ('a → 'a → BOOL)
├───────────
│   ∀ V r⦁ V ◁⋎o r = λx y⦁ if x ∈ V ∧ y ∈ V then r x y else x = y
■

\subsection{Conjunction of Orders}

ⓈHOLCONST
│ ⦏ConjOrder⦎ : ('a → 'a → BOOL) → ('a → 'a → BOOL) → ('a → 'a → BOOL)
├───────────
│ ∀r1 r2⦁ ConjOrder r1 r2 = λx y⦁ r1 x y ∧ r2 x y
■

\subsection{Derived Orderings}

I don't know a good name for these, but a common way to impose an order on a collection is by defining a function which maps the collection into some collection for which we have a suitable ordering.
Often suitable means well-founded, but in our case it is completeness which is desired.

ⓈHOLCONST
│ ⦏DerivedOrder⦎ : ('b → 'a) → ('a → 'a → BOOL) → ('b → 'b → BOOL)
├───────────
│ ∀f r⦁ DerivedOrder f r = λx y⦁ r (f x) (f y)
■

We require sufficient conditions for the result to be complete.

=GFT
⦏fi_isub_lemma⦎ =
   ⊢ ∀ f r s e⦁ IsUb r (FunImage f s) (f e) ⇒ IsUb (DerivedOrder f r) s e

⦏do_isub_lemma⦎ =
   ⊢ ∀ f r s x⦁ IsUb (DerivedOrder f r) s x ⇒ IsUb r (FunImage f s) (f x)

⦏fi_islub_lemma⦎ =
   ⊢ ∀ f r s e
     ⦁ IsLub r (FunImage f s) (f e) ⇒ IsLub (DerivedOrder f r) s e

⦏do_lubs_exist_thm⦎ =
   ⊢ ∀ f r⦁ LubsExist r ∧ Onto f ⇒ LubsExist (DerivedOrder f r)
=TEX
=GFT
⦏fi_islb_lemma⦎ =
   ⊢ ∀ f r s e⦁ IsLb r (FunImage f s) (f e) ⇒ IsLb (DerivedOrder f r) s e

⦏do_islb_lemma⦎ =
   ⊢ ∀ f r s x⦁ IsLb (DerivedOrder f r) s x ⇒ IsLb r (FunImage f s) (f x)

⦏fi_isglb_lemma⦎ =
   ⊢ ∀ f r s e⦁ IsGlb r (FunImage f s) (f e) ⇒ IsGlb (DerivedOrder f r) s e

⦏do_glbs_exist_thm⦎ =
   ⊢ ∀ f r⦁ GlbsExist r ∧ Onto f ⇒ GlbsExist (DerivedOrder f r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀f r s e⦁ IsUb r (FunImage f s) (f e) ⇒ IsUb (DerivedOrder f r) s e⌝);
a (rewrite_tac (map get_spec [⌜Onto⌝, ⌜DerivedOrder⌝, ⌜IsUb⌝, ⌜FunImage⌝])
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜f x⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
val fi_isub_lemma = pop_thm ();

set_goal([], ⌜∀f r s x⦁ IsUb (DerivedOrder f r) s x ⇒ IsUb r (FunImage f s) (f x)⌝);
a (rewrite_tac (map get_spec [⌜IsUb⌝, ⌜DerivedOrder⌝, ⌜FunImage⌝]) THEN REPEAT strip_tac);
a (asm_fc_tac[]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
val do_isub_lemma = pop_thm ();

set_goal([], ⌜∀f r s e⦁ IsLub r (FunImage f s) (f e) ⇒ IsLub (DerivedOrder f r) s e ⌝);
a (rewrite_tac (map get_spec [⌜Onto⌝, ⌜IsLub⌝]) THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [fi_isub_lemma]);
(* *** Goal "2" *** *)
a (fc_tac [do_isub_lemma]);
a (all_asm_fc_tac[]);
a (rewrite_tac (map get_spec [⌜DerivedOrder⌝]) THEN REPEAT strip_tac);
val fi_islub_lemma = pop_thm ();

set_goal([], ⌜∀f r⦁ LubsExist r ∧ Onto f ⇒ LubsExist (DerivedOrder f r)⌝);
a (rewrite_tac (map get_spec [⌜Onto⌝, ⌜LubsExist⌝]) THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜FunImage f s⌝);
a (spec_nth_asm_tac 2 ⌜e⌝);
a (var_elim_asm_tac ⌜e = f x⌝ THEN ∃_tac ⌜x⌝ THEN fc_tac [fi_islub_lemma] THEN asm_rewrite_tac[]);
val do_lubs_exist_thm = save_pop_thm "do_lubs_exist_thm";

set_goal([], ⌜∀f r s e⦁ IsLb r (FunImage f s) (f e) ⇒ IsLb (DerivedOrder f r) s e⌝);
a (rewrite_tac (map get_spec [⌜Onto⌝, ⌜DerivedOrder⌝, ⌜IsLb⌝, ⌜FunImage⌝])
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜f x⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
val fi_islb_lemma = pop_thm ();

set_goal([], ⌜∀f r s x⦁ IsLb (DerivedOrder f r) s x ⇒ IsLb r (FunImage f s) (f x)⌝);
a (rewrite_tac (map get_spec [⌜IsLb⌝, ⌜DerivedOrder⌝, ⌜FunImage⌝]) THEN REPEAT strip_tac);
a (asm_fc_tac[]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
val do_islb_lemma = pop_thm ();

set_goal([], ⌜∀f r s e⦁ IsGlb r (FunImage f s) (f e) ⇒ IsGlb (DerivedOrder f r) s e ⌝);
a (rewrite_tac (map get_spec [⌜Onto⌝, ⌜IsGlb⌝]) THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [fi_islb_lemma]);
(* *** Goal "2" *** *)
a (fc_tac [do_islb_lemma]);
a (all_asm_fc_tac[]);
a (rewrite_tac (map get_spec [⌜DerivedOrder⌝]) THEN REPEAT strip_tac);
val fi_isglb_lemma = pop_thm ();

set_goal([], ⌜∀f r⦁ GlbsExist r ∧ Onto f ⇒ GlbsExist (DerivedOrder f r)⌝);
a (rewrite_tac (map get_spec [⌜Onto⌝, ⌜GlbsExist⌝]) THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜FunImage f s⌝);
a (spec_nth_asm_tac 2 ⌜e⌝);
a (var_elim_asm_tac ⌜e = f x⌝ THEN ∃_tac ⌜x⌝ THEN fc_tac [fi_isglb_lemma] THEN asm_rewrite_tac[]);
val do_glbs_exist_thm = save_pop_thm "do_glbs_exist_thm";
=TEX
}%ignore

=GFT
⦏wf_derived_order_thm⦎ =
	⊢ ∀ r⦁ well_founded r ⇒ (∀ f⦁ well_founded (DerivedOrder f r))
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ well_founded r ⇒ ∀f⦁ well_founded (DerivedOrder f r)⌝);
a (strip_tac
	THEN rewrite_tac[get_spec ⌜well_founded⌝, get_spec ⌜DerivedOrder⌝]
	THEN REPEAT strip_tac);
a (SPEC_NTH_ASM_T 2 ⌜λx:'b⦁ ¬ ∃y:'a⦁ x = f y ∧ ¬ s y⌝ ante_tac
	THEN_TRY rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 4 ⌜y⌝);
a (spec_nth_asm_tac 5 ⌜f y'⌝);
(* *** Goal "1.1" *** *)
a (var_elim_asm_tac ⌜x' = f y⌝);
(* *** Goal "1.2" *** *)
a (spec_nth_asm_tac 1 ⌜y'⌝);
(* *** Goal "2" *** *)
a (list_spec_nth_asm_tac 1 [⌜f x⌝]);
a (list_spec_nth_asm_tac 1 [⌜x⌝]);
val wf_derived_order_thm = save_pop_thm "wf_derived_order_thm";
=TEX
}%ignore

\subsection{Projections}

Projections are a special case of derived orderings in which the onto requirement can be taken for granted.

=GFT
⦏projections_onto_lemma⦎ =
   ⊢ Onto Fst ∧ Onto Snd

⦏lubsexist_dofst_thm⦎ =
   ⊢ ∀ f r⦁ LubsExist r ⇒ LubsExist (DerivedOrder Fst r)

⦏glbsexist_dofst_thm⦎ =
   ⊢ ∀ f r⦁ GlbsExist r ⇒ GlbsExist (DerivedOrder Fst r)

⦏lubsexist_dosnd_thm⦎ =
   ⊢ ∀ f r⦁ LubsExist r ⇒ LubsExist (DerivedOrder Snd r)

⦏glbsexist_dosnd_thm⦎ =
   ⊢ ∀ f r⦁ GlbsExist r ⇒ GlbsExist (DerivedOrder Snd r)
=TEX


\ignore{
=SML
set_goal([], ⌜Onto Fst ∧ Onto Snd⌝);
a (rewrite_tac (map get_spec [⌜Onto⌝]) THEN REPEAT strip_tac);
a (∃_tac ⌜(y, z)⌝ THEN rewrite_tac[]);
a (∃_tac ⌜(z, y)⌝ THEN rewrite_tac[]);
val projections_onto_lemma = pop_thm ();

set_goal([], ⌜∀f r⦁ LubsExist r ⇒ LubsExist (DerivedOrder Fst r)⌝);
a (REPEAT strip_tac THEN bc_tac [do_lubs_exist_thm]
	THEN_TRY asm_rewrite_tac[projections_onto_lemma]);
val lubsexist_dofst_thm = save_pop_thm "lubsexist_dofst_thm";

set_goal([], ⌜∀f r⦁ GlbsExist r ⇒ GlbsExist (DerivedOrder Fst r)⌝);
a (REPEAT strip_tac THEN bc_tac [do_glbs_exist_thm]
	THEN_TRY asm_rewrite_tac[projections_onto_lemma]);
val glbsexist_dofst_thm = save_pop_thm "glbsexist_dofst_thm";

set_goal([], ⌜∀f r⦁ LubsExist r ⇒ LubsExist (DerivedOrder Snd r)⌝);
a (REPEAT strip_tac THEN bc_tac [do_lubs_exist_thm]
	THEN_TRY asm_rewrite_tac[projections_onto_lemma]);
val lubsexist_dosnd_thm = save_pop_thm "lubsexist_dosnd_thm";

set_goal([], ⌜∀f r⦁ GlbsExist r ⇒ GlbsExist (DerivedOrder Snd r)⌝);
a (REPEAT strip_tac THEN bc_tac [do_glbs_exist_thm]
	THEN_TRY asm_rewrite_tac[projections_onto_lemma]);
val glbsexist_dosnd_thm = save_pop_thm "glbsexist_dosnd_thm";
=TEX
}%ignore

\subsection{Functions}

Most of our orderings are orderings of functions obtained from orderings of truth values by the following operation.

ⓈHOLCONST
│ ⦏Pw⦎ : ('a → 'a → BOOL) → (('b → 'a) → ('b → 'a) → BOOL)
├───────────
│ ∀ r⦁ Pw r = λ lo ro⦁ ∀x⦁ r (lo x) (ro x)
■

=GFT
⦏pw_isub_lemma⦎ =
   ⊢ ∀ r G f⦁ (∀ v⦁ IsUb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v)) ⇒ IsUb (Pw r) G f

⦏pw_isub_lemma2⦎ =
   ⊢ ∀ r G f⦁ IsUb (Pw r) G f ⇔ (∀ v⦁ IsUb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v))

⦏pw_islb_lemma⦎ =
   ⊢ ∀ r G f⦁ (∀ v⦁ IsLb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v)) ⇒ IsLb (Pw r) G f

⦏pw_islb_lemma2⦎ =
   ⊢ ∀ r G f⦁ IsLb (Pw r) G f ⇔ (∀ v⦁ IsLb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v))

⦏pw_islub_lemma⦎ =
   ⊢ ∀ r G f
     ⦁ (∀ v⦁ IsLub r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v)) ⇒ IsLub (Pw r) G f

⦏pw_islub_lemma2⦎ =
   ⊢ ∀ r G f
     ⦁ IsLub (Pw r) G f ⇔ (∀ v⦁ IsLub r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v))

⦏pw_isglb_lemma⦎ =
   ⊢ ∀ r G f
     ⦁ (∀ v⦁ IsGlb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v)) ⇒ IsGlb (Pw r) G f

⦏pw_isglb_lemma2⦎ =
   ⊢ ∀ r G f
     ⦁ IsGlb (Pw r) G f ⇔ (∀ v⦁ IsGlb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v))

⦏pw_rpo_lemma⦎ =
	⊢ ∀ r⦁ Rpo (Universe, r) ⇒ Rpo (Universe, Pw r)

⦏pw_cc_lemma⦎ =
	⊢ ∀ r⦁ CcRpo (Universe, r) ⇒ ChainComplete (Universe, Pw r)

⦏pw_ccrpou_thm⦎ =
	⊢ ∀ r⦁ CcRpoU r ⇒ CcRpoU (Pw r)

⦏pw_lubs_exist_thm⦎ =
	⊢ ∀ r⦁ LubsExist r ⇒ LubsExist (Pw r)

⦏pw_glbs_exist_thm⦎ =
	⊢ ∀ r⦁ GlbsExist r ⇒ GlbsExist (Pw r)

⦏pw_crpou_thm⦎ =
	⊢ ∀ r⦁ CRpoU r ⇒ CRpoU (Pw r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r G f⦁ (∀ v⦁ IsUb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))
	⇒ IsUb (Pw r) G f⌝);
a (rewrite_tac [get_spec ⌜IsUb⌝, get_spec ⌜Pw⌝] THEN REPEAT strip_tac);
a (list_spec_nth_asm_tac 2 [⌜x'⌝, ⌜x x'⌝]);
a (spec_nth_asm_tac 1 ⌜x⌝);
val pw_isub_lemma = pop_thm ();

set_goal([], ⌜∀r G f⦁ IsUb (Pw r) G f ⇔ (∀ v⦁ IsUb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))⌝);
a (REPEAT strip_tac THEN all_fc_tac [pw_isub_lemma]);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜IsUb⌝, get_spec ⌜Pw⌝] THEN REPEAT strip_tac);
a (asm_fc_tac[] THEN asm_rewrite_tac[]);
val pw_isub_lemma2 = pop_thm ();

set_goal([], ⌜∀r G f⦁ (∀ v⦁ IsLb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))
	⇒ IsLb (Pw r) G f⌝);
a (rewrite_tac [get_spec ⌜IsLb⌝, get_spec ⌜Pw⌝] THEN REPEAT strip_tac);
a (list_spec_nth_asm_tac 2 [⌜x'⌝, ⌜x x'⌝]);
a (spec_nth_asm_tac 1 ⌜x⌝);
val pw_islb_lemma = pop_thm ();

set_goal([], ⌜∀r G f⦁ IsLb (Pw r) G f
	⇔ (∀ v⦁ IsLb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))⌝);
a (REPEAT strip_tac THEN all_fc_tac [pw_islb_lemma]);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜IsLb⌝, get_spec ⌜Pw⌝] THEN REPEAT strip_tac);
a (asm_fc_tac[] THEN asm_rewrite_tac[]);
val pw_islb_lemma2 = pop_thm ();

set_goal([], ⌜∀r G f⦁ (∀ v⦁ IsLub r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))
	⇒ IsLub (Pw r) G f⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜IsLub⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜∀ v⦁ IsUb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v)⌝
	THEN1 (POP_ASM_T (strip_asm_tac o (rewrite_rule [get_spec ⌜IsLub⌝]))
		THEN asm_rewrite_tac[]));
a (fc_tac [pw_isub_lemma]);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜Pw⌝]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜x'⌝);
a (fc_tac [get_spec ⌜IsLub⌝]);
a (spec_nth_asm_tac 2 ⌜x x'⌝);
a (GET_ASM_T ⌜IsUb (Pw r) G x⌝ ante_tac
	THEN rewrite_tac [get_spec ⌜Pw⌝]);
a (swap_nth_asm_concl_tac 1);
a (DROP_NTH_ASM_T 6 ante_tac
	THEN rewrite_tac [get_spec ⌜Pw⌝, get_spec ⌜IsUb⌝]
	THEN REPEAT strip_tac);
a (all_asm_fc_tac[]);
a (spec_nth_asm_tac 2 ⌜x'⌝
	THEN POP_ASM_T ante_tac
	THEN asm_rewrite_tac[]);
val pw_islub_lemma = pop_thm ();

set_goal([], ⌜∀r G f⦁ IsLub (Pw r) G f
	⇔ (∀ v⦁ IsLub r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))⌝);
a (REPEAT strip_tac THEN all_fc_tac [pw_islub_lemma]);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜IsLub⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [pw_isub_lemma2] THEN asm_rewrite_tac []);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜λz⦁ if z = v then x else f z⌝);
(* *** Goal "2.1" *** *)
a (swap_nth_asm_concl_tac 1);
a (DROP_NTH_ASM_T 4 ante_tac);
a (DROP_NTH_ASM_T 2 ante_tac);
a (rewrite_tac [pw_isub_lemma2]);
a (rewrite_tac[get_spec ⌜IsUb⌝]);
a (REPEAT strip_tac);
a (cond_cases_tac ⌜v' = v⌝);
(* *** Goal "2.1.1" *** *)
a (var_elim_asm_tac ⌜v' = v⌝);
a (var_elim_asm_tac ⌜x' = g v⌝);
a (spec_nth_asm_tac 3 ⌜g v⌝);
a (spec_nth_asm_tac 1 ⌜g⌝);
(* *** Goal "2.1.2" *** *)
a (var_elim_asm_tac ⌜x' = g v'⌝);
a (list_spec_nth_asm_tac 3 [⌜v'⌝, ⌜g v'⌝]);
a (spec_nth_asm_tac 1 ⌜g⌝);
(* *** Goal "2.2" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜Pw⌝]);
a (strip_tac THEN spec_nth_asm_tac 1 ⌜v⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac[]);
val pw_islub_lemma2 = pop_thm ();

set_goal([], ⌜∀r G f⦁ (∀ v⦁ IsGlb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))
	⇒ IsGlb (Pw r) G f⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜IsGlb⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜∀ v⦁ IsLb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v)⌝
	THEN1 (POP_ASM_T (strip_asm_tac o (rewrite_rule [get_spec ⌜IsGlb⌝]))
		THEN asm_rewrite_tac[]));
a (fc_tac [pw_islb_lemma]);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜Pw⌝]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜x'⌝);
a (fc_tac [get_spec ⌜IsGlb⌝]);
a (spec_nth_asm_tac 2 ⌜x x'⌝);
a (GET_ASM_T ⌜IsLb (Pw r) G x⌝ ante_tac
	THEN rewrite_tac [get_spec ⌜Pw⌝]);
a (swap_nth_asm_concl_tac 1);
a (DROP_NTH_ASM_T 6 ante_tac
	THEN rewrite_tac [get_spec ⌜Pw⌝, get_spec ⌜IsLb⌝]
	THEN REPEAT strip_tac);
a (all_asm_fc_tac[]);
a (spec_nth_asm_tac 2 ⌜x'⌝
	THEN POP_ASM_T ante_tac
	THEN asm_rewrite_tac[]);
val pw_isglb_lemma = pop_thm ();

set_goal([], ⌜∀r G f⦁ IsGlb (Pw r) G f
	⇔ (∀ v⦁ IsGlb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))⌝);
a (REPEAT strip_tac THEN all_fc_tac [pw_isglb_lemma]);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜IsGlb⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [pw_islb_lemma2] THEN asm_rewrite_tac []);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜λz⦁ if z = v then x else f z⌝);
(* *** Goal "2.1" *** *)
a (swap_nth_asm_concl_tac 1);
a (DROP_NTH_ASM_T 4 ante_tac);
a (DROP_NTH_ASM_T 2 ante_tac);
a (rewrite_tac [pw_islb_lemma2]);
a (rewrite_tac[get_spec ⌜IsLb⌝]);
a (REPEAT strip_tac);
a (cond_cases_tac ⌜v' = v⌝);
(* *** Goal "2.1.1" *** *)
a (var_elim_asm_tac ⌜v' = v⌝);
a (var_elim_asm_tac ⌜x' = g v⌝);
a (spec_nth_asm_tac 3 ⌜g v⌝);
a (spec_nth_asm_tac 1 ⌜g⌝);
(* *** Goal "2.1.2" *** *)
a (var_elim_asm_tac ⌜x' = g v'⌝);
a (list_spec_nth_asm_tac 3 [⌜v'⌝, ⌜g v'⌝]);
a (spec_nth_asm_tac 1 ⌜g⌝);
(* *** Goal "2.2" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜Pw⌝]);
a (strip_tac THEN spec_nth_asm_tac 1 ⌜v⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac[]);
val pw_isglb_lemma2 = pop_thm ();

(* set_merge_pcs ["rbjmisc1", "'GS1", "'misc2"]; *)

set_merge_pcs ["rbjmisc1", "'misc1"];

set_goal([], ⌜∀r⦁ Rpo (Universe, r) ⇒ Rpo (Universe, Pw r)⌝);
a (REPEAT strip_tac
	THEN fc_tac[rpou_fc_clauses]
	THEN rewrite_tac (map get_spec [⌜Rpo⌝, ⌜Pw⌝, ⌜PartialOrder⌝, ⌜Antisym⌝, ⌜Trans⌝, ⌜Refl⌝])
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (list_spec_nth_asm_tac 3 [⌜x x'⌝, ⌜y x'⌝]);
(* *** Goal "1.1" *** *)
a (∃_tac ⌜x'⌝ THEN strip_tac);
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (REPEAT_N 2 (spec_nth_asm_tac 2 ⌜x'⌝)
	THEN all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a (asm_rewrite_tac[]);
val pw_rpo_lemma = pop_thm ();

set_goal([], ⌜∀r⦁ RpoU r ⇒ RpoU (Pw r)⌝);
a (rewrite_tac [get_spec ⌜RpoU⌝] THEN REPEAT strip_tac);
a (fc_tac [pw_rpo_lemma]);
val pw_rpou_lemma = pop_thm ();

(* set_merge_pcs ["misc11", "'GS1", "'misc2"]; *)
set_merge_pcs ["rbjmisc1", "'misc1"];

set_goal([], ⌜∀r⦁ CcRpo (Universe, r) ⇒ ChainComplete (Universe, Pw r)⌝);
a (rewrite_tac (map get_spec [⌜CcRpo⌝, ⌜Rpo⌝, ⌜PartialOrder⌝, ⌜Antisym⌝, ⌜ChainComplete⌝])
	THEN REPEAT strip_tac);
a (lemma_tac ⌜∀v⦁ LinearOrder ({w | ∃f⦁ f ∈ Y ∧ w = f v}, r)⌝);
(* *** Goal "1" *** *)
a (rewrite_tac (map get_spec [⌜LinearOrder⌝, ⌜PartialOrder⌝, ⌜Antisym⌝, ⌜Trans⌝, ⌜Trich⌝])
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a (FC_T (MAP_EVERY (asm_tac o (rewrite_rule[]))) [get_spec ⌜Trans⌝]);
a (all_asm_fc_tac[]);
(* *** Goal "1.3" *** *)
a (fc_tac [get_spec ⌜LinearOrder⌝]);
a (fc_tac [get_spec ⌜Trich⌝]);
(* a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜Pw⌝]
	THEN REPEAT strip_tac); *)
a (list_spec_nth_asm_tac 1 [⌜f⌝, ⌜f'⌝]);
(* *** Goal "1.3.1" *** *)
a (DROP_NTH_ASM_T 6 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.1.2" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜Pw⌝] THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜v⌝);
a (DROP_NTH_ASM_T 6 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.3.3" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜Pw⌝] THEN strip_tac);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜∃f⦁ ∀v⦁ IsLub r {w|∃ f⦁ f ∈ Y ∧ w = f v} (f v)⌝
	THEN1 prove_∃_tac);
(* *** Goal "2.1" *** *)
a (strip_tac);
a (spec_nth_asm_tac 1 ⌜v'⌝);
a (all_asm_fc_tac[]);
a (∃_tac ⌜x⌝ THEN strip_tac);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜f⌝);
a (bc_tac [pw_islub_lemma]);
a (asm_rewrite_tac[]);
val pw_cc_lemma = pop_thm ();

set_goal([], ⌜∀r⦁ CcRpoU r ⇒ CcRpoU (Pw r)⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜CcRpoU⌝]);
a (fc_tac [get_spec ⌜CcRpo⌝]);
a (fc_tac [pw_rpo_lemma]);
a (fc_tac [pw_cc_lemma]);
a (asm_rewrite_tac (map get_spec [⌜CcRpoU⌝, ⌜CcRpo⌝]));
val pw_ccrpou_thm = save_pop_thm "pw_ccrpou_thm";

set_goal([], ⌜∀r⦁ LubsExist r ⇒ LubsExist (Pw r)⌝);
a (rewrite_tac [get_spec ⌜LubsExist⌝] THEN REPEAT strip_tac);
a (lemma_tac ⌜∃f⦁ ∀v⦁ IsLub r {w|∃ g⦁ g ∈ s ∧ w = g v} (f v)⌝
	THEN1 prove_∃_tac);
(* *** Goal "1" *** *)
a (strip_tac);
a (spec_nth_asm_tac 1 ⌜{w|∃ g⦁ g ∈ s ∧ w = g v'}⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [pw_islub_lemma]);
a (∃_tac ⌜f⌝ THEN asm_rewrite_tac[]);
val pw_lubs_exist_thm = save_pop_thm "pw_lubs_exist_thm";

set_goal([], ⌜∀r⦁ GlbsExist r ⇒ GlbsExist (Pw r)⌝);
a (rewrite_tac [get_spec ⌜GlbsExist⌝] THEN REPEAT strip_tac);
a (lemma_tac ⌜∃f⦁ ∀v⦁ IsGlb r {w|∃ g⦁ g ∈ s ∧ w = g v} (f v)⌝
	THEN1 prove_∃_tac);
(* *** Goal "1" *** *)
a (strip_tac);
a (spec_nth_asm_tac 1 ⌜{w|∃ g⦁ g ∈ s ∧ w = g v'}⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [pw_isglb_lemma]);
a (∃_tac ⌜f⌝ THEN asm_rewrite_tac[]);
val pw_glbs_exist_thm = save_pop_thm "pw_glbs_exist_thm";

set_goal([], ⌜∀r⦁ CRpoU r ⇒ CRpoU (Pw r)⌝);
a (rewrite_tac (map get_spec [⌜CRpoU⌝, ⌜RpoU⌝]) THEN REPEAT strip_tac);
a (fc_tac [pw_rpo_lemma]);
a (fc_tac [pw_lubs_exist_thm]);
a (fc_tac [pw_glbs_exist_thm]);
val pw_crpou_thm = save_pop_thm "pw_crpou_thm";
=TEX
}%ignore

=GFT
⦏pw_≤⋎t⋎4_lubsexist_thm⦎ = ⊢ LubsExist (Pw $≤⋎t⋎4)

⦏pw_≤⋎t⋎4_glbsexist_thm⦎ = ⊢ GlbsExist (Pw $≤⋎t⋎4)

⦏pw_≤⋎t⋎4_crpou_thm⦎ = ⊢ CRpoU (Pw $≤⋎t⋎4)
=TEX

\ignore{
=SML
set_goal([], ⌜LubsExist (Pw $≤⋎t⋎4)⌝);
a (bc_tac [pw_lubs_exist_thm]);
a (rewrite_tac []);
val pw_≤⋎t⋎4_lubsexist_thm = save_pop_thm "pw_≤⋎t⋎4_lubsexist_thm";

set_goal([], ⌜GlbsExist (Pw $≤⋎t⋎4)⌝);
a (bc_tac [pw_glbs_exist_thm]);
a (rewrite_tac []);
val pw_≤⋎t⋎4_glbsexist_thm = save_pop_thm "pw_≤⋎t⋎4_glbsexist_thm";

set_goal([], ⌜CRpoU (Pw $≤⋎t⋎4)⌝);
a (bc_tac [pw_crpou_thm]);
a (rewrite_tac []);
val pw_≤⋎t⋎4_cprou_thm = save_pop_thm "pw_≤⋎t⋎4_crpou_thm";
=TEX
}%ignore

=GFT
⦏crpou_lub_pw_lemma⦎ =
   ⊢ ∀ r
     ⦁ CRpoU r ⇒ (∀ G⦁ Lub (Pw r) G = (λ x⦁ Lub r {w|∃ g⦁ g ∈ G ∧ w = g x}))

⦏crpou_lub_pw_pw_lemma⦎ =
   ⊢ ∀ r
     ⦁ CRpoU r
         ⇒ (∀ G
         ⦁ Lub (Pw (Pw r)) G = (λ x y⦁ Lub r {w|∃ g⦁ g ∈ G ∧ w = g x y}))
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ CRpoU r ⇒ ∀G⦁ Lub (Pw r) G = λx⦁ Lub r {w | ∃g⦁ g ∈ G ∧ w = g x}⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜IsLub (Pw r) G λx⦁ Lub r {w | ∃g⦁ g ∈ G ∧ w = g x}⌝);
(* *** Goal "1" *** *)
a (REPEAT strip_tac THEN fc_tac [crpou_fc_clauses]);
a (rewrite_tac [pw_islub_lemma2] THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜{w|∃ g⦁ g ∈ G ∧ w = g v}⌝ (∀_elim ⌜r⌝ lub_lub_lemma2)));
(* *** Goal "2" *** *)
a (lemma_tac ⌜IsLub (Pw r) G (Lub (Pw r) G)⌝);
(* *** Goal "2.1" *** *)
a (fc_tac [inst_type_rule [(ⓣ'a⌝, ⓣ'b⌝), (ⓣ'b⌝, ⓣ'a⌝)] pw_crpou_thm]);
a (fc_tac [crpou_fc_clauses]);
a (strip_asm_tac (∀_elim ⌜G⌝ (∀_elim ⌜Pw r⌝ lub_lub_lemma2)));
(* *** Goal "2.2" *** *)
a (fc_tac [inst_type_rule [(ⓣ'a⌝, ⓣ'b⌝), (ⓣ'b⌝, ⓣ'a⌝)] pw_crpou_thm]);
a (fc_tac [get_spec ⌜CRpoU⌝]);
a (fc_tac [get_spec ⌜RpoU⌝]);
a (fc_tac [get_spec ⌜Rpo⌝]);
a (fc_tac [get_spec ⌜PartialOrder⌝]);
a (all_fc_tac [lub_unique_lemma]);
a (POP_ASM_T discard_tac THEN once_asm_rewrite_tac [] THEN strip_tac);
val crpou_lub_pw_lemma = pop_thm ();

set_goal([], ⌜∀r⦁ CRpoU r ⇒ ∀G:('b → 'c → 'a) SET⦁ Lub (Pw (Pw r)) G
		= λx y⦁ Lub r {w | ∃g⦁ g ∈ G ∧ w = g x y}⌝);
a (REPEAT strip_tac);
a (fc_tac [inst_type_rule [(ⓣ'c⌝, ⓣ'a⌝), (ⓣ'a⌝, ⓣ'b⌝)] pw_crpou_thm]);
a (fc_tac [crpou_lub_pw_lemma]);
a (asm_rewrite_tac[]);
a (rewrite_tac [∀_elim ⌜{w|∃ g⦁ g ∈ G ∧ (∀ x'⦁ w x' = g x x')}⌝
	(⇒_elim (∀_elim ⌜r⌝ crpou_lub_pw_lemma) (asm_rule ⌜CRpoU r⌝))]);
a (LEMMA_T ⌜{w|∃ g⦁ (∃ g'⦁ g' ∈ G ∧ (∀ x'⦁ g x' = g' x x')) ∧ w = g x'}
             = {w|∃ g⦁ g ∈ G ∧ w = g x x'}⌝ rewrite_thm_tac);
a (rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜g'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜g x⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜g⌝ THEN asm_rewrite_tac[]);
val crpou_lub_pw_pw_lemma = pop_thm ();
=TEX
}%ignore


Sometimes we are only interested in the behaviour of a function over some subset of its domain type.
The following version of {\it Pw} is parameterised by a set which gives the subdomain over which the values of the function are significant to the resulting ordering.

This is not a partial order since it is not antisymmetric.
It is a pre-order.

ⓈHOLCONST
│ ⦏PwS⦎ : 'b SET → ('a → 'a → BOOL) → (('b → 'a) → ('b → 'a) → BOOL)
├───────────
│ ∀V r⦁ PwS V r = λ lo ro⦁ ∀x⦁ x ∈ V ⇒ r (lo x) (ro x)
■

=GFT
⦏pws_isub_lemma⦎ =
   ⊢ ∀V r G f⦁ (∀ v⦁ v ∈ V ⇒ IsUb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))
	⇒ IsUb (PwS V r) G f

⦏pws_isub_lemma3⦎ =
   ⊢ ∀ V r G f
     ⦁ IsUb (PwS V r) G f
         ⇔ (∀ v⦁ v ∈ V ⇒ IsUb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v))
=TEX
=GFT
⦏pws_islb_lemma⦎ =
   ⊢ ∀ V r G f⦁ (∀ v⦁ v ∈ V ⇒ IsLb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v))
	⇒ IsLb (PwS V r) G f

⦏pws_islb_lemma2⦎ =
   ⊢ ∀ V r G f
     ⦁ IsLb (PwS V r) G f
         ⇒ (∀ v⦁ v ∈ V ⇒ IsLb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v))

⦏pws_islb_lemma3⦎ =
   ⊢ ∀ V r G f
     ⦁ IsLb (PwS V r) G f
         ⇔ (∀ v⦁ v ∈ V ⇒ IsLb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v))
=TEX
=GFT
⦏pws_islub_lemma⦎ =
   ⊢ ∀ V r G f
     ⦁ (∀ v⦁ v ∈ V ⇒ IsLub r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v))
	⇒ IsLub (PwS V r) G f

⦏pws_islub_lemma2⦎ =
   ⊢ ∀ V r G f
     ⦁ IsLub (PwS V r) G f
         ⇒ (∀ v⦁ v ∈ V ⇒ IsLub r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v))

⦏pws_islub_lemma3⦎ =
   ⊢ ∀ V r G f
     ⦁ IsLub (PwS V r) G f
         ⇔ (∀ v⦁ v ∈ V ⇒ IsLub r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v))
=TEX
=GFT
⦏pws_isglb_lemma⦎ =
   ⊢ ∀ V r G f
     ⦁ (∀ v⦁ v ∈ V ⇒ IsGlb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v))
	⇒ IsGlb (PwS V r) G f

⦏pws_isglb_lemma2⦎ =
   ⊢ ∀ V r G f
     ⦁ IsGlb (PwS V r) G f
         ⇒ (∀ v⦁ v ∈ V ⇒ IsGlb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v))

⦏pws_isglb_lemma3⦎ =
   ⊢ ∀ V r G f
     ⦁ (∀ v⦁ v ∈ V ⇒ IsGlb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v))
         ⇔ IsGlb (PwS V r) G f
=TEX
=GFT
⦏pws_lubs_exist_thm⦎ =
	⊢ ∀ V r⦁ LubsExist r ⇒ LubsExist (PwS V r)

⦏pws_glbs_exist_thm⦎ =
	⊢ ∀ V r⦁ GlbsExist r ⇒ GlbsExist (PwS V r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀V r G f⦁ (∀ v⦁ v ∈ V ⇒ IsUb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))
	⇒ IsUb (PwS V r) G f⌝);
a (rewrite_tac [get_spec ⌜IsUb⌝, get_spec ⌜PwS⌝] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 3 ⌜x'⌝);
a (list_spec_nth_asm_tac 1 [⌜x x'⌝]);
a (spec_nth_asm_tac 1 ⌜x⌝);
val pws_isub_lemma = pop_thm ();

set_goal([], ⌜∀V r G f⦁ IsUb (PwS V r) G f ⇒ (∀ v⦁ v ∈ V
		⇒ IsUb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))⌝);
a (rewrite_tac [get_spec ⌜IsUb⌝, get_spec ⌜PwS⌝] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 4 ⌜g⌝);
a (list_spec_nth_asm_tac 1 [⌜v⌝]);
a (asm_rewrite_tac[]);
val pws_isub_lemma2 = pop_thm ();

set_goal([], ⌜∀V r G f⦁ IsUb (PwS V r) G f
	⇔ (∀ v⦁ v ∈ V ⇒ IsUb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))⌝);
a (REPEAT_N 7 strip_tac THEN asm_fc_tac [pws_isub_lemma, pws_isub_lemma2]);
val pws_isub_lemma3 = pop_thm ();

set_goal([], ⌜∀V r G f⦁ (∀ v⦁ v ∈ V ⇒ IsLb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))
	⇒ IsLb (PwS V r) G f⌝);
a (rewrite_tac [get_spec ⌜IsLb⌝, get_spec ⌜PwS⌝] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 3 ⌜x'⌝);
a (spec_nth_asm_tac 1 ⌜x x'⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
val pws_islb_lemma = pop_thm ();

set_goal([], ⌜∀V r G f⦁ IsLb (PwS V r) G f
	⇒ (∀ v⦁ v ∈ V ⇒ IsLb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))⌝);
a (rewrite_tac [get_spec ⌜IsLb⌝, get_spec ⌜PwS⌝] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 4 ⌜g⌝);
a (spec_nth_asm_tac 1 ⌜v⌝);
a (asm_rewrite_tac []);
val pws_islb_lemma2 = pop_thm ();

set_goal([], ⌜∀V r G f⦁ IsLb (PwS V r) G f
	⇔ (∀ v⦁ v ∈ V ⇒ IsLb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))⌝);
a (REPEAT_N 7 strip_tac THEN asm_fc_tac [pws_islb_lemma, pws_islb_lemma2]);
val pws_islb_lemma3 = pop_thm ();

set_goal([], ⌜∀V r G f⦁ (∀ v⦁ v ∈ V ⇒ IsLub r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))
	⇒ IsLub (PwS V r) G f⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜IsLub⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜∀ v⦁ v ∈ V ⇒ IsUb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v)⌝
	THEN1 (REPEAT strip_tac THEN asm_fc_tac [] 
		THEN POP_ASM_T (strip_asm_tac o (rewrite_rule [get_spec ⌜IsLub⌝]))
		THEN asm_rewrite_tac[]));
a (fc_tac [pws_isub_lemma]);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜PwS⌝]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 3 ⌜x'⌝);
a (fc_tac [get_spec ⌜IsLub⌝]);
a (spec_nth_asm_tac 2 ⌜x x'⌝);
a (GET_ASM_T ⌜IsUb (PwS V r) G x⌝ ante_tac
	THEN rewrite_tac [get_spec ⌜PwS⌝]);
a (swap_nth_asm_concl_tac 1);
a (DROP_NTH_ASM_T 7 ante_tac
	THEN rewrite_tac [get_spec ⌜PwS⌝, get_spec ⌜IsUb⌝]
	THEN REPEAT strip_tac);
a (all_asm_fc_tac[]);
a (asm_rewrite_tac[]);
val pws_islub_lemma = pop_thm ();

set_goal([], ⌜∀V r G f⦁ IsLub (PwS V r) G f
	⇒ (∀ v⦁ v ∈ V ⇒ IsLub r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜IsLub⌝, pws_isub_lemma3, get_spec ⌜PwS⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜∃h⦁ ∀z⦁ h z = if z = v then x else f z⌝
	THEN1 prove_∃_tac);
a (spec_nth_asm_tac 4 ⌜h⌝);
(* *** Goal "2.1" *** *)
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac[get_spec ⌜IsUb⌝]
		THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
a (var_elim_nth_asm_tac 1);
a (cond_cases_tac ⌜v' = v⌝);
(* *** Goal "2.1.1" *** *)
a (var_elim_nth_asm_tac 1);
a (DROP_NTH_ASM_T 4 (asm_tac o (rewrite_rule [get_spec ⌜IsUb⌝])));
a (spec_nth_asm_tac 1 ⌜g v⌝);
a (spec_nth_asm_tac 1 ⌜g⌝);
(* *** Goal "2.1.2" *** *)
a (all_asm_fc_tac[]);
a (DROP_NTH_ASM_T 2 (asm_tac o (rewrite_rule [get_spec ⌜IsUb⌝])));
a (spec_nth_asm_tac 1 ⌜g v'⌝);
a (spec_nth_asm_tac 1 ⌜g⌝);
(* *** Goal "2.2" *** *)
a (spec_nth_asm_tac 1 ⌜v⌝);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
val pws_islub_lemma2 = pop_thm ();

set_goal([], ⌜∀V r G f⦁ IsLub (PwS V r) G f
	⇔ (∀ v⦁ v ∈ V ⇒ IsLub r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))⌝);
a (REPEAT_N 7 strip_tac THEN asm_fc_tac [pws_islub_lemma, pws_islub_lemma2]);
val pws_islub_lemma3 = pop_thm ();

set_goal([], ⌜∀V r G f⦁ (∀ v⦁ v ∈ V ⇒ IsGlb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))
	⇒ IsGlb (PwS V r) G f⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜IsGlb⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜∀ v⦁ v ∈ V ⇒ IsLb r {w|∃ g⦁ g ∈ G ∧ w = g v} (f v)⌝
	THEN1 (REPEAT strip_tac THEN asm_fc_tac [] 
		THEN POP_ASM_T (strip_asm_tac o (rewrite_rule [get_spec ⌜IsGlb⌝]))
		THEN asm_rewrite_tac[]));
a (fc_tac [pws_islb_lemma]);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜PwS⌝]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 3 ⌜x'⌝);
a (fc_tac [get_spec ⌜IsGlb⌝]);
a (spec_nth_asm_tac 2 ⌜x x'⌝);
a (GET_ASM_T ⌜IsLb (PwS V r) G x⌝ ante_tac
	THEN rewrite_tac [get_spec ⌜PwS⌝]);
a (swap_nth_asm_concl_tac 1);
a (DROP_NTH_ASM_T 7 ante_tac
	THEN rewrite_tac [get_spec ⌜PwS⌝, get_spec ⌜IsLb⌝]
	THEN REPEAT strip_tac);
a (all_asm_fc_tac[]);
a (asm_rewrite_tac[]);
val pws_isglb_lemma = pop_thm ();

set_goal([], ⌜∀V r G f⦁ IsGlb (PwS V r) G f
	⇒ (∀ v⦁ v ∈ V ⇒ IsGlb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜IsGlb⌝, pws_islb_lemma3, get_spec ⌜PwS⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜∃h⦁ ∀z⦁ h z = if z = v then x else f z⌝
	THEN1 prove_∃_tac);
a (spec_nth_asm_tac 4 ⌜h⌝);
(* *** Goal "2.1" *** *)
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac[get_spec ⌜IsLb⌝]
		THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
a (var_elim_nth_asm_tac 1);
a (cond_cases_tac ⌜v' = v⌝);
(* *** Goal "2.1.1" *** *)
a (var_elim_nth_asm_tac 1);
a (DROP_NTH_ASM_T 4 (asm_tac o (rewrite_rule [get_spec ⌜IsLb⌝])));
a (spec_nth_asm_tac 1 ⌜g v⌝);
a (spec_nth_asm_tac 1 ⌜g⌝);
(* *** Goal "2.1.2" *** *)
a (all_asm_fc_tac[]);
a (DROP_NTH_ASM_T 2 (asm_tac o (rewrite_rule [get_spec ⌜IsLb⌝])));
a (spec_nth_asm_tac 1 ⌜g v'⌝);
a (spec_nth_asm_tac 1 ⌜g⌝);
(* *** Goal "2.2" *** *)
a (spec_nth_asm_tac 1 ⌜v⌝);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
val pws_isglb_lemma2 = pop_thm ();

set_goal([], ⌜∀V r G f⦁ IsGlb (PwS V r) G f
	⇔ (∀ v⦁ v ∈ V ⇒ IsGlb r {w | ∃g⦁ g ∈ G ∧ w = g v} (f v))⌝);
a (REPEAT_N 7 strip_tac THEN asm_fc_tac [pws_isglb_lemma, pws_isglb_lemma2]);
val pws_isglb_lemma3 = pop_thm ();

(* set_merge_pcs ["misc11", "'GS1", "'misc2"]; *)
set_merge_pcs ["rbjmisc1", "'misc1"];

set_goal([], ⌜∀V r⦁ LubsExist r ⇒ LubsExist (PwS V r)⌝);
a (rewrite_tac [get_spec ⌜LubsExist⌝] THEN REPEAT strip_tac);
a (lemma_tac ⌜∃f⦁ ∀v⦁ v ∈ V ⇒ IsLub r {w|∃ g⦁ g ∈ s ∧ w = g v} (f v)⌝
	THEN1 prove_∃_tac);
(* *** Goal "1" *** *)
a (strip_tac);
a (spec_nth_asm_tac 1 ⌜{w|∃ g⦁ g ∈ s ∧ w = g v'}⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [pws_islub_lemma]);
a (∃_tac ⌜f⌝ THEN asm_rewrite_tac[]);
val pws_lubs_exist_thm = save_pop_thm "pws_lubs_exist_thm";

set_goal([], ⌜∀V r⦁ GlbsExist r ⇒ GlbsExist (PwS V r)⌝);
a (rewrite_tac [get_spec ⌜GlbsExist⌝] THEN REPEAT strip_tac);
a (lemma_tac ⌜∃f⦁ ∀v⦁ v ∈ V ⇒ IsGlb r {w|∃ g⦁ g ∈ s ∧ w = g v} (f v)⌝
	THEN1 prove_∃_tac);
(* *** Goal "1" *** *)
a (strip_tac);
a (spec_nth_asm_tac 1 ⌜{w|∃ g⦁ g ∈ s ∧ w = g v'}⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [pws_isglb_lemma]);
a (∃_tac ⌜f⌝ THEN asm_rewrite_tac[]);
val pws_glbs_exist_thm = save_pop_thm "pws_glbs_exist_thm";
=TEX
}%ignore


\subsection{Products}

We also need the following ordering over products.

ⓈHOLCONST
│ ⦏PrO⦎ : ('a → 'a → BOOL) → ('b → 'b → BOOL) → (('a × 'b) → ('a × 'b) → BOOL)
├───────────
│ ∀ ra rb⦁ PrO ra rb = λl r⦁ ra (Fst l) (Fst r) ∧ rb (Snd l) (Snd r)
■

=GFT
⦏pro_isub_lemma⦎ =
   ⊢ ∀ ra rb s lub rub
     ⦁ IsUb ra {w|∃ g⦁ g ∈ s ∧ w = Fst g} lub
           ∧ IsUb rb {w|∃ g⦁ g ∈ s ∧ w = Snd g} rub
         ⇔ IsUb (PrO ra rb) s (lub, rub)

⦏pro_islb_lemma⦎ =
   ⊢ ∀ ra rb s llb rlb
     ⦁ IsLb ra {w|∃ g⦁ g ∈ s ∧ w = Fst g} llb
           ∧ IsLb rb {w|∃ g⦁ g ∈ s ∧ w = Snd g} rlb
         ⇔ IsLb (PrO ra rb) s (llb, rlb)

⦏pro_islub_lemma⦎ =
   ⊢ ∀ ra rb s llub rlub
     ⦁ IsLub ra {w|∃ g⦁ g ∈ s ∧ w = Fst g} llub
           ∧ IsLub rb {w|∃ g⦁ g ∈ s ∧ w = Snd g} rlub
         ⇒ IsLub (PrO ra rb) s (llub, rlub)

⦏pro_isglb_lemma⦎ =
   ⊢ ∀ ra rb s lglb rglb
     ⦁ IsGlb ra {w|∃ g⦁ g ∈ s ∧ w = Fst g} lglb
           ∧ IsGlb rb {w|∃ g⦁ g ∈ s ∧ w = Snd g} rglb
         ⇒ IsGlb (PrO ra rb) s (lglb, rglb)

⦏pro_refl_lemma⦎ =
   ⊢ ∀ ra rb
     ⦁ Refl (Universe, ra) ∧ Refl (Universe, rb) ⇒ Refl (Universe, PrO ra rb)

⦏pro_partialorder_lemma⦎ =
   ⊢ ∀ ra rb
     ⦁ PartialOrder (Universe, ra) ∧ PartialOrder (Universe, rb)
         ⇒ PartialOrder (Universe, PrO ra rb)

⦏pro_rpo_lemma⦎ =
   ⊢ ∀ ra rb
     ⦁ Rpo (Universe, ra) ∧ Rpo (Universe, rb) ⇒ Rpo (Universe, PrO ra rb)

⦏pro_lubs_exist_thm⦎ =
   ⊢ ∀ ra rb⦁ LubsExist ra ∧ LubsExist rb ⇒ LubsExist (PrO ra rb)

⦏pro_glbs_exist_thm⦎ =
   ⊢ ∀ ra rb⦁ GlbsExist ra ∧ GlbsExist rb ⇒ GlbsExist (PrO ra rb)

⦏pro_crpou_thm⦎ =
   ⊢ ∀ ra rb⦁ CRpoU ra ∧ CRpoU rb ⇒ CRpoU (PrO ra rb)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ra rb s lub rub ⦁
	  IsUb ra {w | ∃g⦁ g ∈ s ∧ w = Fst g} lub
	∧ IsUb rb {w | ∃g⦁ g ∈ s ∧ w = Snd g} rub
	⇔ IsUb (PrO ra rb) s (lub, rub)⌝);
a (rewrite_tac [get_spec ⌜IsUb⌝, get_spec ⌜PrO⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (list_spec_nth_asm_tac 3 [⌜Fst x⌝]);
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "2" *** *)
a (list_spec_nth_asm_tac 2 [⌜Snd x⌝]);
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "3" *** *)
a (asm_fc_tac [] THEN asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (asm_fc_tac [] THEN asm_rewrite_tac[]);
val pro_isub_lemma = pop_thm ();

set_goal([], ⌜∀ra rb s llb rlb⦁
	  IsLb ra {w | ∃g⦁ g ∈ s ∧ w = Fst g} llb
	∧ IsLb rb {w | ∃g⦁ g ∈ s ∧ w = Snd g} rlb
	⇔ IsLb (PrO ra rb) s (llb, rlb)⌝);
a (rewrite_tac [get_spec ⌜IsLb⌝, get_spec ⌜PrO⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (list_spec_nth_asm_tac 3 [⌜Fst x⌝]);
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "2" *** *)
a (list_spec_nth_asm_tac 2 [⌜Snd x⌝]);
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "3" *** *)
a (asm_fc_tac [] THEN asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (asm_fc_tac [] THEN asm_rewrite_tac[]);
val pro_islb_lemma = pop_thm ();

set_goal([], ⌜∀ra rb s llub rlub ⦁
	  IsLub ra {w | ∃g⦁ g ∈ s ∧ w = Fst g} llub
	∧ IsLub rb {w | ∃g⦁ g ∈ s ∧ w = Snd g} rlub
	⇒ IsLub (PrO ra rb) s (llub, rlub)⌝);
a (rewrite_tac [get_spec ⌜IsLub⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [pro_isub_lemma]);
(* *** Goal "2" *** *)
a (strip_asm_tac (rewrite_rule [] (list_∀_elim [⌜ra⌝, ⌜rb⌝, ⌜s⌝, ⌜Fst x⌝, ⌜Snd x⌝]
	(map_eq_sym_rule pro_isub_lemma))));
a (rewrite_tac [get_spec ⌜PrO⌝]);
a (all_asm_fc_tac[] THEN contr_tac);
val pro_islub_lemma = pop_thm ();

set_goal([], ⌜∀ra rb s lglb rglb ⦁
	  IsGlb ra {w | ∃g⦁ g ∈ s ∧ w = Fst g} lglb
	∧ IsGlb rb {w | ∃g⦁ g ∈ s ∧ w = Snd g} rglb
	⇒ IsGlb (PrO ra rb) s (lglb, rglb)⌝);
a (rewrite_tac [get_spec ⌜IsGlb⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [pro_islb_lemma]);
(* *** Goal "2" *** *)
a (strip_asm_tac (rewrite_rule [] (list_∀_elim [⌜ra⌝, ⌜rb⌝, ⌜s⌝, ⌜Fst x⌝, ⌜Snd x⌝]
	(map_eq_sym_rule pro_islb_lemma))));
a (rewrite_tac [get_spec ⌜PrO⌝]);
a (all_asm_fc_tac[] THEN contr_tac);
val pro_isglb_lemma = pop_thm ();

set_goal([], ⌜∀ra rb⦁ Refl (Universe, ra) ∧ Refl (Universe, rb) ⇒ Refl (Universe, (PrO ra rb))⌝);
a (rewrite_tac [get_spec ⌜Refl⌝, get_spec ⌜PrO⌝]
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
val pro_refl_lemma = save_pop_thm "pro_refl_lemma";

set_goal([], ⌜∀ra rb⦁ PartialOrder (Universe, ra) ∧ PartialOrder (Universe, rb)
	⇒ PartialOrder (Universe, (PrO ra rb))⌝);
a (rewrite_tac [get_spec ⌜PartialOrder⌝, get_spec ⌜PrO⌝, get_spec ⌜Antisym⌝, get_spec ⌜Trans⌝]
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (contr_tac THEN all_asm_fc_tac[]);
a (rename_tac[]);
a (lemma_tac ⌜¬ (Fst x = Fst y ∧ Snd x = Snd y)⌝
	THEN1 contr_tac);
a (DROP_NTH_ASM_T 11 ante_tac THEN pure_once_asm_rewrite_tac [prove_rule [] ⌜∀x⦁ x = (Fst x, Snd x)⌝]); 
a (asm_rewrite_tac []); 
(* *** Goal "1.2" *** *)
a (asm_fc_tac[]);
(* *** Goal "1.3" *** *)
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "3" *** *)
a (all_asm_fc_tac[]);
val pro_partialorder_lemma = save_pop_thm "pro_partialorder_lemma";

set_goal([], ⌜∀ra rb⦁ Rpo (Universe, ra) ∧ Rpo (Universe, rb) ⇒ Rpo (Universe, (PrO ra rb))⌝);
a (rewrite_tac [get_spec ⌜Rpo⌝]
	THEN REPEAT strip_tac
	THEN all_fc_tac [pro_refl_lemma, pro_partialorder_lemma]);
val pro_rpo_lemma = save_pop_thm "pro_rpo_lemma";

set_goal([], ⌜∀ra rb⦁ LubsExist ra ∧ LubsExist rb ⇒ LubsExist (PrO ra rb)⌝);
a (rewrite_tac [get_spec ⌜LubsExist⌝] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜{w | ∃ g⦁ g ∈ s ∧ w = Fst g}⌝);
a (spec_nth_asm_tac 2 ⌜{w | ∃ g⦁ g ∈ s ∧ w = Snd g}⌝);
a (all_fc_tac [pro_islub_lemma]);
a (∃_tac ⌜(e, e')⌝ THEN asm_rewrite_tac[]);
val pro_lubs_exist_thm = save_pop_thm "pro_lubs_exist_thm";

set_goal([], ⌜∀ra rb⦁ GlbsExist ra ∧ GlbsExist rb ⇒ GlbsExist (PrO ra rb)⌝);
a (rewrite_tac [get_spec ⌜GlbsExist⌝] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜{w | ∃ g⦁ g ∈ s ∧ w = Fst g}⌝);
a (spec_nth_asm_tac 2 ⌜{w | ∃ g⦁ g ∈ s ∧ w = Snd g}⌝);
a (all_fc_tac [pro_isglb_lemma]);
a (∃_tac ⌜(e, e')⌝ THEN asm_rewrite_tac[]);
val pro_glbs_exist_thm = save_pop_thm "pro_glbs_exist_thm";

set_goal([], ⌜∀ra rb⦁ CRpoU ra ∧ CRpoU rb ⇒ CRpoU (PrO ra rb)⌝);
a (rewrite_tac [get_spec ⌜CRpoU⌝, get_spec ⌜RpoU⌝]
	THEN REPEAT strip_tac
	THEN all_fc_tac [pro_rpo_lemma, pro_glbs_exist_thm, pro_lubs_exist_thm]);
val pro_crpou_thm = save_pop_thm "pro_crpou_thm";
=TEX
}%ignore

\subsection{OPT}

ⓈHOLCONST
│ ⦏OptO⦎ : ('a → 'a → BOOL) → ('a OPT → 'a OPT → BOOL)
├───────────
│ ∀rl⦁ OptO rl = λl r⦁ l = Undefined
│		 ∨ IsDefined l ∧ IsDefined r ∧ rl (ValueOf l) (ValueOf r)
■

\subsection{Discrete Partial Orders}

The things I am calling discrete partial orders come with the ordering of a discrete lattice.

When these are used to construct indexed sets whose elements have some ordering then there will be another ordering which is derived from the ordering on the elements.
This is defined for use in defining orderings over indexed sets.

ⓈHOLCONST
│ ⦏DpoEO⦎ : ('a → 'a → BOOL) → ('a DPO → 'a DPO → BOOL)
├───────────
│ ∀rl⦁ DpoEO rl = λl r⦁ dpoUdef l ∨ dpoOdef r
│		∨ ∃le re⦁ rl le re ∧ l = dpoE le ∧ r = dpoE re
■

To get the discrete ordering apply this function to the equality relation.

=GFT
⦏is_isub_lemma⦎ =
   ⊢ ∀ r G d
     ⦁ IsUb r G d ⇒ IsUb (DpoEO r) {w|∃ v⦁ v ∈ G ∧ w = dpoE v} (dpoE d)

⦏is_islb_lemma⦎ =
   ⊢ ∀ r G d
     ⦁ IsLb r G d ⇒ IsLb (DpoEO r) {w|∃ v⦁ v ∈ G ∧ w = dpoE v} (dpoE d)

⦏is_isub_lemma2⦎ =
   ⊢ ∀ r G d
     ⦁ IsUb (DpoEO r) G d
         = (d = dpoT
           ∨ G ⊆ {dpoB} ∧ d = dpoB
           ∨ (∃ e⦁ d = dpoE e ∧ IsUb r {w|dpoE w ∈ G} e) ∧ ¬ dpoT ∈ G)

⦏is_islb_lemma2⦎ =
   ⊢ ∀ r G d
     ⦁ IsLb (DpoEO r) G d
         = (d = dpoB
           ∨ G ⊆ {dpoT} ∧ d = dpoT
           ∨ (∃ e⦁ d = dpoE e ∧ IsLb r {w|dpoE w ∈ G} e) ∧ ¬ dpoB ∈ G)

⦏is_islub_lemma⦎ =
   ⊢ ∀ r G d
     ⦁ IsLub (DpoEO r) G d
         = ((dpoT ∈ G ∨ (∃ w⦁ dpoE w ∈ G) ∧ ¬ (∃ e⦁ IsUb r {w|dpoE w ∈ G} e))
             ∧ d = dpoT
           ∨ G ⊆ {dpoB} ∧ d = dpoB
           ∨ ¬ G ⊆ {dpoB}
             ∧ (∃ e⦁ d = dpoE e ∧ IsLub r {w|dpoE w ∈ G} e)
             ∧ ¬ dpoT ∈ G)

⦏is_isglb_lemma⦎ =
   ⊢ ∀ r G d
     ⦁ IsGlb (DpoEO r) G d
         = ((dpoB ∈ G ∨ (∃ w⦁ dpoE w ∈ G) ∧ ¬ (∃ e⦁ IsLb r {w|dpoE w ∈ G} e))
             ∧ d = dpoB
           ∨ G ⊆ {dpoT} ∧ d = dpoT
           ∨ ¬ G ⊆ {dpoT}
             ∧ (∃ e⦁ d = dpoE e ∧ IsGlb r {w|dpoE w ∈ G} e)
             ∧ ¬ dpoB ∈ G)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r G d⦁ IsUb r G d
	⇒ IsUb (DpoEO r) {w | ∃v⦁ v ∈ G ∧ w = dpoE v} (dpoE d)⌝);
a (rewrite_tac [get_spec ⌜IsUb⌝, get_spec ⌜DpoEO⌝] THEN REPEAT strip_tac);
a (∃_tac ⌜v⌝ THEN ∃_tac ⌜d⌝ THEN all_asm_fc_tac [] THEN asm_rewrite_tac[]);
val dpoeo_isub_lemma = pop_thm ();

set_goal([], ⌜∀r G d⦁ IsLb r G d
	⇒ IsLb (DpoEO r) {w | ∃v⦁ v ∈ G ∧ w = dpoE v} (dpoE d)⌝);
a (rewrite_tac [get_spec ⌜IsLb⌝, get_spec ⌜DpoEO⌝] THEN REPEAT strip_tac);
a (∃_tac ⌜d⌝ THEN ∃_tac ⌜v⌝ THEN all_asm_fc_tac [] THEN asm_rewrite_tac[]);
val dpoeo_islb_lemma = pop_thm ();

(* set_merge_pcs ["misc1", "'GS1", "'misc2"]; *)
set_merge_pcs ["rbjmisc", "'misc1"];

set_goal([], ⌜∀r G d⦁ IsUb (DpoEO r) G d
	⇔ d = dpoT
		∨ G ⊆ {dpoB} ∧ d = dpoB
		∨ (∃e⦁ d = dpoE e ∧ IsUb r {w | dpoE w ∈ G} e) ∧ ¬ dpoT ∈ G⌝);
a (REPEAT ∀_tac);
a (strip_asm_tac (∀_elim ⌜d⌝ dpo_cases_thm)
	THEN_TRY asm_rewrite_tac[get_spec ⌜DpoEO⌝, get_spec ⌜IsUb⌝, get_spec ⌜dpoUdef⌝]);
(* *** Goal "1" *** *)
a (PC_T1 "hol1" prove_tac[]);
(* *** Goal "2" *** *)
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[get_spec ⌜IsUb⌝]
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (spec_nth_asm_tac 1 ⌜dpoT⌝);
(* *** Goal "2.3" *** *)
a (strip_asm_tac (∀_elim ⌜x⌝ dpo_cases_thm));
(* *** Goal "2.3.1" *** *)
a (var_elim_asm_tac ⌜x = dpoT⌝);
(* *** Goal "2.3.2" *** *)
a (∃_tac ⌜dpoV x⌝ THEN ∃_tac ⌜e⌝
	THEN asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 5 ante_tac
	THEN rewrite_tac[get_spec ⌜IsUb⌝]
	THEN strip_tac);
a (var_elim_asm_tac ⌜x = dpoE e''⌝
	THEN asm_fc_tac[]);
a (LEMMA_T ⌜e = e'⌝ (fn x => asm_rewrite_tac[x]));
a (var_elim_asm_tac ⌜d = dpoE e⌝);
val dpoeo_isub_lemma2 = pop_thm ();

set_goal([], ⌜∀r G d⦁ IsLb (DpoEO r) G d
	⇔ d = dpoB
		∨ G ⊆ {dpoT} ∧ d = dpoT
		∨ (∃e⦁ d = dpoE e ∧ IsLb r {w | dpoE w ∈ G} e) ∧ ¬ dpoB ∈ G⌝);
a (REPEAT ∀_tac);
a (strip_asm_tac (∀_elim ⌜d⌝ dpo_cases_thm)
	THEN_TRY asm_rewrite_tac[get_spec ⌜DpoEO⌝, get_spec ⌜IsLb⌝, get_spec ⌜dpoOdef⌝]);
(* *** Goal "1" *** *)
a (PC_T1 "hol1" prove_tac[]);
(* *** Goal "2" *** *)
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[get_spec ⌜IsLb⌝]
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]
	THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (spec_nth_asm_tac 1 ⌜dpoB⌝);
(* *** Goal "2.3" *** *)
a (strip_asm_tac (∀_elim ⌜x⌝ dpo_cases_thm));
(* *** Goal "2.3.1" *** *)
a (var_elim_asm_tac ⌜x = dpoB⌝);
(* *** Goal "2.3.2" *** *)
a (∃_tac ⌜e⌝ THEN ∃_tac ⌜dpoV x⌝
	THEN asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 5 ante_tac
	THEN rewrite_tac[get_spec ⌜IsLb⌝]
	THEN strip_tac);
a (var_elim_asm_tac ⌜x = dpoE e''⌝
	THEN asm_fc_tac[]);
a (LEMMA_T ⌜e = e'⌝ (fn x => asm_rewrite_tac[x]));
a (var_elim_asm_tac ⌜d = dpoE e⌝);
val dpoeo_islb_lemma2 = pop_thm ();

push_extend_pc "'mmp1";

set_goal([], ⌜∀r G d⦁ IsLub (DpoEO r) G d
	⇔ (dpoT ∈ G ∨ (∃w⦁ dpoE w ∈ G) ∧ ¬ (∃e⦁ IsUb r {w | dpoE w ∈ G} e)) ∧ d = dpoT
		∨ G ⊆ {dpoB} ∧ d = dpoB
		∨ ¬ G ⊆ {dpoB} ∧ (∃e⦁ d = dpoE e ∧ IsLub r {w | dpoE w ∈ G} e) ∧ ¬ dpoT ∈ G⌝);
a (REPEAT ∀_tac);
a (strip_asm_tac (∀_elim ⌜d⌝ dpo_cases_thm)
	THEN_TRY asm_rewrite_tac[get_spec ⌜IsLub⌝, dpoeo_isub_lemma2]);
(* *** Goal "1" *** *)
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac [get_spec ⌜DpoEO⌝]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac [get_spec ⌜DpoEO⌝]
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (spec_nth_asm_tac 2 ⌜dpoB⌝);
a (DROP_NTH_ASM_T 2 ante_tac THEN PC_T "hol1" (REPEAT strip_tac));
a (strip_asm_tac (∀_elim ⌜x⌝ dpo_cases_thm)
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1.1" *** *)
a (var_elim_asm_tac ⌜x = dpoT⌝);
(* *** Goal "2.1.2" *** *)
a (var_elim_asm_tac ⌜x = dpoE e⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (spec_nth_asm_tac 2 ⌜dpoE e⌝
	THEN spec_nth_asm_tac 1 ⌜e⌝);
(* *** Goal "2.3" *** *)
a (DROP_ASM_T ⌜G ⊆ {dpoB}⌝ ante_tac
	THEN PC_T "hol1" (REPEAT strip_tac)
	THEN asm_fc_tac[]);
(* *** Goal "2.4" *** *)
a (spec_nth_asm_tac 3 ⌜dpoV dpoT⌝);
a (POP_ASM_T ante_tac
	THEN rewrite_tac [get_spec ⌜IsUb⌝]
	THEN REPEAT strip_tac);
a (DROP_NTH_ASM_T 3 ante_tac
	THEN (PC_T "hol1" (REPEAT strip_tac))
	THEN asm_fc_tac[]);
(* *** Goal "2.5" *** *)
a (asm_fc_tac[]);
(* *** Goal "3" *** *)
a (asm_rewrite_tac [get_spec ⌜DpoEO⌝]
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "3.1" *** *)
a (spec_nth_asm_tac 1 ⌜dpoB⌝);
(* *** Goal "3.2" *** *)
a (var_elim_asm_tac ⌜d = dpoE e'⌝);
a (var_elim_asm_tac ⌜e' = e⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
a (asm_rewrite_tac [get_spec ⌜IsLub⌝]
	THEN REPEAT strip_tac);
a (fc_tac [get_spec ⌜IsUb⌝]);
(* *** Goal "3.2.1" *** *)
a (spec_nth_asm_tac 4 ⌜dpoE x⌝);
(* *** Goal "3.2.1.1" *** *)
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "3.2.1.2" *** *)
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "3.2.1.3" *** *)
a (all_var_elim_asm_tac);
(* *** Goal "3.2.2" *** *)
a (spec_nth_asm_tac 4 ⌜dpoE x⌝);
(* *** Goal "3.2.2.1" *** *)
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "3.2.2.2" *** *)
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "3.2.2.3" *** *)
a (all_var_elim_asm_tac);
(* *** Goal "3.3" *** *)
a (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[]);
a (fc_tac [get_spec ⌜IsLub⌝]);
(* *** Goal "3.4" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "3.5" *** *)
a (var_elim_asm_tac ⌜d = dpoE e'⌝);
a (var_elim_asm_tac ⌜e' = e⌝);
a (∃_tac ⌜e⌝ THEN ∃_tac ⌜e''⌝
	THEN asm_rewrite_tac[]);
a (fc_tac [get_spec ⌜IsLub⌝]);
a (all_asm_fc_tac[]);
val dpoeo_islub_lemma = pop_thm ();

set_goal([], ⌜∀r G d⦁ IsGlb (DpoEO r) G d
	⇔ (dpoB ∈ G ∨ (∃w⦁ dpoE w ∈ G) ∧ ¬ (∃e⦁ IsLb r {w | dpoE w ∈ G} e)) ∧ d = dpoB
		∨ G ⊆ {dpoT} ∧ d = dpoT
		∨ ¬ G ⊆ {dpoT} ∧ (∃e⦁ d = dpoE e ∧ IsGlb r {w | dpoE w ∈ G} e) ∧ ¬ dpoB ∈ G⌝);
a (REPEAT ∀_tac);
a (strip_asm_tac (∀_elim ⌜d⌝ dpo_cases_thm)
	THEN_TRY asm_rewrite_tac[get_spec ⌜IsGlb⌝, dpoeo_islb_lemma2]);
(* *** Goal "2" *** *)
set_labelled_goal "2";
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac [get_spec ⌜DpoEO⌝]);
(* *** Goal "1" *** *)
a (asm_rewrite_tac [get_spec ⌜DpoEO⌝]
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (spec_nth_asm_tac 2 ⌜dpoT⌝);
a (DROP_NTH_ASM_T 2 ante_tac THEN PC_T "hol1" (REPEAT strip_tac));
a (strip_asm_tac (∀_elim ⌜x⌝ dpo_cases_thm)
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1.1" *** *)
a (var_elim_asm_tac ⌜x = dpoB⌝);
(* *** Goal "2.1.2" *** *)
a (var_elim_asm_tac ⌜x = dpoE e⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (spec_nth_asm_tac 2 ⌜dpoE e⌝
	THEN spec_nth_asm_tac 1 ⌜e⌝);
(* *** Goal "2.3" *** *)
a (DROP_ASM_T ⌜G ⊆ {dpoT}⌝ ante_tac
	THEN PC_T "hol1" (REPEAT strip_tac)
	THEN asm_fc_tac[]);
(* *** Goal "2.4" *** *)
a (spec_nth_asm_tac 3 ⌜dpoV dpoB⌝);
a (POP_ASM_T ante_tac
	THEN rewrite_tac [get_spec ⌜IsLb⌝]
	THEN REPEAT strip_tac);
a (DROP_NTH_ASM_T 3 ante_tac
	THEN (PC_T "hol1" (REPEAT strip_tac))
	THEN asm_fc_tac[]);
(* *** Goal "2.5" *** *)
a (asm_fc_tac[]);
(* *** Goal "3" *** *)
a (asm_rewrite_tac [get_spec ⌜DpoEO⌝]
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "3.1" *** *)
a (spec_nth_asm_tac 1 ⌜dpoT⌝);
(* *** Goal "3.2" *** *)
a (var_elim_asm_tac ⌜d = dpoE e'⌝);
a (var_elim_asm_tac ⌜e' = e⌝);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
a (asm_rewrite_tac [get_spec ⌜IsGlb⌝]
	THEN REPEAT strip_tac);
a (fc_tac [get_spec ⌜IsLb⌝]);
(* *** Goal "3.2.1" *** *)
a (spec_nth_asm_tac 4 ⌜dpoE x⌝);
(* *** Goal "3.2.1.1" *** *)
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "3.2.1.2" *** *)
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "3.2.1.3" *** *)
a (all_var_elim_asm_tac);
(* *** Goal "3.2.2" *** *)
a (spec_nth_asm_tac 4 ⌜dpoE x⌝);
(* *** Goal "3.2.2.1" *** *)
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "3.2.2.2" *** *)
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "3.2.2.3" *** *)
a (all_var_elim_asm_tac);
(* *** Goal "3.3" *** *)
a (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[]);
a (fc_tac [get_spec ⌜IsGlb⌝]);
(* *** Goal "3.4" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "3.5" *** *)
a (var_elim_asm_tac ⌜d = dpoE e'⌝);
a (var_elim_asm_tac ⌜e' = e⌝);
a (∃_tac ⌜e''⌝ THEN ∃_tac ⌜e⌝
	THEN asm_rewrite_tac[]);
a (fc_tac [get_spec ⌜IsGlb⌝]);
a (all_asm_fc_tac[]);
val dpoeo_isglb_lemma = pop_thm ();

set_goal([], ⌜∀r⦁ LubsExist r ⇒ LubsExist (DpoEO r)⌝);
a (rewrite_tac [get_spec ⌜LubsExist⌝, dpoeo_islub_lemma] THEN REPEAT strip_tac);
a (∃_tac ⌜
	if dpoT ∈ s
	then dpoT
	else
		if s ⊆ {dpoB}
		then dpoB
		else dpoE (Lub r {y | dpoE y ∈ s})⌝);
a (cases_tac ⌜dpoT ∈ s⌝ THEN_TRY asm_rewrite_tac[]);
a (cases_tac ⌜s ⊆ {dpoB}⌝ THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜Lub r {y|dpoE y ∈ s}⌝ THEN asm_rewrite_tac []);
a (spec_nth_asm_tac 3 ⌜{w|dpoE w ∈ s}⌝);
a (all_fc_tac[lub_lub_lemma]);
val dpoeo_lubs_exist_thm = save_pop_thm "dpoeo_lubs_exist_thm";

set_goal([], ⌜∀r⦁ GlbsExist r ⇒ GlbsExist (DpoEO r)⌝);
a (rewrite_tac [get_spec ⌜GlbsExist⌝, dpoeo_isglb_lemma] THEN REPEAT strip_tac);
a (∃_tac ⌜
	if dpoB ∈ s
	then dpoB
	else
		if s ⊆ {dpoT}
		then dpoT
		else dpoE (Glb r {y | dpoE y ∈ s})⌝);
a (cases_tac ⌜dpoB ∈ s⌝ THEN_TRY asm_rewrite_tac[]);
a (cases_tac ⌜s ⊆ {dpoT}⌝ THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜Glb r {y|dpoE y ∈ s}⌝ THEN asm_rewrite_tac []);
a (spec_nth_asm_tac 3 ⌜{w | dpoE w ∈ s}⌝);
a (all_fc_tac[glb_glb_lemma]);
val dpoeo_glbs_exist_thm = save_pop_thm "dpoeo_glbs_exist_thm";

pop_pc ();

=TEX
}%ignore

=GFT
⦏≤⋎t⋎4_trich_lub_ft_lemma⦎ =
   ⊢ ∀ X z⦁ Trich (X, $≤⋎t⋎4) ∧ fT ≤⋎t⋎4 Lub $≤⋎t⋎4 X ⇒ fT ∈ X


=TEX

\ignore{
=SML
set_goal([], ⌜∀X z⦁ Trich (X, $≤⋎t⋎4) ∧ fT ≤⋎t⋎4 (Lub $≤⋎t⋎4 X) ⇒ fT ∈ X⌝);
a (REPEAT strip_tac THEN REPEAT_N 1 (POP_ASM_T ante_tac));
a (fc_tac [rewrite_rule [get_spec ⌜LinearOrder⌝] (∀_elim ⌜X⌝ ≤⋎t⋎4_lin_cases_lemma)]
	THEN asm_rewrite_tac[]
	THEN contr_tac
	THEN asm_fc_tac[]);
val ≤⋎t⋎4_trich_lub_ft_lemma = save_pop_thm "≤⋎t⋎4_trich_lub_ft_lemma";
=TEX
}%ignore

\subsection{Indexed Sets}

\subsubsection{IX}

The following function lifts an ordering on the elements of the codomain to an ordering on the indexed sets.

ⓈHOLCONST
│ ⦏IxO⦎ : ('b → 'b → BOOL) → (('a, 'b) IX → ('a, 'b) IX → BOOL)
├───────────
│ ∀r⦁ IxO r = Pw (OptO r)
■

It may be more convenient in some cases to use the following ordering in which the comparison is restricted to some subdomain.

(I should have used domain restriction here.)

ⓈHOLCONST
│ ⦏IxO2⦎ : ('a, 'b) IX SET × ('b → 'b → BOOL) → (('a, 'b) IX → ('a, 'b) IX → BOOL)
├───────────
│ ∀d r⦁ IxO2 (d, r) = λx y⦁
│		if x ∈ d ∧ y ∈ d
│		then IxDom x = IxDom y ∧ IxO r x y
│		else x = y
■

\subsection{A Pre-order on Sets}

The following pre-order on sets based on a pre-order of the elements is used later with sets of truth values.

ⓈHOLCONST
│ ⦏SetO⦎ : ('a → 'a → BOOL) → ('a SET) → ('a SET) → BOOL
├───────────
│ ∀ r⦁ SetO r = λm n⦁
│		(∀x⦁ x ∈ m ⇒ ∃y⦁ y ∈ n ∧ r x y)
│	∧	(∀y⦁ y ∈ n ⇒ ∃x⦁ x ∈ m ∧ r x y)
■

That turns out to be stronger than we need, this one simplifies matters.

ⓈHOLCONST
│ ⦏SetO2⦎ : ('a → 'a → BOOL) → ('a SET) → ('a SET) → BOOL
├───────────
│ ∀ r⦁ SetO2 r = λm n⦁ ∀x⦁ x ∈ m ⇒ ∃y⦁ r x y ∧ y ∈ n
■

=GFT
⦏trans_seto_lemma⦎ =
	⊢ ∀ r⦁ Trans (Universe, r) ⇒ Trans (Universe, SetO r)

⦏trans_seto2_lemma⦎ =
   ⊢ ∀ r⦁ Trans (Universe, r) ⇒ Trans (Universe, SetO2 r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ Trans (Universe, r) ⇒ Trans (Universe, SetO r)⌝);
a (rewrite_tac [get_spec ⌜Trans⌝, get_spec ⌜SetO⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_asm_fc_tac[]);
a (all_asm_fc_tac[]);
a (all_asm_fc_tac[]);
a (∃_tac ⌜y''⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_asm_fc_tac[]);
a (all_asm_fc_tac[]);
a (all_asm_fc_tac[]);
a (∃_tac ⌜x''⌝ THEN asm_rewrite_tac[]);
val trans_seto_lemma = pop_thm ();

set_goal([], ⌜∀r⦁ Trans (Universe, r) ⇒ Trans (Universe, SetO2 r)⌝);
a (rewrite_tac [get_spec ⌜Trans⌝, get_spec ⌜SetO2⌝] THEN REPEAT strip_tac);
a (all_asm_fc_tac[]);
a (all_asm_fc_tac[]);
a (all_asm_fc_tac[]);
a (∃_tac ⌜y''⌝ THEN asm_rewrite_tac[]);
val trans_seto2_lemma = pop_thm ();
=TEX
}%ignore

=GFT
=TEX

\ignore{
=IGN
set_goal ([], ⌜∀V⦁ Increasing (SetO2 $≤⋎t⋎4) $⇒ (λs⦁ ¬ s ∈ CompFTV)⌝);
a (strip_tac);
a (PC_T1 "hol" rewrite_tac [get_spec ⌜Increasing⌝, get_spec ⌜SetO2⌝, CompFTV_Lub_lemma]);
	THEN REPEAT strip_tac); 
=TEX
}%ignore



\subsection{A Pre-order for Sets of Functions}

To get a pre-order over sets of functions from an pre-order of the codomain of the functions, we could apply {\it Pw} and then {\it SetO}, however the following construction proves more useful.

[Though I don't appear to have used it!]

ⓈHOLCONST
│ ⦏FunSetO⦎ : ('a → 'a → BOOL) → ('b → 'a) SET → ('b → 'a) SET → BOOL
├───────────
│ ∀ r:('a → 'a → BOOL)⦁ FunSetO r =
│	λs t⦁ Pw (SetO r) (λx⦁ {v | ∃y⦁ y ∈ s ∧ v = y x}) (λx⦁ {v | ∃y⦁ y ∈ t ∧ v = y x})
■

=IGN
⦏trans_funseto_lemma⦎ =
	∀ r⦁ Trans (Universe, r) ⇒ Trans (Universe, FunSetO r)
=TEX

\ignore{
=IGN
set_goal([], ⌜∀r⦁ Trans (Universe, r) ⇒ Trans (Universe, FunSetO r)⌝);
a (rewrite_tac [get_spec ⌜FunSetO⌝] THEN REPEAT strip_tac);
a (fc_tac [trans_seto_lemma]);
a (fc_tac [trans_seto_lemma]);
 THEN POP_ASM_T ante_tac
	THEN rewrite_tac [get_spec ⌜Trans⌝]);
	THEN REPEAT strip_tac
	THEN all_asm_ufc_tac[]
	THEN asm_rewrite_tac[]);
val trans_funseto_lemma = pop_thm ();
=TEX
}%ignore

\section{MISCELLANEOUS THEOREMS}

\subsection{Monotonicity of Lub}

=GFT
⦏lub_increasing_lemma⦎ =
	⊢ ∀ r⦁ RpoU r ∧ LubsExist r ⇒ Increasing (SetO r) r (Lub r)

⦏lub_increasing2_lemma⦎ =
	⊢ ∀ r⦁ RpoU r ∧ LubsExist r ⇒ Increasing (SetO2 r) r (Lub r)

⦏lub_increasing_lemma2⦎ =
	⊢ ∀ r⦁ CRpoU r ⇒ Increasing (SetO r) r (Lub r)

⦏lub_increasing2_lemma2⦎ =
	⊢ ∀ r⦁ CRpoU r ⇒ Increasing (SetO2 r) r (Lub r)

⦏lub_increasing_lemma3⦎ =
	⊢ ∀ r⦁ CRpoU r ⇒ (∀ x y⦁ SetO r x y ⇒ r (Lub r x) (Lub r y))

⦏lub_increasing2_lemma3⦎ =
   ⊢ ∀ r⦁ CRpoU r ⇒ (∀ x y⦁ SetO2 r x y ⇒ r (Lub r x) (Lub r y))
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ RpoU r ∧ LubsExist r ⇒ Increasing (SetO r) r (Lub r)⌝);
a (rewrite_tac (map get_spec [⌜Increasing⌝])
	THEN REPEAT strip_tac);
a (fc_tac [lub_lub_lemma2]);
a (spec_nth_asm_tac 1 ⌜x⌝
	THEN spec_nth_asm_tac 2 ⌜y⌝
	THEN fc_tac [get_spec ⌜IsLub⌝]);
a (rename_tac[]);
a (lemma_tac ⌜IsUb r x (Lub r y)⌝);
(* *** Goal "1" *** *)
a (DROP_ASM_T ⌜SetO r x y⌝ ante_tac THEN rewrite_tac [get_spec ⌜SetO⌝]
	THEN strip_tac);
a (rewrite_tac [get_spec ⌜IsUb⌝] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
a (GET_NTH_ASM_T 8 ante_tac THEN rewrite_tac [get_spec ⌜IsUb⌝] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
a (fc_tac [rpou_fc_clauses2] THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (asm_fc_tac[]);
val lub_increasing_lemma = save_pop_thm "lub_increasing_lemma";

set_goal([], ⌜∀r⦁ RpoU r ∧ LubsExist r ⇒ Increasing (SetO2 r) r (Lub r)⌝);
a (rewrite_tac (map get_spec [⌜Increasing⌝])
	THEN REPEAT strip_tac);
a (fc_tac [lub_lub_lemma2]);
a (spec_nth_asm_tac 1 ⌜x⌝
	THEN spec_nth_asm_tac 2 ⌜y⌝
	THEN fc_tac [get_spec ⌜IsLub⌝]);
a (lemma_tac ⌜IsUb r x (Lub r y)⌝);
(* *** Goal "1" *** *)
a (DROP_ASM_T ⌜SetO2 r x y⌝ ante_tac THEN rewrite_tac [get_spec ⌜SetO2⌝]
	THEN strip_tac);
a (rewrite_tac [get_spec ⌜IsUb⌝] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
a (GET_NTH_ASM_T 7 ante_tac THEN rewrite_tac [get_spec ⌜IsUb⌝] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
a (fc_tac [rpou_fc_clauses2] THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (asm_fc_tac[]);
val lub_increasing2_lemma = save_pop_thm "lub_increasing2_lemma";

set_goal([], ⌜∀ r⦁ CRpoU r ⇒ Increasing (SetO r) r (Lub r)⌝);
a (rewrite_tac [get_spec ⌜CRpoU⌝, get_spec ⌜RpoU⌝]
	THEN REPEAT strip_tac);
a (all_fc_tac [rewrite_rule [get_spec ⌜RpoU⌝] lub_increasing_lemma]);
val lub_increasing_lemma2 = save_pop_thm "lub_increasing_lemma2";

set_goal([], ⌜∀ r⦁ CRpoU r ⇒ Increasing (SetO2 r) r (Lub r)⌝);
a (rewrite_tac [get_spec ⌜CRpoU⌝, get_spec ⌜RpoU⌝]
	THEN REPEAT strip_tac);
a (all_fc_tac [rewrite_rule [get_spec ⌜RpoU⌝] lub_increasing2_lemma]);
val lub_increasing2_lemma2 = save_pop_thm "lub_increasing2_lemma2";

val lub_increasing_lemma3 = save_thm("lub_increasing_lemma3",
	rewrite_rule [get_spec⌜Increasing⌝] lub_increasing_lemma2);

val lub_increasing2_lemma3 = save_thm("lub_increasing2_lemma3",
	rewrite_rule [get_spec⌜Increasing⌝] lub_increasing2_lemma2);
=TEX
}%ignore

\subsection{Product of Functions}

We now define the product of two functions:

ⓈHOLCONST
│ ⦏FunProd⦎ : ('a → 'b) → ('a → 'c) → ('a → 'b × 'c)
├───────────
│ ∀ f g⦁ FunProd f g = λx⦁ (f x, g x)
■

And prove that the product of two increasing functions is increasing.

=GFT
⦏funprod_increasing_thm⦎ =
   ⊢ ∀ f g ra rb rc
     ⦁ Increasing ra rb f ∧ Increasing ra rc g
         ⇒ Increasing ra (PrO rb rc) (FunProd f g)
=TEX

\ignore{
=SML
set_goal([], ⌜∀f g ra rb rc⦁ Increasing ra rb f ∧ Increasing ra rc g
	⇒ Increasing ra (PrO rb rc) (FunProd f g)⌝);
a (rewrite_tac [get_spec ⌜Increasing⌝, get_spec ⌜PrO⌝, get_spec ⌜FunProd⌝]
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
val funprod_increasing_thm = save_pop_thm "funprod_increasing_thm";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏FunLeft⦎ : ('a × 'c → 'b) → ('a × 'c → 'b × 'c)
├───────────
│ ∀ f⦁ FunLeft f = λx⦁ (f x, Snd x)
■

ⓈHOLCONST
│ ⦏FunRight⦎ : ('c × 'a → 'b) → ('c × 'a → 'c × 'b)
├───────────
│ ∀ f⦁ FunRight f = λx⦁ (Fst x, f x)
■

=GFT
⦏funleft_increasing_thm⦎ =
   ⊢ ∀ f ra rb rc
     ⦁ Increasing (PrO ra rc) rb f
         ⇒ Increasing (PrO ra rc) (PrO rb rc) (FunLeft f)

⦏funright_increasing_thm⦎ =
   ⊢ ∀ f ra rb rc
     ⦁ Increasing (PrO rc ra) rb f
         ⇒ Increasing (PrO rc ra) (PrO rc rb) (FunRight f)
=TEX

\ignore{
=SML
set_goal([], ⌜∀f ra rb rc⦁ Increasing (PrO ra rc) rb f
	⇒ Increasing (PrO ra rc) (PrO rb rc) (FunLeft f)⌝);
a (rewrite_tac [get_spec ⌜Increasing⌝, get_spec ⌜PrO⌝, get_spec ⌜FunLeft⌝]
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
val funleft_increasing_thm = save_pop_thm "funleft_increasing_thm";

set_goal([], ⌜∀f ra rb rc⦁ Increasing (PrO rc ra) rb f
	⇒ Increasing (PrO rc ra) (PrO rc rb) (FunRight f)⌝);
a (rewrite_tac [get_spec ⌜Increasing⌝, get_spec ⌜PrO⌝, get_spec ⌜FunRight⌝]
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
val funright_increasing_thm = save_pop_thm "funright_increasing_thm";

set_flag("subgoal_package_quiet", false);
=TEX
}%ignore

\subsection{FunImage Preserves Linearity}

The function must be a morphism and the target set must be a partial order (these are sufficient conditions).

=GFT
⦏trich_funimage_lemma⦎ =
   ⊢ ∀ r1 r2 f X⦁ Increasing r1 r2 f ⇒ Trich (X, r1) ⇒ Trich (FunImage f X, r2)

⦏linear_funimage_thm⦎ =
   ⊢ ∀ r1 r2 f X⦁ Increasing r1 r2 f
           ∧ LinearOrder (X, r1)
           ∧ PartialOrder (FunImage f X, r2)
         ⇒ LinearOrder (FunImage f X, r2)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r1 r2 f X⦁ Increasing r1 r2 f ⇒ Trich (X, r1) ⇒ Trich (FunImage f X, r2)⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜Increasing⌝, get_spec ⌜Trich⌝, get_spec ⌜FunImage⌝]
	THEN contr_tac);
a (DROP_NTH_ASM_T 4 (asm_tac o eq_sym_rule));
a (var_elim_nth_asm_tac 1);
a (DROP_NTH_ASM_T 5 (asm_tac o eq_sym_rule));
a (var_elim_nth_asm_tac 1);
a (list_spec_nth_asm_tac 7 [⌜a⌝,⌜a'⌝]);
a (list_spec_nth_asm_tac 8 [⌜a'⌝,⌜a⌝]);
a (list_spec_nth_asm_tac 8 [⌜a⌝,⌜a'⌝]);
a (var_elim_asm_tac ⌜a = a'⌝);
val trich_funimage_lemma = pop_thm ();

set_goal([], ⌜∀r1 r2 f X⦁ Increasing r1 r2 f ∧ LinearOrder (X, r1) ∧ PartialOrder (FunImage f X, r2)
			⇒ LinearOrder (FunImage f X, r2)⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜LinearOrder⌝, get_spec ⌜PartialOrder⌝]
	THEN contr_tac);
a (all_fc_tac [trich_funimage_lemma]);
val linear_funimage_thm = save_pop_thm "linear_funimage_thm";
=TEX
}%ignore

\section{GENERALISED RELATIONS}

=SML
declare_type_abbrev (⦏"BR"⦎, ["'a", "'b"], ⓣ'a → 'a → 'b⌝);
declare_infix (300, ⦏"≤⋎∈"⦎);
=TEX

\subsection{Partial Relations}

One way to represent a partial relation is to use more than one truth value.
Alternatively you can have two relations, one for the true values and one for the false ones.

In the latter case you might have an inconsistency, a pair might appear in both.
This `defect' is also present if you chose the former representation using four truth values as in a discrete partial ordering of the type BOOL.

We might as well have a type abbreviation for the partial (equivalence) relations.

=SML
declare_infix (300, "=⋎p");
declare_infix (300, "=⋎q");
declare_infix (300, "=⋎r");
=TEX

It will be convenient perhaps to be able to switch between having a single four valued relation and having two boolean relations.

ⓈHOLCONST
│ ⦏Pr2BrT⦎ : ('a, FTV) BR → ('a, BOOL) BR
├───────────
│ ∀$=⋎p⦁ Pr2BrT $=⋎p = λx y⦁  fTrue ≤⋎t⋎4 (x =⋎p y) 
■ 

ⓈHOLCONST
│ ⦏Pr2BrF⦎ : ('a, FTV) BR → ('a, BOOL) BR
├───────────
│ ∀$=⋎p⦁ Pr2BrF $=⋎p = λx y⦁  fFalse ≤⋎t⋎4 (x =⋎p y) 
■ 

ⓈHOLCONST
│ ⦏BrTF2Pr⦎ : ('a, BOOL) BR → ('a, BOOL) BR → ('a, FTV) BR
├───────────
│ ∀$=⋎p $=⋎q⦁ BrTF2Pr $=⋎p $=⋎q = λx y⦁ Lub $≤⋎t⋎4 {ftv | x =⋎p y ∧ ftv = fTrue ∨ x =⋎p y ∧ ftv = fFalse} 
■ 

\subsection{Proof Context}

=SML
add_pc_thms "'misc1" [];
commit_pc "'misc1";

force_new_pc "⦏misc1⦎";
merge_pcs ["rbjmisc", "'misc1"] "misc1";
commit_pc "misc1";
force_new_pc "⦏misc11⦎";
merge_pcs ["rbjmisc1", "'misc1"] "misc11";
commit_pc "misc11";
=TEX


\section{MISC2}

=SML
open_theory "misc1";
force_new_theory "⦏misc2⦎";
new_parent "GS";
force_new_pc "⦏'misc2⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'misc2";
set_merge_pcs ["misc1", "'GS1", "'misc2"];
=TEX

\section{SET THEORY}

\subsection{Mapping Functions over Sets}

The following function makes recursive definition of functions over sets of type GS just a little more compact.

ⓈHOLCONST
│ ⦏FunImage⋎g⦎ : (GS → 'a) → GS → ('a SET)
├───────────
│ ∀f s⦁ FunImage⋎g f s = {x | ∃y⦁ y ∈⋎g s ∧ x = f y}
■

=GFT
⦏funimage⋎g_fc_lemma⦎ =
	⊢ ∀ f s x⦁ x ∈⋎g s ⇒ f x ∈ FunImage⋎g f s
=TEX

\ignore{
=SML
set_flag("subgoal_package_quiet", true);


set_goal([], ⌜∀f s x⦁ x ∈⋎g s ⇒ f x ∈ FunImage⋎g f s⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜FunImage⋎g⌝] THEN REPEAT strip_tac);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val funimage⋎g_fc_lemma = save_pop_thm "funimage⋎g_fc_lemma";

set_merge_pcs ["misc1", "'misc2"];
=TEX
}%ignore



\section{INDEXED SETS}

There is a version of indexed sets in \cite{rbjt006}.

In this version the functions yield DPOs.
This gives a complete partial order over the indexed sets which was required for some versions of infinitary first order logic.
This is more complicated of course and not to be used unless essential.

In this implementation of indexed sets we use discrete partial orders in the codomain, so that the resulting partial orders are complete.

=SML
declare_type_abbrev("⦏IS⦎", ["'a"], ⓣGS → 'a DPO⌝);
=TEX

ⓈHOLCONST
│ ⦏IsVal⦎ : 'a IS → GS → 'a
├───────────
│ ∀is g⦁ IsVal is g = dpoV (is g)
■

ⓈHOLCONST
│ ⦏IsRan⦎ : 'a IS → 'a SET
├───────────
│ ∀is⦁ IsRan is = {v | ∃α⦁ dpoE v = is α}
■

ⓈHOLCONST
│ ⦏IsDom⦎ : 'a IS → GS SET
├───────────
│ ∀is⦁ IsDom is = {i | ¬ (is i) = dpoB}
■

ⓈHOLCONST
│ ⦏IsSDom⦎ : 'a IS → GS SET
├───────────
│ ∀is⦁ IsSDom is = {i | ¬ ((is i) = dpoB ∨ (is i) = dpoT)}
■

=GFT
⦏is_domran_lemma⦎ =
	⊢ ∀ x y⦁ x ∈ IsSDom y ⇒ IsVal y x ∈ IsRan y
=TEX

\ignore{
=SML
set_goal ([], ⌜∀x y⦁ x ∈ IsSDom y ⇒ IsVal y x ∈ IsRan y⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜IsSDom⌝, get_spec ⌜IsVal⌝, get_spec ⌜IsRan⌝]);
a (strip_tac THEN ∃_tac ⌜x⌝); 
a (all_fc_tac [rewrite_rule [get_spec ⌜dpoUdef⌝, get_spec ⌜dpoOdef⌝] dpoev_lemma1]);
val is_domran_lemma = save_pop_thm "is_domran_lemma";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏IsOd⦎ : 'a IS → GS SET
├───────────
│ ∀is⦁ IsOd is = {i | is i = dpoT}
■

ⓈHOLCONST
│ ⦏IsUd⦎ : 'a IS → GS SET
├───────────
│ ∀is⦁ IsUd is = {i | is i = dpoB}
■

ⓈHOLCONST
│ ⦏IsTDom⦎ : 'a IS → (GS SET × GS SET × GS SET)
├───────────
│ ∀is⦁ IsTDom is = (IsSDom is, IsUd is, IsOd is)
■

ⓈHOLCONST
│ ⦏IsOverRide⦎ : 'a IS → 'a IS → 'a IS
├───────────
│ ∀is1 is2⦁ IsOverRide is1 is2 =
│	λi⦁ if ¬ dpoUdef (is2 i) then is2 i else is1 i 
■

=GFT
⦏istdom_eq_fc_lemma⦎ =
   ⊢ ∀ x y
     ⦁ IsTDom x = IsTDom y
         ⇒ IsUd x = IsUd y
           ∧ IsOd x = IsOd y
           ∧ IsSDom x = IsSDom y
           ∧ IsDom x = IsDom y

⦏isoverride_isdom_lemma⦎ =
   ⊢ ∀ x y⦁ IsDom (IsOverRide x y) = IsDom x ∪ IsDom y

⦏isoverride_isud_lemma⦎ =
   ⊢ ∀ x y⦁ IsUd (IsOverRide x y) = IsUd x \ IsDom y

⦏isoverride_isod_lemma⦎ =
   ⊢ ∀ x y⦁ IsOd (IsOverRide x y) = IsOd y ∪ IsOd x \ IsDom y

isoverride_issdom_lemma =
   ⊢ ∀ x y⦁ IsSDom (IsOverRide x y) = IsSDom y ∪ IsSDom x \ IsDom y
=TEX

\ignore{
=SML
set_goal ([], ⌜∀x y⦁ IsTDom x = IsTDom y ⇒
	IsUd x = IsUd y ∧ IsOd x = IsOd y ∧ IsSDom x = IsSDom y ∧ IsDom x = IsDom y⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜IsTDom⌝, get_spec ⌜IsDom⌝] THEN REPEAT strip_tac
	THEN POP_ASM_T ante_tac THEN_TRY asm_rewrite_tac[]);
a (strip_tac THEN DROP_NTH_ASM_T 2 ante_tac THEN PC_T1 "hol1" rewrite_tac[get_spec ⌜IsUd⌝]);
a (strip_tac THEN asm_rewrite_tac[]);
val istdom_eq_fc_lemma = save_pop_thm "istdom_eq_fc_lemma";

set_goal ([], ⌜∀x y⦁ IsDom (IsOverRide x y) = IsDom x ∪ IsDom y⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜IsDom⌝, get_spec ⌜IsOverRide⌝]
	THEN PC_T "hol1" strip_tac
	THEN strip_tac THEN rewrite_tac[∈_in_clauses, get_spec ⌜dpoUdef⌝]);
a (cases_tac ⌜y x' = dpoB⌝ THEN asm_rewrite_tac[]);
val isoverride_isdom_lemma = save_pop_thm "isoverride_isdom_lemma";

set_goal ([], ⌜∀x y⦁ IsUd (IsOverRide x y) = IsUd x \ IsDom y ⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜IsUd⌝, get_spec ⌜IsDom⌝, get_spec ⌜IsOverRide⌝]
	THEN PC_T "hol1" strip_tac
	THEN strip_tac THEN rewrite_tac[∈_in_clauses, get_spec ⌜dpoUdef⌝]);
a (cases_tac ⌜y x' = dpoB⌝ THEN asm_rewrite_tac[]);
val isoverride_isud_lemma = save_pop_thm "isoverride_isud_lemma";

set_goal ([], ⌜∀x y⦁ IsOd (IsOverRide x y) = IsOd y ∪ (IsOd x \ IsDom y)⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜IsOd⌝, get_spec ⌜IsDom⌝, get_spec ⌜IsOverRide⌝]
	THEN PC_T "hol1" strip_tac
	THEN strip_tac THEN rewrite_tac[∈_in_clauses, get_spec ⌜dpoUdef⌝]);
a (cases_tac ⌜y x' = dpoB⌝ THEN asm_rewrite_tac[]);
val isoverride_isod_lemma = save_pop_thm "isoverride_isod_lemma";

set_goal ([], ⌜∀x y⦁ IsSDom (IsOverRide x y) = IsSDom y ∪ ((IsSDom x) \ (IsDom y))⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜IsSDom⌝, get_spec ⌜IsDom⌝, get_spec ⌜IsOverRide⌝]
	THEN PC_T "hol1" strip_tac
	THEN strip_tac THEN rewrite_tac[∈_in_clauses, get_spec ⌜dpoUdef⌝]);
a (cases_tac ⌜y x' = dpoB⌝ THEN asm_rewrite_tac[]);
val isoverride_issdom_lemma = save_pop_thm "isoverride_issdom_lemma";
=IGN
set_goal ([], ⌜∀x y v w⦁ IsSDom x = IsSDom y ∧ IsSDom v = IsSDom w ⇒
	IsSDom (IsOverRide x v) = IsSDom (IsOverRide y w)⌝);

set_goal ([], ⌜∀x y v w⦁ IsTDom x = IsTDom y ∧ IsTDom v = IsTDom w ⇒
	IsTDom (IsOverRide x v) = IsTDom (IsOverRide y w)⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜IsTDom⌝]);


=TEX
}%ignore

\section{ORDERS AND PRE-ORDERS}

\subsection{Indexed Sets}

\subsubsection{IS}

Indexed sets are functions whose codomain is a discrete partial order.
From any ordering of the codomain an ordering of the indexed sets may be obtained using {\it Pw}.
This can be done with the discrete order, but we also need to do this with other orders.

The following function lifts an ordering on the elements of the codomain to an ordering on the indexed sets.

ⓈHOLCONST
│ ⦏IsEO⦎ : ('a → 'a → BOOL) → ('a IS → 'a IS → BOOL)
├───────────
│ ∀r⦁ IsEO r = Pw (DpoEO r)
■

=GFT
⦏is_lubs_exist_thm⦎ =
	⊢ ∀ r⦁ LubsExist r ⇒ LubsExist (IsEO r)

⦏is_glbs_exist_thm⦎ =
	⊢ ∀ r⦁ GlbsExist r ⇒ GlbsExist (IsEO r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ LubsExist r ⇒ LubsExist (IsEO r)⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜IsEO⌝]
	THEN fc_tac [dpoeo_lubs_exist_thm]
	THEN fc_tac [inst_type_rule [(ⓣGS⌝, ⓣ'a⌝)] pw_lubs_exist_thm]
	THEN strip_tac);
val is_lubs_exist_thm = save_pop_thm "is_lubs_exist_thm";

set_goal([], ⌜∀r⦁ GlbsExist r ⇒ GlbsExist (IsEO r)⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜IsEO⌝]
	THEN fc_tac [dpoeo_glbs_exist_thm]
	THEN fc_tac [inst_type_rule [(ⓣGS⌝, ⓣ'a⌝)] pw_glbs_exist_thm]
	THEN strip_tac);
val is_glbs_exist_thm = save_pop_thm "is_glbs_exist_thm";
=TEX
}%ignore


\subsection{Partial Relations}

For this section a partial relation is taken to be a four valued relation.
In my applications these are membership relations so the ordering is suggestive of those applications.


ⓈHOLCONST
│ ⦏$≤⋎∈⦎ : (GS, FTV)BR → (GS, FTV)BR → BOOL
├───────────
│ $≤⋎∈ = Pw (Pw $≤⋎t⋎4)
■

=GFT
⦏crpou_≤⋎∈_thm⦎ = ⊢ CRpoU $≤⋎∈

⦏ccrpou_≤⋎∈_thm⦎ = ⊢ CcRpoU $≤⋎∈

⦏≤⋎∈_clauses⦎ = ⊢ GlbsExist $≤⋎∈ ∧ LubsExist $≤⋎∈ ∧ (∀ x⦁ x ≤⋎∈ x)

⦏≤⋎∈_fc_clauses⦎ =
   ⊢ (∀ x y z⦁ x ≤⋎∈ y ∧ y ≤⋎∈ z ⇒ x ≤⋎∈ z)
       ∧ (∀ x y⦁ x ≤⋎∈ y ∧ y ≤⋎∈ x ⇒ x = y)
=TEX

\ignore{
=SML
set_goal([], ⌜CRpoU $≤⋎∈⌝);
a (rewrite_tac [get_spec ⌜$≤⋎∈⌝]);
a (bc_tac [pw_crpou_thm]);
a (bc_tac [pw_crpou_thm]);
a (rewrite_tac[≤⋎t⋎4_crpou_thm]);
val crpou_≤⋎∈_thm = save_pop_thm "crpou_≤⋎∈_thm";

set_goal([], ⌜CcRpoU $≤⋎∈⌝);
a (bc_tac [crpou_ccrpou_lemma]);
a (rewrite_tac[crpou_≤⋎∈_thm]);
val ccrpou_≤⋎∈_thm = save_pop_thm "ccrpou_≤⋎∈_thm";

set_goal([], ⌜GlbsExist $≤⋎∈
       ∧ LubsExist $≤⋎∈
       ∧ (∀ x⦁ x ≤⋎∈ x)⌝);
a (rewrite_tac [rewrite_rule [crpou_≤⋎∈_thm] (∀_elim ⌜$≤⋎∈⌝ crpou_fc_clauses)]);
val ≤⋎∈_clauses = save_pop_thm "≤⋎∈_clauses";

val ≤⋎∈_fc_clauses = prove_thm ("≤⋎∈_fc_clauses",
	⌜(∀ x y z⦁ x ≤⋎∈ y ∧ y ≤⋎∈ z ⇒ x ≤⋎∈ z)
      		∧ (∀ x y⦁ x ≤⋎∈ y ∧ y ≤⋎∈ x ⇒ x = y)⌝,
	rewrite_tac [rewrite_rule [crpou_≤⋎∈_thm] (∀_elim ⌜$≤⋎∈⌝ crpou_fc_clauses)]);


add_pc_thms "'misc2" (map get_spec [] @ [ccrpou_≤⋎∈_thm, crpou_≤⋎∈_thm, ≤⋎∈_clauses]);
set_merge_pcs ["misc11", "'GS1", "'misc2"];
=TEX
}%ignore

Because the ordering here is derived from the ordering on the four truth values there are some simplifications to reasoning about limits which are worth turning into theorems.

=GFT
⦏≤⋎∈_lub_thm⦎ =
   ⊢ ∀ G⦁ Lub $≤⋎∈ G = (λ x y⦁ Lub $≤⋎t⋎4 {w|∃ g⦁ g ∈ G ∧ w = g x y})
=TEX

\ignore{
=SML
set_goal([], ⌜∀ G⦁ Lub $≤⋎∈ G = (λ x y⦁ Lub $≤⋎t⋎4 {w|∃ g⦁ g ∈ G ∧ w = g x y})⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜$≤⋎∈⌝, rewrite_rule [] (∀_elim ⌜$≤⋎t⋎4⌝ crpou_lub_pw_pw_lemma)]);
val ≤⋎∈_lub_thm = save_pop_thm "≤⋎∈_lub_thm";
=TEX
}%ignore

\section{MISCELLANEOUS THEOREMS}

\subsection{Partial Relations}

=GFT
⦏≤⋎∈_increasing_pointwise_thm⦎ =
   ⊢ Increasing $≤⋎∈ $≤⋎t⋎4 (λ f⦁ f x' y)
=TEX

\ignore{
=SML
set_goal([], ⌜Increasing $≤⋎∈ $≤⋎t⋎4 (λ f⦁ f x' y)⌝);
a (rewrite_tac [get_spec ⌜Increasing⌝, get_spec ⌜$≤⋎∈⌝, get_spec ⌜Pw⌝]
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[]);
val ≤⋎∈_increasing_pointwise_thm = save_pop_thm "≤⋎∈_increasing_pointwise_thm";
=TEX
}%ignore


\subsection{Proof Contexts}

=SML
add_pc_thms "'misc2" [];
commit_pc "'misc2";

force_new_pc "⦏misc2⦎";
merge_pcs ["misc1", "'GS1", "'misc2"] "misc2";
commit_pc "misc2";
force_new_pc "⦏misc21⦎";
merge_pcs ["misc11", "'GS1", "'misc2"] "misc21";
commit_pc "misc21";
=TEX

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{misc1.th}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{misc2.th}
}  %\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
