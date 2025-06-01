=IGN
$Id: t005.doc,v 1.18 2013/01/10 16:35:58 rbj Exp $
open_theory "wfrel";
set_merge_pcs ["hol", "wfrel"];
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\tabstop=0.25in
\usepackage{A4}

\def\Hide#1{\relax}
\newcommand{\ignore}[1]{}

\title{Well Founded Relations and Recursion}
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
Fixed points, well founded relations and a recursion theorem.
\end{abstract}

\vfill

\begin{centering}

\href{http://www.rbjones.com/rbjpub/pp/doc/t005.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t005.pdf}

{\footnotesize

Created 2004/07/15

Last Modified $ $Date: 2013/01/10 16:35:58 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t005.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t005.pdf}

$ $Id: t005.doc,v 1.18 2013/01/10 16:35:58 rbj Exp $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize

\end{centering}

\thispagestyle{empty}
\end{titlepage}
\newpage
{\parskip=0pt\tableofcontents}

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\newpage
\section{Introduction}

For context and motivation see \cite{rbjt000}.

There are in this document two treatments of well-foundedness and the recursion theorem which differ primarily only in the type of the relations which they deal with.

Actually, they don't look different at all.
Must check out whether there are {\it any} differences!

They were at one time in separate documents but have now been brought together in the one document as a step towards rationalisation.

The material on transitive closure is common to both.

\section{Transitive Closure}

Elementary results about transitive relations and transitive closure.

The new theory $tc$ is first created.
=SML
open_theory "hol";
force_new_theory "⦏tc⦎";
set_pc "hol";
=TEX

\subsection{Definitions}

There is in hol4 a theory of relations in which transitive closure is defined in the obvious way, similar to the way in which it is defined here.
There is also a package providing support for defining relations using rules, and an example in which a Church-Rosser result for the pure combinatory logic is obtained very concisely by using a definition of reflexive transitive relation through that package instead of the one in the theory of relations.
The main advantage of this alternative approach is that it gives automatically induction principles for reasoning about reflexive transitive closures which are not available in the theory of relations.

The following development begins in a similar vein to the hol4 theory of relations but then continues to obtain the results delivered by defining reflexive transitive closure using the hol4 relation definition package.
Of these the most important are the induction principles, but I have replicated the other principles which are automatically obtained in hol4.

The results below which involve decomposition of transitive closure into a path of direct reductions represent a more cumbersome approach to proofs about transitive closures which demand some kind of induction.
It may be best in considering such proofs, first to look at the induction principles which follow these decompositions.

ⓈHOLCONST
│ ⦏trans⦎: ('a  → 'a → BOOL) → BOOL
├
│ ∀r⦁ trans r ⇔ ∀ s t u⦁ r s t ∧ r t u ⇒ r s u
■

ⓈHOLCONST
│ ⦏tc⦎: ('a  → 'a → BOOL) →  ('a  → 'a → BOOL)
├
│ ∀r⦁ tc r = λ s t⦁ ∀tr⦁ trans tr ∧ (∀v u⦁ r v u ⇒ tr v u) ⇒ tr s t
■

\subsection{Theorems}

=GFT
⦏tran_tc_thm⦎ =
	⊢ ∀r⦁ trans (tc r)

⦏tran_tc_thm2⦎ =
	⊢ ∀ r x y z⦁ tc r x y ∧ tc r y z
		⇒ tc r x z
⦏tc_incr_thm⦎ =
	⊢ ∀r x y ⦁ r x y
		⇒ tc r x y
=TEX
=GFT
⦏tc_decomp_thm⦎ =
	⊢ ∀ r x y⦁ tc r x y ∧ ¬ r x y
		⇒ ∃z⦁ tc r x z ∧ r z y
⦏tc_decomp_thm2⦎ =
	⊢ ∀ r x y⦁ tc r x y
		⇒ (∃ f n⦁ x = f 0 ∧ y = f n ∧ (∀ m⦁ m < n ⇒ r (f m) (f (m + 1))))
⦏tc_decomp_thm3⦎ =
	⊢ ∀ r x y⦁ tc r x y 
		⇒ (∃ f n⦁ x = f 0 ∧ y = f (n + 1)
		∧ (∀ m⦁ m ≤ n ⇒ r (f m) (f (m + 1))))
⦏tc_decomp_thm4⦎ =
	⊢ ∀ r x y⦁ (∃ f n⦁ x = f 0 ∧ y = f (n + 1) ∧ (∀ m⦁ m ≤ n ⇒ r (f m) (f (m + 1))))
		⇒ tc r x y
⦏tc_decomp_thm5⦎ =
	⊢ ∀ r x y⦁ tc r x y ∧ ¬ r x y
		⇒ (∃ z⦁ r x z ∧ tc r z y)
⦏tc_⇔_thm⦎ =
	⊢ ∀ r x y⦁ tc r x y
		⇔ (∃ f n⦁ x = f 0 ∧ y = f (n + 1) ∧ (∀ m⦁ m ≤ n ⇒ r (f m) (f (m + 1))))

⦏tc_mono_thm⦎ = 
	⊢ ∀ r1 r2⦁ (∀ x y⦁ r1 x y ⇒ r2 x y)
		⇒ (∀ x y⦁ tc r1 x y ⇒ tc r2 x y)
⦏tc_p_thm⦎ = 
	⊢ ∀ r p⦁ (∀ x y⦁ r x y ⇒ p x)
		⇒ (∀ x y⦁ tc r x y ⇒ p x)
=TEX
=GFT
⦏tc_induced_thm⦎ =
	⊢ ∀ r u x⦁ tc (λ x y⦁ r (f x) (f y)) u x
		⇒ tc r (f u) (f x)
⦏tran_tc_id_thm⦎ =
	⊢ ∀ r⦁ trans r ⇒ tc r = r
=TEX

\ignore{
=SML
val tc_def = get_spec ⌜tc⌝;

set_goal([], ⌜∀r⦁ trans (tc r)⌝);
a (rewrite_tac(map get_spec [⌜tc⌝,⌜trans⌝]));
a (REPEAT strip_tac);
a (all_asm_fc_tac []);
a (all_asm_fc_tac []);
val tran_tc_thm = save_pop_thm("tran_tc_thm");

set_goal([],⌜∀ r x y z⦁ tc r x y ∧ tc r y z ⇒ tc r x z⌝);
a (prove_tac [rewrite_rule [get_spec ⌜trans⌝] tran_tc_thm]);
val tran_tc_thm2 = save_pop_thm("tran_tc_thm2");

set_goal([],⌜∀r x y ⦁ r x y ⇒ tc r x y⌝);
a (rewrite_tac [get_spec ⌜tc⌝, sets_ext_clauses]
	THEN REPEAT strip_tac);
a (all_asm_fc_tac[]);
val tc_incr_thm = save_pop_thm("tc_incr_thm");

set_goal([],⌜∀ r x y⦁ tc r x y ∧ ¬ r x y ⇒ ∃z⦁ tc r x z ∧ r z y⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜∀q⦁ trans q ∧ (∀v w⦁ r v w ⇒ q v w) ⇒ q x y⌝);
a (asm_ante_tac ⌜tc r x y⌝);
a (rewrite_tac [get_spec ⌜tc⌝, get_spec ⌜trans⌝]);
a (spec_nth_asm_tac 1 ⌜λv w⦁ r v w ∨ ∃u⦁ tc r v u ∧ r u w⌝);
(* *** Goal "2.1" *** *)
a (swap_nth_asm_concl_tac 1
	THEN rewrite_tac [get_spec ⌜trans⌝]
	THEN REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a (∃_tac ⌜t⌝
	THEN asm_rewrite_tac[]);
a (all_fc_tac [tc_incr_thm]);
(* *** Goal "2.1.2" *** *)
a (∃_tac ⌜u'⌝
	THEN asm_rewrite_tac[]);
a (REPEAT (all_asm_fc_tac [tran_tc_thm2,tc_incr_thm]));
(* *** Goal "2.1.3" *** *)
a (∃_tac ⌜t⌝
	THEN asm_rewrite_tac[]);
a (REPEAT(all_asm_fc_tac [tran_tc_thm2,tc_incr_thm]));
(* *** Goal "2.1.4" *** *)
a (∃_tac ⌜u''⌝
	THEN asm_rewrite_tac[]);
a (REPEAT(all_asm_fc_tac [tran_tc_thm2,tc_incr_thm]));
(* *** Goal "2.2" *** *)
a (swap_nth_asm_concl_tac 1
	THEN asm_rewrite_tac []);
(* *** Goal "2.3" *** *)
a (swap_nth_asm_concl_tac 1
	THEN asm_rewrite_tac []);
val tc_decomp_thm = save_pop_thm "tc_decomp_thm";

set_goal([], ⌜∀ r x y⦁ tc r x y ⇒ ∃f n⦁ x = f 0 ∧ y = f n ∧ (∀m⦁ m < n ⇒ r (f m) (f (m+1)))⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜∀q⦁ trans q ∧ (∀v w⦁ r v w ⇒ q v w) ⇒ q x y⌝);
(* *** Goal "1" *** *)
a (asm_ante_tac ⌜tc r x y⌝);
a (rewrite_tac [get_spec ⌜tc⌝, get_spec ⌜trans⌝]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 1 ⌜λx y⦁ ∃f n⦁ x = f 0 ∧ y = f n ∧ (∀m⦁ m < n ⇒ r (f m) (f (m+1)))⌝);
(* *** Goal "2.1" *** *)
a (swap_nth_asm_concl_tac 1
	THEN rewrite_tac[get_spec ⌜trans⌝]
	THEN REPEAT strip_tac);
a (∃_tac ⌜λx⦁ if x < n then f x else f' (x - n)⌝ THEN ∃_tac ⌜n + n'⌝ THEN asm_rewrite_tac[]);
a (REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a (cases_tac ⌜n = 0⌝);
(* *** Goal "2.1.1.1" *** *)
a (DROP_NTH_ASM_T 6 (asm_tac o (rewrite_rule[asm_rule ⌜n = 0⌝])));
a (rewrite_tac[asm_rule ⌜n = 0⌝, eq_sym_rule (asm_rule ⌜t = f' 0⌝), eq_sym_rule (asm_rule ⌜t = f 0⌝)]);
(* *** Goal "2.1.1.2" *** *)
a (strip_asm_tac (rewrite_rule [asm_rule ⌜¬ n = 0⌝] (∀_elim ⌜n⌝ ℕ_cases_thm)));
a (asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
a (cond_cases_tac ⌜m < n⌝);
(* *** Goal "2.1.2.1" *** *)
a (asm_fc_tac[]);
a (cond_cases_tac ⌜m + 1 < n⌝);
a (LEMMA_T ⌜m < n ∧ ¬ m + 1 < n ⇒ n = m+1⌝ (fn x => all_fc_tac[x]) THEN1 (PC_T1 "lin_arith" prove_tac[]));
a (LEMMA_T ⌜f' ((m + 1) - n) = f (m + 1)⌝ rewrite_thm_tac
	THEN1 (rewrite_tac[(eq_sym_rule o asm_rule) ⌜n = m + 1⌝] THEN SYM_ASMS_T rewrite_tac));
a (strip_tac);
(* *** Goal "2.1.2.2" *** *)
a (cond_cases_tac ⌜m + 1 < n⌝);
(* *** Goal "2.1.2.2.1" *** *)
a (lemma_tac ⌜F:BOOL⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "2.1.2.2.2" *** *)
(* a (lemma_tac ⌜m - n < n'⌝ THEN1 PC_T1 "lin_arith" prove_tac[asm_rule ⌜m < n + n'⌝, asm_rule ⌜¬ m < n⌝]); *)
a (lemma_tac ⌜m - n < n'⌝);
(* *** Goal "2.1.2.2.2.1" *** *)
a (DROP_ASM_T ⌜m < n + n'⌝ ante_tac THEN rewrite_tac [less_def]);
a (fc_tac [pc_rule1 "lin_arith" prove_rule [] ⌜¬ m < n ⇒ n ≤ m ⌝]);
a (fc_tac [≤_def]);
a (rewrite_tac [eq_sym_rule (asm_rule ⌜n + i = m⌝)]);
a (PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2.1.2.2.2.2" *** *)
a (spec_nth_asm_tac 5 ⌜m - n⌝);
a (fc_tac [pc_rule1 "lin_arith" prove_rule [] ⌜¬ m < n ⇒ n ≤ m ⌝]);
a (fc_tac [≤_def]);
a (rewrite_tac [eq_sym_rule (asm_rule ⌜n + i = m⌝)]);
a (LEMMA_T ⌜((n + i) + 1) - n = i+1⌝ asm_rewrite_thm_tac);
(* *** Goal "2.1.2.2.2.2.1" *** *)
a (LEMMA_T ⌜(n + i) + 1 = n + (i + 1)⌝ rewrite_thm_tac THEN1 PC_T1 "lin_arith" prove_tac[]);
(* *** Goal "2.1.2.2.2.2.2" *** *)
a (LEMMA_T ⌜i = m - n⌝ asm_rewrite_thm_tac);
a (rewrite_tac [(eq_sym_rule o asm_rule) ⌜n + i = m⌝]);
(* *** Goal "2.2" *** *)
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
a (∃_tac ⌜λz⦁ if z = 0 then v else w⌝
	THEN ∃_tac ⌜1⌝
	THEN asm_rewrite_tac[]);
a (REPEAT strip_tac);
a (lemma_tac ⌜m = 0⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a (asm_rewrite_tac[]);
(* *** Goal "2.3" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac[] THEN strip_tac);
val tc_decomp_thm2 = save_pop_thm "tc_decomp_thm2";

set_goal([], ⌜∀ r x y⦁ tc r x y ⇒ ∃f n⦁ x = f 0 ∧ y = f (n+1)
	∧ (∀m⦁ m ≤ n ⇒ r (f m) (f (m+1)))⌝);
a (REPEAT strip_tac);
a (fc_tac [tc_decomp_thm]);
(* *** Goal "1" *** *)
a (∃_tac ⌜λz⦁ if z = 0 then x else y⌝
	THEN ∃_tac ⌜0⌝
	THEN asm_rewrite_tac[]);
a (REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [tc_decomp_thm2]);
a (∃_tac ⌜λv⦁ if v ≤ n' then f' v else y⌝
	THEN ∃_tac ⌜n'⌝
	THEN asm_rewrite_tac[]);
a (REPEAT strip_tac THEN asm_rewrite_tac[]);
a (cond_cases_tac ⌜m + 1 ≤ n'⌝);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜m < n'⌝
	THEN1 (PC_T1 "lin_arith" prove_tac [asm_rule ⌜m + 1 ≤ n'⌝]));
a (all_asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (lemma_tac ⌜m = n'⌝ THEN1 (PC_T1 "lin_arith" prove_tac
	[asm_rule ⌜¬ m + 1 ≤ n'⌝,
	asm_rule ⌜m ≤ n'⌝]));
a (var_elim_asm_tac ⌜m = n'⌝);
a (DROP_ASM_T  ⌜r z y⌝ ante_tac
	THEN asm_rewrite_tac[]);
val tc_decomp_thm3 = save_pop_thm "tc_decomp_thm3";

set_goal([], ⌜∀ r x y⦁ (∃f n⦁ x = f 0 ∧ y = f (n + 1)
	∧ (∀m⦁ m ≤ n ⇒ r (f m) (f (m+1))))
		⇒ tc r x y⌝);
a (lemma_tac ⌜∀n r x y⦁ (∃f⦁ x = f 0 ∧ y = f (n + 1)
	∧ (∀m⦁ m ≤ n ⇒ r (f m) (f (m+1))))
		⇒ tc r x y⌝);
(* *** Goal "1" *** *)
a (strip_tac);
a (induction_tac ⌜n⌝ THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a (spec_nth_asm_tac 1 ⌜0⌝);
a (LEMMA_T ⌜tc r (f 0) (f (0 + 1))⌝ ante_tac
	THEN_LIST [fc_tac [tc_incr_thm], rewrite_tac[]]);
(* *** Goal "1.2" *** *)
a (list_spec_nth_asm_tac 4 [⌜r⌝, ⌜x⌝, ⌜f (n + 1)⌝]);
a (spec_nth_asm_tac 1 ⌜f⌝);
a (spec_nth_asm_tac 4 ⌜m'⌝);
a (PC_T1 "lin_arith" asm_prove_tac[]);
(* *** Goal "1.2.2" *** *)
a (spec_nth_asm_tac 2 ⌜n + 1⌝);
a (lemma_tac ⌜tc r (f (n + 1)) (f ((n + 1) + 1))⌝ THEN1 fc_tac [tc_incr_thm]);
a (LEMMA_T ⌜tc r x (f ((n + 1) + 1))⌝ ante_tac THEN1 all_fc_tac [tran_tc_thm2]);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (REPEAT strip_tac );
a (spec_nth_asm_tac 4 ⌜n⌝);
a (all_asm_fc_tac[]);
val tc_decomp_thm4 = save_pop_thm "tc_decomp_thm4";

set_goal([], ⌜∀ r x y⦁ tc r x y ⇔ ∃f n⦁ x = f 0 ∧ y = f (n + 1)
	∧ (∀m⦁ m ≤ n ⇒ r (f m) (f (m+1)))⌝);
a (REPEAT ∀_tac THEN REPEAT_N 3 strip_tac
	THEN all_fc_tac [tc_decomp_thm3, tc_decomp_thm4]);
a (∃_tac ⌜f⌝ THEN ∃_tac ⌜n⌝ THEN asm_rewrite_tac[]);
val tc_⇔_thm = save_pop_thm "tc_⇔_thm";

set_goal([],⌜∀ r x y⦁ tc r x y ∧ ¬ r x y ⇒ ∃z⦁ r x z ∧ tc r z y⌝);
a (REPEAT strip_tac);
a (asm_fc_tac [tc_decomp_thm3]);
a (∃_tac ⌜f 1⌝ THEN asm_rewrite_tac[]);
a (SPEC_NTH_ASM_T 1 ⌜0⌝ (rewrite_thm_tac o  (rewrite_rule[])));
a (rewrite_tac [tc_⇔_thm]);
a (∃_tac ⌜λx⦁ f (x + 1)⌝ THEN asm_rewrite_tac[]);
a (lemma_tac ⌜∃n'⦁ n = n'+1⌝ THEN1 contr_tac);
(* *** Goal "1" *** *)
a (strip_asm_tac (∀_elim ⌜n⌝ ℕ_cases_thm));
(* *** Goal "1.1" *** *)
a (var_elim_asm_tac ⌜n = 0⌝);
a (spec_nth_asm_tac 2 ⌜0⌝);
a (POP_ASM_T ante_tac THEN SYM_ASMS_T rewrite_tac);
(* *** Goal "1.2" *** *)
a (spec_nth_asm_tac 2 ⌜i⌝);
(* *** Goal "2" *** *)
a (∃_tac ⌜n'⌝ THEN asm_rewrite_tac[]);
a (REPEAT strip_tac THEN asm_fc_tac[]);
a (lemma_tac ⌜m + 1≤ n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a (asm_fc_tac[]);
val tc_decomp_thm5 = save_pop_thm "tc_decomp_thm5";

set_goal([],⌜∀ r1 r2⦁ (∀ x y⦁ r1 x y ⇒ r2 x y)
	⇒ (∀ x y⦁ tc r1 x y ⇒ tc r2 x y)⌝);
a (rewrite_tac [get_spec ⌜tc⌝]);
a (REPEAT strip_tac);
a (spec_nth_asm_tac 3 ⌜tr⌝);
a (all_asm_fc_tac[]);
a (all_asm_fc_tac[]);
val tc_mono_thm = save_pop_thm "tc_mono_thm";

set_goal([],⌜∀ r p⦁ (∀ x y⦁ r x y ⇒ p x)
	⇒ (∀ x y⦁ tc r x y ⇒ p x)⌝);
a (rewrite_tac [get_spec ⌜tc⌝]);
a (REPEAT strip_tac);
a (SPEC_NTH_ASM_T 1 ⌜λx y:'a ⦁ (p x):BOOL⌝
	(fn x => strip_asm_tac (rewrite_rule[] x))
	THEN_TRY all_asm_fc_tac[]);
a (swap_nth_asm_concl_tac 1
	THEN rewrite_tac [get_spec ⌜trans⌝]
	THEN REPEAT strip_tac);
val tc_p_thm = save_pop_thm "tc_p_thm";

set_goal ([], ⌜∀r u x⦁ tc (λ x y⦁ r (f x) (f y)) u x ⇒ tc r (f u) (f x)⌝);
a (rewrite_tac [get_spec ⌜tc⌝] THEN REPEAT strip_tac);
a (SPEC_NTH_ASM_T 3 ⌜λx y⦁ tr (f x) (f y)⌝ (strip_asm_tac o (rewrite_rule[])));
a (POP_ASM_T ante_tac THEN DROP_NTH_ASM_T 2 ante_tac
	THEN rewrite_tac [get_spec ⌜trans⌝]
	THEN REPEAT strip_tac
	THEN REPEAT (asm_fc_tac[]));
a (asm_fc_tac[]);
val tc_induced_thm = save_pop_thm "tc_induced_thm";

set_goal([], ⌜∀r⦁ trans r ⇒ tc r = r⌝);
a (rewrite_tac [get_spec ⌜trans⌝, get_spec ⌜tc⌝]);
a (rewrite_tac [ext_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜r⌝);
a (list_spec_nth_asm_tac 5 [⌜s⌝, ⌜t⌝, ⌜u⌝]);
(* *** Goal "2" *** *)
a (asm_fc_tac[]);
val tran_tc_id_thm = save_pop_thm "tran_tc_id_thm";
=TEX
}%ignore

=GFT
⦏tc_decomp_thm6⦎ =
	⊢ ∀ r x y⦁ tc r x y ⇒ r x y ∨ (∃ z⦁ tc r x z ∧ r z y)
⦏tc_decomp_thm7⦎ =
	⊢ ∀ r x y⦁ tc r x y ⇒ r x y ∨ (∃ z⦁ r x z ∧ tc r z y)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ r x y⦁ tc r x y ⇒ r x y ∨ (∃ z⦁ tc r x z ∧ r z y)⌝);
a (REPEAT strip_tac THEN all_fc_tac [tc_decomp_thm]);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
val tc_decomp_thm6 = save_pop_thm "tc_decomp_thm6";

set_goal([], ⌜∀ r x y⦁ tc r x y ⇒ r x y ∨ (∃ z⦁ r x z ∧ tc r z y)⌝);
a (REPEAT strip_tac THEN all_fc_tac [tc_decomp_thm5]);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
val tc_decomp_thm7 = save_pop_thm "tc_decomp_thm7";
=TEX
}%ignore

=GFT
⦏tc_ind0⦎ =
	⊢ ∀ R r⦁ (∀ x y⦁ r x y ⇒ R x y) ∧ (∀ x y z⦁ R x y ∧ R y z ⇒ R x z)
	 ⇒ (∀ x y⦁ tc r x y ⇒ R x y)

⦏tc_ind1⦎ =
	⊢ ∀ R r⦁ (∀ x y⦁ r x y ⇒ R x y) ∧ (∀ x y z⦁ R x y ∧ r y z ⇒ R x z)
	 ⇒ (∀ x y⦁ tc r x y ⇒ R x y)

⦏tc_ind2⦎ =
	⊢ ∀ R r⦁ (∀ x y⦁ r x y ⇒ R x y) ∧ (∀ x y z⦁ r x y ∧ R y z ⇒ R x z)
	 ⇒ (∀ x y⦁ tc r x y ⇒ R x y)
=TEX

\ignore{
=SML
set_goal([], ⌜∀R r⦁ (∀x y⦁ r x y ⇒ R x y) ∧ (∀x y z⦁ R x y ∧ R y z ⇒ R x z)
	⇒ (∀x y⦁ tc r x y ⇒ R x y)⌝);
a (REPEAT strip_tac);
a (POP_ASM_T (asm_tac o (rewrite_rule[tc_def, get_spec ⌜trans⌝])));
a (all_asm_fc_tac[]);
val tc_ind0 = save_pop_thm "tc_ind0";

set_goal([], ⌜∀R r⦁ (∀x y⦁ r x y ⇒ R x y) ∧ (∀x y z⦁ R x y ∧ r y z ⇒ R x z)
	⇒ (∀x y⦁ tc r x y ⇒ R x y)⌝);
a (REPEAT strip_tac);
a (all_fc_tac[tc_decomp_thm3]);
a (lemma_tac ⌜∀m⦁ m < n ⇒ R x (f (m+1))⌝
	THEN1 (strip_tac));
(* *** Goal "1" *** *)
a (induction_tac ⌜m⌝);
(* *** Goal "1.1" *** *)
a (spec_nth_asm_tac 1 ⌜0⌝ THEN asm_rewrite_tac[]);
a (POP_ASM_T (asm_tac o (rewrite_rule[]))
	THEN ALL_ASM_FC_T rewrite_tac []);
(* *** Goal "1.2" *** *)
a (lemma_tac ⌜¬ m < n ⇒ ¬ m + 1 < n⌝ THEN1 (PC_T1 "lin_arith" prove_tac[]));
a (strip_tac);
(* *** Goal "1.3" *** *)
a (strip_tac);
a (lemma_tac ⌜m +1 ≤ n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a (all_asm_fc_tac[]);
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (strip_asm_tac (∀_elim ⌜n⌝ ℕ_cases_thm));
(* *** Goal "2.1" *** *)
a (all_var_elim_asm_tac);
a (LEMMA_T ⌜0 ≤ 0⌝ asm_tac THEN1 prove_tac[]);
a (spec_nth_asm_tac 3 ⌜0⌝ THEN asm_rewrite_tac[]);
a (POP_ASM_T ante_tac THEN rewrite_tac[]
	THEN strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (lemma_tac ⌜i < n⌝ THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a (all_asm_fc_tac[]);
a (LEMMA_T ⌜n ≤ n⌝ asm_tac THEN1 PC_T1 "lin_arith" asm_prove_tac[]);
a (all_asm_fc_tac[]);
a (DROP_NTH_ASM_T 3 (asm_tac o (rewrite_rule [(eq_sym_rule o asm_rule) ⌜n = i + 1⌝])));
a (all_asm_fc_tac[]);
a (var_elim_asm_tac ⌜y = f (n + 1)⌝);
val tc_ind1 = save_pop_thm "tc_ind1";

set_goal([], ⌜∀y x:ℕ⦁ x ≤ y ⇒ y - x + x = y⌝);
a (∀_tac);
a (induction_tac ⌜y⌝);
(* *** Goal "1" *** *)
a (∀_tac THEN rewrite_tac[≤_def] THEN strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∀_tac);
a (rewrite_tac [≤_def] THEN strip_tac);
a (SYM_ASMS_T rewrite_tac);
val minus_lemma1 = pop_thm ();

set_goal([], ⌜∀y x z:ℕ⦁ x + z ≤ y ⇒ y - (x + z) + z = y - x⌝);
a (∀_tac);
a (induction_tac ⌜y⌝);
(* *** Goal "1" *** *)
a (∀_tac THEN rewrite_tac[≤_def] THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (REPEAT ∀_tac);
a (rewrite_tac [≤_def] THEN strip_tac);
a (SYM_ASMS_T rewrite_tac);
a (rewrite_tac [pc_rule1 "lin_arith" prove_rule[] ⌜(x + z) + i = (i + z) + x⌝]);
val minus_lemma2 = pop_thm ();

set_goal([], ⌜∀R r⦁ (∀x y⦁ r x y ⇒ R x y) ∧ (∀x y z⦁ r x y ∧ R y z ⇒ R x z)
	⇒ (∀x y⦁ tc r x y ⇒ R x y)⌝);
a (REPEAT strip_tac);
a (all_fc_tac[tc_decomp_thm3]);
a (lemma_tac ⌜∀m⦁ m ≤ n ⇒ R (f (n - m)) y⌝ THEN1 (strip_tac));
(* *** Goal "1" *** *)
a (induction_tac ⌜m⌝);
(* *** Goal "1.1" *** *)
a (spec_nth_asm_tac 1 ⌜n⌝ THEN asm_rewrite_tac[]);
a (asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a (lemma_tac ⌜¬ m ≤ n ⇒ ¬ m + 1 ≤ n⌝ THEN1 (PC_T1 "lin_arith" prove_tac[]));
a (strip_tac);
(* *** Goal "1.3" *** *)
a (strip_tac);
a (all_fc_tac [minus_lemma1]);
a (lemma_tac ⌜(n - (m + 1)) ≤ n⌝ THEN1 (rewrite_tac[≤_def]));
(* *** Goal "1.3.1" *** *)
a (∃_tac ⌜m+1⌝ THEN strip_tac);
(* *** Goal "1.3.2" *** *)
a (LEMMA_T ⌜r (f (n - (m + 1))) (f (n - (m + 1) + 1))⌝ ante_tac THEN1 all_asm_fc_tac[]);
a (ALL_FC_T rewrite_tac [minus_lemma2] THEN strip_tac);
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (SPEC_NTH_ASM_T 1 ⌜n⌝ ante_tac);
a (rewrite_tac[]);
a (rewrite_tac[asm_rule ⌜x = f 0⌝]);
val tc_ind2 = save_pop_thm "tc_ind2";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏rtc⦎: ('a  → 'a → BOOL) →  ('a  → 'a → BOOL)
├
│ ∀r⦁ rtc r = λ s t⦁ s = t ∨ tc r s t
■

=GFT
⦏tran_rtc_thm⦎ =
	⊢ ∀r⦁ trans (rtc r)

⦏tran_rtc_thm2⦎ =
	⊢ ∀ r s t u⦁ rtc r s t ∧ rtc r t u ⇒ rtc r s u

⦏rtc_incr_thm⦎ =
	⊢ ∀r x y ⦁ r x y ∨ x = y ⇒ rtc r x y
=TEX

\ignore{
=SML
val rtc_def = get_spec ⌜rtc⌝;

set_goal([], ⌜∀r⦁ trans (rtc r)⌝);
a (rewrite_tac [get_spec ⌜trans⌝, rtc_def] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac);
a (all_fc_tac [tran_tc_thm2]);
val tran_rtc_thm = save_pop_thm "tran_rtc_thm";

val tran_rtc_thm2 = save_thm("tran_rtc_thm2", rewrite_rule [get_spec ⌜trans⌝] tran_rtc_thm);

set_goal([], ⌜∀r x y ⦁ r x y ∨ x = y ⇒ rtc r x y⌝);
a (rewrite_tac[rtc_def] THEN REPEAT strip_tac
	THEN all_asm_fc_tac [tc_incr_thm]);
val rtc_incr_thm = save_pop_thm "rtc_incr_thm";
=TEX
}%ignore


=GFT
⦏rtc_decomp_thm⦎ =
	⊢ ∀ R a0 a1⦁ rtc R a0 a1 ⇒ a1 = a0 ∨ (∃ y⦁ R a0 y ∧ rtc R y a1)
⦏rtc_decomp_thm2⦎ =
	⊢ ∀ R a0 a1⦁ rtc R a0 a1 ⇒ a1 = a0 ∨ R a0 a1 ∨ (∃ y⦁ R a0 y ∧ tc R y a1)
⦏rtc_decomp_thm3⦎ =
	⊢ ∀ R a0 a1⦁ rtc R a0 a1 ⇒ a1 = a0 ∨ R a0 a1 ∨ (∃ y⦁ tc R a0 y ∧ R y a1)
=TEX

\ignore{
=SML
set_goal([], ⌜∀R a0 a1⦁ rtc R a0 a1 ⇒ (a1 = a0) ∨ ∃y⦁ R a0 y ∧ rtc R y a1⌝);
a (REPEAT ∀_tac THEN rewrite_tac[rtc_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_var_elim_asm_tac);
(* *** Goal "2" *** *)
a (fc_tac [tc_decomp_thm7]);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜a1⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
val rtc_decomp_thm = save_pop_thm "rtc_decomp_thm";

set_goal([], ⌜∀R a0 a1⦁ rtc R a0 a1 ⇒ (a1 = a0) ∨ R a0 a1 ∨ ∃y⦁ R a0 y ∧ tc R y a1⌝);
a (REPEAT ∀_tac THEN rewrite_tac[rtc_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_var_elim_asm_tac);
(* *** Goal "2" *** *)
a (fc_tac [tc_decomp_thm7]);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
val rtc_decomp_thm2 = save_pop_thm "rtc_decomp_thm2";

set_goal([], ⌜∀R a0 a1⦁ rtc R a0 a1 ⇒ (a1 = a0) ∨ R a0 a1 ∨ ∃y⦁ tc R a0 y ∧ R y a1⌝);
a (REPEAT ∀_tac THEN rewrite_tac[rtc_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_var_elim_asm_tac);
(* *** Goal "2" *** *)
a (fc_tac [tc_decomp_thm6]);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
val rtc_decomp_thm3 = save_pop_thm "rtc_decomp_thm3";
=TEX
}%ignore

=GFT
⦏rtc_mono_thm⦎ =
	⊢ ∀ r1 r2⦁ (∀ x y⦁ r1 x y ⇒ r2 x y)
	 ⇒ (∀ x y⦁ rtc r1 x y ⇒ rtc r2 x y)

⦏rtc_ind0⦎ =
	⊢ ∀ R r⦁ (∀ x y⦁ r x y ⇒ R x y) ∧ (∀ x⦁ R x x)
		∧ (∀ x y z⦁ R x y ∧ R y z ⇒ R x z)
         ⇒ (∀ x y⦁ rtc r x y ⇒ R x y)

⦏rtc_ind1⦎ =
	⊢ ∀ R r⦁ (∀ x⦁ R x x) ∧ (∀ x y z⦁ R x y ∧ r y z ⇒ R x z)
	 ⇒ (∀ x y⦁ rtc r x y ⇒ R x y)

⦏rtc_ind⦎ =
	⊢ ∀ r R⦁ (∀ x⦁ R x x) ∧ (∀ x y z⦁ r x y ∧ R y z ⇒ R x z)
	 ⇒ (∀ x y⦁ rtc r x y ⇒ R x y)
=TEX

\ignore{
=SML
set_goal([],⌜∀ r1 r2⦁ (∀ x y⦁ r1 x y ⇒ r2 x y)
	⇒ (∀ x y⦁ rtc r1 x y ⇒ rtc r2 x y)⌝);
a (rewrite_tac [rtc_def]);
a (REPEAT strip_tac);
a (all_asm_fc_tac[tc_mono_thm]);
val rtc_mono_thm = save_pop_thm "rtc_mono_thm";

set_goal([], ⌜∀R r⦁ (∀x y⦁ r x y ⇒ R x y) ∧ (∀x⦁ R x x) ∧ (∀x y z⦁ R x y ∧ R y z ⇒ R x z) ⇒ (∀x y⦁ rtc r x y ⇒ R x y)⌝);
a (REPEAT strip_tac);
a (POP_ASM_T (strip_asm_tac o (rewrite_rule[rtc_def, tc_def, get_spec ⌜trans⌝]))
	THEN_TRY asm_rewrite_tac[]);
a (all_asm_fc_tac[]);
val rtc_ind0 = save_pop_thm "rtc_ind0";

set_goal([], ⌜∀R r⦁ (∀x⦁ R x x) ∧ (∀x y z⦁ R x y ∧ r y z ⇒ R x z)
	⇒ (∀x y⦁ rtc r x y ⇒ R x y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [rtc_def] THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
a (lemma_tac ⌜∀x y⦁ r x y ⇒ R x y⌝
	THEN1 (REPEAT strip_tac THEN all_asm_ufc_tac[]));
a (all_fc_tac [tc_ind1]);
val rtc_ind1 = save_pop_thm "rtc_ind1";

set_goal([], ⌜∀R r⦁ (∀x⦁ R x x) ∧ (∀x y z⦁ r x y ∧ R y z ⇒ R x z)
	⇒ (∀x y⦁ rtc r x y ⇒ R x y)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [rtc_def] THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
a (lemma_tac ⌜∀x y⦁ r x y ⇒ R x y⌝
	THEN1 (REPEAT strip_tac THEN all_asm_ufc_tac[]));
a (all_fc_tac [tc_ind2]);
val rtc_ind2 = pop_thm ();

set_goal([], ⌜∀r R⦁ (∀x⦁ R x x) ∧ (∀x y z⦁ r x y ∧ R y z ⇒ R x z)
	⇒ (∀x y⦁ rtc r x y ⇒ R x y)⌝);
a (rewrite_tac [rtc_ind2]);
val rtc_ind = save_pop_thm "rtc_ind";
=TEX
}%ignore

=GFT
⦏rtc_rules⦎ =
	⊢ ∀ r⦁ (∀ x⦁ rtc r x x) ∧ (∀ x y z⦁ r x y ∧ rtc r y z ⇒ rtc r x z)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ (∀x⦁ rtc r x x) ∧ ∀x y z⦁ r x y ∧ rtc r y z ⇒ rtc r x z⌝);
a (rewrite_tac [rtc_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (SYM_ASMS_T rewrite_tac);
a (fc_tac [tc_incr_thm]);
(* *** Goal "2" *** *)
a (fc_tac [tc_incr_thm]);
a (all_fc_tac[tran_tc_thm2]);
val rtc_rules = save_pop_thm "rtc_rules";
=TEX
}%ignore

We are now able to obtain a stronger induction principle.

=GFT
⦏rtc_strongind⦎ =
	⊢ ∀ r rtc'⦁ (∀ x⦁ rtc' x x)
		∧ (∀ x y z⦁ r x y ∧ rtc r y z ∧ rtc' y z ⇒ rtc' x z)
         ⇒ (∀ a0 a1⦁ rtc r a0 a1 ⇒ rtc' a0 a1)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r rtc'⦁ (∀x⦁ rtc' x x)
	∧ (∀x y z⦁ r x y ∧ rtc r y z ∧ rtc' y z ⇒ rtc' x z)
	⇒ ∀a0 a1⦁ rtc r a0 a1 ⇒ rtc' a0 a1⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜∀ x⦁ rtc' x x ∧ rtc r x x⌝
	THEN1 (asm_rewrite_tac[rtc_rules]));
a (lemma_tac ⌜∀ x y z⦁ r x y ∧ rtc' y z ∧ rtc r y z ⇒ rtc' x z ∧ rtc r x z⌝
	THEN1 (REPEAT strip_tac
		THEN all_asm_fc_tac[rtc_rules]));
a (ante_tac (rewrite_rule[](list_∀_elim [⌜r⌝, ⌜λx y⦁ rtc' x y ∧ rtc r x y⌝] rtc_ind)));
a (asm_rewrite_tac[]
	THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
val rtc_strongind = save_pop_thm "rtc_strongind";
=TEX
}%ignore

\subsection{Induction Tactics}


=SML
fun ⦏rel_induction_tac⦎ (thm : THM): TACTIC =
(	let	fun bad_thm thm = thm_fail "REL_INDUCTION_T" 29021 [thm];
		val ([r,rtc], body) = (strip_∀ (concl thm))
			handle Fail _ => bad_thm thm;
		val (prem, conc) = dest_⇒ body
			handle Fail _ => bad_thm thm;
		fun match tm = simple_ho_match [] tm conc
			handle Fail _ => bad_thm thm;
	in 	fn (asms, tm) =>
		let	val (tys, tms) = match tm;
			val nth = (conv_rule (MAP_C β_conv) (inst_term_rule tms
					(inst_type_rule tys (all_∀_elim thm))));
		in	bc_tac [nth] (asms, tm)
		end
	end
);
=TEX

=SML
val ⦏rtc_ind_tac⦎ = rel_induction_tac rtc_ind;
val ⦏rtc_strongind_tac⦎ = rel_induction_tac rtc_strongind;
=TEX


=GFT
⦏rtc_cases⦎ =
	⊢ ∀ R a0 a1⦁ rtc R a0 a1 ⇔ a1 = a0 ∨ (∃ y⦁ R a0 y ∧ rtc R y a1)
=TEX

\ignore{
=SML
set_goal([], ⌜∀R a0 a1⦁ rtc R a0 a1 ⇔ (a1 = a0) ∨ ∃y⦁ R a0 y ∧ rtc R y a1⌝);
a (REPEAT ∀_tac THEN rewrite_tac [rtc_def]
	THEN REPEAT strip_tac THEN_TRY all_var_elim_asm_tac
	THEN fc_tac [tc_incr_thm]
	THEN all_fc_tac [tran_tc_thm2]);
a (fc_tac [tc_decomp_thm5]);
(* *** Goal "1" *** *)
a (∃_tac ⌜a1⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜a1⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
val rtc_cases = save_pop_thm "rtc_cases";
=TEX
}%ignore


=GFT
=TEX

\ignore{
=IGN

=TEX
}%ignore


\section{Well Founded Relations (I)}

=SML
open_theory "tc";
force_new_theory "⦏wfrel⦎";
set_pc "hol";
=TEX

Definition of well-founded and transitive-well-founded and proof that the transitive closure of a well-founded relation is transitive-well-founded.

ⓈHOLCONST
│ ⦏well_founded⦎: ('a → 'a → BOOL) → BOOL
├─────────
│ ∀r⦁ well_founded r ⇔ ∀ s ⦁ (∀ x ⦁ (∀ y ⦁ r y x ⇒ s y) ⇒ s x) ⇒ ∀ x ⦁ s x
■

ⓈHOLCONST
│ ⦏twfp⦎: ('a → 'a → BOOL) → BOOL
├──────────
│ ∀r⦁ twfp r ⇔ well_founded r ∧ trans r
■

The first thing I need to prove here is that the transitive closure of a well-founded relation is also well-founded.
This provides a form of induction with a stronger induction hypothesis.

Naturally we would expect this to be proven inductively and the question is therefore what property to use in the inductive proof, the observation that the transitive closure of a relation is well-founded is not explicitly the ascription of a property to the field of the relation.
The obvious method is to relativise the required result to the transitive closure of a set, giving a property of sets, and then to prove that this property is hereditary if the relation is well-founded.

=GFT
⦏tcwf_lemma1⦎ =
   ⊢ ∀ s r⦁ well_founded r
         ⇒ (∀ x⦁ (∀ y⦁ tc r y x ⇒ (∀ z⦁ tc r z y ⇒ s z) ⇒ s y)
             ⇒ (∀ y⦁ tc r y x ⇒ s y))

⦏wf_lemma⦎ =
   ⊢ ∀ r⦁ well_founded r ⇒ (∀ s⦁ (∀ t⦁ (∀ u⦁ r u t ⇒ s u) ⇒ s t) ⇒ (∀ e⦁ s e))

⦏tcwf_lemma2⦎ =
   ⊢ ∀ r⦁ well_founded r
         ⇒ (∀ s⦁ (∀ t⦁ (∀ u⦁ tc r u t ⇒ s u) ⇒ s t) ⇒ (∀ e⦁ s e))

⦏wf_tc_wf_thm⦎ = ⊢ ∀ r⦁ well_founded r ⇒ well_founded (tc r)
=TEX

\ignore{
=SML
set_goal([],⌜∀s r⦁ well_founded r
	⇒ ∀x⦁ (∀y⦁ tc r y x ⇒ (∀z⦁ tc r z y ⇒ s z) ⇒ s y)
	⇒ (∀y⦁ tc r y x ⇒ s y)⌝);
a (rewrite_tac [get_spec ⌜well_founded⌝]);
a (REPEAT_N 3 strip_tac);
a (SPEC_NTH_ASM_T 1 ⌜λx ⦁ (∀y⦁ tc r y x ⇒ (∀z⦁ tc r z y ⇒ s z) ⇒ s y)
	⇒ (∀y⦁ tc r y x ⇒ s y)⌝ ante_tac
	THEN rewrite_tac[]
	THEN REPEAT strip_tac);
a (fc_tac [list_∀_elim [⌜r⌝,⌜y⌝,⌜x⌝] tc_decomp_thm]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 7 ⌜y⌝);
(* *** Goal "1.1" *** *)
a (all_fc_tac [tran_tc_thm2]);
a (spec_nth_asm_tac 10 ⌜y''⌝);
a (asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a (spec_nth_asm_tac 7 ⌜y⌝);
a (spec_nth_asm_tac 3 ⌜z⌝);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 8 ⌜z⌝);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜tc r z x⌝
	THEN1 fc_tac [tc_incr_thm]);
a (lemma_tac ⌜tc r y'' x⌝
	THEN1 strip_asm_tac (list_∀_elim [⌜r⌝,⌜y''⌝,⌜z⌝,⌜x⌝] tran_tc_thm2));
a (spec_nth_asm_tac 12 ⌜y''⌝);
a (spec_nth_asm_tac 6 ⌜z'⌝);
(* *** Goal "2.2" *** *)
a (asm_fc_tac[]);
val tcwf_lemma1 = save_pop_thm "tcwf_lemma1";
=TEX
}%\ignore

\ignore{
=SML
set_goal([],⌜∀r⦁ well_founded r ⇒ ∀s⦁ (∀t⦁ (∀u⦁ r u t ⇒ s u) ⇒ s t) ⇒ (∀e⦁ s e)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜well_founded⌝]);
val wf_lemma = save_pop_thm "wf_lemma";

set_goal([],⌜∀r⦁ well_founded r ⇒ ∀s⦁ (∀t⦁ (∀u⦁ tc r u t ⇒ s u) ⇒ s t) ⇒ (∀e⦁ s e)⌝);
a (REPEAT strip_tac THEN fc_tac [tcwf_lemma1]);
a (spec_nth_asm_tac 2 ⌜e⌝);
a (list_spec_nth_asm_tac 3 [⌜e⌝,⌜s⌝,⌜u⌝]);
a (spec_nth_asm_tac 7 ⌜y⌝);
a (spec_nth_asm_tac 4 ⌜u'⌝);
val tcwf_lemma2 = save_pop_thm "tcwf_lemma2";
=TEX
}%\ignore

\ignore{
=SML
set_goal([],⌜∀r⦁ well_founded r ⇒ well_founded (tc r)⌝);
a (strip_tac THEN strip_tac
	THEN fc_tac [tcwf_lemma1]);
a (rewrite_tac [get_spec ⌜well_founded⌝]);
a (REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (list_spec_nth_asm_tac 4 [⌜x⌝,⌜s⌝,⌜y⌝]);
a (spec_nth_asm_tac 6 ⌜y'⌝);
a (spec_nth_asm_tac 4 ⌜y''⌝);
val wf_tc_wf_thm = save_pop_thm "wf_tc_wf_thm";
=TEX
}%\ignore
Now we prove that if the transitive closure of a relation is well-founded then so must be the relation.

=GFT
⦏tc_wf_wf_thm⦎ = ⊢ ∀ r⦁ well_founded (tc r) ⇒ well_founded r
=TEX

\ignore{
=SML

set_goal([], ⌜∀r⦁ well_founded (tc r) ⇒ well_founded r⌝);
a (rewrite_tac [get_spec ⌜well_founded⌝]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜s⌝);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 3 ⌜x'⌝);
a (all_asm_fc_tac [tc_incr_thm]);
a (all_asm_fc_tac []);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
val tc_wf_wf_thm = save_pop_thm "tc_wf_wf_thm";
=TEX
}%\ignore

\ignore{
=SML
set_goal([],⌜∀r⦁ well_founded r ⇒ twfp (tc r)⌝);
a (REPEAT strip_tac);
a (fc_tac [wf_tc_wf_thm]);
a (asm_rewrite_tac [get_spec ⌜twfp⌝, tran_tc_thm]);
val tc_wf_twf_thm = save_pop_thm "tc_wf_twf_thm";
=TEX
}%\ignore

\subsection{Induction Tactics etc.}

We here define a general tactic for performing induction using some well-founded relation.
The following function (I think these things are called "THM-TACTICAL"s) must be given a theorem which asserts that some relation is well-founded, and then a THM-TACTIC (which determines what is done with the induction assumption), and then a term which is the variable to induct over, and will then facilitate an inductive proof of the current goal using that theorem.
=SML
fun ⦏WF_INDUCTION_T2⦎ (thm : THM) (ttac : THM -> TACTIC) : TERM -> TACTIC =
 let	fun bad_thm thm = thm_fail "WF_INDUCTION_T2" 29021 [thm];
	val (wf, r) = (dest_app (concl thm))
		handle Fail _ => bad_thm thm;
	val sthm = ∀_elim r wf_lemma
		handle Fail _ => bad_thm thm;
	val ithm = ⇒_elim sthm thm
		handle Fail _ => bad_thm thm;
 in GEN_INDUCTION_T ithm ttac
 end;

fun ⦏WFCV_INDUCTION_T⦎ (thm : THM) (ttac : THM -> TACTIC) : TERM -> TACTIC =
 let	fun bad_thm thm = thm_fail "WFCV_INDUCTION_T" 29021 [thm];
	val (wf, r) = (dest_app (concl thm))
		handle Fail _ => bad_thm thm;
	val sthm = ∀_elim r tcwf_lemma2
		handle Fail _ => bad_thm thm;
	val ithm = ⇒_elim sthm thm
		handle Fail _ => bad_thm thm;
 in GEN_INDUCTION_T ithm ttac
 end;
=TEX

And now we make a tactic out of that (basically by saying "strip the induction hypothesis into the assumptions").

=SML
fun ⦏wf_induction_tac⦎ (thm : THM) : TERM -> TACTIC = (
	let	val ttac = (WF_INDUCTION_T2 thm strip_asm_tac)
			handle ex => reraise ex "wf_induction_tac";
	in
	fn tm =>
	let	val tac = (ttac tm) handle ex => reraise ex "wf_induction_tac";
	in	fn gl => ((tac gl) handle ex => reraise ex "wf_induction_tac")
	end
	end
);

fun ⦏wfcv_induction_tac⦎ (thm : THM) : TERM -> TACTIC = (
	let	val ttac = (WFCV_INDUCTION_T thm strip_asm_tac)
			handle ex => reraise ex "wfcv_induction_tac";
	in
	fn tm =>
	let	val tac = (ttac tm) handle ex => reraise ex "wfcv_induction_tac";
	in	fn gl => ((tac gl) handle ex => reraise ex "wfcv_induction_tac")
	end
	end
);
=TEX

\subsection{Well-foundedness and Induction}

The following proof shows how the above induction tactic can be used.
The theorem can be paraphrased loosely along the lines that there are no bottomless descending chains in a well-founded relation.
We think of a bottomless descending chain as a non-empty set (represented by a property called "p") every element of which is preceded by an element under the transitive closure of r.

\ignore{
=SML
set_goal([], ⌜∀r⦁ well_founded r ⇒ ∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ tc r y x ∧ ∃z⦁ p z ∧ r z y⌝);
a (strip_tac THEN strip_tac THEN strip_tac);
a (wfcv_induction_tac (asm_rule ⌜well_founded r⌝) ⌜x⌝);
a contr_tac;
a (all_asm_fc_tac[]);
a (spec_nth_asm_tac 6 ⌜v⌝);
a (SPEC_NTH_ASM_T 1 ⌜λx⦁ p x ∧ tc r x v⌝ ante_tac
	THEN rewrite_tac[]
	THEN REPEAT strip_tac);
a (∃_tac ⌜z⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [tc_incr_thm]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 7 ⌜y⌝);
a (∃_tac ⌜z'⌝ THEN asm_rewrite_tac[]);
a (lemma_tac ⌜tc r z' y⌝ THEN1 fc_tac [tc_incr_thm]);
a (all_fc_tac [tran_tc_thm2]);
val wf_nochain_thm = save_pop_thm "wf_nochain_thm";
=TEX
}%\ignore

Now a shorter formulation of bottomless pits.

\ignore{
=SML
set_goal([], ⌜∀r⦁ well_founded r ⇒ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ ∃z⦁ p z ∧ r z y⌝);
a (contr_tac);
a (lemma_tac ⌜∀x⦁ ¬ p x⌝ THEN1 (strip_tac
	THEN wfcv_induction_tac (asm_rule ⌜well_founded r⌝) ⌜x⌝));
(* *** Goal "1" *** *)
a (contr_tac
	THEN REPEAT (all_asm_fc_tac[tc_incr_thm]));
(* *** Goal "2" *** *)
a (REPEAT (all_asm_fc_tac[]));
val wf_wf_thm = save_pop_thm "wf_wf_thm";
=TEX
}%\ignore

Next we prove the converse, that the lack of bottomless pits entails well-foundedness.

\ignore{
=SML
set_goal([], ⌜∀r⦁ (∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ tc r y x ∧ ∃z⦁ p z ∧ r z y) ⇒ well_founded r⌝);
a (rewrite_tac [get_spec ⌜well_founded⌝]);
a contr_tac;
a (DROP_NTH_ASM_T 3 ante_tac
	THEN rewrite_tac[]
	THEN strip_tac);
a (∃_tac ⌜x⌝
	THEN rewrite_tac[]);
a (lemma_tac ⌜∃rel⦁ rel = λ v w⦁ ¬ s v ∧ ¬ s w ∧ r v w⌝
	THEN1 prove_∃_tac);
a (∃_tac ⌜λq⦁ tc rel q x⌝	THEN rewrite_tac[]);
a (spec_nth_asm_tac 3 ⌜x⌝);
a (∃_tac ⌜y⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜rel y x⌝ THEN1 asm_rewrite_tac[]);
a (all_asm_fc_tac [tc_incr_thm]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜∀x y⦁ rel x y ⇒ r x y⌝
	THEN1 (strip_tac THEN strip_tac
	THEN asm_rewrite_tac[] THEN REPEAT strip_tac));
a (all_fc_tac [tc_mono_thm]);
(* *** Goal "3" *** *)
a (lemma_tac ⌜¬ s y'⌝);
(* *** Goal "3.1" *** *)
a (lemma_tac ⌜∀ x y⦁ rel x y ⇒ ¬ s x⌝
	THEN1
	(REPEAT ∀_tac
	THEN asm_rewrite_tac []
	THEN REPEAT strip_tac));
a (all_asm_fc_tac[rewrite_rule[](list_∀_elim [⌜rel⌝, ⌜λx⦁¬ s x⌝] tc_p_thm)]);
(* *** Goal "3.2" *** *)
a (spec_nth_asm_tac 7 ⌜y'⌝);
a (∃_tac ⌜y''⌝ THEN REPEAT strip_tac);
a (lemma_tac ⌜tc rel y'' y'⌝);
(* *** Goal "3.2.1" *** *)
a (lemma_tac ⌜rel y'' y'⌝
	THEN1 asm_rewrite_tac[]);
a (all_asm_fc_tac[tc_incr_thm]);
(* *** Goal "3.2.2" *** *)
a (all_asm_fc_tac[tran_tc_thm2]);
val nochain_wf_thm = save_pop_thm "nochain_wf_thm";
=TEX
}%\ignore

Now with second order foundation.
\ignore{
=SML
set_goal([], ⌜(¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ ∃z⦁ p z ∧ r z y) ⇒ well_founded r⌝);
a (rewrite_tac [get_spec ⌜well_founded⌝]
	THEN REPEAT strip_tac);
a (SPEC_NTH_ASM_T 2 ⌜λx⦁ ¬ s x⌝ ante_tac
	THEN rewrite_tac[] THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (spec_nth_asm_tac 4 ⌜y⌝);
a (spec_nth_asm_tac 3 ⌜y'⌝);
val wf_induct_thm = save_pop_thm "wf_induct_thm";
=TEX
}%\ignore

Try a weaker hypothesis.

\ignore{
=SML
set_goal([], ⌜∀r⦁ (∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ ∃z⦁ p z ∧ r z y) ⇒ well_founded r⌝);
a (rewrite_tac [get_spec ⌜well_founded⌝]);
a contr_tac;
a (DROP_NTH_ASM_T 3 ante_tac
	THEN rewrite_tac[]
	THEN strip_tac);
a (lemma_tac ⌜∃rel⦁ rel = λ v w⦁ ¬ s v ∧ ¬ s w ∧ r v w⌝
	THEN1 prove_∃_tac);
a (∃_tac ⌜λq⦁ tc rel q x⌝	THEN rewrite_tac[]);
a (spec_nth_asm_tac 3 ⌜x⌝);
a (∃_tac ⌜y⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜rel y x⌝ THEN1 asm_rewrite_tac[]);
a (all_asm_fc_tac [tc_incr_thm]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜∀ x y⦁ rel x y ⇒ ¬ s x⌝
	THEN1
	(REPEAT ∀_tac
	THEN asm_rewrite_tac []
	THEN REPEAT strip_tac));
a (all_asm_fc_tac[rewrite_rule[](list_∀_elim [⌜rel⌝, ⌜λx⦁¬ s x⌝] tc_p_thm)]);
a (spec_nth_asm_tac 8 ⌜y'⌝);
a (∃_tac ⌜y''⌝ THEN REPEAT strip_tac);
a (lemma_tac ⌜rel y'' y'⌝ THEN1 asm_rewrite_tac[]);
a (lemma_tac ⌜tc rel y'' y'⌝ THEN1 all_asm_fc_tac[tc_incr_thm]);
a (all_asm_fc_tac[tran_tc_thm2]);
val nochain_wf_thm2 = save_pop_thm "nochain_wf_thm2";
=TEX
}%\ignore

\subsection{Bottomless Pits and Minimal Elements}

The following theorem states something like that if there are no unending downward chains then every "set" has a minimal element.

\ignore{
=SML
set_goal([], ⌜∀r⦁(∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ tc r y x ∧ ∃z⦁ p z ∧ r z y)
	⇒ ∀x⦁ (∃y⦁ r y x) ⇒ ∃z⦁ r z x ∧ ¬∃v⦁ r v z ∧ r v x⌝);
a contr_tac;
a (DROP_NTH_ASM_T 3 ante_tac
	THEN rewrite_tac[]
	THEN REPEAT strip_tac
	THEN rewrite_tac[]
);
a (∃_tac ⌜x⌝
	THEN ∃_tac ⌜λw⦁ r w x⌝
	THEN ∃_tac ⌜y⌝
	THEN asm_rewrite_tac[]);
a (strip_tac THEN asm_rewrite_tac[]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_asm_fc_tac [tc_incr_thm]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2  ⌜y'⌝);
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
val nochain_min_thm = save_pop_thm "nochain_min_thm";
=TEX
}%\ignore

A second order version with the weaker bottomless pits can be formulated as follows:

\ignore{
=SML
set_goal([], ⌜∀r⦁(∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ ∃z⦁ p z ∧ r z y)
	⇒ ∀p⦁ (∃y⦁ p y) ⇒ ∃z⦁ p z ∧ ¬∃v⦁ r v z ∧ p v⌝);
a contr_tac;
a (DROP_NTH_ASM_T 3 ante_tac
	THEN rewrite_tac[]
	THEN REPEAT strip_tac
);
a (∃_tac ⌜p⌝
	THEN ∃_tac ⌜y⌝
	THEN asm_rewrite_tac[]);
a (REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜y'⌝);
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
val nochain_min_thm2 = save_pop_thm "nochain_min_thm2";
=TEX
}%\ignore

It follows that all non-empty collections of predecessors under a well-founded relation have minimal elements.

\ignore{
=SML
set_goal([], ⌜∀r⦁ well_founded r ⇒ ∀x⦁ (∃y⦁ r y x) ⇒ ∃z⦁ r z x ∧ ¬∃v⦁ r v z ∧ r v x⌝);
a (REPEAT_N 2 strip_tac);
a (strip_asm_tac ( ∀_elim ⌜r⌝ wf_nochain_thm));
a (ante_tac (∀_elim ⌜r⌝ nochain_min_thm));
a (GET_NTH_ASM_T 1 ante_tac);
a (rewrite_tac [prove_rule [] ⌜∀a b⦁ a ⇒ (a ⇒ b) ⇒ b⌝ ]);
val wf_min_thm = save_pop_thm "wf_min_thm";
=TEX
}%\ignore

But the converse does not hold.

\ignore{
=SML
set_goal([], ⌜∃r: BOOL→BOOL→BOOL⦁(∀x⦁ (∃y⦁ r y x) ⇒ ∃z⦁ r z x ∧ ¬∃v⦁ r v z ∧ r v x)
	∧ ¬ well_founded r⌝);
a (∃_tac ⌜λx y:BOOL⦁ y⌝
	THEN rewrite_tac [get_spec ⌜well_founded⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜F⌝ THEN asm_rewrite_tac []);
(* *** Goal "2" *** *)
a (∃_tac ⌜$¬⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (spec_nth_asm_tac 1  ⌜x⌝);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜T⌝ THEN rewrite_tac[]);
val minr_not_wf_thm = save_pop_thm "minr_not_wf_thm";
=TEX
}%\ignore

\subsection{Restrictions of Well-Founded Relations}

In this section we show that a restriction of a well-founded relation is well-founded.

\ignore{
=SML
set_goal([], ⌜∀r⦁ well_founded r ⇒ ∀r2⦁ well_founded (λx y⦁ r2 x y ∧ r x y)⌝);
a (REPEAT strip_tac);
a (bc_tac [nochain_wf_thm]);
a (fc_tac [wf_nochain_thm]);
a (REPEAT strip_tac);
a (list_spec_nth_asm_tac 2 [⌜p⌝, ⌜x⌝, ⌜v⌝]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 3 ⌜y⌝);
a (lemma_tac ⌜∀ x y⦁ (λ x y⦁ r2 x y ∧ r x y) x y ⇒ r x y⌝
	THEN1 (rewrite_tac[] THEN REPEAT strip_tac));
a (FC_T fc_tac [tc_mono_thm]);
(* *** Goal "2" *** *)
a (SPEC_NTH_ASM_T 3 ⌜y⌝ ante_tac
	THEN (rewrite_tac []) THEN REPEAT strip_tac);
a (spec_nth_asm_tac 5 ⌜z⌝);
val wf_restrict_wf_thm = save_pop_thm "wf_restrict_wf_thm";
=IGN
set_goal([], ⌜∀r⦁ well_founded r ⇒ ∀r2⦁ well_founded (λx y⦁ r2 x y ∧ r x y)⌝);
a (REPEAT strip_tac);
a (bc_tac [wf_induct_thm]);
a (fc_tac [wf_nochain_thm]);
a (REPEAT strip_tac);
a (list_spec_nth_asm_tac 2 [⌜p⌝, ⌜x⌝, ⌜v⌝]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 3 ⌜y⌝);
a (lemma_tac ⌜∀ x y⦁ (λ x y⦁ r2 x y ∧ r x y) x y ⇒ r x y⌝
	THEN1 (rewrite_tac[] THEN REPEAT strip_tac));
a (FC_T fc_tac [tc_mono_thm]);
(* *** Goal "2" *** *)
a (SPEC_NTH_ASM_T 3 ⌜y⌝ ante_tac
	THEN (rewrite_tac []) THEN REPEAT strip_tac);
a (spec_nth_asm_tac 5 ⌜z⌝);
val wf_restrict_wf_thm = save_pop_thm "wf_restrict_wf_thm";
=TEX
}%\ignore

\subsection{Well Founded Recursion}

I have already proved a recursion theorem fairly closely following the formulation and proof devised by Tobias Nipkow for Isabelle-HOL.
There are two reasons for my wanting a different version of this result.
The Nipkow derived version works with relations rather than functions, and in my version the relations are ProofPower sets of pairs (I think in the original they were probably properties of pairs).
This is probably all easily modded into one which works directly with functions but I though it should be possible also to do a neater proof (the "proof" of the recursion theorem in Kunen is just a couple of lines).

The end result certainly looks nicer, we'll have to see whether it works out well in practice.
In particular the fixpoint operator simply takes a functional as an argument and delivers the fixed point as a result.
The functional which you give it as an argument, in the simple cases, is just what you get by abstracting the right hand side of a recursive definition on the name of the function (more complicated of course if a pattern matching definition is used).
The relation with respect to which the recursion is well-founded need only be mentioned when attempting to prove that this does yield a fixed point.

Another minor improvement is that I do not require the relation to be transitive.

This is the end result:

=GFT
⦏fixp_thm1⦎ = ⊢ ∀f r⦁ well_founded r ∧ f respects r ⇒ ∃g⦁ f g = g
=TEX

The proof is shorter than (my version of) the original, but by less than 20 percent.
I'm sure there's lots of scope for improvement.
(The isabelle version is much shorter than either.)

\subsubsection{Defining the Fixed Point Operator}

The main part of this is the proof that functionals which are well-founded with respect to some well-founded relation have fixed points.
This done, the operator ``fix'' is defined, which yields such a fixed point.

=SML
declare_infix (240, "respects");
=TEX

ⓈHOLCONST
│ $⦏respects⦎: (('a → 'b) → ('a → 'b)) → ('a → 'a → BOOL) → BOOL
├──────────────
│ ∀ f r ⦁ f respects r ⇔ ∀g h x⦁ (∀y⦁ (tc r) y x ⇒ g y = h y) ⇒ f g x = f h x
■

ⓈHOLCONST
│ ⦏fixed_below⦎: (('a → 'b) → ('a → 'b)) → ('a → 'a → BOOL) → ('a → 'b) → 'a → BOOL
├──────────────
│ ∀f r g x⦁ fixed_below f r g x ⇔ ∀y⦁ tc r y x ⇒ f g y = g y
■

ⓈHOLCONST
│ ⦏fixed_at⦎: (('a → 'b) → ('a → 'b)) → ('a → 'a → BOOL) → ('a → 'b) → 'a → BOOL
├───────────────
│ ∀f r g x⦁ fixed_at f r g x ⇔ fixed_below f r g x ∧ f g x = g x
■

\ignore{
=SML
set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀x g y⦁ fixed_below f r g x ∧ tc r y x ⇒ fixed_below f r g y⌝);
a (rewrite_tac [get_spec ⌜fixed_below⌝, get_spec ⌜$respects⌝]);
a (REPEAT strip_tac);
a (all_asm_fc_tac [tran_tc_thm2]);
a (all_asm_fc_tac []);
val fixed_below_lemma1 = save_pop_thm "fixed_below_lemma1";
=TEX
} % \ignore

\ignore{
=SML
set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀x g⦁ fixed_below f r g x ⇒ fixed_at f r (f g) x⌝);
a (rewrite_tac [get_spec ⌜fixed_below⌝, get_spec ⌜fixed_at⌝, get_spec ⌜$respects⌝]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (list_spec_nth_asm_tac 3 [⌜f g⌝, ⌜g⌝]);
a (spec_nth_asm_tac 1 ⌜y⌝);
a (all_asm_fc_tac [tran_tc_thm2]);
a (all_asm_fc_tac []);
(* *** Goal "2" *** *)
a (list_spec_nth_asm_tac 2 [⌜f g⌝, ⌜g⌝]);
a (all_asm_fc_tac []);
val fixed_at_lemma1 = save_pop_thm "fixed_at_lemma1";
=TEX
} %\ignore

\ignore{
=SML
set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀x g⦁ fixed_below f r g x ⇒ ∀y⦁ tc r y x ⇒ fixed_at f r g y⌝);
a (rewrite_tac [get_spec ⌜fixed_below⌝, get_spec ⌜fixed_at⌝, get_spec ⌜$respects⌝]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_asm_fc_tac [tran_tc_thm2]);
a (all_asm_fc_tac []);
(* *** Goal "2" *** *)
a (all_asm_fc_tac []);
val fixed_at_lemma2 = save_pop_thm "fixed_at_lemma2";
=TEX
} %\ignore

\ignore{
=SML
set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀x g⦁ (∀y⦁ tc r y x ⇒ fixed_at f r g y) ⇒ fixed_below f r g x⌝);
a (REPEAT_N 4 strip_tac);
a (rewrite_tac [get_spec ⌜fixed_at⌝, get_spec ⌜fixed_below⌝]);
a (REPEAT strip_tac);
a (all_asm_fc_tac []);
val fixed_at_lemma3 = save_pop_thm "fixed_at_lemma3";
=TEX
} %\ignore

\ignore{
=SML
set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀x g h⦁ fixed_below f r g x ∧ fixed_below f r h x ⇒ ∀z⦁ tc r z x ⇒ h z = g z⌝);
a (REPEAT_N 4 strip_tac);
a (wfcv_induction_tac (asm_rule ⌜well_founded r⌝) ⌜x⌝);
a (REPEAT strip_tac);
a (spec_nth_asm_tac 4 ⌜z⌝);
a (all_asm_fc_tac [fixed_below_lemma1]);
a (list_spec_nth_asm_tac 3 [⌜g⌝, ⌜h⌝]);
a (all_asm_fc_tac [fixed_at_lemma2]);
a (all_asm_fc_tac [get_spec ⌜fixed_at⌝]);
a (all_asm_fc_tac [fixed_at_lemma1]);
a (all_asm_fc_tac [get_spec ⌜$respects⌝]);
a (GET_ASM_T ⌜f h z = h z⌝ (rewrite_thm_tac o eq_sym_rule));
a (GET_ASM_T ⌜f h z = f g z⌝ rewrite_thm_tac);
a strip_tac;
val fixed_below_lemma2 =  save_pop_thm "fixed_below_lemma2";
=TEX
} %\ignore

\ignore{
=SML
set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀g x⦁ fixed_at f r g x ⇒ ∀y⦁ tc r y x ⇒ fixed_at f r g y⌝);
a (REPEAT strip_tac);
a (all_fc_tac [get_spec ⌜fixed_at⌝]);
a (all_fc_tac[fixed_at_lemma2]);
val fixed_at_lemma4 = save_pop_thm "fixed_at_lemma4";
=TEX
} %\ignore

\ignore{
=SML
set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀g h x⦁ fixed_at f r g x ∧ fixed_at f r h x ⇒ g x = h x⌝);
a (REPEAT strip_tac);
a (fc_tac[get_spec ⌜$respects⌝]);
a (all_fc_tac[get_spec ⌜fixed_at⌝]);
a (all_asm_fc_tac[get_spec ⌜$respects⌝]);
a (fc_tac[get_spec ⌜fixed_below⌝]);
a (fc_tac[fixed_below_lemma2]);
a (REPEAT_N 4 (EXTEND_PC_T1 "'mmp1" asm_fc_tac[]));
a (eq_sym_nth_asm_tac 14);
a (eq_sym_nth_asm_tac 13);
a (asm_rewrite_tac[]);
val fixed_at_lemma5 = save_pop_thm "fixed_at_lemma5";
=TEX
} %\ignore

\ignore{
=SML
set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀x⦁ (∀y⦁ tc r y x ⇒ ∃g⦁ fixed_at f r g y) ⇒ ∃g⦁ fixed_below f r g x⌝);
a (REPEAT strip_tac);
a (∃_tac ⌜λz⦁ (εh⦁ fixed_at f r h z) z⌝);
a (rewrite_tac [get_spec ⌜fixed_below⌝]
	THEN REPEAT strip_tac);
a (GET_ASM_T ⌜f respects r⌝ ante_tac
	THEN rewrite_tac [list_∀_elim [⌜f⌝, ⌜r⌝] (get_spec ⌜$respects⌝)]
	THEN strip_tac);
a (list_spec_nth_asm_tac 1 [⌜λ z⦁ (ε h⦁ fixed_at f r h z) z⌝, ⌜ε h⦁ fixed_at f r h y⌝]);
a (spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "1" *** *)
a (swap_nth_asm_concl_tac 1 THEN rewrite_tac[]);
a (asm_fc_tac[fixed_at_lemma4]);
a (list_spec_nth_asm_tac 2 [⌜f⌝, ⌜g⌝, ⌜y⌝, ⌜y'⌝]);
a (asm_fc_tac[]);
a (all_ε_tac);
(* *** Goal "1.1" *** *)
a (∃_tac ⌜g⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜g⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.3" *** *)
a (∃_tac ⌜g⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.4" *** *)
a (asm_tac fixed_at_lemma4);
a (list_spec_nth_asm_tac 1 [⌜f⌝, ⌜r⌝]);
a (list_spec_nth_asm_tac 1 [⌜ε h⦁ fixed_at f r h y⌝, ⌜y⌝]);
a (list_spec_nth_asm_tac 1 [⌜y'⌝]);
a (all_asm_fc_tac[fixed_at_lemma5]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
a (all_asm_fc_tac[]);
a (all_ε_tac);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜g⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (all_fc_tac[get_spec ⌜fixed_at⌝]);
val fixed_below_lemma3 = save_pop_thm "fixed_below_lemma3";
=TEX
} %\ignore

\ignore{
=SML
set_goal ([],⌜∀r f⦁ well_founded r ∧ f respects r
	⇒ ∀x⦁ ∃g⦁ fixed_below f r g x ⌝);
a (REPEAT_N 4 strip_tac);
a (wfcv_induction_tac (asm_rule ⌜well_founded r⌝) ⌜x⌝);
a (lemma_tac ⌜∀ u⦁ tc r u t ⇒ (∃ g⦁ fixed_at f r g u)⌝
	THEN1 (REPEAT strip_tac
	THEN all_asm_fc_tac[]
	THEN all_fc_tac[fixed_at_lemma1]
	THEN ∃_tac ⌜f g⌝
	THEN asm_rewrite_tac[]));
a (all_fc_tac[fixed_below_lemma3]);
a (∃_tac ⌜g⌝ THEN strip_tac);
val fixed_below_lemma4 = save_pop_thm "fixed_below_lemma4";
=TEX
} %\ignore

\ignore{
=SML
set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀x⦁ ∃g⦁ fixed_at f r g x ⌝);
a (REPEAT_N 4 strip_tac);
a (all_fc_tac[fixed_below_lemma4]);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (∃_tac ⌜f g⌝);
a (all_fc_tac[fixed_at_lemma1]);
val fixed_at_lemma6 = save_pop_thm "fixed_at_lemma6";
=TEX
} %\ignore

\ignore{
=SML
set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r ⇒
	∀x⦁ fixed_at f r (λ x⦁ (ε h⦁ fixed_at f r h x) x) x⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜∃g⦁ (λ x⦁ (ε h⦁ fixed_at f r h x) x) = g⌝ THEN1 prove_∃_tac);
a (asm_rewrite_tac[]);
a (wfcv_induction_tac (asm_rule ⌜well_founded r⌝) ⌜x⌝);
a (rewrite_tac[get_spec ⌜fixed_at⌝] THEN strip_tac);
(* *** Goal "1" *** *)
a (asm_fc_tac [list_∀_elim [⌜f⌝, ⌜r⌝] fixed_at_lemma3]);
a (asm_fc_tac []);
a (list_spec_nth_asm_tac 1 [⌜t⌝, ⌜g⌝]);
a (asm_fc_tac []);
(* *** Goal "2" *** *)
a (fc_tac [list_∀_elim [⌜f⌝, ⌜r⌝] fixed_at_lemma6]);
a (list_spec_nth_asm_tac 1 [⌜f⌝, ⌜t⌝]);
a (fc_tac [get_spec ⌜fixed_at⌝]);
a (lemma_tac ⌜g t = g' t⌝ THEN1 (GET_NTH_ASM_T 6 (rewrite_thm_tac o eq_sym_rule)));
(* *** Goal "2.1" *** *)
a (ε_tac ⌜ε h⦁ fixed_at f r h t⌝);
(* *** Goal "2.1.1" *** *)
a (∃_tac ⌜g'⌝  THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
a (fc_tac [get_spec ⌜fixed_at⌝]);
a (fc_tac [fixed_at_lemma5]);
a (list_spec_nth_asm_tac 1 [⌜f⌝, ⌜ε h⦁ fixed_at f r h t⌝, ⌜t⌝, ⌜g'⌝]);
(* *** Goal "2.2" *** *)
a (fc_tac [get_spec ⌜$respects⌝]);
a (list_spec_nth_asm_tac 1 [⌜t⌝, ⌜g⌝, ⌜g'⌝]);
(* *** Goal "2.2.1" *** *)
a (asm_fc_tac []);
a (asm_fc_tac [fixed_at_lemma4]);
a (list_spec_nth_asm_tac 1 [⌜f⌝, ⌜g'⌝, ⌜t⌝, ⌜y⌝]);
a (asm_fc_tac [fixed_at_lemma5]);
a (REPEAT (asm_fc_tac[]));
(* *** Goal "2.2.2" *** *)
a (asm_rewrite_tac[]);
val fixed_lemma1 = save_pop_thm "fixed_lemma1";
=TEX
} %\ignore

\ignore{
=SML
set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r ⇒ ∃g⦁ f g = g⌝);
a (REPEAT strip_tac);
a (∃_tac ⌜λx⦁ (εh⦁ fixed_at f r h x) x⌝
	THEN rewrite_tac [ext_thm]
	THEN REPEAT strip_tac);
a (all_fc_tac [list_∀_elim [⌜f⌝, ⌜r⌝] fixed_lemma1]);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (all_fc_tac [get_spec ⌜fixed_at⌝]);
a (asm_rewrite_tac[]);
val fixp_thm1 = save_pop_thm "fixp_thm1";
=TEX
} %\ignore

\ignore{
=SML
set_goal ([],⌜∃fix⦁ ∀f r⦁	well_founded r ∧ f respects r
	⇒ f (fix f) = (fix f)⌝);
a (∃_tac ⌜λf⦁ εg⦁ f g = g⌝);
a (REPEAT strip_tac THEN rewrite_tac[]);
a (all_ε_tac);
a (all_fc_tac [fixp_thm1]);
a (∃_tac ⌜g⌝ THEN strip_tac);
val _ = save_cs_∃_thm (pop_thm ());
=TEX
} %\ignore

ⓈHOLCONST
│ ⦏fix⦎: (('a → 'b) → ('a → 'b)) → 'a → 'b
├──────────────
│ ∀f r⦁ well_founded r ∧ f respects r ⇒ f (fix f) = fix f
■

\subsubsection{Partial Functions}

Having reformulated the recursion theorem to work with total functions in HOL rather than relations, I later decided that I needed a version which supported the definition of functions over a subset of a type.

The application I am thinking of here is as follows.

A new type is to be defined.
The carrier is defined using induction.
One of the primitive operators over the new type must be defined inductively.
If it weren't primitive it could be defined by well founded induction over the new type, but given that it is primitive it has to be defined over the representation {\it set}.
I'm guessing a function is still required rather than a relation (it probably doesn't make much difference) but either way it will only be nicely behaved over the representation set.

I'm not sure that I have an example of that kind, but here is a better example.
If you want to code something into some membership structure, e.g. ``godelising'' the syntax of a language to prove a Tarski-like definability result, you don't want to make a new type of this inductively defined set, but you will need to define functions by recursion over the set.

There are some other things I want to try out at the same time.

They are:

\begin{itemize}
\item recovering the ``well-founded'' relation from the functor which is required to respect it, i.e. recovering the relation which it respects.
\item taking a fixed point which is a function not defined over the whole type, not even defined over some specified subset, but which is defined over the well-founded part of the dependency relation of the defining functor.
\end{itemize}

The possibility has arisen to take a fixpoint of this kind without consideration of well-foundedness, but taking a closure of the empty set under some functor derived from the defining functor.
I haven't yet got a very clear idea on this one, and don't know how closely this material comes to it.

Anyway, for starters I will try to formulate the revised fixedpoint conjecture.

\subsubsection{Extracting a Minimal Respected Relation}

ⓈHOLCONST
│ ⦏ResRelOfFunctor⦎: (('a → 'a) → ('a → 'a)) → ('a → 'a → BOOL)
├──────
│ ∀f x y⦁ ResRelOfFunctor f x y ⇔
│	∃g v⦁ ¬ f g y = f (λz⦁ if z = x then v else g z) y
■

\subsubsection{The Well-founded Part of a Relation}

ⓈHOLCONST
│ ⦏WfDomOf⦎: ('a → 'a → BOOL) → ('a → BOOL)
├──────
│ ∀r⦁ WfDomOf r =
│	(λ x⦁ ∀p⦁ (∀v⦁ (∀w⦁ r w v ⇒ p w) ⇒ p v) ⇒ p x)
■

ⓈHOLCONST
│ ⦏WfPartOf⦎: ('a → 'a → BOOL) → ('a → 'a → BOOL)
├──────
│ ∀r⦁ WfPartOf r = (λx y⦁ r x y ∧ WfDomOf r y)
■

Now we want a conjecture to the effect that any functor has a partial fixed point, i.e. a function whose behaviour over the well-founded part of its respected relation is fixed under the functor.

However, there is no point in doing that without checking that these definitions work.

=SML
val ResRelOfFunctor_def = get_spec ⌜ResRelOfFunctor⌝;
val WfPartOf_def = get_spec ⌜WfPartOf⌝;
val WfDomOf_def = get_spec ⌜WfDomOf⌝;
=IGN
set_goal([], ⌜∀r x y⦁ WfDomOf r y ∧ r x y ⇒ WfDomOf r x⌝);
a (rewrite_tac [WfDomOf_def] THEN REPEAT strip_tac);

set_goal([], ⌜∀r⦁ well_founded (WfPartOf r)⌝);
a (rewrite_tac [ResRelOfFunctor_def, WfDomOf_def, WfPartOf_def, get_spec ⌜well_founded⌝]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (SPEC_NTH_ASM_T 2 ⌜λz⦁ ¬ r y z⌝ ante_tac);
a (rewrite_tac[] THEN REPEAT strip_tac);
=TEX

\subsubsection{Respect Theorems}

Some theorems which help to prove that functions respect relations.

My first applications of the recursion theorem are in set theory, typically involving recursion which respects membership or its transitive closure.

\subsubsection{The Inverse of a Relation}

The following function takes a relation and a function and returns a function which maps each element in the domain of the relation to the relation which holds between a predecessor of that element and its value under the function.
i.e. it maps the function over the predecessors of the element and returns the result as a relation.
It may therefore be used to rephrase primitive recursive definitions, and so the result which follows may be used to establish the existence of functions defined by primitive recursion.

ⓈHOLCONST
│  ⦏relmap⦎ : ('a → 'a → BOOL) → ('a → 'b) → ('a → ('a → 'b → BOOL))
├───────────
│  ∀r f⦁ relmap r f = λx y z⦁ r y x ∧ z = f y
■

\ignore{
=SML
set_goal ([],⌜∀r g⦁ (λf⦁ g o (relmap r f)) respects r⌝);
a (rewrite_tac[get_spec ⌜$respects⌝, get_spec ⌜relmap⌝, get_spec ⌜$o⌝]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜(λ y z⦁ r y x ∧ z = g' y) = (λ y z⦁ r y x ∧ z = h y)⌝
	THEN1 rewrite_tac[ext_thm]);
(* *** Goal "1" *** *)
a (REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a (asm_fc_tac[tc_incr_thm]);
a (asm_fc_tac[]);
a (asm_rewrite_tac []);
(* *** Goal "1.2" *** *)
a (asm_fc_tac[tc_incr_thm]);
a (asm_fc_tac[]);
a (asm_rewrite_tac []);
(* *** Goal "2" *** *)
a (asm_rewrite_tac []);
val relmap_respect_thm = save_pop_thm "relmap_respect_thm";
=TEX
}%\ignore

\ignore{
=SML
set_goal([], ⌜∀f r1 r2⦁ f respects r1 ∧ (∀x y⦁ r1 x y ⇒ r2 x y) ⇒ f respects r2⌝);
a (rewrite_tac [get_spec ⌜$respects⌝] THEN REPEAT strip_tac);
a (fc_tac [tc_mono_thm]);
a (lemma_tac ⌜∀ y⦁ tc r1 y x ⇒ g y = h y⌝
	THEN1 REPEAT strip_tac
	THEN REPEAT (asm_fc_tac []));
val mono_respects_thm = save_pop_thm "mono_respects_thm";
=IGN
set_goal([], ⌜∀f s⦁ (∀r⦁ s r ⇒ f respects r) ⇒ f respects (λx y⦁ ∀r⦁ s r ⇒ r x y)⌝);
a (rewrite_tac [get_spec ⌜$respects⌝] THEN REPEAT strip_tac);
a (

=TEX
}%ignore

\section{Well-Founded Relations (II)}

This is a transcription of the treatment of well-foundedness on which "galactic" set theory was based (from rbjpub/pp/x002.xml).

One of the principle well-founded relations of interest in this application is $∈⋎g$, which has type

=GFT
ⓣGS → GS → BOOL⌝
=TEX

so I would like a version of "well-founded" which has type:

=GFT
ⓣ('a → 'a → BOOL) → BOOL⌝
=TEX

The new theory {\it wf\_relp} is first created.

=SML
open_theory "hol";
force_new_theory "⦏wf_relp⦎";
new_parent "tc";
=TEX

\ignore{
=SML
force_new_pc "'wf_relp";
merge_pcs ["'savedthm_cs_∃_proof"] "'wf_relp";
(* merge_pcs ["xl_cs_∃_conv"] "'wf_relp"; *)
set_merge_pcs ["hol", "'wf_relp"];
=TEX
}%ignore

\subsection{Well-Founded Relations}

Definition of well-founded and transitive-well-founded and proof that the transitive closure of a well-founded relation is transitive-well-founded.

ⓈHOLCONST
│ ⦏well_founded⦎: ('a → 'a → BOOL) → BOOL
├
│ ∀r⦁ well_founded r ⇔ ∀ s ⦁ (∀ x ⦁ (∀ y ⦁ r y x ⇒ s y) ⇒ s x) ⇒ ∀ x ⦁ s x
■

ⓈHOLCONST
│ ⦏twfp⦎: ('a → 'a → BOOL) → BOOL
├
│ ∀r⦁ twfp r ⇔ well_founded r ∧ trans r
■

The first thing I need to prove here is that the transitive closure of a well-founded relation is also well-founded.
This provides a form of induction with a stronger induction hypothesis.
Naturally we would expect this to be proven inductively and the question is therefore what property to use in the inductive proof, the observation that the transitive closure of a relation is well-founded is not explicitly the ascription of a property to the field of the relation.
The obvious method is to relativise the required result to the transitive closure of a set, giving a property of sets, and then to prove that this property is hereditary if the relation is well-founded.

=GFT
⦏tcwf_lemma1⦎ = 
	⊢ ∀s r⦁ well_founded r
		⇒ ∀x⦁ (∀y⦁ tc r y x ⇒ (∀z⦁ tc r z y ⇒ s z) ⇒ s y)
		⇒ (∀y⦁ tc r y x ⇒ s y)
⦏wf_lemma2⦎ =
	⊢ ∀ r⦁ well_founded r ⇒ (∀ s⦁ (∀ t⦁ (∀ u⦁ r u t ⇒ s u) ⇒ s t) ⇒ (∀ e⦁ s e))
⦏tcwf_lemma2⦎ =
	⊢ ∀r⦁ well_founded r
		⇒ ∀s⦁ (∀t⦁ (∀u⦁ tc r u t ⇒ s u) ⇒ s t)
		⇒ (∀e⦁ s e)
⦏wf_tc_wf_thm⦎ =
	⊢  ∀r⦁ well_founded (tc r) ⇒ well_founded r
=TEX

\ignore{
=SML
set_goal([],⌜∀s r⦁ well_founded r ⇒ ∀x⦁ (∀y⦁ tc r y x ⇒ (∀z⦁ tc r z y ⇒ s z) ⇒ s y)
	⇒ (∀y⦁ tc r y x ⇒ s y)⌝);
a (rewrite_tac [get_spec ⌜well_founded⌝]);
a (REPEAT_N 3 strip_tac);
a (SPEC_NTH_ASM_T 1 ⌜λx ⦁ (∀y⦁ tc r y x ⇒ (∀z⦁ tc r z y ⇒ s z) ⇒ s y)
	⇒ (∀y⦁ tc r y x ⇒ s y)⌝ ante_tac
	THEN rewrite_tac[]
	THEN REPEAT strip_tac);
a (fc_tac [list_∀_elim [⌜r⌝,⌜y⌝,⌜x⌝] tc_decomp_thm]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 7 ⌜y⌝);
(* *** Goal "1.1" *** *)
a (all_fc_tac [tran_tc_thm2]);
a (spec_nth_asm_tac 10 ⌜y''⌝);
a (asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a (spec_nth_asm_tac 7 ⌜y⌝);
a (spec_nth_asm_tac 3 ⌜z⌝);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 8 ⌜z⌝);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜tc r z x⌝
	THEN1 fc_tac [tc_incr_thm]);
a (lemma_tac ⌜tc r y'' x⌝
	THEN1 strip_asm_tac (list_∀_elim [⌜r⌝,⌜y''⌝,⌜z⌝,⌜x⌝] tran_tc_thm2));
a (spec_nth_asm_tac 12 ⌜y''⌝);
a (spec_nth_asm_tac 6 ⌜z'⌝);
(* *** Goal "2.2" *** *)
a (asm_fc_tac[]);
val tcwf_lemma1 = save_pop_thm "tcwf_lemma1";
=TEX

=SML
set_goal([],⌜∀r⦁ well_founded r ⇒ ∀s⦁ (∀t⦁ (∀u⦁ r u t ⇒ s u) ⇒ s t) ⇒ (∀e⦁ s e)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜well_founded⌝]);
val wf_lemma2 = save_pop_thm "wf_lemma2";
=TEX

=SML
set_goal([],⌜∀r⦁ well_founded r ⇒ ∀s⦁ (∀t⦁ (∀u⦁ tc r u t ⇒ s u) ⇒ s t) ⇒ (∀e⦁ s e)⌝);
a (REPEAT strip_tac THEN fc_tac [tcwf_lemma1]);
a (spec_nth_asm_tac 2 ⌜e⌝);
a (list_spec_nth_asm_tac 3 [⌜e⌝,⌜s⌝,⌜u⌝]);
a (spec_nth_asm_tac 7 ⌜y⌝);
a (spec_nth_asm_tac 4 ⌜u'⌝);
val tcwf_lemma2 = save_pop_thm "tcwf_lemma2";
=TEX

=SML
set_goal([],⌜∀r⦁ well_founded r ⇒ well_founded (tc r)⌝);
a (strip_tac THEN strip_tac
	THEN fc_tac [tcwf_lemma1]);
a (rewrite_tac [get_spec ⌜well_founded⌝]);
a (REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (list_spec_nth_asm_tac 4 [⌜x⌝,⌜s⌝,⌜y⌝]);
a (spec_nth_asm_tac 6 ⌜y'⌝);
a (spec_nth_asm_tac 4 ⌜y''⌝);
val wf_tc_wf_thm = save_pop_thm "wf_tc_wf_thm";
=TEX
}%ignore

Now we prove that if the transitive closure of a relation is well-founded then so must be the relation.

=GFT
⦏tc_wf_wf_thm⦎ =
	⊢ ∀r⦁ well_founded (tc r) ⇒ well_founded r

⦏tc_wf_twf_thm⦎ =
	⊢ ∀r⦁ well_founded r ⇒ twfp (tc r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ well_founded (tc r) ⇒ well_founded r⌝);
a (rewrite_tac [get_spec ⌜well_founded⌝]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜s⌝);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 3 ⌜x'⌝);
a (all_asm_fc_tac [tc_incr_thm]);
a (all_asm_fc_tac []);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
val tc_wf_wf_thm = save_pop_thm "tc_wf_wf_thm";
=TEX

=SML
set_goal([],⌜∀r⦁ well_founded r ⇒ twfp (tc r)⌝);
a (REPEAT strip_tac);
a (fc_tac [wf_tc_wf_thm]);
a (asm_rewrite_tac [get_spec ⌜twfp⌝, tran_tc_thm]);
val tc_wf_twf_thm = save_pop_thm "tc_wf_twf_thm";
=TEX
}%ignore

We here define a general tactic for performing induction using some well-founded relation.

The following function (I think these things are called ``THM-TACTICAL''s) must be given a theorem which asserts that some relation is well-founded, and then a THM-TACTIC (which determines what is done with the induction assumption), and then a term which is the variable to induct over, and will then facilitate an inductive proof of the current goal using that theorem.

=SML
fun ⦏WF_INDUCTION_T⦎ (thm : THM) (ttac : THM -> TACTIC) : TERM -> TACTIC =
(	let	fun bad_thm thm = thm_fail "WF_INDUCTION_T" 29021 [thm];
		val (wf, r) = (dest_app (concl thm))
			handle Fail _ => bad_thm thm;
		val sthm = ∀_elim r wf_lemma2
			handle Fail _ => bad_thm thm;
		val ithm = ⇒_elim sthm thm
			handle Fail _ => bad_thm thm;
	in GEN_INDUCTION_T ithm ttac
	end
);

fun ⦏WFCV_INDUCTION_T⦎ (thm : THM) (ttac : THM -> TACTIC) : TERM -> TACTIC =
(	let	fun bad_thm thm = thm_fail "WFCV_INDUCTION_T" 29021 [thm];
		val (wf, r) = (dest_app (concl thm))
			handle Fail _ => bad_thm thm;
		val sthm = ∀_elim r tcwf_lemma2
			handle Fail _ => bad_thm thm;
		val ithm = ⇒_elim sthm thm
			handle Fail _ => bad_thm thm;
	in GEN_INDUCTION_T ithm ttac
	end
);
=TEX

And now we make a tactic out of that (basically by saying "strip the induction hypothesis into the assumptions").

=SML
fun ⦏wf_induction_tac⦎ (thm : THM) : TERM -> TACTIC = (
	let	val ttac = (WF_INDUCTION_T thm strip_asm_tac)
			handle ex => reraise ex "wf_induction_tac";
	in
	fn tm =>
	let	val tac = (ttac tm) handle ex => reraise ex "wf_induction_tac";
	in	fn gl => ((tac gl) handle ex => reraise ex "wf_induction_tac")
	end
	end
);

fun ⦏wfcv_induction_tac⦎ (thm : THM) : TERM -> TACTIC = (
	let	val ttac = (WFCV_INDUCTION_T thm strip_asm_tac)
			handle ex => reraise ex "wfcv_induction_tac";
	in
	fn tm =>
	let	val tac = (ttac tm) handle ex => reraise ex "wfcv_induction_tac";
	in	fn gl => ((tac gl) handle ex => reraise ex "wfcv_induction_tac")
	end
	end
);
=TEX

\subsubsection{Well-foundedness and Induction}

The following proof shows how the above induction tactic can be used.
The theorem can be paraphrased loosely along the lines that there are no bottomless descending chains in a well-founded relation.
We think of a bottomless descending chain as a non-empty set (represented by a property called "p") every element of which is preceded by an element under the transitive closure of r.

=GFT
⦏wf_nochain_thm⦎ =
	⊢ ∀r⦁ well_founded r
		⇒ ∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ tc r y x ∧ ∃z⦁ p z ∧ r z y
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ well_founded r ⇒
	∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ tc r y x ∧ ∃z⦁ p z ∧ r z y⌝);
a (strip_tac THEN strip_tac THEN strip_tac);
a (wfcv_induction_tac (asm_rule ⌜well_founded r⌝) ⌜x⌝);
a contr_tac;
a (all_asm_fc_tac[]);
a (spec_nth_asm_tac 6 ⌜v⌝);
a (SPEC_NTH_ASM_T 1 ⌜λx⦁ p x ∧ tc r x v⌝ ante_tac
	THEN rewrite_tac[]
	THEN REPEAT strip_tac);
a (∃_tac ⌜z⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [tc_incr_thm]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 7 ⌜y⌝);
a (∃_tac ⌜z'⌝ THEN asm_rewrite_tac[]);
a (lemma_tac ⌜tc r z' y⌝ THEN1 fc_tac [tc_incr_thm]);
a (all_fc_tac [tran_tc_thm2]);
val wf_nochain_thm = save_pop_thm "wf_nochain_thm";
=TEX
}%ignore

Now a shorter formulation of bottomless pits.

=GFT
⦏wf_wf_thm⦎ = 
	⊢ ∀r⦁ well_founded r
		⇒ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ ∃z⦁ p z ∧ r z y
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ well_founded r ⇒ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ ∃z⦁ p z ∧ r z y⌝);
a (contr_tac);
a (lemma_tac ⌜∀x⦁ ¬ p x⌝ THEN1 (strip_tac
	THEN wfcv_induction_tac (asm_rule ⌜well_founded r⌝) ⌜x⌝));
(* *** Goal "1" *** *)
a (contr_tac
	THEN REPEAT (all_asm_fc_tac[tc_incr_thm]));
(* *** Goal "2" *** *)
a (REPEAT (all_asm_fc_tac[]));
val wf_wf_thm = save_pop_thm "wf_wf_thm";
=TEX
}%ignore

=GFT
⦏nochain_wf_thm⦎ =
   ⊢ ∀r⦁ (∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ tc r y x ∧ ∃z⦁ p z ∧ r z y)
		⇒ well_founded r

⦏wf_⇔_nochain_thm⦎ =
   ⊢ ∀r⦁ well_founded r
         ⇔ (∀ x⦁ ¬ (∃ p v⦁ p v ∧ (∀ y⦁ p y ⇒ tc r y x ∧ (∃ z⦁ p z ∧ r z y))))
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ (∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ tc r y x ∧ ∃z⦁ p z ∧ r z y) ⇒ well_founded r⌝);
a (rewrite_tac [get_spec ⌜well_founded⌝]);
a contr_tac;
a (DROP_NTH_ASM_T 3 ante_tac
	THEN rewrite_tac[]
	THEN strip_tac);
a (∃_tac ⌜x⌝
	THEN rewrite_tac[]);
a (lemma_tac ⌜∃rel⦁ rel = λ v w⦁ ¬ s v ∧ ¬ s w ∧ r v w⌝
	THEN1 prove_∃_tac);
a (∃_tac ⌜λq⦁ tc rel q x⌝	THEN rewrite_tac[]);
a (spec_nth_asm_tac 3 ⌜x⌝);
a (∃_tac ⌜y⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜rel y x⌝ THEN1 asm_rewrite_tac[]);
a (all_asm_fc_tac [tc_incr_thm]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜∀x y⦁ rel x y ⇒ r x y⌝
	THEN1 (strip_tac THEN strip_tac
	THEN asm_rewrite_tac[] THEN REPEAT strip_tac));
a (all_fc_tac [tc_mono_thm]);
(* *** Goal "3" *** *)
a (lemma_tac ⌜¬ s y'⌝);
(* *** Goal "3.1" *** *)
a (lemma_tac ⌜∀ x y⦁ rel x y ⇒ ¬ s x⌝
	THEN1
	(REPEAT ∀_tac
	THEN asm_rewrite_tac []
	THEN REPEAT strip_tac));
a (all_asm_fc_tac[rewrite_rule[](list_∀_elim [⌜rel⌝, ⌜λx⦁¬ s x⌝] tc_p_thm)]);
(* *** Goal "3.2" *** *)
a (spec_nth_asm_tac 7 ⌜y'⌝);
a (∃_tac ⌜y''⌝ THEN REPEAT strip_tac);
a (lemma_tac ⌜tc rel y'' y'⌝);
(* *** Goal "3.2.1" *** *)
a (lemma_tac ⌜rel y'' y'⌝
	THEN1 asm_rewrite_tac[]);
a (all_asm_fc_tac[tc_incr_thm]);
(* *** Goal "3.2.2" *** *)
a (all_asm_fc_tac[tran_tc_thm2]);
val nochain_wf_thm = save_pop_thm "nochain_wf_thm";

set_goal([], ⌜∀r⦁ (well_founded r ⇔ ∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ tc r y x ∧ ∃z⦁ p z ∧ r z y)⌝);
a (strip_tac THEN strip_tac);
a (rewrite_tac [nochain_wf_thm, wf_nochain_thm]);
val wf_⇔_nochain_thm = save_pop_thm "wf_⇔_nochain_thm";
=TEX
}%ignore

Now with second order foundation.

=GFT
⦏wf_induct_thm⦎ = 
	⊢ (¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ ∃z⦁ p z ∧ r z y)
		⇒ well_founded r
=TEX

\ignore{
=SML
set_goal([], ⌜(¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ ∃z⦁ p z ∧ r z y) ⇒ well_founded r⌝);
a (rewrite_tac [get_spec ⌜well_founded⌝]
	THEN REPEAT strip_tac);
a (SPEC_NTH_ASM_T 2 ⌜λx⦁ ¬ s x⌝ ante_tac
	THEN rewrite_tac[] THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (spec_nth_asm_tac 4 ⌜y⌝);
a (spec_nth_asm_tac 3 ⌜y'⌝);
val wf_induct_thm = save_pop_thm "wf_induct_thm";
=TEX
}%ignore

Try a weaker hypothesis.

=GFT
⦏nochain_wf_thm2⦎ = 
	⊢ ∀r⦁ (∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ ∃z⦁ p z ∧ r z y)
		⇒ well_founded r
=TEX


\ignore{
=SML
set_goal([], ⌜∀r⦁ (∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ ∃z⦁ p z ∧ r z y) ⇒ well_founded r⌝);
a (rewrite_tac [get_spec ⌜well_founded⌝]);
a contr_tac;
a (DROP_NTH_ASM_T 3 ante_tac
	THEN rewrite_tac[]
	THEN strip_tac);
a (lemma_tac ⌜∃rel⦁ rel = λ v w⦁ ¬ s v ∧ ¬ s w ∧ r v w⌝
	THEN1 prove_∃_tac);
a (∃_tac ⌜λq⦁ tc rel q x⌝	THEN rewrite_tac[]);
a (spec_nth_asm_tac 3 ⌜x⌝);
a (∃_tac ⌜y⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜rel y x⌝ THEN1 asm_rewrite_tac[]);
a (all_asm_fc_tac [tc_incr_thm]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜∀ x y⦁ rel x y ⇒ ¬ s x⌝
	THEN1
	(REPEAT ∀_tac
	THEN asm_rewrite_tac []
	THEN REPEAT strip_tac));
a (all_asm_fc_tac[rewrite_rule[](list_∀_elim [⌜rel⌝, ⌜λx⦁¬ s x⌝] tc_p_thm)]);
a (spec_nth_asm_tac 8 ⌜y'⌝);
a (∃_tac ⌜y''⌝ THEN REPEAT strip_tac);
a (lemma_tac ⌜rel y'' y'⌝ THEN1 asm_rewrite_tac[]);
a (lemma_tac ⌜tc rel y'' y'⌝ THEN1 all_asm_fc_tac[tc_incr_thm]);
a (all_asm_fc_tac[tran_tc_thm2]);
val nochain_wf_thm2 = save_pop_thm "nochain_wf_thm2";
=TEX
}%ignore

\subsubsection{Bottomless Pits and Minimal Elements}

The following theorem states something like that if there are no unending downward chains then every "set" has a minimal element.

=GFT
⦏nochain_min_thm⦎ = 
	⊢ ∀r⦁(∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ tc r y x ∧ ∃z⦁ p z ∧ r z y)
		⇒ ∀x⦁ (∃y⦁ r y x) ⇒ ∃z⦁ r z x ∧ ¬∃v⦁ r v z ∧ r v x
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁(∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ tc r y x ∧ ∃z⦁ p z ∧ r z y)
	⇒ ∀x⦁ (∃y⦁ r y x) ⇒ ∃z⦁ r z x ∧ ¬∃v⦁ r v z ∧ r v x⌝);
a contr_tac;
a (DROP_NTH_ASM_T 3 ante_tac
	THEN rewrite_tac[]
	THEN REPEAT strip_tac
	THEN rewrite_tac[]
);
a (∃_tac ⌜x⌝
	THEN ∃_tac ⌜λw⦁ r w x⌝
	THEN ∃_tac ⌜y⌝
	THEN asm_rewrite_tac[]);
a (strip_tac THEN asm_rewrite_tac[]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_asm_fc_tac [tc_incr_thm]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2  ⌜y'⌝);
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
val nochain_min_thm = save_pop_thm "nochain_min_thm";
=TEX
}%ignore

A second order version with the weaker bottomless pits can be formulated as follows:

=GFT
⦏nochain_min_thm2⦎ =
	⊢ ∀r⦁(∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ ∃z⦁ p z ∧ r z y)
		⇒ ∀p⦁ (∃y⦁ p y) ⇒ ∃z⦁ p z ∧ ¬∃v⦁ r v z ∧ p v
=TEX


\ignore{
=SML
set_goal([], ⌜∀r⦁(∀x⦁ ¬∃p v⦁ p v ∧ ∀y⦁ p y ⇒ ∃z⦁ p z ∧ r z y)
	⇒ ∀p⦁ (∃y⦁ p y) ⇒ ∃z⦁ p z ∧ ¬∃v⦁ r v z ∧ p v⌝);
a contr_tac;
a (DROP_NTH_ASM_T 3 ante_tac
	THEN rewrite_tac[]
	THEN REPEAT strip_tac
);
a (∃_tac ⌜p⌝
	THEN ∃_tac ⌜y⌝
	THEN asm_rewrite_tac[]);
a (REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜y'⌝);
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
val nochain_min_thm2 = save_pop_thm "nochain_min_thm2";
=TEX
}%ignore

It follows that all non-empty collections of predecessors under a well-founded relation have minimal elements.

=GFT
⦏wf_min_thm⦎ = 
	⊢ ∀r⦁ well_founded r
		⇒ ∀x⦁ (∃y⦁ r y x) ⇒ ∃z⦁ r z x ∧ ¬∃v⦁ r v z ∧ r v x
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ well_founded r ⇒ ∀x⦁ (∃y⦁ r y x) ⇒ ∃z⦁ r z x ∧ ¬∃v⦁ r v z ∧ r v x⌝);
a (REPEAT_N 2 strip_tac);
a (strip_asm_tac ( ∀_elim ⌜r⌝ wf_nochain_thm));
a (ante_tac (∀_elim ⌜r⌝ nochain_min_thm));
a (GET_NTH_ASM_T 1 ante_tac);
a (rewrite_tac [prove_rule [] ⌜∀a b⦁ a ⇒ (a ⇒ b) ⇒ b⌝ ]);
val wf_min_thm = save_pop_thm "wf_min_thm";
=TEX
}%ignore

But the converse does not hold.

=GFT
⦏minr_not_wf_thm⦎ =
	⊢ ∃r: BOOL→BOOL→BOOL⦁
		(∀x⦁ (∃y⦁ r y x) ⇒ ∃z⦁ r z x ∧ ¬∃v⦁ r v z ∧ r v x)
		∧ ¬ well_founded r
=TEX

\ignore{
=SML
set_goal([], ⌜∃r: BOOL→BOOL→BOOL⦁(∀x⦁ (∃y⦁ r y x) ⇒
	∃z⦁ r z x ∧ ¬∃v⦁ r v z ∧ r v x) ∧ ¬ well_founded r⌝);
a (∃_tac ⌜λx y:BOOL⦁ y⌝
	THEN rewrite_tac [get_spec ⌜well_founded⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜F⌝ THEN asm_rewrite_tac []);
(* *** Goal "2" *** *)
a (∃_tac ⌜$¬⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (spec_nth_asm_tac 1  ⌜x⌝);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜T⌝ THEN rewrite_tac[]);
val minr_not_wf_thm = save_pop_thm "minr_not_wf_thm";
=TEX
}%ignore

\subsection{Some Consequences of Well Foundedness}

=GFT
⦏wf_not_refl_thm⦎ =
	⊢ ∀ r⦁ well_founded r ⇒ ¬ (∃ x⦁ r x x)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ r⦁ well_founded r ⇒ ¬ ∃x⦁ r x x⌝);
a (rewrite_tac [wf_⇔_nochain_thm] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (spec_nth_asm_tac 1 ⌜λw⦁ w = x⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac THEN POP_ASM_T ante_tac
	THEN rewrite_tac[]
	THEN strip_tac
	THEN asm_rewrite_tac[]);
a (contr_tac THEN fc_tac[tc_incr_thm]);
(* *** Goal "3" *** *)
a (SPEC_NTH_ASM_T 1 ⌜x⌝ ante_tac THEN rewrite_tac[]);
a (DROP_NTH_ASM_T 2 (rewrite_thm_tac o (rewrite_rule[])));
val wf_not_refl_thm = save_pop_thm "wf_not_refl_thm";
=TEX
}%ignore

\subsection{Ways of Constructing Well Founded Relations}

In this section we show that a restriction of a well-founded relation is well-founded.

=GFT
⦏wf_restrict_wf_thm⦎ =
	⊢ ∀r⦁ well_founded r ⇒ ∀r2⦁ well_founded (λx y⦁ r2 x y ∧ r x y)

⦏wf_image_wf_thm⦎ =
	⊢ ∀r⦁ well_founded r ⇒ ∀f⦁ well_founded (λx y⦁ r (f x) (f y))
=TEX

\ignore{
=SML
set_goal([], ⌜∀r⦁ well_founded r ⇒ ∀r2⦁ well_founded (λx y⦁ r2 x y ∧ r x y)⌝);
a (REPEAT strip_tac);
a (bc_tac [nochain_wf_thm]);
a (fc_tac [wf_nochain_thm]);
a (REPEAT strip_tac);
a (list_spec_nth_asm_tac 2 [⌜p⌝, ⌜x⌝, ⌜v⌝]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 3 ⌜y⌝);
a (lemma_tac ⌜∀ x y⦁ (λ x y⦁ r2 x y ∧ r x y) x y ⇒ r x y⌝
	THEN1 (rewrite_tac[] THEN REPEAT strip_tac));
a (FC_T fc_tac [tc_mono_thm]);
(* *** Goal "2" *** *)
a (SPEC_NTH_ASM_T 3 ⌜y⌝ ante_tac
	THEN (rewrite_tac []) THEN REPEAT strip_tac);
a (spec_nth_asm_tac 5 ⌜z⌝);
val wf_restrict_wf_thm = save_pop_thm "wf_restrict_wf_thm";

set_goal([], ⌜∀r⦁ well_founded r ⇒ ∀f⦁ well_founded (λx y⦁ r (f x) (f y))⌝);
a (rewrite_tac [wf_⇔_nochain_thm] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜f x⌝);
a (SPEC_NTH_ASM_T 1 ⌜λw⦁ ∃u⦁ w = f u ∧ p u⌝ (strip_asm_tac o (rewrite_rule[])));
a (spec_nth_asm_tac 1 ⌜f v⌝);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜v⌝);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 6 ⌜u⌝);
a (fc_tac [tc_induced_thm]);
a (var_elim_asm_tac ⌜y = f u⌝);
(* *** Goal "3" *** *)
a (var_elim_asm_tac ⌜y = f u⌝);
a (spec_nth_asm_tac 5 ⌜u⌝);
a (spec_nth_asm_tac 4 ⌜f u⌝);
(* *** Goal "3.1" *** *)
a (spec_nth_asm_tac 1 ⌜u⌝);
(* *** Goal "3.2" *** *)
a (spec_nth_asm_tac 5 ⌜f z⌝);
a (spec_nth_asm_tac 1 ⌜z⌝);
val wf_image_wf_thm = save_pop_thm "wf_image_wf_thm";
=TEX
}%ignore

\subsection{Proof Context}

In this section I will create a decent proof context for recursive definitions, eventually.

\subsubsection{Proof Context}

=SML
(* commit_pc "'wf_relp"; *)
=TEX

\subsection{Recursion Theorem}

=SML
open_theory "wf_relp";
force_new_theory "wf_recp";
=TEX

\ignore{
=SML
force_new_pc "'wf_recp";
merge_pcs ["'savedthm_cs_∃_proof"] "'wf_recp";
set_merge_pcs ["hol", "'wf_relp", "'wf_recp"];
=TEX
}%ignore

\subsubsection{Defining the Fixed Point Operator}

The main part of this is the proof that functionals which are well-founded with respect to some well-founded relation have fixed points.
This done, the operator "fix" is defined, which yields such a fixed point.


=SML
declare_infix (240, "respects");
=TEX

ⓈHOLCONST
│ $⦏respects⦎: (('a → 'b) → ('a → 'b)) → ('a → 'a → BOOL) → BOOL
├─────────────
│ ∀ f r ⦁ f respects r ⇔ ∀g h x⦁ (∀y⦁ (tc r) y x ⇒ g y = h y) ⇒ f g x = f h x
■

ⓈHOLCONST
│ ⦏fixed_below⦎: (('a → 'b) → ('a → 'b)) → ('a → 'a → BOOL) → ('a → 'b) → 'a → BOOL
├─────────────
│ ∀f r g x⦁ fixed_below f r g x ⇔ ∀y⦁ tc r y x ⇒ f g y = g y
■

ⓈHOLCONST
│ ⦏fixed_at⦎: (('a → 'b) → ('a → 'b)) → ('a → 'a → BOOL) → ('a → 'b) → 'a → BOOL
├─────────────
│ ∀f r g x⦁ fixed_at f r g x ⇔ fixed_below f r g x ∧ f g x = g x
■

=GFT
=TEX

\ignore{
=SML
set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀x g y⦁ fixed_below f r g x ∧ tc r y x ⇒ fixed_below f r g y⌝);
a (rewrite_tac [get_spec ⌜fixed_below⌝, get_spec ⌜$respects⌝]);
a (REPEAT strip_tac);
a (all_asm_fc_tac [tran_tc_thm2]);
a (all_asm_fc_tac []);
val fixed_below_lemma1 = save_pop_thm "fixed_below_lemma1";

set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀x g⦁ fixed_below f r g x ⇒ fixed_at f r (f g) x⌝);
a (rewrite_tac [get_spec ⌜fixed_below⌝, get_spec ⌜fixed_at⌝, get_spec ⌜$respects⌝]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (list_spec_nth_asm_tac 3 [⌜f g⌝, ⌜g⌝]);
a (spec_nth_asm_tac 1 ⌜y⌝);
a (all_asm_fc_tac [tran_tc_thm2]);
a (all_asm_fc_tac []);
(* *** Goal "2" *** *)
a (list_spec_nth_asm_tac 2 [⌜f g⌝, ⌜g⌝]);
a (all_asm_fc_tac []);
val fixed_at_lemma1 = save_pop_thm "fixed_at_lemma1";

set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀x g⦁ fixed_below f r g x ⇒ ∀y⦁ tc r y x ⇒ fixed_at f r g y⌝);
a (rewrite_tac [get_spec ⌜fixed_below⌝, get_spec ⌜fixed_at⌝, get_spec ⌜$respects⌝]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_asm_fc_tac [tran_tc_thm2]);
a (all_asm_fc_tac []);
(* *** Goal "2" *** *)
a (all_asm_fc_tac []);
val fixed_at_lemma2 = save_pop_thm "fixed_at_lemma2";

set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀x g⦁ (∀y⦁ tc r y x ⇒ fixed_at f r g y) ⇒ fixed_below f r g x⌝);
a (REPEAT_N 4 strip_tac);
a (rewrite_tac [get_spec ⌜fixed_at⌝, get_spec ⌜fixed_below⌝]);
a (REPEAT strip_tac);
a (all_asm_fc_tac []);
val fixed_at_lemma3 = save_pop_thm "fixed_at_lemma3";

set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀x g h⦁ fixed_below f r g x ∧ fixed_below f r h x ⇒ ∀z⦁ tc r z x ⇒ h z = g z⌝);
a (REPEAT_N 4 strip_tac);
a (wfcv_induction_tac (asm_rule ⌜well_founded r⌝) ⌜x⌝);
a (REPEAT strip_tac);
a (spec_nth_asm_tac 4 ⌜z⌝);
a (all_asm_fc_tac [fixed_below_lemma1]);
a (list_spec_nth_asm_tac 3 [⌜g⌝, ⌜h⌝]);
a (all_asm_fc_tac [fixed_at_lemma2]);
a (all_asm_fc_tac [get_spec ⌜fixed_at⌝]);
a (all_asm_fc_tac [fixed_at_lemma1]);
a (all_asm_fc_tac [get_spec ⌜$respects⌝]);
a (GET_ASM_T ⌜f h z = h z⌝ (rewrite_thm_tac o eq_sym_rule));
a (GET_ASM_T ⌜f h z = f g z⌝ rewrite_thm_tac);
a strip_tac;
val fixed_below_lemma2 =  save_pop_thm "fixed_below_lemma2";

set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀g x⦁ fixed_at f r g x ⇒ ∀y⦁ tc r y x ⇒ fixed_at f r g y⌝);
a (REPEAT strip_tac);
a (all_fc_tac [get_spec ⌜fixed_at⌝]);
a (all_fc_tac[fixed_at_lemma2]);
val fixed_at_lemma4 = save_pop_thm "fixed_at_lemma4";

set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀g h x⦁ fixed_at f r g x ∧ fixed_at f r h x ⇒ g x = h x⌝);
a (REPEAT strip_tac);
a (fc_tac[get_spec ⌜$respects⌝]);
a (all_fc_tac[get_spec ⌜fixed_at⌝]);
a (all_asm_fc_tac[get_spec ⌜$respects⌝]);
a (fc_tac[get_spec ⌜fixed_below⌝]);
a (fc_tac[fixed_below_lemma2]);
a (REPEAT_N 4 (EXTEND_PC_T1 "'mmp1" asm_fc_tac[]));
a (eq_sym_nth_asm_tac 14);
a (eq_sym_nth_asm_tac 13);
a (asm_rewrite_tac[]);
val fixed_at_lemma5 = save_pop_thm "fixed_at_lemma5";

set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀x⦁ (∀y⦁ tc r y x ⇒ ∃g⦁ fixed_at f r g y) ⇒ ∃g⦁ fixed_below f r g x⌝);
a (REPEAT strip_tac);
a (∃_tac ⌜λz⦁ (εh⦁ fixed_at f r h z) z⌝);
a (rewrite_tac [get_spec ⌜fixed_below⌝]
	THEN REPEAT strip_tac);
a (GET_ASM_T ⌜f respects r⌝ ante_tac
	THEN rewrite_tac [list_∀_elim [⌜f⌝, ⌜r⌝] (get_spec ⌜$respects⌝)]
	THEN strip_tac);
a (list_spec_nth_asm_tac 1 [⌜λ z⦁ (ε h⦁ fixed_at f r h z) z⌝, ⌜ε h⦁ fixed_at f r h y⌝]);
a (spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "1" *** *)
a (swap_nth_asm_concl_tac 1 THEN rewrite_tac[]);
a (asm_fc_tac[fixed_at_lemma4]);
a (list_spec_nth_asm_tac 2 [⌜f⌝, ⌜g⌝, ⌜y⌝, ⌜y'⌝]);
a (asm_fc_tac[]);
a (all_ε_tac);
(* *** Goal "1.1" *** *)
a (∃_tac ⌜g⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜g⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.3" *** *)
a (∃_tac ⌜g⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.4" *** *)
a (asm_tac fixed_at_lemma4);
a (list_spec_nth_asm_tac 1 [⌜f⌝, ⌜r⌝]);
a (list_spec_nth_asm_tac 1 [⌜ε h⦁ fixed_at f r h y⌝, ⌜y⌝]);
a (list_spec_nth_asm_tac 1 [⌜y'⌝]);
a (all_asm_fc_tac[fixed_at_lemma5]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
a (all_asm_fc_tac[]);
a (all_ε_tac);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜g⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (all_fc_tac[get_spec ⌜fixed_at⌝]);
val fixed_below_lemma3 = save_pop_thm "fixed_below_lemma3";
=SML
set_goal ([],⌜∀r f⦁ well_founded r ∧ f respects r
	⇒ ∀x⦁ ∃g⦁ fixed_below f r g x ⌝);
a (REPEAT_N 4 strip_tac);
a (wfcv_induction_tac (asm_rule ⌜well_founded r⌝) ⌜x⌝);
a (lemma_tac ⌜∀ u⦁ tc r u t ⇒ (∃ g⦁ fixed_at f r g u)⌝
	THEN1 (REPEAT strip_tac
	THEN all_asm_fc_tac[]
	THEN all_fc_tac[fixed_at_lemma1]
	THEN ∃_tac ⌜f g⌝
	THEN asm_rewrite_tac[]));
a (all_fc_tac[fixed_below_lemma3]);
a (∃_tac ⌜g⌝ THEN strip_tac);
val fixed_below_lemma4 = save_pop_thm "fixed_below_lemma4";
=SML
set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r
	⇒ ∀x⦁ ∃g⦁ fixed_at f r g x ⌝);
a (REPEAT_N 4 strip_tac);
a (all_fc_tac[fixed_below_lemma4]);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (∃_tac ⌜f g⌝);
a (all_fc_tac[fixed_at_lemma1]);
val fixed_at_lemma6 = save_pop_thm "fixed_at_lemma6";
=SML
set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r ⇒
	∀x⦁ fixed_at f r (λ x⦁ (ε h⦁ fixed_at f r h x) x) x⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜∃g⦁ (λ x⦁ (ε h⦁ fixed_at f r h x) x) = g⌝ THEN1 prove_∃_tac);
a (asm_rewrite_tac[]);
a (wfcv_induction_tac (asm_rule ⌜well_founded r⌝) ⌜x⌝);
a (rewrite_tac[get_spec ⌜fixed_at⌝] THEN strip_tac);
(* *** Goal "1" *** *)
a (asm_fc_tac [list_∀_elim [⌜f⌝, ⌜r⌝] fixed_at_lemma3]);
a (asm_fc_tac []);
a (list_spec_nth_asm_tac 1 [⌜t⌝, ⌜g⌝]);
a (asm_fc_tac []);
(* *** Goal "2" *** *)
a (fc_tac [list_∀_elim [⌜f⌝, ⌜r⌝] fixed_at_lemma6]);
a (list_spec_nth_asm_tac 1 [⌜f⌝, ⌜t⌝]);
a (fc_tac [get_spec ⌜fixed_at⌝]);
a (lemma_tac ⌜g t = g' t⌝ THEN1 (GET_NTH_ASM_T 6 (rewrite_thm_tac o eq_sym_rule)));
(* *** Goal "2.1" *** *)
a (ε_tac ⌜ε h⦁ fixed_at f r h t⌝);
(* *** Goal "2.1.1" *** *)
a (∃_tac ⌜g'⌝  THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
a (fc_tac [get_spec ⌜fixed_at⌝]);
a (fc_tac [fixed_at_lemma5]);
a (list_spec_nth_asm_tac 1 [⌜f⌝, ⌜ε h⦁ fixed_at f r h t⌝, ⌜t⌝, ⌜g'⌝]);
(* *** Goal "2.2" *** *)
a (fc_tac [get_spec ⌜$respects⌝]);
a (list_spec_nth_asm_tac 1 [⌜t⌝, ⌜g⌝, ⌜g'⌝]);
(* *** Goal "2.2.1" *** *)
a (asm_fc_tac []);
a (asm_fc_tac [fixed_at_lemma4]);
a (list_spec_nth_asm_tac 1 [⌜f⌝, ⌜g'⌝, ⌜t⌝, ⌜y⌝]);
a (asm_fc_tac [fixed_at_lemma5]);
a (REPEAT (asm_fc_tac[]));
(* *** Goal "2.2.2" *** *)
a (asm_rewrite_tac[]);
val fixed_lemma1 = save_pop_thm "fixed_lemma1";
=SML
set_goal ([],⌜∀f r⦁ well_founded r ∧ f respects r ⇒ ∃g⦁ f g = g⌝);
a (REPEAT strip_tac);
a (∃_tac ⌜λx⦁ (εh⦁ fixed_at f r h x) x⌝
	THEN rewrite_tac [ext_thm]
	THEN REPEAT strip_tac);
a (all_fc_tac [list_∀_elim [⌜f⌝, ⌜r⌝] fixed_lemma1]);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (all_fc_tac [get_spec ⌜fixed_at⌝]);
a (asm_rewrite_tac[]);
val fixp_thm1 = save_pop_thm "fixp_thm1";
=TEX
}%ignore

\ignore{
=SML
set_goal ([],⌜∃fix⦁ ∀f r⦁	well_founded r ∧ f respects r
	⇒ f (fix f) = (fix f)⌝);
a (∃_tac ⌜λf⦁ εg⦁ f g = g⌝);
a (REPEAT strip_tac THEN rewrite_tac[]);
a (all_ε_tac);
a (all_fc_tac [fixp_thm1]);
a (∃_tac ⌜g⌝ THEN strip_tac);
val _ = save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏fix⦎: (('a → 'b) → ('a → 'b)) → 'a → 'b
├
│ ∀f r⦁ well_founded r ∧ f respects r ⇒ f (fix f) = fix f
■

\subsubsection{The Inverse of a Relation}

The following function takes a relation and a function and returns a function which maps each element in the domain of the relation to the relation which holds between a predecessor of that element and its value under the function.
i.e. it maps the function over the predecessors of the element and returns the result as a relation.
It may therefore be used to rephrase primitive recursive definitions, and so the result which follows may be used to establish the existence of functions defined by primitive recursion.

ⓈHOLCONST
│  ⦏relmap⦎ : ('a → 'a → BOOL) → ('a → 'b) → ('a → ('a → 'b → BOOL))
├──────────────
│  ∀r f⦁ relmap r f = λx y z⦁ r y x ∧ z = f y
■

\ignore{
=SML
set_goal ([],⌜∀r g⦁ (λf⦁ g o (relmap r f)) respects r⌝);
a (rewrite_tac[get_spec ⌜$respects⌝, get_spec ⌜relmap⌝, get_spec ⌜$o⌝]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜(λ y z⦁ r y x ∧ z = g' y) = (λ y z⦁ r y x ∧ z = h y)⌝
	THEN1 rewrite_tac[ext_thm]);
(* *** Goal "1" *** *)
a (REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a (asm_fc_tac[tc_incr_thm]);
a (asm_fc_tac[]);
a (asm_rewrite_tac []);
(* *** Goal "1.2" *** *)
a (asm_fc_tac[tc_incr_thm]);
a (asm_fc_tac[]);
a (asm_rewrite_tac []);
(* *** Goal "2" *** *)
a (asm_rewrite_tac []);
val relmap_respect_thm = save_pop_thm "relmap_respect_thm";
=TEX
}%ignore

\subsubsection{Proof Context}

=SML
(* commit_pc "'wf_relp"; *)
=TEX



{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{tc.th}
\include{wfrel.th}
\include{wf_relp.th}
\include{wf_recp.th}
}  %\let

\twocolumn[\section{INDEX}\label{INDEX}]
{\small\printindex}

\end{document}
