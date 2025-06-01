=IGN
$Id: t003.doc,v 1.14 2012/08/11 21:01:53 rbj Exp $
open_theory "diffgeom";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℝ", "'savedthm_cs_∃_conv"];
set_flag ("pp_use_alias", false);
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{rbj}
\ftlinepenalty=9999
\tabstop=0.25in
\usepackage{A4}
\def\N{\mathbb{N}}
\def\D{\mathbb{D}}
\def\B{\mathbb{B}}
\def\R{\mathbb{R}}
\def\Z{\mathbb{Z}}
\def\Q{\mathbb{Q}}

\def\Hide#1{\relax}
\newcommand{\ignore}[1]{}

\title{Differential Geometry}
\author{Rob Arthan, Roger Jones}
\date{\ }

\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

\makeindex
\begin{document}
\vfill
\maketitle
\begin{abstract}
The theory of real vector spaces, norms and derivatives of functions between normed vector spaces as required for formal modelling of some physical theories.
\end{abstract}
\vfill
\begin{centering}

{\footnotesize

Created 2004/07/15

Last Change $ $Date: 2012/08/11 21:01:53 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t003.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t003.pdf}

$ $Id: t003.doc,v 1.14 2012/08/11 21:01:53 rbj Exp $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize

\end{centering}

\newpage
\tableofcontents
\newpage
%%%%
%%%%
\subsection*{To Do}
\begin{itemize}

\item

\end{itemize}

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\section{INTRODUCTION}

This document contains some first approaches to formalising differential fer use in the formalisation of Physics.
It is now of little interest, since my inclination now is to work with geometric algebra and geometric calculus.
However, though Rob Arthan has now formalised "The Geometric Algebra", there has been no progress (so far as I am aware) on differential geometry based on geometric algebra.

Create new theory ``diffgeom'', parents being ``group\_egs'' from \cite{LEMMA1/HOL/WRK068} and ``analysis'' from \cite{LEMMA1/HOL/WRK066}.

=SML
open_theory "rbjmisc";
open PreConsisProof; open UnifyForwardChain; open Trawling;
force_new_theory "diffgeom";
new_parent "geomalg";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℝ", "'savedthm_cs_∃_proof"];
set_flag ("pp_use_alias", false);
=TEX

\ignore{
=SML
=TEX
}%ignore

\section{MISCELLANEA}

\subsection{The Schwartz Inequality and Triangle Theorems}

\ignore{
=SML
set_goal([], ⌜∀a b x y A B C: ℝ⦁
	A = a^2 + b^2
∧	B = x^2 + y^2
∧	C = a *⋎R x + b *⋎R y
⇒	B *⋎R (A *⋎R B -⋎R C^2) = (B *⋎R a -⋎R C *⋎R x)^2 + (B *⋎R b -⋎R C *⋎R y)^2
⌝);
a (REPEAT strip_tac
	THEN asm_rewrite_tac[ℝ_ℕ_exp_square_thm]);
a (conv_tac (ONCE_MAP_C ℝ_anf_conv) THEN strip_tac);
val ⦏schwartz_2d_lemma1⦎ = pop_thm();
=TEX

=SML
set_goal([], ⌜∀u v x y A B C: ℝ⦁
	A = u^2 +⋎R v^2
∧	B = x^2 +⋎R y^2
∧	C = u *⋎R x +⋎R v *⋎R y
⇒	C^2 ≤ A *⋎R B
⌝);
a (REPEAT strip_tac THEN all_fc_tac [schwartz_2d_lemma1]);
a(lemma_tac⌜ℕℝ 0 ≤ B⌝ THEN1 asm_rewrite_tac[ℝ_sum_square_pos_thm]);
a(strip_asm_tac (list_∀_elim[⌜B⌝, ⌜ℕℝ 0⌝]ℝ_less_cases_thm));
(* *** Goal "1" *** *)
a(PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a(var_elim_nth_asm_tac 1);
a(DROP_NTH_ASM_T 3 (ante_tac o eq_sym_rule));
a (rewrite_tac [ℝ_sum_square_zero_thm] THEN strip_tac);
a(all_var_elim_asm_tac1 THEN rewrite_tac[]);
(* *** Goal "3" *** *)
a(lemma_tac ⌜ℕℝ 0 ≤ B*(A * B -⋎R C ^ 2) ⌝ THEN1
	(GET_NTH_ASM_T 3 rewrite_thm_tac THEN 
		rewrite_tac[ℝ_sum_square_pos_thm]));
a (POP_ASM_T (strip_asm_tac o (rewrite_rule[ℝ_prod_sign_iff_clauses]))
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val schwartz_2nd_thm = save_pop_thm "schwartz_2nd_thm";
=TEX

=SML
declare_infix (310, ".⋎i");
declare_infix (310, "+⋎V");
set_goal([], ⌜
	let (u,v) .⋎i (x,y) = u *⋎R x +⋎R v *⋎R y
	in ∀u v: ℝ × ℝ⦁ (u .⋎i v) ^ 2 ≤ (u .⋎i u) * (v .⋎i v)⌝);
a (rewrite_tac[let_def, ℝ_ℕ_exp_square_thm] THEN REPEAT strip_tac);
a (rewrite_tac [rewrite_rule [ℝ_ℕ_exp_square_thm]
	(list_∀_elim [⌜Fst u⌝, ⌜Snd u⌝, ⌜Fst v⌝, ⌜Snd v⌝,
		⌜Fst u ^⋎N 2 +⋎R Snd u ^⋎N 2⌝, ⌜Fst v ^⋎N 2 +⋎R Snd v ^⋎N 2⌝,
		⌜Fst u *⋎R Fst v +⋎R Snd u *⋎R Snd v⌝] schwartz_2nd_thm)]);
val schwartz_2nd_thm1 = save_pop_thm "schwartz_2nd_thm1";
=TEX

=SML
set_goal([], ⌜
	∀ $.⋎i⦁ (∀ u v x y:ℝ⦁ (u,v) .⋎i (x,y) = u *⋎R x +⋎R v *⋎R y)
	⇒ ∀u v: ℝ × ℝ⦁ (u .⋎i v) ^ 2 ≤ (u .⋎i u) * (v .⋎i v)⌝);
a (rewrite_tac[ℝ_ℕ_exp_square_thm] THEN REPEAT strip_tac);
a (once_rewrite_tac [prove_rule [] ⌜u = (Fst u, Snd u) ∧ v = (Fst v, Snd v)⌝]);
a (asm_rewrite_tac [rewrite_rule [ℝ_ℕ_exp_square_thm]
	(list_∀_elim [⌜Fst u⌝, ⌜Snd u⌝, ⌜Fst v⌝, ⌜Snd v⌝,
		⌜Fst u ^⋎N 2 +⋎R Snd u ^⋎N 2⌝, ⌜Fst v ^⋎N 2 +⋎R Snd v ^⋎N 2⌝,
		⌜Fst u *⋎R Fst v +⋎R Snd u *⋎R Snd v⌝] schwartz_2nd_thm)]);
val schwartz_2nd_thm1b = save_pop_thm "schwartz_2nd_thm1b";
=TEX

=SML
set_goal([], ⌜
	∀ $.⋎i⦁ (∀ u v x y:ℝ⦁ (u,v) .⋎i (x,y) = (u *⋎R x) +⋎R (v *⋎R y))
	∧	(∀u v x y:ℝ⦁(u,v) +⋎V (x,y) = (u +⋎R x, v +⋎R y))
	⇒ ∀x y: ℝ × ℝ⦁ (x +⋎V y) .⋎i (x +⋎V y) = (x .⋎i x) +⋎R (ℕℝ 2 *⋎R (x .⋎i y)) +⋎R (y .⋎i y)⌝);
a (REPEAT strip_tac);
a (once_rewrite_tac [prove_rule [] ⌜x = (Fst x, Snd x) ∧ y = (Fst y, Snd y)⌝]);
a (asm_rewrite_tac []);
a (ℝ_top_anf_tac THEN strip_tac);
val ip_distrib_thm = save_pop_thm "ip_distrib_thm";
=TEX
=SML
set_goal([], ⌜
	let (u,v) .⋎i (x,y) = u *⋎R x +⋎R v *⋎R y
	in let n (v: ℝ × ℝ) = SqrtA(v .⋎i v)
	in ∀u v: ℝ × ℝ⦁ Abs(u .⋎i v) ≤ (n u) *⋎R (n v)⌝);
a (rewrite_tac[let_def] THEN REPEAT strip_tac);
a (rewrite_tac [map_eq_sym_rule ℝ_sqrt_prod_thm]);
a (bc_tac [ℝ_square_≤_≤_thm]
	THEN TRY (rewrite_tac [
		ℝ_Abs_Norm_clauses,
		ℝ_prod_sign_iff_clauses,
		get_spec ⌜SqrtA⌝]));
a (rewrite_tac [	map_eq_sym_rule ℝ_abs_prod_thm,
		rewrite_rule [ℝ_ℕ_exp_square_thm]ℝ_abs_square_thm2,
		map_eq_sym_rule ℝ_sqrt_prod_thm,
		ℝ_sqrt_square_thm1]);
a (LEMMA_T ⌜Abs⋎R
               ((Fst u *⋎R Fst u +⋎R Snd u *⋎R Snd u)
                   *⋎R (Fst v *⋎R Fst v +⋎R Snd v *⋎R Snd v)) =
	     ((Fst u *⋎R Fst u +⋎R Snd u *⋎R Snd u)
                   *⋎R (Fst v *⋎R Fst v +⋎R Snd v *⋎R Snd v))⌝
		rewrite_thm_tac
	THEN_LIST [
		rewrite_tac [ℝ_abs_prod_thm],		
		rewrite_tac [rewrite_rule [let_def, ℝ_ℕ_exp_square_thm] schwartz_2nd_thm1]]);
a (lemma_tac ⌜ℕℝ 0 ≤⋎R Fst u *⋎R Fst u +⋎R Snd u *⋎R Snd u⌝
	THEN1 rewrite_tac [rewrite_rule [ℝ_ℕ_exp_square_thm] ℝ_sum_square_pos_thm]);
a (lemma_tac ⌜ℕℝ 0 ≤⋎R Fst v *⋎R Fst v +⋎R Snd v *⋎R Snd v⌝
	THEN1 rewrite_tac [rewrite_rule [ℝ_ℕ_exp_square_thm] ℝ_sum_square_pos_thm]);
a (asm_rewrite_tac [get_spec ⌜Abs⋎R⌝]);
val schwartz_2nd_thm2 = save_pop_thm "schwartz_2nd_thm2";
=TEX

=SML
set_goal([], ⌜
	∀ $.⋎i n⦁ (∀ u v x y:ℝ⦁ (u,v) .⋎i (x,y) = u *⋎R x +⋎R v *⋎R y)
	⇒ ∀u: ℝ × ℝ⦁ ℕℝ 0 ≤⋎R (u .⋎i u)⌝);
a (REPEAT strip_tac
	THEN once_rewrite_tac [prove_rule [] ⌜u = (Fst u, Snd u)⌝]
	THEN asm_rewrite_tac []
	THEN bc_tac [ℝ_sum_pos_thm]
	THEN rewrite_tac [rewrite_rule [ℝ_ℕ_exp_square_thm] ℝ_square_pos_thm]);
val ip_pos_lemma = pop_thm ();
=TEX

=SML
set_goal([], ⌜
	∀ $.⋎i n⦁ (∀ u v x y:ℝ⦁ (u,v) .⋎i (x,y) = u *⋎R x +⋎R v *⋎R y)
	∧ (∀v:ℝ × ℝ⦁ n v = SqrtA(v .⋎i v))
	⇒ ∀u: ℝ × ℝ⦁ ℕℝ 0 ≤⋎R n u⌝);
a (REPEAT strip_tac THEN asm_rewrite_tac [get_spec ⌜SqrtA⌝]);
val n_pos_lemma = pop_thm();
=TEX

=SML
set_goal([], ⌜
	∀ $.⋎i n⦁ (∀ u v x y:ℝ⦁ (u,v) .⋎i (x,y) = u *⋎R x +⋎R v *⋎R y)
	∧ (∀v:ℝ × ℝ⦁ n v = SqrtA(v .⋎i v))
	⇒ ∀u v: ℝ × ℝ⦁ (u .⋎i v) ≤ (n u) * (n v)⌝);
a (REPEAT strip_tac);
a (all_fc_tac [schwartz_2nd_thm1b]);
a (POP_ASM_T ante_tac
	THEN rewrite_tac [ℝ_ℕ_exp_square_thm]
	THEN GET_NTH_ASM_T 1 rewrite_thm_tac
	THEN strip_tac);
a (LEMMA_T ⌜SqrtA((u .⋎i v) *⋎R u .⋎i v) ≤⋎R SqrtA((u .⋎i u) *⋎R v .⋎i v)⌝ ante_tac);
(* *** Goal "1" *** *)
a (bc_tac [ℝ_sqrt_mono_thm]
	THEN1 rewrite_tac [rewrite_rule [ℝ_ℕ_exp_square_thm] ℝ_square_pos_thm]);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (rewrite_tac [ℝ_sqrt_square_thm1] THEN rewrite_tac [ℝ_sqrt_prod_thm]);
a (lemma_tac ⌜u .⋎i v ≤⋎R Abs⋎R (u .⋎i v)⌝ THEN1 rewrite_tac[ℝ_≤_abs_thm]);
a (strip_tac THEN all_fc_tac [ℝ_≤_trans_thm]);
val schwartz_2nd_thm2b = save_pop_thm "schwartz_2nd_thm2b";
=TEX

=SML
set_goal([],
	⌜∀$.⋎i $+⋎V n⦁
		(∀u v x y:ℝ⦁ (u,v) .⋎i (x,y) = u *⋎R x +⋎R v *⋎R y)
	∧	(∀u v x y:ℝ⦁(u,v) +⋎V (x,y) = (u +⋎R x, v +⋎R y))
	∧	(∀v:ℝ × ℝ⦁ n v = SqrtA(v .⋎i v))
	⇒	∀u v: ℝ × ℝ⦁ n (u +⋎V v)  ≤ (n u) + (n v)⌝);
a (REPEAT strip_tac THEN asm_rewrite_tac[]);
a (LEMMA_T ⌜SqrtA (u .⋎i u) +⋎R SqrtA (v .⋎i v)
	= SqrtA (u .⋎i u +⋎R ℕℝ 2 *⋎R (SqrtA (u .⋎i u)) *⋎R (SqrtA (v .⋎i v)) +⋎R v .⋎i v)⌝
	rewrite_thm_tac);
(* *** Goal "1" *** *)
a (bc_tac [ℝ_square_eq_thm2]
	THEN TRY (rewrite_tac [get_spec ⌜SqrtA⌝]));
(* *** Goal "1.1" *** *)
a (bc_tac [ℝ_sum_pos_thm] THEN rewrite_tac [get_spec ⌜SqrtA⌝]);
(* *** Goal "1.2" *** *)
a (rewrite_tac [map_eq_sym_rule ℝ_sqrt_prod_thm, ℝ_sqrt_square_thm1]);
a (rewrite_tac [ℝ_sqrt_prod_thm, ℝ_times_plus_distrib_thm]);
a (lemma_tac ⌜ℕℝ 0 ≤⋎R u .⋎i u ∧ ℕℝ 0 ≤⋎R v .⋎i v
	∧ ℕℝ 0 ≤⋎R SqrtA (u .⋎i u) ∧ ℕℝ 0 ≤⋎R SqrtA (v .⋎i v)⌝
	THEN1 (all_asm_fc_tac [ip_pos_lemma]
		THEN asm_rewrite_tac [get_spec ⌜SqrtA⌝]));
a (LEMMA_T ⌜Abs⋎R (u .⋎i u +⋎R ℕℝ 2 *⋎R SqrtA (u .⋎i u) *⋎R SqrtA (v .⋎i v) +⋎R v .⋎i v) =
	u .⋎i u +⋎R ℕℝ 2 *⋎R SqrtA (u .⋎i u) *⋎R SqrtA (v .⋎i v) +⋎R v .⋎i v⌝
	rewrite_thm_tac
	THEN1 (bc_tac [ℝ_abs_pos_id_thm, ℝ_sum_pos_thm, ℝ_sum_pos_thm, ℝ_sum_pos_thm]
		THEN TRY (asm_rewrite_tac[ℝ_prod_sign_iff_clauses])));
a (rewrite_tac [rewrite_rule [ℝ_ℕ_exp_square_thm] (get_spec ⌜SqrtA⌝)]);
a (LEMMA_T ⌜Abs⋎R (u .⋎i u) = u .⋎i u ∧ Abs⋎R (v .⋎i v) = v .⋎i v⌝ rewrite_thm_tac
	THEN1 (strip_tac THEN bc_tac [ℝ_abs_pos_id_thm]
		THEN all_asm_fc_tac [ip_pos_lemma]));
a (ℝ_top_anf_tac THEN strip_tac);
(* *** Goal "2" *** *)
a (lemma_tac ⌜ℕℝ 0 ≤⋎R (u +⋎V v) .⋎i (u +⋎V v)⌝
	THEN1 ALL_FC_T rewrite_tac [ip_pos_lemma]);
a (bc_tac [ℝ_sqrt_mono_thm] THEN TRY strip_tac);
a (LEMMA_T  ⌜(u +⋎V v) .⋎i (u +⋎V v) ≤⋎R u .⋎i u +⋎R ℕℝ 2 *⋎R (u .⋎i v) +⋎R v .⋎i v
	∧ u .⋎i u +⋎R ℕℝ 2 *⋎R (u .⋎i v) +⋎R v .⋎i v
		≤⋎R u .⋎i u +⋎R ℕℝ 2 *⋎R SqrtA (u .⋎i u) *⋎R SqrtA (v .⋎i v) +⋎R v .⋎i v⌝
	((MAP_EVERY asm_tac) o strip_∧_rule)
	THEN_LIST [strip_tac, all_asm_fc_tac [ℝ_≤_trans_thm]]);
(* *** Goal "2.1" *** *)
a (ALL_FC_T rewrite_tac [ip_distrib_thm]);
(* *** Goal "2.2" *** *)
a (rewrite_tac[]);
a (bc_tac [ℝ_times_mono_thm2] THEN1 rewrite_tac[]);
a (all_fc_tac [schwartz_2nd_thm2b]);
a (LIST_SPEC_NTH_ASM_T 1 [⌜u⌝, ⌜v⌝] ante_tac);
a (GET_NTH_ASM_T 3 pure_rewrite_thm_tac);
a (REPEAT strip_tac);
val triangle_ineq_thm = save_pop_thm "triangle_ineq_thm";
=TEX

=SML
set_goal([], ⌜
	let (u,v) .⋎i (x,y) = u *⋎R x +⋎R v *⋎R y
	and (u,v) +⋎V (x,y) = (u +⋎R x, v +⋎R y)
	in let n v = SqrtA(v .⋎i v)
	in ∀u v: ℝ × ℝ⦁ n (u +⋎V v)  ≤ (n u) + (n v)⌝);
a (rewrite_tac [let_def] THEN REPEAT strip_tac);
a (strip_asm_tac (
	list_∀_elim [⌜λ(u, v) (x, y)⦁ u *⋎R x +⋎R v *⋎R y⌝,
	⌜λ(u, v) (x, y)⦁ (u +⋎R x, v +⋎R y)⌝,
	⌜λ(u, v)⦁ SqrtA(u *⋎R u +⋎R v *⋎R v)⌝] triangle_ineq_thm)
	THEN TRY(swap_nth_asm_concl_tac 1
		THEN rewrite_tac[]
		THEN swap_nth_asm_concl_tac 1));
a (asm_rewrite_tac[]);
val triangle_ineq_thm2 = save_pop_thm "triangle_ineq_thm2";
=TEX

}%ignore

\section{VECTOR SPACES}

\subsection{Signature for Real Vector Spaces}

A candidate for being a vector space is something with the signature of a group together with an ℝ-action on the elements.

ⓈHOLLABPROD RVS─────────────────
│	Group⋎RVS	:'a GROUP;
│	Scale⋎RVS	:ℝ → 'a → 'a
■─────────────────────────

=SML
declare_alias("Grp", ⌜Group⋎RVS⌝);
declare_alias("Scale", ⌜Scale⋎RVS⌝);
=TEX

\ignore{
=SML
val ⦏grp_def⦎ = get_spec⌜Grp⌝;
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Plus⋎V⦎ :  'a → 'a → 'a RVS → 'a;
│ ⦏Minus⋎V⦎ :  'a → 'a RVS → 'a;
│ ⦏Subtract⋎V⦎ :  'a → 'a → 'a RVS → 'a;
│ ⦏0⋎V⦎ :  'a RVS → 'a;
│ ⦏Scale⋎V⦎ :  ℝ → 'a → 'a RVS → 'a
├──────
│ ∀ R⦁	  (∀v w⦁ Plus⋎V v w R = (v.w)(Grp R))
│ 	∧ (∀v⦁ Minus⋎V v R = (v ⋏~)(Grp R))
│	∧ (∀v w⦁ Subtract⋎V v w R = (v.(w ⋏~)(Grp R))(Grp R))
│	∧ 0⋎V R = Unit (Grp R)
│	∧ (∀x v⦁ Scale⋎V x v R = (Scale R) x v)
■

=SML
declare_infix(310, "*⋎s");
declare_alias("+", ⌜Plus⋎V⌝);
declare_alias("~", ⌜Minus⋎V⌝);
declare_alias("-", ⌜Subtract⋎V⌝);
declare_alias("*⋎s", ⌜Scale⋎V⌝);
=TEX

\subsection{Vector Space Laws}

For simplicity in using the theory, we ignore the carrier set of the group component and require the carrier set of a real vector space to be the universe of the type of the elements.
This makes working with subspaces harder theoretically, but that shouldn't matter much for RBJ's application.

ⓈHOLCONST
│ ⦏VS⋎R⦎ : 'a RVS SET
├──────
│ ∀ V⦁
│	V ∈ VS⋎R
│ ⇔	Grp V ∈ AbelianGroup
│ ∧	Car (Grp V) = Universe
│ ∧	(∀x v w⦁  ((x*⋎s v)V + (x*⋎s w)V)V = (x*⋎s(v + w) V) V)
│ ∧	(∀x y v⦁ ((x*⋎s v)V + (y*⋎s v)V)V  = ((x + y) *⋎s v) V)
│ ∧	(∀x y:ℝ; v⦁ (x*⋎s(y*⋎s v)V)V = ((x*y)*⋎s v)V)
│ ∧	(∀v⦁ (ℕℝ 1*⋎s v)V = v)
■

\ignore{
=SML
val ⦏vs_ops_def⦎ = get_spec⌜Plus⋎V⌝;
val ⦏vs_def⦎ = get_spec⌜VS⋎R⌝;
val ⦏rvs_def⦎ = get_spec⌜MkRVS⌝;
=TEX
=SML
set_goal([], ⌜∀ R: 'a RVS
     ⦁ (∀ v w:'a⦁ (v + w) R = (v . w) (Grp R))
         ∧ (∀ v⦁ ~ v R:'a = ($⋏~: 'a → 'a GROUP → 'a) v (Grp R))
         ∧ (∀ v:'a; w:'a⦁ (v - w) R:'a =
		($.:'a→ 'a → 'a GROUP → 'a)
		v
		(($⋏~: 'a → 'a GROUP → 'a) w (Grp R)) (Grp R))
         ∧ 0⋎V R = Unit (Grp R)
         ∧ (∀ x v⦁ (x *⋎s v) R = (Scale R) x v)⌝);
a(rewrite_tac [vs_ops_def]);
val vs_ops_def1 = save_pop_thm "vs_ops_def1";
=TEX
}\ignore

\subsection{Examples}

ⓈHOLCONST
│ ⦏ℝ⋎RVS⦎ : ℝ RVS
├──────
│ ℝ⋎RVS = MkRVS ℝ⋎+ (λx y⦁ x * y) 
■

\ignore{
=SML
val ⦏ℝ_v_def⦎ = get_spec⌜ℝ⋎RVS⌝;
set_goal([], ⌜ℝ⋎RVS ∈ VS⋎R⌝);
a (rewrite_tac[
	get_spec ⌜ℝ⋎RVS⌝,
	get_spec ⌜VS⋎R⌝,
	get_spec ⌜MkRVS⌝,
	get_spec ⌜Scale⋎V⌝,
	ℝ_plus_abelian_thm,
	ℝ_additive_ops_thm,
	ℝ_times_assoc_thm,
	ℝ_times_plus_distrib_thm
	]);
val ℝ⋎RVS_VS⋎R_thm = save_pop_thm "ℝ⋎RVS_VS⋎R_thm";
=TEX
}%\ignore

\subsection{Product Spaces}

ⓈHOLCONST
│ ⦏VectorSpaceProduct⦎ : 'a RVS → 'b RVS → ('a × 'b) RVS
├──────
│ ∀ V:'a RVS; W:'b RVS⦁ VectorSpaceProduct V W =
│ 	let group = (Grp V) * (Grp W)
│	and action (r:ℝ) (ga, gb) = ((r *⋎s ga) V, (r *⋎s gb) W)
│	in MkRVS group action
■

=SML
declare_alias ("*", ⌜VectorSpaceProduct⌝);
=TEX

\ignore{
=SML
val ⦏vsp_def⦎ = get_spec⌜VectorSpaceProduct⌝;
set_goal([], ⌜∀V:'a RVS; U:'b RVS⦁
	V ∈ VS⋎R ∧ U ∈ VS⋎R ⇒ V * U ∈ VS⋎R⌝);
a(rewrite_tac [	vs_def,
		vsp_def,
		vs_ops_def,
		rvs_def,
		let_def,
		grp_def]
	THEN REPEAT strip_tac
	THEN TRY (all_asm_fc_tac[
		abelian_group_product_thm,
		abelian_group_product_lemma])
	THEN TRY (asm_rewrite_tac[
		vs_ops_def,
		group_prod_prod_thm,
		rvs_def]));
(* *** Goal "1" *** *)
a (GET_NTH_ASM_T 16 ante_tac
	THEN GET_NTH_ASM_T 10 ante_tac);
a (REPEAT strip_tac
	THEN asm_rewrite_tac[group_prod_prod_thm1]);
(* *** Goal "2" *** *)
a (GET_NTH_ASM_T 15 ante_tac
	THEN GET_NTH_ASM_T 9 ante_tac);
a (REPEAT strip_tac
	THEN asm_rewrite_tac[group_prod_prod_thm1]);
val vector_product_thm = save_pop_thm "vector_product_thm";
=TEX
}%\ignore


\subsection{Linear Mappings}

A homomorphism between vector spaces is called a linear mapping and is defined as follows:

ⓈHOLCONST
│ ⦏Lin⦎ : 'a RVS × 'b RVS→ ('a → 'b) SET
├──────
│ ∀ V W f⦁
│	f ∈ Lin(V, W)
│ ⇔	f ∈ Homomorphism(Grp V, Grp W)
│ ∧	(∀x v⦁ f((x *⋎s v) V) = (x *⋎s f v)W)
■

\ignore{
=SML
set_goal([], ⌜∀r:ℝ⦁ $*⋎R r ∈ Lin(ℝ⋎RVS, ℝ⋎RVS)⌝);
a (rewrite_tac (td_thml[Spec ⌜Lin⌝, Spec ⌜ℝ⋎RVS⌝,
	Spec ⌜Grp⌝, Spec ⌜$*⋎s⌝])
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac (td_thml[Spec ⌜Homomorphism⌝,
	Spec ⌜ℝ⋎+⌝, Spec ⌜Car⌝,
	Thm ("\175", "\175_times_plus_distrib_thm")]));
(* *** Goal "2" *** *)
a (PC_T1 "ℝ_lin_arith" prove_tac[]);
val ℝ_Lin_thm1 = save_pop_thm "ℝ_Lin_thm1";
=TEX

=SML
set_goal([], ⌜∀V:'a RVS; l: ℝ → 'a⦁ V ∈ VS⋎R
	 ⇒ (l ∈ Lin(ℝ⋎RVS, V)
	⇔l (ℕℝ 1) ∈ Car (Grp V)
	∧ ∀r:ℝ⦁ l r = (r *⋎s (l (ℕℝ 1))) V)⌝);
a (rewrite_tac (td_thml[Spec ⌜Lin⌝, Spec ⌜ℝ⋎RVS⌝,
	Spec ⌜Homomorphism⌝, Spec ⌜Car⌝,
	Spec ⌜Grp⌝,
	Spec ⌜$*⋎s⌝,
	Spec ⌜ℝ⋎+⌝,
	Spec ⌜VS⋎R⌝]));
a (LEMMA_T ⌜∀V l⦁(∀ x v⦁ l (x * v) = Scale V x (l v))
	⇔ (∀ x v⦁ Scale V x (l v) = l (x * v))⌝
	rewrite_thm_tac);
(* *** Goal "1" *** *)
a (REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (REPEAT strip_tac
	THEN once_asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (rewrite_tac[]);
(* *** Goal "2.3" *** *)
a (once_asm_rewrite_tac[]);
a (GET_NTH_ASM_T 3 rewrite_thm_tac);
(* *** Goal "2.4" *** *)
a (once_asm_rewrite_tac[]);
a (GET_NTH_ASM_T 3 rewrite_thm_tac);
val ℝ_Lin_thm2 = save_pop_thm "ℝ_Lin_thm2";
=TEX
}%\ignore

ⓈHOLCONST
│ ⦏Fun⋎G⦎ : ('a → ℝ) GROUP
├──────
│ Fun⋎G = MkGROUP Universe (λf g a⦁f a + g a) (λa⦁ℕℝ 0) (λf a⦁~(f a))
■

\ignore{
=SML
val ⦏fun_g_def⦎ = get_spec⌜Fun⋎G⌝;
set_goal([], ⌜Fun⋎G ∈ Group⌝);
a(rewrite_tac[fun_g_def, abelian_group_def, group_def, group_ops_def]  THEN PC_T1 "ℝ_lin_arith" prove_tac[]);
val ⦏fun_g_group_thm⦎ = save_pop_thm "fun_g_group_thm";
=TEX
}\ignore

ⓈHOLCONST
│ ⦏Fun⋎RVS⦎ : ('a → ℝ) RVS
├──────
│ Fun⋎RVS = MkRVS Fun⋎G (λx:ℝ; f⦁ λa:'a⦁x * f a)
■

\ignore{
=SML
val ⦏fun_v_def⦎ = get_spec⌜Fun⋎RVS⌝;
set_goal([], ⌜Fun⋎RVS ∈ VS⋎R⌝);
a(rewrite_tac[fun_v_def, vs_def, vs_ops_def, grp_def]);
a(REPEAT strip_tac THEN TRY
	(rewrite_tac[fun_g_def, group_ops_def, vs_ops_def, abelian_group_def, group_def])
	THEN (PC_T1 "ℝ_lin_arith" prove_tac[]));
val ⦏fun_v_vs_thm⦎ = save_pop_thm "fun_v_vs_thm";
=TEX
}%\ignore

ⓈHOLCONST
│ ⦏ℝ⋏2⋎RVS⦎ : (ℝ × ℝ) RVS
├──────
│	ℝ⋏2⋎RVS = ℝ⋎RVS * ℝ⋎RVS
■
ⓈHOLCONST
│ ⦏ℝ⋏3⋎RVS⦎ : (ℝ × ℝ × ℝ) RVS
├──────
│	ℝ⋏3⋎RVS = ℝ⋎RVS * ℝ⋎RVS * ℝ⋎RVS
■

\ignore{
=SML
val ⦏ℝ_1_def⦎ = get_spec⌜ℝ⋎RVS⌝;
val ⦏ℝ_2_def⦎ = get_spec⌜ℝ⋏2⋎RVS⌝;
val ⦏ℝ_3_def⦎ = get_spec⌜ℝ⋏3⋎RVS⌝;
set_goal([], ⌜ℝ⋎RVS ∈ VS⋎R ∧ ℝ⋏2⋎RVS ∈ VS⋎R ∧ ℝ⋏3⋎RVS ∈ VS⋎R⌝);
a(rewrite_tac[ℝ⋎RVS_VS⋎R_thm, ℝ_2_def, ℝ_3_def]
	THEN (strip_asm_tac ℝ⋎RVS_VS⋎R_thm)
	THEN REPEAT_N 2 (all_asm_fc_tac [vector_product_thm])
	THEN asm_rewrite_tac[]);
val ⦏ℝ_123_vs_thm⦎ = save_pop_thm "ℝ_123_vs_thm";
=TEX
}%\ignore

Triples of reals are used for spatial coordinates and various vectors, a type abbreviation is used to make the specifications a little more readable.

=SML
declare_type_abbrev ("ℝ⋏3", [], ⓣℝ×ℝ×ℝ⌝);
=TEX

The following definition names the zero 3-tuple.
ⓈHOLCONST
│ ⦏0⋎R3⦎ : ℝ⋏3
├──────
│ 0⋎R3 = (0⋎R, 0⋎R, 0⋎R)
■

\ignore{
This is aliased to permit omission of the subscript where this can be done without ambiguity.
=IGN
declare_alias("0", ⌜0⋎R3⌝);
=TEX
}%ignore

The following function yeilds the square of the distance between two points in a three dimensional Euclidean space.

=SML
declare_infix (300, "-⋎tr");
=TEX
ⓈHOLCONST
│ $⦏-⋎tr⦎ : ℝ⋏3 → ℝ⋏3 → ℝ⋏3
├──────
│ ∀x⋎1 y⋎1 z⋎1 x⋎2 y⋎2 z⋎2 ⦁
│	(x⋎1, y⋎1, z⋎1) -⋎tr (x⋎2, y⋎2, z⋎2) = (x⋎1 - x⋎2, y⋎1 - y⋎2, z⋎1 - z⋎2)		
■
=SML
declare_alias ("-", ⌜$-⋎tr⌝);
=SML
declare_infix (300, "+⋎tr");
=TEX
ⓈHOLCONST
│ $⦏+⋎tr⦎ : ℝ⋏3 → ℝ⋏3 → ℝ⋏3
├──────
│ ∀x⋎1 y⋎1 z⋎1 x⋎2 y⋎2 z⋎2 ⦁
│	(x⋎1, y⋎1, z⋎1) +⋎tr (x⋎2, y⋎2, z⋎2) = (x⋎1 + x⋎2, y⋎1 + y⋎2, z⋎1 + z⋎2)		
■
=SML
declare_alias ("+", ⌜$-⋎tr⌝);
declare_infix (310, "*⋎trs");
=TEX
ⓈHOLCONST
│ $⦏*⋎trs⦎ : ℝ⋏3 → ℝ → ℝ⋏3
├──────
│ ∀x⋎1 y⋎1 z⋎1 r ⦁
│	(x⋎1, y⋎1, z⋎1) *⋎trs r = (x⋎1 * r, y⋎1 * r, z⋎1 * r)		
■
=SML
declare_alias ("*", ⌜$*⋎trs⌝);
declare_infix (310, "/⋎trs");
=TEX
ⓈHOLCONST
│ $⦏/⋎trs⦎ : ℝ⋏3 → ℝ → ℝ⋏3
├──────
│ ∀x⋎1 y⋎1 z⋎1 r ⦁
│	(x⋎1, y⋎1, z⋎1) /⋎trs r = (x⋎1 / r, y⋎1 / r, z⋎1 / r)		
■
=SML
declare_alias ("/", ⌜$/⋎trs⌝);
=TEX

\section{NORMED VECTOR SPACES}
\subsection{Norms}
=SML
declare_type_abbrev("NORM", ["'a"], ⓣ'a → ℝ⌝);
=TEX

ⓈHOLCONST
│ ⦏Norm⦎ : 'a RVS → 'a NORM SET
├──────
│ ∀ V norm⦁
│	norm ∈ Norm V
│ ⇔	(∀v⦁ℕℝ 0 ≤ norm v)
│ ∧	(∀v⦁norm v = ℕℝ 0 ⇔ v = 0⋎V V)
│ ∧	(∀x v⦁norm ((x *⋎s v)V) = Abs x * norm v)
│ ∧	(∀v w⦁norm ((v + w)V) ≤ norm v + norm w)
■

ⓈHOLCONST
│ ⦏NormProduct⦎ : 'a NORM → 'b NORM → ('a × 'b) NORM
├──────
│ ∀ n:'a NORM; m:'b NORM; a:'a; b:'b⦁
│	NormProduct n m (a, b) = Abs(SqrtA((n a) ^ 2 + (m b) ^ 2))
■
=SML
declare_alias("*", ⌜NormProduct⌝);
=TEX

\ignore{
=IGN
set_goal([], ⌜∀ n:'a NORM; m:'b NORM; a1 a2 :'a; b1 b2:'b⦁
	a1 *⋎V a2 + b1 *⋎V b2 ≤ (NormProduct n m (a1, b1)) *⋎VW (NormProduct n m (a2, b2))⌝);

a (REPEAT strip_tac THEN rewrite_tac [ℝ_ℕ_exp_square_thm, ℝ_times_plus_distrib_thm]);
a (ℝ_top_anf_tac);
=TEX

=IGN
set_goal([], ⌜∀ nfv nfw msv msw⦁
	SqrtA ((nfv +⋎R nfw) ^⋎N 2 +⋎R (msv +⋎R msw) ^⋎N 2)
             ≤⋎R SqrtA (nfv ^⋎N 2 +⋎R msv ^⋎N 2) +⋎R SqrtA (nfw ^⋎N 2 +⋎R msw ^⋎N 2)⌝);
a (REPEAT strip_tac THEN rewrite_tac [ℝ_ℕ_exp_square_thm, ℝ_times_plus_distrib_thm]);
a (ℝ_top_anf_tac);
=TEX

=SML
set_goal([], ⌜∀V:'a RVS; W:'b RVS; n:'a NORM; m:'b NORM⦁
	V ∈ VS⋎R ∧ W ∈ VS⋎R ∧ n ∈ Norm V ∧ m ∈ Norm W ⇒ n * m ∈ Norm (V * W)⌝);
a (rewrite_tac [get_spec ⌜NormProduct⌝, get_spec ⌜Norm⌝, get_spec ⌜VectorSpaceProduct⌝,
	ℝ_Abs_Norm_clauses]);
a (pure_once_rewrite_tac [
	prove_rule [] ⌜NormProduct n m v = NormProduct n m (Fst v, Snd v)⌝]);
a (pure_rewrite_tac [get_spec ⌜NormProduct⌝]);
a (rewrite_tac [ℝ_Abs_Norm_clauses, let_def]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [vs_ops_def1, get_spec ⌜Grp⌝,
	get_spec ⌜Grp⌝, get_spec ⌜SqrtA⌝,
	get_spec ⌜Unit⌝, get_spec ⌜GroupProduct⌝, let_def]);
a (fc_tac [sqrt_square_thm]);
a (LEMMA_T ⌜Fst v = 0⋎V V⌝ rewrite_thm_tac THEN1 asm_fc_tac[]);
a (LEMMA_T ⌜Snd v = 0⋎V W⌝ rewrite_thm_tac THEN1 asm_fc_tac[]);
a (rewrite_tac[get_spec ⌜0⋎V⌝]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac [sqrt_square_thm, get_spec ⌜0⋎V⌝,
	get_spec ⌜Group⋎RVS⌝, get_spec ⌜Unit⌝, get_spec ⌜GroupProduct⌝, let_def]);
(* *** Goal "3" *** *)
a (once_rewrite_tac [get_spec ⌜Scale⋎V⌝]);
a (asm_rewrite_tac [sqrt_square_thm, get_spec ⌜NormProduct⌝,
	get_spec ⌜Scale⋎RVS⌝, ℝ_abs_clauses]);
a (LEMMA_T ⌜(Abs⋎R x *⋎R n (Fst v)) ^⋎N 2 +⋎R (Abs⋎R x *⋎R m (Snd v)) ^⋎N 2
	= ((Abs⋎R x) ^⋎N 2) *⋎R ((n (Fst v)) ^⋎N 2 +⋎R (m (Snd v)) ^⋎N 2)⌝
	rewrite_thm_tac
	THEN1 rewrite_tac [ℝ_times_plus_distrib_thm, ℝ_ℕ_exp_times_thm]);
a (rewrite_tac [ℝ_sqrt_prod_thm, ℝ_sqrt_square_thm1, ℝ_ℕ_exp_square_thm,
	ℝ_abs_clauses, rewrite_rule [ℝ_ℕ_exp_square_thm] (get_spec ⌜SqrtA⌝)]);
(* *** Goal "4" *** *)
a (pure_once_rewrite_tac [
	prove_rule [] ⌜∀w⦁ NormProduct n m w = NormProduct n m (Fst w, Snd w)⌝]);
a (asm_rewrite_tac [sqrt_square_thm, get_spec ⌜NormProduct⌝, get_spec ⌜Scale⋎V⌝,
	get_spec ⌜Scale⋎RVS⌝, get_spec ⌜Car⌝, get_spec ⌜GroupProduct⌝, ℝ_abs_clauses, let_def]);
a (lemma_tac ⌜n ((Fst v . Fst w) (Group⋎RVS V)) ≤⋎R n (Fst v) +⋎R n (Fst w)⌝
	THEN1 GET_NTH_ASM_T 5 (rewrite_thm_tac o (rewrite_rule[get_spec ⌜Plus⋎V⌝])));
a (lemma_tac ⌜m ((Snd v . Snd w) (Group⋎RVS W)) ≤⋎R m (Snd v) +⋎R m (Snd w)⌝
	THEN1 GET_NTH_ASM_T 2 (rewrite_thm_tac o (rewrite_rule[get_spec ⌜Plus⋎V⌝])));
a (all_asm_ante_tac);
a (LEMMA_T ⌜∃A⦁ A = n ((Fst v . Fst w) (Group⋎RVS V))⌝
	(fn x=> strip_asm_tac x THEN GET_NTH_ASM_T 1 (rewrite_thm_tac o eq_sym_rule))
	THEN1 prove_∃_tac);
a (LEMMA_T ⌜∃B⦁ B = m ((Snd v . Snd w) (Group⋎RVS W))⌝
	(fn x=> strip_asm_tac x THEN GET_NTH_ASM_T 1 (rewrite_thm_tac o eq_sym_rule))
	THEN1 prove_∃_tac);
a (LEMMA_T ⌜∃nfv⦁ nfv = n (Fst v)⌝
	(fn x=> strip_asm_tac x THEN GET_NTH_ASM_T 1 (rewrite_thm_tac o eq_sym_rule))
	THEN1 prove_∃_tac);
a (LEMMA_T ⌜∃msv⦁ msv = m (Snd v)⌝
	(fn x=> strip_asm_tac x THEN GET_NTH_ASM_T 1 (rewrite_thm_tac o eq_sym_rule))
	THEN1 prove_∃_tac);
a (LEMMA_T ⌜∃nfw⦁ nfw = n (Fst w)⌝
	(fn x=> strip_asm_tac x THEN GET_NTH_ASM_T 1 (rewrite_thm_tac o eq_sym_rule))
	THEN1 prove_∃_tac);
a (LEMMA_T ⌜∃msw⦁ msw = m (Snd w)⌝
	(fn x=> strip_asm_tac x THEN GET_NTH_ASM_T 1 (rewrite_thm_tac o eq_sym_rule))
	THEN1 prove_∃_tac);
a (REPEAT strip_tac);

(* Now following Rob's outline proof *)

a (lemma_tac ⌜SqrtA (A ^⋎N 2 +⋎R B ^⋎N 2) ≤⋎R SqrtA((nfv +⋎R nfw)^2 +⋎R (msv +⋎R msw)^2)⌝
	THEN1 (bc_tac [ℝ_sqrt_mono_thm]
		THEN TRY (rewrite_tac [ℝ_sum_square_pos_thm, ℝ_ℕ_exp_square_thm])
		THEN bc_tac [ℝ_plus_mono_thm, ℝ_square_mono_thm1]
		THEN asm_rewrite_tac[]));
a (lemma_tac ⌜SqrtA((nfv +⋎R nfw)^2 +⋎R (msv +⋎R msw)^2)
	≤⋎R SqrtA (nfv ^⋎N 2 +⋎R msv ^⋎N 2) +⋎R SqrtA (nfw ^⋎N 2 +⋎R msw ^⋎N 2)⌝);
(* *** Goal "4.1" *** *)
a (bc_tac [ℝ_square_≤_≤_thm, ℝ_sum_pos_thm]
	THEN TRY (rewrite_tac [rewrite_rule [ℝ_ℕ_exp_square_thm] (get_spec ⌜SqrtA⌝),
		ℝ_abs_sum_square_thm,
		ℝ_times_plus_distrib_thm,
		ℝ_ℕ_exp_square_thm]));
a (ℝ_top_anf_tac THEN rewrite_tac[∀_elim ⌜msw *⋎R msw⌝ ℝ_plus_order_thm]);
(*
a (rewrite_tac[∀_elim ⌜nfv *⋎R nfv⌝ ℝ_plus_order_thm]);
a (rewrite_tac[∀_elim ⌜nfw *⋎R nfw⌝ ℝ_plus_order_thm]);
a (LEMMA_T ⌜ℕℝ 2 *⋎R msv *⋎R msw +⋎R ℕℝ 2 *⋎R nfv *⋎R nfw
	= ℕℝ 2 *⋎R (msv *⋎R msw +⋎R nfv *⋎R nfw)⌝ rewrite_thm_tac
	THEN1 rewrite_tac [ℝ_times_plus_distrib_thm]);
*)
a (rewrite_tac[∀_elim ⌜nfv ^⋎N 2⌝ ℝ_plus_order_thm]);
a (rewrite_tac[∀_elim ⌜nfw ^⋎N 2⌝ ℝ_plus_order_thm]);
a (rewrite_tac[∀_elim ⌜msw ^⋎N 2⌝ ℝ_plus_order_thm]);
a (LEMMA_T ⌜ℕℝ 2 *⋎R msv *⋎R msw +⋎R ℕℝ 2 *⋎R nfv *⋎R nfw
	= ℕℝ 2 *⋎R (msv *⋎R msw +⋎R nfv *⋎R nfw)⌝ rewrite_thm_tac
	THEN1 rewrite_tac [ℝ_times_plus_distrib_thm]);

(*
a (lemma_tac ⌜msv *⋎R msw +⋎R nfv *⋎R nfw ≤⋎R Abs⋎R (msv *⋎R msw +⋎R nfv *⋎R nfw)⌝
	THEN1 rewrite_tac [ℝ_≤_abs_thm]);
a (lemma_tac ⌜Abs(msv *⋎R msw +⋎R nfv *⋎R nfw)
             ≤⋎R SqrtA (nfv *⋎R nfv +⋎R msv *⋎R msv) *⋎R SqrtA (nfw *⋎R nfw +⋎R msw *⋎R msw)⌝);
*)
a (lemma_tac ⌜msv *⋎R msw +⋎R nfv *⋎R nfw ≤⋎R Abs⋎R (msv *⋎R msw +⋎R nfv *⋎R nfw)⌝
	THEN1 rewrite_tac [ℝ_≤_abs_thm]);
a (lemma_tac ⌜Abs(msv *⋎R msw +⋎R nfv *⋎R nfw)
             ≤⋎R SqrtA (nfv ^⋎N 2 +⋎R msv ^⋎N 2) *⋎R SqrtA (msw ^⋎N 2 +⋎R nfw ^⋎N 2)⌝);

(*
a (lemma_tac ⌜2. *⋎R msv *⋎R msw +⋎R nfv *⋎R nfw ≤⋎R 2. *⋎R Abs⋎R (msv *⋎R msw +⋎R nfv *⋎R nfw)⌝
	THEN1 rewrite_tac [ℝ_≤_abs_thm]);
*)

(* *** Goal "4.1.1" *** *)

(*
a (lemma_tac ⌜SqrtA (nfv *⋎R nfv +⋎R msv *⋎R msv) *⋎R SqrtA (nfw *⋎R nfw +⋎R msw *⋎R msw)
	= SqrtA (msv *⋎R msv +⋎R nfv *⋎R nfv)
         *⋎R SqrtA (msw *⋎R msw +⋎R nfw *⋎R nfw)⌝
	THEN1 (ℝ_top_anf_tac THEN strip_tac));
a (once_rewrite_tac [ℝ_plus_comm_thm]);
a (once_rewrite_tac [∀_elim ⌜nfv *⋎R nfw⌝ ℝ_plus_comm_thm]);
a (LEMMA_T ⌜∀m⦁ m ^⋎N 2 = m *⋎R m⌝ rewrite_thm_tac THEN1 (strip_tac THEN ℝ_top_anf_tac THEN strip_tac));
a (accept_tac (rewrite_rule [] (list_∀_elim [⌜(msv, nfv)⌝, ⌜(msw, nfw)⌝]
	(rewrite_rule [let_def] schwartz_2nd_thm2))));
a (accept_tac (rewrite_rule [] (list_∀_elim [⌜(msv, nfv)⌝, ⌜(nfw, msw)⌝]
	(rewrite_rule [let_def] schwartz_2nd_thm2))));
*)
a (LEMMA_T ⌜SqrtA (nfv ^⋎N 2 +⋎R msv ^⋎N 2) *⋎R SqrtA (msw ^⋎N 2 +⋎R nfw ^⋎N 2)
	= SqrtA (msv *⋎R msv +⋎R nfv *⋎R nfv) *⋎R SqrtA (msw *⋎R msw +⋎R nfw *⋎R nfw)⌝ rewrite_thm_tac
	THEN1 (ℝ_top_anf_tac THEN strip_tac));
a (accept_tac (rewrite_rule [] (list_∀_elim [⌜(msv, nfv)⌝, ⌜(msw, nfw)⌝]
	(rewrite_rule [let_def] schwartz_2nd_thm2))));
(* *** Goal "4.1.2" *** *)
a (all_fc_tac [ℝ_≤_trans_thm]);
a (LEMMA_T ⌜0. ≤⋎R 2.⌝ asm_tac THEN1 prove_tac[]);
a (FC_T (MAP_EVERY asm_tac) [ℝ_times_mono_thm2]);
a (all_asm_fc_tac[]);
(* *** Goal "4.2" *** *)
a (all_fc_tac [ℝ_≤_trans_thm]);
val NormProduct_thm = save_pop_thm "NormProduct_thm";
=TEX

}%\ignore

ⓈHOLCONST
│ ⦏Di⋎R⦎ : ℝ NORM;
│ ⦏Di⋎R2⦎ : (ℝ × ℝ) NORM;
│ ⦏Di⋎R3⦎ : (ℝ × ℝ × ℝ) NORM
├──────
│ (∀r:ℝ⦁ Di⋎R r = Abs r)
│ ∧ Di⋎R2 = NormProduct Di⋎R Di⋎R
│ ∧ Di⋎R3 = NormProduct Di⋎R Di⋎R2
■

\ignore{
=SML
set_goal([], ⌜Di⋎R ∈ (Norm ℝ⋎RVS)⌝);
a (rewrite_tac [get_spec ⌜Di⋎R⌝, get_spec ⌜Norm⌝, get_spec ⌜ℝ⋎RVS⌝,
	get_spec ⌜Scale⋎V⌝, get_spec ⌜Group⋎RVS⌝,
	get_spec ⌜ℝ⋎+⌝, get_spec ⌜Unit⌝,
	ℝ_Abs_Norm_clauses]);
val Di⋎R_Norm_thm = save_pop_thm "Di⋎R_Norm_thm";
=TEX
}%\ignore

\subsection{Normed Vector Spaces}

ⓈHOLLABPROD NVS─────────────────
│	Rvs⋎NVS		:'a RVS;
│	Norm⋎NVS		:'a → ℝ
■─────────────────────────────
ⓈHOLCONST
│ ⦏Nvs⦎ : 'a NVS SET
├──────
│ ∀ N⦁ N ∈ Nvs
│ ⇔ Rvs⋎NVS N ∈ VS⋎R ∧ (Norm⋎NVS N) ∈ Norm (Rvs⋎NVS N)  
■
ⓈHOLCONST
│ ⦏Plus⋎N⦎ :  'a → 'a → 'a NVS → 'a;
│ ⦏Minus⋎N⦎ :  'a → 'a NVS → 'a;
│ ⦏Subtract⋎N⦎ :  'a → 'a → 'a NVS → 'a;
│ ⦏0⋎N⦎ :  'a NVS → 'a;
│ ⦏Scale⋎N⦎ :  ℝ → 'a → 'a NVS → 'a;
│ ⦏Norm⋎N⦎ :  'a → 'a NVS → ℝ
├──────
│ ∀ N⦁
│ 	(∀v w⦁ Plus⋎N v w N = Plus⋎V v w (Rvs⋎NVS N))
│ ∧	(∀v⦁ Minus⋎N v N = Minus⋎V v (Rvs⋎NVS N))
│ ∧	(∀v w⦁ Subtract⋎N v w N = Plus⋎V v (Minus⋎V w (Rvs⋎NVS N)) (Rvs⋎NVS N))
│ ∧	0⋎N N = 0⋎V (Rvs⋎NVS N)
│ ∧	(∀x v⦁Scale⋎N x v N = Scale⋎V x v (Rvs⋎NVS N))
│ ∧	(∀v⦁Norm⋎N v N = Norm⋎NVS N v)
■
=SML
declare_alias("+", ⌜Plus⋎N⌝);
declare_alias("~", ⌜Minus⋎N⌝);
declare_alias("-", ⌜Subtract⋎N⌝);
declare_alias("*", ⌜Scale⋎N⌝);
=TEX

ⓈHOLCONST
│ ⦏NvsProduct⦎ : 'a NVS → 'b NVS → ('a × 'b) NVS
├──────
│ ∀ n:'a NVS; m:'b NVS⦁
│	NvsProduct n m = MkNVS ((Rvs⋎NVS n) * (Rvs⋎NVS m)) ((Norm⋎NVS n) * (Norm⋎NVS m))
■

=SML
declare_alias("*", ⌜NvsProduct⌝);
=TEX

\ignore{

=SML
set_goal([], ⌜∀N:'a NVS; M:'b NVS⦁ N ∈ Nvs ∧ M ∈ Nvs ⇒ N * M ∈ Nvs⌝);
a (rewrite_tac [get_spec ⌜Nvs⌝, get_spec ⌜Rvs⋎NVS⌝,
	get_spec ⌜NvsProduct⌝] THEN REPEAT strip_tac);
a (all_fc_tac [vector_product_thm]);
a (all_fc_tac [NormProduct_thm]);
val NvsProduct_thm = save_pop_thm "NvsProduct_thm";
=TEX

}%ignore

ⓈHOLCONST
│ ⦏ℝ⋎NVS⦎ : ℝ NVS;
│ ⦏ℝ⋏2⋎NVS⦎ : (ℝ × ℝ) NVS;
│ ⦏ℝ⋏3⋎NVS⦎ : (ℝ × ℝ × ℝ) NVS;
│ ⦏ℝ⋏4⋎NVS⦎ : (ℝ × ℝ × ℝ × ℝ) NVS
├──────
│   ℝ⋎NVS = MkNVS ℝ⋎RVS Di⋎R
│ ∧ ℝ⋏2⋎NVS = ℝ⋎NVS * ℝ⋎NVS
│ ∧ ℝ⋏3⋎NVS = ℝ⋎NVS * ℝ⋏2⋎NVS
│ ∧ ℝ⋏4⋎NVS = ℝ⋎NVS * ℝ⋏3⋎NVS
■

\ignore{
=SML
val ⦏norm_def⦎ = get_spec⌜Norm⌝;
set_goal([], ⌜ℝ⋎NVS ∈ Nvs⌝);
a (rewrite_tac[
	get_spec ⌜ℝ⋎NVS⌝,
	get_spec ⌜Nvs⌝,
	get_spec ⌜MkNVS⌝,
	Di⋎R_Norm_thm,
	ℝ⋎RVS_VS⋎R_thm]);
val ℝ⋎NVS_Nvs_lemma = pop_thm ();

set_goal([], ⌜ℝ⋏2⋎NVS ∈ Nvs⌝);
a (once_rewrite_tac [get_spec ⌜ℝ⋎NVS⌝]);
a (asm_tac ℝ⋎NVS_Nvs_lemma THEN all_fc_tac [NvsProduct_thm]);
val ℝ⋎NVS_Nvs_lemma2 = pop_thm ();

set_goal([], ⌜ℝ⋏3⋎NVS ∈ Nvs⌝);
a (once_rewrite_tac [get_spec ⌜ℝ⋎NVS⌝]);
a (asm_tac ℝ⋎NVS_Nvs_lemma THEN asm_tac ℝ⋎NVS_Nvs_lemma2
	THEN all_fc_tac [NvsProduct_thm]);
val ℝ⋎NVS_Nvs_lemma3 = pop_thm ();

set_goal([], ⌜ℝ⋏4⋎NVS ∈ Nvs⌝);
a (once_rewrite_tac [get_spec ⌜ℝ⋎NVS⌝]);
a (asm_tac ℝ⋎NVS_Nvs_lemma THEN asm_tac ℝ⋎NVS_Nvs_lemma3
	THEN all_fc_tac [NvsProduct_thm]);
val ℝ⋎NVS_Nvs_lemma4 = pop_thm ();

set_goal([], ⌜ℝ⋎NVS ∈ Nvs ∧ ℝ⋏2⋎NVS ∈ Nvs ∧ ℝ⋏3⋎NVS ∈ Nvs ∧ ℝ⋏4⋎NVS ∈ Nvs⌝);
a (rewrite_tac [ℝ⋎NVS_Nvs_lemma, ℝ⋎NVS_Nvs_lemma2,  ℝ⋎NVS_Nvs_lemma3, ℝ⋎NVS_Nvs_lemma4]);
val ℝ⋎NVS_Nvs_thm = save_pop_thm "ℝ⋎NVS_Nvs_thm";
=TEX
}%\ignore

\subsection{Frechet Derivative}

In the following read, as so often, $\in$ as ``is a'': the set in question will have at most one element.
In ordinary notation, the last inequality here amounts to 
$|((f(v+h) - f(v) - D(h))/|h|) < e$.

ⓈHOLCONST
│ ⦏FrechetDeriv⦎ : ('a NVS) × ('b NVS) → ('a → 'b) → 'a → ('a → 'b) SET
├──────
│ ∀ (M:'a NVS) (N:'b NVS) f (v:'a) (D: 'a → 'b)⦁
│	D ∈ FrechetDeriv(M, N) f v
│ ⇔	D ∈ Lin(Rvs⋎NVS M, Rvs⋎NVS N)
│ ∧	(∀e:ℝ⦁ ℕℝ 0 < e ⇒∃d⦁
│		ℕℝ 0 < d
│ 	∧	(∀h:'a⦁ ℕℝ 0 < Norm⋎N h M ∧ Norm⋎N h M < d ⇒ 
│		Norm⋎N ((((Norm⋎N h M)⋏-⋏1) * (((f((v + h)M) - (f v))N) - (D h))N) N) N < e))
■

ⓈHOLCONST
│ ⦏FDifferentiable⦎ : ('a NVS) × ('b NVS) → ('a → 'b) → 'a → BOOL
├──────
│ ∀ (M:'a NVS) (N:'b NVS) f (v:'a) ⦁
│	FDifferentiable (M, N) f v
│ ⇔	¬ FrechetDeriv(M, N) f v = {}
■

The special case of the derivative in which the domain of the function is $ℝ⋎NVS$ (representing time perhaps) is defined here.
A different convention is adopted for representation of a possibly not everywhere defined derivative.

\ignore{
=SML
set_flag ("pp_use_alias", false);
set_goal ([],⌜∃VDeriv⦁
	 ∀ (N:'a NVS); f:ℝ → 'a; r⦁
	let D = FrechetDeriv (ℝ⋎NVS, N) f r
	in ¬D = {} ⇒ (λr'⦁ (r' * (VDeriv N f r)) N) ∈ D⌝);
a (rewrite_tac [let_def]);
a (∃_tac ⌜λ(N:'b NVS) f r⦁ εb⦁ (λr'⦁ (r' * b) N) ∈ FrechetDeriv (ℝ⋎NVS, N) f r⌝
	THEN rewrite_tac[sets_ext_clauses]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜x ∈ Lin(ℝ⋎RVS, Rvs⋎NVS N)⌝
	THEN1 (all_asm_ante_tac
		THEN rewrite_tac [
			get_spec ⌜FrechetDeriv⌝,
			get_spec ⌜Rvs⋎NVS⌝,
			get_spec ⌜ℝ⋎NVS⌝
			]
		THEN REPEAT strip_tac));
a (all_asm_fc_tac[get_spec ⌜Lin⌝]);
a (LEMMA_T ⌜x =  λr'⦁ (r' * (x (ℕℝ 1))) N⌝ asm_tac
	THEN1 (asm_rewrite_tac []
		THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (rewrite_tac (td_thml [Spec ⌜Scale⋎N⌝]));
a (list_spec_nth_asm_tac 1 [⌜x'⌝, ⌜ℕℝ 1⌝]);
a (POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a (rewrite_tac (td_thml [Spec ⌜Scale⋎V⌝, Spec ⌜ℝ⋎RVS⌝, Spec ⌜Scale⋎RVS⌝]));
(* *** Goal "2" *** *)
a (ε_tac ⌜ε b⦁ (λ r'⦁ Scale⋎N r' b N) ∈ FrechetDeriv (ℝ⋎NVS, N) f r⌝);
a (∃_tac ⌜x (ℕℝ 1)⌝);
a (POP_ASM_T (asm_tac o eq_sym_rule));
a (asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%\ignore

ⓈHOLCONST
│ ⦏VDeriv⦎ : 'a NVS → (ℝ → 'a) → (ℝ → 'a)
├──────
│ ∀ (N:'a NVS) f r⦁
│	let D = FrechetDeriv (ℝ⋎NVS, N) f r
│	in ¬D = {} ⇒ (λr'⦁ (r' * (VDeriv N f r)) N) ∈ D
■

ⓈHOLCONST
│ ⦏VNthDeriv⦎ : ℕ → ('b NVS) → (ℝ → 'b) → (ℝ → 'b)
├──────
│ ∀ (n:ℕ); N:'b NVS; f :ℝ → 'b⦁
│	 VNthDeriv 0 N f = f
│∧ 	 VNthDeriv (n+1) N f =
│		let f' = VDeriv N f
│		in VNthDeriv n N f'
■

ⓈHOLCONST
│ ⦏EDiff⦎ : ('a NVS) × ('b NVS) → ('a → 'b) → ('a → 'a → 'b) → BOOL
├──────
│ ∀ N M f df⦁
│	EDiff (N, M) f df
│ ⇔	∀v⦁ df v ∈ FrechetDeriv (N, M) f v
■

\subsection{The Natural Topology Over a Normed Vector Space}

ⓈHOLCONST
│ NVSTopology: 'a NVS → 'a SET SET
├──────
│ ∀v:'a NVS⦁ NVSTopology v = {vs: 'a SET | ∀x:'a⦁ x ∈ vs ⇒
│	∃ξ⦁ ∀y:'a⦁ Norm⋎N ((Subtract⋎N y x) v) v <⋎R ξ ⇒ y ∈ vs}
■

\section{INNER PRODUCT SPACES}

\subsection{Inner Products}
=SML
declare_type_abbrev("IP", ["'a"], ⓣ'a → 'a → ℝ⌝);
=TEX

=SML
declare_infix(310, "*⋎V");
declare_infix(300, "+⋎V");
declare_infix(310, ".⋎i");
=TEX

ⓈHOLCONST
│ ⦏InnerProduct⦎ : 'a RVS → 'a IP SET
├────────────
│ ∀ V:'a RVS; $.⋎i: 'a → 'a → ℝ⦁
│	$.⋎i ∈ InnerProduct V
│ ⇔	let x *⋎V y = Scale⋎V x y V
│	and $+⋎V = (λx y⦁ Plus⋎V x y V) in
│	(∀ a b p q r⦁ (a *⋎V p +⋎V b *⋎V q) .⋎i r = (a *⋎V p) .⋎i r +⋎R (b *⋎V q) .⋎i r)
│ ∧	(∀ p q⦁ p .⋎i q = q .⋎i p)
│ ∧	(∀ p:'a⦁ p .⋎i p ≥ 0⋎R)
│ ∧	(∀ p:'a⦁ p .⋎i p = 0⋎R ⇒ p = 0⋎V V)
■

\subsection{Inner Product Spaces}

ⓈHOLLABPROD IPS─────────────────
│	Rvs⋎IPS		:'a RVS;
│	Ip⋎IPS		:'a → 'a → ℝ
■──────────────────────────
ⓈHOLCONST
│ ⦏Ips⦎ : 'a IPS SET
├──────
│ ∀ i:'a IPS⦁ i ∈ Ips
│ ⇔ Rvs⋎IPS i ∈ VS⋎R ∧ (Ip⋎IPS i) ∈ InnerProduct (Rvs⋎IPS i) 
■

ⓈHOLCONST
│ ⦏Plus⋎I⦎ :  'a → 'a → 'a IPS → 'a;
│ ⦏Minus⋎I⦎ :  'a → 'a IPS → 'a;
│ ⦏Subtract⋎I⦎ :  'a → 'a → 'a IPS → 'a;
│ ⦏0⋎I⦎ :  'a IPS → 'a;
│ ⦏Scale⋎I⦎ :  ℝ → 'a → 'a IPS → 'a;
│ ⦏Ip⋎I⦎ :  'a → 'a → 'a IPS → ℝ;
│ ⦏Norm⋎I⦎ :  'a → 'a IPS → ℝ
├──────
│ ∀ i:'a IPS⦁
│ 	(∀v w⦁ Plus⋎I v w i = Plus⋎V v w (Rvs⋎IPS i))
│ ∧	(∀v⦁ Minus⋎I v i = Minus⋎V v (Rvs⋎IPS i))
│ ∧	(∀v w⦁ Subtract⋎I v w i = Plus⋎V v (Minus⋎V w (Rvs⋎IPS i)) (Rvs⋎IPS i))
│ ∧	0⋎I i = 0⋎V (Rvs⋎IPS i)
│ ∧	(∀x v⦁Scale⋎I x v i = Scale⋎V x v (Rvs⋎IPS i))
│ ∧	(∀v w⦁Ip⋎I v w i = Ip⋎IPS i v w)
│ ∧	(∀v⦁Norm⋎I v i = SqrtA(Ip⋎IPS i v v))
■

\section{MANIFOLDS}

In order to reason about space-time and the nature of the physical universe it is necessary to have mathematical structures which abstract away from the specific coordinate systems of pre-relativistic physics.

My objective is to use formalisation as way of analysing the various arguments which are presented to justify moving from Aristotelian to Gallilean to special and general relativistic models of space-time.

According to \cite{Hawking73} a manifold is a collection of coordinate patches over a topological space.
This however, they recognise contains too much specific information about coordinate systems,
An atlas of coordinate patches is necessary in defining the concept of differentiability, but is not itself a part of the manifold.

We therefore approach the definition of manifolds as the definition of certain properties of topologies, where a topology is itself just a set of sets satisfying certain properties.

\subsection{Topology for Manifolds}

A topological manifold is a topology which is:
\begin{itemize}
\item locally homeomorphic to $ℝ^n$ for some positive integer n
\end{itemize}

Sometimes it is required to be hausdorff, connected or paracompact but I don't propose to include any of these properties in the definition of a topological manifold.
Presumably, if it is locally homeomorphic to $ℝ^n$ it will be hausdorff.

The concept ``locally homeomorphic'' can be defined without specific reference to $ℝ^n$, as a relationship between two topologies, or as here, by defining for any topology V the equivalence class of topologies with which it is locally homemorphic.

ⓈHOLCONST
│ LocallyHomeomorphicTo: 'a SET SET → 'b SET SET SET
├──────
│ ∀U V⦁ U ∈ LocallyHomeomorphicTo V ⇔
│ ∀x⦁ x ∈ Space⋎T U ⇒ ∃y z f⦁ x ∈ y ∧ y ∈ U ∧ z ∈ V
		∧  f ∈ (y ◁⋎T U, z ◁⋎T V) Homeomorphism 
■

A topological manifold:

ⓈHOLCONST
│ TopologicalManifold: 'a SET SET → 'b SET SET SET
├──────
│ ∀U V⦁ U ∈ TopologicalManifold V ⇔
│	U ∈ Topology ∧ V ∈ Topology ∧ U ∈ LocallyHomeomorphicTo V
■

Normally the topology V will be the usual topology on $ℝ^n$ for some n.

There are two further steps in the definition of the kind of manifold we need.
The first is the requirement of differentiability.
It turns out that differentiability is a property not just of the topological manifold, but rather of the topology together with some system of coordinate patches.
Such a collection of coordinate patches is called an atlas, and an atlas is differentiable if translations between the different coordinate systems it encompasses are all differentiable.

In order to define differentiable manifolds we seem to need to introduce coordinate systems, even though our definition of differentiability above is coordinate free.
However, because we have a coordinate free definition of differentiability I can indulge in a modest (but probably not actually useful) ``generalisation''.

Though it seems normal to expect the coordinate space to be in some power of the positive real line, its easier at this stage to allow an arbitrary normed vector space.

Differentiability is asserted using an atlas of coordinate patches.
In this presentation a coordinate patch is an open set in some vector space.

ⓈHOLLABPROD ATLAS─────────────────
│	Nvs⋎M	:'b NVS;
│	Cmap⋎M	: ('a SET × ('a → 'b)) SET
■──────────────────────────


\section{GEOMETRIC ALGEBRA}

Geometric algebras may be the best way to do differential geometry.
This section is a first sally in that direction.

There are two different strategies for exploiting geometric algebra and geometric analysis.
One way is to construct a single geometric algebra which is the union of all the GA(n) for each finite n.
Let us call this the concrete approach.
This may be thought of by analogy with the treatment of real arithmetic in HOL and in contrast with the treament of algebraic theories such as that of groups or vector spaces.

The second approach is to follow the model provided by the treatement of groups and vector spaces.

The main factor determining which of these two approaches to follow is whether the structure in question is unique.
Thus, in the case of the real numbers, the axioms are categorical, and so there is no obvious advantage from reasoning about "real number structures" in general.
In HOL there would be disadvantages, since such reasoning would be hypothetical.
The theorems involve hypotheses about certain variables denoting the relevant kind of algebraic structure, and that certain other variables lie in the domain of the structures.
These are unnecessary when reasoning about a single structure whose domain is a type.

It seems likely that the development of differential algebra in the context of an infinite dimensional geometric algebra would be the most efficient way to formalise physics.
Its not quite so obvious that this would be good for the kinds of metaphysics which I have in mind as applications, but Rob Arthan is working with $GA(\infty,\infty)$, so my best bet is to build on his work.

Since my objective is to do metaphysics, and for the kind of metaphysics I have in mind, doing physics is a prerequisite, I propose pro-tem to follow Hestenes and try to formalise aspects of his accounts of physics using geometric algebra.


{\let\Section\section
\def\section#1{\Section{#1}\label{TheoryListing}}
\include{diffgeom.th}
}  %\let

\twocolumn[\section{INDEX}\label{INDEX}]
{\small\printindex}

\end{document}
=SML
set_flag ("pp_use_alias", true);
output_theory{out_file="diffgeom.th.doc", theory="diffgeom"};
set_flag ("pp_use_alias", false);
=TEX
