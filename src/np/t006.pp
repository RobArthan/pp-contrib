=IGN
$Id: t006.doc,v 1.44 2013/01/03 17:12:44 rbj Exp $
=TEX
\documentclass[11pt,a4paper]{article}
%\usepackage{latexsym}
\usepackage{rbj}
\ftlinepenalty=9999
\tabstop=0.25in
\usepackage{A4}

\def\Hide#1{\relax}
\newcommand{\ignore}[1]{}

\title{Miscellanea}
\author{Roger Bishop Jones}
\date{2022-02-24}

\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

\makeindex
\begin{document}
\vfill
\maketitle
\begin{abstract}
This document contains things used by my other theories which do not particularly belong in them.
Definitions or theorems which arguably belong in a theory already produced by someone else.
\end{abstract}
\vfill
\begin{centering}
{\footnotesize

Date Created 2004/07/15

Last Changed $ $Date: 2013/01/03 17:12:44 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t006.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t006.pdf}

$ $Id: t006.doc,v 1.44 2013/01/03 17:12:44 rbj Exp $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize
\end{centering}

\newpage

{\setcounter{tocdepth}{4}
\parskip=0pt\tableofcontents}

%%%%

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\section{The Theory rbjmisc}

For context and motivation see \cite{rbjt000}.

All the theorems are placed in the one temporary location, which therefore must have as ancestors all the theories which are being extended.

There is one section in this document, following this one, for each theory to which an addition is being made so new parents may be added in those sections, or new proof contexts used.

=SML
open PreConsisProof;
=TEX

=SML
open_theory "cache'rbjhol";
force_new_theory "rbjmisc";
val _ =	let open ReaderWriterSupport.PrettyNames;
	in add_new_symbols [ (["sqsubseteq2"], Value "⊑", Simple) ]
        end
handle _ => ();
new_parent "analysis";
new_parent "equiv_rel";
force_new_pc ⦏"'rbjmisc"⦎;
merge_pcs ["'prove_∃_⇒_conv", "'savedthm_cs_∃_proof"] "'rbjmisc";
set_merge_pcs ["basic_hol1", "'sets_alg", "'ℝ", "'rbjmisc"];
open UnifyForwardChain; open RbjTactics1;
=TEX

\ignore{
 ⓈHOLLABPROD EIGHTTUPLE─────────────────
│	aaaa bbbb cccc dddd eeee ffff gggg hhhh: 'a
 ■─────────────────────────
}%ignore

\section{Functions}


=GFT
⦏OneOne_o_thm⦎ = ⊢ ∀ f g⦁ OneOne f ∧ OneOne g ⇒ OneOne (f o g)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ f g⦁ OneOne f ∧ OneOne g ⇒ OneOne (f o g)⌝);
a (rewrite_tac [one_one_def, o_def] THEN REPEAT strip_tac);
a (REPEAT (asm_fc_tac[]));
val OneOne_o_thm = save_pop_thm "OneOne_o_thm";
=TEX
}%ignore

\section{Combinators}

ⓈHOLCONST
│ $⦏CombC⦎: ('a → 'b → 'c) → ('b → 'a → 'c)
├──────
│ ∀f⦁ CombC f = λx y⦁ f y x 
■

=GFT
⦏combc_thm⦎ = ⊢ ∀ f x y⦁ CombC f x y = f y x
=TEX

\ignore{
=SML
set_goal([], ⌜∀f x y⦁ CombC f x y = f y x⌝);
a (rewrite_tac [get_spec ⌜CombC⌝]);
val combc_thm = save_pop_thm "combc_thm";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏BinComp⦎ : ('a → 'b → 'c) → ('d → 'a) → ('e → 'b) → ('d → 'e → 'c)
├──────
│ ∀ f g h⦁ BinComp f g h = λx y⦁ f (g x) (h y) 
■

=GFT
⦏combc_thm⦎ = ⊢ ∀ f x y⦁ CombC f x y = f y x
=TEX

\ignore{
=SML
set_goal([], ⌜∀ f g h x y⦁ BinComp f g h x y = f (g x) (h y)⌝);
a (rewrite_tac [get_spec ⌜BinComp⌝]);
val bincomp_thm = save_pop_thm "bincomp_thm";
=TEX
}%ignore

\ignore{
=SML
add_pc_thms "'rbjmisc" (map get_spec [] @ [combc_thm, bincomp_thm]);
set_merge_pcs ["basic_hol1", "'sets_alg", "'ℝ", "'rbjmisc"];
=TEX
}%ignore

\section{Predicate Calculus}

There is probably a better way of doing this (or a better thing to be doing).

In some circumstances $∀\_∧\_out\_lemma$ can be used to avoid or postpone a case split.

=GFT
⦏∀_η_lemma⦎ =
	⊢ ∀ p⦁ $∀ p ⇔ (∀ x⦁ p x)

⦏∀_∧_out_lemma⦎ =
	⊢ ∀ p q⦁ $∀ p ∧ $∀ q ⇔ (∀ x⦁ p x ∧ q x)
=TEX

\ignore{
=SML
set_goal([], ⌜∀p:'a → BOOL⦁ $∀ p ⇔ $∀ λx⦁ p x⌝);
a (REPEAT strip_tac);
a (POP_ASM_T (rewrite_thm_tac o (rewrite_rule []) o (once_rewrite_rule [map_eq_sym_rule η_axiom])));
a (once_rewrite_tac [map_eq_sym_rule η_axiom]);
a (asm_rewrite_tac[]);
val ∀_η_lemma = save_pop_thm "∀_η_lemma";

set_goal([], ⌜∀p q:'a → BOOL⦁ $∀ p ∧ $∀ q ⇔ $∀ λx⦁ p x ∧ q x⌝);
a (REPEAT strip_tac);
a (GET_ASM_T ⌜$∀ p⌝ (rewrite_thm_tac o (once_rewrite_rule [∀_η_lemma])));
a (GET_ASM_T ⌜$∀ q⌝ (rewrite_thm_tac o (once_rewrite_rule [∀_η_lemma])));
a (once_rewrite_tac [∀_η_lemma]);
a (asm_rewrite_tac[]);
a (once_rewrite_tac [∀_η_lemma]);
a (asm_rewrite_tac[]);
val ∀_∧_out_lemma = save_pop_thm "∀_∧_out_lemma";
=TEX
}%ignore

\subsubsection{ManyOne}

The relations used in replacement must be ``ManyOne'' relations, otherwise the image may be larger than the domain, and Russell's paradox would reappear.

ⓈHOLCONST
│ ⦏ManyOne⦎ : ('a → 'b → BOOL) → BOOL
├
│ ∀r⦁ ManyOne r ⇔ ∀x y z⦁ r x y ∧ r x z ⇒ y = z
■


\section{Type Definition Lemmas}

=GFT
⦏type_lemmas_thm2⦎ =
   ⊢ ∀ pred
     ⦁ (∃ f⦁ TypeDefn pred f)
         ⇒ (∃ abs rep
         ⦁ (∀ a⦁ abs (rep a) = a)
             ∧ (∀ r⦁ pred r ⇔ rep (abs r) = r)
             ∧ OneOne rep)

⦏type_defn_lemma1⦎ =
   ⊢ ∀ f g⦁ (∀ x⦁ f (g x) = x) ⇒ (∀ x y⦁ g x = g y ⇒ x = y)

⦏type_defn_lemma2⦎ =
   ⊢ ∀ p f g
     ⦁ (∀ x⦁ p x ⇒ f (g x) = x) ⇒ (∀ x y⦁ p x ∧ p y ⇒ g x = g y ⇒ x = y)
=TEX
=GFT
⦏type_defn_lemma3⦎ =
   ⊢ (∃ f⦁ TypeDefn (λ x⦁ T) f)
       ⇒ (∃ abs rep⦁ (∀ a⦁ abs (rep a) = a) ∧ (∀ r⦁ rep (abs r) = r))

⦏type_defn_lemma4⦎ =
   ⊢ ∀ pred
     ⦁ (∃ f⦁ TypeDefn pred f)
         ⇒ (∃ abs rep
         ⦁ (∀ a⦁ abs (rep a) = a)
             ∧ (∀ r⦁ pred r ⇔ rep (abs r) = r)
             ∧ OneOne rep
             ∧ (∀ a⦁ pred (rep a)))

⦏oneone_contrapos_lemma⦎ =
	⊢ OneOne f ⇒ (∀ x y⦁ ¬ x = y ⇒ ¬ f x = f y)
=TEX


\ignore{
=SML
set_goal([], ⌜∀ pred
     ⦁ (∃ f: 'a → 'b⦁ TypeDefn pred f)
         ⇒ (∃ abs (rep: 'a → 'b)
         ⦁ (∀ a⦁ abs (rep a) = a) ∧ (∀ r⦁ pred r ⇔ rep (abs r) = r)
	∧ OneOne rep)⌝);
a (REPEAT strip_tac THEN fc_tac [type_lemmas_thm]);
a (∃_tac ⌜abs⌝ THEN ∃_tac ⌜rep⌝
	THEN asm_rewrite_tac[get_spec ⌜OneOne⌝]
	THEN REPEAT strip_tac);
a (LEMMA_T ⌜abs (rep x1) = abs(rep x2)⌝
	(rewrite_thm_tac o (rewrite_rule[asm_rule ⌜∀ a⦁ abs (rep a) = a⌝]))
	THEN1 rewrite_tac[asm_rule ⌜rep x1 = rep x2⌝]);
val type_lemmas_thm2 = save_pop_thm "type_lemmas_thm2";

set_goal([], ⌜∀f g⦁ (∀x⦁f(g(x)) = x) ⇒ (∀x y⦁ g x = g y ⇒ x = y)⌝);
a (REPEAT strip_tac);
a (LEMMA_T ⌜f(g(x)) = f(g(y))⌝ ante_tac THEN1 rewrite_tac[asm_rule ⌜g x = g y⌝]
	THEN asm_rewrite_tac[]);
val type_defn_lemma1 = save_pop_thm "type_defn_lemma1";

set_goal([], ⌜∀p f g⦁ (∀x⦁ p x ⇒ f(g(x)) = x) ⇒ (∀x y⦁ p x ∧ p y ⇒ g x = g y ⇒ x = y)⌝);
a (REPEAT strip_tac);
a (LEMMA_T ⌜f(g(x)) = f(g(y))⌝ ante_tac THEN1 rewrite_tac[asm_rule ⌜g x = g y⌝]);
a (LEMMA_T ⌜f (g x) = x⌝ rewrite_thm_tac THEN1 asm_fc_tac[]);
a (LEMMA_T ⌜f (g y) = y⌝ rewrite_thm_tac THEN1 asm_fc_tac[]);
val type_defn_lemma2 = save_pop_thm "type_defn_lemma2";

set_goal([], ⌜(∃ f: 'a → 'b⦁ TypeDefn (λx⦁T) f)
         ⇒ ∃ abs (rep: 'a → 'b)⦁
	(∀ a⦁ abs (rep a) = a) ∧ (∀ r⦁ rep (abs r) = r)⌝);
a (REPEAT strip_tac);
a (fc_tac [type_lemmas_thm2]);
a (DROP_NTH_ASM_T 2 (asm_tac o (rewrite_rule[])));
a (∃_tac ⌜abs⌝ THEN ∃_tac ⌜rep⌝ THEN asm_rewrite_tac[]);
val type_defn_lemma3 = save_pop_thm "type_defn_lemma3";

set_goal([], ⌜∀ pred
     ⦁ (∃ f: 'a → 'b⦁ TypeDefn pred f)
         ⇒ ∀ a⦁ pred (rep a)⌝);
a (REPEAT strip_tac THEN fc_tac [type_lemmas_thm]);

set_goal([], ⌜∀ pred
     ⦁ (∃ f: 'a → 'b⦁ TypeDefn pred f)
         ⇒ (∃ abs (rep: 'a → 'b)⦁
	  (∀ a⦁ abs (rep a) = a)
	∧ (∀ r⦁ pred r ⇔ rep (abs r) = r)
	∧ OneOne rep
	∧ ∀ a⦁ pred (rep a))⌝);
a (REPEAT strip_tac THEN fc_tac [type_lemmas_thm]);
a (∃_tac ⌜abs⌝ THEN ∃_tac ⌜rep⌝
	THEN asm_rewrite_tac[get_spec ⌜OneOne⌝]
	THEN REPEAT strip_tac);
a (LEMMA_T ⌜abs (rep x1) = abs(rep x2)⌝
	(rewrite_thm_tac o (rewrite_rule[asm_rule ⌜∀ a⦁ abs (rep a) = a⌝]))
	THEN1 rewrite_tac[asm_rule ⌜rep x1 = rep x2⌝]);
val type_defn_lemma4 = save_pop_thm "type_defn_lemma4";

set_goal([], ⌜∀f⦁ OneOne f ⇒ ∀x y⦁ ¬ x = y ⇒ ¬ f x = f y⌝);
a (strip_tac THEN rewrite_tac [get_spec ⌜OneOne⌝] THEN contr_tac);
a (asm_fc_tac[]);
val oneone_contrapos_lemma = save_pop_thm "oneone_contrapos_lemma";
=TEX
}%ignore

\section{Sets}

\subsection{Pairwise Disjointness}

Here is a definition of ``Pairwise disjoint''.

ⓈHOLCONST
│ $⦏PDisj⦎: 'a  SET SET → BOOL
├──────
│ ∀ss⦁ PDisj ss ⇔ ¬ ∃t u⦁ {t; u} ⊆ ss ∧ ¬ t = u ∧ ¬ t ∩ u = {} 
■

\subsection{Transitivity of Inclusion}

=GFT
⦏⊆_trans_thm⦎ = ⊢ ∀ A B C⦁ A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C
=TEX

\ignore{
=SML
val ⊆_trans_thm = save_thm ("⊆_trans_thm", pc_rule1 "hol1" prove_rule []
	⌜∀A B C⦁ A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C⌝);
=TEX
}%ignore

\subsection{Singleton Subsets}

=GFT
⦏singleton_subset_lemma⦎ =
   ⊢ ∀ x v⦁ {x} ⊆ V ⇔ x ∈ V
=TEX

\ignore{
=SML
set_goal ([], ⌜∀V x⦁ {x} ⊆ V ⇔ x ∈ V⌝);
a (PC_T1 "hol1" prove_tac[]);
val singleton_subset_lemma = save_pop_thm "singleton_subset_lemma";
=TEX
}%ignore

\subsection{Image of a Set under a Function}

ⓈHOLCONST
│ ⦏FunImage⦎: ('a → 'b) → 'a SET → 'b SET
├──────
│ ∀f A⦁ FunImage f A = {b | ∃a⦁ a ∈ A ∧ f a = b}
■

=GFT
⦏FunImage_o_thm⦎ =
	⊢ ∀ A f g⦁ FunImage (f o g) A = FunImage f (FunImage g A)

⦏FunImage_mono_thm⦎ =
	⊢ ∀ A B f⦁ A ⊆ B ⇒ FunImage f A ⊆ FunImage f B
=TEX

\ignore{
=SML
val FunImage_def = get_spec ⌜FunImage⌝;

set_goal([], ⌜∀A f g⦁ FunImage (f o g) A = FunImage f (FunImage g A)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [FunImage_def, sets_ext_clauses] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜g a⌝ THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (∃_tac ⌜a⌝ THEN REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac[o_def]);
(* *** Goal "2" *** *)
a (∃_tac ⌜a'⌝ THEN asm_rewrite_tac[o_def]);
val FunImage_o_thm = save_pop_thm "FunImage_o_thm";

set_goal([], ⌜∀A B (f:'a → 'b)⦁ A ⊆ B ⇒ FunImage f A ⊆ FunImage f B⌝);
a (REPEAT ∀_tac THEN rewrite_tac [FunImage_def, sets_ext_clauses] THEN REPEAT strip_tac);
a (∃_tac ⌜a⌝ THEN REPEAT strip_tac);
a (asm_fc_tac[]);
val FunImage_mono_thm = save_pop_thm "FunImage_mono_thm";
=TEX
}%ignore

\subsection{Set Displays}

The following are introduced to facilitate reasoning about sets of truth values below.

=GFT
⦏insert_com_thm⦎ = 
	⊢ ∀ x y z⦁ Insert x (Insert y z) = Insert y (Insert x z)

⦏insert_twice_thm⦎ =
	⊢ ∀ x y⦁ Insert x (Insert x y) = Insert x y
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y z⦁ Insert x (Insert y z) = Insert y (Insert x z)⌝);
a (rewrite_tac [sets_ext_clauses, get_spec ⌜Insert⌝] THEN REPEAT strip_tac);
val insert_com_thm = save_pop_thm "insert_com_thm";

set_goal([], ⌜∀x y⦁ Insert x (Insert x y) = (Insert x y)⌝);
a (rewrite_tac [sets_ext_clauses, get_spec ⌜Insert⌝] THEN REPEAT strip_tac);
val insert_twice_thm = save_pop_thm "insert_twice_thm";
=TEX
}%ignore

\ignore{
=SML
add_pc_thms "'rbjmisc" (map get_spec [] @ [singleton_subset_lemma, insert_twice_thm]);
set_merge_pcs ["basic_hol1", "'sets_alg", "'ℝ", "'rbjmisc"];
=TEX
}%ignore

=GFT
∈_disp_⇒_thm =
	⊢ ∀p d s⦁ (∀ e⦁ e ∈ Insert d s ⇒ p e) ⇔ p d ∧ ∀ e⦁ e ∈ s ⇒ p e
=TEX

\ignore{
=SML
set_goal([], ⌜∀p d s⦁ (∀e⦁ e ∈ Insert d s ⇒ p e) ⇔ p d ∧ ∀e⦁ e ∈ s ⇒ p e⌝);
a (REPEAT ∀_tac THEN rewrite_tac [insert_def] THEN REPEAT strip_tac THEN asm_fc_tac[]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜d⌝);
(* *** Goal "2" *** *)
a (asm_rewrite_tac []);
val ∈_disp_⇒_thm = save_pop_thm "∈_disp_⇒_thm";
=TEX
}%ignore

A conversion to apply ∈\_disp\_⇒\_thm (because we don't have higher order rewriting).

=SML
val ⦏∈_disp_⇒_conv⦎:CONV = fn t =>
	let val (e, body) = dest_∀ t;
	    val (lh, rh) = dest_⇒ body;
	    val (_, [vare, ins]) = strip_app lh;
	    val (_, [d, s]) = strip_app ins
	    val p = mk_λ (vare, rh);
	    val equiv = conv_rule (LEFT_C(SIMPLE_BINDER_C(RIGHT_C β_conv))) (list_∀_elim [p, d, s] ∈_disp_⇒_thm)
	in equiv
	end handle _ => fail_conv t;

val ⦏∈_disp_⇒_tac⦎ = conv_tac (MAP_C ∈_disp_⇒_conv);
=TEX

\subsection{NESET - A Type of Non-Empty Sets}

=SML
new_type_defn (["NESET"], "NESET", ["'a"],
	tac_proof (([], ⌜∃x:'a ℙ⦁ (λy⦁ ∃z⦁ z ∈ y) x⌝),
	∃_tac ⌜{εx:'a⦁T}⌝ THEN rewrite_tac [] THEN ∃_tac ⌜εx:'a⦁T⌝ THEN rewrite_tac[]) );
=TEX

\ignore{
=SML
set_goal([], ⌜∃(NeSet: 'a ℙ → 'a NESET) (PeSet : 'a NESET → 'a ℙ)⦁
	(∀x⦁ ∃y⦁ y ∈ PeSet x)
	∧ (∀x y⦁ x = y ⇔ ∀z⦁ z ∈ PeSet x ⇔ z ∈ PeSet y)
	∧ (∀x y⦁ x ∈ y ⇒ PeSet (NeSet y) = y)
	∧ (∀y⦁ NeSet (PeSet y) = y)⌝);
a (strip_asm_tac (get_defn "-" "NESET"));
a (fc_tac [type_lemmas_thm2]);
a (lemma_tac ⌜∀ r z⦁ z ∈ r ⇒ rep (abs r) = r⌝
	THEN1 (REPEAT strip_tac));
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 3 ⌜r⌝
		THEN_TRY asm_fc_tac[]
		THEN (DROP_NTH_ASM_T 2 ante_tac)
		THEN rewrite_tac[] THEN strip_tac THEN asm_fc_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜abs⌝ THEN ∃_tac ⌜rep⌝ THEN asm_rewrite_tac [] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac THEN asm_fc_tac[] THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜rep(abs(rep x)) = rep x⌝
	THEN1 asm_rewrite_tac[]);
a (spec_nth_asm_tac 4 ⌜rep x⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (fc_tac [get_spec ⌜OneOne⌝]);
a (POP_ASM_T (strip_asm_tac o (rewrite_rule [])));
a (lemma_tac ⌜rep x = rep y⌝ THEN1 fc_tac [map_eq_sym_rule sets_ext_clauses]);
a (asm_fc_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏NeSet⦎ : 'a ℙ → 'a NESET;
│ ⦏PeSet⦎ : 'a NESET → 'a ℙ
├───────────
│	  (∀x⦁ ∃y⦁ y ∈ PeSet x)
│	∧ (∀x y⦁ x = y ⇔ ∀z⦁ z ∈ PeSet x ⇔ z ∈ PeSet y)
│	∧ (∀x y⦁ x ∈ y ⇒ PeSet (NeSet y) = y)
│	∧ (∀y⦁ NeSet (PeSet y) = y)
■

=GFT
⦏NeSet_ne_thm⦎ =
	⊢ ∀ x⦁ ∃ y⦁ y ∈ PeSet x
⦏NeSet_ext_thm⦎ =
	⊢ ∀ x y⦁ x = y ⇔ (∀ z⦁ z ∈ PeSet x ⇔ z ∈ PeSet y)
⦏NeSet_fc_thm⦎ =
	⊢ ∀ x y⦁ x ∈ y ⇒ PeSet (NeSet y) = y
⦏NeSet_PeSet_thm⦎ =
	⊢ ∀ y⦁ NeSet (PeSet y) = y
=TEX

\ignore{
=SML
val [NeSet_ne_thm, NeSet_ext_thm, NeSet_fc_thm, NeSet_PeSet_thm] = strip_∧_rule (get_spec ⌜NeSet⌝);
=TEX
}%ignore

=GFT
⦏PeSet_Insert_thm⦎ =
	⊢ ∀ x y⦁ PeSet (NeSet (Insert x y)) = Insert x y
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y⦁ PeSet(NeSet(Insert x y)) = (Insert x y)⌝);
a (REPEAT strip_tac);
a (bc_tac [list_∀_elim [⌜x⌝, ⌜Insert x y⌝] NeSet_fc_thm]);
a (rewrite_tac [get_spec ⌜Insert⌝]);
val PeSet_Insert_thm = save_pop_thm "PeSet_Insert_thm";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏MemOf⦎ : 'a NESET → 'a
├───────────
│	∀x⦁ MemOf x = εy⦁ y ∈ PeSet x 
■

=GFT
⦏MemOf_memof_thm⦎ =
	⊢ ∀ x⦁ MemOf x ∈ PeSet x
⦏MemOf_NeSet_unit_thm⦎ =
	⊢ ∀ x⦁ MemOf (NeSet {x}) = x
=TEX

\ignore{
=SML
set_goal([], ⌜∀x⦁ MemOf x ∈ PeSet x⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜MemOf⌝]);
a (ε_tac ⌜ε y⦁ y ∈ PeSet x⌝);
a (rewrite_tac [NeSet_ne_thm]);
val MemOf_memof_thm = save_pop_thm "MemOf_memof_thm";

val MemOf_NeSet_unit_thm = save_thm ("MemOf_NeSet_unit_thm",
	all_∀_intro (rewrite_rule [PeSet_Insert_thm] (∀_elim ⌜NeSet {x}⌝ MemOf_memof_thm)));
=TEX
}%ignore

=SML
add_pc_thms1 "'rbjmisc" [NeSet_ne_thm];
add_pc_thms "'rbjmisc" [NeSet_PeSet_thm, MemOf_memof_thm, PeSet_Insert_thm, MemOf_NeSet_unit_thm];
=TEX


\subsection{Cantor's Theorem}

Presumably there is a proof of this somewhere but here is another.

The following is a record of a proof session with ProofPower in which the Cantor's theorem is proven.
The logic is very close to that of Principia Mathematica\cite{russell10}, being based on Church's formulation\cite{church40} of the Simple Theory of Types (which is more or less equivalent to Russell's Theory of Types \cite{russell08} once the ramifications have been neutralised by the axiom of reducibility).

The interactive proof tool effectively checks a formal proof which it has constructed behind the scenes following instructions from the user of the system, but does not display the full details of the proof (complete automation is the ideal, which we approach from afar).
The user gives his instructions in a language called `Standard ML' (in the passages headed `SML') in which the `ML' stands for `Meta-Language', the sections marked `{\Product} output' show the output from the proof tool.
The proof is conducted using a `goal package' (a bit of software written in SML) which supports a backward proof idiom in which the proof begins with the conjecture to be proven, and simplifies this conjecture by reverse application of rules until we reach axiomatic premises.
Behind the scenes the proof tool verifies the existence of a forward proof from axioms to the desired theorem. 

The proof is begun by stating the goal (conjecture) to be proven, which is that there does not exist a function from a type ⓣ'a⌝ onto the type ⓣ'a SET⌝ (in which $'a$ is a type variable).

=SML
set_goal([], ⌜¬ ∃f:'a → 'a SET⦁ ∀s:'a SET⦁ ∃e:'a⦁ f e = s⌝);
=TEX

=GFT ProofPower output
(* *** Goal "" *** *)

(* ?⊢ *)  ⌜¬ (∃ f⦁ ∀ s⦁ ∃ e⦁ f e = s)⌝
=TEX

By the most routine transformations:

=SML
a (REPEAT strip_tac);
=TEX

we get (showing some intermediate steps):

=GFT ProofPower output
(* ?⊢ *)  ⌜∀ f⦁ ¬ (∀ s⦁ ∃ e⦁ f e = s)⌝

(* ?⊢ *)  ⌜¬ (∀ s⦁ ∃ e⦁ f e = s)⌝

(* ?⊢ *)  ⌜∃ s⦁ ¬ (∃ e⦁ f e = s)⌝
=TEX

Which is asking for a counterexample to the supposition that $f$ is a surjection.

The required counterexample is supplied thus:

=SML
a (∃_tac ⌜{x | ¬ x ∈ f x }⌝);
=TEX

and we then have to prove that it is indeed a counterexample:

=GFT ProofPower output
(* ?⊢ *)  ⌜¬ (∃ e⦁ f e = {x|¬ x ∈ f x})⌝
=TEX

which again involves first some routine inferences:

=SML
a (REPEAT strip_tac);
=TEX

which goes:

=GFT ProofPower output
(* ?⊢ *)  ⌜∀ e⦁ ¬ f e = {x|¬ x ∈ f x}⌝

(* ?⊢ *)  ⌜¬ f e = {x|¬ x ∈ f x}⌝
=TEX

To progress this proof we now must use extensionality of sets transforming the equation into an equivalence by rewriting.

=SML
a (rewrite_tac [sets_ext_clauses]);
=TEX

Which gives:

=GFT ProofPower output
(* ?⊢ *)  ⌜¬ (∀ x⦁ x ∈ f e ⇔ ¬ x ∈ f x)⌝
=TEX

which is too obvious for us to care how it is discharged!

=SML
a (prove_tac []);
=TEX

=GFT ProofPower output
Tactic produced 0 subgoals:
Current and main goal achieved
=TEX

We now have a theorem, which we can save in our theory:

=SML
val cantors_thm = save_pop_thm "cantors_thm";
=TEX

=GFT ProofPower output
val cantors_thm = ⊢ ¬ (∃ f⦁ ∀ s⦁ ∃ e⦁ f e = s) : THM
=TEX

\section{Type OPT}

=SML
set_merge_pcs ["hol1", "'rbjmisc"];

new_type_defn (["OPT"], "OPT", ["'a"],
	tac_proof (([], ⌜∃x:'a+ONE⦁ (λy⦁T) x⌝), ∃_tac ⌜InR One⌝ THEN rewrite_tac []) );
=TEX

To make use of the type abbreviation `OPT' more readable the following constants are introduced:

\ignore{
=SML
set_goal([], ⌜∃(Value:'a → 'a OPT) Undefined⦁
	OneOne Value
	∧ (∀x⦁ ¬ Value x = Undefined)
	∧ (∀y⦁ y = Undefined ∨ (∃z⦁ y = Value z))⌝);
a (strip_asm_tac (get_defn "-" "OPT"));
a (fc_tac [type_lemmas_thm2]);
a (DROP_NTH_ASM_T 2 (asm_tac o (rewrite_rule[])));
a (fc_tac [get_spec ⌜OneOne⌝] THEN POP_ASM_T (asm_tac o rewrite_rule[]));
a (∃_tac ⌜λx⦁ abs (InL x)⌝ THEN ∃_tac ⌜abs (InR One)⌝ THEN rewrite_tac [] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac[ get_spec ⌜OneOne⌝] THEN REPEAT strip_tac);
a (lemma_tac ⌜rep(abs(InL x1)) = rep(abs(InL x2))⌝ THEN1 rewrite_tac[asm_rule ⌜abs (InL x1) = abs (InL x2)⌝]);
a (POP_ASM_T (asm_tac o (rewrite_rule [asm_rule ⌜∀ r⦁ rep (abs r) = r⌝])));
a strip_tac;
(* *** Goal "2" *** *)
a (contr_tac);
a (LEMMA_T ⌜rep(abs(InL x)) = rep(abs(InR One))⌝ (strip_asm_tac o (rewrite_rule [asm_rule ⌜∀ r⦁ rep (abs r) = r⌝]))
	THEN1 rewrite_tac[asm_rule ⌜abs (InL x) = abs (InR One)⌝]);
(* *** Goal "3" *** *)
a (strip_asm_tac (∀_elim ⌜rep y⌝ sum_cases_thm));
(* *** Goal "3.1" *** *)
a (∃_tac ⌜y'⌝ THEN rewrite_tac [map_eq_sym_rule (asm_rule ⌜rep y = InL y'⌝), asm_rule ⌜∀ a⦁ abs (rep a) = a⌝]);
(* *** Goal "3.2" *** *)
a (LEMMA_T ⌜z = One⌝ asm_tac THEN1 rewrite_tac[]);
a (var_elim_asm_tac ⌜z = One⌝);
a (lemma_tac ⌜abs(rep(y)) = abs(InR One)⌝ THEN1 rewrite_tac[asm_rule ⌜rep y = InR One⌝]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Value⦎ : 'a → 'a OPT;
│ ⦏Undefined⦎ : 'a OPT
├───────────
│ OneOne Value
│	∧ (∀x⦁ ¬ Value x = Undefined)
│	∧ (∀y⦁ y = Undefined ∨ (∃z⦁ y = Value z))
■

=GFT
⦏opt_cases_thm⦎ =
   ⊢ ∀ x⦁ x = Undefined ∨ (∃ y⦁ x = Value y)

⦏value_not_undefined_lemma⦎ =
   ⊢ ∀ x⦁ ¬ Value x = Undefined ∧ ¬ Undefined = Value x
=TEX

\ignore{
=SML
set_goal([], ⌜∀x⦁ x = Undefined ∨ (∃y⦁ x = Value y)⌝);
a strip_tac;
a (strip_asm_tac (get_spec ⌜Value⌝));
a (spec_nth_asm_tac 1 ⌜x⌝ THEN_TRY asm_rewrite_tac[]);
val opt_cases_thm = save_pop_thm "opt_cases_thm";

set_goal([], ⌜∀x⦁ ¬ Value x = Undefined ∧ ¬ Undefined = Value x⌝);
a (strip_tac);
a (strip_asm_tac (get_spec ⌜Value⌝)
	THEN asm_rewrite_tac[]
	THEN SYM_ASMS_T rewrite_tac);
val value_not_undefined_lemma = save_pop_thm "value_not_undefined_lemma";

set_goal([], ⌜∀x y⦁ Value x = Value y ⇔ x = y⌝);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (strip_asm_tac (rewrite_rule [get_spec ⌜OneOne⌝] (get_spec ⌜Value⌝))
	THEN asm_fc_tac[]);
val value_oneone_lemma = save_pop_thm "value_oneone_lemma";

set_goal([], ⌜∃ValueOf: 'a OPT → 'a⦁ ∀v⦁ ValueOf (Value v) = v⌝);
a (∃_tac ⌜λx⦁ ε y⦁ Value y = x⌝ THEN rewrite_tac[get_spec ⌜Value⌝]
	THEN strip_tac);
a (ε_tac ⌜ε y⦁ Value y = Value v⌝);
a (∃_tac ⌜v⌝ THEN rewrite_tac[]);
a (strip_asm_tac (get_spec ⌜Value⌝));
a (fc_tac [get_spec ⌜OneOne⌝]);
a (POP_ASM_T ante_tac THEN rewrite_tac[] THEN strip_tac);
a (all_asm_fc_tac []);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏ValueOf⦎ : 'a OPT → 'a
├───────────
│ ∀v⦁ ValueOf (Value v) = v
■

ⓈHOLCONST
│ ⦏IsDefined⦎ : 'a OPT → BOOL
├───────────
│ ∀v⦁ IsDefined v ⇔ ¬ v = Undefined
■

\subsection{Proof Contexts}

=SML
add_pc_thms "'rbjmisc" (map get_spec [⌜IsDefined⌝, ⌜ValueOf⌝] @
	[value_not_undefined_lemma, value_oneone_lemma]);
set_merge_pcs ["basic_hol1", "'sets_alg", "'ℝ", "'rbjmisc"];
=TEX

\section{Lists}

\subsection{List Membership}

=SML
declare_infix(300, "∈⋎L");
=TEX

ⓈHOLCONST
│ $⦏∈⋎L⦎: 'a → 'a  LIST → BOOL
├──────
│ ∀ a b al⦁ (a ∈⋎L [] ⇔ F)
│	∧ (a ∈⋎L (Cons b al) ⇔ a = b ∨ a ∈⋎L al)
■

\subsection{Quantification}

ⓈHOLCONST
│ ⦏∀⋎L⦎: BOOL LIST → BOOL
├──────
│ ∀ bl⦁ ∀⋎L bl = Fold $∧ bl T
■

ⓈHOLCONST
│ ⦏∃⋎L⦎: BOOL LIST → BOOL
├──────
│ ∀ bl⦁ ∃⋎L bl = Fold $∨ bl F
■

=GFT
⦏∀⋎L_thm⦎ =
   ⊢ (∀⋎L [] ⇔ T) ∧ (∀h list⦁ ∀⋎L (Cons h list) ⇔ h ∧ ∀⋎L list)

⦏∃⋎L_thm⦎ =
   ⊢ (∃⋎L [] ⇔ F) ∧ (∀ h list⦁ ∃⋎L (Cons h list) ⇔ h ∨ ∃⋎L list)

⦏∀⋎L_clauses⦎ =
   ⊢ ∀⋎L [] ⇔ T ∧ (∀ t⦁ ∀⋎L (Cons T t) ⇔ ∀⋎L t) ∧ (∀ t⦁ ∀⋎L (Cons F t) ⇔ F)

⦏∃⋎L_clauses⦎ =
   ⊢ ∃⋎L [] ⇔ F ∧ (∀ t⦁ ∃⋎L (Cons F t) ⇔ ∃⋎L t) ∧ (∀ t⦁ ∃⋎L (Cons T t) ⇔ T)

⦏∀⋎L_append_thm⦎ =
   ⊢ ∀ l m⦁ ∀⋎L (l ⁀ m) ⇔ ∀⋎L l ∧ ∀⋎L m

⦏∃⋎L_append_thm⦎ =
   ⊢ ∀ l m⦁ ∃⋎L (l ⁀ m) ⇔ ∃⋎L l ∨ ∃⋎L m
=TEX

\ignore{
=SML
val ∀⋎L_def= get_spec ⌜∀⋎L⌝;
val ∃⋎L_def= get_spec ⌜∃⋎L⌝;

set_goal([], ⌜(∀⋎L [] ⇔ T)
       ∧ (∀h list⦁ ∀⋎L (Cons h list) ⇔ h ∧ ∀⋎L list)⌝);
a (rewrite_tac [∀⋎L_def, fold_def]);
val ∀⋎L_thm = save_pop_thm "∀⋎L_thm";

set_goal([], ⌜(∃⋎L [] ⇔ F)
       ∧ (∀h list⦁ ∃⋎L (Cons h list) ⇔ h ∨ ∃⋎L list)⌝);
a (rewrite_tac [∃⋎L_def, fold_def]);
val ∃⋎L_thm = save_pop_thm "∃⋎L_thm";

set_goal([], ⌜(∀⋎L [] ⇔ T)
	∧ (∀t⦁ ∀⋎L (Cons T t) ⇔ ∀⋎L t)
	∧ (∀t⦁ ∀⋎L (Cons F t) ⇔ F)
	∧ (∀h⦁ ∀⋎L [h] ⇔ h)⌝);
a (rewrite_tac [∀⋎L_def, fold_def] THEN REPEAT strip_tac);
val ∀⋎L_clauses = save_pop_thm "∀⋎L_clauses";

set_goal([], ⌜(∃⋎L [] ⇔ F)
	∧ (∀t⦁ ∃⋎L (Cons F t) ⇔ ∃⋎L t)
	∧ (∀t⦁ ∃⋎L (Cons T t) ⇔ T)
	∧ (∀h⦁ ∃⋎L [h] ⇔ h)
	∧ (∀h⦁ ∃⋎L [h] ⇔ h)⌝);
a (rewrite_tac [∃⋎L_def, fold_def] THEN REPEAT strip_tac);
val ∃⋎L_clauses = save_pop_thm "∃⋎L_clauses";

set_goal([],⌜ (∀l m⦁ ∀⋎L (Append l m) ⇔ (∀⋎L l ∧ ∀⋎L m))⌝);
a (REPEAT ∀_tac);
a (list_induction_tac ⌜l⌝ THEN strip_tac THEN asm_rewrite_tac[append_def, ∀⋎L_thm]);
val ∀⋎L_append_thm = save_pop_thm "∀⋎L_append_thm";

set_goal([],⌜ (∀l m⦁ ∃⋎L (Append l m) ⇔ (∃⋎L l ∨ ∃⋎L m))⌝);
a (REPEAT ∀_tac);
a (list_induction_tac ⌜l⌝ THEN strip_tac THEN asm_rewrite_tac[append_def, ∃⋎L_thm]);
val ∃⋎L_append_thm = save_pop_thm "∃⋎L_append_thm";
=TEX
}%ignore

\subsection{Proof Contexts}

=SML
add_pc_thms "'rbjmisc" (map get_spec [⌜$∈⋎L⌝] @
	[∀⋎L_clauses, ∃⋎L_clauses, ∀⋎L_thm, ∃⋎L_thm, ∀⋎L_append_thm, ∃⋎L_append_thm]);
set_merge_pcs ["basic_hol1", "'sets_alg", "'ℝ", "'rbjmisc"];
=TEX

\subsection{Mapping Constructors}

The idea here is to facilitate the construction of a list of objects of some kind (typically a HOL labelled product), given a curried constructor and lists of the operands.
We will need a different one for each arity of constructor, so I will use a numeric suffix.

ⓈHOLCONST
│ ⦏MapCf⋎2⦎: ('a → 'b → 'c) → 'a LIST → 'b LIST → 'c LIST
├──────
│ ∀ cf al bl⦁  MapCf⋎2 cf al bl = Map (Uncurry cf) (Combine al bl)
■

ⓈHOLCONST
│ ⦏MapCf⋎3⦎: ('a → 'b → 'c → 'd) → 'a LIST → 'b LIST → 'c LIST → 'd LIST
├──────
│ ∀ cf al bl cl⦁  MapCf⋎3 cf al bl cl =
	Map (Uncurry (Uncurry cf)) (Combine (Combine al bl) cl)
■

\subsection{Liberal Combine}

This is a combine function which ``works'' with lists of different lengths.

ⓈHOLCONST
│ ⦏Combine2⦎: 'a LIST → 'b LIST → ('a × 'b) LIST
├──────
│   (∀b⦁  Combine2 [] b = [])
│ ∧ (∀a⦁  Combine2 a [] = [])
│ ∧ (∀ha ta hb tb⦁ Combine2 (Cons ha ta) (Cons hb tb) = Cons (ha, hb) (Combine2 ta tb))
■


\subsection{Lists of Sets}

ⓈHOLCONST
│ ⦏List2Set⦎: 'a LIST → 'a SET
├──────
│ ∀l⦁ List2Set l = {e | e ∈⋎L l}
■
ⓈHOLCONST
│ ⦏ListUnion⦎: 'a SET LIST → 'a SET
├──────
│ ∀l⦁ ListUnion l = ⋃ (List2Set l)
■
ⓈHOLCONST
│ ⦏ListFunUnion⦎: ('a SET → 'a SET) LIST → ('a SET → 'a SET)
├──────
│ ∀l as⦁ ListFunUnion l as = ListUnion (Map (λf⦁ f as) l)
■

=GFT
⦏ListUnion_thm⦎ =
   ⊢ ListUnion [] = {} ∧ (∀ h t⦁ ListUnion (Cons h t) = h ∪ ListUnion t)
=TEX

\ignore{
=SML
set_goal([], ⌜ListUnion [] = {} ∧ ∀h t⦁ ListUnion (Cons h t) = h ∪ (ListUnion t)⌝);
a (rewrite_tac ((map get_spec [⌜ListUnion⌝, ⌜Fold⌝, ⌜List2Set⌝, ⌜$∈⋎L⌝])@[sets_ext_clauses])
	THEN REPEAT strip_tac THEN_TRY (all_asm_fc_tac[]));
(* *** Goal "1" *** *)
a ( ∃_tac ⌜s⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a ( ∃_tac ⌜h⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a ( ∃_tac ⌜s⌝ THEN asm_rewrite_tac[]);
val ListUnion_thm = save_pop_thm "ListUnion";
=TEX
}%ignore

\subsection{Lists of Natural Numbers}

A function for making a list of ascending natural numbers.

=SML
declare_infix (300, "..⋎L");
=TEX
ⓈHOLCONST
│ $⦏..⋎L⦎: ℕ → ℕ → ℕ LIST
├──────
│ ∀ x y⦁ x ..⋎L 0 = []
│ ∧ x ..⋎L (y + 1) = if x ≤ y then (x ..⋎L y) @ [y+1] else []
■

\section{Natural Numbers and Arithmetic}

\subsection{Primitive Recursion}

=GFT
⦏prim_rec_thm2⦎ = ⊢ ∀ z s⦁ ∃ f⦁ f 0 = z ∧ (∀ n⦁ f (n + 1) = s (f n) n)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ z s⦁ ∃ f⦁ f 0 = z ∧ (∀ n⦁ f (n + 1) = s (f n) n)⌝);
a (strip_asm_tac (conv_rule (MAP_C ∃⋎1_conv) prim_rec_thm));
a (REPEAT strip_tac);
a (list_spec_nth_asm_tac 1 [⌜z⌝, ⌜s⌝]);
a (∃_tac ⌜f⌝ THEN asm_rewrite_tac[]);
val prim_rec_thm2 = save_pop_thm "prim_rec_thm2";
=TEX
}%ignore


\section{Real Numbers and Analysis}

\subsection{Products}
=GFT
ℝ_prod_sign_iff_clauses 
⊢ (∀ x y⦁ ℕℝ 0 <R x *⋎R y		⇔ ℕℝ 0 <⋎R x ∧ ℕℝ 0 <⋎R y ∨ x <⋎R ℕℝ 0 ∧ y <⋎R ℕℝ 0)
∧ (∀ x y⦁ x *⋎R y <⋎R ℕℝ 0		⇔ ℕℝ 0 <⋎R x ∧ y <⋎R ℕℝ 0 ∨ x <⋎R ℕℝ 0 ∧ ℕℝ 0 <⋎R y)
∧ (∀ x y⦁ ℕℝ 0 ≤⋎R x *⋎R y		⇔ ℕℝ 0 ≤⋎R x ∧ ℕℝ 0 ≤⋎R y ∨ x ≤⋎R ℕℝ 0 ∧ y ≤⋎R ℕℝ 0)
∧ (∀ x y⦁ x *⋎R y ≤⋎R ℕℝ 0		⇔ ℕℝ 0 ≤⋎R x ∧ y ≤⋎R ℕℝ 0 ∨ x ≤⋎R ℕℝ 0 ∧ ℕℝ 0 ≤⋎R y)
∧ (∀ x y⦁ x *⋎R y = ℕℝ 0		⇔ x = ℕℝ 0 ∨ y = ℕℝ 0)
∧ (∀ x y⦁ ℕℝ 0 = x *⋎R y		⇔ x = ℕℝ 0 ∨ y = ℕℝ 0)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ x y⦁
	(ℕℝ 0 <⋎R x ∧ ℕℝ 0 <⋎R y ⇒ ℕℝ 0 <⋎R x *⋎R y)
	∧ (x <⋎R ℕℝ 0 ∧ y <⋎R ℕℝ 0 ⇒ ℕℝ 0 <⋎R x *⋎R y)
	∧ (x <⋎R ℕℝ 0 ∧ ℕℝ 0 <⋎R y ⇒ x *⋎R y <⋎R ℕℝ 0)
	∧ (ℕℝ 0 <⋎R x ∧ y <⋎R ℕℝ 0 ⇒ x *⋎R y <⋎R ℕℝ 0)
	∧ (x = ℕℝ 0 ∨ y = ℕℝ 0 ⇒ x *⋎R y = ℕℝ 0)
⌝);
a (REPEAT strip_tac
	THEN TRY (asm_rewrite_tac[]));
(* *** Goal "1" *** *)
a (all_asm_ufc_tac [ℝ_0_less_0_less_times_thm]);
(* *** Goal "2" *** *)
a (all_asm_ufc_tac [ℝ_less_0_less_thm]);
a (LEMMA_T ⌜ℕℝ 0 <⋎R (~⋎R x) *⋎R (~⋎R y)⌝ ante_tac
	THEN1 all_asm_ufc_tac [ℝ_0_less_0_less_times_thm]);
a (rewrite_tac[ℝ_times_minus_thm]);
(* *** Goal "3" *** *)
a (once_rewrite_tac [ℝ_less_0_less_thm]);
a (rewrite_tac[]);
a (lemma_tac ⌜ℕℝ 0 <⋎R (~⋎R x)⌝
	THEN1 (ALL_ASM_FC_T (MAP_EVERY ante_tac) [ℝ_less_0_less_thm]
		THEN rewrite_tac[]
		THEN REPEAT strip_tac));
a (all_asm_ufc_tac [ℝ_0_less_0_less_times_thm]);
a (lemma_tac ⌜~⋎R (x *⋎R y) = ~⋎R x *⋎R y⌝
	THEN1 (PC_T1 "ℝ_lin_arith" prove_tac[]));
a (asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (once_rewrite_tac [ℝ_less_0_less_thm]);
a (rewrite_tac[]);
a (lemma_tac ⌜ℕℝ 0 <⋎R (~⋎R y)⌝
	THEN1 (ALL_ASM_FC_T (MAP_EVERY ante_tac) [ℝ_less_0_less_thm]
		THEN rewrite_tac[]
		THEN REPEAT strip_tac));
a (all_asm_ufc_tac [ℝ_0_less_0_less_times_thm]);
a (lemma_tac ⌜~⋎R (x *⋎R y) = x *⋎R ~⋎R y⌝
	THEN1 (PC_T1 "ℝ_lin_arith" prove_tac[]));
a (asm_rewrite_tac[]);
val ℝ_product_sign_lemma = pop_thm ();
=TEX
=SML
set_goal([], ⌜∀ x y⦁
	(ℕℝ 0 <⋎R x *⋎R y ⇒ ℕℝ 0 <⋎R x ∧ ℕℝ 0 <⋎R y ∨ x <⋎R ℕℝ 0 ∧ y <⋎R ℕℝ 0)
	∧ (x *⋎R y <⋎R ℕℝ 0 ⇒ ℕℝ 0 <⋎R x ∧ y <⋎R ℕℝ 0 ∨ ℕℝ 0 <⋎R y ∧ x <⋎R ℕℝ 0)
	∧ (x *⋎R y = ℕℝ 0 ⇒ x = ℕℝ 0 ∨ y = ℕℝ 0)
⌝);
a contr_tac;
(* *** Goal "1" *** *)
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
a (DROP_NTH_ASM_T 4 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
(* *** Goal "2.1" *** *)
a (strip_asm_tac (list_∀_elim [⌜y⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
(* *** Goal "2.1.1" *** *)
a (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
a (all_asm_ufc_tac[ℝ_product_sign_lemma]);
a (all_asm_ufc_tac[ℝ_less_trans_thm]);
(* *** Goal "2.2" *** *)
a (DROP_NTH_ASM_T 4 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (strip_asm_tac (list_∀_elim [⌜y⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
(* *** Goal "3.1" *** *)
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
(* *** Goal "3.1.1" *** *)
a (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "3.1.2" *** *)
a (all_asm_ufc_tac[ℝ_product_sign_lemma]);
a (all_asm_ufc_tac[ℝ_less_trans_thm]);
(* *** Goal "3.2" *** *)
a (DROP_NTH_ASM_T 4 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (strip_asm_tac (list_∀_elim [⌜y⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
a (DROP_NTH_ASM_T 4 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "5" *** *)
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
(* *** Goal "5.1" *** *)
a (strip_asm_tac (list_∀_elim [⌜y⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
(* *** Goal "5.1.1" *** *)
a (all_asm_ufc_tac[ℝ_product_sign_lemma]);
a (all_asm_ufc_tac[ℝ_less_trans_thm]);
(* *** Goal "5.1.2" *** *)
a (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "5.2" *** *)
a (DROP_NTH_ASM_T 4 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "6" *** *)
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
a (DROP_NTH_ASM_T 4 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "7" *** *)
a (strip_asm_tac (list_∀_elim [⌜y⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
a (DROP_NTH_ASM_T 4 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "8" *** *)
a (strip_asm_tac (list_∀_elim [⌜y⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
(* *** Goal "8.1" *** *)
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
(* *** Goal "8.1.1" *** *)
a (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "8.1.2" *** *)
a (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "8.2" *** *)
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
(* *** Goal "8.2.1" *** *)
a (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "8.2.2" *** *)
a (all_asm_ufc_tac[ℝ_product_sign_lemma]);
a (all_asm_ufc_tac[ℝ_less_trans_thm]);
(* *** Goal "9" *** *)
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
(* *** Goal "9.1" *** *)
a (strip_asm_tac (list_∀_elim [⌜y⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
(* *** Goal "9.1.1" *** *)
a (all_asm_ufc_tac[ℝ_product_sign_lemma]);
a (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "9.1.2" *** *)
a (all_asm_ufc_tac[ℝ_product_sign_lemma]);
a (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "9.2" *** *)
a (strip_asm_tac (list_∀_elim [⌜y⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm));
(* *** Goal "9.2.1" *** *)
a (all_asm_ufc_tac[ℝ_product_sign_lemma]);
a (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "9.2.2" *** *)
a (all_asm_ufc_tac[ℝ_product_sign_lemma]);
a (DROP_NTH_ASM_T 5 ante_tac THEN asm_rewrite_tac[]);
val ℝ_product_sign_cp_lemma = pop_thm ();
=TEX
=SML
set_goal([], ⌜(∀ x y⦁ ℕℝ 0 <⋎R x *⋎R y ⇔ ℕℝ 0 <⋎R x ∧ ℕℝ 0 <⋎R y
		∨ x <⋎R ℕℝ 0 ∧ y <⋎R ℕℝ 0)
	∧ (∀ x y⦁ x *⋎R y <⋎R ℕℝ 0 ⇔ ℕℝ 0 <⋎R x ∧ y <⋎R ℕℝ 0
		∨ x <⋎R ℕℝ 0 ∧ ℕℝ 0 <⋎R y)
	∧ (∀ x y⦁ x *⋎R y = ℕℝ 0 ⇔ x = ℕℝ 0 ∨ y = ℕℝ 0)
	∧ (∀ x y⦁ ℕℝ 0 = x *⋎R y ⇔ x = ℕℝ 0 ∨ y = ℕℝ 0)⌝);
a (REPEAT strip_tac
	THEN TRY (asm_rewrite_tac [])
	THEN TRY (all_ufc_tac [ℝ_product_sign_lemma,
	ℝ_product_sign_cp_lemma]));
a (DROP_NTH_ASM_T 2 (asm_tac o (conv_rule eq_sym_conv))
	THEN ufc_tac [ℝ_product_sign_cp_lemma]
	THEN asm_rewrite_tac[]);
val ℝ_prod_sign_iff_lemma = pop_thm ();
=TEX
=SML
set_goal([], ⌜(∀ x y⦁ ℕℝ 0 ≤⋎R x *⋎R y ⇔ ℕℝ 0 ≤⋎R x ∧ ℕℝ 0 ≤⋎R y
		∨ x ≤⋎R ℕℝ 0 ∧ y ≤⋎R ℕℝ 0)
	∧ (∀ x y⦁ x *⋎R y ≤⋎R ℕℝ 0 ⇔ ℕℝ 0 ≤⋎R x ∧ y ≤⋎R ℕℝ 0
		∨ x ≤⋎R ℕℝ 0 ∧ ℕℝ 0 ≤⋎R y)
	∧ (∀ x y⦁ x *⋎R y = ℕℝ 0 ⇔ x = ℕℝ 0 ∨ y = ℕℝ 0)
	∧ (∀ x y⦁ ℕℝ 0 = x *⋎R y ⇔ x = ℕℝ 0 ∨ y = ℕℝ 0)⌝);
a (rewrite_tac [get_spec ⌜$≤⋎R⌝, ℝ_prod_sign_iff_lemma]);
a (REPEAT_N 6 strip_tac THEN TRY (asm_rewrite_tac[])
	THEN (PC_T1 "ℝ_lin_arith" prove_tac[]));
val ℝ_prod_sign_iff_lemma2 = pop_thm ();
=TEX
=SML
set_goal([], ⌜(∀ x y⦁ ℕℝ 0 <⋎R x *⋎R y ⇔ ℕℝ 0 <⋎R x ∧ ℕℝ 0 <⋎R y
		∨ x <⋎R ℕℝ 0 ∧ y <⋎R ℕℝ 0)
	∧ (∀ x y⦁ x *⋎R y <⋎R ℕℝ 0 ⇔ ℕℝ 0 <⋎R x ∧ y <⋎R ℕℝ 0
		∨ x <⋎R ℕℝ 0 ∧ ℕℝ 0 <⋎R y)
	∧ (∀ x y⦁ ℕℝ 0 ≤⋎R x *⋎R y ⇔ ℕℝ 0 ≤⋎R x ∧ ℕℝ 0 ≤⋎R y
		∨ x ≤⋎R ℕℝ 0 ∧ y ≤⋎R ℕℝ 0)
	∧ (∀ x y⦁ x *⋎R y ≤⋎R ℕℝ 0 ⇔ ℕℝ 0 ≤⋎R x ∧ y ≤⋎R ℕℝ 0
		∨ x ≤⋎R ℕℝ 0 ∧ ℕℝ 0 ≤⋎R y)
	∧ (∀ x y⦁ x *⋎R y = ℕℝ 0 ⇔ x = ℕℝ 0 ∨ y = ℕℝ 0)
	∧ (∀ x y⦁ ℕℝ 0 = x *⋎R y ⇔ x = ℕℝ 0 ∨ y = ℕℝ 0)⌝);
a (rewrite_tac [ℝ_prod_sign_iff_lemma, ℝ_prod_sign_iff_lemma2]
	THEN (PC_T1 "ℝ_lin_arith" prove_tac[]));
val ℝ_prod_sign_iff_clauses = save_pop_thm "ℝ_prod_sign_iff_clauses";
=TEX
}%ignore

\ignore{

=SML
set_goal([], ⌜∀ x y z⦁ ℕℝ 0 <⋎R x ∧ y <⋎R z ⇒ y *⋎R x <⋎R z *⋎R x⌝);
a (REPEAT strip_tac);
a (all_ufc_tac [ℝ_times_mono_thm]);
a (PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ℝ_times_mono_thm1 = save_pop_thm "ℝ_times_mono_thm1";
=TEX

=SML

set_goal([], ⌜∀ x y z⦁ ℕℝ 0 ≤⋎R x ∧ y ≤⋎R z ⇒ x *⋎R y ≤⋎R x *⋎R z⌝);
a (rewrite_tac [get_spec ⌜$≤⋎R⌝]
	THEN REPEAT strip_tac
	THEN TRY (asm_rewrite_tac[])
	THEN TRY (SYM_ASMS_T rewrite_tac)
	THEN TRY (all_ufc_tac
	[ℝ_times_mono_thm, ℝ_times_mono_thm1, ℝ_less_trans_thm]));
val ℝ_times_mono_thm2 = save_pop_thm "ℝ_times_mono_thm2";

set_goal([], ⌜∀ x y z⦁ ℕℝ 0 ≤⋎R x ∧ y ≤⋎R z ⇒ y *⋎R x ≤⋎R z *⋎R x⌝);
a (rewrite_tac [get_spec ⌜$≤⋎R⌝]
	THEN REPEAT strip_tac
	THEN TRY (asm_rewrite_tac[])
	THEN TRY (SYM_ASMS_T rewrite_tac)
	THEN TRY (all_ufc_tac
	[ℝ_times_mono_thm, ℝ_times_mono_thm1, ℝ_less_trans_thm]));
val ℝ_times_mono_thm3 = save_pop_thm "ℝ_times_mono_thm3";
=TEX

=SML
set_goal([], ⌜∀ w x y z⦁ ℕℝ 0 <⋎R w ∧ ℕℝ 0 <⋎R y ∧ w <⋎R x ∧ y <⋎R z ⇒ w *⋎R y <⋎R x *⋎R z⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜ℕℝ 0 <⋎R z ∧ ℕℝ 0 <⋎R x⌝
	THEN1 (all_asm_ufc_tac[ℝ_less_trans_thm])
	THEN REPEAT strip_tac);
a (lemma_tac ⌜w *⋎R y <⋎R w *⋎R z⌝
	THEN1 (all_asm_ufc_tac[ℝ_times_mono_thm, ℝ_times_mono_thm1, ℝ_less_trans_thm]));
a (lemma_tac ⌜w *⋎R z <⋎R x *⋎R z⌝
	THEN1 (strip_asm_tac (list_∀_elim [⌜z⌝, ⌜w⌝, ⌜x⌝] ℝ_times_mono_thm1)));
a (strip_asm_tac (list_∀_elim [⌜w *⋎R y⌝, ⌜w *⋎R z⌝, ⌜x *⋎R z⌝] ℝ_less_trans_thm));
val ℝ_times_mono_thm4 = save_pop_thm "ℝ_times_mono_thm4";
=TEX

=SML
set_goal([], ⌜∀ w x y z⦁ ℕℝ 0 ≤⋎R w ∧ ℕℝ 0 ≤⋎R y ∧ w ≤⋎R x ∧ y ≤⋎R z ⇒ w *⋎R y ≤⋎R x *⋎R z⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜ℕℝ 0 ≤⋎R z ∧ ℕℝ 0 ≤⋎R x⌝
	THEN1 (all_asm_ufc_tac[ℝ_≤_trans_thm])
	THEN REPEAT strip_tac);
a (lemma_tac ⌜w *⋎R y ≤⋎R w *⋎R z⌝
	THEN1 (all_asm_ufc_tac[ℝ_times_mono_thm2, ℝ_times_mono_thm3, ℝ_≤_trans_thm]));
a (lemma_tac ⌜w *⋎R z ≤⋎R x *⋎R z⌝
	THEN1 (strip_asm_tac (list_∀_elim [⌜z⌝, ⌜w⌝, ⌜x⌝] ℝ_times_mono_thm3)));
a (strip_asm_tac (list_∀_elim [⌜w *⋎R y⌝, ⌜w *⋎R z⌝, ⌜x *⋎R z⌝] ℝ_≤_trans_thm));
val ℝ_times_mono_thm5 = save_pop_thm "ℝ_times_mono_thm5";
=TEX
}%ignore

\subsection{Squares}

\ignore{
=SML
set_goal([], ⌜∀ x y⦁ ℕℝ 0 <⋎R x ∧ x <⋎R y ⇒ x *⋎R x <⋎R y *⋎R y⌝);
a (REPEAT strip_tac);
a (all_asm_ufc_tac [ℝ_less_trans_thm]);
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜y⌝, ⌜x⌝, ⌜y⌝] ℝ_times_mono_thm4));
val ℝ_square_mono_thm = save_pop_thm "ℝ_square_mono_thm";
=TEX

=SML
set_goal([], ⌜∀ x y⦁ ℕℝ 0 ≤⋎R x ∧ x ≤⋎R y ⇒ x *⋎R x ≤⋎R y *⋎R y⌝);
a (REPEAT strip_tac);
a (all_asm_ufc_tac [ℝ_≤_trans_thm]);
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜y⌝, ⌜x⌝, ⌜y⌝] ℝ_times_mono_thm5));
val ℝ_square_mono_thm1 = save_pop_thm "ℝ_square_mono_thm1";
=TEX

=SML
set_goal([], ⌜∀ x y z⦁ ℕℝ 0 <⋎R x ∧ ℕℝ 0 <⋎R y ∧ x *⋎R x <⋎R y *⋎R y ⇒ x <⋎R y⌝);
a (REPEAT strip_tac);
a (strip_asm_tac (all_∀_elim ℝ_less_cases_thm));
(* *** Goal "1" *** *)
a (DROP_ASM_T ⌜x *⋎R x <⋎R y *⋎R y⌝ ante_tac
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (strip_asm_tac (list_∀_elim [⌜y⌝, ⌜x⌝] ℝ_square_mono_thm));
a (all_ufc_tac [ℝ_less_antisym_thm]);
val ℝ_square_less_less_thm = save_pop_thm "ℝ_square_less_less_thm";
=TEX

-SML
set_goal([], ⌜∀ x y⦁ ℕℝ 0 <⋎R x ∧ ℕℝ 0 <⋎R y ⇒ (x *⋎R x <⋎R y *⋎R y ⇔ x <⋎R y)⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_ufc_tac [ℝ_square_less_less_thm]);
(* *** Goal "2" *** *)
a (all_ufc_tac [ℝ_square_mono_thm]);
val ℝ_square_less_iff_less_thm = save_pop_thm "ℝ_square_less_iff_less_thm";
=TEX

=SML
set_goal([], ⌜∀x y:ℝ⦁ ℕℝ 0 <⋎R x ∧ ℕℝ 0 <⋎R y ∧ y *⋎R y = x *⋎R x ⇒ x = y⌝);
a (REPEAT strip_tac);
a (strip_asm_tac (all_∀_elim ℝ_less_cases_thm)
	THEN (ufc_tac [ℝ_times_mono_thm]));
(* *** Goal "1" *** *)
a (lemma_tac ⌜x *⋎R x <⋎R x *⋎R y⌝
	THEN1 asm_ufc_tac []);
a (lemma_tac ⌜x *⋎R y <⋎R y *⋎R y⌝
	THEN1 all_ufc_tac [list_∀_elim [⌜y⌝, ⌜x⌝, ⌜y⌝] ℝ_times_mono_thm1]);
a (ALL_FC_T (MAP_EVERY ante_tac) [ℝ_less_trans_thm]
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜x *⋎R y <⋎R x *⋎R x⌝
	THEN1 asm_ufc_tac []);
a (lemma_tac ⌜y *⋎R y <⋎R x *⋎R y⌝
	THEN1 all_ufc_tac [list_∀_elim [⌜y⌝, ⌜y⌝, ⌜x⌝] ℝ_times_mono_thm1]);
a (ALL_FC_T (MAP_EVERY ante_tac) [ℝ_less_trans_thm]
	THEN asm_rewrite_tac[]);
val ℝ_square_eq_thm1 = save_pop_thm "ℝ_square_eq_thm1";
=TEX

=SML
set_goal([], ⌜∀x y:ℝ⦁ ℕℝ 0 ≤⋎R x ∧ ℕℝ 0 ≤⋎R y ∧ y *⋎R y = x *⋎R x ⇒ x = y⌝);
a (rewrite_tac[get_spec ⌜$≤⋎R⌝]);
a (rewrite_tac (map eq_sym_conv [⌜ℕℝ 0 = x⌝, ⌜ℕℝ 0 = y⌝])
	THEN REPEAT strip_tac
	THEN TRY (asm_rewrite_tac[]));
(* *** Goal "1" *** *)
a (all_ufc_tac [ℝ_square_eq_thm1]);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[ℝ_prod_sign_iff_clauses]);
(* *** Goal "3" *** *)
a (POP_ASM_T ante_tac
	THEN asm_rewrite_tac[ℝ_prod_sign_iff_clauses]
	THEN STRIP_T rewrite_thm_tac);
val ℝ_square_eq_thm2 = save_pop_thm "ℝ_square_eq_thm2";
=TEX

=SML
set_goal([], ⌜∀ x y⦁ ℕℝ 0 <⋎R x ∧ ℕℝ 0 <⋎R y ⇒ (x *⋎R x = y *⋎R y ⇔ x = y)⌝);
a (REPEAT strip_tac
	THEN TRY (asm_rewrite_tac[]));
a (strip_asm_tac (all_∀_elim ℝ_less_cases_thm)
	THEN (ALL_FC_T (MAP_EVERY ante_tac) [ℝ_square_mono_thm])
	THEN TRY (asm_rewrite_tac[]));
val ℝ_square_eq_eq_thm = save_pop_thm "ℝ_square_eq_eq_thm";
=TEX

=SML
set_goal([], ⌜∀ x y⦁ ℕℝ 0 ≤⋎R x ∧ ℕℝ 0 ≤⋎R y ⇒ (x *⋎R x = y *⋎R y ⇔ x = y)⌝);
a (rewrite_tac[get_spec ⌜$≤⋎R⌝]
	THEN REPEAT strip_tac
	THEN TRY (SYM_ASMS_T rewrite_tac));
(* *** Goal "1" *** *)
a (all_ufc_tac [ℝ_square_eq_eq_thm]);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac
	THEN SYM_ASMS_T rewrite_tac
	THEN rewrite_tac [ℝ_prod_sign_iff_clauses]);
(* *** Goal "3" *** *)
a (POP_ASM_T ante_tac
	THEN SYM_ASMS_T rewrite_tac
	THEN rewrite_tac [ℝ_prod_sign_iff_clauses]
	THEN strip_tac
	THEN asm_rewrite_tac[]);
val ℝ_square_eq_eq_thm2 = save_pop_thm "ℝ_square_eq_eq_thm2";
=TEX

=SML
set_goal([], ⌜∀ x y⦁ ℕℝ 0 ≤⋎R x ∧ ℕℝ 0 ≤⋎R y ∧ x *⋎R x ≤⋎R y *⋎R y ⇒ x ≤⋎R y⌝);
a (REPEAT strip_tac);
a (strip_asm_tac (all_∀_elim ℝ_less_cases_thm));
(* *** Goal "1" *** *)
a (asm_rewrite_tac[get_spec ⌜$≤⋎R⌝]);
(* *** Goal "2" *** *)
a (DROP_ASM_T ⌜x *⋎R x ≤⋎R y *⋎R y⌝ ante_tac
	THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (strip_asm_tac (list_∀_elim [⌜y⌝, ⌜x⌝] ℝ_square_mono_thm1));
(* *** Goal "3.1" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[get_spec ⌜$≤⋎R⌝]);
(* *** Goal "3.2" *** *)
a (all_ufc_tac [pc_rule1 "ℝ_lin_arith"
	prove_rule [] ⌜∀x y:ℝ⦁ x ≤⋎R y ∧ y ≤⋎R x ⇒ x = y⌝]);
a (all_ufc_tac [ℝ_square_eq_eq_thm2]);
a (all_var_elim_asm_tac);
val ℝ_square_≤_≤_thm = save_pop_thm "ℝ_square_≤_≤_thm";
=TEX

=SML
set_goal([], ⌜∀ x y⦁ ℕℝ 0 ≤⋎R x ∧ ℕℝ 0 ≤⋎R y ⇒ (x *⋎R x ≤⋎R y *⋎R y ⇔ x ≤⋎R y)⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_ufc_tac [ℝ_square_≤_≤_thm]);
(* *** Goal "2" *** *)
a (all_ufc_tac [ℝ_square_mono_thm1]);
val ℝ_square_≤_iff_≤_thm = save_pop_thm "ℝ_square_≤_iff_≤_thm";
=TEX

=SML
set_goal([], ⌜∀ x y⦁ x *⋎R x = y *⋎R y ⇔ Abs x = Abs y⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜Abs⋎R⌝]
	THEN cases_tac ⌜ℕℝ 0 ≤⋎R x⌝
	THEN cases_tac ⌜ℕℝ 0 ≤⋎R y⌝
	THEN TRY (asm_rewrite_tac[])
	);
(* *** Goal "1" *** *)
a (all_ufc_⇔_rewrite_tac [ℝ_square_eq_eq_thm2]); 
(* *** Goal "2" *** *)
a (all_asm_ante_tac
	THEN lemma_tac ⌜∃ z⦁ y = ~⋎R z⌝
	THEN1 (∃_tac ⌜~⋎R y⌝
		THEN rewrite_tac[])
	THEN asm_rewrite_tac [ℝ_times_minus_thm]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜ℕℝ 0 ≤⋎R z⌝
	THEN1 (PC_T1 "ℝ_lin_arith" asm_prove_tac []));
a (all_ufc_tac [ℝ_square_eq_eq_thm2]); 
(* *** Goal "2.2" *** *)
a (asm_rewrite_tac []);
(* *** Goal "3" *** *)
a (all_asm_ante_tac
	THEN lemma_tac ⌜∃ z⦁ x = ~⋎R z⌝
	THEN1 (∃_tac ⌜~⋎R x⌝
		THEN rewrite_tac[])
	THEN asm_rewrite_tac [ℝ_times_minus_thm]);
a (strip_tac THEN strip_tac);
a (lemma_tac ⌜ℕℝ 0 ≤⋎R z⌝
	THEN1 (PC_T1 "ℝ_lin_arith" asm_prove_tac []));
a (all_ufc_⇔_rewrite_tac [ℝ_square_eq_eq_thm2]); 
(* *** Goal "4" *** *)
a (all_asm_ante_tac
	THEN lemma_tac ⌜∃ z⦁ x = ~⋎R z⌝
	THEN1 (∃_tac ⌜~⋎R x⌝
		THEN rewrite_tac[])
	THEN lemma_tac ⌜∃ v⦁ y = ~⋎R v⌝
	THEN1 (∃_tac ⌜~⋎R y⌝
		THEN rewrite_tac[])
	THEN asm_rewrite_tac[]
	THEN strip_tac THEN strip_tac);
a (lemma_tac ⌜ℕℝ 0 ≤⋎R z⌝
	THEN1 (PC_T1 "ℝ_lin_arith" asm_prove_tac []));
a (lemma_tac ⌜ℕℝ 0 ≤⋎R v⌝
	THEN1 (PC_T1 "ℝ_lin_arith" asm_prove_tac []));
a (rewrite_tac [ℝ_times_minus_thm]);
a (all_ufc_⇔_rewrite_tac [ℝ_square_eq_eq_thm2]);
val ℝ_square_eq_iff_abs_eq_thm = save_pop_thm "ℝ_square_eq_iff_abs_eq_thm";
=TEX

=SML
set_goal([], ⌜∀x:ℝ⦁ ℕℝ 0 ≤ x ^ 2⌝);
a (rewrite_tac [ℝ_ℕ_exp_square_thm, ℝ_prod_sign_iff_clauses]);
a (PC_T1 "ℝ_lin_arith" prove_tac[]);
val ℝ_square_pos_thm = save_pop_thm "ℝ_square_pos_thm";
=TEX
}%ignore

\subsection{Sums}

\ignore{
=SML
set_goal([], ⌜∀x y:ℝ⦁ ℕℝ 0 ≤ x ∧ ℕℝ 0 ≤ y ⇒ ℕℝ 0 ≤ x + y⌝);
a (PC_T1 "ℝ_lin_arith" prove_tac[]);
val ℝ_sum_pos_thm = save_pop_thm "ℝ_sum_pos_thm";
=TEX

=SML
set_goal([], ⌜∀ x y:ℝ⦁ ℕℝ 0 ≤ x ^⋎N 2 +⋎R y ^⋎N 2⌝);
a (REPEAT ∀_tac);
a (lemma_tac ⌜ℕℝ 0 ≤ x ^ 2 ∧ ℕℝ 0 ≤ y ^ 2⌝
	THEN1 rewrite_tac [ℝ_square_pos_thm]);
a (all_ufc_tac [ℝ_sum_pos_thm]);
val ℝ_sum_square_pos_thm = save_pop_thm "ℝ_sum_square_pos_thm";
=TEX

=SML
set_goal([], ⌜∀x y: ℝ⦁ x^2 + y^2 = ℕℝ 0 ⇔ x = ℕℝ 0 ∧ y = ℕℝ 0⌝);
a (REPEAT_N 5 strip_tac THEN TRY (asm_rewrite_tac[]));
a (lemma_tac ⌜ℕℝ 0 ≤ x ^ 2 ∧ ℕℝ 0 ≤ y ^ 2⌝
	THEN1 rewrite_tac [ℝ_square_pos_thm]);
a (ALL_FC_T (MAP_EVERY (asm_tac o (rewrite_rule [ℝ_ℕ_exp_square_thm, ℝ_prod_sign_iff_clauses])))
	[pc_rule1 "ℝ_lin_arith" prove_rule []
	⌜∀x y: ℝ⦁ℕℝ 0 ≤ x ∧ ℕℝ 0 ≤ y ⇒ x + y = ℕℝ 0 ⇒ x = ℕℝ 0 ∧ y = ℕℝ 0⌝]
	THEN asm_rewrite_tac[]);
val ℝ_sum_square_zero_thm = save_pop_thm "ℝ_sum_square_zero_thm";
=TEX

=SML
set_goal([], ⌜∀x y:ℝ⦁ ℕℝ 0 ≤ x ∧ ℕℝ 0 ≤ y
	⇒ (x + y = ℕℝ 0 ⇔ x = ℕℝ 0 ∧ y = ℕℝ 0)⌝);
a (PC_T1 "ℝ_lin_arith" prove_tac[]);
val ℝ_sum_zero_thm = save_pop_thm "ℝ_sum_zero_thm";
=TEX

=SML
set_goal([], ⌜∀ x y:ℝ⦁ Abs (x ^⋎N 2 +⋎R y ^⋎N 2) = x ^⋎N 2 +⋎R y ^⋎N 2⌝);
a (REPEAT ∀_tac);
a (asm_rewrite_tac [get_spec ⌜Abs⋎R⌝, ℝ_sum_square_pos_thm]);
val ℝ_abs_sum_square_thm = save_pop_thm "ℝ_abs_sum_square_thm";
=TEX


=SML
val ℝ_plus_mono_thm = save_thm ("ℝ_plus_mono_thm", pc_rule1 "ℝ_lin_arith" prove_rule []
	⌜∀u v x y⦁ u ≤⋎R v ∧ x ≤⋎R y ⇒ u +⋎R x ≤⋎R v +⋎R y⌝);
=TEX
}%ignore

\subsection{Abs}

The following arithmetic results are obtained for reasoning about norms on real vector spaces, in particular to prove that $Abs$ is a norm over the reals and that the defined product operation over norms yields a norm.

=GFT
ℝ_Abs_Norm_clauses 
⊢ (∀ v⦁ ℕℝ 0 ≤⋎R Abs⋎R v)
∧ (∀ v⦁ (Abs⋎R v = ℕℝ 0) ⇔ v = ℕℝ 0)
∧ (∀ x v⦁ Abs⋎R (x *⋎R v) = Abs⋎R x *⋎R Abs⋎R v)
∧ (∀ v w⦁ Abs⋎R (v +⋎R w) ≤⋎R Abs⋎R v +⋎R Abs⋎R w)
=TEX

\ignore{
=SML
set_goal([], ⌜(∀ v⦁ ℕℝ 0 ≤⋎R Abs⋎R v)
             ∧ (∀ v⦁ (Abs⋎R v = ℕℝ 0) = v = ℕℝ 0)
             ∧ (∀ x v⦁ Abs⋎R (x *⋎R v) = Abs⋎R x *⋎R Abs⋎R v)
             ∧ (∀ v w⦁ Abs⋎R (v +⋎R w) ≤⋎R Abs⋎R v +⋎R Abs⋎R w)⌝);
a (rewrite_tac [get_spec ⌜Abs⋎R⌝, get_spec ⌜$≤⋎R⌝, ℝ_prod_sign_iff_clauses]);
a (REPEAT ∧_tac THEN REPEAT ∀_tac);
(* *** Goal "1" *** *)
a (CASES_T ⌜ℕℝ 0 < v ∨ ℕℝ 0 = v⌝ asm_tac
	THEN TRY (asm_rewrite_tac[]));
a (PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "2" *** *)
a (CASES_T ⌜ℕℝ 0 < v ∨ ℕℝ 0 = v⌝ asm_tac
	THEN TRY (asm_rewrite_tac[])
	THEN TRY (PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
(* *** Goal "3" *** *)
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm)
	THEN asm_rewrite_tac[]
	THEN (strip_asm_tac (list_∀_elim [⌜v⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm))
	THEN asm_rewrite_tac[]);
(* *** Goal "3.1" *** *)
a (LEMMA_T ⌜¬(ℕℝ 0 < x ∨ ℕℝ 0 = x)⌝ asm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a (LEMMA_T ⌜¬(ℕℝ 0 < v ∨ ℕℝ 0 = v)⌝ asm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a (asm_rewrite_tac[ℝ_times_minus_thm]);
(* *** Goal "3.2" *** *)
a (LEMMA_T ⌜¬(ℕℝ 0 < x ∨ ℕℝ 0 = x)⌝ asm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a (LEMMA_T ⌜¬(v < ℕℝ 0 ∨ x = ℕℝ 0 ∨ v = ℕℝ 0)⌝ asm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a (asm_rewrite_tac[ℝ_times_minus_thm]);
(* *** Goal "3.3" *** *)
a (LEMMA_T ⌜¬(ℕℝ 0 < v ∨ ℕℝ 0 = v)⌝ asm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a (asm_rewrite_tac[ℝ_times_minus_thm]);
a (LEMMA_T ⌜¬(x < ℕℝ 0 ∨ x = ℕℝ 0 ∨ v = ℕℝ 0)⌝ asm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a (asm_rewrite_tac[ℝ_times_minus_thm]);
(* *** Goal "4" *** *)
a (strip_asm_tac (list_∀_elim [⌜w⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm)
	THEN TRY (asm_rewrite_tac[])
	THEN (strip_asm_tac (list_∀_elim [⌜v⌝, ⌜ℕℝ 0⌝] ℝ_less_cases_thm))
	THEN TRY (asm_rewrite_tac[]));
(* *** Goal "4.1" *** *)
a (LEMMA_T ⌜¬(ℕℝ 0 <⋎R v ∨ ℕℝ 0 = v)⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a (LEMMA_T ⌜¬(ℕℝ 0 <⋎R w ∨ ℕℝ 0 = w)⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a (LEMMA_T ⌜¬(ℕℝ 0 <⋎R v +⋎R w ∨ ℕℝ 0 = v +⋎R w)⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "4.2" *** *)
a (LEMMA_T ⌜¬(ℕℝ 0 <⋎R w ∨ ℕℝ 0 = w)⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a (CASES_T ⌜ℕℝ 0 <⋎R v +⋎R w ∨ ℕℝ 0 = v +⋎R w⌝ rewrite_thm_tac
	THEN TRY (PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
(* *** Goal "4.3" *** *)
a (LEMMA_T ⌜¬(ℕℝ 0 <⋎R v ∨ ℕℝ 0 = v)⌝ rewrite_thm_tac
	THEN1 PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
a (CASES_T ⌜ℕℝ 0 <⋎R v +⋎R w ∨ ℕℝ 0 = v +⋎R w⌝ rewrite_thm_tac
	THEN TRY (PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
(* *** Goal "4.4" *** *)
a (CASES_T ⌜ℕℝ 0 <⋎R v +⋎R w ∨ ℕℝ 0 = v +⋎R w⌝ rewrite_thm_tac
	THEN TRY (PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
val ℝ_Abs_Norm_clauses = save_pop_thm "ℝ_Abs_Norm_clauses";
=TEX

=SML
set_goal([], ⌜∀x:ℝ⦁ x ≤⋎R Abs x⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜Abs⋎R⌝]
	THEN cases_tac ⌜ℕℝ 0 ≤⋎R x⌝
	THEN asm_rewrite_tac[]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ℝ_≤_abs_thm = save_pop_thm "ℝ_≤_abs_thm";
=TEX

=SML
set_goal([], ⌜∀x:ℝ⦁ ℕℝ 0 ≤⋎R x ⇒ Abs x = x⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜Abs⋎R⌝]
	THEN asm_rewrite_tac []);
val ℝ_abs_pos_id_thm = save_pop_thm "ℝ_abs_pos_id_thm";
=TEX

=SML
set_goal([], ⌜∀x y:ℝ⦁ ℕℝ 0 ≤⋎R x ∧ x ≤⋎R y ⇒ Abs x ≤⋎R Abs y⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜Abs⋎R⌝]
	THEN cases_tac ⌜ℕℝ 0 ≤⋎R x⌝
	THEN cases_tac ⌜ℕℝ 0 ≤⋎R y⌝
	THEN asm_rewrite_tac[]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
val ℝ_abs_mono_thm = save_pop_thm "ℝ_abs_mono_thm";
=TEX

=SML
set_goal([], ⌜∀x y:ℝ⦁ x ^ 2 = y ^ 2 ⇒ Abs x = Abs y⌝);
a (rewrite_tac [ℝ_ℕ_exp_square_thm, get_spec ⌜Abs⋎R⌝]
	THEN REPEAT strip_tac);
a (cases_tac ⌜ℕℝ 0 ≤⋎R x⌝
	THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (cases_tac ⌜ℕℝ 0 ≤⋎R y⌝
	THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a (all_asm_ufc_tac [ℝ_square_eq_thm2] THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (all_asm_ante_tac);
a (lemma_tac ⌜∃z⦁ y = ~⋎R z⌝
	THEN1 (∃_tac ⌜~⋎R y⌝ THEN rewrite_tac[])
	THEN asm_rewrite_tac[ℝ_times_minus_thm]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜ℕℝ 0 ≤⋎R z⌝
	THEN1 (PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a (all_ufc_tac [ℝ_square_eq_thm2]
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_asm_ante_tac);
a (lemma_tac ⌜∃z⦁ x = ~⋎R z⌝
	THEN1 (∃_tac ⌜~⋎R x⌝ THEN rewrite_tac[])
	THEN asm_rewrite_tac[ℝ_times_minus_thm]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜ℕℝ 0 ≤⋎R z⌝
	THEN1 (PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a (cases_tac ⌜ℕℝ 0 ≤⋎R y⌝
	THEN asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (all_asm_ufc_tac [ℝ_square_eq_thm2] THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (all_asm_ante_tac);
a (lemma_tac ⌜∃v⦁ y = ~⋎R v⌝
	THEN1 (∃_tac ⌜~⋎R y⌝ THEN rewrite_tac[])
	THEN asm_rewrite_tac[ℝ_times_minus_thm]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜ℕℝ 0 ≤⋎R v⌝
	THEN1 (PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a (all_asm_ufc_tac [ℝ_square_eq_thm2] THEN asm_rewrite_tac[]);
val ℝ_square_eq_abs_thm = pop_thm ();
=TEX

=SML
set_goal([], ⌜∀x y:ℝ⦁ Abs x = Abs y ⇒ x ^ 2 = y ^ 2⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜Abs⋎R⌝]
	THEN cases_tac ⌜ℕℝ 0 ≤⋎R x⌝
	THEN cases_tac ⌜ℕℝ 0 ≤⋎R y⌝
	THEN asm_rewrite_tac[]
	THEN strip_tac
	THEN TRY (asm_rewrite_tac[ℝ_ℕ_exp_square_thm, ℝ_times_minus_thm]));
(* *** Goal "1" *** *)
a (POP_ASM_T (rewrite_thm_tac o eq_sym_rule));
a (asm_rewrite_tac[ℝ_times_minus_thm]);
(* *** Goal "2" *** *)
a (LEMMA_T ⌜~⋎R (~⋎R x) = ~⋎R (~⋎R y)⌝ (asm_tac o (rewrite_rule[]))
	THEN1 (pure_asm_rewrite_tac[]
		THEN rewrite_tac[])
	THEN asm_rewrite_tac[]);
val ℝ_abs_eq_square_thm = pop_thm ();
=TEX

=SML
set_goal([], ⌜∀x y:ℝ⦁ x ^ 2 = y ^ 2 ⇔ Abs x = Abs y⌝);
a (REPEAT strip_tac
	THEN all_ufc_tac [ℝ_square_eq_abs_thm, ℝ_abs_eq_square_thm]
	THEN asm_rewrite_tac[]);
val ℝ_square_eq_abs_thm = save_pop_thm "ℝ_square_eq_abs_thm";
=TEX

=SML
set_goal([], ⌜∀x:ℝ⦁ Abs (x *⋎R x) = x *⋎R x⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜Abs⋎R⌝]);
a (LEMMA_T ⌜ℕℝ 0 ≤⋎R x *⋎R x⌝ rewrite_thm_tac
	THEN1 (rewrite_tac [ℝ_prod_sign_iff_clauses]
		THEN PC_T1 "ℝ_lin_arith" prove_tac[]));
val ℝ_abs_square_thm1 = save_pop_thm "ℝ_abs_square_thm1";
=TEX

=SML
set_goal([], ⌜∀ x y⦁ x *⋎R x ≤⋎R y *⋎R y ⇒ Abs x ≤⋎R Abs y⌝);
a (REPEAT strip_tac
	THEN bc_tac [ℝ_square_≤_≤_thm]
	THEN TRY (rewrite_tac [ℝ_Abs_Norm_clauses]));
a (asm_rewrite_tac [map_eq_sym_rule ℝ_Abs_Norm_clauses,
	ℝ_abs_square_thm1]);
val ℝ_square_≤_abs_≤_thm = save_pop_thm "ℝ_square_≤_abs_≤_thm";
=TEX

=SML
set_goal([], ⌜∀ x y⦁ Abs x ≤⋎R Abs y ⇒ x *⋎R x ≤⋎R y *⋎R y⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜ℕℝ 0 ≤⋎R Abs x⌝
	THEN1 rewrite_tac [ℝ_Abs_Norm_clauses]);
a (ALL_FC_T (MAP_EVERY ante_tac) [ℝ_square_mono_thm1]);
a (rewrite_tac [map_eq_sym_rule ℝ_Abs_Norm_clauses,
	ℝ_abs_square_thm1]);
val ℝ_abs_≤_square_≤_thm = save_pop_thm "ℝ_abs_≤_square_≤_thm";
=TEX

=SML
set_goal([], ⌜∀ x y⦁ x *⋎R x ≤⋎R y *⋎R y ⇔ Abs x ≤⋎R Abs y⌝);
a (REPEAT ∀_tac THEN strip_tac
	THEN rewrite_tac [ℝ_abs_≤_square_≤_thm, ℝ_square_≤_abs_≤_thm]);
val ℝ_square_≤_iff_abs_≤_thm = save_pop_thm "ℝ_square_≤_iff_abs_≤_thm";
=TEX

=SML
set_goal([], ⌜∀ x y⦁ x *⋎R x <⋎R y *⋎R y ⇔ Abs x <⋎R Abs y⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜Abs⋎R x ≤⋎R Abs⋎R y⌝);
(* *** Goal "1.1" *** *)
a (lemma_tac ⌜x *⋎R x ≤⋎R y *⋎R y⌝
	THEN1 asm_rewrite_tac [get_spec ⌜$≤⋎R⌝]);
a (bc_tac [ℝ_square_≤_iff_abs_≤_thm] THEN strip_tac);
(* *** Goal "1.2" *** *)
a (POP_ASM_T ante_tac
	THEN rewrite_tac [get_spec ⌜$≤⋎R⌝]
	THEN REPEAT strip_tac);
a (DROP_NTH_ASM_T 2 ante_tac
	THEN LEMMA_T ⌜x *⋎R x = y *⋎R y⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac [ℝ_square_eq_iff_abs_eq_thm]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜x *⋎R x ≤⋎R y *⋎R y⌝);
a (lemma_tac ⌜Abs x ≤⋎R Abs y⌝
	THEN1 asm_rewrite_tac [get_spec ⌜$≤⋎R⌝]);
a (bc_tac [ℝ_abs_≤_square_≤_thm] THEN strip_tac);
(* *** Goal "2.2" *** *)
a (POP_ASM_T ante_tac
	THEN rewrite_tac [get_spec ⌜$≤⋎R⌝]
	THEN REPEAT strip_tac);
a (DROP_NTH_ASM_T 2 ante_tac
	THEN LEMMA_T ⌜Abs x = Abs y⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac [map_eq_sym_rule ℝ_square_eq_iff_abs_eq_thm]);
val ℝ_square_less_iff_abs_less_thm = save_pop_thm "ℝ_square_less_iff_abs_less_thm";
=TEX

=SML
set_goal([], ⌜∀x:ℝ⦁ Abs (x ^⋎N 2) = x ^⋎N 2⌝);
a (rewrite_tac [ℝ_ℕ_exp_square_thm, ℝ_abs_square_thm1]);
val ℝ_abs_square_thm2 = save_pop_thm "ℝ_abs_square_thm2";
=TEX

=SML
set_goal([], ⌜∀x y:ℝ⦁ Abs (x *⋎R y) = (Abs x) *⋎R (Abs y)⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜Abs⋎R⌝]);
a (cases_tac ⌜ℕℝ 0 ≤⋎R x⌝ THEN cases_tac ⌜ℕℝ 0 ≤⋎R y⌝
	THEN TRY (asm_rewrite_tac[]));
(* *** Goal "1" *** *)
a (lemma_tac ⌜ℕℝ 0 ≤⋎R x *⋎R y⌝
	THEN1 (rewrite_tac [ℝ_prod_sign_iff_clauses]
		THEN contr_tac)
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (cases_tac ⌜x = ℕℝ 0⌝ THEN TRY (asm_rewrite_tac[]));
a (lemma_tac ⌜¬ ℕℝ 0 ≤⋎R x *⋎R y⌝
	THEN1 (rewrite_tac [ℝ_prod_sign_iff_clauses]
		THEN REPEAT strip_tac
		THEN TRY (PC_T1 "ℝ_lin_arith" asm_prove_tac[]))
	THEN asm_rewrite_tac[ℝ_times_minus_thm]);
(* *** Goal "3" *** *)
a (cases_tac ⌜y = ℕℝ 0⌝ THEN TRY (asm_rewrite_tac[]));
a (lemma_tac ⌜¬ ℕℝ 0 ≤⋎R x *⋎R y⌝
	THEN1 (rewrite_tac [ℝ_prod_sign_iff_clauses]
		THEN REPEAT strip_tac
		THEN TRY (PC_T1 "ℝ_lin_arith" asm_prove_tac[]))
	THEN asm_rewrite_tac[ℝ_times_minus_thm]);
(* *** Goal "4" *** *)
a (lemma_tac ⌜ℕℝ 0 ≤⋎R x *⋎R y⌝
	THEN1 (rewrite_tac [ℝ_prod_sign_iff_clauses]
		THEN (PC_T1 "ℝ_lin_arith" asm_prove_tac[]))
	THEN asm_rewrite_tac[ℝ_times_minus_thm]);
val ℝ_abs_prod_thm = save_pop_thm "ℝ_abs_prod_thm";
=TEX

}%ignore

\subsection{Square Root}

\ignore{
=SML
push_goal ([], ⌜∃SqrtA⦁ ∀ x⦁ ℕℝ 0 ≤ SqrtA x ∧ (SqrtA x)^2 = Abs x⌝);
a(prove_∃_tac THEN strip_tac);
a (lemma_tac ⌜ℕℝ 0 ≤ Abs x'⌝
	THEN1 (rewrite_tac [ℝ_0_≤_abs_thm]));
a (all_ufc_tac [square_root_thm1]);
a(∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
val _ = save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏SqrtA⦎ :ℝ → ℝ
├──────
│ ∀ x⦁ ℕℝ 0 ≤ SqrtA x 
│ ∧ (SqrtA x)^2 = Abs x
■

\ignore{

=SML
set_goal([], ⌜∀x y:ℝ⦁ SqrtA x = SqrtA y ⇒ Abs x = Abs y⌝);
a (REPEAT strip_tac);
a (LEMMA_T ⌜(SqrtA x) ^⋎N 2 = (SqrtA y) ^⋎N 2⌝ ante_tac
	THEN1 asm_rewrite_tac[]);
a (rewrite_tac [get_spec ⌜SqrtA⌝]);
val ℝ_sqrt_abs_thm1 = pop_thm ();
=TEX

=SML
set_goal([], ⌜∀x:ℝ⦁ SqrtA x = ℕℝ 0 ⇔ x = ℕℝ 0⌝);
a (REPEAT strip_tac THEN TRY (asm_rewrite_tac[]));
a (contr_tac THEN lemma_tac ⌜ℕℝ 0 <⋎R SqrtA x ^⋎N 2⌝
	THEN1 rewrite_tac[get_spec ⌜SqrtA⌝,
	get_spec ⌜Abs⋎R⌝,
	get_spec ⌜$≤⋎R⌝]);
(* *** Goal "1.1" *** *)
a (cases_tac ⌜ℕℝ 0 <⋎R x ∨ ℕℝ 0 = x⌝
	THEN asm_rewrite_tac[]
	THEN PC_T1 "ℝ_lin_arith" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a (POP_ASM_T ante_tac
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (strip_asm_tac (rewrite_rule [ℝ_ℕ_exp_square_thm, ℝ_prod_sign_iff_clauses]
	(∀_elim ⌜ℕℝ 0⌝ (get_spec ⌜SqrtA⌝))));
val sqrt_thm1 = save_pop_thm "sqrt_thm1";
=TEX

=SML
set_goal([], ⌜∀x y:ℝ⦁ SqrtA (x ^ 2 + y ^ 2) = ℕℝ 0 ⇔ x = ℕℝ 0 ∧ y = ℕℝ 0⌝);
a (REPEAT ∀_tac THEN rewrite_tac [sqrt_thm1]);
a (lemma_tac ⌜ℕℝ 0 ≤ x ^ 2 ∧ ℕℝ 0 ≤ y ^ 2⌝
	THEN1 (rewrite_tac [ℝ_square_pos_thm]));
a (lemma_tac ⌜ℕℝ 0 ≤ x ^ 2 + y ^ 2⌝
	THEN1 (all_ufc_tac [ℝ_sum_pos_thm]));
a (LEMMA_T ⌜(x ^⋎N 2 + y ^⋎N 2 = ℕℝ 0)
		= (x ^⋎N 2 = ℕℝ 0 ∧ y ^⋎N 2 = ℕℝ 0)⌝
	rewrite_thm_tac
	THEN1 (ALL_FC_T1 fc_⇔_canon rewrite_tac [ℝ_sum_zero_thm]));
a (rewrite_tac[ℝ_ℕ_exp_square_thm, ℝ_prod_sign_iff_clauses]);
val sqrt_square_thm = save_pop_thm "sqrt_square_thm";
=TEX
}%\ignore

\ignore{

=SML
set_goal([], ⌜∀x:ℝ⦁ Abs(SqrtA x) = SqrtA x
	∧ Abs (Abs x) = Abs x
	∧ Abs (ℕℝ 0) = ℕℝ 0
	∧ Abs (~⋎R  x) = Abs x⌝);
a (REPEAT strip_tac
	THEN TRY (rewrite_tac [get_spec ⌜Abs⋎R⌝, get_spec ⌜SqrtA⌝]));
(* *** Goal "1" *** *)
a (cases_tac ⌜ℕℝ 0 ≤⋎R x⌝
	THEN asm_rewrite_tac[]);
a (lemma_tac ⌜ℕℝ 0 ≤⋎R ~⋎R x⌝
	THEN1 (PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜$≤⋎R⌝]);
a (strip_asm_tac (list_∀_elim [⌜ℕℝ 0⌝, ⌜x⌝] ℝ_less_cases_thm)
	THEN TRY (asm_rewrite_tac[]));
(* *** Goal "2.1" *** *)
a (LEMMA_T ⌜¬ (ℕℝ 0 <⋎R ~⋎R x ∨ ℕℝ 0 = ~⋎R x)⌝ rewrite_thm_tac
	THEN1 (PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
(* *** Goal "2.2" *** *)
a (LEMMA_T ⌜x = ℕℝ 0⌝ rewrite_thm_tac
	THEN1 (PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
(* *** Goal "2.3" *** *)
a (LEMMA_T ⌜ℕℝ 0 <⋎R ~⋎R x⌝ rewrite_thm_tac
	THEN1 (PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
a (LEMMA_T ⌜¬ (ℕℝ 0 <⋎R x ∨ ℕℝ 0 = x)⌝ rewrite_thm_tac
	THEN1 (PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
val ℝ_abs_clauses1 = pop_thm ();
=TEX

=SML
set_goal([], ⌜∀x:ℝ⦁ SqrtA (~⋎R x) = SqrtA x⌝);
a (strip_tac);
a (lemma_tac ⌜SqrtA (~⋎R x) ^⋎N 2 = Abs⋎R x⌝
	THEN1 (strip_asm_tac (∀_elim ⌜~⋎R x⌝ (get_spec ⌜SqrtA⌝))
		THEN asm_rewrite_tac[ℝ_abs_clauses1]));
a (lemma_tac ⌜(SqrtA x) ^⋎N 2 = Abs⋎R x⌝
	THEN1 (strip_asm_tac (∀_elim ⌜x⌝ (get_spec ⌜SqrtA⌝))
		THEN asm_rewrite_tac[ℝ_abs_clauses1]));
a (lemma_tac ⌜SqrtA (~⋎R x) ^⋎N 2 = SqrtA x ^⋎N 2⌝
	THEN1 asm_rewrite_tac[]);
a (ALL_FC_T (MAP_EVERY ante_tac) [ℝ_square_eq_abs_thm]
	THEN rewrite_tac [ℝ_abs_clauses1]
	THEN strip_tac);
val ℝ_sqrt_minus_thm = save_pop_thm "ℝ_sqrt_minus_thm";
=TEX

=SML
set_goal([], ⌜∀x:ℝ⦁ SqrtA(Abs x) = SqrtA x⌝);
a (REPEAT strip_tac
	THEN TRY (rewrite_tac [get_spec ⌜Abs⋎R⌝, get_spec ⌜SqrtA⌝]));
a (cases_tac ⌜ℕℝ 0 ≤⋎R x⌝
	THEN asm_rewrite_tac[ℝ_sqrt_minus_thm]);
val ℝ_sqrt_abs_thm = pop_thm ();
=TEX

=SML
set_goal([], ⌜∀x:ℝ⦁ SqrtA(Abs x) = SqrtA x
	∧ Abs(SqrtA x) = SqrtA x
	∧ Abs (Abs x) = Abs x
	∧ Abs (ℕℝ 0) = ℕℝ 0
	∧ Abs (~⋎R  x) = Abs x⌝);
a (rewrite_tac[ℝ_abs_clauses1, ℝ_sqrt_abs_thm]);
val ℝ_abs_clauses = save_pop_thm "ℝ_abs_clauses";
=TEX

=SML
set_goal([], ⌜∀x y:ℝ⦁ Abs x = Abs y ⇒ SqrtA x = SqrtA y⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜Abs⋎R⌝]);
a (cases_tac ⌜ℕℝ 0 ≤⋎R x⌝
	THEN asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (cases_tac ⌜ℕℝ 0 ≤⋎R y⌝
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[ℝ_sqrt_minus_thm]);
(* *** Goal "2" *** *)
a (cases_tac ⌜ℕℝ 0 ≤⋎R y⌝
	THEN (asm_rewrite_tac[])
	THEN REPEAT strip_tac
	THEN TRY (asm_rewrite_tac[ℝ_sqrt_minus_thm]));
(* *** Goal "2.1" *** *)
a (LEMMA_T ⌜y = ~⋎R x⌝ rewrite_thm_tac
	THEN1 asm_rewrite_tac[]);
a (rewrite_tac[ℝ_sqrt_minus_thm]);
(* *** Goal "2.2" *** *)
a (LEMMA_T ⌜x = y⌝ rewrite_thm_tac
	THEN1 (PC_T1 "ℝ_lin_arith" asm_prove_tac[]));
val ℝ_sqrt_abs_thm2 = pop_thm ();
=TEX

=SML
set_goal([], ⌜∀x y:ℝ⦁ SqrtA x = SqrtA y ⇔ Abs x = Abs y⌝);
a (REPEAT strip_tac THEN all_ufc_tac [ℝ_sqrt_abs_thm1, ℝ_sqrt_abs_thm2]);
val ℝ_sqrt_abs_thm = save_pop_thm "ℝ_sqrt_abs_thm";
=TEX

=SML
set_goal([], ⌜∀x y:ℝ⦁ ℕℝ 0 ≤⋎R x ∧ x ≤⋎R y ⇒ SqrtA x ≤⋎R SqrtA y⌝);
a (REPEAT strip_tac
	THEN bc_tac [ℝ_square_≤_≤_thm]
	THEN TRY (rewrite_tac [rewrite_rule [ℝ_ℕ_exp_square_thm] (get_spec ⌜SqrtA⌝)])
	THEN all_ufc_tac [ℝ_abs_mono_thm]);
val ℝ_sqrt_mono_thm = save_pop_thm "ℝ_sqrt_mono_thm";
=TEX

=SML
set_goal([], ⌜∀x:ℝ⦁ SqrtA (x * x) = Abs x⌝);
a (strip_tac
	THEN lemma_tac ⌜SqrtA (x *⋎R x) ^⋎N 2 = (Abs⋎R x) ^⋎N 2⌝
	THEN1 (rewrite_tac [rewrite_conv [ℝ_ℕ_exp_square_thm] ⌜(Abs⋎R x) ^⋎N 2⌝,
		get_spec ⌜SqrtA⌝, get_spec ⌜Abs⋎R⌝, ℝ_abs_square_thm1]
		THEN cases_tac ⌜ℕℝ 0 ≤⋎R x⌝
		THEN asm_rewrite_tac[ℝ_times_minus_thm]));
a (ALL_ASM_FC_T
	(MAP_EVERY (strip_asm_tac o (rewrite_rule [ℝ_abs_clauses1])))
	[ℝ_square_eq_abs_thm]);
val ℝ_sqrt_square_thm1 = save_pop_thm "ℝ_sqrt_square_thm1";
=TEX

=SML
set_goal([], ⌜∀x:ℝ⦁ SqrtA (x ^ 2) = Abs x⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [ℝ_sqrt_square_thm1, ℝ_ℕ_exp_square_thm]);
val ℝ_sqrt_square_thm2 = save_pop_thm "ℝ_sqrt_square_thm2";
=TEX

=SML
set_goal([], ⌜∀x y:ℝ⦁ SqrtA (x * y) = SqrtA x * SqrtA y⌝);
a (REPEAT strip_tac
	THEN lemma_tac ⌜(SqrtA x *⋎R SqrtA y) *⋎R (SqrtA x *⋎R SqrtA y)
	 = (SqrtA x *⋎R SqrtA x) *⋎R (SqrtA y *⋎R SqrtA y)⌝
	THEN1 rewrite_tac [∀_elim ⌜SqrtA x⌝ ℝ_times_order_thm]);
a (lemma_tac ⌜SqrtA x *⋎R SqrtA x = Abs⋎R x⌝
	THEN1 (rewrite_tac [rewrite_rule [ℝ_ℕ_exp_square_thm]
			(∀_elim ⌜x⌝ (get_spec ⌜SqrtA⌝))]));
a (lemma_tac ⌜SqrtA y *⋎R SqrtA y = Abs⋎R y⌝
	THEN1 (rewrite_tac [rewrite_rule [ℝ_ℕ_exp_square_thm]
			(∀_elim ⌜y⌝ (get_spec ⌜SqrtA⌝))]));
a (DROP_NTH_ASM_T 3 ante_tac);
a (once_asm_rewrite_tac[]);
a (rewrite_tac[eq_sym_rule(rewrite_rule [ℝ_Abs_Norm_clauses, ℝ_ℕ_exp_square_thm]
	((∧_right_elim o (∀_elim ⌜x *⋎R y⌝)) (get_spec ⌜SqrtA⌝))),
	rewrite_rule [ℝ_ℕ_exp_square_thm] ℝ_square_eq_abs_thm,
	ℝ_abs_clauses]);
a (once_rewrite_tac [eq_sym_conv ⌜Abs⋎R (SqrtA x *⋎R SqrtA y) = SqrtA (x *⋎R y)⌝]
	THEN STRIP_T rewrite_thm_tac);
a (rewrite_tac [ℝ_abs_clauses, ℝ_Abs_Norm_clauses]);
val ℝ_sqrt_prod_thm = save_pop_thm "ℝ_sqrt_prod_thm";
=TEX

=SML
set_goal([], ⌜∀x y:ℝ⦁ SqrtA(x + y) ≤ (SqrtA x) +⋎R (SqrtA y)⌝);
a (REPEAT strip_tac);
a (LEMMA_T ⌜SqrtA(x + y) = Abs (SqrtA(x + y))
	∧ (SqrtA x) +⋎R (SqrtA y) = Abs((SqrtA x) +⋎R (SqrtA y))⌝
	once_rewrite_thm_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜ℕℝ 0 ≤⋎R SqrtA (x +⋎R y) ∧ ℕℝ 0 ≤⋎R SqrtA x +⋎R SqrtA y⌝
	THEN1 (rewrite_tac [get_spec ⌜SqrtA⌝]
		THEN bc_tac [ℝ_sum_pos_thm]
		THEN rewrite_tac [get_spec ⌜SqrtA⌝])
	THEN ALL_FC_T rewrite_tac [ℝ_abs_pos_id_thm]);
(* *** Goal "2" *** *)
a (bc_tac [ℝ_square_≤_abs_≤_thm]);
a (rewrite_tac[rewrite_rule [ℝ_ℕ_exp_square_thm] (get_spec ⌜SqrtA⌝),
	ℝ_times_plus_distrib_thm]);
a (ℝ_top_anf_tac);
a (lemma_tac ⌜Abs⋎R (x +⋎R y) ≤⋎R (Abs⋎R x) +⋎R (Abs⋎R y)⌝
	THEN1 rewrite_tac [ℝ_Abs_Norm_clauses]);
a (LEMMA_T ⌜(Abs⋎R x) +⋎R (Abs⋎R y) ≤⋎R Abs⋎R x +⋎R Abs⋎R y +⋎R ℕℝ 2 *⋎R SqrtA x *⋎R SqrtA y⌝
	asm_tac
	THEN1 rewrite_tac [ℝ_prod_sign_iff_clauses, get_spec ⌜SqrtA⌝]);
a (all_ufc_tac [ℝ_≤_trans_thm]);
val sqrt_plus_thm = save_pop_thm "sqrt_plus_thm"; 
=TEX

}%ignore

\subsection{Sums of Countable Collections of Reals}

In evaluating the cosmological consequences of Newton's Laws it is desirable to formulate them as cosmological theories in ways which do not prejudge such questions as whether the cardinality of the universe is finite.
To do this it is necessary to be able, where possible, to form the sum of an infinite set of reals, possibly even an uncountably infinite set of real numbers.

For the most general formulations it seems possible that the use of non-standard reals might be needed.
We are concerned here with what can be done with standard reals, i.e. with formalising the notion that some collection of real numbers has a finite sum.

The following definition gives the sum of a possibly finite or countable collection of real numbers.

=SML
declare_infix (300, "⤖>");
=TEX
ⓈHOLCONST
│ $⦏⤖>⦎ : ('a → ℝ + ONE) → ℝ → BOOL
├──────
│ ∀c r⦁ c ⤖> r ⇔
│	∃s⦁ (∀ a n m⦁ IsL (c a) ⇒ s n = s m ⇒ n = m)
│	⇒ (Series (λn⦁ if IsR (c (s n)) then 0⋎R else OutL (c (s n)))) -> r
■

\section{Cartesian and Dependent Products}

\subsection{Cartesian Products}

=GFT
⦏cp_eq_thm1⦎ =
   ⊢ ∀ x y v w p q⦁ p ∈ x ∧ q ∈ y ⇒ (x × y) = (v × w) ⇒ x = v ∧ y = w

⦏cp_eq_thm2⦎ =
   ⊢ ∀ x y v w p⦁ p ∈ (x × y) ⇒ (x × y) = (v × w) ⇒ x = v ∧ y = w
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y v w p q⦁ p ∈ x ∧ q ∈ y ⇒ (x × y) = (v × w) ⇒ x = v ∧ y = w⌝);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]
	THEN POP_ASM_T ante_tac
	THEN rewrite_tac[sets_ext_clauses]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜(x', q) ∈ (x × y)⌝  THEN1 asm_rewrite_tac [rel_∈_in_clauses]); 
a (asm_fc_tac[]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac [rel_∈_in_clauses] THEN contr_tac); 
(* *** Goal "2" *** *)
a (lemma_tac ⌜(p, q) ∈ (x × y)⌝  THEN1 asm_rewrite_tac [rel_∈_in_clauses]); 
a (asm_fc_tac[]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac [rel_∈_in_clauses] THEN REPEAT strip_tac); 
a (lemma_tac ⌜(x', q) ∈ (v × w)⌝  THEN1 asm_rewrite_tac [rel_∈_in_clauses]); 
a (spec_nth_asm_tac 6 ⌜(x', q)⌝);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac [rel_∈_in_clauses] THEN contr_tac); 
(* *** Goal "3" *** *)
a (lemma_tac ⌜(p, x') ∈ (x × y)⌝  THEN1 asm_rewrite_tac [rel_∈_in_clauses]); 
a (asm_fc_tac[]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac [rel_∈_in_clauses] THEN contr_tac); 
(* *** Goal "4" *** *)
a (lemma_tac ⌜(p, q) ∈ (x × y)⌝  THEN1 asm_rewrite_tac [rel_∈_in_clauses]); 
a (asm_fc_tac[]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac [rel_∈_in_clauses] THEN REPEAT strip_tac); 
a (lemma_tac ⌜(p, x') ∈ (v × w)⌝  THEN1 asm_rewrite_tac [rel_∈_in_clauses]); 
a (spec_nth_asm_tac 6 ⌜(p, x')⌝);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac [rel_∈_in_clauses] THEN contr_tac); 
val cp_eq_thm1 = save_pop_thm "cp_eq_thm1";

set_goal([], ⌜∀x y v w p⦁ p ∈ (x × y) ⇒ (x × y) = (v × w) ⇒ x = v ∧ y = w⌝);
a (REPEAT_N 7 strip_tac);
a (DROP_NTH_ASM_T 2 ante_tac THEN split_pair_rewrite_tac [⌜p⌝][rel_∈_in_clauses] THEN strip_tac);
a (all_fc_tac [cp_eq_thm1] THEN contr_tac);
val cp_eq_thm2 = save_pop_thm "cp_eq_thm2";
=TEX
}%ignore


=GFT
⦏cp_l_part_thm⦎ = ⊢ ∀ l r x⦁ x ∈ r ⇒ l = {m|∃ p⦁ p ∈ (l × r) ∧ m = Fst p}

⦏cp_r_part_thm⦎ = ⊢ ∀ l r x⦁ x ∈ l ⇒ r = {m|∃ p⦁ p ∈ (l × r) ∧ m = Snd p}

⦏cp_part_thm⦎ =
   ⊢ ∀ l r x⦁ x ∈ (l × r)
         ⇒ l = {m|∃ p⦁ p ∈ (l × r) ∧ m = Fst p}
           ∧ r = {m|∃ p⦁ p ∈ (l × r) ∧ m = Snd p}
=TEX

\ignore{
=SML
set_goal([], ⌜∀l r x⦁ x ∈ r ⇒ l = {m | ∃p⦁ p ∈ (l × r) ∧ m = Fst p}⌝);
a (REPEAT strip_tac THEN rewrite_tac [sets_ext_clauses]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜x',x⌝ THEN asm_rewrite_tac[rel_∈_in_clauses]);
(* *** Goal "2" *** *)
a (DROP_NTH_ASM_T 2 ante_tac THEN split_pair_rewrite_tac [⌜p⌝][rel_∈_in_clauses]);
a (var_elim_asm_tac ⌜x' = Fst p⌝ THEN contr_tac);
val cp_l_part_thm = save_pop_thm "cp_l_part_thm";

set_goal([], ⌜∀l r x⦁ x ∈ l ⇒ r = {m | ∃p⦁ p ∈ (l × r) ∧ m = Snd p}⌝);
a (REPEAT strip_tac THEN rewrite_tac [sets_ext_clauses]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜x,x'⌝ THEN asm_rewrite_tac[rel_∈_in_clauses]);
(* *** Goal "2" *** *)
a (DROP_NTH_ASM_T 2 ante_tac THEN split_pair_rewrite_tac [⌜p⌝][rel_∈_in_clauses]);
a (var_elim_asm_tac ⌜x' = Snd p⌝ THEN contr_tac);
val cp_r_part_thm = save_pop_thm "cp_r_part_thm";

set_goal([], ⌜∀l r x⦁ x ∈ (l × r) ⇒
		  l = {m | ∃p⦁ p ∈ (l × r) ∧ m = Fst p}
		∧ r = {m | ∃p⦁ p ∈ (l × r) ∧ m = Snd p}⌝);
a (REPEAT ∀_tac THEN split_pair_rewrite_tac [⌜x⌝][rel_∈_in_clauses]);
a (REPEAT strip_tac);
a (bc_tac [cp_l_part_thm]);
a (∃_tac ⌜Snd x⌝ THEN strip_tac);
a (bc_tac [cp_r_part_thm]);
a (∃_tac ⌜Fst x⌝ THEN strip_tac);
val cp_part_thm = save_pop_thm "cp_part_thm";
=TEX
}%ignore

\subsection{Distributed Cartesian Product}

The "distributed cartesian product" is what you need to get the equivalance classes generated by two relations to the equivalence classes generated by the product of the equivalence relations (see section \ref{PER}).

=SML
declare_infix (340, "×⋎D");
=TEX

ⓈHOLCONST
│ $⦏×⋎D⦎ : ('a SET SET) → ('b SET SET) →  (('a × 'b) SET SET)
├──────
│ ∀l r⦁ l ×⋎D r = {cp | ∃ leq req⦁ leq ∈ l ∧ req ∈ r ∧ cp = (leq × req)}
■

=GFT
⦏×⋎D_ext_thm⦎ =
   ⊢ ∀ l r cp⦁ cp ∈ l ×⋎D r ⇔ (∃ leq req⦁ leq ∈ l ∧ req ∈ r ∧ cp = (leq × req))
=TEX

\ignore{
=SML
val ×⋎D_def = get_spec ⌜$×⋎D⌝;

set_goal ([], ⌜∀l r cp⦁ cp ∈ l ×⋎D r ⇔ ∃ leq req⦁ leq ∈ l ∧ req ∈ r ∧ cp = (leq × req)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [×⋎D_def, sets_ext_clauses]);
val ×⋎D_ext_thm = save_pop_thm "×⋎D_ext_thm";
=TEX
}%ignore

\subsection{Dependent Function Spaces ??}

Our generic treatment of algebraic operators represents operators as functions over indexed sets of arugments.
In order to take a quotient of an algebra involving such operators we need to lift the equivalence relation over the domain of the algebra to one over indexed sets of domain values.
This is taking an arbitrary power of the equivalence relation.

These indexed sets are actually functions, and the equivalence classes are like dependent function spaces, whose type corresponds to an indexed set of the equivalence classes over the domain, i.e. a function from the indexes into the set of equivalence classes.

It is therefore useful to define this dependent function space operation which may also be though of as a dependent cartesian power.

ⓈHOLCONST
│ ⦏Π⋎f⦎ : 'b SET → ('b → 'a SET) → ('b → 'a) SET
├──────
│ ∀ is f⦁ Π⋎f is f = {g | ∀i⦁ i ∈ is ⇒ g i ∈ f i}
■

Now we take a set of (probably equivalence) classes and map the dependent function space over all the indexed sets taken from this set.

ⓈHOLCONST
│ ⦏×⋎Π⦎ : 'b SET → ('a SET SET) → ('b → 'a) SET SET
├──────
│ ∀ is ss⦁ ×⋎Π is ss = {g | ∃h⦁ (∀i⦁ i ∈ is ⇒ h i ∈ ss) ∧ g = Π⋎f is h}
■

\section{Relation Products}

The kind of relation which we consider here is the kind which is used in the theory \emph{equiv\_rel}, structures represented by an ordered pair of which the first element is the domain of the relation and the second is a relation as a curried function of two operands into type \emph{BOOL}.


This section provides some small additions to the theory ``equiv\_rel'' related to lifting functions over quotients.

=SML
declare_infix(210, "RelProd");
declare_infix(230, "≤⋎l");
declare_infix(230, "≤⋎r");
=TEX

ⓈHOLCONST
│ ⦏$RelProd⦎ : ('a SET × ('a → 'a → BOOL))
│		→ ('b SET × ('b → 'b → BOOL))
│		→ (('a × 'b) SET × ('a × 'b → 'a × 'b → BOOL))
├──────
│ ∀ $≤⋎l $≤⋎r L R⦁ ((L, $≤⋎l) RelProd (R, $≤⋎r)) =
│	((L × R),
│	λ(l1, r1) (l2, r2)⦁ l1 ∈ L ∧ l2 ∈ L ∧ r1 ∈ R ∧ r2 ∈ R
│			∧ l1 ≤⋎l l2 ∧ r1 ≤⋎r r2)
■
=GFT
⦏RelProd_projections_thm⦎ =
   ⊢ ∀ (L, $≤⋎l) (R, $≤⋎r)⦁
	Fst ((L, $≤⋎l) RelProd (R, $≤⋎r)) = (L × R)
      ∧ Snd ((L, $≤⋎l) RelProd (R, $≤⋎r)) = (λ (l1, r1) (l2, r2)
        	   ⦁ l1 ∈ L ∧ l2 ∈ L ∧ r1 ∈ R ∧ r2 ∈ R ∧ l1 ≤⋎l l2 ∧ r1 ≤⋎r r2)
=TEX

\ignore{
=SML
val RelProd_def = get_spec ⌜$RelProd⌝;

push_pc "hol1";

set_goal([], ⌜∀(L, $≤⋎l) (R, $≤⋎r)⦁ Fst(((L, $≤⋎l) RelProd (R, $≤⋎r))) = (L × R)
	∧ Snd(((L, $≤⋎l) RelProd (R, $≤⋎r))) = λ(l1, r1) (l2, r2)⦁ l1 ∈ L ∧ l2 ∈ L ∧ r1 ∈ R ∧ r2 ∈ R
			∧ l1 ≤⋎l l2 ∧ r1 ≤⋎r r2⌝);
a (rewrite_tac [RelProd_def] THEN REPEAT strip_tac);
val RelProd_projections_thm = save_pop_thm "RelProd_projections_thm";

pop_pc();
=TEX
}%ignore

\ignore{
=SML
add_pc_thms "'rbjmisc" (map get_spec [] @ [RelProd_projections_thm]);
set_merge_pcs ["basic_hol", "'sets_alg", "'ℝ", "'rbjmisc"];
=TEX
}%ignore

The product construction preserves various properties of relations.

=GFT
⦏Trans_RelProd_thm⦎ =
   ⊢ ∀ (L, $≜⋎l) (R, $≜⋎r)⦁
	Trans (L, $≜⋎l) ∧ Trans (R, $≜⋎r) ⇒ Trans ((L, $≜⋎l) RelProd (R, $≜⋎r))

⦏Sym_RelProd_thm⦎ =
   ⊢ ∀ (L, $≜⋎l) (R, $≜⋎r)⦁
	Sym (L, $≜⋎l) ∧ Sym (R, $≜⋎r) ⇒ Sym ((L, $≜⋎l) RelProd (R, $≜⋎r))

⦏Refl_RelProd_thm⦎ =
   ⊢ ∀ (L, $≜⋎l) (R, $≜⋎r)⦁
	Refl (L, $≜⋎l) ∧ Refl (R, $≜⋎r) ⇒ Refl ((L, $≜⋎l) RelProd (R, $≜⋎r))
=TEX

\ignore{
=SML
set_goal([], ⌜∀(L, $≜⋎l) (R, $≜⋎r)⦁ Trans(L, $≜⋎l) ∧ Trans(R, $≜⋎r) ⇒ Trans ((L, $≜⋎l) RelProd (R, $≜⋎r))⌝);
a (REPEAT strip_tac);
a (fc_tac [equiv_def]);
a (fc_tac [trans_def]);
a (rewrite_tac [RelProd_def, trans_def]);
a (REPEAT strip_tac
	THEN_TRY (POP_ASM_T (strip_asm_tac o (rewrite_rule[rel_∈_in_clauses]) o (pure_once_rewrite_rule [prove_rule [] ⌜x = (Fst x, Snd x)⌝])))
	THEN REPEAT (all_asm_ufc_tac[]));
val Trans_RelProd_thm = save_pop_thm "Trans_RelProd_thm";

set_goal([], ⌜∀(L, $≜⋎l) (R, $≜⋎r)⦁ Sym(L, $≜⋎l) ∧ Sym(R, $≜⋎r) ⇒ Sym ((L, $≜⋎l) RelProd (R, $≜⋎r))⌝);
a (REPEAT strip_tac);
a (fc_tac [equiv_def]);
a (fc_tac [sym_def]);
a (rewrite_tac [RelProd_def, sym_def]);
a (REPEAT strip_tac
	THEN_TRY (POP_ASM_T (strip_asm_tac o (rewrite_rule[rel_∈_in_clauses]) o (pure_once_rewrite_rule [prove_rule [] ⌜x = (Fst x, Snd x)⌝])))
	THEN REPEAT (all_asm_ufc_tac[]));
val Sym_RelProd_thm = save_pop_thm "Sym_RelProd_thm";

set_goal([], ⌜∀(L, $≜⋎l) (R, $≜⋎r)⦁ Refl(L, $≜⋎l) ∧ Refl(R, $≜⋎r) ⇒ Refl ((L, $≜⋎l) RelProd (R, $≜⋎r))⌝);
a (REPEAT strip_tac);
a (fc_tac [equiv_def]);
a (fc_tac [refl_def]);
a (rewrite_tac [RelProd_def, refl_def]);
a (REPEAT strip_tac
	THEN_TRY (POP_ASM_T (strip_asm_tac o (rewrite_rule[rel_∈_in_clauses]) o (pure_once_rewrite_rule [prove_rule [] ⌜x = (Fst x, Snd x)⌝])))
	THEN REPEAT (all_asm_ufc_tac[]));
val Refl_RelProd_thm = save_pop_thm "Refl_RelProd_thm";
=TEX
}%ignore

\section{Powers of Relations}

Universal algebra (below) involves operators of arbitrary arity, and reasoning generally about algebras involving such operators involves raising equivalence relations to arbitrary powers.

We define such operations first for relations in general.

The operators are represented by functions over indexed sets of arguments, the indexed sets being represented by total functions over a type of indexes, together with a subset of the type indicating the range of significance of the functions in the domain of the operators.
The operators are themselves also significant only for arguments all of which fall in some domain (the domain of a structure), but this need not concern us here.

Our concern here is not with the operators, but with quotients of the domain of the operators, and with the resulting equivalence relations over the domain of the operators.
So we want to take an equivalence relation over some type, together with a set of indices, and obtain an equivalence relation over the total functions from indexes to values in the domain.
We define this for arbitrary relations, and then prove (later) that when the relation is an equivalence the result will be an equivalence.

ⓈHOLCONST
│ ⦏$RelPower⦎ : ('a SET × ('a → 'a → BOOL)) → 'b SET
│		→ (('b → 'a) SET × (('b → 'a) → ('b → 'a) → BOOL))
├──────
│ ∀ D r is⦁ RelPower (D, r) is =
│	({f | ∀i⦁ i ∈ is ⇒ f i ∈ D}, λf g⦁ ∀i⦁ i ∈ is ⇒ r (f i) (g i))
■

We now show that this construction preserves various properties of the relation.
=GFT
⦏RelPower_Trans_thm⦎ =
   ⊢ ∀ (D, r) is⦁ Trans (D, r) ⇒ Trans (RelPower (D, r) is)

⦏RelPower_Sym_thm⦎ =
   ⊢ ∀ (D, r) is⦁ Sym (D, r) ⇒ Sym (RelPower (D, r) is)

⦏RelPower_Refl_thm⦎ =
   ⊢ ∀ (D, r) is⦁ Refl (D, r) ⇒ Refl (RelPower (D, r) is)
=TEX

\ignore{
=SML
val RelPower_def = get_spec ⌜RelPower⌝;

set_goal([], ⌜∀(D, r) is⦁ Trans(D, r) ⇒ Trans (RelPower (D, r) is)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [RelPower_def, trans_def]
	THEN REPEAT strip_tac
	THEN REPEAT (all_asm_ufc_tac[]));
val RelPower_Trans_thm = save_pop_thm "RelPower_Trans_thm";

set_goal([], ⌜∀(D, r) is⦁ Sym(D, r) ⇒ Sym(RelPower (D, r) is)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [RelPower_def, sym_def]
	THEN REPEAT strip_tac
	THEN REPEAT (all_asm_ufc_tac[]));
val RelPower_Sym_thm = save_pop_thm "RelPower_Sym_thm";

set_goal([], ⌜∀(D, r) is⦁ Refl(D, r) ⇒ Refl(RelPower (D, r) is)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [RelPower_def, refl_def]
	THEN REPEAT strip_tac
	THEN REPEAT (all_asm_ufc_tac[]));
val RelPower_Refl_thm = save_pop_thm "RelPower_Refl_thm";
=TEX
}%ignore

\section{Group Theory}

=SML
new_parent "group_egs";
get_alias_info "Append";
set_merge_pcs ["basic_hol1", "'sets_alg", "'ℝ", "'rbjmisc"];
=TEX

\subsection{Group Products}

ⓈHOLCONST
│ ⦏GroupProduct⦎ : 'a GROUP → 'b GROUP → ('a × 'b) GROUP
├──────
│ ∀ G H⦁ GroupProduct G H =
│	let car = (Car G × Car H)
│	and prod	(la, lb) (ra, rb) = ((la.ra) G, (lb.rb) H)
│	and unit = (Unit G, Unit H)
│	and inv (a, b) = ((a ⋏~) G, (b ⋏~) H)
│	in MkGROUP car prod unit inv
■
=SML
declare_alias ("*", ⌜GroupProduct⌝);
=TEX
\ignore{
=SML
val ⦏group_def⦎ = get_spec⌜Group⌝;
val ⦏group_unit_def⦎ = get_spec⌜Unit⌝;
val ⦏gp_def⦎ = get_spec⌜GroupProduct⌝;
=TEX
=SML
set_goal([], ⌜∀g:'a GROUP; h:'b GROUP⦁
	g ∈ Group ∧ h ∈ Group ⇒ g * h ∈ Group⌝);
a(rewrite_tac [get_spec ⌜Group⌝,
	gp_def,
	group_unit_def,
	get_spec ⌜$×⌝,
	let_def]
	THEN REPEAT strip_tac
	THEN TRY (all_asm_fc_tac[])); (* ufc takes twice as long *)
val ⦏group_product_thm⦎ = save_pop_thm "group_product_thm";
=TEX
}%ignore

=GFT
group_product_thm = ⊢ ∀g:'a GROUP; h:'b GROUP⦁
	g ∈ Group ∧ h ∈ Group ⇒ g * h ∈ Group
=TEX

\subsection{Abelian Groups}

ⓈHOLCONST
│ ⦏AbelianGroup⦎ : 'a GROUP SET
├──────
│ ∀ G⦁ G ∈ AbelianGroup ⇔ G ∈ Group
│	∧ ∀ u v:'a⦁ u ∈ Car G ∧ v ∈ Car G
│	         ⇒ (u.v) G = (v.u) G
■

\ignore{
=SML
val ⦏abelian_group_def⦎ = get_spec⌜AbelianGroup⌝;
set_goal([], ⌜∀g:'a GROUP; h:'b GROUP⦁
	g ∈ AbelianGroup ∧ h ∈ AbelianGroup ∧
	Car g = Universe ∧ Car h = Universe
	⇒ Car (g * h) = Universe⌝);
a(rewrite_tac [abelian_group_def,
	group_def,
	gp_def,
	group_unit_def,
	get_spec ⌜$×⌝,
	let_def]
	THEN REPEAT strip_tac
	THEN TRY (asm_rewrite_tac[sets_ext_clauses]));
val ⦏abelian_group_product_lemma⦎ = save_pop_thm "abelian_group_product_lemma";
=TEX

=SML
set_goal([], ⌜∀g:'a GROUP; h:'b GROUP⦁
	g ∈ AbelianGroup ∧ h ∈ AbelianGroup 
	⇒ (g * h) ∈ AbelianGroup⌝);
a (rewrite_tac [abelian_group_def]);
a (REPEAT strip_tac);
a (all_asm_ufc_tac[group_product_thm]);
a (REPEAT_N 2 (POP_ASM_T ante_tac));
a (asm_rewrite_tac [
	gp_def,
	let_def,
	group_unit_def,
	get_spec ⌜$×⌝]);
a (REPEAT strip_tac
	THEN all_asm_ufc_tac[]);
val ⦏abelian_group_product_thm⦎ = save_pop_thm "abelian_group_product_thm";
=TEX

=SML
set_goal([], ⌜∀G:'g GROUP; H:'h GROUP; x y:'g; v w:'h⦁
	((x,v) . (y, w)) (G * H)
	= ((x . y)G, (v . w)H)⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [gp_def, let_def, group_unit_def]
	THEN REPEAT strip_tac);
val group_prod_prod_thm = save_pop_thm "group_prod_prod_thm";
=TEX
=SML
set_goal([], ⌜∀G:'g GROUP; H:'h GROUP; x y:'g × 'h⦁
	(x . y) (G * H)
	= ((Fst x . Fst y)G, (Snd x . Snd y)H)⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [gp_def, let_def, group_unit_def]
	THEN REPEAT strip_tac);
val group_prod_prod_thm1 = save_pop_thm "group_prod_prod_thm1";
=TEX

}%ignore

=GFT
abelian_group_product_thm = ⊢ ∀g:'a GROUP; h:'b GROUP⦁
	g ∈ AbelianGroup ∧ h ∈ AbelianGroup ⇒ (g * h) ∈ AbelianGroup
=TEX

\ignore{
=SML
set_goal([], ⌜ℝ⋎+ ∈ AbelianGroup⌝);
a (rewrite_tac [
	get_spec ⌜AbelianGroup⌝,
	ℝ_additive_ops_thm,
	ℝ_additive_group_thm
	]);
val ℝ_plus_abelian_thm = save_pop_thm "ℝ_plus_abelian_thm";
=TEX
}%ignore

=GFT
ℝ_plus_abelian_thm = ⊢ ℝ⋎+ ∈ AbelianGroup
=TEX

\section{Topology}

=SML
new_parent "topology";
get_alias_info "Append";
=TEX

\subsection{Bases etc.}

The following definitions belong properly in the theory ``topology''.

First we define the relationship between a $base$ and the topology of which it is a base.

=SML
declare_infix (300, "BaseOf");
=TEX

ⓈHOLCONST
│ $⦏BaseOf⦎ :  'a SET SET → 'a SET SET → BOOL
├──────
│ ∀ base topology⦁ base BaseOf topology ⇔
│	∀s⦁ s ∈ topology ⇒ ∃ ss⦁ ss ⊆ base ∧ s = ⋃ ss
■

However, what we really need here is the construction of a topology from an arbitrary set of sets, which is done as follows:

ⓈHOLCONST
│ $⦏TopologyFrom⦎ :  'a SET SET → 'a SET SET
├──────
│ ∀ sets⦁ TopologyFrom sets =
│	⋂ {topology | topology ∈ Topology ∧ sets ⊆ topology}
■

\ignore{

Prove that $TopologyFrom$ yields a topology.

}%ignore

\section{Disjoint Unions (Sum)}

Another cases theorem.

=GFT
sum_cases_thm2 =	⊢ ∀ x⦁ IsL x ∨ IsR x
=TEX

\ignore{
=SML
set_goal([], ⌜∀x⦁ IsL x ∨ IsR x⌝);
a (strip_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ sum_cases_thm));
(* *** Goal "1" *** *)
a (asm_rewrite_tac[sum_clauses]);
(* *** Goal "1" *** *)
a (asm_rewrite_tac[sum_clauses]);
val sum_cases_thm2 = save_pop_thm "sum_cases_thm2";
=TEX
}%ignore


Two ways of constructing functions over disjoint unions.

ⓈHOLCONST
│ ⦏Fun⋎+⦎: ('a → 't) → ('b→ 'u) → ('a + 'b → 't + 'u)
├──────
│ ∀f:'a → 't; g:'b → 'u; ab:'a + 'b⦁
│	Fun⋎+ f g ab = if IsL ab then InL (f (OutL ab)) else InR (g (OutR ab))
■

ⓈHOLCONST
│ ⦏FunSum⦎: ('a → 't) → ('b→ 't) → ('a + 'b → 't)
├──────
│ ∀f:'a → 't; g:'b → 't; ab:'a + 'b⦁
│	FunSum f g ab = if IsL ab then f (OutL ab) else g (OutR ab)
■

=GFT
⦏IsL_IsR_lemma⦎ =
	⊢ ∀ x⦁ IsR x ⇔ ¬ IsL x
=TEX

\ignore{
=SML
set_merge_pcs ["hol1", "'rbjmisc"];

set_goal([], ⌜∀x⦁ IsR x ⇔ ¬ IsL x⌝);
a (∀_tac);
a (strip_asm_tac (∀_elim ⌜x⌝ sum_cases_thm) THEN asm_rewrite_tac[]);
val IsL_IsR_lemma = save_pop_thm "IsL_IsR_lemma";

add_pc_thms "'rbjmisc" (map get_spec [] @ [IsL_IsR_lemma]);
set_merge_pcs ["hol", "'rbjmisc"];
=TEX
}%ignore

\section{Indexed Sets}

=SML
declare_type_abbrev(⦏"IX"⦎, ["'a", "'b"], ⓣ'a → 'b OPT⌝);
=TEX

ⓈHOLCONST
│ ⦏IxVal⦎ : ('b, 'a) IX → 'b → 'a
├───────────
│ ∀is g⦁ IxVal is g = ValueOf (is g)
■

ⓈHOLCONST
│ ⦏IxRan⦎ : ('b, 'a) IX → 'a SET
├───────────
│ ∀is⦁ IxRan is = {v | ∃α⦁ Value v = is α}
■

ⓈHOLCONST
│ ⦏IxDom⦎ : ('b, 'a) IX → 'b SET
├───────────
│ ∀is⦁ IxDom is = {i | IsDefined (is i)}
■

=GFT
⦏ix_domran_lemma⦎ =
   ⊢ ∀ x y⦁ x ∈ IxDom y ⇒ IxVal y x ∈ IxRan y

⦏ix_valueof_ran_lemma⦎ =
   ⊢ ∀ x y⦁ ¬ x y = Undefined ⇒ ValueOf (x y) ∈ IxRan x
=TEX

\ignore{
=SML
val IxVal_def = get_spec ⌜IxVal⌝;
val IxRan_def = get_spec ⌜IxRan⌝;
val IxDom_def = get_spec ⌜IxDom⌝;

set_goal ([], ⌜∀x y⦁ x ∈ IxDom y ⇒ IxVal y x ∈ IxRan y⌝);
a (REPEAT ∀_tac THEN rewrite_tac [IxDom_def, get_spec ⌜IxVal⌝, get_spec ⌜IxRan⌝]);
a (strip_tac THEN ∃_tac ⌜x⌝);
a (strip_asm_tac (∀_elim ⌜y x⌝ opt_cases_thm) THEN asm_rewrite_tac[]);
val ix_domran_lemma = save_pop_thm "ix_domran_lemma";

set_goal ([], ⌜∀x y⦁ ¬ x y = Undefined ⇒ ValueOf (x y) ∈ IxRan x⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜IxRan⌝]
	THEN REPEAT strip_tac);
a (strip_asm_tac (∀_elim ⌜x y⌝ (∧_right_elim (∧_right_elim (get_spec ⌜Value⌝)))));
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
val ix_valueof_ran_lemma = save_pop_thm "ix_valueof_ran_lemma";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏IxDomRes⦎ : 'a SET → ('a, 'b) IX → ('a, 'b) IX
├───────────
│ ∀ns is⦁ IxDomRes ns is = λx⦁ if x ∈ ns then is x else Undefined
■

ⓈHOLCONST
│ ⦏IxRanRes⦎ : ('a, 'b) IX → 'b SET → ('a, 'b) IX
├───────────
│ ∀is ns⦁ IxRanRes is ns = λx⦁ if x ∈ IxDom is ∧ ValueOf (is x) ∈ ns then is x else Undefined
■

=SML
declare_alias ("◁", ⌜IxDomRes⌝);
declare_alias ("▷", ⌜IxRanRes⌝);
=TEX

ⓈHOLCONST
│ ⦏IxUd⦎ : ('a, 'b) IX → 'a SET
├───────────
│ ∀is⦁ IxUd is = {i | is i = Undefined}
■

ⓈHOLCONST
│ ⦏IxOverRide⦎ : ('a, 'b) IX → ('a, 'b) IX → ('a, 'b) IX
├───────────
│ ∀is1 is2⦁ IxOverRide is1 is2 =
│	λi⦁ if ¬ i ∈ IxUd is2 then is2 i else is1 i 
■

=GFT
⦏ixud_eq_iff_ixdom_eq_lemma⦎ =
   ⊢ ∀ x y⦁ IxUd x = IxUd y ⇔ IxDom x = IxDom y

⦏ixoverride_ixdom_lemma⦎ =
   ⊢ ∀ x y⦁ IxDom (IxOverRide x y) = IxDom x ∪ IxDom y

⦏ixoverride_ixud_lemma⦎ =
   ⊢ ∀ x y⦁ IxUd (IxOverRide x y) = IxUd x \ IxDom y

⦏ixoverride_ixran_lemma⦎ =
   ⊢ ∀ x y⦁ IxRan (IxOverRide x y) ⊆ IxRan x ∪ IxRan y
=TEX

\ignore{
=SML
set_goal ([], ⌜∀x y⦁ IxUd x = IxUd y ⇔ IxDom x = IxDom y⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜IxDom⌝, get_spec ⌜IxUd⌝]
	THEN PC_T1 "hol1" prove_tac[]);
val ixud_eq_iff_ixdom_eq_lemma = save_pop_thm "ixud_eq_iff_ixdom_eq_lemma";

set_goal ([], ⌜∀x y⦁ IxDom (IxOverRide x y) = IxDom x ∪ IxDom y⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜IxDom⌝, get_spec ⌜IxOverRide⌝]
	THEN PC_T "hol1" strip_tac
	THEN strip_tac THEN rewrite_tac[∈_in_clauses, get_spec ⌜IxUd⌝]);
a (cases_tac ⌜y x' = Undefined⌝ THEN asm_rewrite_tac[]);
val ixoverride_ixdom_lemma = save_pop_thm "ixoverride_ixdom_lemma";

set_goal ([], ⌜∀x y⦁ IxRan (IxOverRide x y) ⊆ IxRan x ∪ IxRan y⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜IxRan⌝, get_spec ⌜IxOverRide⌝]
	THEN PC_T "hol1" strip_tac
	THEN strip_tac THEN rewrite_tac[∈_in_clauses, get_spec ⌜IxUd⌝]
	THEN strip_tac THEN POP_ASM_T ante_tac);
a (cases_tac ⌜y α = Undefined⌝ THEN asm_rewrite_tac[] THEN strip_tac);
(* *** Goal "1" *** *)
a (∨_left_tac THEN ∃_tac ⌜α⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∨_right_tac THEN ∃_tac ⌜α⌝ THEN asm_rewrite_tac[]);
val ixoverride_ixran_lemma = save_pop_thm "ixoverride_ixran_lemma";

set_goal ([], ⌜∀x y⦁ IxUd (IxOverRide x y) = IxUd x \ IxDom y ⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [get_spec ⌜IxUd⌝, get_spec ⌜IxDom⌝, get_spec ⌜IxOverRide⌝]
	THEN PC_T "hol1" strip_tac
	THEN strip_tac THEN rewrite_tac[∈_in_clauses, get_spec ⌜Undefined⌝]);
a (cases_tac ⌜y x' = Undefined⌝ THEN asm_rewrite_tac[]);
val ixoverride_ixud_lemma = save_pop_thm "ixoverride_ixud_lemma";

add_pc_thms "'rbjmisc" (map get_spec [] @ [ixud_eq_iff_ixdom_eq_lemma, ixoverride_ixdom_lemma, ixoverride_ixud_lemma]);
set_merge_pcs ["hol", "'rbjmisc"];
=TEX
}%ignore

ⓈHOLCONST
│ ⦏IxComp⦎ : ('a, 'b) IX → ('b → 'c) → ('a, 'c) IX
├───────────
│ ∀ix j⦁ IxComp ix j = λx⦁
│	if IsDefined (ix x) then Value (j (ValueOf (ix x))) else Undefined
■

=GFT
⦏IxDom_IxComp_thm⦎ =
	⊢ ∀ is f⦁ IxDom (IxComp is f) = IxDom is
=TEX

\ignore{
=SML
val IxComp_def = get_spec ⌜IxComp⌝;

set_goal([], ⌜∀is f⦁ IxDom (IxComp is f) = IxDom is⌝);
a (rewrite_tac [IxDom_def, IxComp_def,sets_ext_clauses] THEN REPEAT ∀_tac);
a (cond_cases_tac ⌜is x = Undefined⌝);
val IxDom_IxComp_thm = save_pop_thm "IxDom_IxComp_thm";

add_pc_thms "'rbjmisc" (map get_spec [] @ [IxDom_IxComp_thm]);
set_merge_pcs ["hol", "'rbjmisc"];
=TEX
}%ignore


ⓈHOLCONST
│ ⦏IxCompIx⦎ : ('a, 'b) IX → ('b, 'c) IX → ('a, 'c) IX
├───────────
│ ∀ix jx⦁ IxCompIx ix jx = λx⦁
│	if IsDefined (ix x) then jx (ValueOf (ix x)) else Undefined
■

=GFT
⦏IxDom_IxCompIx_thm⦎ =
	⊢ ∀ is1 is2⦁ IxDom (IxCompIx is1 is2) ⊆ IxDom is1
=TEX

\ignore{
=SML
val IxCompIx_def = get_spec ⌜IxCompIx⌝;

set_goal([], ⌜∀is1 is2⦁ IxDom (IxCompIx is1 is2) ⊆ IxDom is1⌝);
a (rewrite_tac [IxDom_def, IxCompIx_def, sets_ext_clauses] THEN REPEAT ∀_tac);
a (cond_cases_tac ⌜is1 x = Undefined⌝);
val IxDom_IxCompIx_thm = save_pop_thm "IxDom_IxCompIx_thm";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏IxInc⦎ : ('a, 'b) IX → ('a, 'b) IX → BOOL
├───────────
│ ∀i j⦁ IxInc i j ⇔ ∀x⦁ IsDefined (i x) ⇒ j x = i x 
■

=SML
declare_alias("⊑", ⌜IxInc⌝);
declare_infix(200, "⊑");
=TEX

=GFT
⦏IxInc_trans_thm⦎ =
	⊢ ∀ A B C⦁ A ⊑ B ∧ B ⊑ C ⇒ A ⊑ C

⦏IxDom_⊑_thm⦎ =
	⊢ ∀ A B s⦁ s ∈ IxDom A ∧ A ⊑ B ⇒ s ∈ IxDom B

⦏⊑_IxVal_thm⦎ =
	⊢ ∀ A B s⦁ s ∈ IxDom A ∧ A ⊑ B ⇒ IxVal B s = IxVal A s
=TEX

\ignore{
=SML
val IxInc_def = get_spec ⌜IxInc⌝;

set_goal([], ⌜∀A B C:('a, 'b) IX⦁ A ⊑ B ∧ B ⊑ C ⇒ A ⊑ C⌝);
a (REPEAT ∀_tac THEN rewrite_tac[IxInc_def] THEN REPEAT strip_tac
	THEN (all_asm_fc_tac[]));
a (DROP_NTH_ASM_T 2 ante_tac THEN SYM_ASMS_T rewrite_tac
	THEN strip_tac THEN all_asm_fc_tac[]);
val IxInc_trans_thm = save_pop_thm "IxInc_trans_thm";

set_goal([], ⌜∀A B s⦁ s ∈ IxDom A ∧ A ⊑ B ⇒ s ∈ IxDom B⌝);
a (REPEAT ∀_tac THEN rewrite_tac[IxInc_def, IxDom_def] THEN REPEAT strip_tac
	THEN (all_asm_fc_tac[]) THEN asm_rewrite_tac[]);
val IxDom_⊑_thm = save_pop_thm "IxDom_⊑_thm";

set_goal([], ⌜∀A B s⦁ s ∈ IxDom A ∧ A ⊑ B ⇒ IxVal B s = IxVal A s⌝);
a (REPEAT ∀_tac THEN rewrite_tac[IxInc_def, IxDom_def, IxVal_def] THEN REPEAT strip_tac
	THEN (all_asm_fc_tac[]) THEN asm_rewrite_tac[]);
val ⊑_IxVal_thm = save_pop_thm "⊑_IxVal_thm";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏IxPack⦎ : ('a × 'b)LIST → ('a, 'b)IX
├───────────
│         IxPack [] = (λis⦁ Undefined)
│ ∧ ∀h t⦁ IxPack (Cons h t) = λis⦁
│		if Fst h = is then Value (Snd h) else IxPack t is
■

=GFT
⦏IxDom_IxPack_disp_thm⦎ =
	⊢ IxDom (IxPack []) = {}
	∧ (∀ x y z⦁ IxDom (IxPack (Cons (x, y) z)) = Insert x (IxDom (IxPack z)))

⦏IxPack_lemma1⦎ =
	⊢ ∀ x y z⦁ IxPack (Cons (x, y) z) x = Value y

⦏IxPack_lemma2⦎ =
	⊢ ∀ w x y z⦁ (x=w ⇔ F) ⇒ IxPack (Cons (x, y) z) w = IxPack z w

⦏IxComp_IxPack_lemma⦎ =
	⊢ ∀ f h t⦁ IxComp (IxPack (Cons h t)) f
		= (λ z⦁ if z = Fst h then Value (f (Snd h)) else IxComp (IxPack t) f z)

⦏IxComp_IxPack_thm⦎ =
	⊢ ∀ f l⦁ IxComp (IxPack l) f = IxPack (Map (λ (x, y)⦁ (x, f y)) l)
=TEX

\ignore{
=SML
val IxPack_def = get_spec ⌜IxPack⌝;

set_goal([], ⌜IxDom (IxPack []) = {}
	∧ ∀x y z⦁ IxDom (IxPack (Cons (x,y) z)) = Insert x (IxDom (IxPack z))⌝);
a (rewrite_tac [IxDom_def, IxPack_def, sets_ext_clauses]);
a (REPEAT ∀_tac);
a (cond_cases_tac ⌜x = x'⌝);
(* *** Goal "1" *** *)
a (rewrite_tac [insert_def]);
(* *** Goal "2" *** *)
a (REPEAT strip_tac THEN all_var_elim_asm_tac);
val IxDom_IxPack_disp_thm = pop_thm();

set_goal([], ⌜∀x y z⦁ IxPack (Cons (x,y) z) x = Value y⌝);
a (rewrite_tac [IxPack_def]);
val IxPack_lemma1 = save_pop_thm "IxPack_lemma1";

set_goal([], ⌜∀w x y z⦁ (x=w ⇔ F) ⇒ IxPack (Cons (x,y) z) w = IxPack z w⌝);
a (rewrite_tac [IxPack_def] THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
val IxPack_lemma2 = save_pop_thm "IxPack_lemma2";

set_goal([], ⌜∀f h t⦁ IxComp (IxPack (Cons h t)) f = λz⦁ if z = Fst h then Value (f (Snd h)) else IxComp (IxPack t) f z⌝);
a (rewrite_tac [IxComp_def, IxPack_def, ext_thm]);
a (REPEAT ∀_tac);
a (cond_cases_tac ⌜x = Fst h⌝);
a (LEMMA_T ⌜¬ Fst h = x⌝ rewrite_thm_tac THEN1 (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac []));
val IxComp_IxPack_lemma = save_pop_thm "IxComp_IxPack_lemma";

set_goal([], ⌜∀f l⦁ IxComp (IxPack l) f = IxPack (Map (λ(x,y)⦁ (x, f y)) l)⌝);
a (REPEAT ∀_tac);
a (rewrite_tac [ext_thm]);
a (REPEAT ∀_tac);
a (list_induction_tac ⌜l⌝);
(* *** Goal "1" *** *)
a (rewrite_tac [IxComp_def, IxPack_def, map_def]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac [IxComp_IxPack_lemma]);
a (rewrite_tac [IxComp_def, IxPack_def, map_def]);
a (strip_tac);
a (LEMMA_T ⌜(Fst x' = x) = (x = Fst x')⌝ rewrite_thm_tac THEN1 (REPEAT strip_tac THEN asm_rewrite_tac []));
val IxComp_IxPack_thm = save_pop_thm "IxComp_IxPack_thm";
=TEX
}%ignore


=SML
fun IxPack_conv t =
	let val (_, [c, w]) = strip_app t;
            val (_, [xy, z]) = strip_app c;
	    val (x, y) = dest_pair xy;
	    val thm =  list_∀_elim [w,x,y,z] IxPack_lemma2;
	    val eq = mk_eq (x,w);
	    val prem = string_eq_conv eq
	in  ⇒_elim thm prem
	end handle _ => fail_conv t;
=IGN
IxPack_conv ⌜IxPack (Cons ("3",y) z) "32"⌝;

=SML
set_rw_eqn_cxt ([(⌜IxPack (Cons (x,y) z) w⌝, IxPack_conv)]) "'rbjmisc";
add_rw_thms (map get_spec [] @ [singleton_subset_lemma, insert_twice_thm]) "'rbjmisc";
add_rw_thms [NeSet_ne_thm] "'rbjmisc";
add_rw_thms [NeSet_PeSet_thm, MemOf_memof_thm, PeSet_Insert_thm, MemOf_NeSet_unit_thm] "'rbjmisc";
add_rw_thms (map get_spec [⌜IsDefined⌝, ⌜ValueOf⌝] @ [value_not_undefined_lemma, value_oneone_lemma]) "'rbjmisc";
add_rw_thms (map get_spec [⌜$∈⋎L⌝] @ [∀⋎L_clauses, ∃⋎L_clauses, ∀⋎L_thm, ∃⋎L_thm, ∀⋎L_append_thm, ∃⋎L_append_thm]) "'rbjmisc";
add_rw_thms (map get_spec [] @ [RelProd_projections_thm]) "'rbjmisc";
add_rw_thms (map get_spec [] @ [IsL_IsR_lemma]) "'rbjmisc";
add_rw_thms (map get_spec [] @ [ixud_eq_iff_ixdom_eq_lemma, ixoverride_ixdom_lemma, ixoverride_ixud_lemma]) "'rbjmisc";
add_rw_thms (map get_spec [] @ [IxDom_IxPack_disp_thm, IxPack_lemma1, IxDom_IxComp_thm]) "'rbjmisc";
add_rw_thms (map get_spec [] @ [combc_thm, bincomp_thm]) "'rbjmisc";

add_pc_thms "'rbjmisc" (map get_spec [] @ [IxDom_IxPack_disp_thm, IxPack_lemma1]);
set_merge_pcs ["hol", "'rbjmisc"];

commit_pc "'rbjmisc";


force_new_pc "⦏rbjmisc⦎";
merge_pcs ["hol", "'rbjmisc"] "rbjmisc";
commit_pc "rbjmisc";

force_new_pc "⦏rbjmisc1⦎";
merge_pcs ["'rbjmisc", "hol1"] "rbjmisc1";
commit_pc "rbjmisc1";
=TEX


{\let\Section\section
\def\section#1{\Section{#1}\label{TheoryListing}}
\include{rbjmisc.th}
}  %\let

\twocolumn[\section{INDEX}\label{INDEX}]
{\small\printindex}

\end{document}
=SML
set_flag ("pp_use_alias", true);
output_theory{out_file="rbjmisc.th.doc", theory="rbjmisc"};
=TEX
