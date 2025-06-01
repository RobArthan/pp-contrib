=IGN
$Id: t017.doc,v 1.7 2011/08/15 17:00:38 rbj Exp $
open_theory "cat";
set_merge_pcs["basic_hol1", "'sets_alg", "'ℝ", "'savedthm_cs_∃_conv"];
set_flag ("pp_use_alias", false);
=TEX
\documentclass[11pt,a4paper]{article}
%\usepackage{latexsym}
%\usepackage{ProofPower}
\usepackage{rbj}
\ftlinepenalty=9999
\tabstop=0.25in
\usepackage{A4}

\def\Hide#1{\relax}
\newcommand{\ignore}[1]{}

\title{Category Theory}
\author{Roger Jones}
\date{\ }

\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

\makeindex
\begin{document}
\vfill
\maketitle
\begin{abstract}
Formalisation of some of the concepts of category theory in {\ProductHOL}.
\end{abstract}
\vfill

\begin{centering}
{\footnotesize

Created 2006/04/09

Last Changed $ $Date: 2011/08/15 17:00:38 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t017.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t017.pdf}

$ $Id: t017.doc,v 1.7 2011/08/15 17:00:38 rbj Exp $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize
\end{centering}

\newpage
\tableofcontents
\newpage
%%%%
%%%%

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\section{Introduction}

This is minor exercise to help some of the elementary concepts of category theory into my brain, and is not intended to show offer any enlightenment which cannot be found in any elementary text on category theory.
In fact I am following Saunders Mac Lane (roughly).

Create new theory ``cat'', parent ``rbjmisc''.
=SML
open_theory "rbjmisc";
open PreConsisProof; open UnifyForwardChain; open Trawling;
force_new_theory "cat";
force_new_pc "'cat";
merge_pcs ["'savedthm_cs_∃_proof"] "'cat";
new_parent "sum";
new_parent "one";
set_merge_pcs["rbjmisc", "'cat"];
set_flag ("pp_use_alias", true);
=TEX

\ignore{
=SML
=TEX
}%ignore

\section{Categories Functors and Natural Transformations}

\subsection{Definition of Category}

We model a category by its set of arrows.
It is therefore a set (of arrows), together with:

\begin{itemize}
\item a partial associative operation over the arrows
\item left and right operators which return the domain and codomain of each arrow
\end{itemize}

ⓈHOLLABPROD ⦏CAT⦎─────────────────
│	Arrows	:'a SET;
│	Compose	:'a → 'a → 'a;
│	Left Right: 'a → 'a
■─────────────────────────

Before giving the definition of a category it will be convenient to define some auxiliary concepts.

ⓈHOLCONST
│ ⦏Obj⦎ :  'a CAT → 'a SET
├──────
│ ∀ C a⦁ a ∈ Obj C ⇔ a ∈ Arrows C ∧ a = Left C a
■

We need often to state explicitly that two arrows are composable and therefore introduce a notation for this.
We use an infix operator which yields a property of categories.

=SML
declare_infix(400, "Υ");
=TEX

ⓈHOLCONST
│ ⦏$Υ⦎ :  'a → 'a → 'a CAT → BOOL
├──────
│ ∀ f g C⦁ (f Υ g) C ⇔
│	f ∈ Arrows C ∧ g ∈ Arrows C
│	∧ Right C f = Left C g
■

ⓈHOLCONST
│ ⦏Identity⦎ :  'a CAT → 'a SET
├──────
│ ∀ C a⦁ a ∈ Identity C ⇔ a ∈ Arrows C
│	∧ Left C a = a ∧ Right  C a = a
│	∧ ∀b⦁ b ∈ Arrows C ⇒ (Left C b = a ⇒ Compose C a b = b)
│	     ∧ (Right C b = a ⇒ Compose C b a = b)
■

It will also be convenient to cite concisely the domain and codomain of an arrow, i.e. a notation for homsets.

=SML
declare_infix(400, ">->");
=TEX

ⓈHOLCONST
│ ⦏$>->⦎ :  'a → 'a → 'a CAT → 'a SET
├──────
│ ∀ f a b C⦁ f ∈ (a >-> b) C ⇔
│	f ∈ Arrows C ∧ a ∈ Arrows C ∧ b ∈ Arrows C
│	∧ Left C f = a ∧ Right C f = b
■

=SML
declare_alias ("↣", ⌜$>->⌝);
=TEX

An infix notation for composition:

=SML
declare_infix(500, "o⋎c");
=TEX

ⓈHOLCONST
│ ⦏$o⋎c⦎ :  'a → 'a → 'a CAT → 'a
├──────
│ ∀ f g C⦁ (f o⋎c g) C = Compose C f g
■

ⓈHOLCONST
│ ⦏Cat⦎ :  'a CAT → BOOL
├──────
│ ∀ ⋎c⦁ Cat ⋎c ⇔
│   (∀ x⦁ x ∈ Arrows ⋎c
│	⇒ Left ⋎c x ∈ Identity ⋎c ∧ Right ⋎c x ∈ Identity ⋎c)
│ ∧ (∀ x y⦁ (x Υ y)⋎c ⇒ (x o⋎c y)⋎c ∈ Arrows ⋎c
│	∧ ((x o⋎c y)⋎c) ∈ ((Left ⋎c x) ↣ (Right ⋎c y))⋎c)
│ ∧ (∀ x y z⦁ (x Υ y)⋎c ∧ (y Υ z)⋎c 
│	⇒ (x o⋎c (y o⋎c z)⋎c)⋎c = (((x o⋎c y)⋎c) o⋎c z)⋎c)
■

=GFT

=TEX
\ignore{
=SML
val ⦏CAT_def⦎ = get_spec ⌜MkCAT⌝;
val ⦏obj_def⦎ = get_spec ⌜Obj⌝;
val ⦏Υ_def⦎ = get_spec ⌜$Υ⌝;
val ⦏Identity_def⦎ = get_spec ⌜Identity⌝;
val ⦏gt_gt_def⦎ = get_spec ⌜$>->⌝;
val ⦏o⋎c_def⦎ = get_spec ⌜$o⋎c⌝;
val ⦏Cat_def⦎ = get_spec ⌜Cat⌝;

add_pc_thms "'cat" [CAT_def];
set_merge_pcs ["rbjmisc", "'cat"];
=TEX
}%ignore

\subsubsection{Notation for Commutative Diagrams}

I have no idea whether this is any use.

=SML
declare_infix (310, "Ξ");
declare_infix (310, "Λ");
=TEX
\ignore{
=SML
set_goal ([], ⌜∃$Λ:'a CAT → 'a LIST → 'a⦁
 ∀ C la a⦁ C Λ [a] = a
	∧ (la = [] ∨ C Λ (Cons a la) = Compose C a (C Λ la))⌝);
a (prove_∃_tac THEN  strip_tac);
a (lemma_tac ⌜∃f:'a LIST → 'a⦁ ∀x y z⦁
	f [] = (εv:'a⦁T) ∧ f (Cons y z) = if z = [] then y else (Compose C' y (f z))⌝);
a (prove_∃_tac);
a (∃_tac ⌜f⌝ THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏$Λ⦎ :  'a CAT → 'a LIST → 'a
├──────
│ ∀ C la a⦁ C Λ [a] = a
│	∧ (la = [] ∨ C Λ (Cons a la) = Compose C a (C Λ la))
■

ⓈHOLCONST
│ ⦏$Ξ⦎ :  'a CAT → 'a LIST LIST → BOOL
├──────
│ ∀ C lla⦁ CΞ lla ⇔
│    ∃x⦁ Fold Insert (Map ($Λ C) lla) {} = {x}
■

\subsection{Categories}

\ignore{
=SML
set_goal([], ⌜∃∅⋎c:'a CAT⦁ Arrows ∅⋎c = {}⌝);
a (∃_tac ⌜MkCAT ({}:'a SET) (λx y⦁x) (λx⦁x) (λx⦁x)⌝);
a (rewrite_tac [get_spec ⌜Arrows⌝]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏∅⋎c⦎ :  'a CAT 
├──────
│ Arrows ∅⋎c = {} 
■

\ignore{
=SML
set_goal([], ⌜∃1⋎c:'a → 'a CAT⦁ ∀x:'a⦁ Cat (1⋎c x) ∧ Arrows (1⋎c x) = {x}⌝);
a (∃_tac ⌜λx:'a⦁ MkCAT ({x}:'a SET) (λy z⦁x) (λy⦁x) (λy⦁x)⌝);
a (rewrite_tac [Cat_def, get_spec ⌜Arrows⌝, gt_gt_def, Identity_def, o⋎c_def]
	THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏1⋎c⦎ :  'a → 'a CAT 
├──────
│ ∀x:'a⦁ Cat (1⋎c x) ∧ Arrows (1⋎c x) = {x} 
■

Of course, we have:

=GFT
⦏Cat_∅⋎c_thm⦎ ⊢ Cat ∅⋎c
=TEX

\ignore{
=SML
val ∅⋎c_def = get_spec ⌜∅⋎c⌝;
set_pc "hol1";
set_goal ([], ⌜Cat ∅⋎c⌝);
a (prove_tac [Cat_def, ∅⋎c_def, Υ_def]
	THEN REPEAT strip_tac);
val Cat_∅⋎c_thm = save_pop_thm "Cat_∅⋎c_thm";
=TEX
=SML
val one⋎c_def = get_spec ⌜1⋎c⌝;
set_goal ([], ⌜∀x⦁ Cat (1⋎c x)⌝);
a (prove_tac [Cat_def, one⋎c_def]
	THEN REPEAT strip_tac);
val Cat_1⋎c_thm = save_pop_thm "Cat_1⋎c_thm";
=TEX
}

Both of the above are special cases of {\it discrete} categories.
In a discrete category all arrows are identity arrows.
The following function allows the construction of arbitrary discrete categories.

ⓈHOLCONST
│ ⦏Discrete⋎c⦎ :  'a SET → 'a CAT 
├──────
│ ∀s:'a SET⦁ Discrete⋎c s = MkCAT s (λx y⦁ x) (λx⦁x) (λx⦁x) 
■

Any set can be made into a discrete category in this way:

=GFT
discrete_cat_thm ⊢ ∀s⦁ Cat (Discrete⋎c s)
=TEX

\ignore{
=SML
set_goal([], ⌜∀s⦁ Cat (Discrete⋎c s)⌝);
a (prove_tac [Cat_def, get_spec ⌜MkCAT⌝, get_spec ⌜Discrete⋎c⌝,
	Identity_def, Υ_def, gt_gt_def, o⋎c_def]);
val discrete_cat_thm = save_pop_thm "discrete_cat_thm";


add_pc_thms "'cat" [Cat_∅⋎c_thm, discrete_cat_thm];
set_merge_pcs ["rbjmisc", "'cat"];
=TEX
}%ignore

\subsection{Functors}

ⓈHOLCONST
│ ⦏Functor⦎ :  'a CAT × 'b CAT → ('a → 'b) SET
├──────
│ ∀ A B f⦁ f ∈ Functor (A,B) ⇔
│    (∀a⦁ a ∈ Arrows A ⇒ f a ∈ Arrows B)
│ ∧   ∀a b⦁ (a Υ b) A
│	⇒ Right B (f a) = f (Right A a)
│	∧ Left B (f b) = f (Left A b)
│	∧ Compose B (f a) (f b) = f (Compose A a b)
■

ⓈHOLCONST
│ ⦏Full⦎ :  'a CAT × 'b CAT → ('a → 'b) SET
├──────
│ ∀ A B f⦁ f ∈ Full (A,B) ⇔
│    ∀b⦁ b ∈ Arrows B ⇒ ∃a⦁ a ∈ Arrows A ∧ b = f a
■

ⓈHOLCONST
│ ⦏Faithful⦎ :  'a CAT × 'b CAT → ('a → 'b) SET
├──────
│ ∀ A B f⦁ f ∈ Faithful (A,B) ⇔
│    ∀a b⦁ a ∈ Arrows A ∧ b ∈ Arrows A ∧ f a = f b ⇒ a = b
■

Since functors are functions, they compose, and the composition is also a functor.
Composition also preserves fullness and faithfulness.

=GFT
functor_composition_thm ⊢
	∀A:'a CAT; B:'b CAT; C:'c CAT; ab: 'a → 'b; bc: 'b → 'c⦁
	ab ∈ Functor (A,B) ∧ bc ∈ Functor (B,C) ⇒ (bc o ab) ∈ Functor (A,C)
=TEX

\ignore{
=SML
push_merge_pcs["hol", "'savedthm_cs_∃_proof"];
set_goal([], ⌜∀A:'a CAT; B:'b CAT; C:'c CAT; ab: 'a → 'b; bc: 'b → 'c⦁
	ab ∈ Functor (A,B) ∧ bc ∈ Functor (B,C) ⇒ (bc o ab) ∈ Functor (A,C)⌝);
a (rewrite_tac [get_spec ⌜Functor⌝, Υ_def]
	THEN REPEAT_N 6 strip_tac);
a (lemma_tac ⌜∀ a⦁ a ∈ Arrows A ⇒ bc (ab a) ∈ Arrows C⌝ THEN1 asm_prove_tac[]);
a (asm_rewrite_tac[] THEN REPEAT_N 3 strip_tac);
a (lemma_tac ⌜Right B (ab a) = Left B (ab b)⌝ THEN1 (
	all_asm_ufc_tac[] THEN asm_rewrite_tac[]));
a (all_asm_ufc_tac[]);
a (all_asm_ufc_tac[]);
a (asm_rewrite_tac[]);
val functor_composition_thm = save_pop_thm "functor_composition_thm ";
pop_pc();
=TEX
}%ignore

=GFT
full_compose_thm ⊢
	∀A:'a CAT; B:'b CAT; C:'c CAT; ab: 'a → 'b; bc: 'b → 'c⦁
	ab ∈ Full (A,B) ∧ bc ∈ Full (B,C) ⇒ (bc o ab) ∈ Full (A,C)
=TEX

\ignore{
=SML
push_merge_pcs["hol", "'savedthm_cs_∃_proof"];
set_goal([], ⌜∀A:'a CAT; B:'b CAT; C:'c CAT; ab: 'a → 'b; bc: 'b → 'c⦁
	ab ∈ Full (A,B) ∧ bc ∈ Full (B,C) ⇒ (bc o ab) ∈ Full (A,C)⌝);
a (rewrite_tac (map get_spec [⌜Full⌝])
	THEN REPEAT strip_tac);
a (REPEAT_N 2 (all_asm_ufc_tac[]));
a (∃_tac ⌜a'⌝ THEN rewrite_tac [asm_rule ⌜b = bc a⌝]
	THEN asm_rewrite_tac[]);
val full_compose_thm = save_pop_thm "full_compose_thm ";
pop_pc();
=TEX
}%ignore

=GFT
faithful_compose_thm ⊢
	∀A:'a CAT; B:'b CAT; C:'c CAT; ab: 'a → 'b; bc: 'b → 'c⦁
	ab ∈ Functor (A,B) ∧ ab ∈ Faithful (A,B) ∧ bc ∈ Faithful (B,C)
	⇒ (bc o ab) ∈ Faithful (A,C)
=TEX

\ignore{
=SML
push_merge_pcs["hol", "'savedthm_cs_∃_proof"];
set_goal([], ⌜∀A:'a CAT; B:'b CAT; a:'a; ab:'a → 'b⦁
	a ∈ Arrows A ∧ ab ∈ Functor (A,B) ⇒ ab a ∈ Arrows B⌝);
a (prove_tac (map get_spec [⌜Functor⌝, ⌜Arrows⌝]));
val functor_arrow_thm = save_pop_thm "functor_arrow_thm";

set_goal([], ⌜∀A:'a CAT; B:'b CAT; C:'c CAT; ab: 'a → 'b; bc: 'b → 'c⦁
	ab ∈ Functor (A,B) ∧ ab ∈ Faithful (A,B) ∧ bc ∈ Faithful (B,C)
	⇒ (bc o ab) ∈ Faithful (A,C)⌝);
a (rewrite_tac (map get_spec [⌜Functor⌝, ⌜Faithful⌝])
	THEN REPEAT strip_tac);
a (REPEAT (all_asm_ufc_tac[]));
val faithful_thm = save_pop_thm "faithful_thm ";
pop_pc();
=TEX
}%ignore

\subsubsection{Subcategories}

=SML
declare_infix (310, "⊆⋎c");
=TEX

ⓈHOLCONST
│ $⦏⊆⋎c⦎ : 'a CAT → 'a CAT → BOOL
├──────
│ ∀ A1 A2⦁ A1 ⊆⋎c A2 ⇔
│	(∀a⦁ a ∈ Arrows A1 ⇒ a ∈ Arrows A2
│   		∧ Left A1 a ∈ Arrows A1 ∧ Right A1 a ∈ Arrows A1
│   		∧ Left A1 a = Left A2 a ∧ Right A1 a = Right A2 a)

	∧ (∀a b⦁ a ∈ Arrows A1 ∧ b ∈ Arrows A1 ⇒ 
		  Compose A1 a b ∈ Arrows A1
		∧ Compose A1 a b = Compose A2 a b)
■

A subcategory of a category is of course a category.

=GFT
subcat_cat_thm ⊢ ∀a b:'a CAT⦁ Cat a ∧ b ⊆⋎c a ⇒ Cat b
=TEX

\ignore{
=SML
set_goal ([], ⌜∀A B:'a CAT⦁ Cat A ∧ B ⊆⋎c A ⇒ Cat B⌝);
a (rewrite_tac (map get_spec [⌜Cat⌝, ⌜$⊆⋎c⌝])
	THEN REPEAT_N 6 strip_tac
	THEN REPEAT (all_asm_fc_tac [] THEN (asm_rewrite_tac[])));
(* *** Goal "1" *** *)
a (lemma_tac ⌜∀z⦁ z ∈ Arrows B ⇒ z ∈ Identity A ⇒ z ∈ Identity B⌝
	THEN1 rewrite_tac [Identity_def] THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (LEMMA_T ⌜Left B z = Left A z⌝ rewrite_thm_tac THEN1 spec_nth_asm_tac 15 ⌜z⌝
	THEN strip_tac);
(* *** Goal "1.2" *** *)
a (LEMMA_T ⌜Right B z = Right A z⌝ rewrite_thm_tac THEN1 spec_nth_asm_tac 15 ⌜z⌝
	THEN strip_tac);
(* *** Goal "1.3" *** *)
a (lemma_tac ⌜b ∈ Arrows A⌝ THEN1 REPEAT (all_asm_fc_tac[]));
a (lemma_tac ⌜Left B b = Left A b⌝ THEN1 REPEAT (all_asm_fc_tac[]));
a (lemma_tac ⌜Left A b = z⌝ THEN1 (DROP_ASM_T ⌜Left B b = z⌝ ante_tac THEN asm_rewrite_tac[]));
a (lemma_tac ⌜Compose A z b = b⌝ THEN1 REPEAT (all_asm_fc_tac[]));
a (LEMMA_T ⌜Compose B z b = Compose A z b⌝ rewrite_thm_tac THEN1 REPEAT (all_asm_fc_tac[]));
a (strip_tac);
(* *** Goal "1.4" *** *)
a (lemma_tac ⌜b ∈ Arrows A⌝ THEN1 REPEAT (all_asm_fc_tac[]));
a (lemma_tac ⌜Right B b = Right A b⌝ THEN1 REPEAT (all_asm_fc_tac[]));
a (lemma_tac ⌜Right A b = z⌝ THEN1 (DROP_ASM_T ⌜Right B b = z⌝ ante_tac THEN asm_rewrite_tac[]));
a (lemma_tac ⌜Compose A b z = b⌝ THEN1 REPEAT (all_asm_fc_tac[]));
a (LEMMA_T ⌜Compose B b z = Compose A b z⌝ rewrite_thm_tac THEN1 REPEAT (all_asm_fc_tac[]));
a (strip_tac);
(* *** Goal "1.5" *** *)
a (lemma_tac ⌜Left A x ∈ Identity A⌝ THEN1 REPEAT (all_asm_fc_tac[]));
a (LEMMA_T ⌜Left B x ∈ Arrows A⌝ (asm_tac o (rewrite_rule [asm_rule ⌜Left B x = Left A x⌝]))THEN1 REPEAT (all_asm_fc_tac[]));
a (GET_ASM_T ⌜Left B x ∈ Arrows B⌝ (asm_tac o (rewrite_rule [asm_rule ⌜Left B x = Left A x⌝])));
a (all_asm_fc_tac[]);
(* *** Goal "1.6" *** *)
a (lemma_tac ⌜Right A x ∈ Identity A⌝ THEN1 REPEAT (all_asm_fc_tac[]));
a (LEMMA_T ⌜Right B x ∈ Arrows A⌝ (asm_tac o (rewrite_rule [asm_rule ⌜Right B x = Right A x⌝]))THEN1 REPEAT (all_asm_fc_tac[]));
a (GET_ASM_T ⌜Right B x ∈ Arrows B⌝ (asm_tac o (rewrite_rule [asm_rule ⌜Right B x = Right A x⌝])));
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (REPEAT_N 2 strip_tac THEN lemma_tac ⌜(x Υ y) A⌝ );
(* *** Goal "2.1" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac [Υ_def] THEN REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a (asm_fc_tac[]);
(* *** Goal "2.1.2" *** *)
a (asm_fc_tac[]);
(* *** Goal "2.1.3" *** *)
a (POP_ASM_T ante_tac);
a (LEMMA_T ⌜Left B y = Left A y⌝ rewrite_thm_tac THEN1 asm_fc_tac[]);
a (LEMMA_T ⌜Right B x = Right A x⌝ rewrite_thm_tac THEN1 asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (list_spec_nth_asm_tac 6 [⌜x⌝, ⌜y⌝]);
a (strip_tac);
(* *** Goal "2.2.1" *** *)
a (DROP_ASM_T ⌜(x o⋎c y) A ∈ Arrows A⌝ ante_tac THEN rewrite_tac[o⋎c_def]);
=IGN
a (lemma_tac ⌜∀z⦁ z ∈ Arrows B ⇒ z ∈ Identity A ⇒ z ∈ Identity B⌝
	THEN1 rewrite_tac [Identity_def] THEN REPEAT strip_tac);


a (LEMMA_T ⌜Left A x ∈ Identity A ∧ Right A x ∈ Identity A⌝ ante_tac
	THEN1 (all_asm_fc_tac[] THEN REPEAT strip_tac));
a (rewrite_tac [Identity_def] THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a ((ante_tac o asm_rule) ⌜Left B x ∈ Arrows B⌝
	THEN rewrite_tac[(eq_sym_rule o asm_rule) ⌜Left B x = Left A x⌝]);
(* *** Goal "1.2" *** *)

	THEN_TRY SYM_ASMS_T once_rewrite_tac);

a (rewrite_tac (map get_spec [⌜Cat⌝, ⌜$Υ⌝, ⌜$⊆⋎c⌝, ⌜Identity⌝])
	THEN REPEAT_N 4 strip_tac
	THEN REPEAT (all_asm_fc_tac [] THEN (asm_rewrite_tac[])));
(* *** Goal "1" *** *)
a (lemma_tac ⌜Left a b = Right a x⌝);


a (spec_nth_asm_tac 3 ⌜x⌝ THEN asm_rewrite_tac[]);


a (lemma_tac ⌜Left b x ∈ Arrows b ∧ Right b x ∈ Arrows b⌝
	THEN1 (asm_fc_tac[] THEN REPEAT strip_tac));
a (lemma_tac ⌜((Left b x) o⋎c x) b = ((Left b x) o⋎c x) a⌝
	THEN1 all_asm_fc_tac[]);
a (lemma_tac ⌜(x o⋎c (Right b x))b = (x o⋎c (Right b x)) a⌝
	THEN1 all_asm_fc_tac[]);
a (lemma_tac ⌜Left b x = Left a x ∧ Right b x = Right a x⌝
	THEN1 (asm_fc_tac[] THEN REPEAT strip_tac)
	THEN asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 10 (asm_tac o (rewrite_rule [get_spec ⌜$⊆⌝])));
a (lemma_tac ⌜x ∈ Arrows a⌝ THEN1 all_asm_fc_tac[]);
a (rewrite_tac [Identity_def]);
a (all_asm_fc_tac[] THEN asm_rewrite_tac[]);
a (asm_tac (rewrite_rule [asm_rule ⌜Left b x = Left a x⌝]
	(asm_rule ⌜Left b x ∈ Arrows b⌝)));
a (spec_nth_asm_tac 43 ⌜Left a x⌝);
a (asm_rewrite_tac[]);
a (asm_tac (rewrite_rule [asm_rule ⌜Right b x = Right a x⌝]
	(asm_rule ⌜Right b x ∈ Arrows b⌝)));
a (spec_nth_asm_tac 48 ⌜Right a x⌝);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (all_asm_fc_tac[] THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (lemma_tac ⌜(Compose b x y) ∈ Arrows b⌝
	THEN1 all_asm_ufc_tac[]);
a (lemma_tac ⌜Left b (Compose b x y) = Left a (Compose b x y)
	∧ Compose b x y = Compose a x y ∧ Left b x = Left a x
	∧ Right b x = Right a x ∧ Left b y = Left a y
	∧ x ∈ Arrows a ∧ y ∈ Arrows a⌝
	THEN1 (all_asm_ufc_tac[] THEN REPEAT strip_tac));
a (asm_rewrite_tac[]);
a (GET_NTH_ASM_T 9 (asm_tac o (rewrite_rule [
	asm_rule ⌜Right b x = Right a x⌝,
	asm_rule ⌜Left b y = Left a y⌝])));
a (all_asm_ufc_tac []);
(* *** Goal "2.3" *** *)
a (lemma_tac ⌜(Compose b x y) ∈ Arrows b⌝
	THEN1 all_asm_ufc_tac[]);
a (lemma_tac ⌜Right b (Compose b x y) = Right a (Compose b x y)
	∧ Compose b x y = Compose a x y ∧ Right b y = Right a y
	∧ Right b x = Right a x ∧ Left b y = Left a y
	∧ x ∈ Arrows a ∧ y ∈ Arrows a⌝
	THEN1 (all_asm_ufc_tac[] THEN REPEAT strip_tac));
a (asm_rewrite_tac[]);
a (GET_NTH_ASM_T 9 (asm_tac o (rewrite_rule [
	asm_rule ⌜Right b x = Right a x⌝,
	asm_rule ⌜Left b y = Left a y⌝])));
a (all_asm_ufc_tac []);
(* *** Goal "3" *** *)
a (REPEAT strip_tac);
a (list_spec_nth_asm_tac 6 [⌜y⌝, ⌜z⌝]);
a (list_spec_nth_asm_tac 8 [⌜x⌝, ⌜y⌝]);
a (list_spec_nth_asm_tac 10 [⌜x⌝, ⌜Compose b y z⌝]);
a (list_spec_nth_asm_tac 12 [⌜Compose b x y⌝, ⌜z⌝]);
a (asm_rewrite_tac[]);
a (fc_tac [asm_rule ⌜∀ x⦁ x ∈ Arrows b ⇒ x ∈ Arrows a⌝]);
a (list_spec_nth_asm_tac 24 [⌜x⌝, ⌜y⌝, ⌜z⌝]);
(* *** Goal "3.1" *** *)
a (spec_nth_asm_tac 23 ⌜x⌝);
a (spec_nth_asm_tac 27 ⌜y⌝);
a (GET_NTH_ASM_T 26 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "3.2" *** *)
a (spec_nth_asm_tac 23 ⌜y⌝);
a (spec_nth_asm_tac 27 ⌜z⌝);
a (GET_NTH_ASM_T 25 ante_tac THEN asm_rewrite_tac[]);
val subcat_cat_thm = save_pop_thm "subcat_cat_thm ";
=TEX
}%ignore

\subsection{Natural Transformations}

ⓈHOLCONST
│ $⦏NatTran⦎ :  ('a CAT × 'b CAT) → (('a → 'b) × ('a → 'b)) → ('a → 'b) SET
├──────
│ ∀ A B R S τ⦁ τ ∈ NatTran (A,B) (R,S) ⇔
│    (∀a⦁ a ∈ Obj A
│	⇒ τ a ∈ Arrows B ∧ Left B(τ a) = R a ∧ Right B(τ a) = S a)
│ ∧ (∀f⦁ f ∈ Arrows A
│	⇒ Left B(τ (Right A f)) = R f ∧ Right B(τ (Right A f)) = S f
│	∧ Compose B (τ (Left A f)) (S f) = Compose B (R f) (τ (Right A f)))
■

ⓈHOLCONST
│ $⦏Id⋎N⋎T⦎ :  ('a CAT × 'b CAT) → ('a → 'b) → ('a → 'b)
├──────
│ ∀ A B R f⦁ Id⋎N⋎T (A,B) R f = Left B (R f)
■

\ignore{
=IGN
val nat_tran_def = get_spec ⌜NatTran⌝;
val idnt_def = get_spec ⌜Id⋎N⋎T⌝;
set_goal([], ⌜∀A B R⦁ Cat A ∧ Cat B ∧ R ∈ Functor (A,B)
	⇒ Id⋎N⋎T (A,B) R ∈ NatTran (A,B) (R,R)⌝);
a (rewrite_tac [nat_tran_def, idnt_def, get_spec ⌜Functor⌝, get_spec ⌜Obj⌝, Cat_def]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_asm_ufc_tac[] THEN all_asm_ufc_tac[]);
(* *** Goal "2" *** *)
a (all_asm_ufc_tac[] THEN all_asm_ufc_tac[]);
(* *** Goal "3" *** *)
a (all_asm_ufc_tac[] THEN all_asm_ufc_tac[]);

=TEX
}%ignore

\section{Constructions on Categories}

\subsection{Opposites}

=SML
declare_postfix (400, "⋏op");
=TEX

ⓈHOLCONST
│ $⦏⋏op⦎ : 'a CAT → 'a CAT
├──────
│ ∀ C⦁ C ⋏op = MkCAT (Arrows C) (λx y ⦁ Compose C y x) (Right C) (Left C)
■

\ignore{
=IGN
val Cat_def = get_spec ⌜Cat⌝;
val op_def = get_spec ⌜$⋏op⌝;

set_goal([], ⌜∀C⦁ Cat C ⇒ Cat (C ⋏op)⌝);
a (rewrite_tac[Cat_def, op_def] THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);

=TEX
}%ignore


\subsection{Functor Categories}



\section{The Yoneda Embedding}

I conjecture that the Yoneda embedding can be defined without resort to "The" category of sets, and without constraints on size.




\section{Categorial Structures}

This doesn't belong here, and if it gets anywhere it will be moved elsewhere.
Its an experiment in doing a kind of categorical foundation system by methods analogous to the study of foundations via the study of membership structures.

In the domain of discourse there exist only arrows.
Some of these are identity arrows and such arrows are themselves categories.

The structure which constitutes a category is taken as defined in {\it Category Theory} \cite{rbjt017}.
The categorial structure is given by a type of arrows one element of which is distinguished as the universal category together with a function which assignes to each identity arrow in that category some other category.

=SML
open_theory "cat";
force_new_theory "fcat";
new_parent "membership";
=TEX

ⓈHOLLABPROD FCAT─────
│ Ucat : 'a CAT;
│ Catmap: 'a → 'a CAT
■──────────────

The idea is then to define the properties of FCAT which are desirable for if they are to serve as the model of a foundation system, as an ontology for mathematics.

As in set theory we have some axioms which tell us what kind of things sets are, and then axioms which tell us which objects of that kind actually exist.

ⓈHOLCONST
│ ⦏Fcat⦎ :  'a FCAT → BOOL
├──────
│ ∀fc: 'a FCAT⦁ Cat (Ucat fc)
│       ∧ ∀obj:'a⦁ obj ∈ Obj (Ucat fc) ⇒ Cat (Catmap fc obj)
■

\section{Categories in Universal Algebra}

In this section I hope to explore the development of category theory as an application of the Universal Algebra under development in \cite{rbjt039}.

The motivations for this are not very strong.
The greatest of these is my desire now to find a way to explore some possible philosophical applications of category theory.
Why this should favour this particular approach is not obvious.
However, I am working on the Universal Algebra and wanting to probe category theory, so doing the latter in the former makes some sense.

Whether a category is an algebra is moot.
It depends on what you mean by algebra.
Universal algebra normally deals with systems in which there are only total first order operations over a single domain, extended by some theoretical computer scientists (most prominently Goguen) to many sorted algebras.
Typically there is also a presumption that algebra is done in or with a first order equational logic (at least for some purposes, e.g. for the presentation of particular algebras).

In Category theory one of the required operations, composition, is partial, and no particular logical institition is presumed.
For these reasons Category theory may not be thought of as an algebra, but some of the results of our Universal Algebra may nevertheless be applicable, and crucially, the general manner of representing structures used in our Universal Algebra looks suitable for use in Category theory (a category being such a structure).

I propose to begin by replaying some of the former material in a new theory using the Universalm Algebra.

=SML
open_theory "unalg";
force_new_theory "uacat";
force_new_pc ⦏"'uacat"⦎;
merge_pcs ["'prove_∃_⇒_conv", "'savedthm_cs_∃_proof"] "'uacat";
set_merge_pcs ["unalg", "'uacat"];
=TEX

\subsection{Definition of Category}

We model a category by its set of arrows.
It is therefore a set (of arrows), together with:

\begin{itemize}
\item a partial associative operation over the arrows
\item left and right operators which return the domain and codomain of each arrow
\end{itemize}

We will represent categories using objects of type \emph{STRUCT} having a suitable signature.
The signature of a category is defined:

ⓈHOLCONST
│ ⦏CatSig⦎ : SIG
├──────
│ CatSig = IxPack [("⨾⋎c" , 2); ("Left⋎c" , 1); ("Right⋎c" , 1)]
■

=SML
declare_infix (300, "⨾⋎c");
=TEX

We need a convenient notation for categories and therefore define the following constructor:

ⓈHOLCONST
│ ⦏MkCat⦎ : 'a SET → ('a → 'a → 'a) → ('a → 'a) → ('a → 'a) → 'a STRUCT
├──────
│ ∀D $⨾⋎c Left⋎c Right⋎c⦁ MkCat D $⨾⋎c Left⋎c Right⋎c =
│	MkSTRUCT D (IxPack [("⨾⋎c" , pack2op $⨾⋎c); ("Left⋎c" , pack1op Left⋎c); ("Right⋎c" , pack1op Right⋎c)])
■

To enable pattern matching in definitions we prove and install an appropriate existential theorem.

=SML
val MkCat_∃_lemma = make_alg_∃_thm ⌜MkCat⌝;
=TEX

=GFT
⦏MkCat_∃_lemma⦎ =
	⊢ ∀ cf⦁ ∃ f⦁ ∀ D $⨾⋎c Left⋎c Right⋎c⦁
		f (MkCat D ⨾⋎c Left⋎c Right⋎c) = cf D ⨾⋎c Left⋎c Right⋎c
=TEX

=SML
add_∃_cd_thms [MkCat_∃_lemma] "'uacat";
set_merge_pcs ["unalg", "'uacat"];
=TEX


Before giving the definition of a category it will be convenient to define some auxiliary concepts.

\ignore{
=IGN
set_goal([], ⌜∃Obj⦁ ∀D $⨾⋎c Left⋎c Right⋎c a⦁ let C = MkCat D $⨾⋎c Left⋎c Right⋎c in a ∈ Obj C ⇔ a ∈ SCar C ∧ a = Left⋎c a⌝);
a (rewrite_tac [let_def]);
a (prove_∃_tac);

 (pure_once_rewrite_conv [let_def] THEN_C (MAP_C β_conv)) ⌜let C = MkCat D $⨾⋎c Left⋎c Right⋎c in a ∈ Obj C ⇔ a ∈ SCar C ∧ a = Left⋎c a⌝;

=TEX
}%ignore

ⓈHOLCONST
│ ⦏Obj⦎ :  'a STRUCT → 'a SET
├──────
│ ∀D $⨾⋎c Left⋎c Right⋎c a⦁ let C = MkCat D $⨾⋎c Left⋎c Right⋎c in
│	a ∈ Obj C ⇔ a ∈ SCar C ∧ a = Left⋎c a
■

{\let\Section\section
\def\section#1{\Section{#1}\label{TheoryListing}}
\include{cat.th}
}  %\let

\twocolumn[\section{Index}\label{INDEX}]
{\small\printindex}

\end{document}
