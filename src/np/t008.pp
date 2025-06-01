=IGN
$Id: t008.doc,v 1.7 2012/08/11 21:01:53 rbj Exp $
open_theory "fixp-egs";
set_merge_pcs["hol", "'savedthm_cs_∃_proof"];
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\tabstop=0.25in
\usepackage{A4}

\def\Hide#1{\relax}
\newcommand{\ignore}[1]{}

\title{Illustrations of (Co-)Inductive Definitions}
\author{Roger Bishop Jones}
\date{$ $Date: 2012/08/11 21:01:53 $ $}

\usepackage[unicode]{hyperref}

\makeindex
\begin{document}
\vfill
\maketitle
\begin{abstract}
This document provides examples of the use of the facilities provided in t007.doc.
\end{abstract}
\vfill
\begin{centering}

\href{http://www.rbjones.com/rbjpub/pp/doc/t008.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t008.pdf}

$ $Id: t008.doc,v 1.7 2012/08/11 21:01:53 rbj Exp $ $

\bf Copyright \copyright\ : Roger Bishop Jones \\

\end{centering}

\newpage
\tableofcontents
\newpage
%%%%

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\section{INTRODUCTION}

The document follows, as far as is reasonable, the structure of \cite{rbjt007} in providing material illustrating (and testing) the facilities for (co-)inductive definition of sets and types provided in that document.

\subsection{Formalities}

Create new theory ``fixp\_egs''.

=SML
open_theory "fixp";
force_new_theory "fixp-egs";
set_merge_pcs["hol", "'savedthm_cs_∃_proof"];
=IGN
set_flag ("pp_use_alias", false);
set_flag ("pp_show_HOL_types", true);
=TEX

\section{FIXED POINTS}

I probably won't supply any direct examples of this material.
It is used indirectly in all that follows.

\section{INDUCTIVE DEFINITIONS OF SETS}

\subsection{Hereditarily Over a Function}

The example I had in mind which made me think this kind of definition useful is the inductive definition of the theorems of some deductive system.
This belongs here because taking the rules of a deductive system as constructors gives an inductive definition in which the constructor is not one-one.
It also raises a question about inductive definition of functions over the type, since a naive interpretation of the `content' relation would not be well-founded.

Another example would be the definition of recursive function.

These things are easy to do without any special machinery so it might be interesting to try one which has already been done that way, for example my definition of a first order property in \cite{rbjt004}.

=SML
new_parent "membership";
=TEX

The inductive definition is that of {\it fof}.
How would that look if formulated as the fixed point of a function?

ⓈHOLCONST
│ FofCSet: ((STRING, 'a) PPMS SET × (STRING, 'a)PPMS) SET
├──────
│ FofCSet = {(ppmss, ppms1) |
│	ppmss = {} ∧ (∃s1 s2⦁ ppms1 = s1 =⋎p s2 ∨ ppms1 = s1 ∈⋎p s2)
│	∨ (∃p s⦁ ppmss = {p} ∧ ppms1 = (∃⋎p s p) ∨ ppms1 = ¬⋎p p)
│	∨ (∃p1 p2⦁ ppmss = {p1; p2} ∧ ppms1 = p1 ∧⋎p p2)
│	}
■
This is turned into a set of formulae thus:

ⓈHOLCONST
│ Fof: (STRING, 'a)PPMS SET
├──────
│ Fof = HeredFun (Rules2Fun FofCSet)
■

From this we should be able to get an induction principle by instantiating and expanding {\it HeredFun\_induction\_thm2}.

However, this looks quite hard to massage into a nicely formulated induction property.

By comparison coding up the required closure property directly gives:

ⓈHOLCONST
│ FofCProp: (STRING, 'a)PPMS SET → BOOL
├──────
│ ∀ ppmss⦁ FofCProp ppmss ⇔
│	(∀s1 s2⦁ s1 =⋎p s2 ∈ ppmss ∧ s1 ∈⋎p s2 ∈ ppmss)
│	∧ (∀p⦁ p ∈ ppmss ⇒ ¬⋎p p ∈ ppmss ∧ ∀s⦁ (∃⋎p s p) ∈ ppmss)
│	∧ (∀p1 p2⦁ p1 ∈ ppmss ∧ p2 ∈ ppmss ⇒ p1 ∧⋎p p2 ∈ ppmss)
■


ⓈHOLCONST
│ Fof⋎2: (STRING, 'a)PPMS SET
├──────
│ Fof⋎2 = ⋂ {s | FofCProp s}
■

=GFT
fof_induction_thm ⊢ ∀s⦁ FofCProp s ⇒ Fof⋎2 ⊆ s

fof_induction_thm2 ⊢ ∀ s
     ⦁ (∀ s1 s2⦁ s1 =⋎p s2 ∈ s ∧ s1 ∈⋎p s2 ∈ s)
           ∧ (∀ p⦁ p ∈ s ⇒ ¬⋎p p ∈ s ∧ (∀ s'⦁ ∃⋎p s' p ∈ s))
           ∧ (∀ p1 p2⦁ p1 ∈ s ∧ p2 ∈ s ⇒ p1 ∧⋎p p2 ∈ s)
         ⇒ Fof⋎2 ⊆ s
=TEX

\ignore{
=SML
push_pc "hol1";
set_goal([], ⌜∀s⦁ FofCProp s ⇒ Fof⋎2 ⊆ s⌝);
a (rewrite_tac [get_spec ⌜FofCProp⌝, get_spec ⌜Fof⋎2⌝]
	THEN REPEAT strip_tac
	THEN all_asm_ufc_tac[]);
val fof_induction_thm = save_pop_thm "fof_induction_thm";
pop_pc();
val fof_induction_thm2 = save_thm ("fof_induction_thm2",
	rewrite_rule [get_spec ⌜FofCProp⌝] fof_induction_thm);
=TEX
}%ignore

=IGN
rewrite_rule [get_spec ⌜Rules2Fun⌝, get_spec ⌜FofCSet⌝, sets_ext_clauses]
(rewrite_rule [eq_sym_rule (get_spec ⌜Fof⌝)]
	(∀_elim ⌜Rules2Fun FofCSet⌝ HeredFun_induction_thm2));
,
	rewrite_conv [get_spec ⌜Rules2Fun⌝, get_spec ⌜FofCSet⌝]
	]

eq_sym_rule (get_spec ⌜Fof⌝);

set_goal([], ⌜∀s⦁ s ClosedUnderFun (Rules2Fun FofCSet) ⇒ Fof ⊆ s⌝);
a (rewrite_tac [get_spec ⌜Fof⌝, HeredFun_induction_thm2]);
val lemma1= top_thm();

rewrite_rule ((map get_spec [⌜FofCSet⌝, ⌜Rules2Fun⌝, ⌜$ClosedUnderFun⌝,
	⌜$ClosedUnder⌝, ⌜Fun2MonoFun⌝])@[sets_ext_clauses]) lemma1; 
∀_elime sets_ext_clauses;
list_∀_elim ⌜Rules2Fun FofCSet⌝ HeredFun_induction_thm;
=TEX

\subsection{Hereditarily Over a Relation}

\subsection{Hereditarily Over a Property}

\section{INDUCTIVE DEFINITIONS OF SETS}

The examples here are examples which do not use the machinery for generating constructor functions.

\subsection{Sets Defined Using CCP's}

\subsubsection{Hereditarily Pure Functions}

\subsubsection{Hereditarily Pure Functors and Categories}

\section{CODING CONSTRUCTIONS}

\subsection{HOL Types and Terms}

Here is a simple type description to work from, the types and terms of HOL:
Note that for each constructor is supplied the type of the constructor and a predicate over the domain of the constructor.
In this example the predicates enforce constraints on the names of constants and variables requiring that names beginning with ' are variable names.

The type variables $'TYPE$ and $'TERM$ give the names of the sets or types which are being defined.

=SML
val constructor_types = [
	(⌜MkVarType: STRING → 'TYPE⌝,
				⌜λx:STRING⦁ Hd x = '''⌝),
	(⌜MkCType: STRING → 'TYPE LIST →'TYPE⌝,
				⌜λ(x:STRING, y:'TYPE LIST)⦁ ¬ Hd x = '''⌝),
	(⌜MkVarTerm: STRING → 'TYPE →'TERM⌝,
				⌜λ(x:STRING, y:'TYPE)⦁ Hd x = '''⌝),
	(⌜MkCTerm: STRING → 'TYPE →'TERM⌝,
				⌜λ(x:STRING, y:'TYPE)⦁ ¬ Hd x = '''⌝),
	(⌜MkLamTerm: STRING → 'TYPE → 'TERM → 'TERM⌝,
				⌜λ(x:STRING, y:'TYPE, z:'TERM)⦁ Hd x = '''⌝),
	(⌜MkAppTerm: 'TERM → 'TERM → 'TERM⌝,
				⌜λ(x:'TERM, y:'TERM)⦁ T⌝)
];
=TEX

This system of type specifications can be translated into an expression for a fixedpoint as follows:
=SML
set_flag ("pp_use_alias", true);
declare_ctk_aliases ntree_ctk ctk_aliases;
val fixp_expression = translate_sig ntree_ctk constructor_types;
undeclare_ctk_aliases ntree_ctk ctk_aliases;
fixp_expression;
=TEX

Which yields:
=GFT
val fixp_expression =
   ⌜Θ
     [[Ξ (φ γ) (φ ρ) (λ x⦁ Head x = ''');
           Ξ (φ γ × φ I) (φ ρ × φ (ω 1)) (λ (x, y)⦁ ¬ Head x = ''')];
         [Ξ (φ γ × I) (φ ρ × ω 1) (λ (x, y)⦁ Head x = ''');
             Ξ (φ γ × I) (φ ρ × ω 1) (λ (x, y)⦁ ¬ Head x = ''');
             Ξ (φ γ × I × I) (φ ρ × ω 1 × ω 2) (λ (x, y, z)⦁ Head x = ''');
             Ξ (I × I) (ω 2 × ω 2) (λ (x, y)⦁ T)]]⌝ : TERM

=TEX
Without the aliases that is:
=GFT
val fixp_expression =
   ⌜FR
     [[CR (NTreeeMkList MkLeafTreee) (NTrListC NTrLeafC) (λ x⦁ Head x = ''');
           CR
               (NTreeeMkProd (NTreeeMkList MkLeafTreee) (NTreeeMkList I))
               (NTrProdC (NTrListC NTrLeafC) (NTrListC (NTreeeTagC 1)))
               (λ (x, y)⦁ ¬ Head x = ''')];
         [CR
               (NTreeeMkProd (NTreeeMkList MkLeafTreee) I)
               (NTrProdC (NTrListC NTrLeafC) (NTreeeTagC 1))
               (λ (x, y)⦁ Head x = ''');
             CR
                 (NTreeeMkProd (NTreeeMkList MkLeafTreee) I)
                 (NTrProdC (NTrListC NTrLeafC) (NTreeeTagC 1))
                 (λ (x, y)⦁ ¬ Head x = ''');
             CR
                 (NTreeeMkProd (NTreeeMkList MkLeafTreee) (NTreeeMkProd I I))
                 (NTrProdC
                     (NTrListC NTrLeafC)
                     (NTrProdC (NTreeeTagC 1) (NTreeeTagC 2)))
                 (λ (x, y, z)⦁ Head x = ''');
             CR
                 (NTreeeMkProd I I)
                 (NTrProdC (NTreeeTagC 2) (NTreeeTagC 2))
                 (λ (x, y)⦁ T)]]⌝
: TERM
=TEX
which has type:

=SML
type_of fixp_expression;
=GFT
val it = ⓣ(ℕ, CHAR) TREEE SET⌝ : TYPE
=TEX

This set contains the representatives of each type discriminated by tags, so to recover the two sets we need to filter the one as follows:

=SML
declare_ctk_aliases ntree_ctk ctk_aliases;
val type_rep = ⌜{x | ∃y⦁ y ∈ ⓜfixp_expression⌝ ∧ IsTag 1 y ∧ x = UnTag y}⌝;
=GFT
val term_rep =
   ⌜{x
   |∃ y
     ⦁ y
           ∈ Θ
             [[Ξ (φ ρ) (φ ρ) (λ x⦁ Head x = ''');
                   Ξ (φ ρ × φ I) (φ ρ × φ (ω 1)) (λ (x, y)⦁ ¬ Head x = ''')];
                 [Ξ (φ ρ × I) (φ ρ × ω 1) (λ (x, y)⦁ Head x = ''');
                     Ξ (φ ρ × I) (φ ρ × ω 1) (λ (x, y)⦁ ¬ Head x = ''');
                     Ξ
                         (φ ρ × I × I)
                         (φ ρ × ω 1 × ω 2)
                         (λ (x, y, z)⦁ Head x = ''');
                     Ξ (I × I) (ω 2 × ω 2) (λ (x, y)⦁ T)]]
         ∧ IsTag 2 y
         ∧ x = UnTag y}⌝ : TERM
=SML
val term_rep = ⌜{x | ∃y⦁ y ∈ ⓜfixp_expression⌝ ∧ IsTag 2 y ∧ x = UnTag y}⌝;
=GFT
val term_rep =
   ⌜{x
   |∃ y
     ⦁ y
           ∈ Θ
             [[Ξ (φ ρ) (φ ρ) (λ x⦁ Head x = ''');
                   Ξ (φ ρ × φ I) (φ ρ × φ (ω 1)) (λ (x, y)⦁ ¬ Head x = ''')];
                 [Ξ (φ ρ × I) (φ ρ × ω 1) (λ (x, y)⦁ Head x = ''');
                     Ξ (φ ρ × I) (φ ρ × ω 1) (λ (x, y)⦁ ¬ Head x = ''');
                     Ξ
                         (φ ρ × I × I)
                         (φ ρ × ω 1 × ω 2)
                         (λ (x, y, z)⦁ Head x = ''');
                     Ξ (I × I) (ω 2 × ω 2) (λ (x, y)⦁ T)]]
         ∧ IsTag 2 y
         ∧ x = UnTag y}⌝ : TERM
=TEX

Let's check this out by trying a proof that the set of types is non-empty.

=SML
set_goal ([], ⌜∃t⦁ t ∈ ⓜtype_rep⌝⌝);
a (rewrite_tac (map get_spec [⌜Θ⌝, ⌜Ξ⌝, ⌜NTrProdC⌝, ⌜NTreeeMkProd⌝]));
=TEX

\section{MAKING NEW TYPES}

Here are some examples I would like to be able to handle.

\begin{description}
\item[algebras] e.g. a type of groups, these are essentially subtypes of labelled product types in which the projections yield objects conforming to the signature of the relevant algebra.  This is therefore a special case of the general inductive datatypes problem (if an implementation of that allowed predicates).
\item[types from algebras] e.g. given a type of groups, make a type out of a presentation of a particular group.
\item[from hereditatily sets]
e.g. a type of hereditarily pure functions, or a pair of types for the pure concrete categories and functors.
\end{description}


{\let\Section\section
\def\section#1{\Section{#1}\label{TheoryListing}}
\include{fixp-egs.th}
}  %\let

\twocolumn[\section{INDEX}\label{INDEX}]
{\small\printindex}

\end{document}
=SML
set_flag ("pp_use_alias", true);
output_theory{out_file="fixp-egs.th.doc", theory="fixp-egs"};
set_flag ("pp_use_alias", false);
=TEX
