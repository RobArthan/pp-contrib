=IGN
open_theory "infos";
set_flag ("pp_use_alias", true);
set_merge_pcs ["misc21", "'holw"];
=TEX

\def\rbjidtADBdoc{$$Id: t031.doc,v 1.3 2009/10/05 09:18:19 rbj Exp $$}

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

\title{Pure Type Systems and HOL-Omega in ProofPower}
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
The abstract syntax and semantics of Pure Type Systems and HOL-Omega in a formal higher-order theory of well-founded sets.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created: 2009/8/31

Last Change $ $Date: 2009/10/05 09:18:19 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t031.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t031.pdf}

$ $Id: t031.doc,v 1.3 2009/10/05 09:18:19 rbj Exp $ $

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
\section{Introduction}

This document was started after discussions with Peter Homeier at a workshop on Interactive Theorem Proving in 2009.
It is intended for explorations into the formalisation of the semantics of Pure Type Systems and of Hol-Omega \cite{homeier2009} using a well-founded theory of well-founded sets \cite{rbjt023}.

The connections betweem the Pure Type Systems and HOL-Omega are very tenuous indeed.
For me they are both examples of systems which in some way or to some extent seek to mitigate the problems which arise in trying to work formally with a well-founded ontology.

This can be done either by dropping the constraint to a well-founded ontology, or by adopting various pragmatic paliatives.
The Pure Type Systems include systems which have no well-founded semantics, notably Coquand's Calculus of Constructions.
For this reason they are worth study to increase one's armoury of methods for constructing consistent logical systems without the draconian constraint to well-foundedness.
HOL-Omega on the other hand, represents one of the many different ways of mitigating the problems arising from well-foundedness without actually disposing of it. 
HOL is itself such a system, its polymorphism probably representing the least one can do in the object language.
Though HOL's polymorphism is of the very simplest kind, it is very effective.
It is hard to improve upon and attempts to improve on it usually yield much more complex logical systems whose merits in the respects we consider are not beyond debate.
HOL-Omega is such a system.

It may be worth mentioning what are the principle problems which this kind of development is intended to address.
For me, they relate to formalisation ``in tha large'', i.e. in support for abstraction, modularity and reuse of specifications and proofs.
The formalisation of abstract theories, notably of category theory, is also, whether or not thought of in the context of modularity, a test for this kind of foundational development.

The attempt to deal with these problems by foundational innovation is itself controversial.
This is primarily I think because of the difficulties involved, the risk of ending up with a system which provides poor support for mainstream mathematics (such as analysis) done in the established manner, and because these matters can be addressed without resort to foundational innovations (and are usually addressed in such ways).

My own interest has primarily been in the foundational route, no doubt because I just like thinking about this problem.
But I have also an interest in approaches, at least to the `specification in the large' side of things, which are foundationally neutral, and allow interworking between logical systems.

So far as this document is concerned, it has so far gone nowhere, for I quickly realised (though not until after I had started the document) that the higher order theory of well-founded sets which I had intended to use for the purpose \cite{rbjt023} fell short of the demands I would put upon it and would have to be upgraded.
So that is where movement is taking place at present.

\section{Pure Type Systems}


\section{HOL-Omega}

=SML
open_theory "misc2";
force_new_theory "⦏holw⦎";
force_new_pc ⦏"'holw"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'holw";
set_merge_pcs ["misc21", "'holw"];
=TEX

\section{Syntax}

The formalisation of the syntax has no particular interest.
It is essentially the definition of a recursive datatype.
If our proof tool supported datatype definitions then I would have used them, since it does not the easiest way to get the required dayatype is by using set theory.
Note however, that I do not necessarily need to make a new type, and will only prove those theorems which I actually need.

The manual construction of the three mutually recursive datatypes in our higher order set theory is done by defining the constructors and taking the intersection of all sets closed under the constructors.

\subsection{Constructors and Discriminators}

\subsubsection{Kinds}

ⓈHOLCONST
│ ⦏MkKindTy⦎ : GS → GS
├───────────
│ ∀t⦁ MkKindTy t = (Nat⋎g 0) ↦⋎g t
■

ⓈHOLCONST
│ ⦏IsKindTy⦎ : GS → BOOL
├───────────
│    ∀k⦁ IsKindTy k ⇔ ∃t⦁ k = MkKindTy t
■

ⓈHOLCONST
│ ⦏MkKindVar⦎ : GS → GS
├───────────
│ ∀n⦁ MkKindVar n = (Nat⋎g 1) ↦⋎g n
■

ⓈHOLCONST
│ ⦏IsKindVar⦎ : GS → BOOL
├───────────
│    ∀k⦁ IsKindVar k ⇔ ∃n⦁ k = MkKindVar n
■

ⓈHOLCONST
│ ⦏MkKindArr⦎ : GS × GS → GS
├───────────
│ ∀lr⦁ MkKindArr lr = (Nat⋎g 2) ↦⋎g (MkPair⋎g lr)
■

ⓈHOLCONST
│ ⦏IsKindArr⦎ : GS → BOOL
├───────────
│    ∀k⦁ IsKindArr k ⇔ ∃t⦁ k = MkKindArr t
■

ⓈHOLCONST
│ ⦏IsKind⦎ : GS → BOOL
├───────────
│    ∀k⦁ IsKind k ⇔ IsKindTy k ∨ IsKindVar k ∨ IsKindArr k
■

\subsubsection{Types}

ⓈHOLCONST
│ ⦏MkTypeVar⦎ : GS × GS × GS → GS
├───────────
│ ∀nkr⦁ MkTypeVar nkr = (Nat⋎g 3) ↦⋎g (MkTriple⋎g nkr)
■

ⓈHOLCONST
│ ⦏IsTypeVar⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsTypeVar t ⇔ ∃p⦁ t = MkTypeVar p
■

ⓈHOLCONST
│ ⦏MkTypeCon⦎ : GS × GS × GS → GS
├───────────
│ ∀nkr⦁ MkTypeCon nkr = (Nat⋎g 4) ↦⋎g (MkTriple⋎g nkr)
■

ⓈHOLCONST
│ ⦏IsTypeCon⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsTypeCon t ⇔ ∃p⦁ t = MkTypeCon p
■

ⓈHOLCONST
│ ⦏MkTypeApp⦎ : GS × GS → GS
├───────────
│ ∀fa⦁ MkTypeApp fa = (Nat⋎g 5) ↦⋎g (MkPair⋎g fa)
■

ⓈHOLCONST
│ ⦏IsTypeApp⦎ : GS → BOOL
├───────────
│    ∀a⦁ IsTypeApp a ⇔ ∃p⦁ a = MkTypeApp p
■

ⓈHOLCONST
│ ⦏MkTypeAbs⦎ : GS × GS → GS
├───────────
│ ∀vb⦁ MkTypeAbs vb = (Nat⋎g 6) ↦⋎g (MkPair⋎g vb)
■

ⓈHOLCONST
│ ⦏IsTypeAbs⦎ : GS → BOOL
├───────────
│    ∀a⦁ IsTypeAbs a ⇔ ∃p⦁ a = MkTypeAbs p
■

ⓈHOLCONST
│ ⦏MkTypeUniv⦎ : GS × GS → GS
├───────────
│ ∀vb⦁ MkTypeUniv vb = (Nat⋎g 7) ↦⋎g (MkPair⋎g vb)
■

ⓈHOLCONST
│ ⦏IsTypeUniv⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsTypeUniv t ⇔ ∃p⦁ t = MkTypeUniv p
■

ⓈHOLCONST
│ ⦏IsType⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsType t ⇔ IsTypeVar t ∨ IsTypeCon t ∨ IsTypeApp t ∨ IsTypeAbs t ∨ IsTypeUniv t
■

\subsubsection{Terms}

ⓈHOLCONST
│ ⦏MkTermVar⦎ : GS × GS → GS
├───────────
│ ∀nt⦁ MkTermVar nt = (Nat⋎g 8) ↦⋎g (MkPair⋎g nt)
■

ⓈHOLCONST
│ ⦏IsTermVar⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsTermVar t ⇔ ∃p⦁ t = MkTermVar p
■

ⓈHOLCONST
│ ⦏MkTermCon⦎ : GS × GS → GS
├───────────
│ ∀nt⦁ MkTermCon nt = (Nat⋎g 9) ↦⋎g (MkPair⋎g nt)
■

ⓈHOLCONST
│ ⦏IsTermCon⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsTermCon t ⇔ ∃p⦁ t = MkTermCon p
■

ⓈHOLCONST
│ ⦏MkTermApp⦎ : GS × GS → GS
├───────────
│ ∀fa⦁ MkTermApp fa = (Nat⋎g 10) ↦⋎g (MkPair⋎g fa)
■

ⓈHOLCONST
│ ⦏IsTermApp⦎ : GS → BOOL
├───────────
│    ∀a⦁ IsTermApp a ⇔ ∃p⦁ a = MkTermApp p
■

ⓈHOLCONST
│ ⦏MkTermAbs⦎ : GS × GS → GS
├───────────
│ ∀vb⦁ MkTermAbs vb = (Nat⋎g 11) ↦⋎g (MkPair⋎g vb)
■

ⓈHOLCONST
│ ⦏IsTermAbs⦎ : GS → BOOL
├───────────
│    ∀a⦁ IsTermAbs a ⇔ ∃p⦁ a = MkTermAbs p
■

ⓈHOLCONST
│ ⦏MkTermAppType⦎ : GS × GS → GS
├───────────
│ ∀fa⦁ MkTermAppType fa = (Nat⋎g 12) ↦⋎g (MkPair⋎g fa)
■

ⓈHOLCONST
│ ⦏IsTermAppType⦎ : GS → BOOL
├───────────
│    ∀a⦁ IsTermAppType a ⇔ ∃p⦁ a = MkTermAppType p
■

ⓈHOLCONST
│ ⦏MkTermAbsType⦎ : GS × GS → GS
├───────────
│ ∀vb⦁ MkTermAbsType vb = (Nat⋎g 13) ↦⋎g (MkPair⋎g vb)
■

ⓈHOLCONST
│ ⦏IsTermAbsType⦎ : GS → BOOL
├───────────
│    ∀a⦁ IsTermAbsType a ⇔ ∃p⦁ a = MkTermAbsType p
■

ⓈHOLCONST
│ ⦏IsTerm⦎ : GS → BOOL
├───────────
│    ∀t⦁ IsTerm t ⇔ IsTermVar t ∨ IsTermCon t ∨ IsTermApp t ∨ IsTermAbs t ∨ IsTermAppType t ∨ IsTermAbsType t
■

\ignore{
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

=IGN
set_flag("subgoal_package_quiet", true);
=IGN

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

\subsection{The Inductive Definition of Syntax}

This is accomplished by defining the required closure condition (closure under the above constructors for arguments of the right kind) and then taking the intersection of all sets which satisfy the closure condition.

The closure condition is:

ⓈHOLCONST
│ ⦏HolwSynClosed⦎: GS SET → BOOL
├───────────
│ ∀ s⦁ HolwSynClosed s ⇔
│	(∀t⦁ t ∈ s ∧ IsType t ⇒
│		MkKindTy t ∈ s)
│∧	(∀p⦁ 	MkKindVar p ∈ s)
│∧	(∀k1 k2⦁ k1 ∈ s ∧ k2 ∈ s ∧ IsKind k1 ∧ IsKind k2 ⇒
│		MkKindArr (k1, k2) ∈ s)
│∧	(∀n k r⦁ k ∈ s ∧ IsKind k ⇒
│ 		MkTypeVar (Nat⋎g n, k, Nat⋎g r) ∈ s)
│∧	(∀n k r⦁ k ∈ s ∧ IsKind k ⇒
│		MkTypeCon (Nat⋎g n, k, Nat⋎g r) ∈ s)
│∧	(∀f a⦁ f ∈ s ∧ a ∈ s ∧ IsType f ∧ IsType a ⇒
│		MkTypeApp (f, a) ∈ s)
│∧	(∀v b⦁ v ∈ s ∧ b ∈ s ∧ IsTypeVar v ∧ IsType b ⇒
│		MkTypeAbs (v, b) ∈ s)
│∧	(∀v b⦁ v ∈ s ∧ b ∈ s ∧ IsTypeVar v ∧ IsType b ⇒
│		MkTypeUniv (v, b) ∈ s)
│∧	(∀n t⦁ t ∈ s ∧ IsType t ⇒
│ 		MkTermVar (Nat⋎g n, t) ∈ s)
│∧	(∀n t⦁ t ∈ s ∧ IsType t ⇒
│		MkTermCon (Nat⋎g n, t) ∈ s)
│∧	(∀f a⦁ f ∈ s ∧ a ∈ s ∧ IsTerm f ∧ IsTerm a ⇒
│		MkTermApp (f, a) ∈ s)
│∧	(∀v b⦁ v ∈ s ∧ b ∈ s ∧ IsTermVar v ∧ IsTerm b ⇒
│		MkTermAbs (v, b) ∈ s)
│∧	(∀f a⦁ f ∈ s ∧ a ∈ s ∧ IsTerm f ∧ IsType a ⇒
│		MkTermAppType (f, a) ∈ s)
│∧	(∀v b⦁ v ∈ s ∧ b ∈ s ∧ IsTypeVar v ∧ IsTerm b ⇒
│		MkTermAbsType (v, b) ∈ s)
■

The well-formed syntax is then the smallest set closed under these constructions (which might be a ``class'').

ⓈHOLCONST
│ ⦏HolwSyntax⦎ : GS SET
├───────────
│ HolwSyntax = ⋂{x | HolwSynClosed x}
■

\section{Proof Contexts}

=SML
(* add_pc_thms "'holw" []; *)

(* add_pc_thms "'holw" []; *)
commit_pc "'holw";

force_new_pc "⦏holw⦎";
merge_pcs ["misc2", "'holw"] "holw";
commit_pc "holw";

force_new_pc "⦏holw1⦎";
merge_pcs ["misc21", "'holw"] "holw1";
commit_pc "holw1";
=TEX

=SML
set_flag ("subgoal_package_quiet", false);
=TEX

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{holw.th}
%\include{sfp.th}
}  %\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
