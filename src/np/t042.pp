=IGN
$Id: t042.doc,v 1.8 2013/01/03 17:12:44 rbj Exp $
open_theory "'a GSU";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-ord", "'savedthm_cs_∃_proof"];
set_merge_pcs ["hol", "'wf_relp", "'wf_recp", "'GSU1", "'savedthm_cs_∃_proof"];
set_merge_pcs ["hol1", "'gsu-ax", "'gsu-ord", "'savedthm_cs_∃_proof"];
=TEX
\documentclass[11pt,a4paper]{article}
%\usepackage{latexsym}
%\usepackage{ProofPower}
\usepackage{rbj}
\ftlinepenalty=9999
\usepackage{A4}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}
\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{A Higher Order Theory of Well-Founded Sets (with Urelements)}
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
This is a modification of the pure set theory GS to admit urelements.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2010/10/08

Last Change $ $Date: 2013/01/03 17:12:44 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t042.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t042.pdf}

$ $Id: t042.doc,v 1.8 2013/01/03 17:12:44 rbj Exp $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize

\end{centering}

\thispagestyle{empty}
\end{titlepage}
\newpage
\addtocounter{page}{1}
{\parskip=0pt\tableofcontents}

\newpage

\section{Introduction}

Since this is a modification of a previous formalisation of higher order set theory \cite{rbjt023}, I omit the preminary discussions for which the reader may refer to the previous document, and confine this introduction to the modifications which I have made in this version.

This is simply the admission of urelements of arbitrary type, so that we introduce here instead of a simple type, a type constructor, which will be called `'a GSU'.
=SML
open_theory "rbjmisc";
force_new_theory "⦏gsu-ax⦎";
new_parent "U_orders";
new_parent "wf_relp";
new_parent "wf_recp";
force_new_pc "⦏'gsu-ax⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];
new_type ("⦏GSU⦎", 1);
=TEX

\subsection{Urelements}

The novelty is urelements.
Since the theory is not conservative over plain HOL, it must be introduced using axioms.

The axiom which introduces the urelements asserts that there is an injection from type ⓣ'a⌝ into type ⓣ'a GSU⌝.

=SML
val Urelement_Axiom = new_axiom(["Urelement_Axiom"], ⌜∃f:'a → 'a GSU⦁ OneOne f⌝);
=TEX

Having asserted the existence of such an injection we now introduce a constant with that characteristic:

\ignore{
=SML
set_goal([], ⌜∃Urelement:'a → 'a GSU⦁ OneOne Urelement⌝);
a (strip_asm_tac Urelement_Axiom);
a (∃_tac ⌜f⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Urelement⦎ : 'a → 'a GSU
├─────────
│ OneOne Urelement
■

The range of this injection is the extension of the set of urelements, but we can't say this until we have introduced membership.

ⓈHOLCONST
│ ⦏UeVal⦎ : 'a GSU → 'a
├─────────
│ ∀x⦁ UeVal x = εy⦁ Urelement y = x 
■

=GFT
⦏UeVal_Urelement_lemma⦎ = ⊢ ∀ x⦁ UeVal (Urelement x) = x
=TEX

\ignore{
=SML
val Urelement_def = get_spec ⌜Urelement⌝;
val UeVal_def = get_spec ⌜UeVal⌝;

set_goal([], ⌜∀x⦁ UeVal (Urelement x) = x⌝);
a (rewrite_tac [UeVal_def] THEN ∀_tac);
a (ε_tac ⌜ε y⦁ Urelement y = Urelement x⌝);
(* *** Goal "1" *** *)
a (∃_tac ⌜x⌝ THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [rewrite_rule [get_spec ⌜OneOne⌝] Urelement_def]);
val UeVal_Urelement_lemma = pop_thm ();
=TEX
}%ignore

I will use the term $Set⋎u$ exclusively for bona-fide sets, i.e. values outside the range of this function.

The following predicate is true just of the urelements.

ⓈHOLCONST
│ ⦏Ue⦎ : 'a GSU → BOOL
├─────────
│ ∀x⦁ Ue x ⇔ ∃y⦁ x = Urelement y
■

=GFT
⦏Urelement_Ue_lemma⦎ = ⊢ ∀ x⦁ Ue x ⇒ Urelement (UeVal x) = x
=TEX

\ignore{
=SML
val Ue_def = get_spec ⌜Ue⌝;

set_goal([], ⌜∀x⦁ Ue x ⇒ Urelement (UeVal x) = x⌝);
a (strip_tac THEN rewrite_tac[Ue_def] THEN REPEAT strip_tac
	THEN asm_rewrite_tac[UeVal_Urelement_lemma]);
val Urelement_Ue_lemma = pop_thm();
=TEX
}%ignore

And this one of sets.

ⓈHOLCONST
│ ⦏Set⋎u⦎ : 'a GSU → BOOL
├─────────
│ ∀x⦁ Set⋎u x ⇔ ¬ ∃y⦁ x = Urelement y
■

=GFT
⦏UeSet⋎u_lemma1⦎ = ⊢ ∀x⦁ Ue x ⇔ ¬ Set⋎u x
⦏Urelement_Ue_lemma2⦎ = ⊢ ∀ x⦁ ¬ Set⋎u x ⇒ Urelement (UeVal x) = x
=TEX

\ignore{
=SML
val Ue_def = get_spec ⌜Ue⌝;
val Set⋎u_def = get_spec ⌜Set⋎u⌝;

set_goal([], ⌜∀x⦁ Ue x ⇔ ¬ Set⋎u x⌝);
a (rewrite_tac [Ue_def, Set⋎u_def] THEN prove_tac[]);
val UeSet⋎u_lemma1 = save_pop_thm "UeSet⋎u_lemma1";

val Urelement_Ue_lemma2 = rewrite_rule [UeSet⋎u_lemma1] Urelement_Ue_lemma;

add_pc_thms "'gsu-ax" [UeVal_Urelement_lemma, UeSet⋎u_lemma1];
set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore


\subsection{Membership}

Membership is a relation over the type.
We can't define this constant (in this context) so it is introduced as a new constant (about which nothing is asserted except its name and type) and its properties are introduced axiomatically. 

=SML
new_const ("⦏∈⋎u⦎", ⓣ'a GSU → 'a GSU → BOOL⌝);
declare_infix (230,"∈⋎u");
=TEX

Since we have urelements, which are not bona-fide sets, it will be convenient to insist that only sets have members:

=SML
val Set⋎u_axiom = new_axiom (["Set⋎u_axiom"], ⌜∀x y⦁ x ∈⋎u y ⇒ Set⋎u y⌝);
=TEX

I will possibly be making use of two different treatments of well-foundedness (from the theories {\it U\_orders}, and {\it wf\_relp}) and it may be helpful to establish the connection between them.

The following theorem does the trick:

=GFT
⦏UWellFounded_well_founded_thm⦎ =
	⊢ ∀ $<<⦁ UWellFounded $<< ⇔ well_founded $<<
=TEX

\ignore{
=SML
set_goal ([], ⌜∀$<<⦁ UWellFounded $<< ⇔ well_founded $<<⌝);
a (rewrite_tac [get_spec ⌜well_founded⌝, u_well_founded_induction_thm]);
val UWellFounded_well_founded_thm = save_pop_thm "UWellFounded_well_founded_thm";
=TEX
}%ignore

The axioms of extensionality and well-foundedness may be thought of as telling us what kind of thing a set is (later axioms tell us which sets are to be found in our domain of discourse).

This is a principle point of departure from the theory without urelements.
Here I have to chose between preserving extensionality (which can by done using Quine's trick of identifying a urelement with its unit set), or preserving well-foundedness of the membership relation (by insisting that urelements have no members).%
\footnote{I could also fudge it by saying nothing about the membership of urelements, but that seems the least attractive option since both extensionality and well-foundedness would have to be qualified.}

When I first addressed this issue, I was mistakenly under the impression that this was just a question of an aribitrary choice of what to say about the membership of urelements, and under this illusion I tried having two different membership relations one well-founded and the other extensional.
One could have two different membership relations which differed only what the members of the urelements are, but the adoption of the unqualified axiom of extensionality (which is the point of Quine's trick) is nevertheless substantive, for otherwise, even though a urelement would be its own sole member, it would nevertheless be distinct from its own unit set and extensionality would fail.
It therefore seems that an unqualified extensionality is incompatible with the closure of the universe under the formation of unit \emph{set}s, for if Quine's trick is used to admit extensionality, the ``unit set'' of a urelement will not be a set at all (or else the urelement is also a set).

This consideration persuaded me against urelements being unit sets, and I will therefore have to put up with extensionality being conditional.

\subsubsection{Extensionality}

The most fundamental property of membership (or is it of sets?) is {\it extensionality}, which tells us what kind of thing a set is.
The axiom tells us that if two sets have the same elements then they are in fact the same set.

=SML
val ⦏gsu_ext_axiom⦎ = new_axiom (["gsu_ext_axiom"],
	⌜∀s t:'a GSU⦁  Set⋎u s ∧ Set⋎u t ⇒ (s = t ⇔ ∀e⦁ e ∈⋎u s ⇔ e ∈⋎u t)⌝);
=TEX

This may be thought of as extensionality of sets themselves or as extensionality of equality over sets.
Though sets are extensional, we do not have an unconditionally extensional equality over the domain of discourse, because we have urelements.

=GFT
⦏gsu_ext_thm⦎ =
	⊢ ∀ s t⦁ Set⋎u s ⇒ Set⋎u t ⇒ (s = t ⇔ (∀ e⦁ e ∈⋎u s ⇔ e ∈⋎u t))
=TEX

\ignore{
=SML
val gsu_ext_thm = save_thm ("gsu_ext_thm",
	rewrite_rule [prove_rule [] ⌜∀A B C⦁ A ∧ B ⇒ C ⇔ A ⇒ B ⇒ C⌝] gsu_ext_axiom);
=TEX
}%ignore

The following (rather crude) conversion is useful in the application of extensionality:

=SML
fun ⦏gsu_ext_conv⦎ tm =
	let fun aux thms =
		let val (lhs, rhs) = dest_eq tm;
		    val extax_thm = list_∀_elim [lhs, rhs] gsu_ext_thm;
		    val [ant1, ant2, con] = strip_⇒ (concl extax_thm);
		    val a1thm1 = conv_rule (LEFT_C (TRY_C (rewrite_conv thms))) (disch_rule ant1 (asm_rule ant1));
		    val a2thm1 = conv_rule (LEFT_C (TRY_C (rewrite_conv thms))) (disch_rule ant2 (asm_rule ant2));
		    val a1thm2 = try (fn x => ⇒_elim x t_thm) a1thm1;
		    val a2thm2 = try (fn x => ⇒_elim x t_thm) a2thm1;
		    val a1thm3 = try undisch_rule a1thm2;
		    val a2thm3 = try undisch_rule a2thm2;
		    val con_thm1 = ⇒_elim extax_thm a1thm3
		    val con_thm2 = ⇒_elim con_thm1 a2thm3
		in pure_rewrite_conv [con_thm2] tm
		end
	in aux []
	end handle _ => fail_conv tm;
=TEX

The corresponding rule and tactics are:
=SML
val ⦏gsu_ext_rule⦎ = conv_rule gsu_ext_conv;
val ⦏gsu_ext_tac⦎ = conv_tac gsu_ext_conv;
=TEX

Those only work for equations at the top level, the following tactic is provided for equations lower down.
It expects to be supplied the term to which it will be applied.

=SML
val ⦏gsu_ext_tac2⦎ = fn tm => rewrite_tac [gsu_ext_conv tm];
=TEX

For facility of reasoning in this theory it is best if as few theorems as possible are conditional upon whether the variables in them have values which are sets rather than urelements.
This is achieved firstly by having no members for urelements (which are therefore extensionally equivalent to the empty set).
Because of this it is important in introducing new operations which are intended to deliver sets that the result is not specified purely by extension, it is important that the result be known to be a set rather than an urelement even when its extension is empty.
We also ensure that all operators over sets are extensional, i.e. the result depends only upon the extension of the arguments, not upon anything else (the only other thing it could depend on would be whether the arguments are sets or urelements).
It would be natural for example to make the Subset relation false if either operand was a urelement, but this would lengthen proofs.

It follows from the definitions of {\it Urelement}, {\it Ue} and $Set⋎u$ that nothing is both a set and a urelement, and that urelements are equal iff the values from which they were obtained under \emph{Ue} are equal.

It is convenient to have a function which gives the extension of a $'a GSU$ set as a SET of $'a GSU$s.

ⓈHOLCONST
│ ⦏X⋎u⦎ : 'a GSU → 'a GSU SET
├─────────
│ ∀s⦁ X⋎u s = {t | t ∈⋎u s}
■

Since equality is not strictly extensional, it is useful to define an extensional equality (equivalence).

=SML
declare_infix(200, "=⋎u");
=TEX

ⓈHOLCONST
│$ ⦏=⋎u⦎ : 'a GSU → 'a GSU  → BOOL
├─────────
│ ∀s t⦁ s =⋎u t ⇔ X⋎u s = X⋎u t
■

=GFT
⦏X⋎u_thm⦎ =	⊢ ∀ s t⦁ s ∈ X⋎u t = s ∈⋎u t
⦏eq⋎u_refl_thm⦎ =	⊢ ∀ s⦁ s =⋎u s
⦏eq⋎u_sym_thm⦎ =	⊢ ∀ s t⦁ s =⋎u t ⇒ t =⋎u s
⦏eq⋎u_trans_thm⦎ =	⊢ ∀ s t u⦁ s =⋎u t ∧ t =⋎u u ⇒ t =⋎u u
⦏eq⋎u_ext_thm⦎ =	⊢ ∀ s t⦁ s =⋎u t ⇔ (∀ u⦁ u ∈⋎u s ⇔ u ∈⋎u t)
⦏¬eq⋎u_¬eq_thm⦎ =	⊢ ∀ s t⦁ ¬ s =⋎u t ⇒ ¬ s = t
=TEX

\ignore{
=SML
val X⋎u_def = get_spec ⌜X⋎u⌝;
val eq⋎u_def = get_spec ⌜$=⋎u⌝;

set_goal([], ⌜∀s t⦁ s ∈ X⋎u t ⇔ s ∈⋎u t⌝);
a (REPEAT ∀_tac THEN PC_T1 "hol1" rewrite_tac [eq⋎u_def, X⋎u_def] THEN prove_tac[]);
val X⋎u_thm = save_pop_thm "X⋎u_thm";

set_goal([], ⌜∀s⦁ s =⋎u s⌝);
a (rewrite_tac [eq⋎u_def] THEN prove_tac[] THEN asm_rewrite_tac[]);
val eq⋎u_refl_thm = save_pop_thm "eq⋎u_refl_thm";

set_goal([], ⌜∀s t⦁ s =⋎u t ⇒ t =⋎u s⌝);
a (rewrite_tac [eq⋎u_def] THEN prove_tac[] THEN asm_rewrite_tac[]);
val eq⋎u_sym_thm = save_pop_thm "eq⋎u_sym_thm";

set_goal([], ⌜∀s t u⦁ s =⋎u t ∧ t =⋎u u ⇒ t =⋎u u⌝);
a (rewrite_tac [eq⋎u_def] THEN prove_tac[] THEN asm_rewrite_tac[]);
val eq⋎u_trans_thm = save_pop_thm "eq⋎u_trans_thm";

set_goal([], ⌜∀s t⦁ s =⋎u t ⇔ ∀u⦁ u ∈⋎u s ⇔ u ∈⋎u t⌝);
a (PC_T1 "hol1" rewrite_tac [sets_ext_clauses, ∈_in_clauses, eq⋎u_def, X⋎u_def] THEN prove_tac[]);
val eq⋎u_ext_thm = save_pop_thm "eq⋎u_ext_thm";

set_goal([], ⌜∀t⦁ ¬ t =⋎u t⌝);
a (PC_T1 "hol1" rewrite_tac [sets_ext_clauses, ∈_in_clauses, eq⋎u_def, X⋎u_def] THEN prove_tac[]);

set_goal([], ⌜∀s t⦁ ¬ s =⋎u t ⇒ ¬ s = t⌝);
a (contr_tac);
a (var_elim_asm_tac ⌜s = t⌝ THEN POP_ASM_T ante_tac THEN rewrite_tac[eq⋎u_refl_thm]);
val ¬eq⋎u_¬eq_thm = save_pop_thm "¬eq⋎u_¬eq_thm";

add_rw_thms [eq⋎u_refl_thm] "'gsu-ax";
add_sc_thms [eq⋎u_refl_thm] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

\subsubsection{Well-Foundedness}

Wellfoundedness is asserted using the definition in the theory ``U\_orders'', which is conventional in asserting that each non-empty set has a minimal element.

=SML
val ⦏gsu_wf_axiom⦎ = new_axiom (["gsu_wf_axiom"], ⌜UWellFounded $∈⋎u⌝);
=TEX


=GFT
⦏gsu_wf_thm1⦎ =		⊢ well_founded $∈⋎u
⦏gsu_wf_min_thm⦎ =		⊢ ∀ x⦁ (∃ y⦁ y ∈⋎u x)
						⇒ (∃ z⦁ z ∈⋎u x ∧ ¬ (∃ v⦁ v ∈⋎u z ∧ v ∈⋎u x))
⦏gsu_wftc_thm⦎ =		⊢ well_founded (tc $∈⋎u)
=TEX

\ignore{
=SML
val gsu_wf_thm1 = save_thm ("gsu_wf_thm1", rewrite_rule [UWellFounded_well_founded_thm] gsu_wf_axiom);
push_pc "sets_ext";

set_goal([], ⌜well_founded (tc $∈⋎u)⌝);
a (bc_tac [wf_tc_wf_thm]);
a (accept_tac gsu_wf_thm1);
val gsu_wftc_thm = save_pop_thm "gsu_wftc_thm";

set_goal([], ⌜∀x⦁ (∃y⦁ y ∈⋎u x) ⇒ ∃z⦁ z ∈⋎u x ∧ ¬∃v⦁ v ∈⋎u z ∧ v ∈⋎u x⌝);
a (REPEAT strip_tac);
a (asm_tac (rewrite_rule [∀_elim ⌜$∈⋎u⌝ u_well_founded_def_thm] gsu_wf_axiom));
a (spec_nth_asm_tac 1 ⌜{z | z ∈⋎u x}⌝);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "2" *** *)
a (∃_tac ⌜x'⌝ THEN contr_tac);
a (asm_prove_tac[]);
val gsu_wf_min_thm = save_pop_thm "gsu_wf_min_thm";
pop_pc();
=TEX
}%ignore

=SML
declare_infix (230, "∈⋎u⋏+");
=TEX

ⓈHOLCONST
│ $⦏∈⋎u⋏+⦎ : 'a GSU → 'a GSU → BOOL
├────────────
│ $∈⋎u⋏+ = tc $∈⋎u
■

=GFT
⦏gsu_wftc_thm2⦎ =	⊢ well_founded $∈⋎u⋏+
⦏tc∈⋎u_incr_thm⦎ =	⊢ ∀ x y⦁ x ∈⋎u y ⇒ x ∈⋎u⋏+ y
⦏tc∈⋎u_cases_thm⦎ =	⊢ ∀ x y⦁ x ∈⋎u⋏+ y ⇔ (x ∈⋎u y ∨ (∃ z⦁ x ∈⋎u⋏+ z ∧ z ∈⋎u y))
⦏tc∈⋎u_trans_thm⦎ =	⊢ ∀ s t u⦁ s ∈⋎u⋏+ t ∧ t ∈⋎u⋏+ u ⇒ s ∈⋎u⋏+ u
⦏tc∈⋎u_decomp_thm⦎ =	⊢ ∀ x y⦁ x ∈⋎u⋏+ y ∧ ¬ x ∈⋎u y ⇒ (∃ z⦁ x ∈⋎u⋏+ z ∧ z ∈⋎u y)
⦏tc∈⋎u_decomp_thm5⦎ =	⊢ ∀ x y⦁ x ∈⋎u⋏+ y ∧ ¬ x ∈⋎u y ⇒ (∃ z⦁ x ∈⋎u z ∧ z ∈⋎u⋏+ y)
=TEX

=IGN
Some other theorems which might be instantiated to ∈⋎u⋏+ (from t005):

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

\ignore{
=SML
set_goal([], ⌜well_founded $∈⋎u⋏+⌝);
a (rewrite_tac [get_spec ⌜$∈⋎u⋏+⌝, gsu_wftc_thm]);
val gsu_wftc_thm2 = save_pop_thm "gsu_wftc_thm2";

set_goal([], ⌜∀x y⦁ x ∈⋎u y ⇒ x ∈⋎u⋏+ y⌝);
a (rewrite_tac [get_spec ⌜$∈⋎u⋏+⌝] THEN REPEAT strip_tac THEN fc_tac [tc_incr_thm]);
val tc∈⋎u_incr_thm = save_pop_thm "tc∈⋎u_incr_thm";

set_goal([], ⌜∀ x y⦁ x ∈⋎u⋏+ y ⇔ x ∈⋎u y ∨ ∃z⦁ x ∈⋎u⋏+ z ∧ z ∈⋎u y⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$∈⋎u⋏+⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [tc_decomp_thm]);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [tc_incr_thm]);
(* *** Goal "3" *** *)
a (lemma_tac ⌜tc $∈⋎u z y⌝ THEN1 fc_tac [tc_incr_thm]);
a (all_ufc_tac [tran_tc_thm2]);
val tc∈⋎u_cases_thm = save_pop_thm "tc∈⋎u_cases_thm";


set_goal([], ⌜∀s t u⦁ s ∈⋎u⋏+ t ∧ t ∈⋎u⋏+ u ⇒ s ∈⋎u⋏+ u⌝);
a(REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$∈⋎u⋏+⌝, tran_tc_thm2]);
val tc∈⋎u_trans_thm = save_pop_thm "tc∈⋎u_trans_thm";

set_goal([], ⌜∀x y⦁ x ∈⋎u⋏+ y ∧ ¬ x ∈⋎u y
		⇒ ∃z⦁ x ∈⋎u⋏+ z ∧ z ∈⋎u y⌝);
a (rewrite_tac[get_spec ⌜$∈⋎u⋏+⌝, tc_decomp_thm]);
val tc∈⋎u_decomp_thm = save_pop_thm "tc∈⋎u_decomp_thm";

set_goal([],⌜∀ x y⦁ x ∈⋎u⋏+ y ∧ ¬ x ∈⋎u y ⇒ (∃ z⦁ x ∈⋎u z ∧ z ∈⋎u⋏+ y)⌝);
a (rewrite_tac[get_spec ⌜$∈⋎u⋏+⌝, tc_decomp_thm5]);
val tc∈⋎u_decomp_thm5 = save_pop_thm "tc∈⋎u_decomp_thm5";
=TEX
}%ignore

The following operator restricts a function over sets to a domain determined by some set.
It was originally introduced to use in definitions by transfinite recursion, and a recursion principle is later proven for that purpose, but I then had some better ideas on how to define functions.

=SML
declare_infix (300, "◁∈⋏+⋎u");
=TEX

ⓈHOLCONST
│ $⦏◁∈⋏+⋎u⦎ : 'a GSU → ('a GSU → 'b) → ('a GSU → 'b)
├
│ ∀s f⦁ s ◁∈⋏+⋎u f = λx⦁ if x ∈⋎u⋏+ s then f x else εy⦁T
■

\ignore{
=SML
val ◁tc∈⋎u_def = get_spec ⌜$◁∈⋏+⋎u⌝;
=TEX
}%ignore



The resulting induction principle (sometimes called Noetherian induction?) is useful.

=GFT
⦏gsu_wf_ind_thm⦎ =	⊢ ∀ p⦁ (∀ x⦁ (∀ y⦁ y ∈⋎u x ⇒ p y) ⇒ p x) ⇒ (∀ x⦁ p x)
⦏gsu_cv_ind_thm⦎ =	⊢ ∀ p⦁ (∀ x⦁ (∀ y⦁ tc $∈⋎u y x ⇒ p y) ⇒ p x) ⇒ (∀ x⦁ p x)
⦏gsu_cv_ind_thm2⦎ =	⊢ ∀ p⦁ (∀ x⦁ (∀ y⦁ y ∈⋎u⋏+ x ⇒ p y) ⇒ p x) ⇒ (∀ x⦁ p x)
=TEX

But we can get induction tactics directly from the well-foundedness theorems:

=SML
val ⦏'a GSU_INDUCTION_T⦎ = WF_INDUCTION_T gsu_wf_thm1;
val ⦏gsu_induction_tac⦎ = wf_induction_tac gsu_wf_thm1;
val ⦏'a GSU_INDUCTION_T2⦎ = WF_INDUCTION_T gsu_wftc_thm2;
val ⦏gsu_induction_tac2⦎ = wf_induction_tac gsu_wftc_thm2;
=TEX

\ignore{
=SML
val gsu_wf_ind_thm = save_thm ("gsu_wf_ind_thm",
	(rewrite_rule  [∀_elim ⌜$∈⋎u⌝ u_well_founded_induction_thm] gsu_wf_axiom));

val gsu_cv_ind_thm = save_thm ("gsu_cv_ind_thm",
	(rewrite_rule  [rewrite_rule [UWellFounded_well_founded_thm]
	(∀_elim ⌜tc $∈⋎u⌝ u_well_founded_induction_thm)] gsu_wftc_thm));

val gsu_cv_ind_thm2 = save_thm ("gsu_cv_ind_thm2",
	(prove_rule  [gsu_cv_ind_thm, get_spec ⌜$∈⋎u⋏+⌝]
	⌜∀ p⦁ (∀ x⦁ (∀ y⦁ y ∈⋎u⋏+ x ⇒ p y) ⇒ p x) ⇒ (∀ x⦁ p x)⌝));
=TEX
}%ignore


=GFT
⦏wf_ul1⦎ =	⊢ ∀ x:'a GSU⦁ ¬ x ∈⋎u x
⦏wf_ul2⦎ =	⊢ ∀ x y:'a GSU⦁ ¬ (x ∈⋎u y ∧ y ∈⋎u x)
⦏wf_ul3⦎ =	⊢ ∀ x y z:'a GSU⦁ ¬ (x ∈⋎u y ∧ y ∈⋎u z ∧ z ∈⋎u x)
=TEX

\ignore{
=SML
set_goal([], ⌜
	∀ x:'a GSU⦁ ¬ x ∈⋎u x
⌝);
a (asm_tac (gsu_wf_ind_thm));
a (spec_nth_asm_tac 1 ⌜λx⦁ ¬ x ∈⋎u x⌝);
a (swap_nth_asm_concl_tac 1
	THEN rewrite_tac[]
	THEN swap_nth_asm_concl_tac 1
	THEN ALL_ASM_FC_T (MAP_EVERY ante_tac) []
	THEN asm_rewrite_tac[]);
a (strip_tac
	THEN swap_nth_asm_concl_tac 1
	THEN rewrite_tac[]
	THEN REPEAT strip_tac
	THEN ∃_tac ⌜x⌝
	THEN asm_rewrite_tac[]);
val wf_ul1 = save_pop_thm "wf_ul1";

set_goal([], ⌜∀ x y:'a GSU⦁ ¬ (x ∈⋎u y ∧ y ∈⋎u x)⌝);
a (asm_tac gsu_wf_ind_thm);
a (spec_nth_asm_tac 1 ⌜λz⦁ ∀x⦁ ¬(x ∈⋎u z ∧ z ∈⋎u x)⌝);
(* *** Goal "1" *** *)
a (swap_nth_asm_concl_tac 1
	THEN rewrite_tac[]
	THEN swap_nth_asm_concl_tac 1
	THEN ALL_ASM_FC_T (MAP_EVERY ante_tac) []
	THEN asm_rewrite_tac[]);
a (strip_tac
	THEN spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "2" *** *)
a (strip_tac
	THEN swap_nth_asm_concl_tac 1
	THEN rewrite_tac[]
	THEN REPEAT strip_tac
	THEN ∃_tac ⌜y⌝
	THEN REPEAT strip_tac
	THEN ∃_tac ⌜x⌝
	THEN REPEAT strip_tac);
val wf_ul2 = save_pop_thm "wf_ul2";

set_goal([], ⌜∀ x y z:'a GSU⦁ ¬ (x ∈⋎u y ∧ y ∈⋎u z ∧ z ∈⋎u x)⌝);
a (asm_tac gsu_wf_ind_thm);
a (spec_nth_asm_tac 1 ⌜λz⦁ ∀x y⦁ ¬(x ∈⋎u y ∧ y ∈⋎u z ∧ z ∈⋎u x)⌝);
(* *** Goal "1" *** *)
a (swap_nth_asm_concl_tac 1
	THEN rewrite_tac[]
	THEN swap_nth_asm_concl_tac 1
	THEN ALL_ASM_FC_T (MAP_EVERY ante_tac) []
	THEN asm_rewrite_tac[]);
a (strip_tac
	THEN list_spec_nth_asm_tac 1 [⌜x⌝, ⌜x''⌝]);
(* *** Goal "2" *** *)
a (REPEAT ∀_tac);
a (SPEC_NTH_ASM_T 1 ⌜z:'a GSU⌝ ante_tac);
a (rewrite_tac[]);
a (strip_tac THEN asm_rewrite_tac[]);
val wf_ul3 = save_pop_thm "wf_ul3";
=TEX
}%ignore


\ignore{
=SML
set_goal([], ⌜∀(af:('a GSU → 'b) → 'a GSU → 'b)⦁ ∃(f:'a GSU → 'b)⦁
	∀s⦁ f s = af ((λf x⦁ if x ∈⋎u⋏+ s then f x else εy⦁T)f) s⌝);
a (rewrite_tac[] THEN REPEAT strip_tac);
a (lemma_tac ⌜∃g⦁ g = λf⦁ λs⦁ af (λx⦁ if x ∈⋎u⋏+ s then f x else εy⦁T) s⌝
	THEN1 prove_∃_tac );
a (lemma_tac ⌜g respects $∈⋎u⌝ THEN1
	(asm_rewrite_tac [get_spec ⌜$respects⌝] THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (LEMMA_T ⌜(λ x'⦁ if x' ∈⋎u⋏+ x then g' x' else ε y⦁ T)
	= (λ x'⦁ if x' ∈⋎u⋏+ x then h x' else ε y⦁ T)⌝ rewrite_thm_tac);
a (rewrite_tac [ext_thm]);
a (strip_tac);
a (spec_nth_asm_tac 1 ⌜x'⌝ THEN_TRY asm_rewrite_tac[]);
a (POP_ASM_T ante_tac);
a (LEMMA_T ⌜tc $∈⋎u x' x ⇔ x' ∈⋎u⋏+ x⌝ rewrite_thm_tac
	THEN1 rewrite_tac[get_spec ⌜$∈⋎u⋏+⌝]);
a (STRIP_T rewrite_thm_tac);
(* *** Goal "2" *** *)
a (∃_tac ⌜fix g⌝);
a (asm_tac gsu_wf_thm1);
a (fc_tac [get_spec ⌜fix⌝]);
a (all_asm_fc_tac[]);
a (strip_tac);
a (rewrite_tac[once_rewrite_conv
	[(eq_sym_rule o asm_rule) ⌜g (fix g) = fix g⌝] ⌜fix g s⌝]);
a (GET_NTH_ASM_T 5 rewrite_thm_tac);
val ∈⋎u⋏p_recursion_lemma = save_pop_thm "∈⋎u⋏p_recursion_lemma";

set_goal([], ⌜∀(af:('a GSU → 'b) → 'a GSU → 'b)⦁ ∃(f:'a GSU → 'b)⦁
	∀s⦁ f s = af ((λf x⦁ if x ∈⋎u⋏+ s then f x else εy⦁T)f) s⌝);

=TEX
}%ignore

=IGN

evaluate_∃_cd_thm ∈⋎u⋏p_recursion_lemma;

add_∃_cd_thms [∈⋎u⋏p_recursion_lemma] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];

basic_prove_∃_conv ⌜⌝;



=TEX

\subsection{The Ontology Axiom}

The remaining axioms are intended to ensure that the sets are a large and well-rounded part of the cumulative heirarchy.
This is to be accomplished by defining a Galaxy as a set satisfying certain closure properties and then asserting that every set is a member of some Galaxy.
It is convenient to introduce new constants and axioms for each of the Galactic closure properties before asserting the existence of the Galaxies.

Here we define the Subset relation and assert the existence of powersets and unions.

\subsubsection{Subsets}

A Subset s of t is a set all of whose members are also members of t.

=SML
declare_infix (230,"⊆⋎u");
declare_infix (230,"⊂⋎u");
=TEX

ⓈHOLCONST
│ $⦏⊆⋎u⦎ : 'a GSU → 'a GSU → BOOL
├───────────
│ ∀s t⦁ s ⊆⋎u t ⇔ ∀e⦁ e ∈⋎u s ⇒ e ∈⋎u t
■

ⓈHOLCONST
│ $⦏⊂⋎u⦎ : 'a GSU → 'a GSU → BOOL
├───────────
│ ∀s t⦁ s ⊂⋎u t ⇔ s ⊆⋎u t ∧ ¬ t ⊆⋎u s
■

=GFT
⦏⊆⋎u_eq_thm⦎ =		⊢ ∀ A B⦁ Set⋎u A ∧ Set⋎u B ⇒ (A = B ⇔ A ⊆⋎u B ∧ B ⊆⋎u A)
⦏⊆⋎u_refl_thm⦎ =		⊢ ∀ A⦁ A ⊆⋎u A
⦏∈⋎u⊆⋎u_def⦎ =		⊢ ∀ e A B⦁ e ∈⋎u A ∧ A ⊆⋎u B ⇒ e ∈⋎u B
⦏⊆⋎u_trans_thm⦎ =	⊢ ∀ A B C⦁ A ⊆⋎u B ∧ B ⊆⋎u C ⇒ A ⊆⋎u C
⦏⊂⋎u_trans_thm⦎ =	⊢ ∀ A B C⦁ A ⊂⋎u B ∧ B ⊂⋎u C ⇒ A ⊂⋎u C
⦏not_⊂⋎u_thm⦎ =	⊢ ∀ x⦁ ¬ x ⊂⋎u x
=TEX

\ignore{
=SML
val ⊆⋎u_def = get_spec ⌜$⊆⋎u⌝;
val ⊂⋎u_def = get_spec ⌜$⊂⋎u⌝;

=IGN
set_goal([], ⌜∀s t⦁ s ⊆⋎u t ∨ s ⊂⋎u t ⇒ Set⋎u s ∧ Set⋎u t⌝);
a (rewrite_tac [⊆⋎u_def, ⊂⋎u_def] THEN REPEAT strip_tac);
val ⊆⋎u_⊂⋎u_Set_fc_thm = save_pop_thm "⊆⋎u_⊂⋎u_Set_fc_thm";
=SML

set_goal([], ⌜∀A B⦁ Set⋎u A ∧ Set⋎u B ⇒ (A = B ⇔ A ⊆⋎u B ∧ B ⊆⋎u A)⌝);
a (REPEAT strip_tac THEN_TRY rewrite_tac [⊆⋎u_def]
	THEN REPEAT strip_tac THEN_TRY all_var_elim_asm_tac);
a (all_asm_ufc_⇔_rewrite_tac [gsu_ext_axiom]);
a (REPEAT_N 2 (POP_ASM_T ante_tac)
	THEN rewrite_tac [⊆⋎u_def]
	THEN prove_tac[]);
val ⊆⋎u_eq_thm = save_pop_thm "⊆⋎u_eq_thm";

val ⊆⋎u_refl_thm = save_thm ("⊆⋎u_refl_thm", 
	prove_rule [⊆⋎u_def]
	⌜∀A⦁ A ⊆⋎u A⌝);
val ∈⋎u⊆⋎u_def = save_thm ("∈⋎u⊆⋎u_def",
	prove_rule [⊆⋎u_def]
	⌜∀e A B⦁ e ∈⋎u A ∧ A ⊆⋎u B ⇒ e ∈⋎u B⌝);
val ⊆⋎u_trans_thm = save_thm ("⊆⋎u_trans_thm",
	prove_rule [⊆⋎u_def]
	⌜∀A B C⦁ A ⊆⋎u B ∧ B ⊆⋎u C ⇒ A ⊆⋎u C⌝);

set_goal([], ⌜∀A B C⦁ A ⊂⋎u B ∧ B ⊂⋎u C ⇒ A ⊂⋎u C⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$⊂⋎u⌝]
	THEN REPEAT strip_tac
	THEN_TRY all_fc_tac [⊆⋎u_trans_thm]);
a contr_tac;
a (all_fc_tac [⊆⋎u_trans_thm]);
val ⊂⋎u_trans_thm = save_pop_thm "⊂⋎u_trans_thm";

set_goal ([], ⌜∀x⦁ ¬ x ⊂⋎u x⌝);
a (rewrite_tac [⊂⋎u_def]);
a (REPEAT strip_tac);
val not_⊂⋎u_thm = save_pop_thm "not_⊂⋎u_thm";

add_pc_thms "'gsu-ax" [];
add_rw_thms [not_⊂⋎u_thm, ⊆⋎u_refl_thm] "'gsu-ax";
add_sc_thms [not_⊂⋎u_thm, ⊆⋎u_refl_thm] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

ⓈHOLCONST
│ ⦏⊆⋎u_closed⦎ : 'a GSU → BOOL
├────────────
│ ∀s⦁ ⊆⋎u_closed s ⇔ ∀e f⦁ e ∈⋎u s ∧ f ⊆⋎u e ⇒ f ∈⋎u s
■

\subsubsection{The Ontology Axiom}

We now specify with a single axiom the closure requirements which ensure that our universe is adequately populated.
The ontology axiom states that every set is a member of some galaxy which is transitive and closed under formation of powersets and unions and under replacement.

The formulation of replacement only makes membership of a galaxy dependent on the range being contained in the galaxy, it asserts unconditionally the sethood of the image of a set under a functional relation.

Because we have urelements and the ontology axiom introduces sets by their extension, special provision is necessary to ensure the existence of the empty set.
In the corresponding theory without urelements the existence of the empty set is obtained from the ontology axiom using the clause which corresponds to the axiom of replacement, but this axiom only establishes that something has no members, leaving open the possibility that there is an urelement but there is no empty set.
We therefore assert that the image of a something through a functional relation is a set.

In some other places it is necessary to insist on certain objects being sets.
Thus, power sets never contain urelements, and this must be made explicit.
This would not have been necessary had we defined the subset relation as holding only between sets, which might possibly have been better.

It is not necessary to assert sethood in any other case, however, I have found it expedient to mention sethood in a couple of places where it is strictly redundant.
This is because to get the consistency proof for the specifications of the constants used for these constructors I would otherwise need to know that the empty set exists, so that I can insist on them yielding it whenever the result has an empty extension.
However, I can't prove the existence of the empty set until I have the separation axiom.
Well I could, but...

=SML
val ⦏UOntology_axiom⦎ =
	new_axiom (["UOntology_axiom"],
⌜ ∀s:'a GSU⦁
	∃g⦁ s ∈⋎u g
∧
	∀t⦁ t ∈⋎u g
	⇒ t ⊆⋎u g
	∧ (∃p⦁ (∀v⦁ v ∈⋎u p ⇔ Set⋎u v ∧ v ⊆⋎u t) ∧ p ∈⋎u g ∧ Set⋎u p)
	∧ (∃u⦁ (∀v⦁ v ∈⋎u u ⇔ ∃w⦁ v ∈⋎u w ∧ w ∈⋎u t) ∧ u ∈⋎u g ∧ Set⋎u u)
	∧ (∀rl⦁ ManyOne rl ⇒
		(∃r⦁ (∀v⦁ v ∈⋎u r ⇔ ∃w ⦁ w ∈⋎u t ∧ rl w v)
			∧ (r ⊆⋎u g ⇒ r ∈⋎u g)
			∧ Set⋎u r))⌝
);
=TEX

I originally thought that in this version of set theory with urelements, iteration of the type constructor would always create larger universes.
However, I don't see anything which tells us that there is a set containing all the urelements, and it is therefore possible that the urelements have the same cardinality as the sets.

\subsection{PowerSets and Union}

Here we define the powerset and union operators.

\subsubsection{PowerSets}

\ignore{
=SML
set_goal([],⌜∃ ℙ⋎u⦁ ∀s⦁ Set⋎u (ℙ⋎u s) ∧ ∀t⦁ t ∈⋎u ℙ⋎u s ⇔ Set⋎u t ∧ t ⊆⋎u s⌝);
a (prove_∃_tac THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜s'⌝ (UOntology_axiom)));
a (spec_nth_asm_tac 1 ⌜s'⌝ THEN ∃_tac ⌜p⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏ℙ⋎u⦎: 'a GSU → 'a GSU
├─────────────
│ ∀s⦁ Set⋎u (ℙ⋎u s) ∧ ∀t:'a GSU⦁ t ∈⋎u ℙ⋎u s ⇔ Set⋎u t ∧ t ⊆⋎u s
■

=GFT
⦏ℙ⋎u_thm⦎ =	⊢ ∀ s t⦁ t ∈⋎u ℙ⋎u s = (Set⋎u t ∧ t ⊆⋎u s)
⦏s∈ℙ⋎us_thm⦎ =	⊢ ∀ s⦁ Set⋎u s ⇒ s ∈⋎u ℙ⋎u s
⦏stc∈ℙ⋎us_thm⦎ =	⊢ ∀ s⦁ Set⋎u s ⇒ s ∈⋎u⋏+ ℙ⋎u s
⦏Set⋎uℙ⋎u_thm⦎ =	⊢ ∀ s⦁ Set⋎u (ℙ⋎u s)
⦏eqℙ⋎u_thm⦎ =
   ⊢ ∀ s t⦁ Set⋎u s ∧ Set⋎u t
	⇒ ((s = ℙ⋎u t) ⇔ (∀ x⦁ x ∈⋎u s ⇔ Set⋎u x ∧ x ⊆⋎u t))
=TEX

\ignore{
=SML
val ℙ⋎u_def = get_spec ⌜ℙ⋎u⌝;
val ∈⋎up_def = get_spec ⌜$∈⋎u⋏+⌝;

set_goal([], ⌜∀s t:'a GSU⦁ t ∈⋎u ℙ⋎u s ⇔ Set⋎u t ∧ t ⊆⋎u s⌝);
a (rewrite_tac[ℙ⋎u_def]);
val ℙ⋎u_thm = save_pop_thm "ℙ⋎u_thm";

set_goal([], ⌜∀s⦁ Set⋎u s ⇒ s ∈⋎u ℙ⋎u s⌝);
a (REPEAT strip_tac THEN asm_rewrite_tac [ℙ⋎u_def, ⊆⋎u_def]);
val s∈ℙ⋎us_thm = save_pop_thm "s∈ℙ⋎us_thm";

set_goal([], ⌜∀s⦁ Set⋎u s ⇒ s ∈⋎u⋏+ ℙ⋎u s⌝);
a (REPEAT strip_tac THEN asm_rewrite_tac [∈⋎up_def]);
a (asm_fc_tac [s∈ℙ⋎us_thm] THEN ufc_tac [tc_incr_thm] THEN asm_rewrite_tac []);
val stc∈ℙ⋎us_thm = save_pop_thm "stc∈ℙ⋎us_thm";

set_goal([], ⌜∀s⦁ Set⋎u (ℙ⋎u s)⌝);
a (rewrite_tac [ℙ⋎u_def]);
val Set⋎uℙ⋎u_thm = save_pop_thm "Set⋎uℙ⋎u_thm";

set_goal([], ⌜∀s t⦁ Set⋎u s ∧ Set⋎u t ⇒ (s = ℙ⋎u t ⇔ ∀x⦁ x ∈⋎u s ⇔ Set⋎u x ∧ x ⊆⋎u t)⌝);
a (REPEAT ∀_tac);
a (lemma_tac ⌜Set⋎u (ℙ⋎u t)⌝ THEN1 rewrite_tac [Set⋎uℙ⋎u_thm]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (DROP_NTH_ASM_T 2 ante_tac THEN all_ufc_⇔_rewrite_tac [gsu_ext_axiom]);
a (REPEAT strip_tac THEN asm_fc_tac []);
a (POP_ASM_T ante_tac THEN rewrite_tac [ℙ⋎u_def] THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a (DROP_NTH_ASM_T 2 ante_tac THEN all_ufc_⇔_rewrite_tac [gsu_ext_axiom]);
a (asm_rewrite_tac [ℙ⋎u_def]);
a (REPEAT strip_tac THEN asm_fc_tac []);
(* *** Goal "3" *** *)
a (asm_rewrite_tac [ℙ⋎u_def]);
(* *** Goal "4" *** *)
a (all_ufc_⇔_rewrite_tac [gsu_ext_axiom]);
a (strip_tac THEN asm_rewrite_tac[ℙ⋎u_def]);
val eqℙ⋎u_thm = save_pop_thm "eqℙ⋎u_thm";
=TEX
}%ignore

\subsubsection{Union}

\ignore{
=SML
set_goal([],⌜∃⋃⋎u⦁ ∀s⦁ Set⋎u (⋃⋎u s) ∧ ∀t⦁ t ∈⋎u ⋃⋎u s ⇔ ∃e⦁ t ∈⋎u e ∧ e ∈⋎u s⌝);
a (prove_∃_tac THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜s'⌝ UOntology_axiom));
a (spec_nth_asm_tac 1 ⌜s'⌝ THEN ∃_tac ⌜u⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏⋃⋎u⦎: 'a GSU → 'a GSU
├───────────
│ ∀s⦁ Set⋎u (⋃⋎u s) ∧ ∀t⦁ t ∈⋎u ⋃⋎u s ⇔ ∃e⦁ t ∈⋎u e ∧ e ∈⋎u s
■

=GFT
⦏⋃⋎u_thm⦎ =	⊢ ∀ s t⦁ t ∈⋎u ⋃⋎u s ⇔ (∃ e⦁ t ∈⋎u e ∧ e ∈⋎u s)
⦏tc∈⋎u_⋃⋎u_thm⦎ =	⊢ ∀ s t⦁ t ∈⋎u⋏+ ⋃⋎u s ⇔ (∃ e⦁ t ∈⋎u⋏+ e ∧ e ∈⋎u s)
⦏∈⋎u⋃⋎u_thm⦎ =	⊢ ∀s t:'a GSU⦁ Set⋎u t ∧ t ∈⋎u s ⇒ t ⊆⋎u ⋃⋎u s
⦏∈⋎u⋃⋎u_thm2⦎ =	⊢ ∀ s t⦁ t ∈⋎u ⋃⋎u s ⇒ (∃ e⦁ t ∈⋎u e ∧ e ∈⋎u s)
⦏∈⋎u⋃⋎u_thm3⦎ =	⊢ ∀ s t⦁ (∃ e⦁ t ∈⋎u e ∧ e ∈⋎u s) ⇒ t ∈⋎u ⋃⋎u s
⦏⋃⋎u_ext_thm⦎ =	⊢ ∀ x y⦁ (⋃⋎u x = y) ⇔ (Set⋎u y ∧ (∀ z⦁ z ∈⋎u y ⇔ (∃ w⦁ z ∈⋎u w ∧ w ∈⋎u x)))
⦏Set⋎u⋃⋎u_thm⦎ =	⊢ ∀ s⦁ Set⋎u (⋃⋎u s)
=TEX

\ignore{
=SML
val ⋃⋎u_def = get_spec ⌜⋃⋎u⌝;

set_goal([], ⌜∀s t⦁ t ∈⋎u ⋃⋎u s ⇔ ∃e⦁ t ∈⋎u e ∧ e ∈⋎u s⌝);
a (rewrite_tac [⋃⋎u_def]);
val ⋃⋎u_thm = save_pop_thm "⋃⋎u_thm";

set_goal([], ⌜∀s t⦁ t ∈⋎u⋏+ ⋃⋎u s ⇔ ∃e⦁ t ∈⋎u⋏+ e ∧ e ∈⋎u s⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [tc∈⋎u_decomp_thm]);
(* *** Goal "1.1" *** *)
a (fc_tac [⋃⋎u_thm]);
a (fc_tac [tc∈⋎u_incr_thm]);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (fc_tac [⋃⋎u_thm]);
a (fc_tac [tc∈⋎u_incr_thm]);
a (all_fc_tac [tc∈⋎u_trans_thm]);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [tc∈⋎u_decomp_thm]);
(* *** Goal "2.1" *** *)
a (LEMMA_T ⌜t ∈⋎u ⋃⋎u s⌝ asm_tac THEN1 asm_rewrite_tac[⋃⋎u_thm]);
(* *** Goal "2.1.1" *** *)
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
a (fc_tac [tc∈⋎u_incr_thm]);
(* *** Goal "2.2" *** *)
a (LEMMA_T ⌜z ∈⋎u ⋃⋎u s⌝ asm_tac THEN1 asm_rewrite_tac[⋃⋎u_thm]);
(* *** Goal "2.2.1" *** *)
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a (fc_tac [tc∈⋎u_incr_thm]);
a (all_fc_tac [tc∈⋎u_trans_thm]);
val tc∈⋎u_⋃⋎u_thm = save_pop_thm "tc∈⋎u_⋃⋎u_thm";

val ∈⋎u⋃⋎u_thm = save_thm ("∈⋎u⋃⋎u_thm",
	prove_rule [⋃⋎u_def, ⊆⋎u_def]
	⌜∀s t:'a GSU⦁ t ∈⋎u s ⇒ t ⊆⋎u ⋃⋎u s⌝);

val ∈⋎u⋃⋎u_thm2 = save_thm ("∈⋎u⋃⋎u_thm2",
	prove_rule [⋃⋎u_def, ⊆⋎u_def]
	⌜∀s t:'a GSU⦁ t ∈⋎u ⋃⋎u s ⇒  ∃e⦁ t ∈⋎u e ∧ e ∈⋎u s⌝);

val ∈⋎u⋃⋎u_thm3 = save_thm ("∈⋎u⋃⋎u_thm3",
	prove_rule [⋃⋎u_def, ⊆⋎u_def]
	⌜∀s t:'a GSU⦁ (∃e⦁ t ∈⋎u e ∧ e ∈⋎u s) ⇒ t ∈⋎u ⋃⋎u s⌝);

val Set⋎u⋃⋎u_thm = save_thm ("Set⋎u⋃⋎u_thm",
	prove_rule [⋃⋎u_def, ⊆⋎u_def]
	⌜∀s⦁ Set⋎u (⋃⋎u s)⌝);

set_goal([], ⌜∀x y⦁ ⋃⋎u x = y ⇔ Set⋎u y ∧ ∀ z⦁ z ∈⋎u y ⇔ (∃ w⦁ z ∈⋎u w ∧ w ∈⋎u x)⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (SYM_ASMS_T rewrite_tac);
a (rewrite_tac[Set⋎u⋃⋎u_thm]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜z ∈⋎u ⋃⋎u x⌝ THEN1 asm_rewrite_tac[]);
a (fc_tac [∈⋎u⋃⋎u_thm2]);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (all_fc_tac [∈⋎u⋃⋎u_thm3] THEN SYM_ASMS_T rewrite_tac);
(* *** Goal "4" *** *)
a (lemma_tac ⌜Set⋎u(⋃⋎u x)⌝ THEN1 rewrite_tac [Set⋎u⋃⋎u_thm]);
a (all_asm_ufc_⇔_rewrite_tac [gsu_ext_axiom]);
a (REPEAT strip_tac);
(* *** Goal "4.1" *** *)
a (all_fc_tac [∈⋎u⋃⋎u_thm2]);
a (spec_nth_asm_tac 5 ⌜e⌝);
(* *** Goal "4.1.1" *** *)
a (spec_nth_asm_tac 1 ⌜e'⌝);
(* *** Goal "4.1.2" *** *)
a (spec_nth_asm_tac 1 ⌜e'⌝);
(* *** Goal "4.2" *** *)
a (rewrite_tac [⋃⋎u_def]);
a (asm_fc_tac[]);
a (∃_tac ⌜w⌝ THEN asm_rewrite_tac[]);
val ⋃⋎u_ext_thm = save_pop_thm "⋃⋎u_ext_thm";

add_pc_thms "'gsu-ax" [ℙ⋎u_thm, ⋃⋎u_thm];
add_rw_thms [Set⋎uℙ⋎u_thm, Set⋎u⋃⋎u_thm, tc∈⋎u_⋃⋎u_thm] "'gsu-ax";
add_sc_thms [Set⋎uℙ⋎u_thm, Set⋎u⋃⋎u_thm, tc∈⋎u_⋃⋎u_thm] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

\subsection{Relational Replacement}

The constant $RelIm⋎u$ is defined for relational replacement.

\ignore{
=SML
set_goal([],⌜∃RelIm⋎u:('a GSU → 'a GSU → BOOL) → 'a GSU → 'a GSU⦁ ∀rl (s:'a GSU)⦁ Set⋎u(RelIm⋎u rl s) ∧ (ManyOne rl ⇒ ∀t⦁ (t ∈⋎u RelIm⋎u rl s ⇔ ∃e⦁ e ∈⋎u s ∧ rl e t))⌝);
a (prove_∃_tac THEN REPEAT strip_tac);
a (strip_asm_tac (∀_elim ⌜s'⌝ UOntology_axiom));
a (spec_nth_asm_tac 1 ⌜s'⌝);
a (spec_nth_asm_tac 1 ⌜rl'⌝);
(* *** Goal "1" *** *)
a (∃_tac ⌜u⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜r⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (∃_tac ⌜r⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm ());
=IGN
set_goal([],⌜∃RelIm⋎u:('a GSU → 'a GSU → BOOL) → 'a GSU → 'a GSU⦁ ∀rel (s:'a GSU) t⦁ ManyOne rel ⇒ (t ∈⋎u RelIm⋎u rel s ⇔ ∃e⦁ e ∈⋎u s ∧ rel e t) ∧ Set⋎u (RelIm⋎u rel s)⌝);
a (prove_∃_tac THEN REPEAT strip_tac);
a (strip_asm_tac (∀_elim ⌜s'⌝ UOntology_axiom));
a (spec_nth_asm_tac 1 ⌜s'⌝);
a (spec_nth_asm_tac 1 ⌜rel'⌝);
a (asm_rewrite_tac[]);
a (∃_tac ⌜r⌝ THEN strip_tac THEN strip_tac THEN asm_rewrite_tac[]);
a (∃_tac ⌜r⌝ THEN strip_tac THEN strip_tac THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏RelIm⋎u⦎: ('a GSU → 'a GSU → BOOL) → 'a GSU → 'a GSU
├───────────────
│ ∀rl s⦁ Set⋎u (RelIm⋎u rl s) ∧ (ManyOne rl ⇒ (∀t⦁ t ∈⋎u RelIm⋎u rl s ⇔ ∃e⦁ e ∈⋎u s ∧ rl e t))
■

=GFT
⦏Set⋎uRelIm⋎u_thm⦎ = ⊢ ∀ rel s⦁ Set⋎u (RelIm⋎u rel s)
⦏RelIm⋎u_thm⦎ =
   ⊢ ∀ rl s⦁ ManyOne rl ⇒ (∀ t⦁ t ∈⋎u RelIm⋎u rl s = (∃ e⦁ e ∈⋎u s ∧ rl e t))
=TEX

\ignore{
=SML
val RelIm⋎u_def = get_spec ⌜RelIm⋎u⌝;

set_goal([], ⌜∀rl s⦁ Set⋎u (RelIm⋎u rl s)⌝);
a (rewrite_tac [RelIm⋎u_def]);
val Set⋎uRelIm⋎u_thm = save_pop_thm "Set⋎uRelIm⋎u_thm";

set_goal([], ⌜∀rl s⦁ ManyOne rl ⇒ (∀t⦁ t ∈⋎u RelIm⋎u rl s ⇔ ∃e⦁ e ∈⋎u s ∧ rl e t)⌝);
a (rewrite_tac [RelIm⋎u_def]);
val RelIm⋎u_thm = save_pop_thm "RelIm⋎u_thm";

add_pc_thms "'gsu-ax" [RelIm⋎u_thm];
add_rw_thms [Set⋎uRelIm⋎u_thm] "'gsu-ax";
add_sc_thms [Set⋎uRelIm⋎u_thm] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

\subsection{Separation}

Separation is introduced by conservative extension.

The specification of $Sep⋎u$ which follows is introduced after proving that it is satisfied by a term involving the use of $RelIm⋎u$.

\ignore{
=SML
set_goal([],⌜∃Sep⋎u⦁ ∀s p⦁ (∀e⦁e ∈⋎u (Sep⋎u s p) ⇔ e ∈⋎u s ∧ p e) ∧ Set⋎u (Sep⋎u s p)⌝);
a (prove_∃_tac THEN REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim [⌜s'⌝] (UOntology_axiom)));
a (lemma_tac ⌜∃rl⦁ rl = λx y⦁ p' x ∧ y = x⌝
	THEN1 prove_∃_tac);
a (lemma_tac ⌜ManyOne rl⌝
	THEN1 asm_rewrite_tac [get_spec ⌜ManyOne rl⌝]);
(* *** Goal "1" *** *)
a (REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜RelIm⋎u rl s'⌝);
a (⇔_FC_T asm_rewrite_tac [get_spec ⌜RelIm⋎u⌝]);
a (prove_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

This higher order formulation of separation is accomplished by defining a new constant which takes a property of sets {\it p} and a set {\it s} and returns the Subset of {\it s} consisting of those elements which satisfy {\it p}.

ⓈHOLCONST
│ ⦏Sep⋎u⦎ : 'a GSU → ('a GSU → BOOL) → 'a GSU
├───────────
│ ∀s p⦁ (∀e⦁e ∈⋎u (Sep⋎u s p) ⇔ e ∈⋎u s ∧ p e) ∧ Set⋎u (Sep⋎u s p)
■

=GFT
⦏Sep⋎u_thm⦎ = ⊢ ∀s p e⦁e ∈⋎u (Sep⋎u s p) ⇔ e ∈⋎u s ∧ p e
⦏Set⋎u_Sep⋎u_thm⦎ = ⊢ ∀s p⦁ Set⋎u (Sep⋎u s p)
=TEX


\ignore{
=SML
val Sep⋎u_def = get_spec ⌜Sep⋎u⌝;

set_goal([], ⌜∀s p e⦁e ∈⋎u (Sep⋎u s p) ⇔ e ∈⋎u s ∧ p e⌝);
a (REPEAT ∀_tac THEN rewrite_tac [Sep⋎u_def]);
val Sep⋎u_thm = save_pop_thm "Sep⋎u_thm";

set_goal([], ⌜∀s p⦁ Set⋎u (Sep⋎u s p)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [Sep⋎u_def]);
val Set⋎u_Sep⋎u_thm = save_pop_thm "Set⋎u_Sep⋎u_thm";

add_pc_thms "'gsu-ax" [Sep⋎u_thm];
add_rw_thms [Set⋎u_Sep⋎u_thm] "'gsu-ax";
add_sc_thms [Set⋎u_Sep⋎u_thm] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

=GFT
⦏Sep⋎u_⊆⋎u_thm⦎ =		⊢ ∀ s p⦁ Set⋎u s ⇒ Sep⋎u s p ⊆⋎u s
⦏Sep⋎u_sub_thm⦎ =	⊢ ∀ s p e⦁ e ∈⋎u Sep⋎u s p ⇒ e ∈⋎u s
⦏Sep⋎u_∈⋎u_ℙ⋎u_thm⦎ =	⊢ ∀ s p⦁ Set⋎u s ⇒ Sep⋎u s p ∈⋎u ℙ⋎u s
⦏Sep⋎u_⊆_thm⦎ =		⊢ ∀ s t⦁ t ⊆⋎u s ⇒ Sep⋎u s (CombC $∈⋎u t) = t
=TEX

\ignore{
=SML
set_goal([], ⌜∀s p⦁ Set⋎u s ⇒ (Sep⋎u s p) ⊆⋎u s⌝);
a (rewrite_tac [⊆⋎u_def, get_spec ⌜Sep⋎u⌝]
	THEN REPEAT strip_tac);
val Sep⋎u_⊆⋎u_thm = save_pop_thm "Sep⋎u_⊆⋎u_thm";

set_goal([], ⌜∀ s p e⦁ e ∈⋎u Sep⋎u s p ⇒ e ∈⋎u s⌝);
a (rewrite_tac [get_spec ⌜Sep⋎u⌝] THEN REPEAT strip_tac);
val Sep⋎u_sub_thm = save_pop_thm "Sep⋎u_sub_thm";

set_goal([], ⌜∀s p⦁ Set⋎u s ⇒ (Sep⋎u s p) ∈⋎u ℙ⋎u s⌝);
a (rewrite_tac [get_spec ⌜ℙ⋎u⌝, Sep⋎u_⊆⋎u_thm]);
val Sep⋎u_∈⋎u_ℙ⋎u_thm = save_pop_thm "Sep⋎u_∈⋎u_ℙ⋎u_thm";

set_goal([], ⌜∀s t⦁ Set⋎u t ∧ t ⊆⋎u s ⇒ Sep⋎u s (CombC $∈⋎u t) = t⌝);
a (strip_tac THEN rewrite_tac [⊆⋎u_def, get_spec ⌜Sep⋎u⌝, get_spec ⌜CombC⌝]
	THEN REPEAT strip_tac);
a (LEMMA_T ⌜Set⋎u (Sep⋎u s (λ y⦁ y ∈⋎u t))⌝ asm_tac THEN1 rewrite_tac[conv_rule(ONCE_MAP_C β_conv)(list_∀_elim [⌜s⌝, ⌜λ y⦁ y ∈⋎u t⌝] (get_spec ⌜Sep⋎u⌝))]);
a (rewrite_tac [⇒_elim (list_∀_elim [⌜Sep⋎u s (λ y⦁ y ∈⋎u t)⌝, ⌜t⌝] gsu_ext_axiom) (∧_intro (asm_rule ⌜Set⋎u (Sep⋎u s (λ y⦁ y ∈⋎u t))⌝)(asm_rule ⌜Set⋎u t⌝)) ]);
a (REPEAT strip_tac THEN asm_fc_tac[]);
val Sep⋎u_⊆_thm = save_pop_thm "Sep⋎u_⊆_thm";

add_rw_thms [Sep⋎u_⊆⋎u_thm] "'gsu-ax";
add_sc_thms [Sep⋎u_⊆⋎u_thm] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

\subsection{Galaxies}

A Galaxy is a transitive set closed under powerset formation, union and replacement.
The Ontology axioms ensures that every set is a member of some galaxy.
Here we define a galaxy constructor and establish some of its properties.

\subsubsection{Definition of Galaxy}

First we define the property of being a galaxy.

ⓈHOLCONST
│ ⦏galaxy⋎u⦎: 'a GSU → BOOL
├───────────
│ ∀s⦁
│	galaxy⋎u s ⇔ (∃x⦁ x ∈⋎u s)
│	∧ ∀t⦁ t ∈⋎u s
│		⇒ t ⊆⋎u s
│		∧ ℙ⋎u t ∈⋎u s
│		∧ ⋃⋎u t ∈⋎u s
│		∧ (∀rl⦁ ManyOne rl
│			⇒ RelIm⋎u rl t ⊆⋎u s
│			⇒ RelIm⋎u rl t ∈⋎u s)
■

=GFT
⦏galaxies⋎u_∃_thm⦎ =
	⊢ ∀s⦁ ∃g⦁ s ∈⋎u g ∧ galaxy⋎u g
=TEX

\ignore{
=SML
val galaxy⋎u_def = get_spec ⌜galaxy⋎u⌝;

set_goal([],⌜∀s⦁ ∃g⦁ s ∈⋎u g ∧ galaxy⋎u g⌝);
a (strip_tac THEN rewrite_tac [get_spec ⌜galaxy⋎u⌝]);
a (strip_asm_tac (∀_elim ⌜s⌝ UOntology_axiom));
a (∃_tac ⌜g⌝ THEN asm_rewrite_tac []);
a (strip_tac
	THEN1 (∃_tac ⌜s⌝ THEN strip_tac)
	THEN strip_tac THEN strip_tac);
a (spec_nth_asm_tac 2 ⌜t⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜Set⋎u (ℙ⋎u t)⌝ THEN1 rewrite_tac [ℙ⋎u_def]);
a (lemma_tac ⌜p = ℙ⋎u t⌝
	THEN1 (all_ufc_⇔_rewrite_tac [gsu_ext_axiom] THEN asm_rewrite_tac[ℙ⋎u_def]));
a (SYM_ASMS_T rewrite_tac);
(* *** Goal "2" *** *)
a (lemma_tac ⌜⋃⋎u t = u⌝
	THEN1 (rewrite_tac [⋃⋎u_def, ⋃⋎u_ext_thm]
		THEN strip_tac
		THEN asm_rewrite_tac[])
	);
a (asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (spec_nth_asm_tac 3 ⌜rl⌝);
(* *** Goal "3.1" *** *)
a (lemma_tac ⌜RelIm⋎u rl t = r⌝);
(* *** Goal "3.1.1" *** *)
a (lemma_tac ⌜Set⋎u(RelIm⋎u rl t)⌝ THEN1 (fc_tac[RelIm⋎u_def] THEN asm_rewrite_tac[]));
a (all_asm_ufc_⇔_rewrite_tac [gsu_ext_axiom]);
a (⇔_FC_T asm_rewrite_tac [get_spec ⌜RelIm⋎u⌝]);
(* *** Goal "3.1.2" *** *)
a (DROP_NTH_ASM_T 3 ante_tac THEN (SYM_ASMS_T rewrite_tac));
(* *** Goal "3.2" *** *)
a (lemma_tac ⌜RelIm⋎u rl t = r⌝);
(* *** Goal "3.2.1" *** *)
a (lemma_tac ⌜Set⋎u(RelIm⋎u rl t)⌝ THEN1 (fc_tac[RelIm⋎u_def] THEN asm_rewrite_tac[]));
a (all_asm_ufc_⇔_rewrite_tac [gsu_ext_axiom]);
a (⇔_FC_T asm_rewrite_tac [get_spec ⌜RelIm⋎u⌝]);
(* *** Goal "3.2.2" *** *)
a (asm_rewrite_tac[]);
val galaxies⋎u_∃_thm = save_pop_thm "galaxies⋎u_∃_thm";

set_goal([], ⌜∀g⦁ galaxy⋎u g ⇒ Set⋎u g⌝);
a (rewrite_tac [galaxy⋎u_def] THEN REPEAT strip_tac);
a (fc_tac [Set⋎u_axiom]);
val galaxy⋎u_Set⋎u_thm = save_pop_thm "galaxy⋎u_Set⋎u_thm";
=TEX
}%ignore

\subsubsection{Definition of Gx}

$Gx⋎u$ is a function which maps each set onto the smallest galaxy of which it is a member.

\ignore{
=SML
set_goal([],⌜∃ Gx⋎u⦁ ∀s t⦁ t ∈⋎u Gx⋎u s ⇔ ∀g⦁ galaxy⋎u g ∧ s ∈⋎u g ⇒ t ∈⋎u g⌝);
a (prove_∃_tac THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜s'⌝ galaxies⋎u_∃_thm));
a (∃_tac ⌜Sep⋎u g (λh⦁ ∀ i⦁ galaxy⋎u i ∧ s' ∈⋎u i ⇒ h ∈⋎u i)⌝);
a (rewrite_tac [get_spec ⌜Sep⋎u⌝]);
a (REPEAT strip_tac THEN_TRY all_asm_fc_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Gx⋎u⦎: 'a GSU → 'a GSU
├────────────
│ ∀s t⦁ t ∈⋎u Gx⋎u s ⇔ ∀g⦁ galaxy⋎u g ∧ s ∈⋎u g ⇒ t ∈⋎u g
■

Each set is in its smallest enclosing galaxy, which is of course a galaxy and is contained in any other galaxy of which that set is a member:

=GFT
⦏t_in_Gx⋎u_t_thm⦎ =		⊢ ∀ t⦁ t ∈⋎u Gx⋎u t
⦏tc∈⋎u_Gx⋎u_thm⦎ =		⊢ ∀ t⦁ t ∈⋎u⋏+ Gx⋎u t
⦏Set⋎u_Gx⋎u_thm⦎ =		⊢ ∀ x⦁ Set⋎u (Gx⋎u x)
=TEX

\ignore{
=SML
val Gx⋎u_def = get_spec ⌜Gx⋎u⌝;

set_goal([], ⌜∀t⦁ t ∈⋎u Gx⋎u t⌝);
a (prove_tac [Gx⋎u_def]);
val t_in_Gx⋎u_t_thm = save_pop_thm "t_in_Gx⋎u_t_thm";

val tc∈⋎u_Gx⋎u_thm = 
	let val [thm] = ufc_rule [tc∈⋎u_incr_thm] [t_in_Gx⋎u_t_thm]
	in save_thm("tc∈⋎u_Gx⋎u_thm", thm)
	end;

set_goal([], ⌜∀x⦁ Set⋎u (Gx⋎u x)⌝);
a (strip_tac);
a (lemma_tac ⌜x ∈⋎u (Gx⋎u x)⌝ THEN1 rewrite_tac [t_in_Gx⋎u_t_thm]);
a (fc_tac [Set⋎u_axiom]);
val Set⋎u_Gx⋎u_thm = save_pop_thm "Set⋎u_Gx⋎u_thm";
=TEX
}%ignore

=GFT
⦏Gx⋎u_⊆⋎u_galaxy⋎u⦎ =		⊢ ∀s g⦁ galaxy⋎u g ∧ s ∈⋎u g  ⇒ (Gx⋎u s) ⊆⋎u g
⦏galaxy⋎u_Gx⋎u⦎ =			⊢ ∀s⦁ galaxy⋎u (Gx⋎u s)
=TEX

\ignore{
=SML
set_goal([],⌜∀s g⦁ galaxy⋎u g ∧ s ∈⋎u g  ⇒ (Gx⋎u s) ⊆⋎u g⌝);
a (rewrite_tac[⊆⋎u_def, Gx⋎u_def]);
a (REPEAT strip_tac THEN all_asm_fc_tac[Set⋎u_axiom] THEN_TRY asm_rewrite_tac [Set⋎u_Gx⋎u_thm]);
val Gx⋎u_⊆⋎u_galaxy⋎u = save_pop_thm "Gx⋎u_⊆⋎u_galaxy⋎u";
=TEX

=SML
set_goal([],⌜∀s⦁ galaxy⋎u (Gx⋎u s)⌝);
a (rewrite_tac [galaxy⋎u_def]);
a (REPEAT_N 2 strip_tac
	THEN1 (∃_tac ⌜s⌝
		THEN rewrite_tac [Gx⋎u_def]
		THEN REPEAT strip_tac)
	THEN strip_tac
	THEN rewrite_tac [Gx⋎u_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [⊆⋎u_def, Gx⋎u_def]);
a (REPEAT strip_tac);
a (all_asm_fc_tac[]);
a (lemma_tac ⌜t ⊆⋎u g⌝ THEN1 (asm_fc_tac [galaxy⋎u_def] THEN asm_fc_tac[]));
a (POP_ASM_T ante_tac THEN rewrite_tac [⊆⋎u_def] THEN REPEAT strip_tac THEN asm_fc_tac[]);
(* *** Goal "2" *** *)
a (all_asm_fc_tac [get_spec ⌜galaxy⋎u⌝]);
a (all_asm_fc_tac [get_spec ⌜galaxy⋎u⌝]);
(* *** Goal "3" *** *)
a (all_asm_fc_tac [get_spec ⌜galaxy⋎u⌝]);
a (all_asm_fc_tac [get_spec ⌜galaxy⋎u⌝]);
(* *** Goal "4" *** *)
a (all_asm_fc_tac[]);
a (asm_fc_tac [list_∀_elim [⌜g⌝] (get_spec ⌜galaxy⋎u⌝)]);
a (REPEAT (all_asm_fc_tac [Gx⋎u_⊆⋎u_galaxy⋎u, ⊆⋎u_trans_thm]));
val galaxy⋎u_Gx⋎u = save_pop_thm "galaxy⋎u_Gx⋎u";
=TEX
}%ignore

\subsubsection{Galaxy Closure}

The galaxy axiom asserts that a Galaxy is a transitive set closed under construction of powersets, distributed union and replacement.
Galaxies are also closed under most other ways of constructing sets, and we need to demonstrate these facts systematically as the theory is developed.

ⓈHOLCONST
│ ⦏Transitive⋎u⦎ : 'a GSU → BOOL
├────────────
│ ∀s⦁ Transitive⋎u s ⇔ ∀e⦁ e ∈⋎u s ⇒ e ⊆⋎u s
■

=GFT
⦏galaxies⋎u_transitive_thm⦎ =	⊢ ∀s⦁ galaxy⋎u s ⇒ Transitive⋎u s
=TEX

\ignore{
=SML
val Transitive⋎u_def = get_spec ⌜Transitive⋎u⌝;

set_goal([],⌜∀s⦁ galaxy⋎u s ⇒ Transitive⋎u s⌝);
a (rewrite_tac [Transitive⋎u_def]);
a (REPEAT strip_tac
	THEN fc_tac [get_spec⌜galaxy⋎u⌝]
	THEN asm_fc_tac[]);
val galaxies⋎u_transitive_thm = save_pop_thm "galaxies⋎u_transitive_thm";
=TEX
}%ignore

=GFT
⦏G⋎uTrans_thm⦎ =		⊢ ∀ g⦁ galaxy⋎u g ⇒ (∀ s t⦁ s ∈⋎u g ∧ t ∈⋎u s ⇒ t ∈⋎u g)
⦏GClose⋎uℙ⋎u_thm⦎ =	⊢ ∀ g⦁ galaxy⋎u g ⇒ (∀ s⦁ s ∈⋎u g ⇒ ℙ⋎u s ∈⋎u g)
⦏GClose⋎u⋃_thm⦎ =	⊢ ∀ g⦁ galaxy⋎u g ⇒ (∀ s⦁ s ∈⋎u g ⇒ ⋃⋎u s ∈⋎u g)
⦏GClose⋎uSep⋎u_thm⦎ =	⊢ ∀ g⦁ galaxy⋎u g ⇒ (∀s⦁ s ∈⋎u g ⇒ ∀p⦁ Sep⋎u s p ∈⋎u g)
⦏GClose⋎u_⊆_thm⦎ =	⊢ ∀ g⦁ galaxy⋎u g ⇒ (∀ s⦁ s ∈⋎u g ⇒ (∀ t⦁ Set⋎u t ∧ t ⊆⋎u s ⇒ t ∈⋎u g))
=TEX

\ignore{
=SML
set_goal([],⌜∀g⦁ galaxy⋎u g ⇒ ∀s t⦁ s ∈⋎u g ∧ t ∈⋎u s ⇒ t ∈⋎u g⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜galaxy⋎u⌝]);
a (LEMMA_T ⌜s ⊆⋎u g⌝ ante_tac THEN1 asm_fc_tac[]);
a (rewrite_tac [⊆⋎u_def] THEN REPEAT strip_tac THEN all_asm_fc_tac[]);
val G⋎uTrans_thm = pop_thm ();

set_goal([],⌜∀g⦁ galaxy⋎u g ⇒ ∀s⦁ s ∈⋎u g ⇒ ℙ⋎u s ∈⋎u g⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜galaxy⋎u⌝]);
a (asm_fc_tac[]);
val GClose⋎uℙ⋎u_thm = pop_thm ();

set_goal([],⌜∀g⦁ galaxy⋎u g ⇒ ∀s⦁ s ∈⋎u g ⇒ ⋃⋎u s ∈⋎u g⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜galaxy⋎u⌝]);
a (asm_fc_tac[]);
val GClose⋎u⋃_thm = pop_thm ();

set_goal([],⌜∀g⦁ galaxy⋎u g ⇒ ∀s⦁ s ∈⋎u g ⇒ ∀p⦁ Sep⋎u s p ∈⋎u g⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜galaxy⋎u⌝]);
a (lemma_tac ⌜∃rl⦁ rl = λx y⦁ p x ∧ y = x⌝
	THEN1 prove_∃_tac);
a (lemma_tac ⌜ManyOne rl⌝
	THEN1 asm_rewrite_tac [get_spec ⌜ManyOne rl⌝]);
(* *** Goal "1" *** *)
a (REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜Sep⋎u s p = RelIm⋎u rl s ∧ RelIm⋎u rl s ∈⋎u g⌝);
(* *** Goal "2.1" *** *)
a (list_spec_nth_asm_tac 7 [⌜s⌝,⌜rl⌝]);
(* *** Goal "2.1.1" *** *)
a (SWAP_NTH_ASM_CONCL_T 1 discard_tac);
a (rewrite_tac[⊆⋎u_def]);
a (⇔_FC_T rewrite_tac [get_spec ⌜RelIm⋎u⌝]);
a (asm_rewrite_tac[]);
a (REPEAT strip_tac THEN asm_rewrite_tac[]);
a (SPEC_NTH_ASM_T 7 ⌜s⌝ ante_tac);
a (rewrite_tac[⊆⋎u_def]);
a (REPEAT strip_tac THEN asm_fc_tac[]);
(* *** Goal "2.1.2" *** *)
a (REPEAT strip_tac);
a (lemma_tac ⌜Set⋎u(Sep⋎u s p)⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜Set⋎u(RelIm⋎u rl s)⌝ THEN1 rewrite_tac[]);
a (all_ufc_⇔_rewrite_tac[gsu_ext_axiom]);
a (⇔_FC_T asm_rewrite_tac [get_spec ⌜RelIm⋎u⌝]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (once_asm_rewrite_tac[] THEN strip_tac);
val GClose⋎uSep⋎u_thm = save_pop_thm "GClose⋎uSep⋎u_thm";

set_goal([],⌜∀g⦁ galaxy⋎u g ⇒ ∀s⦁ s ∈⋎u g ⇒ ∀t⦁ Set⋎u t ∧ t ⊆⋎u s ⇒ t ∈⋎u g⌝);
a (REPEAT strip_tac);
a (fc_tac [G⋎uTrans_thm]);
a (fc_tac [galaxy⋎u_def]);
a (lemma_tac ⌜ℙ⋎u s ∈⋎u g⌝ THEN1 asm_ufc_tac[]);
a (LEMMA_T ⌜t ∈⋎u ℙ⋎u s⌝ asm_tac THEN1 asm_rewrite_tac[ℙ⋎u_thm]);
a (all_asm_fc_tac[]);
val GClose⋎u_⊆_thm = pop_thm ();
=TEX
}%ignore

=GFT
⦏GClose⋎u_fc_clauses⦎ =
   ⊢ ∀ g
     ⦁ galaxy⋎u g
         ⇒ (∀ s
         ⦁ s ∈⋎u g
             ⇒ ℙ⋎u s ∈⋎u g
               ∧ ⋃⋎u s ∈⋎u g
               ∧ (∀ p⦁ Sep⋎u s p ∈⋎u g)
               ∧ (∀ t⦁ Set⋎u t ∧ t ⊆⋎u s ⇒ t ∈⋎u g))
=TEX

\ignore{
=SML
set_goal([], ⌜∀g⦁ galaxy⋎u g ⇒ ∀s⦁ s ∈⋎u g
	⇒ ℙ⋎u s ∈⋎u g
	∧ ⋃⋎u s ∈⋎u g
	∧ (∀p⦁ Sep⋎u s p ∈⋎u g)
	∧ (∀t⦁ Set⋎u t ∧ t ⊆⋎u s ⇒ t ∈⋎u g)⌝);
a (REPEAT strip_tac
	THEN all_fc_tac [GClose⋎uℙ⋎u_thm, GClose⋎u⋃_thm, GClose⋎uSep⋎u_thm, GClose⋎u_⊆_thm]
	THEN asm_rewrite_tac[]);
val GClose⋎u_fc_clauses = save_pop_thm "GClose⋎u_fc_clauses";
=TEX
}%ignore

=GFT
⦏tc∈⋎u_lemma⦎ =		⊢ ∀ s e⦁ e ∈⋎u⋏+ s ⇒ (∀ t⦁ Transitive⋎u t ∧ s ⊆⋎u t ⇒ e ∈⋎u t)
⦏GClose⋎u_tc∈⋎u_thm⦎ =	⊢ ∀ s g⦁ galaxy⋎u g ⇒ s ∈⋎u⋏+ g ⇒ s ∈⋎u g
⦏GClose⋎u_tc∈⋎u_thm2⦎ =   ⊢ ∀ t s g⦁ galaxy⋎u g ∧ t ∈⋎u g ∧ s ∈⋎u⋏+ t ⇒ s ∈⋎u g
=TEX

\ignore{
=SML
set_goal([], ⌜∀s e⦁ e ∈⋎u⋏+ s ⇒ ∀t⦁ Transitive⋎u t ∧ s ⊆⋎u t ⇒ e ∈⋎u t⌝);
a (strip_tac THEN rewrite_tac [Transitive⋎u_def, get_spec ⌜$∈⋎u⋏+⌝]);
a (gsu_induction_tac ⌜s⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac[tc_decomp_thm, ⊆⋎u_def]);
(* *** Goal "1.1" *** *)
a (asm_fc_tac []);
(* *** Goal "1.2" *** *)
a (lemma_tac ⌜tc $∈⋎u z t⌝ THEN1 fc_tac [tc_incr_thm]);
a (spec_nth_asm_tac 8 ⌜z⌝);
a (spec_nth_asm_tac 1 ⌜s⌝);
(* *** Goal "1.2.1" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "1.2.2" *** *)
a (lemma_tac ⌜z ⊆⋎u t'⌝ THEN1 (REPEAT (asm_fc_tac[])));
a (all_asm_fc_tac[]);
val tc∈⋎u_lemma = pop_thm();

set_goal([], ⌜∀s g⦁ galaxy⋎u g ⇒ (s ∈⋎u⋏+ g ⇒ s ∈⋎u g)⌝);
a (REPEAT strip_tac);
a (fc_tac [galaxies⋎u_transitive_thm]);
a (fc_tac [tc∈⋎u_lemma]);
a (asm_fc_tac []);
a (POP_ASM_T ante_tac THEN rewrite_tac[⊆⋎u_refl_thm]);
val GClose⋎u_tc∈⋎u_thm = save_pop_thm "GClose⋎u_tc∈⋎u_thm";

set_goal([], ⌜∀t s g⦁ galaxy⋎u g ∧ t ∈⋎u g ∧ s ∈⋎u⋏+ t ⇒ s ∈⋎u g⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜t ∈⋎u⋏+ g⌝ THEN1 fc_tac [tc∈⋎u_incr_thm]);
a (lemma_tac ⌜s ∈⋎u⋏+ g⌝ THEN1 all_fc_tac [tc∈⋎u_trans_thm]);
a (all_fc_tac[GClose⋎u_tc∈⋎u_thm]);
val GClose⋎u_tc∈⋎u_thm2 = save_pop_thm "GClose⋎u_tc∈⋎u_thm2";
=TEX
}%ignore

=GFT
⦏Gx⋎u_mono_thm⦎ =		⊢ ∀s t⦁ s ⊆⋎u t ⇒ Gx⋎u s ⊆⋎u Gx⋎u t
⦏Gx⋎u_mono_thm2⦎ =		⊢ ∀s t⦁ s ∈⋎u t ⇒ Gx⋎u s ⊆⋎u Gx⋎u t
⦏t_⊆⋎u_Gx⋎u_t_thm⦎ =	⊢ ∀ t⦁ t ⊆⋎u Gx⋎u t
⦏Gx⋎u_mono_thm3⦎ =		⊢ ∀ s t⦁ s ⊆⋎u t ⇒ s ⊆⋎u Gx⋎u t
⦏Gx⋎u_mono_thm4⦎ =		⊢ ∀ s t⦁ Set⋎u s ∧ s ⊆⋎u t ⇒ s ∈⋎u Gx⋎u t
=TEX

=GFT
⦏Gx⋎u_trans_thm⦎ =	⊢ ∀ s⦁ Transitive⋎u (Gx⋎u s)
⦏Gx⋎u_trans_thm2⦎ =	⊢ ∀ s t⦁ s ∈⋎u t ⇒ s ∈⋎u Gx⋎u t
⦏Gx⋎u_trans_thm3⦎ =	⊢ ∀ s t u⦁ s ∈⋎u t ∧ t ∈⋎u Gx⋎u u ⇒ s ∈⋎u Gx⋎u u
⦏Gx⋎u_trans_thm4⦎ =	⊢ ∀ s t u⦁ s ∈⋎u⋏+ t ∧ t ∈⋎u Gx⋎u u ⇒ s ∈⋎u Gx⋎u u
⦏Gx⋎u_trans_thm5⦎ =	⊢ ∀ s t u⦁ s ∈⋎u⋏+ t ⇒ s ∈⋎u Gx⋎u t
=TEX

=GFT
=TEX

\ignore{
=SML
set_goal([], ⌜∀s t⦁ Set⋎u s ∧ Set⋎u t ∧ s ⊆⋎u t ⇒ Gx⋎u s ⊆⋎u Gx⋎u t⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜galaxy⋎u (Gx⋎u t)⌝ THEN1 rewrite_tac [galaxy⋎u_Gx⋎u]);
a (lemma_tac ⌜s ∈⋎u (Gx⋎u t)⌝);
(* *** Goal "1" *** *)
a (lemma_tac ⌜t ∈⋎u Gx⋎u t⌝ THEN1 rewrite_tac [t_in_Gx⋎u_t_thm]);
a (all_fc_tac [GClose⋎uℙ⋎u_thm]);
a (LEMMA_T ⌜s ∈⋎u ℙ⋎u t⌝ asm_tac THEN1 asm_rewrite_tac[ℙ⋎u_def]);
a (all_ufc_tac [G⋎uTrans_thm]);
(* *** Goal "2" *** *)
a (fc_tac [Gx⋎u_⊆⋎u_galaxy⋎u]);
a (asm_fc_tac[]);
val Gx⋎u_mono_thm = save_pop_thm "Gx⋎u_mono_thm";

set_goal([], ⌜∀s t⦁ s ∈⋎u t ⇒ Gx⋎u s ⊆⋎u Gx⋎u t⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜galaxy⋎u (Gx⋎u t)⌝ THEN1 rewrite_tac [galaxy⋎u_Gx⋎u]);
a (fc_tac [galaxies⋎u_transitive_thm]);
a (fc_tac [Transitive⋎u_def]);
a (lemma_tac ⌜t ∈⋎u Gx⋎u t⌝ THEN1 rewrite_tac[t_in_Gx⋎u_t_thm]);
a (ASM_FC_T (MAP_EVERY(strip_asm_tac o (once_rewrite_rule [⊆⋎u_def]))) [] 
	THEN asm_fc_tac[]);
a (all_fc_tac [Gx⋎u_⊆⋎u_galaxy⋎u]);
val Gx⋎u_mono_thm2 = save_pop_thm "Gx⋎u_mono_thm2";

set_goal([], ⌜∀s⦁ Transitive⋎u (Gx⋎u s)⌝);
a (strip_tac);
a (lemma_tac ⌜galaxy⋎u (Gx⋎u s)⌝ THEN1 rewrite_tac [galaxy⋎u_Gx⋎u]);
a (fc_tac [galaxies⋎u_transitive_thm]);
val Gx⋎u_trans_thm = save_pop_thm "Gx⋎u_trans_thm";

set_goal([], ⌜∀t⦁ t ⊆⋎u Gx⋎u t⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜t ∈⋎u Gx⋎u t⌝ THEN1 rewrite_tac [t_in_Gx⋎u_t_thm]);
a (fc_tac [rewrite_rule [Transitive⋎u_def]Gx⋎u_trans_thm]);
val t_⊆⋎u_Gx⋎u_t_thm = save_pop_thm "t_⊆⋎u_Gx⋎u_t_thm";

set_goal([], ⌜∀s t⦁ s ⊆⋎u t ⇒ s ⊆⋎u Gx⋎u t⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜t ⊆⋎u Gx⋎u t⌝ THEN1 rewrite_tac [t_⊆⋎u_Gx⋎u_t_thm]);
a (all_fc_tac [⊆⋎u_trans_thm]);
val Gx⋎u_mono_thm3 = save_pop_thm "Gx⋎u_mono_thm3";

set_goal([], ⌜∀s t⦁ Set⋎u s ∧ s ⊆⋎u t ⇒ s ∈⋎u Gx⋎u t⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜galaxy⋎u (Gx⋎u t)⌝ THEN1 rewrite_tac[galaxy⋎u_Gx⋎u]);
a (lemma_tac ⌜t ∈⋎u Gx⋎u t⌝ THEN1 rewrite_tac[t_in_Gx⋎u_t_thm]);
a (all_ufc_tac [GClose⋎u_fc_clauses]);
val Gx⋎u_mono_thm4 = save_pop_thm "Gx⋎u_mono_thm4";

set_goal([], ⌜∀s t⦁ s ∈⋎u t ⇒ s ∈⋎u Gx⋎u t⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜t ∈⋎u Gx⋎u t⌝ THEN1 rewrite_tac [t_in_Gx⋎u_t_thm]);
a (lemma_tac ⌜Transitive⋎u (Gx⋎u t)⌝ THEN1 rewrite_tac [Gx⋎u_trans_thm]);
a (ALL_FC_T (MAP_EVERY (fn x => fc_tac [rewrite_rule [⊆⋎u_def] x]))
	[Transitive⋎u_def]);
val Gx⋎u_trans_thm2 = save_pop_thm "Gx⋎u_trans_thm2";

set_goal([], ⌜∀s t u⦁ s ∈⋎u t ∧ t ∈⋎u Gx⋎u u ⇒ s ∈⋎u Gx⋎u u⌝);
a (REPEAT strip_tac);
a (LEMMA_T ⌜Transitive⋎u (Gx⋎u u)⌝ ante_tac THEN1 rewrite_tac [Gx⋎u_trans_thm]);
a (rewrite_tac [Transitive⋎u_def]
	THEN STRIP_T (fn x => FC_T (MAP_EVERY ante_tac) [x]));
a (rewrite_tac [⊆⋎u_def] THEN STRIP_T (fn x => fc_tac [x]));
val Gx⋎u_trans_thm3 = save_pop_thm "Gx⋎u_trans_thm3";

set_goal([], ⌜∀s t u⦁ s ∈⋎u⋏+ t ∧ t ∈⋎u Gx⋎u u ⇒ s ∈⋎u Gx⋎u u⌝);
a (REPEAT strip_tac);
a (fc_tac [tc∈⋎u_incr_thm]);
a (all_fc_tac [tc∈⋎u_trans_thm]);
a (lemma_tac ⌜galaxy⋎u (Gx⋎u u)⌝ THEN1 rewrite_tac[galaxy⋎u_Gx⋎u]);
a (all_fc_tac [GClose⋎u_tc∈⋎u_thm]);
val Gx⋎u_trans_thm4 = save_pop_thm "Gx⋎u_trans_thm4";

set_goal([], ⌜∀s t u⦁ s ∈⋎u⋏+ t ⇒ s ∈⋎u Gx⋎u t⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜galaxy⋎u (Gx⋎u t)⌝ THEN1 rewrite_tac[galaxy⋎u_Gx⋎u]);
a (strip_asm_tac (∀_elim ⌜t⌝ t_in_Gx⋎u_t_thm));
a (all_fc_tac [Gx⋎u_trans_thm4]);
val Gx⋎u_trans_thm5 = save_pop_thm "Gx⋎u_trans_thm5";
=TEX
}%ignore

\subsubsection{The Empty Set}

We can now prove that there is an empty set.

\ignore{
=SML
set_goal([], ⌜∃ ∅⋎u⦁ Set⋎u ∅⋎u ∧ ∀s⦁ ¬ s ∈⋎u ∅⋎u⌝);
a (∃_tac ⌜Sep⋎u (εs:'a GSU⦁ T) (λx:'a GSU⦁ F)⌝
	THEN rewrite_tac [get_spec⌜Sep⋎u⌝]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

So we define $⌜∅⋎u⌝$ as the empty set:

ⓈHOLCONST
│ ⦏∅⋎u⦎ : 'a GSU
├
│ Set⋎u ∅⋎u ∧ ∀s⦁ ¬ s ∈⋎u ∅⋎u
■

and the empty set is a member of every galaxy:

=GFT
⦏∅⋎u_thm⦎ =				⊢ ∀ s⦁ ¬ s ∈⋎u ∅⋎u
⦏tc∈⋎u_∅⋎u_thm⦎ =			⊢ ∀ x⦁ ¬ x ∈⋎u⋏+ ∅⋎u
⦏X∅⋎u_thm⦎ =			⊢ ∀ x⦁ ¬ x ∈ X⋎u ∅⋎u
⦏eq_∅⋎u_¬∈⋎u_thm⦎ =		⊢ ∀ x⦁ x =⋎u ∅⋎u ⇒ (∀ y⦁ ¬ y ∈⋎u x)
⦏eq_∅⋎u_¬tc∈⋎u_thm⦎ =		⊢ ∀ x⦁ x =⋎u ∅⋎u ⇒ (∀ y⦁ ¬ y ∈⋎u⋏+ x)
⦏eq⋎u_eq_∅⋎u_thm⦎ =		⊢ ∀ α⦁ Set⋎u α ∧ α =⋎u ∅⋎u ⇒ α = ∅⋎u
=TEX
=GFT
⦏Set⋎u_∅⋎u_thm⦎ =		⊢ Set⋎u ∅⋎u
⦏G∅⋎uC⦎ =				⊢ ∀ g⦁ galaxy⋎u g ⇒ ∅⋎u ∈⋎u g
⦏∅⋎u⊆⋎u_thm⦎ =			⊢ ∀ s⦁ ∅⋎u ⊆⋎u s
⦏⋃⋎u∅⋎u_thm⦎ =			⊢ ⋃⋎u ∅⋎u = ∅⋎u
=TEX
=GFT
⦏∈⋎u_not_empty_thm⦎ =	⊢ ∀ m n⦁ m ∈⋎u n ⇒ ¬ n = ∅⋎u
⦏∅⋎u_∈⋎u_galaxy⋎u_thm⦎ =	⊢ ∀ x⦁ galaxy⋎u x ⇒ ∅⋎u ∈⋎u x
⦏∅⋎u_∈⋎u_Gx⋎u_thm⦎ =		⊢ ∀ x⦁ ∅⋎u ∈⋎u Gx⋎u x
=TEX

\ignore{
=SML
val ∅⋎u_def = get_spec ⌜∅⋎u⌝;
val ∅⋎u_thm = ∧_right_elim ∅⋎u_def;

set_goal([], ⌜∀ x⦁ ¬ x ∈⋎u⋏+ ∅⋎u⌝);
a (REPEAT ∀_tac THEN once_rewrite_tac [tc∈⋎u_cases_thm]);
a (rewrite_tac[∅⋎u_thm]);
val tc∈⋎u_∅⋎u_thm = save_pop_thm "tc∈⋎u_∅⋎u_thm";

val X∅⋎u_thm = prove_thm ("X∅⋎u_thm", ⌜∀x⦁ ¬ x ∈ X⋎u ∅⋎u⌝, PC_T1 "hol1" rewrite_tac[X⋎u_def, ∅⋎u_thm]);

set_goal([], ⌜∀ x⦁ x =⋎u ∅⋎u ⇒ ∀y⦁ ¬ y ∈⋎u x⌝);
a (rewrite_tac [get_spec ⌜$=⋎u⌝, get_spec ⌜X⋎u⌝, sets_ext_clauses, ∅⋎u_thm] THEN PC_T1 "hol1" rewrite_tac[]);
val eq_∅⋎u_¬∈⋎u_thm = save_pop_thm "eq_∅⋎u_¬∈⋎u_thm";

set_goal([], ⌜∀ x⦁ x =⋎u ∅⋎u ⇒ ∀y⦁ ¬ y ∈⋎u⋏+ x⌝);
a (contr_tac);
a (fc_tac [tc∈⋎u_decomp_thm, eq_∅⋎u_¬∈⋎u_thm]
	THEN asm_ufc_tac[]);
val eq_∅⋎u_¬tc∈⋎u_thm = save_pop_thm "eq_∅⋎u_¬tc∈⋎u_thm";

set_goal([], ⌜∀α⦁ Set⋎u α ∧ α =⋎u ∅⋎u ⇒ α = ∅⋎u⌝);
a (rewrite_tac [get_spec ⌜$=⋎u⌝, get_spec ⌜X⋎u⌝, sets_ext_clauses]);
a (PC_T1 "hol1" rewrite_tac [] THEN REPEAT strip_tac);
a (asm_tac (∧_left_elim ∅⋎u_def));
a (all_ufc_⇔_rewrite_tac [gsu_ext_axiom]);
a (asm_rewrite_tac[]);
val eq⋎u_eq_∅⋎u_thm = save_pop_thm "eq⋎u_eq_∅⋎u_thm";

val Set⋎u_∅⋎u_thm = ∧_left_elim ∅⋎u_def;

add_rw_thms [tc∈⋎u_∅⋎u_thm, ∅⋎u_thm, X∅⋎u_thm, Set⋎u_∅⋎u_thm, galaxy⋎u_Gx⋎u, Set⋎u_Gx⋎u_thm] "'gsu-ax";
add_sc_thms [tc∈⋎u_∅⋎u_thm, ∅⋎u_thm, X∅⋎u_thm, Set⋎u_∅⋎u_thm, galaxy⋎u_Gx⋎u, Set⋎u_Gx⋎u_thm] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];

set_goal([],⌜∀g:'a GSU⦁ galaxy⋎u g ⇒ ∅⋎u ∈⋎u g⌝);
a (REPEAT strip_tac);
a (fc_tac [GClose⋎uSep⋎u_thm, get_spec ⌜galaxy⋎u⌝]);
a (list_spec_nth_asm_tac 1 [⌜x⌝,⌜λx:'a GSU⦁ F⌝]);
a (lemma_tac ⌜Set⋎u (∅⋎u:'a GSU) ∧ Set⋎u (Sep⋎u x (λ x:'a GSU⦁ F))⌝ THEN1 rewrite_tac[Set⋎u_∅⋎u_thm]);
a (lemma_tac ⌜∅⋎u = Sep⋎u x (λ x⦁ F)⌝
	THEN1 (all_ufc_⇔_rewrite_tac [gsu_ext_axiom]));
a (asm_rewrite_tac []);
val G∅⋎uC = save_pop_thm "G∅⋎uC";

val ∅⋎u⊆⋎u_thm = save_thm ("∅⋎u⊆⋎u_thm",
	prove_rule [get_spec ⌜∅⋎u⌝, ⊆⋎u_def]
	⌜∀s:'a GSU⦁ ∅⋎u ⊆⋎u s⌝);

set_goal([], ⌜⋃⋎u (∅⋎u:'a GSU) = ∅⋎u:'a GSU⌝);
a (lemma_tac ⌜Set⋎u (⋃⋎u (∅⋎u:'a GSU)) ∧ Set⋎u (∅⋎u:'a GSU)⌝ THEN1 rewrite_tac[Set⋎u_∅⋎u_thm]);
a (all_ufc_⇔_rewrite_tac [gsu_ext_axiom]);
val ⋃⋎u∅⋎u_thm = pop_thm ();

set_goal ([], ⌜∀m n⦁ m ∈⋎u n ⇒ ¬ n = ∅⋎u⌝);
a (contr_tac);
a (DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[]);
val ∈⋎u_not_empty_thm = save_pop_thm "∈⋎u_not_empty_thm";

set_goal ([], ⌜∀x:'a GSU⦁ galaxy⋎u x ⇒ ∅⋎u ∈⋎u x⌝);
a (REPEAT strip_tac THEN fc_tac [GClose⋎u_fc_clauses]);
a (fc_tac [get_spec ⌜galaxy⋎u⌝]);
a (asm_ufc_tac[]);
a (SPEC_NTH_ASM_T 5 ⌜λx:'a GSU⦁F⌝ ante_tac);
a (lemma_tac ⌜∅⋎u ⊆⋎u x'⌝ THEN1 rewrite_tac [∅⋎u⊆⋎u_thm]);
a (lemma_tac ⌜Set⋎u (∅⋎u)⌝ THEN1 rewrite_tac[Set⋎u_∅⋎u_thm]);
a (all_fc_tac[Sep⋎u_⊆_thm]);
a (lemma_tac ⌜(λ x:'a GSU⦁ F) = (CombC $∈⋎u ∅⋎u)⌝
	THEN1 (rewrite_tac [ext_thm, get_spec ⌜CombC⌝, ∅⋎u_thm]));
a (rewrite_tac [asm_rule ⌜(λ x:'a GSU⦁ F) = CombC $∈⋎u ∅⋎u⌝, asm_rule ⌜Sep⋎u x' (CombC $∈⋎u ∅⋎u) = ∅⋎u⌝]);
val ∅⋎u_∈⋎u_galaxy⋎u_thm = save_pop_thm "∅⋎u_∈⋎u_galaxy⋎u_thm";

set_goal ([], ⌜∀x⦁ ∅⋎u ∈⋎u Gx⋎u x⌝);
a (asm_tac galaxy⋎u_Gx⋎u THEN ufc_tac [∅⋎u_∈⋎u_galaxy⋎u_thm]);
val ∅⋎u_∈⋎u_Gx⋎u_thm = save_pop_thm "∅⋎u_∈⋎u_Gx⋎u_thm";

add_pc_thms "'gsu-ax" (map get_spec [⌜ℙ⋎u⌝, ⌜⋃⋎u⌝] @ [∅⋎u⊆⋎u_thm, ⋃⋎u∅⋎u_thm, ∅⋎u_thm]);
add_rw_thms [] "'gsu-ax";
add_sc_thms [] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

It is sometimes useful to force a value to a set having the same extension.
The following function is the identity over sets and maps all urelements to the empty set.

ⓈHOLCONST
│ ⦏set⋎u⦎ : 'a GSU → 'a GSU
├
│ ∀x⦁ set⋎u x = if Set⋎u x then x else ∅⋎u
■

=GFT
⦏Set⋎u_set⋎u_thm⦎ =
	⊢ ∀ s⦁ Set⋎u (set⋎u s)
⦏set⋎u_eq⋎u_thm⦎ =
	⊢ ∀ s⦁ set⋎u s =⋎u s
⦏set⋎u_eq⋎u_thm2⦎ =
	⊢ ∀ s u⦁ u ∈⋎u set⋎u s ⇔ u ∈⋎u s
⦏set⋎u_fc_thm⦎ =
	⊢ ∀ s⦁ Set⋎u s ⇒ set⋎u s = s
=TEX

\ignore{
=SML
val set⋎u_def = get_spec ⌜set⋎u⌝;

set_goal([], ⌜∀s⦁ Set⋎u (set⋎u s)⌝);
a (∀_tac THEN rewrite_tac[set⋎u_def]);
a (cond_cases_tac ⌜Set⋎u s⌝);
val Set⋎u_set⋎u_thm = save_pop_thm "Set⋎u_set⋎u_thm";

set_goal([], ⌜∀s⦁ set⋎u s =⋎u s⌝);
a (strip_tac THEN rewrite_tac[set⋎u_def]);
a (cond_cases_tac ⌜Set⋎u s⌝);
a (rewrite_tac[eq⋎u_ext_thm]);
a (swap_nth_asm_concl_tac 1);
a (fc_tac [Set⋎u_axiom]);
val set⋎u_eq⋎u_thm = save_pop_thm "set⋎u_eq⋎u_thm";

val set⋎u_eq⋎u_thm2 = save_thm ("set⋎u_eq⋎u_thm2", pure_rewrite_rule [eq⋎u_ext_thm] set⋎u_eq⋎u_thm);

set_goal([], ⌜∀s⦁ Set⋎u s ⇒ set⋎u s = s⌝);
a (REPEAT strip_tac THEN asm_rewrite_tac[set⋎u_def]);
val set⋎u_fc_thm = save_pop_thm "set⋎u_fc_thm";
=TEX
}%ignore

\subsection{Functional Replacement}

The more convenient form of replacement which takes a function rather than a relation (and hence needs no ``ManyOne'' caveat) is introduced here.

\subsubsection{Introduction}

Though a functional formulation of replacement is most convenient for most applications, it has a number of small disadvantages which have persuaded me to stay closer to the traditional formulation of replacement in terms of relations.
The more convenient functional version will then be introduced by definition (so if you don't know what I'm talking about, look forward to compare the two versions).

For the record the disadvantages of the functional one (if used as an axiom) are:

\begin{enumerate}
\item It can't be used to prove the existence of the empty set.
\item When used to define separation it requires the axiom of choice.
\end{enumerate}

Now we prove a more convenient version of replacement which takes a HOL function rather than a relation as its argument.
It states that the image of any set under a function is also a set.

\ignore{
=SML
set_goal([],⌜∃Imagep⋎u⦁ ∀f:'a GSU → 'a GSU⦁ ∀s: 'a GSU⦁ 
	Set⋎u (Imagep⋎u f s) ∧ (∀x⦁ x ∈⋎u Imagep⋎u f s ⇔ ∃e⦁ e ∈⋎u s ∧ x = f e)⌝);
a (prove_∃_tac THEN REPEAT strip_tac);
a (lemma_tac ⌜∃fr⦁ fr = λx y⦁ y = f' x⌝ THEN1 prove_∃_tac);
a (lemma_tac ⌜ManyOne fr⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜ManyOne⌝]
		THEN REPEAT strip_tac
		THEN asm_rewrite_tac[]));
a (∃_tac ⌜RelIm⋎u fr s'⌝);
a (⇔_FC_T asm_rewrite_tac [get_spec ⌜RelIm⋎u⌝]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

$⌜Imagep⋎u\ f\ s⌝$ is the image of $s$ through $f$.

ⓈHOLCONST
│ ⦏Imagep⋎u⦎ : ('a GSU → 'a GSU) → 'a GSU → 'a GSU
├───────────
│ ∀f s⦁ Set⋎u(Imagep⋎u f s) ∧ ∀x⦁ x ∈⋎u Imagep⋎u f s ⇔ ∃e⦁ e ∈⋎u s ∧ x = f e
■

This is what computer scientists might call Map.

=GFT
⦏Imagep⋎u_∅⋎u_thm⦎ =
	⊢ ∀ f⦁ Imagep⋎u f ∅⋎u = ∅⋎u
⦏tc∈⋎u_Imagep⋎u_thm⦎ =
	⊢ ∀ f s x⦁ x ∈⋎u⋏+ Imagep⋎u f s ⇔ (∃ y⦁ y ∈⋎u s ∧ (x = f y ∨ x ∈⋎u⋏+ f y))
=TEX

\ignore{
=SML
val Imagep⋎u_def = get_spec ⌜Imagep⋎u⌝;

val Imagep⋎u_thm = tac_proof(([], ⌜∀f s x⦁ x ∈⋎u Imagep⋎u f s ⇔ ∃e⦁ e ∈⋎u s ∧ x = f e⌝), rewrite_tac [Imagep⋎u_def]);

val Set⋎uImagep⋎u_thm = tac_proof(([], ⌜∀f s⦁ Set⋎u(Imagep⋎u f s)⌝), rewrite_tac [Imagep⋎u_def]);

add_rw_thms [Imagep⋎u_def, Set⋎u_set⋎u_thm, set⋎u_eq⋎u_thm, set⋎u_eq⋎u_thm2] "'gsu-ax";
add_sc_thms [Imagep⋎u_def, Set⋎u_set⋎u_thm, set⋎u_eq⋎u_thm, set⋎u_eq⋎u_thm2] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];

set_goal([], ⌜∀f⦁ Imagep⋎u f ∅⋎u = ∅⋎u⌝);
a (strip_tac THEN gsu_ext_tac);
a (rewrite_tac [Imagep⋎u_def]);
val Imagep⋎u_∅⋎u_thm = save_pop_thm "Imagep⋎u_∅⋎u_thm";

set_goal([], ⌜∀f s x⦁ x ∈⋎u⋏+ Imagep⋎u f s ⇔ ∃y⦁ y ∈⋎u s ∧ (x = f y ∨ x ∈⋎u⋏+ f y)⌝);
a (REPEAT ∀_tac);
a (rewrite_tac [once_rewrite_conv [tc∈⋎u_cases_thm] ⌜x ∈⋎u⋏+ Imagep⋎u f s⌝]);
a (LEMMA_T ⌜(∃ z⦁ x ∈⋎u⋏+ z ∧ (∃ e⦁ e ∈⋎u s ∧ z = f e)) ⇔ (∃ e⦁ e ∈⋎u s ∧ x ∈⋎u⋏+ f e)⌝ rewrite_thm_tac
	THEN prove_tac[]);
a (prove_tac[]);
a (∃_tac ⌜e⌝ THEN SYM_ASMS_T rewrite_tac);
val tc∈⋎u_Imagep⋎u_thm = save_pop_thm "tc∈⋎u_Imagep⋎u_thm";

add_rw_thms [Imagep⋎u_∅⋎u_thm] "'gsu-ax";
add_sc_thms [Imagep⋎u_∅⋎u_thm] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

Replacement is used later for definitions by transfinite induction.


=GFT
⦏Imagep⋎u_comp_thm⦎ =
	⊢ ∀ s f g⦁ Imagep⋎u f (Imagep⋎u g s) = Imagep⋎u (f o g) s
=TEX

\ignore{
=SML
set_goal([], ⌜∀s f g⦁ Imagep⋎u f (Imagep⋎u g s) = Imagep⋎u (f o g) s⌝);
a (REPEAT ∀_tac THEN gsu_ext_tac THEN rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜e''⌝ THEN asm_rewrite_tac[get_spec ⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝]);
(* *** Goal "2" *** *)
a (∃_tac ⌜g e'⌝ THEN asm_rewrite_tac[get_spec ⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝]);
a (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[]);
val Imagep⋎u_comp_thm = save_pop_thm "Imagep⋎u_comp_thm";

add_rw_thms [Imagep⋎u_comp_thm] "'gsu-ax";
add_sc_thms [Imagep⋎u_comp_thm] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

\subsubsection{Galaxy Closure}

We now show that galaxies are closed under $Imagep⋎u$.

=GFT
⦏GImagep⋎uC⦎ =	⊢ ∀g⦁ galaxy⋎u g ⇒ ∀s⦁ s ∈⋎u g
				⇒ ∀f⦁ Imagep⋎u f s ⊆⋎u g ⇒ Imagep⋎u f s ∈⋎u g
=IGN
⦏GImagep⋎uC2⦎ =	⊢ ∀ s t⦁ s ∈⋎u Gx⋎u t ⇒ (∀ f⦁ Imagep⋎u f s ⊆⋎u Gx⋎u t
				⇒ Imagep⋎u f s ∈⋎u Gx⋎u t)
⦏GImagep⋎uC3⦎ = ⊢ ∀ f s t⦁ s ∈⋎u Gx⋎u t ⇒ Imagep⋎u f s ⊆⋎u Gx⋎u t ⇒ Imagep⋎u f s ∈⋎u Gx⋎u t
=TEX

\ignore{
=SML
set_goal([],⌜∀g⦁ galaxy⋎u g
	⇒ ∀s⦁ s ∈⋎u g
	⇒ ∀f⦁ Imagep⋎u f s ⊆⋎u g
	⇒ Imagep⋎u f s ∈⋎u g⌝);
a (REPEAT_N 5 strip_tac);
a (lemma_tac ⌜∃fr⦁ fr = λx y⦁ y = f x⌝ THEN1 prove_∃_tac);
a (lemma_tac ⌜ManyOne fr⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜ManyOne⌝]
		THEN REPEAT strip_tac
		THEN asm_rewrite_tac[]));
a (lemma_tac ⌜Imagep⋎u f s = RelIm⋎u fr s⌝);
(* *** Goal "1" *** *)
a (lemma_tac ⌜Set⋎u(Imagep⋎u f s) ∧ Set⋎u(RelIm⋎u fr s)⌝ THEN1 rewrite_tac[]);
a (all_asm_ufc_⇔_rewrite_tac [gsu_ext_axiom]);
a (⇔_FC_T pure_once_rewrite_tac [get_spec ⌜RelIm⋎u⌝]);
a (asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a (once_asm_rewrite_tac[]);
a (fc_tac[get_spec ⌜galaxy⋎u⌝]);
a (list_spec_nth_asm_tac 5 [⌜s⌝,⌜fr⌝]
	THEN asm_rewrite_tac[]);
val GImagep⋎uC = save_pop_thm "GImagep⋎uC";
=IGN
set_goal([],⌜∀s t⦁ s ∈⋎u Gx⋎u t
	⇒ ∀f⦁ Imagep⋎u f s ⊆⋎u Gx⋎u t
	⇒ Imagep⋎u f s ∈⋎u Gx⋎u t⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜galaxy⋎u (Gx⋎u t)⌝ THEN1 rewrite_tac[galaxy⋎u_Gx⋎u]);
a (strip_asm_tac (∀_elim ⌜Gx⋎u t⌝ GImagep⋎uC));
a (all_asm_fc_tac[]);
val GImagep⋎uC2 = save_pop_thm "GImagep⋎uC2";

set_goal([],⌜∀f s t⦁ s ∈⋎u Gx⋎u t
	⇒ Imagep⋎u f s ⊆⋎u Gx⋎u t
	⇒ Imagep⋎u f s ∈⋎u Gx⋎u t⌝);
a (REPEAT strip_tac THEN all_fc_tac[GImagep⋎uC2]);
val GImagep⋎uC3 = save_pop_thm "GImagep⋎uC3";
=TEX
}%ignore

\subsection{Pair and Unit sets}

$Pair⋎u$ is defined using replacement, and $Unit⋎u$ using $Pair⋎u$.

\ignore{
=SML
set_goal([],⌜∃Pair⋎u⦁ ∀s t:'a GSU⦁ Set⋎u (Pair⋎u s t) ∧ 
	∀e:'a GSU⦁ e ∈⋎u Pair⋎u s t ⇔ e = s ∨ e = t⌝);
a (∃_tac ⌜λs t:'a GSU⦁Imagep⋎u (λx:'a GSU⦁ if x = ∅⋎u then s else t) (ℙ⋎u (ℙ⋎u ∅⋎u))⌝
	THEN rewrite_tac[⊆⋎u_def]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (asm_ante_tac ⌜¬ e = s⌝);
a (asm_rewrite_tac[]);
a (cases_tac ⌜e'=∅⋎u⌝
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜∅⋎u⌝
	THEN prove_tac
	[⊆⋎u_def]);
(* *** Goal "3" *** *)
a (∃_tac ⌜ℙ⋎u (∅⋎u:'a GSU)⌝ THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac [ℙ⋎u_def]);
(* *** Goal "3.1" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac[⊆⋎u_def]);
a (strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "3.2" *** *)
a (lemma_tac ⌜Set⋎u (∅⋎u:'a GSU)⌝ THEN1 rewrite_tac[]);
a (LEMMA_T ⌜Set⋎u (ℙ⋎u (∅⋎u:'a GSU))⌝ asm_tac THEN1 rewrite_tac[]);
a (LEMMA_T ⌜¬ ℙ⋎u ∅⋎u = ∅⋎u⌝ rewrite_thm_tac THEN1 (all_asm_ufc_⇔_rewrite_tac[gsu_ext_axiom]
		THEN_TRY rewrite_tac [⊆⋎u_def]));
a (strip_tac);
a (∃_tac ⌜∅⋎u:'a GSU⌝ THEN rewrite_tac[]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

$Pair⋎u$ can be defined as the image of some two element set under a function defined by a conditional.
A suitable two element set can be constructed from the empty set using the powerset construction a couple of times.
However, having proven that this can be done (details omitted), we can introduce the pair constructor by conservative extension as follows.
(the ProofPower tool shows that it has accepted my proof by putting this extension into the "definitions" section of the theory listing).

ⓈHOLCONST
│ ⦏Pair⋎u⦎ : 'a GSU → 'a GSU → 'a GSU
├────────────
│ ∀s t:'a GSU⦁ Set⋎u (Pair⋎u s t) ∧ ∀e:'a GSU⦁ e ∈⋎u Pair⋎u s t ⇔ e = s ∨ e = t	
■

=GFT
⦏Pair⋎u_∈⋎u_thm⦎ =		⊢ ∀ x y⦁ x ∈⋎u Pair⋎u x y ∧ y ∈⋎u Pair⋎u x y
⦏Pair⋎u_tc∈⋎u_thm⦎ =	⊢ ∀ s t⦁ s ∈⋎u⋏+ Pair⋎u s t ∧ t ∈⋎u⋏+ Pair⋎u s t
⦏Pair⋎u_eq_thm⦎ =		⊢ ∀ s t u v⦁ Pair⋎u s t = Pair⋎u u v
					⇔ s = u ∧ t = v ∨ s = v ∧ t = u
=TEX

\ignore{
=SML
val Pair⋎u_def = get_spec ⌜Pair⋎u⌝;

set_goal([], ⌜∀x y⦁ x ∈⋎u Pair⋎u x y ∧ y ∈⋎u Pair⋎u x y⌝);
a (rewrite_tac [Pair⋎u_def]);
val Pair⋎u_∈⋎u_thm = save_pop_thm "Pair⋎u_∈⋎u_thm";

set_goal([], ⌜∀s t⦁ s ∈⋎u⋏+ Pair⋎u s t ∧ t ∈⋎u⋏+ Pair⋎u s t⌝);
a (REPEAT ∀_tac);
a (STRIP_THM_THEN asm_tac (list_∀_elim [⌜s⌝, ⌜t⌝] Pair⋎u_∈⋎u_thm)
	THEN ufc_tac [tc∈⋎u_incr_thm]);
a (REPEAT strip_tac);
val Pair⋎u_tc∈⋎u_thm = save_pop_thm "Pair⋎u_tc∈⋎u_thm";

set_goal([],⌜∀s t u v⦁
	Pair⋎u s t = Pair⋎u u v
	⇔ s = u ∧ t = v
	∨ s = v ∧ t = u⌝);
a (REPEAT ∀_tac);
a (lemma_tac ⌜Set⋎u (Pair⋎u s t) ∧ Set⋎u (Pair⋎u u v)⌝ THEN1 rewrite_tac[Pair⋎u_def]);
a (all_ufc_⇔_rewrite_tac [gsu_ext_axiom]);
a (rewrite_tac[
	Pair⋎u_def]
	THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 2 ⌜s⌝
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜u⌝
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (spec_nth_asm_tac 2 ⌜v⌝
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (spec_nth_asm_tac 2 ⌜t⌝
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY asm_rewrite_tac[]);
val Pair⋎u_eq_thm =
	save_pop_thm "Pair⋎u_eq_thm";
=TEX
}%ignore

=GFT
⦏GClose⋎uPair⋎u⦎ =	⊢ ∀g⦁ galaxy⋎u g ⇒ ∀s t⦁ s ∈⋎u g ∧ t ∈⋎u g
				⇒ Pair⋎u s t ∈⋎u g
=TEX

\ignore{
=SML
set_goal([],⌜∀g⦁ galaxy⋎u g ⇒ ∀s t⦁ s ∈⋎u g ∧ t ∈⋎u g ⇒ Pair⋎u s t ∈⋎u g⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜Pair⋎u s t = Imagep⋎u (λx⦁ if x = ∅⋎u then s else t) (ℙ⋎u (ℙ⋎u ∅⋎u))⌝);
(* *** Goal "1" *** *)
a (lemma_tac ⌜Set⋎u(Pair⋎u s t) ∧ Set⋎u(Imagep⋎u (λ x⦁ if x = ∅⋎u then s else t) (ℙ⋎u (ℙ⋎u ∅⋎u)))⌝ THEN1 rewrite_tac[Pair⋎u_def]);
a (all_ufc_⇔_rewrite_tac [gsu_ext_axiom]);
a (rewrite_tac [Pair⋎u_def, Imagep⋎u_def]);
a (REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.1" *** *)
a (∃_tac ⌜∅⋎u⌝ THEN rewrite_tac[⊆⋎u_def]);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜ℙ⋎u ∅⋎u⌝ THEN rewrite_tac[⊆⋎u_def]);
a (lemma_tac ⌜¬ ℙ⋎u ∅⋎u = ∅⋎u⌝);
(* *** Goal "1.2.1" *** *)
a (LEMMA_T ⌜Set⋎u(ℙ⋎u (∅⋎u:'a GSU)) ∧ Set⋎u(∅⋎u:'a GSU)⌝ (STRIP_THM_THEN asm_tac) THEN1 rewrite_tac[]);
a (all_ufc_⇔_rewrite_tac [gsu_ext_axiom]
	THEN strip_tac
	THEN ∃_tac ⌜∅⋎u⌝
	THEN rewrite_tac[]);
(* *** Goal "1.2.2" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "1.3" *** *)
a (cases_tac ⌜e' = ∅⋎u⌝
	THEN asm_rewrite_tac[]);
a (asm_ante_tac ⌜e = (if e' = ∅⋎u then s else t)⌝
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
a (fc_tac [GImagep⋎uC]);
a (list_spec_nth_asm_tac 1 [⌜ℙ⋎u (ℙ⋎u (∅⋎u:'a GSU))⌝,⌜λ x:'a GSU⦁ if x = ∅⋎u then s else t⌝]);
a (fc_tac [G∅⋎uC]);
a (lemma_tac ⌜∀s⦁ s ∈⋎u g ⇒ ℙ⋎u s ∈⋎u g⌝
	THEN1 (REPEAT (fc_tac [get_spec ⌜galaxy⋎u⌝])));
a (REPEAT (asm_fc_tac []));
(* *** Goal "2.2" *** *)
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac [⊆⋎u_def]);
a (REPEAT strip_tac);
a (POP_ASM_T ante_tac
	THEN cases_tac ⌜e' = ∅⋎u⌝
	THEN asm_rewrite_tac[]
	THEN strip_tac
	THEN asm_rewrite_tac[]);
val GClose⋎uPair⋎u = save_pop_thm "GClose⋎uPair⋎u";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Unit⋎u⦎ : 'a GSU → 'a GSU
├──────────
│ ∀s⦁ Unit⋎u s = Pair⋎u s s
■

The following theorem tells you what the members of a unit sets are.

=GFT
⦏Unit⋎u_thm⦎ =	⊢ ∀s e⦁ e ∈⋎u Unit⋎u s ⇔ e = s
⦏Unit⋎u_thm2⦎ =	⊢ ∀x⦁ x ∈⋎u Unit⋎u x
⦏Unit⋎u_tc∈⋎u_thm⦎ =	⊢ ∀x⦁ x ∈⋎u⋏+ Unit⋎u x
=TEX

\ignore{
=SML
val Unit⋎u_def = get_spec ⌜Unit⋎u⌝;

set_goal([],⌜∀s e⦁
	e ∈⋎u Unit⋎u s ⇔ e = s⌝);
a (rewrite_tac [
	Unit⋎u_def,
	Pair⋎u_def]
	THEN REPEAT strip_tac);
val Unit⋎u_thm = pop_thm ();

val Set⋎uUnit⋎u_thm = prove_rule [Unit⋎u_def, Pair⋎u_def] ⌜∀t⦁ Set⋎u (Unit⋎u t)⌝;

set_goal([], ⌜∀x⦁ x ∈⋎u Unit⋎u x⌝);
a (rewrite_tac [Unit⋎u_thm]);
val Unit⋎u_thm2 = save_pop_thm "Unit⋎u_thm2";

set_goal([], ⌜∀x⦁ x ∈⋎u⋏+ Unit⋎u x⌝);
a (strip_tac);
a (asm_tac (∀_elim ⌜x⌝ Unit⋎u_thm2) THEN fc_tac [tc∈⋎u_incr_thm]);
val Unit⋎u_tc∈⋎u_thm = save_pop_thm "Unit⋎u_tc∈⋎u_thm";

add_pc_thms "'gsu-ax" [Pair⋎u_def, Unit⋎u_thm];
add_rw_thms [Pair⋎u_∈⋎u_thm, Pair⋎u_tc∈⋎u_thm, Unit⋎u_tc∈⋎u_thm, Set⋎uUnit⋎u_thm] "'gsu-ax";
add_sc_thms [Pair⋎u_∈⋎u_thm, Pair⋎u_tc∈⋎u_thm, Unit⋎u_tc∈⋎u_thm, Set⋎uUnit⋎u_thm] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

The following theorem tells you when two unit sets are equal.

=GFT
⦏Unit⋎u_eq_thm⦎ =	⊢ ∀s t⦁ Unit⋎u s = Unit⋎u t ⇔ s = t
=TEX

\ignore{
=SML
set_goal([],⌜∀s t⦁
	Unit⋎u s = Unit⋎u t
	⇔ s = t⌝);
a (REPEAT ∀_tac);
a (lemma_tac ⌜Set⋎u(Unit⋎u s) ∧ Set⋎u(Unit⋎u t)⌝ THEN1 prove_tac[]);
a (all_ufc_⇔_rewrite_tac [gsu_ext_axiom]);
a (prove_tac []);
val Unit⋎u_eq_thm = pop_thm ();

add_pc_thms "'gsu-ax" [Unit⋎u_eq_thm];
set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

\subsubsection{Galaxy Closure}

=GFT
⦏GClose⋎uUnit⋎u⦎ =	⊢ ∀g⦁ galaxy⋎u g ⇒ ∀s⦁ s ∈⋎u g ⇒ Unit⋎u s ∈⋎u g
=TEX

\ignore{
=SML
set_goal([],⌜∀g⦁ galaxy⋎u g ⇒ ∀s⦁ s ∈⋎u g ⇒ Unit⋎u s ∈⋎u g⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [get_spec ⌜Unit⋎u⌝]);
a (REPEAT (asm_fc_tac[GClose⋎uPair⋎u]));
val GClose⋎uUnit⋎u = save_pop_thm "GClose⋎uUnit⋎u";
=TEX
}%ignore


The following theorems tell you when $Pair⋎u$ are really $Unit⋎s$.

=GFT
⦏Unit⋎u_Pair⋎u_eq_thm⦎ =	⊢ ∀s t u⦁ Unit⋎u s = Pair⋎u t u ⇔ s = t ∧ s = u
⦏Pair⋎u_Unit⋎u_eq_thm⦎ =	⊢ ∀s t u⦁ Pair⋎u s t = Unit⋎u u ⇔ s = u ∧ t = u
=TEX

\ignore{
=SML
set_goal([],
	⌜∀s t u⦁
	Unit⋎u s = Pair⋎u t u
	⇔ s = t ∧ s = u⌝);
a (prove_tac [gsu_ext_conv ⌜Unit⋎u s = Pair⋎u t u⌝]);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜s⌝
	THEN spec_nth_asm_tac 2 ⌜t⌝
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY rewrite_tac[]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 1 ⌜u⌝
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY rewrite_tac[]);
val Unit⋎u_Pair⋎u_eq_thm = pop_thm ();
=TEX

=SML
set_goal([],⌜∀s t u⦁
	Pair⋎u s t = Unit⋎u u
	⇔ s = u ∧ t = u⌝);
a (prove_tac [gsu_ext_conv ⌜Pair⋎u s t = Unit⋎u u⌝]);
val Pair⋎u_Unit⋎u_eq_thm = pop_thm ();
=TEX
}%ignore

\subsection{Union and Intersection}

Binary union and distributed and binary intersection are defined.

\subsubsection{Binary Union}

\ignore{
=SML
declare_infix (240, "∪⋎u");
set_goal ([],⌜∃($∪⋎u)⦁ ∀s t⦁ Set⋎u (s ∪⋎u t) ∧ ∀ e⦁
e ∈⋎u (s ∪⋎u t) ⇔ e ∈⋎u s ∨ e ∈⋎u t
⌝);
a (∃_tac ⌜λs t⦁ ⋃⋎u (Pair⋎u s t)⌝);
a (prove_tac [⋃⋎u_def]);
save_cs_∃_thm(pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ $∪⋎u : 'a GSU → 'a GSU → 'a GSU
├─────────────
│ ∀s t⦁ Set⋎u (s ∪⋎u t) ∧ ∀e⦁ e ∈⋎u (s ∪⋎u t) ⇔ e ∈⋎u s ∨ e ∈⋎u t
■

=GFT
⦏⊆⋎u∪⋎u_thm⦎ =		⊢ ∀ A B⦁ A ⊆⋎u A ∪⋎u B ∧ B ⊆⋎u A ∪⋎u B
⦏∪⋎u⊆⋎u_def1⦎ =		⊢ ∀ A B C⦁ A ⊆⋎u C ∧ B ⊆⋎u C ⇒ A ∪⋎u B ⊆⋎u C
⦏∪⋎u⊆⋎u_def2⦎ =		⊢ ∀ A B C D⦁ A ⊆⋎u C ∧ B ⊆⋎u D ⇒ A ∪⋎u B ⊆⋎u C ∪⋎u D
⦏∪⋎u∅⋎u_clauses⦎ =	⊢ ∀ A⦁ Set⋎u A ⇒ A ∪⋎u ∅⋎u = A ∧ ∅⋎u ∪⋎u A = A
⦏∪⋎u_comm_thm⦎ =	⊢ ∀ A B⦁ A ∪⋎u B = B ∪⋎u A
⦏∪⋎u_∅⋎u_set⋎u_thm⦎ =	⊢ ∀ A⦁ A ∪⋎u ∅⋎u = set⋎u A ∧ ∅⋎u ∪⋎u A = set⋎u A
⦏tc∈⋎u_∪⋎u_thm⦎ =	⊢ ∀ x A B⦁ x ∈⋎u⋏+ A ∪⋎u B ⇔ x ∈⋎u⋏+ A ∨ x ∈⋎u⋏+ B
=TEX

\ignore{
=SML
val ⦏∪⋎u_def⦎ = get_spec ⌜$∪⋎u⌝;

val ⦏⊆⋎u∪⋎u_thm⦎ = save_thm ("⊆⋎u∪⋎u_thm", prove_rule
	[⊆⋎u_def, ∪⋎u_def]
	⌜∀A B⦁ A ⊆⋎u A ∪⋎u B ∧ B ⊆⋎u A ∪⋎u B⌝);
val ⦏∪⋎u⊆⋎u_def1⦎ = save_thm ("∪⋎u⊆⋎u_def1", prove_rule
	[⊆⋎u_def, ∪⋎u_def]
	⌜∀A B C⦁ A ⊆⋎u C ∧ B ⊆⋎u C ⇒ A ∪⋎u B ⊆⋎u C⌝);
val ⦏∪⋎u⊆⋎u_def2⦎ = save_thm ("∪⋎u⊆⋎u_def2", prove_rule
	[⊆⋎u_def, ∪⋎u_def]
	⌜∀A B C D⦁ A ⊆⋎u C ∧ B ⊆⋎u D ⇒ (A ∪⋎u B) ⊆⋎u (C ∪⋎u D)⌝);

add_rw_thms [∪⋎u_def, ⊆⋎u∪⋎u_thm] "'gsu-ax";
add_sc_thms [∪⋎u_def, ⊆⋎u∪⋎u_thm] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];

set_goal([], ⌜∀A⦁ Set⋎u A ⇒ (A ∪⋎u ∅⋎u) = A ∧ (∅⋎u ∪⋎u A) = A⌝);
a (REPEAT_N 2 strip_tac);
a (lemma_tac ⌜Set⋎u(A ∪⋎u ∅⋎u) ∧ Set⋎u (∅⋎u ∪⋎u A)⌝ THEN1 rewrite_tac[∪⋎u_def]);
a (all_ufc_⇔_rewrite_tac [gsu_ext_axiom]);
val ⦏∪⋎u∅⋎u_clauses⦎ = save_pop_thm "∪⋎u∅⋎u_clauses";

set_goal([], ⌜∀A B⦁ A ∪⋎u B = B ∪⋎u A⌝);
a (REPEAT strip_tac);
a (gsu_ext_tac THEN ∀_tac THEN rewrite_tac [∪⋎u_def] THEN contr_tac);
val ⦏∪⋎u_comm_thm⦎ = save_pop_thm "∪⋎u_comm_thm";

set_goal([], ⌜∀A⦁ A ∪⋎u ∅⋎u = set⋎u A ∧ ∅⋎u ∪⋎u A = set⋎u A⌝);
a (strip_tac);
a (lemma_tac ⌜A ∪⋎u ∅⋎u = set⋎u A⌝);
(* *** Goal "1" *** *)
a (gsu_ext_tac THEN rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a (asm_rewrite_tac []);
a (once_rewrite_tac[∪⋎u_comm_thm] THEN strip_tac);
val ∪⋎u_∅⋎u_set⋎u_thm = save_pop_thm "∪⋎u_∅⋎u_set⋎u_thm";

set_goal([], ⌜∀x A B⦁ x ∈⋎u⋏+ A ∪⋎u B ⇔ x ∈⋎u⋏+ A ∨ x ∈⋎u⋏+ B⌝);
a (REPEAT ∀_tac THEN once_rewrite_tac[tc∈⋎u_cases_thm]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
a (spec_nth_asm_tac 2 ⌜z⌝);
a (DROP_ASM_T ⌜z ∈⋎u A ∪⋎u B⌝ ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
(* *** Goal "5" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "6" *** *)
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
val tc∈⋎u_∪⋎u_thm = save_pop_thm "tc∈⋎u_∪⋎u_thm";

add_rw_thms [tc∈⋎u_∪⋎u_thm] "'gsu-ax";
add_sc_thms [tc∈⋎u_∪⋎u_thm] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

\subsubsection{Galaxy Closure}

=GFT
⦏GClose⋎u∪⋎u⦎ =	⊢ ∀g⦁ galaxy⋎u g ⇒ ∀s t⦁ s ∈⋎u g ∧ t ∈⋎u g ⇒ s ∪⋎u t ∈⋎u g
=TEX

\ignore{
=SML
set_goal([],⌜∀g⦁ galaxy⋎u g ⇒ ∀s t⦁ s ∈⋎u g ∧ t ∈⋎u g ⇒ s ∪⋎u t ∈⋎u g⌝);
a (REPEAT strip_tac THEN fc_tac [get_spec ⌜galaxy⋎u⌝]);
a (lemma_tac ⌜s ∪⋎u t = ⋃⋎u (Pair⋎u s t)⌝
	THEN1 (once_rewrite_tac [gsu_ext_conv ⌜s ∪⋎u t = ⋃⋎u (Pair⋎u s t)⌝]
		THEN rewrite_tac [⋃⋎u_def, get_spec ⌜$∪⋎u⌝]
		THEN prove_tac[]));
a (asm_rewrite_tac []);
a (lemma_tac ⌜Pair⋎u s t ∈⋎u g⌝
	THEN1 (REPEAT (asm_fc_tac [GClose⋎uPair⋎u])));
a (REPEAT (asm_fc_tac[]));
val GClose⋎u∪⋎u = save_pop_thm "GClose⋎u∪⋎u";
=TEX
}%ignore

\subsubsection{Distributed Intersection}

Distributed intersection doesn't really make sense for the empty set, but under this definition it maps the empty set onto itself.

ⓈHOLCONST
│ ⦏⋂⋎u⦎ : 'a GSU → 'a GSU
├
│ ∀s⦁ ⋂⋎u s = Sep⋎u (⋃⋎u s) (λx⦁ ∀t⦁ t ∈⋎u s ⇒ x ∈⋎u t)
■

=GFT
⦏Set⋎u⋂⋎u_thm⦎ =	⊢ ∀ x⦁ Set⋎u (⋂⋎u x)
⦏⋂⋎u⊆⋎u_thm⦎ =	⊢ ∀x s e⦁ x ∈⋎u s
				⇒ (e ∈⋎u ⋂⋎u s ⇔ ∀y⦁ y ∈⋎u s ⇒ e ∈⋎u y)
⦏⊆⋎u⋂⋎u_thm⦎ =	⊢  ∀A B⦁ A ∈⋎u B
				⇒ ∀C⦁ (∀D⦁ D ∈⋎u B ⇒ C ⊆⋎u D)
				⇒ C ⊆⋎u ⋂⋎u B
⦏⋂⋎u∅⋎u_thm⦎ = 	⊢ ⋂⋎u ∅⋎u = ∅⋎u
=TEX

\ignore{
=SML
val ⋂⋎u_def = get_spec ⌜⋂⋎u⌝;

set_goal([], ⌜∀x⦁ Set⋎u(⋂⋎u x)⌝);
a (rewrite_tac[⋂⋎u_def]);
val Set⋎u⋂⋎u_thm = pop_thm();

set_goal ([],⌜∀x s e⦁ x ∈⋎u s ⇒
	(e ∈⋎u ⋂⋎u s ⇔ ∀y⦁ y ∈⋎u s ⇒ e ∈⋎u y)⌝);
a (prove_tac [
	get_spec ⌜⋂⋎u⌝]);
val ⋂⋎u_thm = save_pop_thm "⋂⋎u_thm";

set_goal([],⌜∀s t⦁ s ∈⋎u t ⇒ ⋂⋎u t ⊆⋎u s⌝);
a (rewrite_tac [⋂⋎u_thm, ⊆⋎u_def]);
a (REPEAT strip_tac);
a (REPEAT (asm_fc_tac[⋂⋎u_thm]));
val ⋂⋎u⊆⋎u_thm = save_pop_thm "⋂⋎u⊆⋎u_thm";

val ⊆⋎u⋂⋎u_thm = save_thm ("⊆⋎u⋂⋎u_thm", 
	(prove_rule [⊆⋎u_def, gsu_ext_axiom,
	get_spec ⌜$⋂⋎u⌝]
	⌜∀A B⦁ A ∈⋎u B ⇒ ∀C⦁	
	(∀D⦁ D ∈⋎u B ⇒ C ⊆⋎u D)
	⇒ C ⊆⋎u ⋂⋎u B⌝));

add_rw_thms [Set⋎u⋂⋎u_thm] "'gsu-ax";
add_sc_thms [Set⋎u⋂⋎u_thm] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];

val ⋂⋎u∅⋎u_thm = save_thm ("⋂⋎u∅⋎u_thm", 
	(prove_rule [gsu_ext_conv ⌜⋂⋎u ∅⋎u = ∅⋎u⌝, get_spec ⌜$⋂⋎u⌝]
	⌜⋂⋎u ∅⋎u = ∅⋎u⌝));
=TEX
}%ignore

\subsubsection{Binary Intersection}

Binary intersection could be defined in terms of distributed intersection, but its easier not to.

=SML
declare_infix (240, "∩⋎u");
=TEX

ⓈHOLCONST
│ $⦏∩⋎u⦎ : 'a GSU → 'a GSU → 'a GSU
├
│ ∀s t⦁ s ∩⋎u t = Sep⋎u s (λx⦁ x ∈⋎u t)
■

=GFT
⦏Set⋎u∩⋎u_thm⦎ = ⊢ ∀ s t⦁ Set⋎u (s ∩⋎u t)
=TEX

\ignore{
=SML
val ∩⋎u_def = get_spec ⌜$∩⋎u⌝;

set_goal([], ⌜∀s t⦁ Set⋎u (s ∩⋎u t)⌝);
a (rewrite_tac[∩⋎u_def]);
val Set⋎u∩⋎u_thm = pop_thm ();

add_rw_thms [Set⋎u∩⋎u_thm] "'gsu-ax";
add_sc_thms [Set⋎u∩⋎u_thm] "'gsu-ax";
set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

\subsubsection{Galaxy Closure}

=GFT
⦏GClose⋎u⋂⋎u⦎ =	⊢ ∀g⦁ galaxy⋎u g ⇒ ∀s⦁ s ∈⋎u g ⇒ ⋂⋎u s ∈⋎u g
⦏GClose⋎u∩⋎u⦎ =	⊢ ∀g⦁ galaxy⋎u g ⇒ ∀s t⦁ s ∈⋎u g ∧ t ∈⋎u g ⇒ s ∩⋎u t ∈⋎u g
=TEX

\ignore{
=SML
set_goal([],⌜∀g⦁ galaxy⋎u g ⇒ ∀s⦁ s ∈⋎u g ⇒ ⋂⋎u s ∈⋎u g⌝);
a (REPEAT strip_tac
	THEN rewrite_tac[get_spec ⌜⋂⋎u⌝]);
a (fc_tac [GClose⋎uSep⋎u_thm, get_spec ⌜galaxy⋎u⌝]);
a (list_spec_nth_asm_tac 1 [⌜⋃⋎u s⌝, ⌜λ x⦁ ∀ t⦁ t ∈⋎u s ⇒ x ∈⋎u t⌝]);
a (asm_fc_tac[]);
val GClose⋎u⋂⋎u = save_pop_thm "GClose⋎u⋂⋎u";

set_goal([],⌜∀g⦁ galaxy⋎u g ⇒ ∀s t⦁ s ∈⋎u g ∧ t ∈⋎u g ⇒ s ∩⋎u t ∈⋎u g⌝);
a (REPEAT strip_tac
	THEN rewrite_tac[get_spec ⌜$∩⋎u⌝]);
a (fc_tac [GClose⋎uSep⋎u_thm]);
a (list_spec_nth_asm_tac 1 [⌜s⌝, ⌜λ x⦁ x ∈⋎u t⌝]);
val GClose⋎u∩⋎u = save_pop_thm "GClose⋎u∩⋎u";
=TEX
}%ignore

=GFT
⦏∩⋎u_thm⦎ =		⊢ ∀s t e⦁ e ∈⋎u s ∩⋎u t ⇔ e ∈⋎u s ∧ e ∈⋎u t
⦏∩⋎u_thm⦎ =		⊢ ∀s t e⦁	e ∈⋎u s ∩⋎u t ⇔ e ∈⋎u s ∧ e ∈⋎u t
=TEX

=GFT
⦏⊆⋎u∩⋎u_thm⦎ =	⊢ ∀A B⦁ A ∩⋎u B ⊆⋎u A ∧ A ∩⋎u B ⊆⋎u B
⦏∩⋎u⊆⋎u_def1⦎ =	⊢ ∀A B C⦁ A ⊆⋎u C ∧ B ⊆⋎u C ⇒ A ∩⋎u B ⊆⋎u C
⦏∩⋎u⊆⋎u_def2⦎ =	⊢ ∀A B C D⦁ A ⊆⋎u C ∧ B ⊆⋎u D ⇒ (A ∩⋎u B) ⊆⋎u (C ∩⋎u D)
⦏∩⋎u⊆⋎u_def3⦎ =	⊢ ∀A B C⦁ C ⊆⋎u A ∧ C ⊆⋎u B ⇒ C ⊆⋎u A ∩⋎u B
=TEX

\ignore{
=SML
set_goal ([],⌜∀s t e⦁
	e ∈⋎u s ∩⋎u t ⇔ e ∈⋎u s ∧ e ∈⋎u t⌝);
a (prove_tac [
	get_spec ⌜$∩⋎u⌝]);
val ∩⋎u_thm = save_thm ("∩⋎u_thm",
	prove_rule [get_spec ⌜$∩⋎u⌝]
	⌜∀s t e⦁	e ∈⋎u s ∩⋎u t ⇔ e ∈⋎u s ∧ e ∈⋎u t⌝);
val ⊆⋎u∩⋎u_thm = save_thm ("⊆⋎u∩⋎u_thm",
	prove_rule [⊆⋎u_def, ∩⋎u_thm]
	⌜∀A B⦁ A ∩⋎u B ⊆⋎u A ∧ A ∩⋎u B ⊆⋎u B⌝);
val ∩⋎u⊆⋎u_def1 = save_thm ("∩⋎u⊆⋎u_def1",
	prove_rule [⊆⋎u_def, ∩⋎u_thm]
	⌜∀A B C⦁ A ⊆⋎u C ∧ B ⊆⋎u C ⇒ A ∩⋎u B ⊆⋎u C⌝);
val ∩⋎u⊆⋎u_def2 = save_thm ("∩⋎u⊆⋎u_def2",
	prove_rule [⊆⋎u_def, ∩⋎u_thm]
	⌜∀A B C D⦁ A ⊆⋎u C ∧ B ⊆⋎u D ⇒ (A ∩⋎u B) ⊆⋎u (C ∩⋎u D)⌝);
val ∩⋎u⊆⋎u_def3 = save_thm ("∩⋎u⊆⋎u_def3",
	prove_rule [⊆⋎u_def, ∩⋎u_thm]
	⌜∀A B C⦁ C ⊆⋎u A ∧ C ⊆⋎u B ⇒ C ⊆⋎u A ∩⋎u B⌝);
=TEX
}%ignore

\subsubsection{Consequences of Well-Foundedness}

=GFT
⦏not_x_∈⋎u_x_thm⦎ =	⊢ ¬ (∃ x⦁ x ∈⋎u x)
=TEX

\ignore{
=SML
set_goal([], ⌜¬ ∃x⦁ x ∈⋎u x⌝);
a contr_tac;
a (asm_tac gsu_wf_min_thm);
a (spec_nth_asm_tac 1 ⌜Sep⋎u x (λy:'a GSU⦁ y = x)⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (POP_ASM_T ante_tac
	THEN rewrite_tac[]);
a strip_tac;
a (DROP_NTH_ASM_T 2 ante_tac
	THEN rewrite_tac[]);
a (swap_nth_asm_concl_tac 1);
a (all_var_elim_asm_tac);
a (strip_tac);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val not_x_∈⋎u_x_thm = save_pop_thm "not_x_∈⋎u_x_thm";
=TEX
}%ignore

\subsection{Galaxy Closure Clauses}

=GFT
⦏GClose⋎u_fc_clauses2⦎ =
   ⊢ ∀ g
     ⦁ galaxy⋎u g
         ⇒ (∀ s t⦁ s ∈⋎u g ∧ t ∈⋎u g ⇒ Pair⋎u s t ∈⋎u g)
           ∧ (∀ s⦁ s ∈⋎u g ⇒ Unit⋎u s ∈⋎u g)
           ∧ (∀ s t⦁ s ∈⋎u g ∧ t ∈⋎u g ⇒ s ∪⋎u t ∈⋎u g)
           ∧ (∀ s⦁ s ∈⋎u g ⇒ ⋂⋎u s ∈⋎u g)
           ∧ (∀ s t⦁ s ∈⋎u g ∧ t ∈⋎u g ⇒ s ∩⋎u t ∈⋎u g)
=TEX

\ignore{
=SML
set_goal([], ⌜∀g⦁ galaxy⋎u g ⇒
	  (∀s t⦁ s ∈⋎u g ∧ t ∈⋎u g ⇒ Pair⋎u s t ∈⋎u g)
	∧ (∀s⦁ s ∈⋎u g ⇒ Unit⋎u s ∈⋎u g)
	∧ (∀s t⦁ s ∈⋎u g ∧ t ∈⋎u g ⇒ s ∪⋎u t ∈⋎u g)
	∧ (∀s⦁ s ∈⋎u g ⇒ ⋂⋎u s ∈⋎u g)
	∧ (∀s t⦁ s ∈⋎u g ∧ t ∈⋎u g ⇒ s ∩⋎u t ∈⋎u g)
	⌝);
a (REPEAT strip_tac
	THEN all_fc_tac [GClose⋎uPair⋎u, GClose⋎uUnit⋎u, GClose⋎u∪⋎u, GClose⋎u⋂⋎u, GClose⋎u∩⋎u]);
val GClose⋎u_fc_clauses2 = save_pop_thm "GClose⋎u_fc_clauses2";
=TEX
}%ignore

=GFT
⦏tc∈⋎u_clauses⦎ =	⊢ ∀ s⦁	s ∈⋎u⋏+ Unit⋎u s
			∧ ∀t⦁	t ∈⋎u⋏+ Pair⋎u s t
			∧ 	s ∈⋎u⋏+ Pair⋎u s t
=TEX

\ignore{
=SML
set_goal([], ⌜∀ s⦁	s ∈⋎u⋏+ Unit⋎u s
		∧ ∀t⦁	t ∈⋎u⋏+ Pair⋎u s t
		∧ 	s ∈⋎u⋏+ Pair⋎u s t⌝);
a (rewrite_tac[]);
val tc∈⋎u_clauses = save_pop_thm "tc∈⋎u_clauses";
=TEX
}%ignore

\subsection{Transitive Closure and Closed Image}

The transitive closure of a set is the set of objects which relate to it under the transitive closure of the membership relation.

ⓈHOLCONST
│ ⦏TrCl⋎u⦎ : 'a GSU → 'a GSU
├───────────────
│ ∀s⦁ TrCl⋎u s = Sep⋎u (Gx⋎u s) (λx⦁ x ∈⋎u⋏+ s)
■

=GFT
⦏Set⋎u_TrCl⋎u_thm⦎ =
	⊢ ∀ s⦁ Set⋎u (TrCl⋎u s)
⦏TrCl⋎u_sup_thm⦎ =
	⊢ ∀ s⦁ s ⊆⋎u TrCl⋎u s
⦏TrCl⋎u_sup_thm2⦎ =
	⊢ ∀ s t⦁ Transitive⋎u t ∧ s ⊆⋎u t ⇒ TrCl⋎u s ⊆⋎u t
⦏Transitive⋎u_TrCl⋎u_thm⦎ =
	⊢ ∀ s⦁ Transitive⋎u (TrCl⋎u s)
⦏TrCl⋎u_ext_thm⦎ =
	⊢ ∀ s x⦁ x ∈⋎u TrCl⋎u s ⇔ (∀ t⦁ Transitive⋎u t ∧ s ⊆⋎u t ⇒ x ∈⋎u t)
⦏TrCl⋎u_ext_thm2⦎ =
	⊢ ∀ s t⦁ s ∈⋎u TrCl⋎u t ⇔ s ∈⋎u⋏+ t
⦏tc∈⋎u_TrCl⋎u_thm⦎ =
	⊢ ∀ s t⦁ s ∈⋎u⋏+ TrCl⋎u t ⇔ s ∈⋎u⋏+ t
⦏Tran_set_TrCl_thm⦎ =
	⊢ ∀ s⦁ Set⋎u s ∧ Transitive⋎u s ⇒ TrCl⋎u s = s
⦏Tran_set_tc∈⋎u_thm⦎ =
	⊢ ∀ s⦁ Set⋎u s ∧ Transitive⋎u s ⇒ (∀ x⦁ x ∈⋎u⋏+ s ⇒ x ∈⋎u s)
⦏Tran_tc∈⋎u_thm⦎ =
	⊢ ∀ s⦁ Transitive⋎u s ⇒ (∀ x⦁ x ∈⋎u⋏+ s ⇒ x ∈⋎u s)
=TEX

\ignore{
=SML
val TrCl⋎u_def = get_spec ⌜TrCl⋎u⌝;

set_goal([], ⌜∀s⦁ Set⋎u(TrCl⋎u s)⌝);
a (rewrite_tac [TrCl⋎u_def]);
val Set⋎u_TrCl⋎u_thm = save_pop_thm "Set⋎u_TrCl⋎u_thm";

set_goal([], ⌜∀s⦁ s ⊆⋎u TrCl⋎u s⌝);
a (rewrite_tac[TrCl⋎u_def, get_spec ⌜$⊆⋎u⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [Gx⋎u_trans_thm2]);
(* *** Goal "2" *** *)
a (once_rewrite_tac [tc∈⋎u_cases_thm] THEN asm_rewrite_tac[]);
val TrCl⋎u_sup_thm = save_pop_thm "TrCl⋎u_sup_thm";

set_goal([], ⌜∀s t⦁ Transitive⋎u t ∧ s ⊆⋎u t ⇒ TrCl⋎u s ⊆⋎u t⌝);
a (rewrite_tac[TrCl⋎u_def] THEN REPEAT strip_tac);
a (rewrite_tac[get_spec ⌜$⊆⋎u⌝] THEN REPEAT strip_tac);
a (all_fc_tac [tc∈⋎u_lemma]);
val TrCl⋎u_sup_thm2 = save_pop_thm "TrCl⋎u_sup_thm2";

set_goal([], ⌜∀s⦁ Transitive⋎u (TrCl⋎u s)⌝);
a (rewrite_tac[TrCl⋎u_def, Transitive⋎u_def] THEN REPEAT strip_tac);
a (once_rewrite_tac[get_spec ⌜$⊆⋎u⌝]
	THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [Gx⋎u_trans_thm3]);
(* *** Goal "2" *** *)
a (asm_fc_tac[tc∈⋎u_incr_thm]);
a (all_asm_fc_tac[tc∈⋎u_trans_thm]);
val Transitive⋎u_TrCl⋎u_thm = save_pop_thm "Transitive⋎u_TrCl⋎u_thm";

set_goal([], ⌜∀s x⦁ x ∈⋎u TrCl⋎u s ⇔ ∀t⦁ Transitive⋎u t ∧ s ⊆⋎u t ⇒ x ∈⋎u t⌝);
a (REPEAT strip_tac);
a (ALL_FC_T (MAP_EVERY ante_tac) [TrCl⋎u_sup_thm2]);
a (rewrite_tac [⊆⋎u_def] THEN REPEAT strip_tac THEN asm_fc_tac[]);
(* *** Goal "2" *** *)
a (rewrite_tac[TrCl⋎u_def]);
a (asm_tac TrCl⋎u_sup_thm);
a (asm_tac Transitive⋎u_TrCl⋎u_thm);
a (ALL_ASM_UFC_T (MAP_EVERY ante_tac) []);
a (rewrite_tac [TrCl⋎u_def]);
val TrCl⋎u_ext_thm = save_pop_thm "TrCl⋎u_ext_thm";

set_goal([], ⌜∀s t⦁ s ∈⋎u TrCl⋎u t ⇔ s ∈⋎u⋏+ t⌝);
a (rewrite_tac [TrCl⋎u_def] THEN REPEAT strip_tac);
a (LEMMA_T ⌜galaxy⋎u(Gx⋎u t)⌝ asm_tac THEN1 rewrite_tac[]);
a (asm_tac (∀_elim ⌜t⌝ t_in_Gx⋎u_t_thm));
a (all_fc_tac [tc∈⋎u_incr_thm]);
a (all_fc_tac [tc∈⋎u_trans_thm]);
a (all_fc_tac [GClose⋎u_tc∈⋎u_thm]);
val TrCl⋎u_ext_thm2 = save_pop_thm "TrCl⋎u_ext_thm2";

set_goal([], ⌜∀s t⦁ s ∈⋎u⋏+ TrCl⋎u t ⇔ s ∈⋎u⋏+ t⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [tc∈⋎u_cases_thm] THEN POP_ASM_T ante_tac
	THEN rewrite_tac [TrCl⋎u_ext_thm2]);
a (strip_tac THEN all_fc_tac [tc∈⋎u_trans_thm]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜s ∈⋎u TrCl⋎u t⌝ THEN1 asm_rewrite_tac[TrCl⋎u_ext_thm2]);
a (all_fc_tac [tc∈⋎u_incr_thm]);
val tc∈⋎u_TrCl⋎u_thm = save_pop_thm "tc∈⋎u_TrCl⋎u_thm";

set_goal([], ⌜∀s⦁ Set⋎u s ∧ Transitive⋎u s ⇒ TrCl⋎u s = s⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜Set⋎u(TrCl⋎u s)⌝ THEN1 rewrite_tac [TrCl⋎u_def]);
a (LEMMA_T ⌜s ⊆⋎u s⌝ asm_tac THEN1 rewrite_tac []);
a (lemma_tac ⌜TrCl⋎u s ⊆⋎u s⌝ THEN1 all_fc_tac [TrCl⋎u_sup_thm2]);
a (lemma_tac ⌜s ⊆⋎u TrCl⋎u s⌝ THEN1 rewrite_tac [TrCl⋎u_sup_thm]);
a (⇔_FC_T (MAP_EVERY asm_tac) [⊆⋎u_eq_thm]);
a (SPEC_NTH_ASM_T 1 ⌜s⌝ ante_tac);
a (rewrite_tac[asm_rule ⌜Set⋎u s⌝]);
a (STRIP_T asm_rewrite_thm_tac);
val Tran_set_TrCl_thm = save_pop_thm "Tran_set_TrCl_thm";

set_goal([], ⌜∀s⦁ Set⋎u s ∧ Transitive⋎u s ⇒ ∀x⦁ x ∈⋎u⋏+ s ⇒ x ∈⋎u s⌝);
a (REPEAT strip_tac);
a (all_fc_tac [Tran_set_TrCl_thm]);
a (LEMMA_T ⌜x ∈⋎u TrCl⋎u s⌝ ante_tac
	THEN1 asm_rewrite_tac [TrCl⋎u_ext_thm2]);
a (asm_rewrite_tac[]);
val Tran_set_tc∈⋎u_thm = save_pop_thm "Tran_set_tc∈⋎u_thm";

set_goal([], ⌜∀s⦁ Transitive⋎u s ⇒ ∀x⦁ x ∈⋎u⋏+ s ⇒ x ∈⋎u s⌝);
a (REPEAT strip_tac);
a (cond_cases_tac ⌜Set⋎u s⌝);
(* *** Goal "1" *** *)
a (all_fc_tac [Tran_set_tc∈⋎u_thm]);
(* *** Goal "2" *** *)
a (contr_tac THEN all_fc_tac [tc∈⋎u_decomp_thm]);
a (all_fc_tac [Set⋎u_axiom]);
val Tran_tc∈⋎u_thm = save_pop_thm "Tran_tc∈⋎u_thm";

add_pc_thms "'gsu-ax" ([]);
add_sc_thms [Set⋎u_TrCl⋎u_thm, TrCl⋎u_sup_thm, Transitive⋎u_TrCl⋎u_thm, TrCl⋎u_ext_thm2, tc∈⋎u_TrCl⋎u_thm] "'gsu-ax";
add_rw_thms [Set⋎u_TrCl⋎u_thm, TrCl⋎u_sup_thm, Transitive⋎u_TrCl⋎u_thm, TrCl⋎u_ext_thm2, tc∈⋎u_TrCl⋎u_thm] "'gsu-ax";

set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

\subsubsection{Closed Image}

When I first introduced the following operator I expected it to be more widely applicable than turns out to be the case.
It is now likely to be phased out in favour of the following limit construction.

Transitive closure is useful later in combination with functional replacement for defining operators over ordinals.
To facilitate such definitions a \emph{closed image} function is defined, which delivers the transitive closure of a set obtained by functional replacement.

Think of $ClIm⋎u$ as the (transitively) CLosed IMage.

ⓈHOLCONST
│ ⦏ClIm⋎u⦎ : ('a GSU → 'a GSU) → 'a GSU → 'a GSU
├────────────────────
│  ∀f α⦁ ClIm⋎u f α = TrCl⋎u(Imagep⋎u f α)
■

The first thing we need to ``prove'' is that it yields a set, and then its membership conditions.

=GFT
⦏Set⋎u_ClIm⋎u_thm⦎ =
	⊢ ∀ f α⦁ Set⋎u (ClIm⋎u f α)
⦏∈⋎u_ClIm⋎u_thm⦎ =
	⊢ ∀ f α⦁ x ∈⋎u ClIm⋎u f α ⇔ (∃ y⦁ y ∈⋎u α ∧ (x = f y ∨ x ∈⋎u⋏+ f y))
⦏tc∈⋎u_ClIm⋎u_thm⦎ =
	⊢ ∀ f α x⦁ x ∈⋎u⋏+ ClIm⋎u f α ⇔ (∃ y⦁ y ∈⋎u α ∧ (x = f y ∨ x ∈⋎u⋏+ f y))
=TEX

\ignore{
=SML
val ClIm⋎u_def = get_spec ⌜ClIm⋎u⌝;

set_goal([], ⌜∀f α⦁ Set⋎u (ClIm⋎u f α)⌝);
a (rewrite_tac [ClIm⋎u_def, TrCl⋎u_def]);
val Set⋎u_ClIm⋎u_thm = save_pop_thm "Set⋎u_ClIm⋎u_thm";

set_goal([], ⌜∀f α x⦁ x ∈⋎u ClIm⋎u f α ⇔ ∃ y⦁ y ∈⋎u α ∧ (x = f y ∨ x ∈⋎u⋏+ f y) ⌝);
a (rewrite_tac[ClIm⋎u_def, TrCl⋎u_ext_thm2, tc∈⋎u_Imagep⋎u_thm]);
val ∈⋎u_ClIm⋎u_thm = save_pop_thm "∈⋎u_ClIm⋎u_thm";

set_goal([], ⌜∀f α x⦁ x ∈⋎u⋏+ ClIm⋎u f α ⇔ ∃ y⦁ y ∈⋎u α ∧ (x = f y ∨ x ∈⋎u⋏+ f y) ⌝);
a (rewrite_tac[ClIm⋎u_def, TrCl⋎u_ext_thm2, tc∈⋎u_Imagep⋎u_thm]);
val tc∈⋎u_ClIm⋎u_thm = save_pop_thm "tc∈⋎u_ClIm⋎u_thm";

add_pc_thms "'gsu-ax" ([]);
add_sc_thms [Set⋎u_ClIm⋎u_thm, ∈⋎u_ClIm⋎u_thm, tc∈⋎u_ClIm⋎u_thm] "'gsu-ax";
add_rw_thms [Set⋎u_ClIm⋎u_thm, ∈⋎u_ClIm⋎u_thm, tc∈⋎u_ClIm⋎u_thm] "'gsu-ax";

set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

This will be used for definitions by transfinite induction, in which case the ``base'' case will correspond to images of the empty set, so these are not interesting.
When empty images are excluded there is an analogy for composition of these maps with ordinary functional composition, which results in an associative law.
If this is proven at this level it subsequently yields more specific associative laws, e.g. for ordinal addition and multiplication. 

=GFT
⦏ClIm⋎u_∅⋎u_thm⦎ =
	⊢ ∀ f s⦁ Set⋎u s ⇒ (ClIm⋎u f s = ∅⋎u ⇔ s = ∅⋎u)
⦏ClIm⋎u_∅⋎u_thm2⦎ =
	⊢ ∀ f s⦁ ClIm⋎u f s = ∅⋎u ⇔ s =⋎u ∅⋎u
⦏ClIm⋎u_∅⋎u_thm3⦎ =
	⊢ ∀ f⦁ ClIm⋎u f ∅⋎u = ∅⋎u
⦏ClIm⋎u_ext_thm⦎ =
	⊢ ∀ f s t⦁ s =⋎u t ⇒ ClIm⋎u f s = ClIm⋎u f t
⦏ClIm⋎u_mono_thm⦎ =
	⊢ ∀ f s t⦁ s ⊆⋎u t ⇒ ClIm⋎u f s ⊆⋎u ClIm⋎u f t
=TEX

\ignore{
=SML
set_goal([],⌜∀f s⦁ Set⋎u s ⇒ (ClIm⋎u f s = ∅⋎u ⇔ s = ∅⋎u)⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (gsu_ext_tac);
a (lemma_tac ⌜∀ e⦁ e ∈⋎u ClIm⋎u f s ⇔ e ∈⋎u ∅⋎u⌝
	THEN1 (pure_asm_rewrite_tac[] THEN prove_tac[]));
a (REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜f e⌝);
a (swap_nth_asm_concl_tac 2);
a (rewrite_tac[]);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
a (gsu_ext_tac THEN rewrite_tac[]);
val ClIm⋎u_∅⋎u_thm = save_pop_thm "ClIm⋎u_∅⋎u_thm";

set_goal([], ⌜∀f s⦁ ClIm⋎u f s = ∅⋎u ⇔ s =⋎u ∅⋎u⌝);
a (rewrite_tac[get_spec ⌜$=⋎u⌝] THEN REPEAT ∀_tac);
a (gsu_ext_tac2 ⌜ClIm⋎u f s = ∅⋎u⌝);
a (rewrite_tac[sets_ext_clauses]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜f x⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (PC_T1 "hol1" asm_rewrite_tac [get_spec ⌜X⋎u⌝]);
(* *** Goal "2" *** *)
a (DROP_NTH_ASM_T 2 (asm_tac o (pc_rule1 "hol1" rewrite_rule[get_spec ⌜X⋎u⌝])));
a (asm_rewrite_tac[]); 
(* *** Goal "3" *** *)
a (DROP_NTH_ASM_T 2 (asm_tac o (pc_rule1 "hol1" rewrite_rule[get_spec ⌜X⋎u⌝])));
a (asm_rewrite_tac[]); 
val ClIm⋎u_∅⋎u_thm2 = save_pop_thm "ClIm⋎u_∅⋎u_thm2";

set_goal([], ⌜∀f⦁ ClIm⋎u f ∅⋎u = ∅⋎u⌝);
a (REPEAT strip_tac THEN rewrite_tac [ClIm⋎u_∅⋎u_thm2]);
val ClIm⋎u_∅⋎u_thm3 = save_pop_thm "ClIm⋎u_∅⋎u_thm3";

set_goal([], ⌜∀f s t⦁ s =⋎u t ⇒ ClIm⋎u f s = ClIm⋎u f t⌝);
a (REPEAT ∀_tac THEN strip_tac THEN gsu_ext_tac);
a (rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 3 ante_tac THEN rewrite_tac [eq⋎u_ext_thm]
	THEN REPEAT strip_tac THEN asm_fc_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 3 ante_tac THEN rewrite_tac [eq⋎u_ext_thm]
	THEN REPEAT strip_tac THEN asm_fc_tac[]);
(* *** Goal "3" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 3 ante_tac THEN rewrite_tac [eq⋎u_ext_thm]
	THEN REPEAT strip_tac THEN spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "4" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 3 ante_tac THEN rewrite_tac [eq⋎u_ext_thm]
	THEN REPEAT strip_tac THEN spec_nth_asm_tac 1 ⌜y⌝);
val ClIm⋎u_ext_thm = save_pop_thm "ClIm⋎u_ext_thm";

set_goal([], ⌜∀f s t⦁ s ⊆⋎u t ⇒ ClIm⋎u f s ⊆⋎u ClIm⋎u f t⌝);
a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜$⊆⋎u⌝]
	THEN REPEAT strip_tac
	THEN asm_fc_tac [] THEN ∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
val ClIm⋎u_mono_thm = save_pop_thm "ClIm⋎u_mono_thm";
=TEX
}%ignore

Whereas the associative behaviour extends to arbitrary functions under functional replacement, in this special kind of replacement it extends only to functions which are well-behaved in relation to transitive closure.
We therefore define the notion of  ``closure compatibility'' for which property we use the name \emph{ClCo}, as follows.


ⓈHOLCONST
│ ⦏ClCo⋎u⦎ : ('a GSU → 'a GSU) → BOOL
├────────────────────
│  ∀f⦁ ClCo⋎u f ⇔ ∀x y⦁ x ∈⋎u⋏+ y ⇒ f x ∈⋎u⋏+ f y
■

=GFT
⦏ClCo⋎u_ClIm⋎u_thm⦎ =
	⊢ ∀ s f g⦁ ClCo⋎u f ⇒ ClIm⋎u f (ClIm⋎u g s) = ClIm⋎u (f o g) s
=TEX

\ignore{
=SML
val ClCo⋎u_def = get_spec ⌜ClCo⋎u⌝;

=IGN
set_goal([], ⌜∀f⦁ ClCo⋎u f ⇒ ∀s⦁ TrCl⋎u(Imagep⋎u f s)  TrCl⋎u(Imagep⋎u f (TrCl⋎u s))⌝);
a (REPEAT ∀_tac THEN  rewrite_tac [ClCo⋎u_def]);
a (gsu_ext_tac2 ⌜TrCl⋎u s = TrCl⋎u t⌝);
a (gsu_ext_tac2 ⌜TrCl⋎u (Imagep⋎u f s) = TrCl⋎u (Imagep⋎u f t)⌝);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);

=SML
set_goal([], ⌜∀s:'a GSU; (f:'a GSU → 'a GSU) g⦁ ClCo⋎u f ⇒ ClIm⋎u f (ClIm⋎u g s) = ClIm⋎u (f o g) s⌝);
a (REPEAT ∀_tac THEN strip_tac THEN gsu_ext_tac THEN rewrite_tac[get_spec ⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜y'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜y'⌝ THEN asm_rewrite_tac[]);
a (var_elim_asm_tac ⌜y = g y'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (∃_tac ⌜y'⌝ THEN asm_rewrite_tac[]);
a (fc_tac [ClCo⋎u_def]);
a (∨_right_tac);
a (all_asm_fc_tac[]);
(* *** Goal "4" *** *)
a (∃_tac ⌜y'⌝ THEN asm_rewrite_tac[]);
a (∨_right_tac);
a (fc_tac [ClCo⋎u_def]);
a (all_asm_fc_tac[]);
a (all_fc_tac [tc∈⋎u_trans_thm]);
(* *** Goal "5" *** *)
a (∃_tac ⌜g y⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "6" *** *)
a (∃_tac ⌜g y⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
val ClCo⋎u_ClIm⋎u_thm = save_pop_thm "ClCo⋎u_ClIm⋎u_thm";
=TEX
}%ignore

\subsubsection{Limits}

In defining operations over ordinals it will be useful to take the limit of a family of sets.
When we come to the ordinals that will be a family of ordinals, but the limit operation can be defined more generally simply as the union of the family.
This pre-ordinal development is placed here since it is another way of applying the replacement principle.

ⓈHOLCONST
│ ⦏Limit⋎u⦎ : ('a GSU → 'a GSU) → 'a GSU → 'a GSU
├────────────────────
│  ∀f α⦁ Limit⋎u f α = ⋃⋎u(Imagep⋎u f α)
■

The first thing we need to ``prove'' is that it yields a set, and then its membership conditions.

=GFT
⦏Set⋎u_Limit⋎u_thm⦎ =
	⊢ ∀ f α⦁ Set⋎u (Limit⋎u f α)
⦏∈⋎u_Limit⋎u_thm⦎ =
	⊢ ∀ f α⦁ x ∈⋎u Limit⋎u f α ⇔ (∃ y⦁ y ∈⋎u α ∧ x ∈⋎u f y)
⦏tc∈⋎u_Limit⋎u_thm⦎ =
	⊢ ∀ f α x⦁ x ∈⋎u⋏+ Limit⋎u f α ⇔ (∃ y⦁ y ∈⋎u α ∧ x ∈⋎u⋏+ f y)
=TEX

\ignore{
=SML
val Limit⋎u_def = get_spec ⌜Limit⋎u⌝;

set_goal([], ⌜∀f α⦁ Set⋎u (Limit⋎u f α)⌝);
a (rewrite_tac [Limit⋎u_def]);
val Set⋎u_Limit⋎u_thm = save_pop_thm "Set⋎u_Limit⋎u_thm";

set_goal([], ⌜∀f α x⦁ x ∈⋎u Limit⋎u f α ⇔ ∃ y⦁ y ∈⋎u α ∧ x ∈⋎u f y⌝);
a (rewrite_tac[Limit⋎u_def]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜e'⌝ THEN SYM_ASMS_T once_asm_rewrite_tac
	THEN contr_tac);
(* *** Goal "2" *** *)
a (∃_tac ⌜f y⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
val ∈⋎u_Limit⋎u_thm = save_pop_thm "∈⋎u_Limit⋎u_thm";

set_goal([], ⌜∀f α x⦁ x ∈⋎u⋏+ Limit⋎u f α ⇔ ∃ y⦁ y ∈⋎u α ∧ x ∈⋎u⋏+ f y ⌝);
a (rewrite_tac[Limit⋎u_def, tc∈⋎u_Imagep⋎u_thm]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[]);
a (var_elim_asm_tac ⌜e = f e'⌝);
(* *** Goal "2" *** *)
a (∃_tac ⌜f y⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
val tc∈⋎u_Limit⋎u_thm = save_pop_thm "tc∈⋎u_Limit⋎u_thm";

add_pc_thms "'gsu-ax" ([]);
add_sc_thms [Set⋎u_Limit⋎u_thm, ∈⋎u_Limit⋎u_thm, tc∈⋎u_Limit⋎u_thm, ClIm⋎u_∅⋎u_thm3] "'gsu-ax";
add_rw_thms [Set⋎u_Limit⋎u_thm, ∈⋎u_Limit⋎u_thm, tc∈⋎u_Limit⋎u_thm, ClIm⋎u_∅⋎u_thm3] "'gsu-ax";

set_merge_pcs ["basic_hol", "'gsu-ax"];
=TEX
}%ignore

=IGN

This will be used for definitions by transfinite induction, in which case the ``base'' case will correspond to images of the empty set, so these are not interesting.
When empty images are excluded there is an analogy for composition of these maps with ordinary functional composition, which results in an associative law.
If this is proven at this level it subsequently yields more specific associative laws, e.g. for ordinal addition and multiplication. 

=IGN
⦏ClIm⋎u_∅⋎u_thm⦎ =
	⊢ ∀ f s⦁ Set⋎u s ⇒ (ClIm⋎u f s = ∅⋎u ⇔ s = ∅⋎u)
⦏ClIm⋎u_∅⋎u_thm2⦎ =
	⊢ ∀ f s⦁ ClIm⋎u f s = ∅⋎u ⇔ s =⋎u ∅⋎u
=TEX

\ignore{
=IGN
set_goal([],⌜∀f s⦁ Set⋎u s ⇒ (ClIm⋎u f s = ∅⋎u ⇔ s = ∅⋎u)⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (gsu_ext_tac);
a (lemma_tac ⌜∀ e⦁ e ∈⋎u ClIm⋎u f s ⇔ e ∈⋎u ∅⋎u⌝
	THEN1 (pure_asm_rewrite_tac[] THEN prove_tac[]));
a (REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜f e⌝);
a (swap_nth_asm_concl_tac 2);
a (rewrite_tac[]);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
a (gsu_ext_tac THEN rewrite_tac[]);
val ClIm⋎u_∅⋎u_thm = save_pop_thm "ClIm⋎u_∅⋎u_thm";

set_goal([], ⌜∀f s⦁ ClIm⋎u f s = ∅⋎u ⇔ s =⋎u ∅⋎u⌝);
a (rewrite_tac[get_spec ⌜$=⋎u⌝] THEN REPEAT ∀_tac);
a (gsu_ext_tac2 ⌜ClIm⋎u f s = ∅⋎u⌝);
a (rewrite_tac[sets_ext_clauses]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜f x⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (PC_T1 "hol1" asm_rewrite_tac [get_spec ⌜X⋎u⌝]);
(* *** Goal "2" *** *)
a (DROP_NTH_ASM_T 2 (asm_tac o (pc_rule1 "hol1" rewrite_rule[get_spec ⌜X⋎u⌝])));
a (asm_rewrite_tac[]); 
(* *** Goal "3" *** *)
a (DROP_NTH_ASM_T 2 (asm_tac o (pc_rule1 "hol1" rewrite_rule[get_spec ⌜X⋎u⌝])));
a (asm_rewrite_tac[]); 
val ClIm⋎u_∅⋎u_thm2 = save_pop_thm "ClIm⋎u_∅⋎u_thm2";
=TEX
}%ignore

\subsection{Recursion Theorems}

To facilitate definition by transfinite induction induction theorems are required which permit various kinds of inductive definition to be proven consistent automatically.

Certain practices in the presentation of inductive definitions facilitate such proofs.
In general, rather than referring directly in the body of such a definition to the function being defined, it is desirable to refer to restricted version of the function obtained by restricting the function to some domain related to the argument of the function by a relationship which is well-founded.

The simplest case of this is to restrict the function to the transitive closure of the set it is applied to.
The two other cases are the use of functional replacement, i.e. the image of a set under a function, and the closed image, i.e. the transitive closure of the image of a set under a function.


To get a recursion theorem we prove first that the functional used in the theorem respects the ordering by membership.

=GFT
⦏◁tc∈⋎u_respects_∈⋎u_thm⦎ =
	⊢ ∀ af⦁ (λ f x⦁ af (x ◁∈⋏+⋎u f) x) respects $∈⋎u

⦏Imagep⋎u_respects_∈⋎u_thm⦎ =
	⊢ ∀ af⦁ (λ f x⦁ af (Imagep⋎u f x) x) respects $∈⋎u

⦏ClIm⋎u_respects_∈⋎u_thm⦎ =
	⊢ ∀ af⦁ (λ f x⦁ af (ClIm⋎u f x) x) respects $∈⋎u
=TEX

The automatic existence proof facility is geared to working with functions over recursive datatypes with constructor functions, and though we don't really want a constructor for this application, it won't work without one.
So we use \emph{CombI}, which is an identity function, as a dummy constructor to trigger the consistency proof.

=GFT
⦏◁tc∈⋎u_recursion_thm⦎ =
	⊢ ∀ af⦁ ∃ f⦁ ∀ x⦁ f (CombI x) = af (x ◁∈⋏+⋎u f) x

⦏Imagep⋎u_recursion_thm⦎ =
	⊢ ∀ af⦁ ∃ f⦁ ∀ x⦁ f (CombI x) = af (Imagep⋎u f x) x

⦏ClIm⋎u_recursion_thm⦎ =
	⊢ ∀ af⦁ ∃ f⦁ ∀ x⦁ f (CombI x) = af (ClIm⋎u f x) x
=TEX

\ignore{
=SML
set_goal([], ⌜∀af⦁ (λ(f:'a GSU → 'b) x⦁ af (x ◁∈⋏+⋎u f) x) respects $∈⋎u⌝);
a (rewrite_tac [get_spec ⌜$respects⌝] THEN REPEAT strip_tac);
a (LEMMA_T ⌜x ◁∈⋏+⋎u g = x ◁∈⋏+⋎u h⌝ rewrite_thm_tac);
a (rewrite_tac [◁tc∈⋎u_def, ext_thm] THEN strip_tac);
a (cond_cases_tac ⌜x' ∈⋎u⋏+ x⌝ THEN REPEAT strip_tac);
a (POP_ASM_T (asm_tac o (rewrite_rule [get_spec ⌜$∈⋎u⋏+⌝])));
a (ALL_ASM_FC_T (MAP_EVERY rewrite_thm_tac) []);
val ◁tc∈⋎u_respects_∈⋎u_thm = save_pop_thm "◁tc∈⋎u_respects_∈⋎u_thm";

set_goal([], ⌜∀af⦁ ∃f:'a GSU → 'b⦁ ∀x⦁ f (CombI x) = af (x ◁∈⋏+⋎u f) x⌝);
a (REPEAT strip_tac THEN rewrite_tac[get_spec ⌜CombI⌝]);
a (∃_tac ⌜fix (λf x⦁ af (x ◁∈⋏+⋎u f) x)⌝);
a (asm_tac ◁tc∈⋎u_respects_∈⋎u_thm);
a (asm_tac gsu_wf_thm1);
a (spec_nth_asm_tac 2 ⌜af⌝);
a (all_fc_tac [get_spec ⌜fix⌝]);
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac[ext_thm]);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac []);
val ◁tc∈⋎u_recursion_thm = save_pop_thm "◁tc∈⋎u_recursion_thm";

set_goal([], ⌜∀af⦁ (λf x⦁ af (Imagep⋎u f x) x) respects $∈⋎u⌝);
a (rewrite_tac [get_spec ⌜$respects⌝] THEN REPEAT strip_tac);
a (LEMMA_T ⌜Imagep⋎u g x = Imagep⋎u h x⌝ rewrite_thm_tac);
a (gsu_ext_tac THEN rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[]);
a (ASM_FC_T (MAP_EVERY (asm_tac o (rewrite_rule [get_spec ⌜$∈⋎u⋏+⌝]))) [tc∈⋎u_incr_thm] );
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[]);
a (ASM_FC_T (MAP_EVERY (asm_tac o (rewrite_rule [get_spec ⌜$∈⋎u⋏+⌝]))) [tc∈⋎u_incr_thm] );
a (asm_fc_tac[]);
a (asm_rewrite_tac[]);
val Imagep⋎u_respects_∈⋎u_thm = save_pop_thm "Imagep⋎u_respects_∈⋎u_thm";

set_goal([], ⌜∀af⦁ ∃f⦁ ∀x⦁ f (CombI x) = af (Imagep⋎u f x) x⌝);
a (REPEAT strip_tac THEN_TRY rewrite_tac[get_spec ⌜CombI⌝]);
a (∃_tac ⌜fix (λf x⦁ af (Imagep⋎u f x) x)⌝);
a (asm_tac Imagep⋎u_respects_∈⋎u_thm);
a (asm_tac gsu_wf_thm1);
a (spec_nth_asm_tac 2 ⌜af⌝);
a (all_fc_tac [get_spec ⌜fix⌝]);
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac[ext_thm]);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac []);
val Imagep⋎u_recursion_thm = save_pop_thm "Imagep⋎u_recursion_thm";

set_goal([], ⌜∀af⦁ (λf x⦁ af (ClIm⋎u f x) x) respects $∈⋎u⌝);
a (rewrite_tac [get_spec ⌜$respects⌝] THEN REPEAT strip_tac);
a (LEMMA_T ⌜ClIm⋎u g x = ClIm⋎u h x⌝ rewrite_thm_tac);
a (gsu_ext_tac THEN rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [tc_incr_thm]);
a (all_asm_fc_tac[]);
a (∃_tac ⌜y⌝ THEN SYM_ASMS_T rewrite_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [tc_incr_thm] THEN all_asm_fc_tac[]);
a (∃_tac ⌜y⌝ THEN SYM_ASMS_T rewrite_tac THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (fc_tac [tc_incr_thm] THEN all_asm_fc_tac[]);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (fc_tac [tc_incr_thm] THEN all_asm_fc_tac[]);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
val ClIm⋎u_respects_∈⋎u_thm = save_pop_thm "ClIm⋎u_respects_∈⋎u_thm";

set_goal([], ⌜∀af⦁ ∃f⦁ ∀x⦁ f (CombI x) = af (ClIm⋎u f x) x⌝);
a (REPEAT strip_tac THEN_TRY rewrite_tac[get_spec ⌜CombI⌝]);
a (∃_tac ⌜fix (λf x⦁ af (ClIm⋎u f x) x)⌝);
a (asm_tac ClIm⋎u_respects_∈⋎u_thm);
a (asm_tac gsu_wf_thm1);
a (spec_nth_asm_tac 2 ⌜af⌝);
a (all_fc_tac [get_spec ⌜fix⌝]);
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac[ext_thm]);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac []);
val ClIm⋎u_recursion_thm = save_pop_thm "ClIm⋎u_recursion_thm";
=TEX
}%ignore

Now we plug in the recursion theorems for use in automatic consistency proofs.
Each is put in a distinct proof context, that particular context is used for consistency proofs of definitions using that recursion principle.
Because of the hack using \emph{CombI} they cannot all be put in the same proof context.

=SML
force_new_pc "'gsu-rec1";
force_new_pc "'gsu-rec2";
force_new_pc "'gsu-rec3";
add_∃_cd_thms [Imagep⋎u_recursion_thm] "'gsu-rec1";
add_∃_cd_thms [◁tc∈⋎u_recursion_thm] "'gsu-rec2";
add_∃_cd_thms [ClIm⋎u_recursion_thm] "'gsu-rec3";
=IGN

val (_,_,_,_,rbjthm1) = evaluate_∃_cd_thm ◁tc∈⋎u_recursion_thm;
val (_,_,_,_,rbjthm2) = evaluate_∃_cd_thm Imagep⋎u_recursion_thm;
CombI_prove_∃_rule
	⌜∃Rank5⋎u⦁ ∀x y⦁ Rank5⋎u y (CombI x)
	= Suc⋎v(x ◁∈⋏+⋎u (Rank5⋎u y)) (⋃⋎u x)⌝;

get_cs_∃_convs "'gsu-ax";

CombI_prove_∃_rule ⌜∃Rank5⋎u⦁ ∀x⦁ Rank5⋎u (CombI x)
	= Ssuc⋎u((x ◁∈⋏+⋎u Rank5⋎u) (⋃⋎u x))⌝;

CombI_prove_∃_rule ⌜∃Rank5⋎u⦁ ∀x⦁ Rank5⋎u (CombI x) = Suc⋎u(Imagep⋎u Rank5⋎u x)⌝;

prove_∃_conv ⌜P x ⇒ ∃ f⦁ P f⌝;

fun rt_conv rt =
	let val (_,_,_,_,et) = evaluate_∃_cd_thm rt
	in simple_∃_cd_thm_conv et
	end ;

rt_conv Imagep⋎u_recursion_thm ⌜∃Rank5⋎u⦁ ∀x⦁ Rank5⋎u (CombI x) = Suc⋎u(Imagep⋎u Rank5⋎u x)⌝;
=TEX

\subsection{Set Clauses}

For the application of the principle of extensionality we need to know that the expressions on either side of the equality are sets.

The following theorem is useful in automating the proofs.


=GFT
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y r p f⦁
		Set⋎u (ℙ⋎u x)
	∧	Set⋎u (⋃⋎u x)
	∧	Set⋎u (RelIm⋎u r x)
	∧	Set⋎u (Sep⋎u x p)
	∧	Set⋎u (Gx⋎u x)
	∧	Set⋎u (∅⋎u)
	∧	Set⋎u (Imagep⋎u f y)
	∧	Set⋎u (Pair⋎u x y)
	∧	Set⋎u (Unit⋎u x)
	∧	Set⋎u (x ∪⋎u y)
	∧	Set⋎u (⋂⋎u x)
	∧	Set⋎u (x ∩⋎u y)
	∧	Set⋎u (TrCl⋎u x)
	∧	Set⋎u (ClIm⋎u f x)
⌝);
a (rewrite_tac[Set⋎u_TrCl⋎u_thm]);
val Set⋎u_clauses = save_pop_thm "Set⋎u_clauses";
=TEX
}%ignore

\subsection{Proof Context}

To simplify Subsequent proofs a new "proof context" is created enabling automatic use of the results now available.

\subsubsection{Principles}

The only principle I know of which assists with elementary proofs in set theory is the principle that set theoretic conjectures can be reduced to the predicate calculus by using extensional rules for relations and for operators.

Too hasty a reduction can be overkill and may convert a simple conjecture into an unintelligible morass.
We have sometimes in the past used made available two proof contexts, an aggressive extensional one, and a milder non-extensional one.
However, the extensional rules for the operators are fairly harmless, expansion is triggered by the extensional rules for the relations (equality and Subset), so a proof context containing the former together with a suitable theorem for the latter gives good control.

\subsubsection{Theorems Used Recklessly}

This is pretty much guesswork, only time will tell whether this is the best collection.

=SML
val gsu_ax_thms = [
	∅⋎u_thm,
	get_spec ⌜ℙ⋎u⌝,
	⋃⋎u_def,
	Imagep⋎u_thm,
	Imagep⋎u_∅⋎u_thm,
	tc∈⋎u_Imagep⋎u_thm,
	Pair⋎u_eq_thm,
	Pair⋎u_def,
	Unit⋎u_eq_thm,
	Unit⋎u_thm,
	Pair⋎u_Unit⋎u_eq_thm,
	Unit⋎u_Pair⋎u_eq_thm,
	Sep⋎u_thm,
	∪⋎u_def,
	∩⋎u_thm
];

val gsu_opext_clauses =
	(all_∀_intro
	o list_∧_intro
	o (map all_∀_elim))
	gsu_ax_thms;
save_thm ("gsu_opext_clauses", gsu_opext_clauses);
=TEX

\subsubsection{Theorems Used Cautiously}

The following theorems are too aggressive for general use in the proof context but are needed when attempting automatic proof.
When an extensional proof is appropriate it can be initiated by a cautious (i.e. a "once") rewrite using the following clauses, after which the extensional rules in the proof context will be triggered.

[This used to be just two extensionality theorems, but one is no longer so its a unit list.]

=SML
val gsu_relext_clauses =
	(all_∀_intro
	o list_∧_intro
	o (map all_∀_elim))
	[⊆⋎u_def, eq⋎u_ext_thm];
save_thm ("gsu_relext_clauses", gsu_relext_clauses);
=TEX

There are a number of important theorems, such as well-foundedness and galaxy closure which have not been mentioned in this context.
The character of these theorems makes them unsuitable for the proof context, their application requires thought.


\subsubsection{Automatic Proof}

The basic proof automation is augmented by adding a preliminary rewrite with the relational extensionality clauses.

=SML
fun gsu_ax_prove_conv thl =
	TRY_C (pure_rewrite_conv [gsu_relext_clauses])
	THEN_TRY_C gsu_ext_conv
	THEN_C (basic_prove_conv thl);
=TEX

\subsubsection{Proof Context 'gsu-ax}

=SML
val nost⋎u_thms = [
	galaxy⋎u_Gx⋎u,
	t_in_Gx⋎u_t_thm,
	Set⋎uImagep⋎u_thm,
	Imagep⋎u_∅⋎u_thm,
	Set⋎uℙ⋎u_thm,
	Set⋎u⋃⋎u_thm,
	Set⋎uRelIm⋎u_thm,
	Set⋎u_Sep⋎u_thm,
	Set⋎uUnit⋎u_thm,
	Set⋎u⋂⋎u_thm,
	Set⋎u∩⋎u_thm,
	set⋎u_eq⋎u_thm,
	set⋎u_eq⋎u_thm2,
	Set⋎u_TrCl⋎u_thm,
	∈⋎u_ClIm⋎u_thm,
	tc∈⋎u_ClIm⋎u_thm,
	TrCl⋎u_ext_thm2,
	tc∈⋎u_TrCl⋎u_thm,
	tc∈⋎u_∪⋎u_thm,
	tc∈⋎u_⋃⋎u_thm
];

add_rw_thms (gsu_ax_thms @ nost⋎u_thms) "'gsu-ax";
add_sc_thms (gsu_ax_thms @ nost⋎u_thms) "'gsu-ax";
add_st_thms gsu_ax_thms "'gsu-ax";
set_pr_conv gsu_ax_prove_conv "'gsu-ax";
set_pr_tac
	(conv_tac o gsu_ax_prove_conv)
	"'gsu-ax";
commit_pc "'gsu-ax";
=TEX

Using the proof context "'gsu-ax" elementary results in gsu are now provable automatically on demand.
For this reason it is not necessary to prove in advance of needing them results such as the associativity of intersection, since they can be proven when required by an expression of the form "prove rule[] term" which proves {\it term} and returns it as a theorem.
If the required proof context for doing this is not in place the form ``
=INLINEFT
merge_pcs_rule ["basic_hol", 'gsu-ax"] (prove_rule []) term
=TEX
'' may be used.
Since this is a little cumbersome we define the function {\it $gsu\_ax\_rule$} and illustrate its use as follows:

=SML
val gsu_ax_rule =
	(merge_pcs_rule1
	["basic_hol", "'gsu-ax"]
	prove_rule) [];
val gsu_ax_conv = 
	MERGE_PCS_C1
	["basic_hol", "'gsu-ax"]
	prove_conv;
val gsu_ax_tac =
	conv_tac o gsu_ax_conv;
=TEX

\subsubsection{Examples}

The following are examples of the elementary results which are now proven automatically:
=SML
gsu_ax_rule ⌜
	a ∩⋎u (b ∩⋎u c)
	= (a ∩⋎u b) ∩⋎u c⌝;
gsu_ax_rule ⌜
	a ∩⋎u (b ∩⋎u c)
	= (a ∩⋎u b) ∩⋎u c⌝;
gsu_ax_rule ⌜a ∩⋎u b ⊆⋎u b⌝;
(* gsu_ax_rule ⌜∅⋎u ∪⋎u b = b⌝; *)
gsu_ax_rule ⌜
	a ⊆⋎u b ∧ c ⊆⋎u d
	⇒ a ∩⋎u c ⊆⋎u b ∩⋎u d⌝;
gsu_ax_rule ⌜Sep⋎u b p ⊆⋎u b⌝;
gsu_ax_rule ⌜a ⊆⋎u b ⇒
	Imagep⋎u f a ⊆⋎u Imagep⋎u f b⌝;
=IGN
Imagep⋎u_axiom;
set_goal([],⌜a ⊆⋎u b ∧ c ⊆⋎u d
	⇒ Imagep⋎u f (a ∩⋎u c)
	⊆⋎u Imagep⋎u f (b ∩⋎u d)⌝);
a (once_rewrite_tac
	[gsu_relext_clauses]);
a (gsu_ax_tac[]);
a (rewrite_tac[]);
a (prove_tac[]);
a contr_tac;
Sep⋎u_thm;
=TEX


\section{Products and Sums}

A new "gsu-fun" theory is created as a child of "gsu-ax".
The theory will contain the definitions of ordered pairs, cartesian product, relations and functions, dependent products (functions), dependent sums (disjoint unions) and related material for general use.

=SML
open_theory "gsu-ax";
force_new_theory "gsu-fun";
force_new_pc "'gsu-fun";
merge_pcs ["'savedthm_cs_∃_proof"] "'gsu-fun";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];
=TEX

\subsection{Ordered Pairs}

=SML
declare_infix (240,"↦⋎u");
=TEX

I first attempted to define ordered pairs in a more abstract way than by explicit use of the Wiener-Kuratovski representation, but this gace me problems so I eventually switched to the explicit definition.

This influences the development of the theory, since the first thing I do is to replicate the previously used defining properties.

ⓈHOLCONST
│ $⦏↦⋎u⦎ : 'a GSU → 'a GSU → 'a GSU
├────────────
│ ∀s t⦁ (s ↦⋎u t) = Pair⋎u (Unit⋎u s) (Pair⋎u s t)
■

=GFT
⦏Set⋎u↦⋎u_thm⦎ =			⊢ ∀ s t⦁ Set⋎u (s ↦⋎u t)
⦏↦⋎u_eq_thm⦎ =			⊢ ∀ s t u v⦁ (s ↦⋎u t = u ↦⋎u v) = (s = u ∧ t = v)
⦏Pair⋎u_∈⋎u_↦⋎u_thm⦎ =		⊢ ∀s t⦁ Pair⋎u s t ∈⋎u s ↦⋎u t
⦏Pair⋎u_∈⋎u_Gx⋎u_↦⋎u_thm⦎ =	⊢ ∀ s t⦁ Pair⋎u s t ∈⋎u Gx⋎u (s ↦⋎u t)
⦏↦⋎u_spec_thm⦎ =		⊢ (∀ s t u v⦁ (s ↦⋎u t = u ↦⋎u v) = (s = u ∧ t = v))
       				∧ (∀ s t⦁ Pair⋎u s t ∈⋎u s ↦⋎u t)
       				∧ (∀ s t⦁ Pair⋎u s t ∈⋎u Gx⋎u (s ↦⋎u t))
⦏↦⋎u_∈⋎u_Gx⋎u_Pair⋎u_thm⦎ =	⊢ ∀ s t⦁ s ↦⋎u t ∈⋎u Gx⋎u (Pair⋎u s t)
=TEX

\ignore{
=SML
val ↦⋎u_def = get_spec ⌜$↦⋎u⌝;

val Set⋎u↦⋎u_thm = prove_thm("Set⋎u↦⋎u_thm", ⌜∀s t:'a GSU⦁ Set⋎u(s ↦⋎u t)⌝, rewrite_tac [↦⋎u_def]);

set_goal([], ⌜∀s t u v:'a GSU⦁
	(s ↦⋎u t = u ↦⋎u v ⇔ s = u ∧ t = v)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[↦⋎u_def] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN REPEAT strip_tac);
val ↦⋎u_eq_thm = save_pop_thm "↦⋎u_eq_thm";
 
set_goal([], ⌜∀s t⦁ Pair⋎u s t ∈⋎u (s ↦⋎u t)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[↦⋎u_def] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN REPEAT strip_tac);
val Pair⋎u_∈⋎u_↦⋎u_thm = save_pop_thm "Pair⋎u_∈⋎u_↦⋎u_thm";

add_pc_thms "'gsu-fun" [↦⋎u_eq_thm];
add_rw_thms [Set⋎u↦⋎u_thm, Pair⋎u_∈⋎u_↦⋎u_thm] "'gsu-fun";
add_sc_thms [Set⋎u↦⋎u_thm, Pair⋎u_∈⋎u_↦⋎u_thm] "'gsu-fun";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];

set_goal([], ⌜∀s t⦁ Pair⋎u s t ∈⋎u Gx⋎u (s ↦⋎u t)⌝);
a (rewrite_tac[↦⋎u_def] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN REPEAT strip_tac);
a (lemma_tac ⌜galaxy⋎u (Gx⋎u (Pair⋎u s t))⌝
	THEN1 rewrite_tac [galaxy⋎u_Gx⋎u]);
a (lemma_tac ⌜Pair⋎u s t ∈⋎u Gx⋎u (Pair⋎u s t)⌝
	THEN1 rewrite_tac [t_in_Gx⋎u_t_thm]);
a (strip_asm_tac (∀_elim ⌜Gx⋎u (Pair⋎u s t)⌝ GClose⋎uPair⋎u));
a (lemma_tac ⌜(Unit⋎u s) ∈⋎u Gx⋎u (Pair⋎u s t)⌝);
(* *** Goal "1" *** *)
a (lemma_tac ⌜s ∈⋎u Gx⋎u (Pair⋎u s t)⌝);
(* *** Goal "1.1" *** *)
a (fc_tac [galaxies⋎u_transitive_thm]);
a (fc_tac [Transitive⋎u_def]);
a (LEMMA_T ⌜Pair⋎u s t ⊆⋎u Gx⋎u (Pair⋎u s t)⌝ ante_tac
	THEN1 asm_fc_tac[]
	THEN once_rewrite_tac [gsu_relext_clauses]
	THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜s⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [Pair⋎u_def]);
(* *** Goal "1.2" *** *)
a (strip_asm_tac (∀_elim ⌜Gx⋎u (Pair⋎u s t)⌝ GClose⋎uUnit⋎u)
	THEN asm_fc_tac[]);
(* *** Goal "2" *** *)
a (LEMMA_T ⌜(Pair⋎u s t) ∈⋎u (Pair⋎u (Unit⋎u s) (Pair⋎u s t))⌝asm_tac 
	THEN1 (once_rewrite_tac [Pair⋎u_def]
		THEN REPEAT strip_tac));
a (LEMMA_T ⌜Gx⋎u (Pair⋎u s t) ⊆⋎u Gx⋎u (Pair⋎u (Unit⋎u s) (Pair⋎u s t))⌝ ante_tac
	THEN1 (all_fc_tac [Gx⋎u_mono_thm2]));
a (once_rewrite_tac [⊆⋎u_def]
	THEN STRIP_T (fn x => all_fc_tac [x]));
val Pair⋎u_∈⋎u_Gx⋎u_↦⋎u_thm = save_pop_thm "Pair⋎u_∈⋎u_Gx⋎u_↦⋎u_thm";

set_goal([], ⌜∀s t⦁ s ↦⋎u t ∈⋎u Gx⋎u (Pair⋎u s t)⌝);
a (REPEAT strip_tac THEN rewrite_tac [↦⋎u_def]);
a (lemma_tac ⌜galaxy⋎u (Gx⋎u (Pair⋎u s t))⌝
	THEN1 rewrite_tac [galaxy⋎u_Gx⋎u]);
a (lemma_tac ⌜Pair⋎u s t ∈⋎u Gx⋎u (Pair⋎u s t)⌝
	THEN1 rewrite_tac [t_in_Gx⋎u_t_thm]);
a (lemma_tac ⌜(Unit⋎u s) ∈⋎u Gx⋎u (Pair⋎u s t)⌝);
(* *** Goal "1" *** *)
a (lemma_tac ⌜s ∈⋎u Gx⋎u (Pair⋎u s t)⌝);
(* *** Goal "1.1" *** *)
a (fc_tac [galaxies⋎u_transitive_thm]);
a (fc_tac [Transitive⋎u_def]);
a (LEMMA_T ⌜Pair⋎u s t ⊆⋎u Gx⋎u (Pair⋎u s t)⌝ ante_tac
	THEN1 asm_fc_tac[]
	THEN once_rewrite_tac [gsu_relext_clauses]
	THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜s⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [Pair⋎u_def]);
(* *** Goal "1.2" *** *)
a (strip_asm_tac (∀_elim ⌜Gx⋎u (Pair⋎u s t)⌝ GClose⋎uUnit⋎u)
	THEN asm_fc_tac[]);
(* *** Goal "2" *** *)
a (strip_asm_tac (list_∀_elim [⌜Gx⋎u (Pair⋎u s t)⌝] GClose⋎uPair⋎u));
a (all_asm_fc_tac[]);
val ↦⋎u_∈⋎u_Gx⋎u_Pair⋎u_thm = save_pop_thm "↦⋎u_∈⋎u_Gx⋎u_Pair⋎u_thm";

val ↦⋎u_spec_thm = list_∧_intro [↦⋎u_eq_thm, Pair⋎u_∈⋎u_↦⋎u_thm, Pair⋎u_∈⋎u_Gx⋎u_↦⋎u_thm];

=IGN

add_pc_thms "'gsu-fun" [↦⋎u_spec_thm];
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];
=TEX
}%ignore

=GFT
⦏¬↦⋎u∅⋎u_thm⦎ =	⊢ ∀ x y⦁ ¬ x ↦⋎u y = ∅⋎u
⦏¬∅⋎u↦⋎u_thm⦎ =	⊢ ∀ x y⦁ ¬ ∅⋎u = x ↦⋎u y
⦏GClose⋎u↦⋎u_thm⦎ =	⊢ ∀ g⦁ galaxy⋎u g ⇒ (∀ s t⦁ s ∈⋎u g ∧ t ∈⋎u g ⇒ s ↦⋎u t ∈⋎u g)
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y⦁ ¬ x ↦⋎u y = ∅⋎u⌝);
a (REPEAT strip_tac THEN once_rewrite_tac [gsu_ext_conv ⌜x ↦⋎u y = ∅⋎u⌝] THEN REPEAT strip_tac);
a (∃_tac ⌜Pair⋎u x y⌝ THEN rewrite_tac [↦⋎u_spec_thm]);
val ¬↦⋎u∅⋎u_thm = save_pop_thm "¬↦⋎u∅⋎u_thm";

set_goal([], ⌜∀x y⦁ ¬ ∅⋎u = x ↦⋎u y⌝);
a (REPEAT strip_tac THEN once_rewrite_tac [gsu_ext_conv ⌜∅⋎u = x ↦⋎u y⌝] THEN REPEAT strip_tac);
a (∃_tac ⌜Pair⋎u x y⌝ THEN rewrite_tac [↦⋎u_spec_thm]);
val ¬∅⋎u↦⋎u_thm = save_pop_thm "¬∅⋎u↦⋎u_thm";

set_goal([], ⌜∀g⦁  galaxy⋎u g ⇒ (∀s t⦁ s ∈⋎u g ∧ t ∈⋎u g ⇒ s ↦⋎u t ∈⋎u g)⌝);
a (REPEAT strip_tac THEN rewrite_tac[↦⋎u_def]);
a (all_fc_tac [GClose⋎u_fc_clauses2]);
a (all_fc_tac [GClose⋎u_fc_clauses2]);
val GClose⋎u↦⋎u_thm = save_pop_thm "GClose⋎u↦⋎u_thm";
=TEX
}%ignore

=GFT
⦏tc∈⋎u_↦⋎u_left_thm⦎ =	⊢ ∀ s t⦁ s ∈⋎u⋏+ s ↦⋎u t
⦏tc∈⋎u_↦⋎u_right_thm⦎ =	⊢ ∀ s t⦁ t ∈⋎u⋏+ s ↦⋎u t
=TEX

\ignore{
=SML
set_goal([], ⌜∀s t:'a GSU⦁ s ∈⋎u⋏+ s ↦⋎u t⌝);
a (REPEAT ∀_tac THEN rewrite_tac[↦⋎u_def]);
a (lemma_tac ⌜Unit⋎u s ∈⋎u⋏+ Pair⋎u (Unit⋎u s) (Pair⋎u s t)⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜s ∈⋎u⋏+ Unit⋎u s⌝ THEN1 rewrite_tac[]);
a (all_fc_tac[tc∈⋎u_trans_thm]);
val tc∈⋎u_↦⋎u_left_thm = save_pop_thm "tc∈⋎u_↦⋎u_left_thm";

set_goal([], ⌜∀s t:'a GSU⦁ t ∈⋎u⋏+ s ↦⋎u t⌝);
a (REPEAT ∀_tac THEN rewrite_tac[↦⋎u_def]);
a (lemma_tac ⌜Pair⋎u s t ∈⋎u⋏+ Pair⋎u (Unit⋎u s) (Pair⋎u s t)⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜t ∈⋎u⋏+ Pair⋎u s t⌝ THEN1 rewrite_tac[]);
a (all_fc_tac[tc∈⋎u_trans_thm]);
val tc∈⋎u_↦⋎u_right_thm = save_pop_thm "tc∈⋎u_↦⋎u_right_thm";
=TEX


=GFT
⦏↦⋎u_tc_thm⦎ =	⊢ ∀ x y⦁ tc $∈⋎u x (x ↦⋎u y) ∧ tc $∈⋎u y (x ↦⋎u y)
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y⦁ tc $∈⋎u x (x ↦⋎u y) ∧ tc $∈⋎u y (x ↦⋎u y)⌝);
a (REPEAT ∀_tac);
a (LEMMA_T ⌜Pair⋎u x y ∈⋎u (x ↦⋎u y) ∧ x ∈⋎u Pair⋎u x y ∧ y ∈⋎u Pair⋎u x y⌝
	(REPEAT_TTCL ∧_THEN asm_tac)
	THEN1 (rewrite_tac [↦⋎u_spec_thm, Pair⋎u_∈⋎u_thm]
		THEN all_var_elim_asm_tac));
a (fc_tac [tc_incr_thm]);
a (all_fc_tac [tran_tc_thm2]
	THEN asm_rewrite_tac[]);
val ↦⋎u_tc_thm = save_pop_thm "↦⋎u_tc_thm";
=TEX


=SML
add_pc_thms "'gsu-fun" [¬↦⋎u∅⋎u_thm, ¬∅⋎u↦⋎u_thm];
add_rw_thms [↦⋎u_∈⋎u_Gx⋎u_Pair⋎u_thm, tc∈⋎u_↦⋎u_left_thm, tc∈⋎u_↦⋎u_right_thm] "'gsu-fun";
add_sc_thms [↦⋎u_∈⋎u_Gx⋎u_Pair⋎u_thm, tc∈⋎u_↦⋎u_left_thm, tc∈⋎u_↦⋎u_right_thm] "'gsu-fun";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];
=TEX
}%ignore

\subsubsection{Projections}

The following functions may be used for extracting the components of ordered pairs.

\ignore{
=SML
set_goal([], ⌜∃ Fst⋎u Snd⋎u⦁
∀s t⦁
	Fst⋎u(s ↦⋎u t) = s
	∧ Snd⋎u(s ↦⋎u t) = t⌝);
a (∃_tac ⌜λp⦁εx⦁∃y⦁p=x ↦⋎u y⌝);
a (∃_tac ⌜λp⦁εy⦁∃x⦁p=x ↦⋎u y⌝);
a (rewrite_tac[] THEN REPEAT ∀_tac);
a (all_ε_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜t⌝ THEN ∃_tac ⌜s⌝
 THEN prove_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜s⌝ THEN ∃_tac ⌜t⌝
 THEN prove_tac[]);
(* *** Goal "3" *** *)
a (∃_tac ⌜t⌝ THEN ∃_tac ⌜s⌝
 THEN prove_tac[]);
(* *** Goal "4" *** *)
a (eq_sym_nth_asm_tac 1);
a (eq_sym_nth_asm_tac 4);
a (asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Fst⋎u⦎ ⦏Snd⋎u⦎ : 'a GSU → 'a GSU
├──────────
│ ∀s t⦁ Fst⋎u(s ↦⋎u t) = s	∧ Snd⋎u(s ↦⋎u t) = t
■

=GFT
=TEX

\ignore{
=SML
set_goal([], ⌜∀s t g⦁ galaxy g ∧ s ↦⋎u t ∈ g ⇒ s ∈ g ∧ t ∈ g⌝);

=TEX
}%ignore




=SML
add_pc_thms "'gsu-fun" [get_spec ⌜Fst⋎u⌝];
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];
=TEX
}%ignore

\subsubsection{MkPair and MkTriple}

It proves convenient to have constructors which take HOL pairs and triples as parameters.

ⓈHOLCONST
│ ⦏MkPair⋎u⦎ : 'a GSU × 'a GSU → 'a GSU
├──────────
│ ∀lr⦁ MkPair⋎u lr = (Fst lr) ↦⋎u (Snd lr)
■

ⓈHOLCONST
│ ⦏MkTriple⋎u⦎ : 'a GSU × 'a GSU × 'a GSU → 'a GSU
├──────────
│ ∀t⦁ MkTriple⋎u t = (Fst t) ↦⋎u (MkPair⋎u (Snd t))
■

\ignore{
=IGN

set_goal([], ⌜∀x y⦁ x ∈⋎u⋏+ MkPair⋎u ⌝);

=TEX
}%ignore

\subsection{Relations}

ⓈHOLCONST
│ ⦏Rel⋎u⦎ : 'a GSU → BOOL
├───────────
│ ∀x⦁ Rel⋎u x ⇔ ∀y⦁ y ∈⋎u x ⇒ ∃s t⦁ y = s ↦⋎u t
■

\ignore{
=SML
val Rel⋎u_def = get_spec ⌜Rel⋎u⌝;
=TEX
}%ignore

=GFT
⦏Rel⋎u_∅⋎u_thm⦎ =	⊢ Rel⋎u ∅⋎u
=TEX

\ignore{
=SML
val Rel⋎u_∅⋎u_thm = prove_thm (
	"Rel⋎u_∅⋎u_thm",
	⌜Rel⋎u ∅⋎u⌝,
	prove_tac[get_spec⌜Rel⋎u⌝]);
=TEX
}%ignore

The domain is the set of elements which are related to something under the relationship.

ⓈHOLCONST
│ ⦏Dom⋎u⦎ : 'a GSU → 'a GSU
├──────────
│ ∀x⦁ Dom⋎u x = Sep⋎u (Gx⋎u x) (λw⦁ ∃v⦁ w ↦⋎u v ∈⋎u x)
■

=GFT
⦏Set⋎uDom⋎u_thm⦎ =	⊢ ∀ r⦁ Set⋎u (Dom⋎u r)
⦏Dom⋎u_∅⋎u_thm⦎ =		⊢ Dom⋎u ∅⋎u = ∅⋎u
⦏Dom⋎u_thm⦎ =		⊢ ∀ r y⦁ y ∈⋎u Dom⋎u r ⇔ (∃ x⦁ y ↦⋎u x ∈⋎u r)
⦏Dom⋎u_Gx⋎u_thm⦎ =	⊢ ∀ r⦁ Dom⋎u r ∈⋎u Gx⋎u r
⦏GClose⋎u_Dom⋎u_thm⦎ =	⊢ ∀ g⦁ galaxy⋎u g ⇒ (∀ r⦁ r ∈⋎u g ⇒ Dom⋎u r ∈⋎u g)
=TEX

\ignore{
=SML
val Dom⋎u_def = get_spec ⌜Dom⋎u⌝;

val Set⋎uDom⋎u_thm = prove_thm ("Set⋎uDom⋎u_thm", ⌜∀r⦁ Set⋎u(Dom⋎u r)⌝, rewrite_tac [Dom⋎u_def]);

add_rw_thms [Set⋎uDom⋎u_thm] "'gsu-fun";
add_sc_thms [Set⋎uDom⋎u_thm] "'gsu-fun";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];

set_goal([],⌜Dom⋎u ∅⋎u = ∅⋎u⌝);
a (rewrite_tac[gsu_ext_conv ⌜Dom⋎u ∅⋎u = ∅⋎u⌝] THEN prove_tac[get_spec ⌜Dom⋎u⌝]);
val Dom⋎u_∅⋎u_thm = save_pop_thm "Dom⋎u_∅⋎u_thm";

set_goal([], ⌜∀r y⦁ y ∈⋎u Dom⋎u r ⇔ ∃ x⦁ y ↦⋎u x ∈⋎u r⌝);
a (rewrite_tac [Dom⋎u_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (LEMMA_T  ⌜(Pair⋎u y x) ∈⋎u Gx⋎u (y ↦⋎u x)⌝ asm_tac
	THEN1 rewrite_tac [↦⋎u_spec_thm]);
a (lemma_tac ⌜Gx⋎u (y ↦⋎u x) ⊆⋎u Gx⋎u r⌝ THEN1 fc_tac [Gx⋎u_mono_thm2]);
a (LEMMA_T ⌜y ∈⋎u Pair⋎u y x⌝ asm_tac THEN1 rewrite_tac []);
a (lemma_tac ⌜y ∈⋎u Gx⋎u (y ↦⋎u x)⌝);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜galaxy⋎u (Gx⋎u (y ↦⋎u x))⌝ THEN1 rewrite_tac[galaxy⋎u_Gx⋎u]);
a (fc_tac [galaxies⋎u_transitive_thm]);
a (fc_tac [Transitive⋎u_def]);
a (ASM_FC_T (MAP_EVERY ante_tac) []
	THEN once_rewrite_tac [⊆⋎u_def]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "2.2" *** *)
a (DROP_NTH_ASM_T 3 (asm_tac o (once_rewrite_rule [get_spec⌜$⊆⋎u⌝])));
a (spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "3" *** *)
a (∃_tac ⌜x⌝ THEN strip_tac);
val Dom⋎u_thm = save_pop_thm "Dom⋎u_thm";

set_goal([], ⌜∀r⦁ Dom⋎u r ∈⋎u Gx⋎u r⌝);
a (strip_tac THEN rewrite_tac [Dom⋎u_def]);
a (lemma_tac ⌜galaxy⋎u (Gx⋎u r)⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜Sep⋎u (Gx⋎u r) (λ w⦁ ∃ v⦁ w ↦⋎u v ∈⋎u r) = Sep⋎u (⋃⋎u (⋃⋎u r)) (λ w⦁ ∃ v⦁ w ↦⋎u v ∈⋎u r)⌝
	THEN1 (rewrite_tac [gsu_ext_conv ⌜Sep⋎u (Gx⋎u r) (λ w⦁ ∃ v⦁ w ↦⋎u v ∈⋎u r) = Sep⋎u (⋃⋎u (⋃⋎u r)) (λ w⦁ ∃ v⦁ w ↦⋎u v ∈⋎u r)⌝] THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (∃_tac ⌜Pair⋎u e v⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜e ↦⋎u v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (lemma_tac ⌜e ∈⋎u⋏+ r⌝ THEN1 (
	ufc_tac [tc∈⋎u_incr_thm]
	THEN REPEAT_N 2 (all_ufc_tac [tc∈⋎u_trans_thm])));
a (asm_tac t_in_Gx⋎u_t_thm);
a (all_ufc_tac [tc∈⋎u_incr_thm]);
a (all_ufc_tac [tc∈⋎u_trans_thm]);
a (all_fc_tac [GClose⋎u_tc∈⋎u_thm]);
(* *** Goal "4" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "5" *** *)
a (asm_rewrite_tac[]);
a (lemma_tac ⌜r ∈⋎u Gx⋎u r⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜⋃⋎u r ∈⋎u Gx⋎u r⌝ THEN1 all_fc_tac[GClose⋎u_fc_clauses]);
a (lemma_tac ⌜(⋃⋎u (⋃⋎u r)) ∈⋎u Gx⋎u r⌝ THEN1 (all_fc_tac[GClose⋎u_fc_clauses]));
a (all_fc_tac [GClose⋎u_fc_clauses]);
a (asm_rewrite_tac[]);
val Dom⋎u_Gx⋎u_thm = save_pop_thm "Dom⋎u_Gx⋎u_thm"; 

set_goal([], ⌜∀g⦁ galaxy⋎u g ⇒ ∀r⦁ r ∈⋎u g ⇒ Dom⋎u r ∈⋎u g⌝);
a (REPEAT strip_tac THEN rewrite_tac [Dom⋎u_def]);
a (lemma_tac ⌜galaxy⋎u (Gx⋎u r)⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜Sep⋎u (Gx⋎u r) (λ w⦁ ∃ v⦁ w ↦⋎u v ∈⋎u r) = Sep⋎u (⋃⋎u (⋃⋎u r)) (λ w⦁ ∃ v⦁ w ↦⋎u v ∈⋎u r)⌝
	THEN1 (rewrite_tac [gsu_ext_conv ⌜Sep⋎u (Gx⋎u r) (λ w⦁ ∃ v⦁ w ↦⋎u v ∈⋎u r) = Sep⋎u (⋃⋎u (⋃⋎u r)) (λ w⦁ ∃ v⦁ w ↦⋎u v ∈⋎u r)⌝] THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (∃_tac ⌜Pair⋎u e v⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜e ↦⋎u v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (lemma_tac ⌜e ∈⋎u⋏+ r⌝ THEN1 (
	ufc_tac [tc∈⋎u_incr_thm]
	THEN REPEAT_N 2 (all_ufc_tac [tc∈⋎u_trans_thm])));
a (asm_tac t_in_Gx⋎u_t_thm);
a (all_ufc_tac [tc∈⋎u_incr_thm]);
a (all_ufc_tac [tc∈⋎u_trans_thm]);
a (all_fc_tac [GClose⋎u_tc∈⋎u_thm]);
(* *** Goal "4" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "5" *** *)
a (asm_rewrite_tac[]);
a (lemma_tac ⌜r ∈⋎u Gx⋎u r⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜⋃⋎u r ∈⋎u Gx⋎u r⌝ THEN1 all_fc_tac[GClose⋎u_fc_clauses]);
a (lemma_tac ⌜(⋃⋎u (⋃⋎u r)) ∈⋎u Gx⋎u r⌝ THEN1 (all_fc_tac[GClose⋎u_fc_clauses]));
a (lemma_tac ⌜⋃⋎u r ∈⋎u g⌝ THEN1 all_fc_tac [GClose⋎u_fc_clauses]);
a (lemma_tac ⌜⋃⋎u (⋃⋎u r) ∈⋎u g⌝ THEN1 all_fc_tac [GClose⋎u_fc_clauses]);
a (lemma_tac ⌜∀ p⦁ Sep⋎u (⋃⋎u (⋃⋎u r)) p ∈⋎u g⌝ THEN1 all_fc_tac [GClose⋎u_fc_clauses]);
a (asm_rewrite_tac[]);
val GClose⋎u_Dom⋎u_thm = save_pop_thm "GClose⋎u_Dom⋎u_thm";
=TEX
}%ignore

=GFT
⦏tc∈⋎u_Dom⋎u_thm⦎ = ⊢ ∀ x⦁ x ∈⋎u⋏+ Dom⋎u y ⇒ x ∈⋎u⋏+ y
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y⦁ x ∈⋎u⋏+ Dom⋎u y ⇒ x ∈⋎u⋏+ y⌝);
a (REPEAT strip_tac);
a (fc_tac [tc∈⋎u_cases_thm]);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac);
a (rewrite_tac [Dom⋎u_thm] THEN REPEAT strip_tac);
a (lemma_tac ⌜$∈⋎u⋏+ x (x ↦⋎u x')⌝ THEN1 rewrite_tac [tc∈⋎u_↦⋎u_left_thm]);
a (fc_tac [tc∈⋎u_incr_thm]);
a (all_fc_tac [tc∈⋎u_trans_thm]);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac);
a (rewrite_tac [Dom⋎u_thm] THEN REPEAT strip_tac);
a (lemma_tac ⌜$∈⋎u⋏+ z (z ↦⋎u x')⌝ THEN1 rewrite_tac [tc∈⋎u_↦⋎u_left_thm]);
a (fc_tac [tc∈⋎u_incr_thm]);
a (all_ufc_tac [tc∈⋎u_trans_thm]);
a (all_ufc_tac [tc∈⋎u_trans_thm]);
val tc∈⋎u_Dom⋎u_thm = save_pop_thm "tc∈⋎u_Dom⋎u_thm";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Ran⋎u⦎ : 'a GSU → 'a GSU
├────────────
│ ∀x⦁ Ran⋎u x = Sep⋎u (Gx⋎u x) (λw⦁ ∃v⦁ v ↦⋎u w ∈⋎u x)
■

=GFT
⦏Set⋎uRan⋎u_thm⦎ =	⊢ ∀ s⦁ Set⋎u (Ran⋎u s)
⦏Ran⋎u_∅⋎u_thm⦎ =		⊢ Ran⋎u ∅⋎u = ∅⋎u
⦏Ran⋎u_thm⦎ =		⊢ ∀r y⦁ y ∈⋎u Ran⋎u r ⇔ ∃ x⦁ x ↦⋎u y ∈⋎u r
⦏GClose⋎u_Ran⋎u_thm⦎ =	⊢ ∀ g⦁ galaxy⋎u g ⇒ (∀ r⦁ r ∈⋎u g ⇒ Ran⋎u r ∈⋎u g)
⦏tc∈⋎u_Ran⋎u_thm⦎ = 		⊢ ∀ x y⦁ x ∈⋎u⋏+ Ran⋎u y ⇒ x ∈⋎u⋏+ y
=TEX

\ignore{
=SML
val Ran⋎u_def = get_spec ⌜Ran⋎u⌝;

val Set⋎uRan⋎u_thm = prove_thm ("Set⋎uRan⋎u_thm", ⌜∀s⦁ Set⋎u (Ran⋎u s)⌝, rewrite_tac [Ran⋎u_def]);

add_rw_thms [Set⋎uRan⋎u_thm] "'gsu-fun";
add_sc_thms [Set⋎uRan⋎u_thm] "'gsu-fun";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];

set_goal([],⌜Ran⋎u ∅⋎u = ∅⋎u⌝);
a (rewrite_tac[get_spec ⌜Ran⋎u⌝, gsu_ext_conv ⌜Ran⋎u ∅⋎u = ∅⋎u⌝]);
val Ran⋎u_∅⋎u_thm = save_pop_thm "Ran⋎u_∅⋎u_thm";

set_goal([], ⌜∀r y⦁ y ∈⋎u Ran⋎u r ⇔ ∃ x⦁ x ↦⋎u y ∈⋎u r⌝);
a (rewrite_tac [get_spec ⌜Ran⋎u⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (LEMMA_T  ⌜(Pair⋎u x y) ∈⋎u Gx⋎u (x ↦⋎u y)⌝ asm_tac
	THEN1 rewrite_tac [↦⋎u_spec_thm]);
a (lemma_tac ⌜Gx⋎u (x ↦⋎u y) ⊆⋎u Gx⋎u r⌝ THEN1 fc_tac [Gx⋎u_mono_thm2]);
a (LEMMA_T ⌜y ∈⋎u Pair⋎u x y⌝ asm_tac THEN1 rewrite_tac []);
a (lemma_tac ⌜y ∈⋎u Gx⋎u (x ↦⋎u y)⌝);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜galaxy⋎u (Gx⋎u (x ↦⋎u y))⌝ THEN1 rewrite_tac[galaxy⋎u_Gx⋎u]);
a (fc_tac [galaxies⋎u_transitive_thm]);
a (fc_tac [Transitive⋎u_def]);
a (ASM_FC_T (MAP_EVERY ante_tac) []
	THEN once_rewrite_tac [⊆⋎u_def]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "2.2" *** *)
a (DROP_NTH_ASM_T 3 (asm_tac o (once_rewrite_rule [get_spec⌜$⊆⋎u⌝])));
a (spec_nth_asm_tac 1 ⌜y⌝);
(* *** Goal "3" *** *)
a (∃_tac ⌜x⌝ THEN strip_tac);
val Ran⋎u_thm = save_pop_thm "Ran⋎u_thm";

set_goal([], ⌜∀g⦁ galaxy⋎u g ⇒ ∀r⦁ r ∈⋎u g ⇒ Ran⋎u r ∈⋎u g⌝);
a (REPEAT strip_tac THEN rewrite_tac [get_spec ⌜Ran⋎u⌝]);
a (lemma_tac ⌜galaxy⋎u (Gx⋎u r)⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜Sep⋎u (Gx⋎u r) (λ w⦁ ∃ v⦁ v ↦⋎u w ∈⋎u r) = Sep⋎u (⋃⋎u (⋃⋎u r)) (λ w⦁ ∃ v⦁ v ↦⋎u w ∈⋎u r)⌝
	THEN1 (rewrite_tac [gsu_ext_conv ⌜Sep⋎u (Gx⋎u r) (λ w⦁ ∃ v⦁ v ↦⋎u w ∈⋎u r) = Sep⋎u (⋃⋎u (⋃⋎u r)) (λ w⦁ ∃ v⦁ v ↦⋎u w ∈⋎u r)⌝] THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (∃_tac ⌜Pair⋎u v e⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜v ↦⋎u e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (lemma_tac ⌜e ∈⋎u⋏+ r⌝ THEN1 (
	ufc_tac [tc∈⋎u_incr_thm]
	THEN REPEAT_N 2 (all_ufc_tac [tc∈⋎u_trans_thm])));
a (asm_tac t_in_Gx⋎u_t_thm);
a (all_ufc_tac [tc∈⋎u_incr_thm]);
a (all_ufc_tac [tc∈⋎u_trans_thm]);
a (all_fc_tac [GClose⋎u_tc∈⋎u_thm]);
(* *** Goal "4" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "5" *** *)
a (asm_rewrite_tac[]);
a (lemma_tac ⌜r ∈⋎u Gx⋎u r⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜⋃⋎u r ∈⋎u Gx⋎u r⌝ THEN1 all_fc_tac[GClose⋎u_fc_clauses]);
a (lemma_tac ⌜(⋃⋎u (⋃⋎u r)) ∈⋎u Gx⋎u r⌝ THEN1 (all_fc_tac[GClose⋎u_fc_clauses]));
a (lemma_tac ⌜⋃⋎u r ∈⋎u g⌝ THEN1 all_fc_tac [GClose⋎u_fc_clauses]);
a (lemma_tac ⌜⋃⋎u (⋃⋎u r) ∈⋎u g⌝ THEN1 all_fc_tac [GClose⋎u_fc_clauses]);
a (lemma_tac ⌜∀ p⦁ Sep⋎u (⋃⋎u (⋃⋎u r)) p ∈⋎u g⌝ THEN1 (all_fc_tac [GClose⋎u_fc_clauses]));
a (asm_rewrite_tac[]);
val GClose⋎u_Ran⋎u_thm = save_pop_thm "GClose⋎u_Ran⋎u_thm";

set_goal([], ⌜∀x y⦁ $∈⋎u⋏+ x (Ran⋎u y) ⇒ $∈⋎u⋏+ x y⌝);
a (REPEAT strip_tac);
a (fc_tac [tc∈⋎u_cases_thm]);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac);
a (rewrite_tac [Ran⋎u_thm] THEN REPEAT strip_tac);
a (lemma_tac ⌜$∈⋎u⋏+ x (x' ↦⋎u x)⌝ THEN1 rewrite_tac [tc∈⋎u_↦⋎u_right_thm]);
a (fc_tac [tc∈⋎u_incr_thm]);
a (all_fc_tac [tc∈⋎u_trans_thm]);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac);
a (rewrite_tac [Ran⋎u_thm] THEN REPEAT strip_tac);
a (lemma_tac ⌜$∈⋎u⋏+ z (x' ↦⋎u z)⌝ THEN1 rewrite_tac [tc∈⋎u_↦⋎u_right_thm]);
a (fc_tac [tc∈⋎u_incr_thm]);
a (all_ufc_tac [tc∈⋎u_trans_thm]);
a (all_ufc_tac [tc∈⋎u_trans_thm]);
val tc∈⋎u_Ran⋎u_thm = save_pop_thm "tc∈⋎u_Ran⋎u_thm";
=TEX
}%ignore

The following function maps a HOL function over the range of a GSU function, returning in effect the composition of the two functions.
Its primary use is likely to be with sequences, for which it can be used to systematically transform all the elements of the sequence, but its definitiom is not specific to sequences so it is included here.

ⓈHOLCONST
│ ⦏RanMap⋎u⦎: ('a GSU → 'a GSU) → 'a GSU → 'a GSU
├───────────
│	∀f s⦁ RanMap⋎u f s = Imagep⋎u (λe⦁ Fst⋎u e ↦⋎u f (Snd⋎u e)) s
■

RanMap does preserves the domain of a relation.

=GFT
⦏Dom⋎u_RanMap⋎u_thm⦎ =	⊢ ∀ f r⦁ Rel⋎u r ⇒ Dom⋎u (RanMap⋎u f r) = Dom⋎u r
=TEX

\ignore{
=SML
val RanMap⋎u_def = get_spec ⌜RanMap⋎u⌝;

set_goal([], ⌜∀f r⦁ Rel⋎u r ⇒ Dom⋎u (RanMap⋎u f r) = Dom⋎u r⌝);
a (REPEAT strip_tac THEN rewrite_tac [RanMap⋎u_def, Dom⋎u_def]);
a (gsu_ext_tac THEN_TRY rewrite_tac[] THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (fc_tac [Rel⋎u_def]);
a (asm_fc_tac []);
a (var_elim_asm_tac ⌜e' = s ↦⋎u t⌝);
a (rewrite_tac[]);
a (lemma_tac ⌜galaxy⋎u (Gx⋎u r)⌝ THEN1 rewrite_tac[galaxy⋎u_Gx⋎u]);
a (lemma_tac ⌜r ∈⋎u Gx⋎u r⌝ THEN1 rewrite_tac[t_in_Gx⋎u_t_thm]);
a (lemma_tac ⌜s ∈⋎u⋏+ s ↦⋎u t⌝ THEN1 rewrite_tac[tc∈⋎u_↦⋎u_right_thm]);
a (lemma_tac ⌜s ↦⋎u t ∈⋎u⋏+ r⌝ THEN1 fc_tac [tc∈⋎u_incr_thm]);
a (lemma_tac ⌜s ∈⋎u⋏+ r⌝ THEN1 all_fc_tac [tc∈⋎u_trans_thm]);
a (lemma_tac ⌜r ∈⋎u⋏+ Gx⋎u r⌝ THEN1 fc_tac [tc∈⋎u_incr_thm]);
a (lemma_tac ⌜s ∈⋎u⋏+ Gx⋎u r⌝ THEN1 all_fc_tac [tc∈⋎u_trans_thm]);
a (all_fc_tac [GClose⋎u_tc∈⋎u_thm]);
(* *** Goal "2" *** *)
a (fc_tac [Rel⋎u_def]);
a (asm_fc_tac []);
a (var_elim_asm_tac ⌜e' = s ↦⋎u t⌝);
a (∃_tac ⌜t⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (lemma_tac ⌜e ↦⋎u f v ∈⋎u (Imagep⋎u (λ e⦁ Fst⋎u e ↦⋎u f (Snd⋎u e)) r)⌝ );
(* *** Goal "3.1" *** *)
a (rewrite_tac [Imagep⋎u_def] THEN REPEAT strip_tac);
a (∃_tac ⌜e ↦⋎u v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3.2" *** *)
a (LEMMA_T ⌜e ∈⋎u⋏+ Imagep⋎u (λ e⦁ Fst⋎u e ↦⋎u f (Snd⋎u e)) r⌝ asm_tac);
(* *** Goal "3.2.1" *** *)
a (LEMMA_T ⌜e ↦⋎u f v ∈⋎u Imagep⋎u (λ e⦁ Fst⋎u e ↦⋎u f (Snd⋎u e)) r⌝ asm_tac);
(* *** Goal "3.2.1.1" *** *)
a (rewrite_tac [Imagep⋎u_def] THEN REPEAT strip_tac);
a (∃_tac ⌜e ↦⋎u v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3.2.1.2" *** *)
a (lemma_tac ⌜e ∈⋎u⋏+ e ↦⋎u f v⌝ THEN1 rewrite_tac[tc∈⋎u_↦⋎u_left_thm]);
a (LEMMA_T ⌜e ↦⋎u f v ∈⋎u⋏+ Imagep⋎u (λ e⦁ Fst⋎u e ↦⋎u f (Snd⋎u e)) r⌝ asm_tac
	THEN1 ALL_FC_T rewrite_tac [tc∈⋎u_incr_thm]);
a (ALL_FC_T rewrite_tac [tc∈⋎u_trans_thm]);
(* *** Goal "3.2.2" *** *)
a (all_fc_tac [Gx⋎u_trans_thm5]);
(* *** Goal "4" *** *)
a (∃_tac ⌜f v⌝ THEN ∃_tac ⌜e ↦⋎u v⌝ THEN_TRY asm_rewrite_tac[]);
val Dom⋎u_RanMap⋎u_thm = save_pop_thm "Dom⋎u_RanMap⋎u_thm";

set_goal([],⌜∃Field⋎u⦁ ∀s e⦁ e ∈⋎u (Field⋎u s) ⇔ e ∈⋎u (Dom⋎u s) ∨ e ∈⋎u (Ran⋎u s)⌝);
a (∃_tac ⌜λx⦁ (Dom⋎u x) ∪⋎u (Ran⋎u x)⌝);
a (prove_tac[]);
save_cs_∃_thm (pop_thm ());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Field⋎u⦎: 'a GSU → 'a GSU
├─────────
│ ∀s⦁ Field⋎u s = (Dom⋎u s) ∪⋎u (Ran⋎u s)
■

=GFT


⦏Field⋎u_∅⋎u_thm⦎ =	⊢ Field⋎u ∅⋎u = ∅⋎u

⦏tc∈⋎u_Field⋎u_thm⦎ =	⊢ ∀ x⦁ x ∈⋎u⋏+ Field⋎u y ⇒ x ∈⋎u⋏+ y
=TEX

\ignore{
=SML
val Field⋎u_def = get_spec ⌜Field⋎u⌝;

val Set⋎uField⋎u_thm = prove_thm("Set⋎uField⋎u_thm", ⌜∀r⦁ Set⋎u(Field⋎u r)⌝, rewrite_tac[Field⋎u_def]);

set_goal([], ⌜∀s e⦁ e ∈⋎u (Field⋎u s) ⇔ e ∈⋎u (Dom⋎u s) ∨ e ∈⋎u (Ran⋎u s)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [Field⋎u_def]);
val Field⋎u_ext_thm = pop_thm ();

add_pc_thms "'gsu-fun" ([
	Field⋎u_ext_thm,
	Rel⋎u_∅⋎u_thm,
	Dom⋎u_∅⋎u_thm,
	Ran⋎u_∅⋎u_thm]);
add_rw_thms [Set⋎uField⋎u_thm] "'gsu-fun";
add_sc_thms [Set⋎uField⋎u_thm] "'gsu-fun";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];

set_goal([],⌜Field⋎u ∅⋎u = ∅⋎u⌝);
a (prove_tac[gsu_ext_conv ⌜Field⋎u ∅⋎u = ∅⋎u⌝]);
val Field⋎u_∅⋎u_thm = save_pop_thm "Field⋎u_∅⋎u_thm";

set_goal([], ⌜∀x y⦁ x ∈⋎u⋏+ Field⋎u y ⇒ x ∈⋎u⋏+ y⌝);
a (REPEAT strip_tac );
a (fc_tac [tc∈⋎u_cases_thm]);
(* *** Goal "1" *** *)
a (fc_tac [tc∈⋎u_incr_thm]);
a (fc_tac [tc∈⋎u_Dom⋎u_thm]);
(* *** Goal "2" *** *)
a (fc_tac [tc∈⋎u_incr_thm]);
a (fc_tac [tc∈⋎u_Ran⋎u_thm]);
(* *** Goal "3" *** *)
a (fc_tac [tc∈⋎u_incr_thm]);
a (fc_tac [tc∈⋎u_Dom⋎u_thm]);
a (all_fc_tac [tc∈⋎u_trans_thm]);
(* *** Goal "4" *** *)
a (fc_tac [tc∈⋎u_incr_thm]);
a (fc_tac [tc∈⋎u_Ran⋎u_thm]);
a (all_fc_tac [tc∈⋎u_trans_thm]);
val tc∈⋎u_Field⋎u_thm = save_pop_thm "tc∈⋎u_Field⋎u_thm";

add_pc_thms "'gsu-fun" ([Field⋎u_∅⋎u_thm]);
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];
=TEX
}%ignore

\subsection{Domain and Range Restrictions}

=SML
declare_infix (300, "◁⋎u");
declare_infix (300, "▷⋎u");
declare_infix (300, "⩤⋎u");
declare_infix (300, "⩥⋎u");
=TEX

ⓈHOLCONST
│ $⦏◁⋎u⦎: 'a GSU → 'a GSU → 'a GSU
├──────
│ ∀s r⦁ s ◁⋎u r = Sep⋎u r (λp⦁ Fst⋎u p ∈⋎u s)
■

ⓈHOLCONST
│ $⦏▷⋎u⦎: 'a GSU → 'a GSU → 'a GSU
├──────
│ ∀s r⦁ r ▷⋎u s = Sep⋎u r (λp⦁ Snd⋎u p ∈⋎u s)
■

ⓈHOLCONST
│ $⦏⩤⋎u⦎: 'a GSU → 'a GSU → 'a GSU
├──────
│ ∀s r⦁ s ⩤⋎u r = Sep⋎u r (λp⦁ ¬ Fst⋎u p ∈⋎u s)
■

ⓈHOLCONST
│ $⦏⩥⋎u⦎: 'a GSU → 'a GSU → 'a GSU
├──────
│ ∀s r⦁ r ⩥⋎u s = Sep⋎u r (λp⦁ ¬ Snd⋎u p ∈⋎u s)
■

=IGN
declare_alias ("◁", ⌜$◁⋎u⌝);
declare_alias ("▷", ⌜$▷⋎u⌝);
declare_alias ("⩤", ⌜$⩤⋎u⌝);
declare_alias ("⩥", ⌜$⩥⋎u⌝);
=TEX

\subsection{Dependent Types}

Any relation may be regarded as a dependent sum type.
When so regarded, each ordered pair in the relation consist with a type-index and a value whose type is that associated with the type.

The indexed set of types, relative to which every pair in the relation is well-typed may be retrieved from the relation as follows.

ⓈHOLCONST
│ ⦏Rel2DepType⋎u⦎ : 'a GSU → 'a GSU
├─────────────
│ ∀r⦁ Rel2DepType⋎u r = Sep⋎u
│		(Gx⋎u r)
│		(λe⦁ ∃i t:'a GSU⦁
│			e = i ↦⋎u t
│			∧ i ∈⋎u Dom⋎u r
│			∧ (∀j⦁ j ∈⋎u t ⇔ i ↦⋎u j ∈⋎u r))
■

=GFT
⦏Set⋎uRel2DepType⋎u_thm⦎ = ⊢ ∀ r⦁ Set⋎u (Rel2DepType⋎u r)
=TEX

\ignore{
=SML
val Rel2DepType⋎u_def =  get_spec ⌜Rel2DepType⋎u⌝;

val Set⋎uRel2DepType⋎u_thm = prove_thm("Set⋎uRel2DepType⋎u_thm", ⌜∀r⦁ Set⋎u(Rel2DepType⋎u r)⌝, rewrite_tac[Rel2DepType⋎u_def]);

add_rw_thms [Set⋎uRel2DepType⋎u_thm] "'gsu-fun";
add_sc_thms [Set⋎uRel2DepType⋎u_thm] "'gsu-fun";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];

=IGN

set_goal([], ⌜∀r e⦁ Rel⋎u r ⇒
	(e ∈⋎u Rel2DepType⋎u r
	⇔ ∃i t:'a GSU⦁ e = i ↦⋎u t
			∧ i ∈⋎u Dom⋎u r
			∧ (∀j⦁ j ∈⋎u t ⇔ i ↦⋎u j ∈⋎u r))⌝);
a (REPEAT_N 3 strip_tac THEN rewrite_tac [get_spec ⌜Rel2DepType⋎u⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜i⌝ THEN ∃_tac ⌜t⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜galaxy⋎u (Gx⋎u r)⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜r ∈⋎u Gx⋎u r⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜Dom⋎u r ∈⋎u (Gx⋎u r)⌝ THEN1 (all_fc_tac [GClose⋎u_Dom⋎u_thm]));
a (lemma_tac ⌜i ∈⋎u (Gx⋎u r)⌝ THEN1 (
	all_fc_tac [tc∈⋎u_incr_thm]
	THEN all_fc_tac [tc∈⋎u_trans_thm]
	THEN all_fc_tac [GClose⋎u_tc∈⋎u_thm]));
a (lemma_tac ⌜t = Sep⋎u (Ran⋎u r) (λj⦁ i ↦⋎u j ∈⋎u r)⌝
	THEN1 (rewrite_tac [gsu_relext_clauses] THEN REPEAT strip_tac));
(* *** Goal "2.1" *** *)
a (rewrite_tac [Ran⋎u_thm]);
a (asm_ufc_tac []);
a (∃_tac ⌜i⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (asm_ufc_tac []);
(* *** Goal "2.3" *** *)
a (SYM_ASMS_T ufc_tac);
(* *** Goal "2.4" *** *)
a (lemma_tac ⌜Ran⋎u r ∈⋎u Gx⋎u r⌝ THEN1 all_fc_tac [GClose⋎u_Ran⋎u_thm]);
a (lemma_tac ⌜Sep⋎u (Ran⋎u r) (λ j⦁ i ↦⋎u j ∈⋎u r) ∈⋎u Gx⋎u r⌝
	THEN1 (ALL_FC_T  rewrite_tac[GClose⋎u_fc_clauses]));

 =========

a (lemma_tac ⌜⌝ THEN1 fc_tac [tc∈⋎u_incr_thm]);


a (∃_tac ⌜i⌝ THEN asm_rewrite_tac[]);

a (∃_tac ⌜⌝ THEN asm_rewrite_tac[]);

a (lemma_tac ⌜∀j⦁ j ∈⋎u t ⇒ j ∈⋎u⋏+ r⌝ THEN1 REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜i ↦⋎u j ∈⋎u r⌝ THEN1 asm_fc_tac[]);
a (lemma_tac ⌜j ∈⋎u⋏+ i ↦⋎u j⌝ THEN1 rewrite_tac[]);
a (all_fc_tac [tc∈⋎u_incr_thm] THEN all_fc_tac [tc∈⋎u_trans_thm]);
(* *** Goal "2.2" *** *)
a (lemma_tac ⌜⌝ THEN1 (asm_rewrite_tac[gsu_relext_clauses]));
a (lemma_tac ⌜∀j⦁ j ∈⋎u t ⇒ j ∈⋎u r⌝
	THEN1 (REPEAT strip_tac
		THEN asm_fc_tac []
		THEN fc_tac [GClose⋎u_tc∈⋎u_thm]));
GClose⋎u_fc_clauses;

a (asm_rewrite_tac[]);
a (fc_tac [GClose⋎u↦⋎u_thm]);

a (lemma_tac ⌜t ∈⋎u Gx⋎u r⌝

a (∃_tac ⌜λr⦁ Sep⋎u
		(Gx⋎u r)
		(λe⦁ ∃i t:'a GSU⦁
			e = i ↦⋎u t
			∧ i ∈⋎u Dom⋎u r
			∧ (∀j⦁ j ∈⋎u t ⇔ i ↦⋎u j ∈⋎u r))⌝
	THEN rewrite_tac[]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜i⌝ THEN ∃_tac ⌜t⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜galaxy⋎u (Gx⋎u r)⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜i ∈⋎u Gx⋎u r ∧ t ∈⋎u Gx⋎u r⌝
a (fc_tac [GClose⋎u↦⋎u_thm]);
a (list_spec_nth_asm_tac 1 [⌜i⌝, ⌜t⌝]);
=TEX
}%ignore

Any similar indexed collection of sets, determines a set of ordered pairs and a set of functions according to the following definitions.

The dependent sums are as follows:

ⓈHOLCONST
│ ⦏DepSum⋎u⦎ : 'a GSU → 'a GSU
├─────────────
│ ∀t⦁ DepSum⋎u t = Sep⋎u
│		(Gx⋎u t)
│		(λe⦁ ∃i t2 v:'a GSU⦁
│			e = i ↦⋎u v
│			∧ v ∈⋎u t2
│			∧ i ↦⋎u t2 ∈⋎u t)
■

=GFT
⦏Set⋎uDepSum⋎u_thm⦎ = ⊢ ∀ t⦁ DepSum⋎u t
         = Sep⋎u
           (Gx⋎u t)
           (λ e⦁ ∃ i t2 v⦁ e = i ↦⋎u v ∧ v ∈⋎u t2 ∧ i ↦⋎u t2 ∈⋎u t)
=TEX

\ignore{
=SML
val DepSum⋎u_def =  get_spec ⌜DepSum⋎u⌝;

val Set⋎uDepSum⋎u_thm = prove_thm("Set⋎uDepSum⋎u_thm", ⌜∀r⦁ Set⋎u(DepSum⋎u r)⌝, rewrite_tac[DepSum⋎u_def]);

add_rw_thms [Set⋎uDepSum⋎u_thm] "'gsu-fun";
add_sc_thms [Set⋎uDepSum⋎u_thm] "'gsu-fun";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];

=IGN

set_goal([], ⌜∀r⦁ Rel⋎u r ⇒ DepSum⋎u (Rel2DepType⋎u r) = r⌝);
a (REPEAT strip_tac THEN rewrite_tac (map get_spec [⌜DepSum⋎u⌝, ⌜Rel2DepType⋎u⌝]));
a (once_rewrite_tac [gsu_relext_clauses] THEN_TRY (rewrite_tac []) THEN REPEAT strip_tac THEN_TRY rewrite_tac[]);
(* *** Goal "1" *** *)
a (all_var_elim_asm_tac);
a (all_asm_fc_tac[]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)

=TEX
}%ignore

\ignore{
 ⓈHOLCONST
│ ⦏DepProd⋎u⦎ : 'a GSU → 'a GSU
├─────────────
│ ∀t⦁ DepProd⋎u t = Sep⋎u
│		(Gx⋎u t)
│		(λf⦁ Dom⋎u f = Dom⋎u t
│			∧ ∀e⦁ e ∈⋎u f ⇒ ∃a v⦁ e = a ↦⋎u v ∈⋎u f ⇒ )
 ■
}%ignore


\subsection{Dependent Sums and Cartesian Products}

=SML
declare_binder "Σ⋎u";
=TEX

ⓈHOLCONST
│ $⦏Σ⋎u⦎ : ('a GSU → 'a GSU) → 'a GSU → 'a GSU
├───────────
│ ∀f s⦁  $Σ⋎u f s = ⋃⋎u (
│	Imagep⋎u	(λe⦁ Imagep⋎u (λx⦁ e ↦⋎u x) (f e))
│		s
│ )
■

=SML
declare_infix(240,"×⋎u");
=TEX

ⓈHOLCONST
│ $⦏×⋎u⦎ : 'a GSU → 'a GSU → 'a GSU
├───────────
│ ∀s t⦁ s ×⋎u t = ⋃⋎u (
│	Imagep⋎u
│	(λse⦁ (Imagep⋎u (λte⦁ se ↦⋎u te) t))
│	s)
■

=GFT
⦏Set⋎u×⋎u_thm⦎ = ⊢ ∀ s t⦁ Set⋎u (s ×⋎u t)
=TEX

\ignore{
=SML
val ×⋎u_def = get_spec ⌜$×⋎u⌝;

val Set⋎u×⋎u_thm = prove_thm ("Set⋎u×⋎u_thm", ⌜∀s t⦁ Set⋎u(s ×⋎u t)⌝, rewrite_tac [×⋎u_def]);

set_goal([],⌜∀s t e⦁ e ∈⋎u s ×⋎u t ⇔
	∃l r⦁l ∈⋎u s ∧ r ∈⋎u t
	∧ e = l ↦⋎u r
⌝);
a (REPEAT ∀_tac THEN rewrite_tac [×⋎u_def]);
a (prove_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜e''⌝
	THEN ∃_tac ⌜Snd⋎u(e)⌝
	THEN asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 3 ante_tac THEN asm_rewrite_tac[]);
a (REPEAT strip_tac THEN_TRY (asm_rewrite_tac[]));
(* *** Goal "2" *** *)
a (∃_tac ⌜Imagep⋎u (λ te⦁ l ↦⋎u te) t⌝);
a (prove_tac[]);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜r⌝ THEN prove_tac[]);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜l⌝ THEN prove_tac[]);
val ×⋎u_spec = save_pop_thm "×⋎u_spec";
=TEX
}%ignore


=GFT
⦏f↦⋎us_thm⦎ =
	⊢ ∀ s t p⦁ p ∈⋎u s ×⋎u t ⇒ Fst⋎u p ↦⋎u Snd⋎u p = p

⦏v∈⋎u×⋎u_thm⦎ =
	⊢ ∀ p s t⦁ p ∈⋎u s ×⋎u t ⇒ Fst⋎u p ∈⋎u s ∧ Snd⋎u p ∈⋎u t

⦏↦⋎u∈⋎u×⋎u_thm⦎ =
	⊢ ∀ l r s t⦁ l ↦⋎u r ∈⋎u s ×⋎u t ⇔ (l ∈⋎u s ∧ r ∈⋎u t)
=TEX

\ignore{
=SML
set_goal ([],⌜∀s t p⦁ p ∈⋎u s ×⋎u t
	⇒ Fst⋎u(p) ↦⋎u Snd⋎u(p) = p⌝);
a (prove_tac[×⋎u_spec]);
a (asm_rewrite_tac[]);
val f↦⋎us_thm = save_pop_thm "f↦⋎us_thm";

set_goal([],⌜∀p s t⦁
	p ∈⋎u (s ×⋎u t)
	⇒ Fst⋎u p ∈⋎u s ∧ Snd⋎u p ∈⋎u t⌝);
a (prove_tac[×⋎u_spec]
      THEN_TRY asm_rewrite_tac[]);
val v∈⋎u×⋎u_thm = save_pop_thm "v∈⋎u×⋎u_thm";

add_pc_thms "'gsu-fun" [];
add_rw_thms [Set⋎u×⋎u_thm] "'gsu-fun";
add_sc_thms [Set⋎u×⋎u_thm] "'gsu-fun";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];


set_goal([],⌜∀l r s t⦁
	(l ↦⋎u r) ∈⋎u (s ×⋎u t)
	⇔ l ∈⋎u s ∧ r ∈⋎u t⌝);
a (prove_tac[×⋎u_spec]);
a (∃_tac ⌜l⌝
	THEN ∃_tac ⌜r⌝
	THEN asm_prove_tac[]);
val ↦⋎u∈⋎u×⋎u_thm = save_pop_thm "↦⋎u∈⋎u×⋎u_thm";

add_pc_thms "'gsu-fun" [↦⋎u∈⋎u×⋎u_thm];
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];
=TEX
}%ignore

=GFT
=TEX

\ignore{
=IGN

set_goal([], ⌜s ×⋎u t ∈⋎u = {z | }⌝);

set_goal([], ⌜∀g⦁ galaxy⋎u g ⇒ (∀s t⦁ s ∈⋎u g ∧ t ∈⋎u g ⇒ s ×⋎u t ∈⋎u g)⌝);
a (REPEAT strip_tac THEN fc_tac [get_spec ⌜galaxy⋎u⌝, GClose⋎uSep⋎u_thm, ]);

=TEX
}%ignore

\subsubsection{Relation Space}

This is the set of all relations over some domain and codomain, i.e. the power set of the cartesian product.

=SML
declare_infix(240,"↔⋎u");
=TEX

ⓈHOLCONST
│ $↔⋎u : 'a GSU → 'a GSU → 'a GSU
├───────────
│ ∀s t⦁ s ↔⋎u t = ℙ⋎u(s ×⋎u t)
■

=GFT
⦏↔⋎u⊆⋎u×⋎u_thm⦎ =	⊢ ∀s t r⦁ r ∈⋎u s ↔⋎u t ⇔ Set⋎u r ∧ r ⊆⋎u (s ×⋎u t)
⦏∅⋎u∈⋎u↔⋎u_thm⦎ =	⊢ ∀s t⦁ ∅⋎u ∈⋎u s ↔⋎u t
=TEX

\ignore{
=SML
set_goal ([], ⌜∀s t r⦁ r ∈⋎u s ↔⋎u t ⇔ Set⋎u r ∧ r ⊆⋎u (s ×⋎u t)⌝);
a (prove_tac[get_spec⌜$↔⋎u⌝, gsu_relext_clauses]);
val ↔⋎u⊆⋎u×⋎u_thm = save_pop_thm "↔⋎u⊆⋎u×⋎u_thm";

set_goal ([], ⌜∀s t⦁ ∅⋎u ∈⋎u s ↔⋎u t⌝);
a (prove_tac[get_spec⌜$↔⋎u⌝,
	gsu_relext_clauses]);
val ∅⋎u∈⋎u↔⋎u_thm = save_pop_thm "∅⋎u∈⋎u↔⋎u_thm";

add_pc_thms "'gsu-fun" [∅⋎u∈⋎u↔⋎u_thm];
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];
=TEX
}%ignore

\subsubsection{Another Pair-Projection Inverse Theorem}

Couched in terms of membership of relation spaces.

=SML
set_goal ([], ⌜∀p r s t⦁
	p ∈⋎u r ∧
	r ∈⋎u s ↔⋎u t ⇒
	Fst⋎u(p) ↦⋎u Snd⋎u(p) = p⌝); 
a (prove_tac[
	get_spec ⌜$↔⋎u⌝,
	⊆⋎u_def]); 
a (REPEAT
	(asm_fc_tac[f↦⋎us_thm])); 
val f↦⋎us_thm1 =
	save_pop_thm "f↦⋎us_thm1"; 
=TEX

\subsubsection{Member of Relation Theorem}

=SML
set_goal ([],⌜∀p r s t⦁
	p ∈⋎u r ∧
	r ∈⋎u s ↔⋎u t ⇒
	Fst⋎u(p) ∈⋎u s ∧
	Snd⋎u(p) ∈⋎u t⌝); 
a (prove_tac[
	get_spec ⌜$↔⋎u⌝,
	⊆⋎u_def]); 
a (asm_fc_tac[]); 
a (fc_tac[v∈⋎u×⋎u_thm]); 
a (asm_fc_tac[]); 
a (fc_tac[v∈⋎u×⋎u_thm]); 
val ∈⋎u↔⋎u_thm =
	save_pop_thm "∈⋎u↔⋎u_thm";
=TEX

\subsubsection{Relational Composition}

=SML
declare_infix (250,"o⋎u");
ⓈHOLCONST
 $o⋎u : 'a GSU → 'a GSU → 'a GSU
├
∀f g⦁ f o⋎u g =
	Imagep⋎u
	(λp⦁ (Fst⋎u(Fst⋎u p) ↦⋎u Snd⋎u(Snd⋎u p)))
	(Sep⋎u (g ×⋎u f) λp⦁ ∃q r s⦁ p = (q ↦⋎u r) ↦⋎u (r ↦⋎u s))
■

=GFT
o⋎u_thm =
   ⊢ ∀f g x⦁ x ∈⋎u f o⋎u g ⇔
	∃q r s⦁ q ↦⋎u r ∈⋎u g ∧ r ↦⋎u s ∈⋎u f
		∧ x = q ↦⋎u s
o⋎u_thm2 =
   ⊢ ∀ f g x y⦁ x ↦⋎u y ∈⋎u f o⋎u g
	⇔ (∃ z⦁ x ↦⋎u z ∈⋎u g ∧ z ↦⋎u y ∈⋎u f)

o⋎u_associative_thm =
   ⊢ ∀f g h⦁ (f o⋎u g) o⋎u h = f o⋎u g o⋎u h

o⋎u_Rel⋎u_thm =
   ⊢ ∀ r s⦁ Rel⋎u r ∧ Rel⋎u s ⇒ Rel⋎u (r o⋎u s)
=TEX

=GFT
⦏Set⋎uo⋎u_thm⦎ = ⊢ ∀ r s⦁ Set⋎u (r o⋎u s)
=TEX

\ignore{
=SML
val o⋎u_def = get_spec ⌜$o⋎u⌝;

val Set⋎uo⋎u_thm = tac_proof(([], ⌜∀r s⦁ Set⋎u (r o⋎u s)⌝), rewrite_tac[o⋎u_def]);

add_rw_thms [Set⋎uo⋎u_thm] "'gsu-fun";
add_sc_thms [Set⋎uo⋎u_thm] "'gsu-fun";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];

set_goal([], ⌜∀f g x⦁ x ∈⋎u f o⋎u g ⇔
	∃q r s⦁ q ↦⋎u r ∈⋎u g
	∧ r ↦⋎u s ∈⋎u f ∧ x = q ↦⋎u s⌝);
a (rewrite_tac (map get_spec [⌜$o⋎u⌝]));
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (MAP_EVERY ∃_tac [⌜q⌝, ⌜r⌝, ⌜s⌝]);
a (DROP_NTH_ASM_T 3 ante_tac
	THEN asm_rewrite_tac []);
(* *** Goal "2" *** *)
a (∃_tac ⌜(q ↦⋎u r) ↦⋎u r ↦⋎u s⌝
	THEN asm_rewrite_tac[]);
a (prove_∃_tac);
val o⋎u_thm = save_pop_thm "o⋎u_thm";
=SML
set_goal([], ⌜∀f g x y⦁ x ↦⋎u y ∈⋎u f o⋎u g ⇔
	∃z⦁ x ↦⋎u z ∈⋎u g
	∧ z ↦⋎u y ∈⋎u f⌝);
a (REPEAT_N 4 strip_tac
	THEN rewrite_tac [o⋎u_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜r⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (MAP_EVERY ∃_tac [⌜x⌝, ⌜z⌝, ⌜y⌝]
	THEN asm_rewrite_tac[]);
val o⋎u_thm2 = save_pop_thm "o⋎u_thm2";

set_goal ([], ⌜∀r s⦁ Rel⋎u r ∧ Rel⋎u s ⇒  Rel⋎u (r o⋎u s)⌝);
a (rewrite_tac [Rel⋎u_def, o⋎u_thm] THEN REPEAT strip_tac);
a (∃_tac ⌜q⌝ THEN ∃_tac ⌜s'⌝ THEN strip_tac);
val o⋎u_Rel⋎u_thm = save_pop_thm "o⋎u_Rel⋎u_thm";

set_goal([], ⌜∀f g h⦁ (f o⋎u g) o⋎u h = f o⋎u (g o⋎u h)⌝);
a (once_rewrite_tac [gsu_ext_conv ⌜(f o⋎u g) o⋎u h = f o⋎u (g o⋎u h)⌝]);
a (rewrite_tac [o⋎u_thm]);
a (REPEAT step_strip_tac);
(* *** Goal "1" *** *)
a (prove_∃_tac THEN all_var_elim_asm_tac);
a (MAP_EVERY ∃_tac [⌜s'⌝, ⌜r'⌝] THEN asm_rewrite_tac[]);
a (∃_tac ⌜q⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜q'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (prove_∃_tac THEN all_var_elim_asm_tac);
a (MAP_EVERY ∃_tac [⌜s⌝, ⌜r'⌝] THEN asm_rewrite_tac[] THEN strip_tac);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜q'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜s'⌝ THEN asm_rewrite_tac[]);
val o⋎u_associative_thm = save_pop_thm "o⋎u_associative_thm"; 

add_pc_thms "'gsu-fun" [o⋎u_thm2];
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];
=TEX
}%ignore

\subsubsection{Relation Subset of Cartesian Product}

=GFT
Rel⋎u_⊆⋎u_cp_thm = 
	⊢ ∀ x⦁ Rel⋎u x ⇔ (∃ s t⦁ x ⊆⋎u s ×⋎u t)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀x⦁ Rel⋎u x ⇔ ∃s t⦁ x ⊆⋎u s ×⋎u t⌝);
a (once_rewrite_tac [gsu_relext_clauses]);
a (rewrite_tac[get_spec⌜Rel⋎u⌝, ×⋎u_spec]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜Dom⋎u x⌝ THEN ∃_tac ⌜Ran⋎u x⌝ THEN REPEAT strip_tac);
a (asm_fc_tac[]);
a (∃_tac ⌜s⌝ THEN ∃_tac ⌜t⌝
	THEN asm_rewrite_tac[Dom⋎u_def, get_spec ⌜Ran⋎u⌝]);
a (lemma_tac ⌜Pair⋎u s t ∈⋎u Gx⋎u e⌝ THEN1 asm_rewrite_tac [↦⋎u_spec_thm]);
a (LEMMA_T ⌜s ∈⋎u Pair⋎u s t⌝ asm_tac THEN1 rewrite_tac[]);
a (LEMMA_T ⌜t ∈⋎u Pair⋎u s t⌝ asm_tac THEN1 rewrite_tac[]);
a (all_fc_tac [Gx⋎u_trans_thm3]);
a (LEMMA_T ⌜Gx⋎u e ⊆⋎u Gx⋎u x⌝ (fn x => fc_tac [rewrite_rule [⊆⋎u_def] x])
	THEN1 fc_tac [Gx⋎u_mono_thm2]
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (DROP_NTH_ASM_T 10 ante_tac THEN asm_rewrite_tac[] THEN strip_tac);
a (∃_tac ⌜t⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (DROP_NTH_ASM_T 10 ante_tac THEN asm_rewrite_tac[] THEN strip_tac);
a (∃_tac ⌜s⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_fc_tac[]);
a (∃_tac ⌜l⌝ THEN ∃_tac ⌜r⌝ THEN asm_rewrite_tac[]);
val Rel⋎u_⊆⋎u_cp_thm = save_pop_thm "Rel⋎u_⊆⋎u_cp_thm";
=TEX
}%ignore

\subsection{Functions}

Definition of partial and total functions and the corresponding function spaces.

\subsubsection{fun}

ⓈHOLCONST
 Fun⋎u : 'a GSU → BOOL
├
∀x⦁ Fun⋎u x ⇔ Rel⋎u x ∧
	∀s t u⦁ s ↦⋎u u ∈⋎u x
		∧ s ↦⋎u t ∈⋎u x
		⇒ u = t
■

\ignore{
=SML
val Fun⋎u_def = get_spec ⌜Fun⋎u⌝;
=TEX
}%ignore

\subsubsection{lemmas}

=GFT
⦏Fun⋎u_∅⋎u_thm⦎ =
	⊢ Fun⋎u ∅⋎u
⦏o⋎u_Fun⋎u_thm⦎ =
	⊢ ∀ f g⦁ Fun⋎u f ∧ Fun⋎u g ⇒ Fun⋎u (f o⋎u g)
⦏Ran⋎u_o⋎u_thm⦎ =
	⊢ ∀ f g⦁ Ran⋎u (f o⋎u g) ⊆⋎u Ran⋎u f
⦏Dom⋎u_o⋎u_thm⦎ =
	⊢ ∀ f g⦁ Dom⋎u (f o⋎u g) ⊆⋎u Dom⋎u g
⦏Dom⋎u_o⋎u_thm2⦎ =
	⊢ ∀ f g⦁ Ran⋎u g ⊆⋎u Dom⋎u f ⇒ Dom⋎u (f o⋎u g) = Dom⋎u g
⦏Fun⋎u_RanMap⋎u_thm⦎ =
	⊢ ∀ f g⦁ Fun⋎u g ⇒ Fun⋎u (RanMap⋎u f g)
=TEX
\ignore{
=SML
val Fun⋎u_∅⋎u_thm = prove_thm (
	"Fun⋎u_∅⋎u_thm", ⌜Fun⋎u ∅⋎u⌝,
	prove_tac[
	 Fun⋎u_def]);

set_goal([], ⌜∀f g⦁ Fun⋎u f ∧ Fun⋎u g ⇒ Fun⋎u (f o⋎u g)⌝);
a (rewrite_tac [Fun⋎u_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [o⋎u_Rel⋎u_thm]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜z = z'⌝ THEN1 all_asm_fc_tac[]);
a (all_var_elim_asm_tac THEN all_asm_fc_tac[]);
val o⋎u_Fun⋎u_thm = save_pop_thm "o⋎u_Fun⋎u_thm";

set_goal ([], ⌜∀f g⦁ Ran⋎u (f o⋎u g) ⊆⋎u Ran⋎u f⌝);
a (once_rewrite_tac [gsu_relext_clauses]);
a (rewrite_tac [Ran⋎u_thm] THEN REPEAT strip_tac);
a (∃_tac ⌜z⌝ THEN strip_tac);
val Ran⋎u_o⋎u_thm = save_pop_thm "Ran⋎u_o⋎u_thm";

set_goal ([], ⌜∀f g⦁ Dom⋎u (f o⋎u g) ⊆⋎u Dom⋎u g⌝);
a (once_rewrite_tac [gsu_relext_clauses]);
a (rewrite_tac [Dom⋎u_thm] THEN REPEAT strip_tac);
a (∃_tac ⌜z⌝ THEN strip_tac);
val Dom⋎u_o⋎u_thm = save_pop_thm "Dom⋎u_o⋎u_thm";

set_goal([], ⌜∀ f g⦁ Ran⋎u g ⊆⋎u Dom⋎u f ⇒ Dom⋎u (f o⋎u g) = Dom⋎u g⌝);
a (once_rewrite_tac [gsu_relext_clauses]
	THEN rewrite_tac [Ran⋎u_thm, Dom⋎u_thm]
	THEN REPEAT strip_tac);
a (gsu_ext_tac THEN rewrite_tac [Dom⋎u_thm]);
a (REPEAT_N 4 strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜x⌝);
(* *** Goal "2.1" *** *)
a (spec_nth_asm_tac 1 ⌜e⌝);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜x'⌝ THEN ∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val Dom⋎u_o⋎u_thm2 = save_pop_thm "Dom⋎u_o⋎u_thm2";

set_goal([], ⌜∀ f g⦁ Fun⋎u g ⇒ Fun⋎u (RanMap⋎u f g)⌝);
a (rewrite_tac [Fun⋎u_def, RanMap⋎u_def, Rel⋎u_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜Fst⋎u e⌝ THEN ∃_tac ⌜f(Snd⋎u e)⌝ THEN strip_tac);
(* *** Goal "2" *** *)
a (all_asm_fc_tac[]);
a (var_elim_nth_asm_tac 1);
a (var_elim_nth_asm_tac 1);
a (lemma_tac ⌜Fst⋎u (s'' ↦⋎u t'') = Fst⋎u (s' ↦⋎u t')⌝
	THEN1 rewrite_tac[eq_sym_rule (asm_rule ⌜s = Fst⋎u (s'' ↦⋎u t'')⌝),
			eq_sym_rule (asm_rule ⌜s = Fst⋎u (s' ↦⋎u t')⌝)]);
a (POP_ASM_T ante_tac);
a (rewrite_tac[] THEN strip_tac);
a (var_elim_asm_tac ⌜s'' = s'⌝);
a (all_asm_fc_tac[]);
a (asm_rewrite_tac[]);
a (var_elim_asm_tac ⌜t'' = t'⌝);
a (var_elim_asm_tac ⌜t' = t'''⌝);
a (asm_rewrite_tac[]);
val Fun⋎u_RanMap⋎u_thm = save_pop_thm "Fun⋎u_RanMap⋎u_thm";
=TEX
}%ignore

\subsubsection{Partial Function Space}

This is the set of all partial functions (i.e. many one mappings) over some domain and codomain.

=SML
declare_infix (240, "⇸⋎u");
ⓈHOLCONST
 $⇸⋎u : 'a GSU → 'a GSU → 'a GSU
├
∀s t⦁ s ⇸⋎u t = Sep⋎u (s ↔⋎u t) Fun⋎u
■
=TEX

\subsubsection{Partial Function Space Non-Empty}

First the theorem that the empty set is a partial function over any domain and codomain.

=GFT
⦏∅⋎u∈⋎u⇸⋎u_thm⦎ = ⊢ ∀s t⦁ ∅⋎u ∈⋎u s ⇸⋎u t
⦏∃⇸⋎u_thm⦎ = ⊢ ∀s t⦁ ∃ f⦁ f ∈⋎u s ⇸⋎u t
=TEX


\ignore{
=SML
set_goal([],
	⌜∀s t⦁ ∅⋎u ∈⋎u s ⇸⋎u t⌝);
a (prove_tac[
	get_spec ⌜$⇸⋎u⌝,
	Fun⋎u_∅⋎u_thm]);
val ∅⋎u∈⋎u⇸⋎u_thm =
	save_pop_thm "∅⋎u∈⋎u⇸⋎u_thm";
=TEX

And then that every partial function space is non-empty.

=SML
set_goal([],
	⌜∀s t⦁ ∃ f⦁ f ∈⋎u s ⇸⋎u t⌝);
a (REPEAT strip_tac
	THEN ∃_tac ⌜∅⋎u⌝
	THEN
	rewrite_tac [∅⋎u∈⋎u⇸⋎u_thm]);
val ∃⇸⋎u_thm =
	save_pop_thm "∃⇸⋎u_thm";
=TEX
}%ignore

\subsubsection{Function Space}

This is the set of all total functions over some domain and codomain.

=SML
declare_infix (240, "→⋎u");
ⓈHOLCONST
│ $→⋎u : 'a GSU → 'a GSU → 'a GSU
├
│ ∀s t⦁ s →⋎u t = Sep⋎u (s ⇸⋎u t)
│	λr⦁ s ⊆⋎u (Dom⋎u r)
■

\subsubsection{Function Space Non-Empty}

First, for the special case of function spaces with empty domain we prove the theorem that the empty set is a member:
Then that whenever the codomain is non-empty the function space is non-empty.

=GFT
⦏∅⋎u∈⋎u∅⋎u→⋎u_thm⦎ =
   ⊢ ∀s t⦁ ∅⋎u ∈⋎u ∅⋎u →⋎u t

⦏∃→⋎u_thm⦎ =
   ⊢ ∀ s t⦁ (∃ x⦁ x ∈⋎u t) ⇒ (∃ f⦁ f ∈⋎u s →⋎u t)
=TEX

\ignore{
=SML
set_goal([],⌜∀s t⦁ ∅⋎u ∈⋎u ∅⋎u →⋎u t⌝);
a (prove_tac[get_spec ⌜$→⋎u⌝,
	Fun⋎u_∅⋎u_thm,
	∅⋎u∈⋎u⇸⋎u_thm]);
val ∅⋎u∈⋎u∅⋎u→⋎u_thm =
	save_pop_thm "∅⋎u∈⋎u∅⋎u→⋎u_thm";

set_goal([], ⌜∀t⦁ (∃x⦁ x ∈⋎u t) ⇒ ∀s⦁ ∃f⦁ f ∈⋎u s →⋎u t⌝);
a (REPEAT strip_tac THEN ∃_tac ⌜s ×⋎u (Unit⋎u x)⌝);
a (rewrite_tac [get_spec ⌜$→⋎u⌝,
	get_spec ⌜$⇸⋎u⌝,
	get_spec ⌜$↔⋎u⌝]);
a (once_rewrite_tac
	[gsu_relext_clauses]);
a (rewrite_tac[
	Dom⋎u_def,
	Fun⋎u_def,
	Rel⋎u_def,
	×⋎u_spec, Dom⋎u_thm]
	THEN REPEAT strip_tac
	THEN TRY (asm_rewrite_tac[])
	THEN TRY prove_∃_tac);
a (∃_tac ⌜x⌝ THEN REPEAT strip_tac
	THEN ∃_tac ⌜l⌝
	THEN asm_rewrite_tac[]);
val ∃→⋎u_thm = save_pop_thm "∃→⋎u_thm";
=TEX
}%ignore

ⓈHOLCONST
│ →⋎u_closed : 'a GSU → BOOL
├────────────
│ ∀s⦁ →⋎u_closed s ⇔ ∀d c⦁ d ∈⋎u s ∧ c ∈⋎u s ⇒ d →⋎u c ∈⋎u s
■

\subsection{Functional Abstraction}

Functional abstraction is defined as a new variable binding construct yeilding a functional set.

\subsubsection{Abstraction}

Because of the closeness to lambda abstraction $λ⋎u$ is used as the name of a new binder for set theoretic functional abstraction.

=SML
declare_binder "λ⋎u";
=TEX

To define a functional set we need a HOL function over sets together with a set which is to be the domain of the function.
Specification of the range is not needed.
The binding therefore yields a function which maps sets to sets (maps the domain to the function).

The following definition is a placeholder, a more abstract definition might eventually be Substituted.
The function is defined as that Subset of the cartesian product of the set s and its image under the function f which coincides with the graph of f over s.

ⓈHOLCONST
│ $λ⋎u: ('a GSU → 'a GSU) → 'a GSU → 'a GSU
├─────────
│ ∀f s⦁ $λ⋎u f s = Sep⋎u (s ×⋎u (Imagep⋎u f s)) (λp⦁ Snd⋎u p = f (Fst⋎u p))
■

\subsection{Application and Extensionality}

In this section we define function application and show that functions are extensional.

\subsubsection{Application}

Application by juxtaposition cannot be overloaded and is used for application of HOL functions.
Application of functional sets is therefore defined as an infix operator whose name is the empty name Subscripted by ``u''.

=SML
declare_infix (250,"⋎u");
=TEX

The particular form shown here is innovative in the value specified for applications of functions to values outside their domain.
The merit of the particular value chosen is that it makes true an extensionality theorem which quantifies over all sets as arguments to the function, which might not otherwise be the case.
Whether this form is useful I don't know.
Generally a result with fewer conditionals is harder to prove but easier to use, but in this case I'm not so sure of the benefit.

It may be noted that it may also be used to apply a non-functional relation, if what you want it some arbitrary value (selected by the choice function) to which some object relates.

ⓈHOLCONST
│ $⋎u : 'a GSU → 'a GSU → 'a GSU
├───────
│ ∀f x⦁ f ⋎u x =
│	if ∃y⦁ x ↦⋎u y ∈⋎u f
│	then εy⦁ x ↦⋎u y ∈⋎u f
│	else f
■

=GFT
app_thm1 = 
	⊢ ∀f x⦁ (∃⋎1y⦁ x ↦⋎u y ∈⋎u f)
	  ⇒ x ↦⋎u (f ⋎u x) ∈⋎u f

app_thm2 = 
	⊢ ∀f x y⦁ Fun⋎u f ∧ (x ↦⋎u y ∈⋎u f)
	  ⇒ f ⋎u x = y

app_thm3 = 
	⊢ ∀f x⦁ Fun⋎u f ∧ x ∈⋎u Dom⋎u f
	  ⇒ x ↦⋎u f ⋎u x ∈⋎u f

o⋎u_⋎u_thm = 
	⊢ ∀f g x⦁ Fun⋎u f ∧ Fun⋎u g ∧ x ∈⋎u Dom⋎u g ∧ Ran⋎u g ⊆⋎u Dom⋎u f
	  ⇒ (f o⋎u g) ⋎u x = f ⋎u g ⋎u x
=TEX
\ignore{
=SML
val lambda⋎u_def = get_spec ⌜$λ⋎u⌝;

set_goal([],⌜∀f x⦁ (∃⋎1y⦁ x ↦⋎u y ∈⋎u f)
	⇒ x ↦⋎u (f ⋎u x) ∈⋎u f⌝);
a (prove_tac[get_spec⌜$⋎u⌝]);
a (LEMMA_T ⌜∃ y⦁ x ↦⋎u y ∈⋎u f⌝
	(fn x=> rewrite_tac[x])
	THEN1 (
		∃_tac ⌜y⌝
		THEN prove_tac[]));
a (all_ε_tac);
a (∃_tac ⌜y⌝ THEN prove_tac[]);
val app_thm1 = save_pop_thm "app_thm1";
=TEX

Note that the result is not conditional on f being a function.

The next theorem applies to functions only and obtains the necessary uniqueness of image from that assumption.

=SML
set_goal([],⌜
∀f x y⦁ Fun⋎u f ∧ (x ↦⋎u y ∈⋎u f)
	⇒ f ⋎u x = y
⌝);
a (prove_tac[get_spec⌜$⋎u⌝,
	Fun⋎u_def]);
a (LEMMA_T
	⌜∃ y⦁ x ↦⋎u y ∈⋎u f⌝
	(fn x=> rewrite_tac[x])
	THEN1 (
		∃_tac ⌜y⌝
		THEN prove_tac[]));
a (all_ε_tac);
a (∃_tac ⌜y⌝
	THEN prove_tac[]);
a (REPEAT (asm_fc_tac[]));
val app_thm2 = save_pop_thm "app_thm2";

set_goal([], ⌜∀f x⦁ Fun⋎u f ∧ x ∈⋎u Dom⋎u f ⇒ x ↦⋎u f ⋎u x ∈⋎u f⌝);
a (rewrite_tac [Fun⋎u_def, get_spec ⌜$⋎u⌝]
	THEN REPEAT strip_tac);
a (POP_ASM_T (strip_asm_tac o (rewrite_rule [Dom⋎u_thm])));
a (LEMMA_T ⌜∃y⦁ x ↦⋎u y ∈⋎u f⌝ rewrite_thm_tac
	THEN1 (∃_tac ⌜x'⌝ THEN asm_rewrite_tac[Dom⋎u_thm]));
a (ε_tac ⌜ε y⦁ x ↦⋎u y ∈⋎u f⌝);
a (∃_tac ⌜x'⌝ THEN strip_tac);
val app_thm3 = save_pop_thm "app_thm3";

set_goal([], ⌜∀f g x⦁ Fun⋎u f ∧ Fun⋎u g ∧ x ∈⋎u Dom⋎u g ∧ Ran⋎u g ⊆⋎u Dom⋎u f
	⇒ (f o⋎u g) ⋎u x = f ⋎u g ⋎u x⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜Fun⋎u (f o⋎u g)⌝ THEN1 all_fc_tac [o⋎u_Fun⋎u_thm]);
a (LEMMA_T ⌜x ∈⋎u Dom⋎u (f o⋎u g)⌝ asm_tac
	THEN1 all_fc_tac [once_rewrite_rule [gsu_relext_clauses] Dom⋎u_o⋎u_thm]);
(* *** Goal "1" *** *)
a (all_fc_tac [Dom⋎u_o⋎u_thm2]
	THEN pure_asm_rewrite_tac[]
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (PC_T "hol" (strip_asm_tac (list_∀_elim [⌜f o⋎u g⌝, ⌜x⌝] app_thm3)));
a (GET_NTH_ASM_T 1 strip_asm_tac);
a (LEMMA_T ⌜g ⋎u x = z⌝ rewrite_thm_tac THEN1 all_fc_tac [app_thm2]); 
a (LEMMA_T ⌜f ⋎u z = (f o⋎u g) ⋎u x⌝ rewrite_thm_tac THEN1 all_fc_tac [app_thm2]); 
val o⋎u_⋎u_thm = save_pop_thm "o⋎u_⋎u_thm"; 
=TEX
}%ignore

=GFT
app_in_Ran_thm = ⊢ ∀ x i⦁ Fun⋎u i ∧ x ∈⋎u Dom⋎u i ⇒ i ⋎u x ∈⋎u Ran⋎u i
=TEX

\ignore{
=SML
set_goal([], ⌜∀x i⦁ Fun⋎u i ∧ x ∈⋎u Dom⋎u i ⇒ i ⋎u x ∈⋎u Ran⋎u i⌝);
a (REPEAT strip_tac);
a (all_fc_tac [app_thm3]);
a (rewrite_tac[Ran⋎u_thm]);
a (∃_tac ⌜x⌝ THEN strip_tac);
val app_in_Ran_thm = save_pop_thm "app_in_Ran_thm";
=TEX
}%ignore

\subsubsection{The ``Type'' of an Application (1)}

The following theorem states that the result of applying a partial function to a value in its domain is a value in its codomain.

=SML
set_goal([],
	⌜∀f s t u⦁ f ∈⋎u s ⇸⋎u t ∧
	u ∈⋎u Dom⋎u f ⇒
	f ⋎u u ∈⋎u t⌝); 
a (prove_tac[
	get_spec ⌜$⇸⋎u⌝,
	Dom⋎u_def]);
a (all_fc_tac [app_thm2] THEN asm_rewrite_tac[]);
a (all_fc_tac [f↦⋎us_thm1]);
a (all_fc_tac [∈⋎u↔⋎u_thm]); 
a (POP_ASM_T ante_tac THEN asm_rewrite_tac []);
val ⋎u∈⋎u_thm = save_pop_thm "⋎u∈⋎u_thm";
=TEX

\subsubsection{The ``Type'' of an Application (2)}

The following theorem states that the result of applying a total function to a value in its domain is a value in its codomain.

=GFT
=TEX

\ignore{
=SML
set_goal([],
	⌜∀f s t u⦁ f ∈⋎u s →⋎u t ∧
	u ∈⋎u s ⇒
	f ⋎u u ∈⋎u t⌝); 
a (prove_tac[
	get_spec ⌜$→⋎u⌝, gsu_relext_clauses]);
a (bc_thm_tac ⋎u∈⋎u_thm
	THEN asm_fc_tac[]);
a (∃_tac ⌜s⌝
	THEN asm_rewrite_tac[]); 
val ⋎u∈⋎u_thm1 = save_pop_thm "⋎u∈⋎u_thm1";
=TEX
}%ignore

\subsubsection{Partial functions are total}

Every partial function is total over its domain.
(there is an ambiguity in the use of the term "domain" for a partial function.
It might mean the left hand operand of some partial function space construction within which the partial function concerned may be found, or it might mean the set of values over which the function is defined.
Here we are saying that if f is a partial function over A, then its domain is some Subset of A and f is a total function over that Subset of A.)

=GFT
∈⋎u⇸⋎u⇒∈⋎u→⋎u_thm =
	⊢ ∀f s t u⦁ f ∈⋎u s ⇸⋎u t ⇒ f ∈⋎u Dom⋎u f →⋎u t
=TEX

\ignore{
=SML
set_goal([],⌜∀f s t u⦁ f ∈⋎u s ⇸⋎u t ⇒ f ∈⋎u Dom⋎u f →⋎u t⌝); 
a (rewrite_tac[
	get_spec ⌜$→⋎u⌝,
	get_spec ⌜$↔⋎u⌝,
	Dom⋎u_def,
	get_spec ⌜$⇸⋎u⌝]);
a (once_rewrite_tac[gsu_relext_clauses]); 
a (REPEAT strip_tac); 
a (rewrite_tac[×⋎u_spec]); 
a (asm_fc_tac[]); 
a (all_fc_tac[
	f↦⋎us_thm,
	v∈⋎u×⋎u_thm]); 
a (∃_tac ⌜Fst⋎u e⌝
	THEN ∃_tac ⌜Snd⋎u e⌝
	THEN asm_rewrite_tac[]
	THEN strip_tac); 
(* *** Goal "1" *** *)
a (LEMMA_T ⌜Pair⋎u (Fst⋎u e) (Snd⋎u e) ∈⋎u Gx⋎u (Fst⋎u e ↦⋎u Snd⋎u e)⌝ ante_tac
	THEN1 rewrite_tac [↦⋎u_spec_thm]);
a (pure_rewrite_tac[asm_rule ⌜Fst⋎u e ↦⋎u Snd⋎u e = e⌝]
	THEN strip_tac);
a (LEMMA_T ⌜Gx⋎u e ⊆⋎u Gx⋎u f⌝ ante_tac THEN1 fc_tac [Gx⋎u_mono_thm2]);
a (rewrite_tac [gsu_relext_clauses] THEN strip_tac THEN asm_fc_tac[]);
a (LEMMA_T ⌜Fst⋎u e ∈⋎u Pair⋎u (Fst⋎u e) (Snd⋎u e)⌝ asm_tac THEN1 rewrite_tac[]);
a (all_fc_tac [Gx⋎u_trans_thm3]);
(* *** Goal "2" *** *)
a (∃_tac ⌜Snd⋎u e⌝	THEN asm_rewrite_tac[]); 
val ∈⋎u⇸⋎u⇒∈⋎u→⋎u_thm = save_pop_thm "∈⋎u⇸⋎u⇒∈⋎u→⋎u_thm";


=TEX
}%ignore

\subsection{The Identity Function}

ⓈHOLCONST
│ Id⋎u : 'a GSU → 'a GSU
├────────
│ ∀s⦁ Id⋎u s = Sep⋎u
│	(s ×⋎u s)
│	λx⦁ Fst⋎u x = Snd⋎u x
■

=GFT
⦏Id⋎u_thm1⦎ =
	⊢ ∀s x⦁ x ∈⋎u Id⋎u s ⇔ ∃y⦁ y ∈⋎u s ∧ x = y ↦⋎u y

⦏Id⋎u_ap_thm⦎ =
	⊢ ∀s x⦁ x ∈⋎u s	⇒ (Id⋎u s) ⋎u x = x

⦏Id⋎u∈⋎u⇸⋎u_thm1⦎ =
	⊢ ∀s t u⦁ s ⊆⋎u t ∩⋎u u ⇒ Id⋎u s ∈⋎u t ⇸⋎u u

⦏Id⋎u∈⋎u⇸⋎u_thm2⦎ =
	⊢ ∀s t u⦁ s ⊆⋎u t ⇒ Id⋎u s ∈⋎u t ⇸⋎u t

⦏tc_Id⋎u_thm⦎ = ⊢ ∀ s t⦁ s ∈⋎u t ⇒ s ∈⋎u⋏+ Id⋎u t

⦏Id⋎u_clauses⦎ =
	⊢ ∀s⦁ Rel⋎u(Id⋎u s) ∧ Fun⋎u (Id⋎u s) ∧ Dom⋎u(Id⋎u s) = s ∧ Ran⋎u(Id⋎u s) = s
=TEX

\ignore{
=SML
val Id⋎u_def = get_spec ⌜Id⋎u⌝;

set_goal([],⌜∀s x⦁
	x ∈⋎u Id⋎u s	
	⇔ ∃y⦁ y ∈⋎u s
	∧ x = y ↦⋎u y⌝);
a (prove_tac[get_spec ⌜Id⋎u⌝]
	THEN_TRY (asm_rewrite_tac[
	get_spec⌜$↔⋎u⌝,
	×⋎u_spec]));
(* *** Goal "1" *** *)
a (fc_tac[×⋎u_spec]);
a (asm_ante_tac ⌜Fst⋎u x = Snd⋎u x⌝
	THEN asm_rewrite_tac[]
	THEN strip_tac
	THEN all_var_elim_asm_tac);
a (∃_tac ⌜r⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (REPEAT (∃_tac ⌜y⌝) THEN asm_rewrite_tac[]);
val Id⋎u_thm1 =
	save_pop_thm "Id⋎u_thm1";

set_goal([],⌜∀s x⦁
	x ∈⋎u s	
	⇒ (Id⋎u s) ⋎u x = x⌝);
a (rewrite_tac[get_spec ⌜$⋎u⌝, Id⋎u_thm1]);
a (REPEAT strip_tac);
a (LEMMA_T ⌜∃ y y'⦁ y' ∈⋎u s ∧ x = y' ∧ y = y'⌝
	(fn x=> rewrite_tac[x] THEN asm_tac x)
	THEN1 (REPEAT_N 2 (∃_tac ⌜x⌝)
		THEN asm_rewrite_tac[]));
a (all_ε_tac
	THEN asm_rewrite_tac[]);
val Id⋎u_ap_thm = save_pop_thm "Id⋎u_ap_thm"; 

set_goal([],⌜∀s t u⦁ s ⊆⋎u t ∩⋎u u ⇒ Id⋎u s ∈⋎u t ⇸⋎u u⌝);
a (rewrite_tac[gsu_relext_clauses]);
a (prove_tac[get_spec ⌜$⇸⋎u⌝,
	get_spec ⌜Id⋎u⌝,
	get_spec ⌜$↔⋎u⌝,
	×⋎u_spec]);
(* *** Goal "1" *** *)
a (once_rewrite_tac[gsu_relext_clauses]);
a (prove_tac[×⋎u_spec]);
a (MAP_EVERY ∃_tac [⌜l⌝, ⌜r⌝] THEN REPEAT strip_tac
	THEN (REPEAT (asm_fc_tac[])));
(* *** Goal "2" *** *)
a (prove_tac[Fun⋎u_def,
	Rel⋎u_def,
	×⋎u_spec]);
val Id⋎u∈⋎u⇸⋎u_thm1 = save_pop_thm "Id⋎u∈⋎u⇸⋎u_thm1";

set_goal([],⌜∀s t u⦁ s ⊆⋎u t ⇒ Id⋎u s ∈⋎u t ⇸⋎u t⌝);
a (prove_tac[]);
a (bc_thm_tac Id⋎u∈⋎u⇸⋎u_thm1);
a (POP_ASM_T ante_tac
	THEN rewrite_tac[gsu_relext_clauses]
	THEN REPEAT strip_tac);
val Id⋎u∈⋎u⇸⋎u_thm2 = save_pop_thm "Id⋎u∈⋎u⇸⋎u_thm2";

set_goal ([], ⌜∀s⦁ Rel⋎u (Id⋎u s)⌝);
a (rewrite_tac [Rel⋎u_def, get_spec ⌜Id⋎u⌝]
	THEN REPEAT strip_tac);
a (fc_tac [×⋎u_spec]);
a (∃_tac ⌜l⌝ THEN ∃_tac ⌜r⌝
	THEN asm_rewrite_tac[]);
val Rel⋎u_Id⋎u_lem = pop_thm();

set_goal ([], ⌜∀s t⦁ s ∈⋎u t ⇒ s ∈⋎u⋏+ (Id⋎u t)⌝);
a (REPEAT strip_tac THEN (once_rewrite_tac [tc∈⋎u_cases_thm])
	THEN REPEAT strip_tac);
a (∃_tac ⌜s ↦⋎u s⌝ THEN asm_rewrite_tac[Id⋎u_thm1]);
a (∃_tac ⌜s⌝ THEN asm_rewrite_tac[Id⋎u_thm1]);
val tc_Id⋎u_thm = pop_thm();

set_goal([], ⌜∀s⦁ Rel⋎u(Id⋎u s) ∧ Fun⋎u (Id⋎u s) ∧ Dom⋎u(Id⋎u s) =⋎u s ∧ Ran⋎u(Id⋎u s) =⋎u s⌝);
a (rewrite_tac [Rel⋎u_Id⋎u_lem] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [Fun⋎u_def, Rel⋎u_Id⋎u_lem, get_spec ⌜Id⋎u⌝]
	THEN REPEAT strip_tac
	THEN all_var_elim_asm_tac
	THEN strip_tac);
(* *** Goal "2" *** *)
a (rewrite_tac [gsu_relext_clauses, Dom⋎u_thm, Id⋎u_thm1] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (all_var_elim_asm_tac);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜u⌝ THEN ∃_tac ⌜u⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (rewrite_tac[get_spec ⌜Ran⋎u⌝]);
a (rewrite_tac [gsu_relext_clauses, Ran⋎u_thm, Id⋎u_thm1] THEN REPEAT strip_tac);
(* *** Goal "3.1" *** *)
a (all_var_elim_asm_tac);
(* *** Goal "3.2" *** *)
a (fc_tac [tc_Id⋎u_thm]);
a (lemma_tac ⌜(Id⋎u s) ∈⋎u Gx⋎u (Id⋎u s)⌝ THEN1 rewrite_tac [t_in_Gx⋎u_t_thm]);
a (fc_tac [list_∀_elim [⌜u⌝, ⌜Id⋎u s⌝, ⌜Id⋎u s⌝] Gx⋎u_trans_thm4]);
(* *** Goal "3.3" *** *)
a (∃_tac ⌜u⌝ THEN ∃_tac ⌜u⌝ THEN asm_rewrite_tac[]);
val Id⋎u_clauses = save_pop_thm "Id⋎u_clauses";

add_pc_thms "'gsu-fun" ([Id⋎u_clauses]);
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];
=TEX
}%ignore

\subsection{Override}

Override is an operator over sets which is intended primarily for use with functions.
It may be used to change the value of the function over any part of its domain by overriding it with a function which is defined only for those values.

=SML
declare_infix (250,"⊕⋎u");
=TEX

ⓈHOLCONST
│ $⦏⊕⋎u⦎ : 'a GSU → 'a GSU → 'a GSU
├─────────────
│ ∀s t⦁ s ⊕⋎u t = Sep⋎u (s ∪⋎u t)
│	λx⦁ if Fst⋎u x ∈⋎u Dom⋎u t then x ∈⋎u t else x ∈⋎u s 
■

=GFT
⦏∈⋎u⊕⋎u_thm⦎ =
   ⊢ ∀ s t x⦁ x ∈⋎u s ⊕⋎u t = (if Fst⋎u x ∈⋎u Dom⋎u t then x ∈⋎u t else x ∈⋎u s)

⦏↦⋎u∈⋎u⊕⋎u_thm⦎ =
   ⊢ ∀ s t x y
     ⦁ x ↦⋎u y ∈⋎u s ⊕⋎u t = (x ↦⋎u y ∈⋎u t ∨ ¬ x ∈⋎u Dom⋎u t ∧ x ↦⋎u y ∈⋎u s)

⦏⊕⋎u_Rel⋎u_thm⦎ =
   ⊢ ∀ s t⦁ Rel⋎u s ∧ Rel⋎u t ⇒ Rel⋎u (s ⊕⋎u t)

⦏⊕⋎u_Fun⋎u_thm⦎ =
   ⊢ ∀ s t⦁ Fun⋎u s ∧ Fun⋎u t ⇒ Fun⋎u (s ⊕⋎u t)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀s t x⦁ x ∈⋎u (s ⊕⋎u t) ⇔
	   if Fst⋎u x ∈⋎u Dom⋎u t then x ∈⋎u t else x ∈⋎u s⌝);
a (rewrite_tac [get_spec ⌜$⊕⋎u⌝]
	THEN REPEAT strip_tac);
val ∈⋎u⊕⋎u_thm = save_pop_thm "∈⋎u⊕⋎u_thm";

set_goal ([], ⌜∀s t x y⦁ x ↦⋎u y ∈⋎u (s ⊕⋎u t) ⇔
	   x ↦⋎u y ∈⋎u t
	∨ ¬ (x ∈⋎u Dom⋎u t)
	   ∧ x ↦⋎u y ∈⋎u s
⌝);
a (rewrite_tac [get_spec ⌜$⊕⋎u⌝] THEN REPEAT strip_tac);
a (POP_ASM_T ante_tac THEN rewrite_tac [Dom⋎u_thm]
	THEN REPEAT strip_tac);
a (asm_fc_tac[]);
val ↦⋎u∈⋎u⊕⋎u_thm = save_pop_thm "↦⋎u∈⋎u⊕⋎u_thm";

set_goal([], ⌜∀s t⦁ Rel⋎u s ∧ Rel⋎u t ⇒ Rel⋎u (s ⊕⋎u t)⌝);
a (rewrite_tac [Rel⋎u_def, ∈⋎u⊕⋎u_thm]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]
	THEN ∃_tac ⌜s'⌝ THEN ∃_tac ⌜t'⌝ THEN strip_tac);
val ⊕⋎u_Rel⋎u_thm = save_pop_thm "⊕⋎u_Rel⋎u_thm";

set_goal([], ⌜∀s t⦁ Fun⋎u s ∧ Fun⋎u t ⇒ Fun⋎u (s ⊕⋎u t)⌝);
a (rewrite_tac [Fun⋎u_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac[⊕⋎u_Rel⋎u_thm]);
(* *** Goal "2" *** *)
a (REPEAT_N 2 (POP_ASM_T ante_tac)
	THEN rewrite_tac [↦⋎u∈⋎u⊕⋎u_thm, Dom⋎u_thm]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
val ⊕⋎u_Fun⋎u_thm = save_pop_thm "⊕⋎u_Fun⋎u_thm";
=TEX
}%ignore

\subsection{Proof Contexts}

Finalisation of a proof context.

\subsubsection{Proof Context}

=SML
add_pc_thms "'gsu-fun" ([
	Field⋎u_∅⋎u_thm,
	∅⋎u∈⋎u⇸⋎u_thm]);
add_rw_thms [Fun⋎u_∅⋎u_thm] "'gsu-fun";
add_sc_thms [Fun⋎u_∅⋎u_thm] "'gsu-fun";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun"];
commit_pc "'gsu-fun";
=TEX

\section{Ordinals}

A new ``gsu-ord'' theory is created as a child of ``gsu-ax''.
The theory will contain the definitions of ordinals and related material for general use.
I began by roughly following "Set Theory" by Frank Drake, chapter 2 section 2, but later development was undertaken without access to that book and was driven by applications.

\subsubsection{Motivation}

When I first started this theory of Ordinals I was motivated by interest and self-education, though the set theory in the context of which the development was undertaken had been initiated for my foundational research.
The educational interest didn't get me very far, and this theory languished scarcely begun for many years.
The set theory continued to be used for my foundational research, which also has progressed very slowly and did not begin to make demands on the theory of ordingals until late in 2012.
Even then, the things I need are very modest, to know for example, that ordinal addition is associative.

Some of the material required is not specific to set theory and is quite widely applicable (in which case I actually develop it elsewhere and then just use it here).
Well-foundedness and induction over well-founded relations is the obvious case relevant to this part of Drake.
The recursion theorem is the important more general result which appears in the next section in Drake.
``more general'' means ``can be developed as a polymorphic theory in HOL and applied outside the context of set theory''.
In fact these things have to be developed in the more general context to be used in the ways they are required in the development of set theory, since, for example, one wants to do definitions by recursion over the set membership relation where neither the function defined nor the relevant well-founded relation are actually sets.

\subsubsection{Divergence}

I never did follow Drake slavishly, and I no longer have a copy of his book, but now refer to Jech as necessary.
However, the level remains elementary, so this is rarely necessary.

Sometimes the context in which I am doing the work makes some divergence desirable or necessary.
For example, I am doing the work in the context of a slightly eccentric set theory (``Galactic Set Theory'') which mainly makes no difference, but has a non-standard formulation of the axiom of foundation.
Mainly this is covered by deriving the standard formulation and its consequences and using them where this is used by Drake (in proving the trichotomy theorem).
However, the machinery for dealing with well-foundedness makes a difference to how induction principles are best formulated and derived.

Sometimes I looked at what he had done and I think, ``no way am I going to do that''.
Not necessarily big things, for example, I couldn't use his definition of successor ordinal which he pretty much admits himself is what I would call a kludge.
If I started again I would not use his definition of ordinal either, I would use an inductive definition (nicer in a higher order theory).

\subsubsection{The Theory ord}

The new theory is first created, together with a proof context which we will build up as we develop the theory.

=SML
open_theory "gsu-ax";
force_new_theory "gsu-ord";
(* new_parent "wf_recp"; *)
force_new_pc "'gsu-ord";
merge_pcs ["'savedthm_cs_∃_proof"] "'gsu-ord";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-ord"];
=TEX

\subsection{Definition of Ordinal}

An ordinal is defined as a transitive and connected set.
The usual ordering over the ordinals is defined and also the successor function.

\subsubsection{The Definition}

The concept of transitive set has already been defined in theory {\it gsu-ax}.
The concepts {\it connected} and {\it ordinal} are now defined.

The possible presence of urelements causes complications here, we have to ensure that ordinals are hereditarily sets.
For this is does not suffice to require that every ordinal is a set, for we do not assert but must prove from the definition that all members of an ordinal are ordinals.

It does suffice to insist that an ordinal is a set and that all its members are sets, so we define that property here.

ⓈHOLCONST
 ⦏SetOfSets⋎u⦎ : 'a GSU → BOOL
├
  ∀s :'a GSU⦁ SetOfSets⋎u s ⇔ Set⋎u s ∧ ∀t:'a GSU⦁ t ∈⋎u s ⇒ Set⋎u t
■

ⓈHOLCONST
 ⦏Connected⋎u⦎ : 'a GSU → BOOL
├
  ∀s :'a GSU⦁ Connected⋎u s ⇔
	∀t u :'a GSU⦁ t ∈⋎u s ∧ u ∈⋎u s ⇒ t ∈⋎u u ∨ t = u ∨ u ∈⋎u t
■

ⓈHOLCONST
 ⦏Ordinal⋎u⦎ : 'a GSU → BOOL
├
  ∀s :'a GSU⦁ Ordinal⋎u s ⇔ SetOfSets⋎u s ∧ Transitive⋎u s ∧ Connected⋎u s
■

=GFT
⦏Set⋎u_ord⋎u_thm⦎ =	⊢ ∀s⦁ Ordinal⋎u s ⇒ Set⋎u s
⦏gsu_ordinal_ext_thm⦎ =	⊢ ∀ s t⦁ Ordinal⋎u s ∧ Ordinal⋎u t
					⇒ (s = t ⇔ (∀ e⦁ e ∈⋎u s ⇔ e ∈⋎u t))
⦏tc∈⋎u_ord⋎u_thm⦎ =	⊢ ∀ α β⦁ Ordinal⋎u α ∧ β ∈⋎u⋏+ α ⇒ β ∈⋎u α
=TEX

\ignore{
=SML
val SetOfSets⋎u_def = get_spec ⌜SetOfSets⋎u⌝;
val ord⋎u_def = get_spec ⌜Ordinal⋎u⌝;

val Set⋎u_ord⋎u_thm = save_thm ("Set⋎u_ord⋎u_thm",
	tac_proof(([], ⌜∀s :'a GSU⦁ Ordinal⋎u s ⇒ Set⋎u s⌝), (prove_tac [ord⋎u_def, SetOfSets⋎u_def])));

set_goal([], ⌜∀ s t⦁ Ordinal⋎u s ∧ Ordinal⋎u t ⇒ (s = t ⇔ (∀ e⦁ e ∈⋎u s ⇔ e ∈⋎u t))⌝);
a (REPEAT ∀_tac THEN rewrite_tac [ord⋎u_def, SetOfSets⋎u_def]
	THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY asm_rewrite_tac[]);
a (all_ufc_⇔_rewrite_tac [gsu_ext_axiom] THEN POP_ASM_T ante_tac THEN rewrite_tac[]);
val gsu_ordinal_ext_thm = save_pop_thm "gsu_ordinal_ext_thm";

set_goal([], ⌜∀α β⦁ Ordinal⋎u α ∧ β ∈⋎u⋏+ α ⇒ β ∈⋎u α⌝);
a (REPEAT ∀_tac
	THEN REPEAT strip_tac
	THEN all_fc_tac [ord⋎u_def]
	THEN (lemma_tac ⌜Set⋎u α⌝ THEN1 all_fc_tac [Set⋎u_ord⋎u_thm])
	THEN all_fc_tac [Tran_set_tc∈⋎u_thm]);
val tc∈⋎u_ord⋎u_thm = save_pop_thm "tc∈⋎u_ord⋎u_thm";
=TEX
}%ignore


We now introduce infix ordering relations over ordinals.

=SML
declare_infix(240,"<⋎u");
declare_infix(240,"≤⋎u");

ⓈHOLCONST
│ $⦏<⋎u⦎ : 'a GSU → 'a GSU → BOOL
├─────────────────────
│  ∀x y:'a GSU⦁ x <⋎u y ⇔ Ordinal⋎u x ∧ Ordinal⋎u y ∧ x ∈⋎u y
■



=GFT
⦏lt⋎u_∈⋎u_thm⦎ =
	⊢ ∀ α β⦁ α <⋎u β ⇒ Ordinal⋎u α ∧ Ordinal⋎u β ∧ α ∈⋎u β

⦏∈⋎u_lt⋎u_thm⦎ =
	⊢ ∀ α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ∧ α ∈⋎u β ⇒ α <⋎u β

⦏∈⋎u_⇔_lt⋎u_thm⦎ =
	⊢ ∀ α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ (α ∈⋎u β ⇔ α <⋎u β)

⦏tc∈⋎u_⇔_lt⋎u_thm⦎ =
	⊢ ∀ α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ (α ∈⋎u⋏+ β ⇔ α <⋎u β)

⦏ord⋎u_∈⋎u_⊂⋎u_thm⦎ =
	⊢ ∀ α⦁ Ordinal⋎u α ⇒ (∀ β⦁ β ∈⋎u α ⇒ β ⊂⋎u α)

⦏ord⋎u_∈⋎u_trans_thm⦎ =
	⊢ ∀ α⦁ Ordinal⋎u α ⇒ (∀ β γ⦁ β ∈⋎u α ∧ γ ∈⋎u β ⇒ β ∈⋎u α)

⦏lt⋎u_⊂⋎u_thm⦎ =
	⊢ ∀ α β⦁ α <⋎u β ⇒ α ⊂⋎u β

⦏lt⋎u_trans_thm⦎ =
	⊢ ∀ α β γ⦁ α <⋎u β ∧ β <⋎u γ ⇒ α <⋎u γ
=TEX

\ignore{
=SML
set_goal([], ⌜∀α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ∧ α ∈⋎u β ⇒ α <⋎u β⌝);
a (REPEAT strip_tac THEN asm_rewrite_tac [get_spec ⌜$<⋎u⌝]);
val ∈⋎u_lt⋎u_thm = save_pop_thm "∈⋎u_lt⋎u_thm";

set_goal([], ⌜∀α β⦁ α <⋎u β ⇒ Ordinal⋎u α ∧ Ordinal⋎u β ∧ α ∈⋎u β⌝);
a (rewrite_tac [get_spec ⌜$<⋎u⌝]
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac []);
val lt⋎u_∈⋎u_thm = save_pop_thm "lt⋎u_∈⋎u_thm";

set_goal([], ⌜∀α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ (α ∈⋎u β ⇔ α <⋎u β)⌝);
a (REPEAT strip_tac
	THEN all_fc_tac [∈⋎u_lt⋎u_thm, lt⋎u_∈⋎u_thm]);
val ∈⋎u_⇔_lt⋎u_thm = save_pop_thm "∈⋎u_⇔_lt⋎u_thm";

set_goal([], ⌜∀α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ (α ∈⋎u⋏+ β ⇔ α <⋎u β)⌝);
a (REPEAT strip_tac THEN REPEAT (all_fc_tac
	[tc∈⋎u_ord⋎u_thm, ∈⋎u_lt⋎u_thm, lt⋎u_∈⋎u_thm, tc∈⋎u_incr_thm]));
val tc∈⋎u_⇔_lt⋎u_thm = save_pop_thm "tc∈⋎u_⇔_lt⋎u_thm";

set_goal([], ⌜∀α⦁ Ordinal⋎u α ⇒ ∀β⦁ β ∈⋎u α ⇒ β ⊂⋎u α⌝);
a (REPEAT strip_tac
	THEN fc_tac [get_spec ⌜Ordinal⋎u⌝]
	THEN fc_tac [Transitive⋎u_def]);
a (rewrite_tac [⊂⋎u_def]);
a (asm_fc_tac []
	THEN asm_rewrite_tac [⊆⋎u_def]
	THEN REPEAT strip_tac);
a (∃_tac ⌜β⌝ THEN asm_rewrite_tac[wf_ul1]);
val ord⋎u_∈⋎u_⊂⋎u_thm = save_pop_thm "ord⋎u_∈⋎u_⊂⋎u_thm";

set_goal([], ⌜∀α⦁ Ordinal⋎u α ⇒ ∀β γ⦁ β ∈⋎u α ∧ γ ∈⋎u β ⇒ γ ∈⋎u α⌝);
a (REPEAT strip_tac);
a (all_fc_tac[ord⋎u_∈⋎u_⊂⋎u_thm]);
a (POP_ASM_T ante_tac THEN rewrite_tac[get_spec ⌜$⊂⋎u⌝, get_spec ⌜$⊆⋎u⌝]);
a (REPEAT strip_tac THEN asm_fc_tac[]);
val ord⋎u_∈⋎u_trans_thm = save_pop_thm "ord⋎u_∈⋎u_trans_thm";

set_goal([], ⌜∀α β⦁ α <⋎u β ⇒ α ⊂⋎u β⌝);
a (REPEAT strip_tac THEN fc_tac [lt⋎u_∈⋎u_thm]);
a (fc_tac [∀_elim ⌜β⌝ ord⋎u_∈⋎u_⊂⋎u_thm]);
a (asm_fc_tac[]);
val lt⋎u_⊂⋎u_thm = save_pop_thm "lt⋎u_⊂⋎u_thm";

set_goal([], ⌜∀α β γ⦁ α <⋎u β ∧ β <⋎u  γ ⇒ α <⋎u γ⌝);
a (rewrite_tac [get_spec ⌜$<⋎u⌝] THEN REPEAT strip_tac);
a (lemma_tac ⌜Transitive⋎u γ⌝ THEN1 fc_tac [get_spec ⌜Ordinal⋎u⌝]);
a (all_fc_tac [Transitive⋎u_def]);
a (all_fc_tac [⊆⋎u_def]);
val lt⋎u_trans_thm = save_pop_thm "lt⋎u_trans_thm";
=TEX
}%ignore


ⓈHOLCONST
│ $⦏≤⋎u⦎ : 'a GSU → 'a GSU → BOOL
├──────────────────────
│  ∀x y:'a GSU⦁ x ≤⋎u y ⇔ Ordinal⋎u x ∧ Ordinal⋎u y ∧ (x ∈⋎u y ∨ x = y)
■

=GFT
⦏≤⋎u_lt⋎u_thm⦎ =
	⊢ ∀ α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ (α ≤⋎u β ⇔ α <⋎u β ∨ α = β)

⦏≤⋎u_lt⋎u_thm2⦎ =
	⊢ ∀ x y⦁ x ≤⋎u y ⇔ Ordinal⋎u x ∧ Ordinal⋎u y ∧ (x <⋎u y ∨ x = y)

⦏≤⋎u_⊆⋎u_thm⦎ =
	⊢ ∀ α β⦁ α ≤⋎u β ⇒ α ⊆⋎u β

⦏≤⋎u_trans_thm⦎ =
	⊢ ∀ α β γ⦁ α ≤⋎u β ∧ β ≤⋎u γ ⇒ α ≤⋎u γ

⦏≤⋎u_lt⋎u_trans_thm⦎ =
	⊢ ∀ α β γ⦁ α ≤⋎u β ∧ β <⋎u γ ⇒ α <⋎u γ

⦏lt⋎u_≤⋎u_trans_thm⦎ =
	⊢ ∀ α β γ⦁ α <⋎u β ∧ β ≤⋎u γ ⇒ α <⋎u γ
=TEX

\ignore{
=SML
set_goal([], ⌜∀ α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ (α ≤⋎u β ⇔ α <⋎u β ∨ α = β)⌝);
a (rewrite_tac [get_spec ⌜$≤⋎u⌝, get_spec ⌜$<⋎u⌝] THEN REPEAT strip_tac);
val ≤⋎u_lt⋎u_thm = save_pop_thm "≤⋎u_lt⋎u_thm";

set_goal([], ⌜∀x y:'a GSU⦁ x ≤⋎u y ⇔ Ordinal⋎u x ∧ Ordinal⋎u y ∧ (x <⋎u y ∨ x = y)⌝);
a (rewrite_tac [get_spec ⌜$≤⋎u⌝, get_spec ⌜$<⋎u⌝]);
a (REPEAT strip_tac);
val ≤⋎u_lt⋎u_thm2 = save_pop_thm "≤⋎u_lt⋎u_thm2";

set_goal([], ⌜∀α β⦁ α ≤⋎u β ⇒ α ⊆⋎u β⌝);
a (REPEAT strip_tac);
a (fc_tac [≤⋎u_lt⋎u_thm2]);
(* *** Goal "1" *** *)
a (fc_tac[lt⋎u_⊂⋎u_thm]);
a (fc_tac[⊂⋎u_def]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac []);
val ≤⋎u_⊆⋎u_thm = save_pop_thm "≤⋎u_⊆⋎u_thm";

set_goal([], ⌜∀α β γ⦁ α ≤⋎u β ∧ β ≤⋎u γ ⇒ α ≤⋎u γ⌝);
a (rewrite_tac [get_spec ⌜$≤⋎u⌝]
	THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY rewrite_tac[]);
a (lemma_tac ⌜Transitive⋎u γ⌝ THEN1 fc_tac [get_spec ⌜Ordinal⋎u⌝]);
a (all_fc_tac [Transitive⋎u_def]);
a (all_fc_tac [⊆⋎u_def]);
val ≤⋎u_trans_thm = save_pop_thm "≤⋎u_trans_thm";

set_goal([], ⌜∀α β γ⦁ α ≤⋎u β ∧ β <⋎u γ ⇒ α <⋎u γ⌝);
a (rewrite_tac [get_spec ⌜$≤⋎u⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [∈⋎u_lt⋎u_thm]);
a (all_fc_tac [lt⋎u_trans_thm]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
val ≤⋎u_lt⋎u_trans_thm = save_pop_thm "≤⋎u_lt⋎u_trans_thm";

set_goal([], ⌜∀α β γ⦁ α <⋎u β ∧ β ≤⋎u γ ⇒ α <⋎u γ⌝);
a (rewrite_tac [get_spec ⌜$≤⋎u⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (strip_asm_tac (list_∀_elim [⌜β⌝, ⌜γ⌝] ∈⋎u_lt⋎u_thm));
a (all_fc_tac [lt⋎u_trans_thm]);
(* *** Goal "2" *** *)
a (all_var_elim_asm_tac);
val lt⋎u_≤⋎u_trans_thm = save_pop_thm "lt⋎u_≤⋎u_trans_thm";
=TEX
}%ignore

The following definition gives the successor function over the ordinals (this appears later in Drake).

ⓈHOLCONST
 ⦏Suc⋎u⦎ : 'a GSU → 'a GSU
├
  ∀x:'a GSU⦁ Suc⋎u x = x ∪⋎u (Unit⋎u x)
■

=GFT
⦏Set⋎u_Suc⋎u_thm⦎ =	⊢ ∀ s⦁ Set⋎u (Suc⋎u s)
⦏⊆⋎u_Suc⋎u_thm⦎ =	⊢ ∀ s⦁ s ⊆⋎u Suc⋎u s ∧ Unit⋎u s ⊆⋎u Suc⋎u s
⦏∈⋎u_Suc⋎u_thm⦎ =		⊢ ∀x y⦁ x ∈⋎u Suc⋎u y ⇔ x ∈⋎u y ∨ x = y
⦏∈⋎u_Suc⋎u_thm2⦎ =		⊢ ∀ s⦁ s ∈⋎u Suc⋎u s
=TEX

\ignore{
=SML
val Suc⋎u_def = get_spec ⌜Suc⋎u⌝;

set_goal([], ⌜∀s⦁ Set⋎u (Suc⋎u s)⌝);
a (rewrite_tac[Suc⋎u_def, SetOfSets⋎u_def]);
val Set⋎u_Suc⋎u_thm = save_pop_thm "Set⋎u_Suc⋎u_thm";

set_goal([], ⌜∀s⦁ s ⊆⋎u Suc⋎u s ∧ Unit⋎u s ⊆⋎u Suc⋎u s⌝);
a (rewrite_tac[Suc⋎u_def, SetOfSets⋎u_def]);
val ⊆⋎u_Suc⋎u_thm = save_pop_thm "⊆⋎u_Suc⋎u_thm";

set_goal([], ⌜∀x y⦁ x ∈⋎u Suc⋎u y ⇔ x ∈⋎u y ∨ x = y⌝);
a (REPEAT ∀_tac THEN rewrite_tac [Suc⋎u_def]);
val ∈⋎u_Suc⋎u_thm = save_pop_thm "∈⋎u_Suc⋎u_thm";

set_goal([], ⌜∀s⦁ s ∈⋎u Suc⋎u s⌝);
a (rewrite_tac[Suc⋎u_def, SetOfSets⋎u_def]);
val ∈⋎u_Suc⋎u_thm2 = save_pop_thm "∈⋎u_Suc⋎u_thm2";

add_rw_thms [Set⋎u_ord⋎u_thm, Set⋎u_Suc⋎u_thm, ⊆⋎u_Suc⋎u_thm, ∈⋎u_Suc⋎u_thm] "'gsu-ord";
add_sc_thms [Set⋎u_ord⋎u_thm, Set⋎u_Suc⋎u_thm, ⊆⋎u_Suc⋎u_thm, ∈⋎u_Suc⋎u_thm] "'gsu-ord";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-ord"];
=TEX
}%ignore

\subsection{The Empty Set and its Successors}

We prove that the empty set is an ordinal, and that the members of an ordinal and the successor of an ordinal are ordinals.

\subsubsection{The Empty Set is an Ordinal}

First we prove that the empty set is an ordinal, which requires only rewriting with the relevant definitions.
We then give a theorem necessitated by the presence of urelements which are extensionally equivalent to the empty set, telling us that the only ordinal with empty extension is the empty set.

=GFT
⦏ord⋎u_∅⋎u_thm⦎ =		⊢ Ordinal⋎u ∅⋎u
⦏ord⋎u_eq_∅⋎u_thm⦎ =	⊢ ∀ α⦁ Ordinal⋎u α ∧ α =⋎u ∅⋎u ⇒ α = ∅⋎u
=TEX

\ignore{
=SML
set_goal([], ⌜	Ordinal⋎u ∅⋎u	⌝);
a (rewrite_tac[SetOfSets⋎u_def, get_spec ⌜Ordinal⋎u⌝, Transitive⋎u_def, get_spec ⌜Connected⋎u⌝]);
val ord⋎u_∅⋎u_thm = save_pop_thm "ord⋎u_∅⋎u_thm";

set_goal([], ⌜∀α⦁ Ordinal⋎u α ∧ α =⋎u ∅⋎u ⇒ α = ∅⋎u⌝);
a (REPEAT strip_tac);
a (gsu_ext_tac THEN1 contr_tac);
(* *** Goal "1" *** *)
a (fc_tac [get_spec ⌜$=⋎u⌝]);
a (swap_asm_concl_tac ⌜X⋎u α = X⋎u ∅⋎u⌝
	THEN rewrite_tac [X⋎u_def, sets_ext_clauses]
	THEN contr_tac);
a (spec_nth_asm_tac 1 ⌜e⌝);
a (POP_ASM_T ante_tac THEN PC_T1 "hol1" rewrite_tac[]
	THEN strip_tac);
(* *** Goal "2" *** *)
a (all_fc_tac [Set⋎u_ord⋎u_thm]);
val ord⋎u_eq_∅⋎u_thm = save_pop_thm "ord⋎u_eq_∅⋎u_thm";

add_rw_thms [ord⋎u_∅⋎u_thm] "'gsu-ord";
add_sc_thms [ord⋎u_∅⋎u_thm] "'gsu-ord";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-ord"];
=TEX
}%ignore

\subsubsection{The Successor of an Ordinal is an Ordinal}

Next we prove that the successor of an ordinal is an ordinal.
This is done in two parts, transitivity and connectedness.

=GFT
⦏tran⋎u_suc⋎u_tran⋎u_thm⦎ =	⊢ ∀x⦁ Transitive⋎u x ⇒ Transitive⋎u (Suc⋎u x)
⦏conn⋎u_suc⋎u_conn⋎u_thm⦎ =	⊢ ∀x⦁ Connected⋎u x ⇒ Connected⋎u (Suc⋎u x)
=TEX

\ignore{

=SML
set_goal([], ⌜	∀ x:'a GSU⦁ Transitive⋎u x ⇒ Transitive⋎u (Suc⋎u x)	⌝);
=TEX

=SML
a (rewrite_tac[Transitive⋎u_def, get_spec ⌜Suc⋎u⌝]
	THEN REPEAT strip_tac
	THEN once_rewrite_tac [gsu_relext_clauses]
	THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 4 ⌜e⌝);
a (POP_ASM_T ante_tac);
a (once_rewrite_tac [get_spec⌜$⊆⋎u⌝]
	THEN strip_tac);
a (all_asm_fc_tac[]);
val tran⋎u_suc⋎u_tran⋎u_thm = save_pop_thm "tran⋎u_suc⋎u_tran⋎u_thm";
=TEX

=SML
set_goal([],⌜∀ x:'a GSU⦁
	Connected⋎u x ⇒ Connected⋎u (Suc⋎u x)
⌝);
=TEX

=SML
a (rewrite_tac[get_spec ⌜Connected⋎u⌝, get_spec ⌜Suc⋎u⌝]);
a (REPEAT strip_tac
	THEN all_asm_fc_tac[]
	THEN all_var_elim_asm_tac);
val conn⋎u_suc⋎u_conn⋎u_thm = save_pop_thm "conn⋎u_suc⋎u_conn⋎u_thm";
=TEX
}%ignore

These together enable us to prove:

=GFT
⦏ord⋎u_suc⋎u_ord⋎u_thm⦎ =	⊢ ∀ x⦁ Ordinal⋎u x ⇒ Ordinal⋎u (Suc⋎u x)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ x:'a GSU⦁ Ordinal⋎u x ⇒ Ordinal⋎u (Suc⋎u x)⌝);
a (rewrite_tac[get_spec ⌜Ordinal⋎u⌝]
	THEN REPEAT strip_tac
	THEN fc_tac [tran⋎u_suc⋎u_tran⋎u_thm, conn⋎u_suc⋎u_conn⋎u_thm]);
a (DROP_NTH_ASM_T 5 ante_tac THEN rewrite_tac [SetOfSets⋎u_def, Suc⋎u_def]
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]
	THEN asm_rewrite_tac[]); 
val ord⋎u_suc⋎u_ord⋎u_thm = save_pop_thm "ord⋎u_suc⋎u_ord⋎u_thm";
=TEX
}%ignore

\subsubsection{The Ordinal Zero is not a Successor}

=GFT
⦏∅⋎u_not_Suc⋎u_thm⦎ =	⊢ ¬ (∃ α⦁ Suc⋎u α = ∅⋎u)
⦏¬_eq_suc⋎u_thm⦎ =	⊢ ∀ α⦁ ¬ α = Suc⋎u α
⦏≤⋎u_suc⋎u_thm⦎ =	⊢ ∀ α⦁ Ordinal⋎u α ⇒ α ≤⋎u Suc⋎u α
⦏lt⋎u_suc⋎u_thm⦎ =	⊢ ∀ α⦁ Ordinal⋎u α ⇒ α <⋎u Suc⋎u α
=TEX

\ignore{
=SML
set_goal([], ⌜¬ ∃α⦁ Suc⋎u α = ∅⋎u⌝);
a ( strip_tac THEN strip_tac);
a (rewrite_tac [get_spec ⌜Suc⋎u⌝]);
a (once_rewrite_tac [gsu_ext_conv ⌜α ∪⋎u Unit⋎u α = ∅⋎u⌝]);
a (rewrite_tac [get_spec ⌜$∪⋎u⌝]);
a (contr_tac);
a (spec_nth_asm_tac 1 ⌜α⌝);
val ∅⋎u_not_Suc⋎u_thm = save_pop_thm "∅⋎u_not_Suc⋎u_thm";

set_goal ([], ⌜∀α⦁ ¬ α = Suc⋎u α⌝);
a (contr_tac);
a (lemma_tac ⌜∀x⦁ x ∈⋎u α ⇔ x ∈⋎u Suc⋎u α⌝
	THEN1 (SYM_ASMS_T pure_rewrite_tac THEN REPEAT strip_tac));
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜Suc⋎u⌝]
	THEN REPEAT strip_tac);
a (∃_tac ⌜α⌝ THEN rewrite_tac [wf_ul1]);
val ¬_eq_suc⋎u_thm = save_pop_thm "¬_eq_suc⋎u_thm";

set_goal ([], ⌜∀α⦁ Ordinal⋎u α ⇒ α ≤⋎u Suc⋎u α⌝);
a (rewrite_tac [get_spec ⌜$≤⋎u⌝]
	THEN REPEAT strip_tac);
a (fc_tac [ord⋎u_suc⋎u_ord⋎u_thm]);
val ≤⋎u_suc⋎u_thm = save_pop_thm "≤⋎u_suc⋎u_thm";

set_goal ([], ⌜∀α⦁ Ordinal⋎u α ⇒ α <⋎u Suc⋎u α⌝);
a (rewrite_tac [get_spec ⌜$<⋎u⌝]
	THEN REPEAT strip_tac);
a (fc_tac [ord⋎u_suc⋎u_ord⋎u_thm]);
val lt⋎u_suc⋎u_thm = save_pop_thm "lt⋎u_suc⋎u_thm";
=TEX
}%ignore

\subsubsection{The members of an Ordinal are Ordinals}

We now aim to prove that the members of an ordinal are ordinals.
We do this by proving first that they are connected and then that they are transitive.
First however, we show that any Subset of a connected set is connected.

=GFT
⦏conn_⊆⋎u_conn⦎ = ∀x⦁ Connected⋎u x ⇒ ∀ y:'a GSU⦁ y ⊆⋎u x ⇒ Connected⋎u y
=TEX

\ignore{
=SML
set_goal([],⌜
	∀ x:'a GSU⦁ Connected⋎u x ⇒ ∀ y:'a GSU⦁ y ⊆⋎u x ⇒ Connected⋎u y
⌝);
=TEX
The proof consists of expanding appropriate definitions, stripping the goal and then reasoning forward from the assumptions.
=SML
a (rewrite_tac (map get_spec [⌜Connected⋎u⌝, ⌜$⊆⋎u⌝])
	THEN REPEAT_N 7 strip_tac);
=GFT
(* *** Goal "" *** *)

(*  4 *)  ⌜∀ t u⦁ t ∈⋎u x ∧ u ∈⋎u x ⇒ t ∈⋎u u ∨ t = u ∨ u ∈⋎u t⌝
(*  3 *)  ⌜∀ e⦁ e ∈⋎u y ⇒ e ∈⋎u x⌝
(*  2 *)  ⌜t ∈⋎u y⌝
(*  1 *)  ⌜u ∈⋎u y⌝

(* ?⊢ *)  ⌜t ∈⋎u u ∨ t = u ∨ u ∈⋎u t⌝
=SML
a (all_asm_fc_tac[]);
a (REPEAT_N 2 (asm_fc_tac[]) THEN REPEAT strip_tac);
val conn_⊆⋎u_conn = save_pop_thm "conn_⊆⋎u_conn";
=TEX
}%ignore

Now we show that any member of an ordinal is an ordinal.

=GFT
⦏conn_∈⋎u_ord⦎ = ∀ x⦁ Ordinal⋎u x ⇒ ∀ y:'a GSU⦁ y ∈⋎u x ⇒ Connected⋎u y
=TEX

\ignore{
=SML
set_goal([],⌜
	∀ x:'a GSU⦁ Ordinal⋎u x ⇒ ∀ y:'a GSU⦁ y ∈⋎u x ⇒ Connected⋎u y
⌝);
=TEX
Expanding the definition of ordinal and making use of transitivity enables us to infer that members of an ordinals are Subsets and permits application of the previous result to obtain connectedness.
=SML
a (rewrite_tac (map get_spec [⌜Ordinal⋎u⌝, ⌜Transitive⋎u⌝])
	THEN REPEAT strip_tac);
a (all_asm_fc_tac []);
a (all_asm_fc_tac [conn_⊆⋎u_conn]);
val conn_∈⋎u_ord = save_pop_thm "conn_∈⋎u_ord";
=TEX
}%ignore

To prove that the members of an ordinal are transitive, well-foundedness is needed.
Now we are ready to prove that the members of an ordinal are transitive.

=GFT
⦏tran⋎u_∈⋎u_ord⦎ = ⊢ ∀ x⦁ Ordinal⋎u x ⇒ ∀ y:'a GSU⦁ y ∈⋎u x ⇒ Transitive⋎u y
=TEX

\ignore{
=SML
set_goal([], ⌜∀ x:'a GSU⦁ Ordinal⋎u x ⇒ ∀ y:'a GSU⦁ y ∈⋎u x ⇒ Transitive⋎u y⌝);
a (rewrite_tac (map get_spec [⌜Ordinal⋎u⌝, ⌜Transitive⋎u⌝]));
a (REPEAT strip_tac);
a (rewrite_tac[⊆⋎u_def]
	THEN REPEAT strip_tac);
a (REPEAT_N 4 (all_asm_fc_tac[∈⋎u⊆⋎u_def]));
a (fc_tac[get_spec⌜Connected⋎u⌝]);
a (lemma_tac ⌜y ∈⋎u e' ∨ y = e' ∨ e' ∈⋎u y⌝);
(* *** Goal "1" *** *)
a (list_spec_nth_asm_tac 1 [⌜e'⌝, ⌜y⌝]
	THEN REPEAT strip_tac);
a( POP_ASM_T ante_tac THEN once_asm_rewrite_tac[]);
a (rewrite_tac[]);
(* *** Goal "2" *** *)
a (asm_tac wf_ul3);
a (list_spec_nth_asm_tac 1 [⌜e⌝, ⌜y⌝, ⌜e'⌝]);
(* *** Goal "3" *** *)
a (all_var_elim_asm_tac);
a (asm_tac wf_ul2);
a (list_spec_nth_asm_tac 1 [⌜e⌝, ⌜e'⌝]);
val tran⋎u_∈⋎u_ord = save_pop_thm "tran⋎u_∈⋎u_ord";
=TEX
}%ignore

We also need to prove that the members of an ordinal are all sets of sets.

=GFT
⦏setosets_∈⋎u_ord⦎ = ⊢ ∀ x⦁ Ordinal⋎u x ⇒ (∀ y⦁ y ∈⋎u x ⇒ SetOfSets⋎u y)
=TEX


\ignore{
=SML
set_goal([], ⌜∀ x:'a GSU⦁ Ordinal⋎u x ⇒ ∀ y:'a GSU⦁ y ∈⋎u x ⇒ SetOfSets⋎u y⌝);
a (rewrite_tac (map get_spec [⌜Ordinal⋎u⌝, ⌜SetOfSets⋎u⌝, ⌜Transitive⋎u⌝]));
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (ASM_FC_T (MAP_EVERY ante_tac) []
	THEN rewrite_tac [gsu_relext_clauses]
	THEN REPEAT strip_tac
	THEN REPEAT (asm_ufc_tac[]));
val setofsets_∈⋎u_ord = save_pop_thm "setofsets_∈⋎u_ord";
=TEX
}%ignore

Finally we prove that all members of an ordinal are ordinals.

=GFT
⦏ord⋎u_∈⋎u_ord⋎u_thm⦎ =	⊢ ∀ x⦁ Ordinal⋎u x ⇒ ∀ y:'a GSU⦁ y ∈⋎u x ⇒ Ordinal⋎u y
⦏ord⋎u_tc∈⋎u_ord⋎u_thm⦎ =	⊢ ∀ x⦁ Ordinal⋎u x ⇒ (∀ y⦁ y ∈⋎u⋏+ x ⇒ Ordinal⋎u y)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ x:'a GSU⦁ Ordinal⋎u x ⇒ ∀ y:'a GSU⦁ y ∈⋎u x ⇒ Ordinal⋎u y⌝);
a (REPEAT strip_tac);
a (rewrite_tac [get_spec ⌜Ordinal⋎u⌝]);
a (all_fc_tac [tran⋎u_∈⋎u_ord, conn_∈⋎u_ord, setofsets_∈⋎u_ord]);
a contr_tac;
val ord⋎u_∈⋎u_ord⋎u_thm = save_pop_thm "ord⋎u_∈⋎u_ord⋎u_thm";

set_goal([], ⌜∀ x:'a GSU⦁ Ordinal⋎u x ⇒ ∀ y:'a GSU⦁ y ∈⋎u⋏+ x ⇒ Ordinal⋎u y⌝);
a (REPEAT strip_tac);
a (fc_tac [get_spec ⌜Ordinal⋎u⌝]);
a (fc_tac [get_spec ⌜Transitive⋎u⌝]);
a (all_fc_tac [Tran_tc∈⋎u_thm]);
a (all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
val ord⋎u_tc∈⋎u_ord⋎u_thm = save_pop_thm "ord⋎u_tc∈⋎u_ord⋎u_thm";
=TEX
}%ignore


I think things might be simpler if we had an extensionality principle expressed in terms of this ordering, and then characterise addition using the ordering.

=GFT
⦏ord⋎u_ext_thm⦎ =
	⊢ ∀ α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ (α = β ⇔ (∀ γ⦁ γ <⋎u α ⇔ γ <⋎u β))
=TEX

\ignore{
=SML
set_goal([], ⌜∀α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β
	⇒ (α = β ⇔ ∀γ⦁ γ <⋎u α ⇔ γ <⋎u β)⌝);
a (REPEAT_N 3 strip_tac);
a (lemma_tac ⌜Set⋎u α ∧ Set⋎u β⌝
		THEN1 ALL_FC_T rewrite_tac [Set⋎u_ord⋎u_thm]);
a (gsu_ext_tac2 ⌜α = β⌝);
a (rewrite_tac [get_spec ⌜$<⋎u⌝] THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]
	THEN_TRY all_asm_fc_tac[]);
(* *** Goal "1" *** *)
a (lemma_tac ⌜Ordinal⋎u e⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜Ordinal⋎u e⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (spec_nth_asm_tac 3 ⌜e⌝);
val ord⋎u_ext_thm = save_pop_thm "ord⋎u_ext_thm";
=TEX
}%ignore



\subsubsection{Galaxies are Closed under Suc}

=GFT
GClose⋎u_Suc⋎u_thm = ⊢ ∀g⦁ galaxy⋎u g ⇒ ∀x⦁ x ∈⋎u g ⇒ Suc⋎u x ∈⋎u g
=TEX

\ignore{
=SML
set_goal ([], ⌜∀g⦁ galaxy⋎u g ⇒ ∀x⦁ x ∈⋎u g ⇒ Suc⋎u x ∈⋎u g⌝);
a (rewrite_tac [get_spec ⌜Suc⋎u⌝]);
a (REPEAT strip_tac);
a (REPEAT (all_fc_tac [GClose⋎u∪⋎u, GClose⋎uUnit⋎u]));
val GClose⋎u_Suc⋎u_thm = save_pop_thm "GClose⋎u_Suc⋎u_thm";
=TEX
}%ignore

\subsection{Ordinals are Linearly Ordered}

We prove that the ordinals are linearly ordered by $<⋎u$.

First we prove some lemmas:

=GFT
⦏tran⋎u_∩⋎u_thm⦎ =	⊢ ∀ x y⦁ Transitive⋎u x ∧ Transitive⋎u y ⇒ Transitive⋎u (x ∩⋎u y)
⦏tran⋎u_∪⋎u_thm⦎ =	⊢ ∀ x y⦁ Transitive⋎u x ∧ Transitive⋎u y ⇒ Transitive⋎u (x ∪⋎u y)
⦏∅⋎u_≤⋎u_thm⦎ =		⊢ ∀ α⦁ Ordinal⋎u α ⇒ ∅⋎u ≤⋎u α
⦏∅⋎u_eq_lt⋎u_thm⦎ =	⊢ ∀ α⦁ Ordinal⋎u α ⇒ α = ∅⋎u ∨ ∅⋎u <⋎u α
⦏∅⋎u_neq_∈⋎u_thm⦎ =	⊢ ∀ α⦁ Ordinal⋎u α ∧ ¬ α = ∅⋎u ⇒ ∅⋎u ∈⋎u α
⦏∅⋎u_neq⋎u_∈⋎u_thm⦎ =	⊢ ∀ α⦁ Ordinal⋎u α ∧ ¬ α =⋎u ∅⋎u ⇒ ∅⋎u ∈⋎u α
=TEX

\ignore{
=SML
set_goal([], ⌜∀ x y:'a GSU⦁ Transitive⋎u x ∧ Transitive⋎u y ⇒ Transitive⋎u (x ∩⋎u y)⌝);
a (rewrite_tac[Transitive⋎u_def]);
a (REPEAT strip_tac);
a (ALL_ASM_FC_T (MAP_EVERY ante_tac) []);
a (rewrite_tac [⊆⋎u_def]
	THEN prove_tac[]);
val tran⋎u_∩⋎u_thm = save_pop_thm "tran⋎u_∩⋎u_thm";

set_goal([], ⌜∀ x y:'a GSU⦁ Transitive⋎u x ∧ Transitive⋎u y ⇒ Transitive⋎u (x ∪⋎u y)⌝);
a (rewrite_tac[Transitive⋎u_def]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (ALL_ASM_FC_T (MAP_EVERY ante_tac) []);
a (rewrite_tac [⊆⋎u_def]
	THEN prove_tac[]);
(* *** Goal "2" *** *)
a (ALL_ASM_FC_T (MAP_EVERY ante_tac) []);
a (rewrite_tac [⊆⋎u_def]
	THEN prove_tac[]);
val tran⋎u_∪⋎u_thm = save_pop_thm "tran⋎u_∪⋎u_thm";

set_goal ([], ⌜∀α⦁ Ordinal⋎u α ⇒ ∅⋎u ≤⋎u α⌝);
a (strip_tac);
a (gsu_induction_tac ⌜α⌝);
a (strip_tac THEN lemma_tac ⌜Set⋎u t⌝ THEN1 all_fc_tac[Set⋎u_ord⋎u_thm]);
a (rewrite_tac [get_spec ⌜$≤⋎u⌝] THEN REPEAT strip_tac);
a (swap_nth_asm_concl_tac 1);
a (POP_ASM_T ante_tac THEN gsu_ext_tac2 ⌜∅⋎u = t⌝);
a (strip_tac);
a (lemma_tac ⌜Ordinal⋎u e⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (all_asm_fc_tac[]);
a (POP_ASM_T ante_tac THEN rewrite_tac[get_spec ⌜$≤⋎u⌝]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [ord⋎u_∈⋎u_trans_thm]);
(* *** Goal "2" *** *)
a (var_elim_asm_tac ⌜∅⋎u = e⌝);
val ∅⋎u_≤⋎u_thm = save_pop_thm "∅⋎u_≤⋎u_thm";

set_goal ([], ⌜∀α⦁ Ordinal⋎u α ⇒ α = ∅⋎u ∨ ∅⋎u <⋎u α⌝);
a (REPEAT strip_tac THEN all_fc_tac [∅⋎u_≤⋎u_thm]);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜$≤⋎u⌝, get_spec ⌜$<⋎u⌝]);
a (REPEAT strip_tac);
a (var_elim_asm_tac ⌜∅⋎u = α⌝);
val ∅⋎u_eq_lt⋎u_thm = save_pop_thm "∅⋎u_eq_lt⋎u_thm";

set_goal ([], ⌜∀α⦁ Ordinal⋎u α ∧ ¬ α = ∅⋎u ⇒ ∅⋎u ∈⋎u α⌝);
a (REPEAT strip_tac THEN all_fc_tac [∅⋎u_eq_lt⋎u_thm]);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜$<⋎u⌝]);
a (REPEAT strip_tac);
val ∅⋎u_neq_∈⋎u_thm = save_pop_thm "∅⋎u_neq_∈⋎u_thm";

set_goal ([], ⌜∀α⦁ Ordinal⋎u α ∧ ¬ α =⋎u ∅⋎u ⇒ ∅⋎u ∈⋎u α⌝);
a (REPEAT strip_tac);
a (fc_tac [¬eq⋎u_¬eq_thm]);
a (lemma_tac ⌜Set⋎u α⌝ THEN all_fc_tac [Set⋎u_ord⋎u_thm]);
a (all_fc_tac [∅⋎u_neq_∈⋎u_thm]);
val ∅⋎u_neq⋎u_∈⋎u_thm = save_pop_thm "∅⋎u_neq⋎u_∈⋎u_thm";
=TEX
}%ignore

=GFT
⦏conn_∩⋎u_thm⦎ =
	⊢ ∀ x y:'a GSU⦁ Connected⋎u x ∧ Connected⋎u y ⇒ Connected⋎u (x ∩⋎u y)
⦏setofsets_∩⋎u_thm⦎ =
	⊢ ∀ x y⦁ SetOfSets⋎u x ∧ SetOfSets⋎u y ⇒ SetOfSets⋎u (x ∩⋎u y)
⦏ord⋎u_∩⋎u_thm⦎ =
	⊢ ∀ x y:'a GSU⦁ Ordinal⋎u x ∧ Ordinal⋎u y ⇒ Ordinal⋎u (x ∩⋎u y)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ x y:'a GSU⦁ Connected⋎u x ∧ Connected⋎u y ⇒ Connected⋎u (x ∩⋎u y)⌝);
a (rewrite_tac[get_spec ⌜Connected⋎u⌝]);
a (REPEAT strip_tac);
a (list_spec_nth_asm_tac 8 [⌜t⌝, ⌜u⌝]);
val conn_∩⋎u_thm = save_pop_thm "conn_∩⋎u_thm";

set_goal([], ⌜∀ x y:'a GSU⦁ SetOfSets⋎u x ∧ SetOfSets⋎u y ⇒ SetOfSets⋎u (x ∩⋎u y)⌝);
a (rewrite_tac[get_spec ⌜SetOfSets⋎u⌝]);
a (REPEAT strip_tac);
a (asm_fc_tac[]);
val setofsets_∩⋎u_thm = save_pop_thm "setofsets_∩⋎u_thm";

set_goal([], ⌜∀ x y:'a GSU⦁ Ordinal⋎u x ∧ Ordinal⋎u y ⇒ Ordinal⋎u (x ∩⋎u y)⌝);
a (rewrite_tac[get_spec ⌜Ordinal⋎u⌝]);
a (REPEAT_N 3 strip_tac);
a (all_asm_fc_tac [tran⋎u_∩⋎u_thm, conn_∩⋎u_thm, setofsets_∩⋎u_thm]
	THEN contr_tac);
val ord⋎u_∩⋎u_thm = save_pop_thm "ord⋎u_∩⋎u_thm";
=TEX
}%ignore

=GFT
⦏trichot⋎u_lemma⦎ =
	⊢ ∀ x y⦁ Ordinal⋎u x ∧ Ordinal⋎u y ∧ x ⊆⋎u y ∧ ¬ x = y ⇒ x ∈⋎u y
=TEX

\ignore{
=SML
set_goal([], ⌜∀ x y:'a GSU⦁ Ordinal⋎u x ∧ Ordinal⋎u y ∧ x ⊆⋎u y ∧ ¬ x = y ⇒ x ∈⋎u y⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜∃z⦁ z = Sep⋎u y (λv⦁ ¬ v ∈⋎u x)⌝ THEN1 prove_∃_tac);
a (DROP_NTH_ASM_T 3 ante_tac THEN rewrite_tac [gsu_relext_clauses] THEN strip_tac);
a (DROP_NTH_ASM_T 3 ante_tac);
a (all_asm_ufc_⇔_rewrite_tac [gsu_ordinal_ext_thm]);
a (strip_tac THEN asm_fc_tac[]);
a (lemma_tac ⌜e ∈⋎u z⌝ THEN1 asm_rewrite_tac[]);
a (strip_asm_tac gsu_wf_min_thm);
a (spec_nth_asm_tac 1 ⌜z⌝);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜e⌝);
(* *** Goal "2" *** *)
a (lemma_tac ⌜z' ∈⋎u y ∧ ¬ z' ∈⋎u x⌝
	THEN1 (DROP_NTH_ASM_T 2 ante_tac
		THEN asm_rewrite_tac[]));
a (lemma_tac ⌜Ordinal⋎u z'⌝ THEN1 (all_ufc_tac [ord⋎u_∈⋎u_ord⋎u_thm]));
a (lemma_tac ⌜z' = x⌝);
(* *** Goal "2.1" *** *)
a (LEMMA_T ⌜z' = x ⇔ (∀ e⦁ e ∈⋎u z' ⇔ e ∈⋎u x)⌝ rewrite_thm_tac THEN1 (ALL_UFC_⇔_T rewrite_tac [gsu_ordinal_ext_thm]));
a (REPEAT strip_tac);
(* *** Goal "2.1.1" *** *)
a (lemma_tac ⌜e' ∈⋎u  y⌝);
(* *** Goal "2.1.1.1" *** *)
a (lemma_tac ⌜Transitive⋎u y⌝
	THEN1 (all_asm_fc_tac [get_spec ⌜Ordinal⋎u⌝]));
a (LEMMA_T ⌜z' ⊆⋎u y⌝ ante_tac THEN1 (all_asm_fc_tac [Transitive⋎u_def]));
a (rewrite_tac [⊆⋎u_def]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
(* *** Goal "2.1.1.2" *** *)
a (spec_nth_asm_tac 6 ⌜e'⌝);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
a (lemma_tac ⌜e' ∈⋎u y⌝
	THEN1 (GET_NTH_ASM_T 11 ante_tac
		THEN asm_prove_tac[]));
a (LEMMA_T ⌜Connected⋎u y⌝ (fn x=> asm_tac(rewrite_rule [get_spec ⌜Connected⋎u⌝] x)) 
	THEN1 (all_asm_fc_tac [get_spec ⌜Ordinal⋎u⌝]));
a (list_spec_nth_asm_tac 1 [⌜e'⌝, ⌜z'⌝]);
(* *** Goal "2.1.2.1" *** *)
a (swap_nth_asm_concl_tac 4 THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2.2" *** *)
a (lemma_tac ⌜Transitive⋎u x⌝
	THEN1 (all_asm_fc_tac [get_spec ⌜Ordinal⋎u⌝]));
a (LEMMA_T ⌜e' ⊆⋎u x⌝ ante_tac THEN1 (all_asm_fc_tac [Transitive⋎u_def]));
a (rewrite_tac [⊆⋎u_def]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (all_var_elim_asm_tac );
val trichot⋎u_lemma = save_pop_thm "trichot⋎u_lemma";

=IGN
set_goal([], ⌜∀ x y:'a GSU⦁ Ordinal⋎u x ∧ Ordinal⋎u y ⇒ Ordinal⋎u (x ∪⋎u y)⌝);
a (REPEAT strip_tac);
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜y⌝] trich_for_ord⋎u_thm));
(* *** Goal "1" *** *)
a 

a (spec_nth_asm_tac 1  

a (rewrite_tac[get_spec ⌜Ordinal⋎u⌝]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_asm_fc_tac [tran⋎u_∪⋎u_thm]);
(* *** Goal "2" *** *)
a (all_asm_ante_tac);
a (rewrite_tac[get_spec ⌜Connected⋎u⌝, Transitive⋎u_def]);
a (REPEAT_N 6 strip_tac);

val ord⋎u_∪⋎u_thm = save_pop_thm "ord⋎u_∪⋎u_thm";
=TEX
}%ignore

=GFT
⦏trich_for_ord⋎u_thm⦎ =
	⊢ ∀ x y⦁ Ordinal⋎u x ∧ Ordinal⋎u y ⇒ x <⋎u y ∨ x = y ∨ y <⋎u x
⦏⊆⋎u_≤⋎u_thm⦎ =
	⊢ ∀ x y⦁ Ordinal⋎u x ∧ Ordinal⋎u y ⇒ (x ⊆⋎u y ⇔ x ≤⋎u y)
⦏⊆⋎u_≤⋎u_thm1⦎ =
	⊢ ∀ x y⦁ Ordinal⋎u x ∧ Ordinal⋎u y ∧ x ⊆⋎u y ⇒ x ≤⋎u y
⦏lt⋎u_⇔_⊂⋎u_thm⦎ =
	⊢ ∀ α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ (α <⋎u β ⇔ α ⊂⋎u β)
⦏⊂⋎u_⇔_lt⋎u_thm⦎ =
	⊢ ∀ x y⦁ Ordinal⋎u x ∧ Ordinal⋎u y ⇒ (x ⊂⋎u y ⇔ x <⋎u y)
⦏⊂⋎u_lt⋎u_thm1⦎ =
	⊢ ∀ x y⦁ Ordinal⋎u x ∧ Ordinal⋎u y ∧ x ⊂⋎u y ⇒ x <⋎u y
⦏ord⋎u_sub⋎u_∈⋎u_thm⦎ =
	⊢ ∀ x y⦁ Ordinal⋎u x ∧ Ordinal⋎u y ∧ x ⊂⋎u y ⇒ x ∈⋎u y
=TEX


\ignore{
=SML
push_extend_pc "'mmp1";

set_goal([], ⌜∀ x y:'a GSU⦁ Ordinal⋎u x ∧ Ordinal⋎u y ⇒ x <⋎u y ∨ x = y ∨ y <⋎u x⌝);
a (rewrite_tac[get_spec ⌜$<⋎u⌝]);
a (REPEAT_N 3 strip_tac THEN asm_rewrite_tac[]);
a (lemma_tac ⌜Ordinal⋎u (x ∩⋎u y)⌝
	THEN1 (all_fc_tac [ord⋎u_∩⋎u_thm]));
pop_pc();
a (lemma_tac ⌜x ∩⋎u y ⊆⋎u x ∧ x ∩⋎u y ⊆⋎u y⌝
	THEN1 (prove_tac[gsu_relext_clauses, gsu_opext_clauses]));
push_extend_pc "'mmp1";

a (lemma_tac ⌜x ∩⋎u y = x ∨ x ∩⋎u y = y⌝
	THEN1 contr_tac);
(* *** Goal "1" *** *)
a (strip_asm_tac trichot⋎u_lemma);
a (all_asm_fc_tac []);
a (list_spec_nth_asm_tac 2 [⌜x ∩⋎u y⌝, ⌜x⌝]);
a (strip_asm_tac wf_ul1);
a (spec_nth_asm_tac 1 ⌜x ∩⋎u y⌝);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac [gsu_relext_clauses, gsu_opext_clauses]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜x ⊆⋎u y⌝ THEN1 (POP_ASM_T ante_tac THEN rewrite_tac[gsu_relext_clauses]));
(* *** Goal "2.1" *** *)
a (LEMMA_T ⌜x ∩⋎u y = x ⇔ (∀ e⦁ e ∈⋎u x ∩⋎u y ⇔ e ∈⋎u x)⌝ rewrite_thm_tac 
	THEN1 all_ufc_⇔_rewrite_tac [gsu_ordinal_ext_thm]);
a (REPEAT strip_tac THEN asm_fc_tac[]);
a (spec_nth_asm_tac 2 ⌜e⌝);
(* *** Goal "2.2" *** *)
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜y⌝] trichot⋎u_lemma)
	THEN contr_tac);
(* *** Goal "3" *** *)
a (lemma_tac ⌜y ⊆⋎u x⌝ THEN1 (POP_ASM_T ante_tac THEN rewrite_tac[gsu_relext_clauses]));
(* *** Goal "3.1" *** *)
a (LEMMA_T ⌜x ∩⋎u y = y ⇔ (∀ e⦁ e ∈⋎u x ∩⋎u y ⇔ e ∈⋎u y)⌝ rewrite_thm_tac 
	THEN1 all_ufc_⇔_rewrite_tac [gsu_ordinal_ext_thm]);
a (REPEAT strip_tac THEN asm_fc_tac[]);
a (spec_nth_asm_tac 2 ⌜e⌝);
(* *** Goal "3.2" *** *)
a (strip_asm_tac (list_∀_elim [⌜y⌝, ⌜x⌝] trichot⋎u_lemma)
	THEN asm_rewrite_tac[]);
val trich_for_ord⋎u_thm = save_pop_thm "trich_for_ord⋎u_thm";

set_goal([], ⌜∀x y:'a GSU⦁ Ordinal⋎u x ∧ Ordinal⋎u y ⇒ (x ⊆⋎u y ⇔ x ≤⋎u y)⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (asm_rewrite_tac [≤⋎u_lt⋎u_thm2]);
a contr_tac;
a (all_fc_tac [trich_for_ord⋎u_thm]);
a (fc_tac [lt⋎u_⊂⋎u_thm]);
a (POP_ASM_T ante_tac THEN DROP_NTH_ASM_T 4 ante_tac);
pop_pc();
a (rewrite_tac [gsu_relext_clauses, ⊂⋎u_def]
	THEN prove_tac[]);
push_extend_pc "'mmp1";
(* *** Goal "2" *** *)
a (fc_tac [≤⋎u_⊆⋎u_thm]);
val ⊆⋎u_≤⋎u_thm = save_pop_thm "⊆⋎u_≤⋎u_thm";

pop_pc();

set_goal([], ⌜∀x y:'a GSU⦁ Ordinal⋎u x ∧ Ordinal⋎u y ∧ x ⊆⋎u y ⇒ x ≤⋎u y⌝);
a (REPEAT strip_tac);
a (fc_tac [⊆⋎u_≤⋎u_thm]);
a (asm_fc_tac[]);
val ⊆⋎u_≤⋎u_thm1 = save_pop_thm "⊆⋎u_≤⋎u_thm1";

set_goal([], ⌜∀α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ (α <⋎u β ⇔ α ⊂⋎u β)⌝);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [lt⋎u_⊂⋎u_thm]);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac);
a (rewrite_tac[get_spec ⌜$⊂⋎u⌝]);
a (ALL_UFC_⇔_T rewrite_tac [⊆⋎u_≤⋎u_thm]);
a (rewrite_tac [≤⋎u_lt⋎u_thm2]);
a (REPEAT strip_tac);
a (var_elim_asm_tac ⌜α = β⌝);
val lt⋎u_⇔_⊂⋎u_thm = save_pop_thm "lt⋎u_⇔_⊂⋎u_thm";

set_goal([], ⌜∀x y:'a GSU⦁ Ordinal⋎u x ∧ Ordinal⋎u y ⇒ (x ⊂⋎u y ⇔ x <⋎u y)⌝);
a (REPEAT_N 3 strip_tac);
a (ALL_UFC_⇔_T rewrite_tac [lt⋎u_⇔_⊂⋎u_thm]);
val ⊂⋎u_⇔_lt⋎u_thm = save_pop_thm "⊂⋎u_⇔_lt⋎u_thm";

set_goal([], ⌜∀ x y:'a GSU⦁ Ordinal⋎u x ∧ Ordinal⋎u y ∧ x ⊂⋎u y ⇒ x ∈⋎u y⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜x <⋎u y⌝ THEN1 all_ufc_⇔_tac [⊂⋎u_⇔_lt⋎u_thm]);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜$<⋎u⌝] THEN REPEAT strip_tac);
val ord⋎u_sub⋎u_∈⋎u_thm = save_pop_thm "ord⋎u_sub⋎u_∈⋎u_thm";
=TEX

=IGN
set_goal([], ⌜∀x y z⦁ Ordinal⋎u x ∧ y ∈⋎u x ∧ z ∈⋎u y ⇒ z ∈⋎u x⌝);
a (REPEAT strip_tac);
a (all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (all_fc_tac [ord⋎u_∈⋎u_⊂⋎u_thm]);
a (all_fc_tac [⊂⋎u_trans_thm]);
a (all_fc_tac [tran⋎u_∈⋎u_ord]);
a (fc_tac [Transitive⋎u_def]);
a (all_asm_fc_tac[]);


=SML
set_goal([], ⌜∀x y:'a GSU⦁ Ordinal⋎u x ∧ Ordinal⋎u y ∧ x ⊂⋎u y ⇒ x <⋎u y⌝);
a (REPEAT strip_tac);
a (all_fc_tac [⊂⋎u_⇔_lt⋎u_thm]);
val ⊂⋎u_lt⋎u_thm1 = save_pop_thm "⊂⋎u_lt⋎u_thm1";
=TEX
}%ignore

\subsection{Successor and Limit Ordinals}

Successor and limit ordinals are defined.
Natural numbers are defined.

These definitions are not the ones used by Drake, and not only the names but the concepts differ.
My successor predicate does not hold of the empty set.
I use the name "natural number" where he talks of integers, and generally I'm chosing longer names.

ⓈHOLCONST
 ⦏Successor⋎u⦎ : 'a GSU → BOOL
├
  ∀s :'a GSU⦁ Successor⋎u s ⇔ ∃t⦁ Ordinal⋎u t ∧ s = Suc⋎u t
■

ⓈHOLCONST
 ⦏LimitOrdinal⋎u⦎ : 'a GSU → BOOL
├
  ∀s :'a GSU⦁ LimitOrdinal⋎u s ⇔ Ordinal⋎u s ∧ ¬ Successor⋎u s ∧ ¬ s = ∅⋎u
■

\subsection{Induction}

Induction theorems over ordinals.

=GFT
⦏Successor⋎u_ord⋎u_thm⦎ = ⊢ ∀x⦁ Successor⋎u x ⇒ Ordinal⋎u x
=TEX

\ignore{
=SML
set_goal([],⌜	∀ x:'a GSU⦁ Successor⋎u x ⇒ Ordinal⋎u x	⌝);
a (rewrite_tac[get_spec ⌜Successor⋎u⌝]
	THEN REPEAT strip_tac
	THEN fc_tac [ord⋎u_suc⋎u_ord⋎u_thm]
	THEN asm_rewrite_tac[]);
val Successor⋎u_ord⋎u_thm = save_pop_thm "Successor⋎u_ord⋎u_thm";
=TEX
}%ignore

\subsubsection{Well-foundedness of the ordinals}

First we prove that $<⋎u$ is well-founded.

=GFT
⦏wf_lt⋎u_thm⦎ =		⊢ well_founded $<⋎u
=IGN
⦏Uwf_lt⋎u_thm⦎ =	⊢ UWellFounded $<⋎u
=TEX

\ignore{
=SML
set_goal([],⌜well_founded $<⋎u⌝);
a (asm_tac gsu_wf_thm1);
a (fc_tac [wf_restrict_wf_thm]);
a (SPEC_NTH_ASM_T 1 ⌜λx y:'a GSU⦁ Ordinal⋎u x ∧ Ordinal⋎u y⌝ ante_tac
	THEN rewrite_tac[]);
a (lemma_tac ⌜$<⋎u = (λ x y⦁ (Ordinal⋎u x ∧ Ordinal⋎u y) ∧ x ∈⋎u y)⌝);
(* *** Goal "1" *** *)
a (once_rewrite_tac [ext_thm]);
a (once_rewrite_tac [ext_thm]);
a (prove_tac[get_spec ⌜$<⋎u⌝]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
val wf_lt⋎u_thm = save_pop_thm "wf_lt⋎u_thm";

set_goal([],⌜UWellFounded $<⋎u⌝);
a (rewrite_tac [UWellFounded_well_founded_thm, wf_lt⋎u_thm]);
val Uwf_lt⋎u_thm = pop_thm ();
=TEX
}%ignore

Which yeild the following induction tactics:

=SML
val ⦏'a ORDINAL_INDUCTION_T⦎ = WF_INDUCTION_T wf_lt⋎u_thm;
val ⦏ordinal_induction_tac⦎ = wf_induction_tac wf_lt⋎u_thm;
=TEX



\subsubsection{Continuity}

ⓈHOLCONST
│ ⦏Continuous⋎u⦎ : ('a GSU → 'a GSU) → BOOL
├────────────────────
│  ∀f⦁ Continuous⋎u f ⇔ ∀x⦁ LimitOrdinal⋎u x ⇒ f x = ClIm⋎u f x
■

\ignore{
=SML
val Continuous⋎u_def = get_spec ⌜Continuous⋎u⌝;

=IGN
set_goal([], ⌜∀f⦁ Continuous⋎u f ⇒ ∀α⦁ P α⌝);

=TEX
}%ignore


\subsubsection{An Ordinal is Zero, a successor or a limit}

=GFT
⦏ord⋎u_kind_thm⦎ =
	⊢ ∀n⦁ Ordinal⋎u n ⇒ n = ∅⋎u ∨ Successor⋎u n  ∨ LimitOrdinal⋎u n
=TEX

\ignore{
=SML
set_goal ([], ⌜∀n⦁ Ordinal⋎u n ⇒ n = ∅⋎u ∨ Successor⋎u n  ∨ LimitOrdinal⋎u n⌝);
a (rewrite_tac [get_spec ⌜LimitOrdinal⋎u⌝, get_spec ⌜Successor⋎u⌝]);
a (REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜t⌝);
val ord⋎u_kind_thm = save_pop_thm "ord⋎u_kind_thm";
=TEX
}%ignore

\subsection{Supremum and Strict Supremum}

The supremum of a set of ordinals is the smallest ordinal greater than or equal to every ordinal in the set.
With the Von Neumann representation of ordinals this is just the union of the set of ordinals.

=SML
declare_infix (200, "Ub⋎u");
declare_infix (200, "Sub⋎u");
=TEX

ⓈHOLCONST
│ $⦏Ub⋎u⦎ : 'a GSU → 'a GSU → BOOL
├────────────────
│  ∀α β⦁ α Ub⋎u β ⇔ ∀γ⦁ γ ∈⋎u α ⇒ γ ≤⋎u β
■

ⓈHOLCONST
│ ⦏Sup⋎u⦎ : 'a GSU → 'a GSU
├─────────────────
│  ∀α⦁ Sup⋎u α = ⋃⋎u α
■

=GFT
⦏ord⋎u_limit_thm⦎ =
	⊢ ∀ α⦁ (∀ β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒ Ordinal⋎u (⋃⋎u α)

⦏ord⋎u_Sup⋎u_thm⦎ =
	⊢ ∀ α⦁ (∀ β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒ Ordinal⋎u (Sup⋎u α)

⦏Sup⋎u_lUb⋎u_thm⦎ =
	⊢ ∀ α⦁ (∀ β⦁ β ∈⋎u α ⇒ Ordinal⋎u β)
		⇒ α Ub⋎u Sup⋎u α
		∧ (∀ γ⦁ Ordinal⋎u γ ∧ α Ub⋎u γ ⇒ Sup⋎u α ≤⋎u γ)
=TEX

\ignore{
=SML
set_goal ([], ⌜∀α⦁ (∀β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒ Ordinal⋎u (⋃⋎u α)⌝);
a (REPEAT strip_tac);
a (rewrite_tac [get_spec ⌜Ordinal⋎u⌝, Transitive⋎u_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac[SetOfSets⋎u_def] THEN REPEAT strip_tac);
a (lemma_tac ⌜Ordinal⋎u e⌝ THEN1 asm_fc_tac[]);
a (fc_tac [ord⋎u_def]);
a (fc_tac [SetOfSets⋎u_def]);
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (rewrite_tac [gsu_relext_clauses] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 4 ⌜e'⌝);
a (fc_tac [get_spec ⌜Ordinal⋎u⌝]);
a (fc_tac [Transitive⋎u_def]);
a (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[]);
a (SPEC_NTH_ASM_T 1 ⌜e⌝ (ante_tac o (rewrite_rule [gsu_relext_clauses])));
a (asm_rewrite_tac [] THEN REPEAT strip_tac);
a (asm_fc_tac[]);
(* *** Goal "3" *** *)
a (rewrite_tac [get_spec ⌜Connected⋎u⌝] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 7 ⌜e⌝);
a (spec_nth_asm_tac 8 ⌜e'⌝);
a (strip_asm_tac (list_∀_elim [⌜e⌝, ⌜e'⌝] trich_for_ord⋎u_thm));
(* *** Goal "3.1" *** *)
a (fc_tac [get_spec ⌜$<⋎u⌝]);
a (lemma_tac ⌜e ⊆⋎u e'⌝
	THEN1 (fc_tac [get_spec ⌜Ordinal⋎u⌝]
	     THEN fc_tac [Transitive⋎u_def]
		THEN asm_fc_tac[]));
a (lemma_tac ⌜t ∈⋎u e'⌝
	THEN1 (POP_ASM_T (asm_tac o (rewrite_rule [⊆⋎u_def]))
		THEN asm_fc_tac []));
a (lemma_tac ⌜Connected⋎u e'⌝ THEN1 fc_tac [get_spec ⌜Ordinal⋎u⌝]);
a (fc_tac [get_spec⌜Connected⋎u⌝]
	THEN all_asm_fc_tac[]);
(* *** Goal "3.2" *** *)
a (all_var_elim_asm_tac);
a (lemma_tac ⌜Connected⋎u e'⌝ THEN1 fc_tac [get_spec ⌜Ordinal⋎u⌝]);
a (fc_tac [get_spec⌜Connected⋎u⌝]
	THEN all_asm_fc_tac[]);
(* *** Goal "3.3" *** *)
a (fc_tac [get_spec ⌜$<⋎u⌝]);
a (lemma_tac ⌜e' ⊆⋎u e⌝
	THEN1 (fc_tac [get_spec ⌜Ordinal⋎u⌝]));
(* *** Goal "3.3.1" *** *)
a (REPEAT_N 3 (POP_ASM_T discard_tac));
a (DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac [Transitive⋎u_def] THEN strip_tac);
(* *** Goal "3.3.2" *** *)
a (asm_fc_tac[]);
a (lemma_tac ⌜u ∈⋎u e⌝
	THEN1 (POP_ASM_T (asm_tac o (rewrite_rule [⊆⋎u_def]))
		THEN asm_fc_tac []));
a (lemma_tac ⌜Connected⋎u e⌝ THEN1 fc_tac [get_spec ⌜Ordinal⋎u⌝]);
a (fc_tac [get_spec⌜Connected⋎u⌝]
	THEN all_asm_fc_tac[]);
val ord⋎u_limit_thm = save_pop_thm "ord⋎u_limit_thm";

set_goal([], ⌜∀α⦁ (∀β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒ Ordinal⋎u (Sup⋎u α)⌝);
a (rewrite_tac[get_spec ⌜Sup⋎u⌝, ord⋎u_limit_thm]);
val ord⋎u_Sup⋎u_thm = save_pop_thm "ord⋎u_Sup⋎u_thm";

set_goal([], ⌜∀α:'a GSU⦁ (∀β:'a GSU⦁ β ∈⋎u α ⇒ Ordinal⋎u β)
	⇒ α Ub⋎u (Sup⋎u α) ∧ ∀γ:'a GSU⦁ Ordinal⋎u γ ∧ α Ub⋎u γ ⇒ (Sup⋎u α) ≤⋎u γ⌝);
a (rewrite_tac [get_spec ⌜$Ub⋎u⌝, get_spec ⌜$Sup⋎u⌝] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (fc_tac [ord⋎u_limit_thm]);
a (asm_fc_tac[]);
a (LEMMA_T ⌜γ ⊆⋎u ⋃⋎u α ⇒ γ ≤⋎u ⋃⋎u α⌝ (fn x => bc_tac [x]));
(* *** Goal "1.1" *** *)
a (strip_tac);
a (all_fc_tac [⊆⋎u_≤⋎u_thm1]);
(* *** Goal "1.2" *** *)
a (rewrite_tac[gsu_relext_clauses]);
a (REPEAT strip_tac);
a (∃_tac ⌜γ⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac [ord⋎u_limit_thm]);
a (bc_tac [⊆⋎u_≤⋎u_thm1]
	THEN_TRY asm_rewrite_tac[gsu_relext_clauses]);
a (REPEAT strip_tac);
a (asm_fc_tac[]);
a (fc_tac [≤⋎u_⊆⋎u_thm]);
a (POP_ASM_T ante_tac
	THEN rewrite_tac [gsu_relext_clauses]
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
val Sup⋎u_lUb⋎u_thm = save_pop_thm "Sup⋎u_lUb⋎u_thm"; 
=TEX
}%ignore

The operand here is intended to be an arbitrary set of ordinals and the result is the smallest ordinal strictly greater than any in the set.

ⓈHOLCONST
│ $⦏Sub⋎u⦎ : 'a GSU → 'a GSU → BOOL
├─────────────────────
│  ∀α β⦁ α Sub⋎u β ⇔ ∀γ⦁ γ ∈⋎u α ⇒ γ <⋎u β
■

ⓈHOLCONST
│ ⦏Ssup⋎u⦎ : 'a GSU → 'a GSU
├──────────────────────
│  ∀α⦁ Ssup⋎u α = ⋃⋎u(Imagep⋎u Suc⋎u α)
■

=GFT
⦏Ssup⋎u_ord⋎u_thm⦎ =
	⊢ ∀ α⦁ (∀ β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒ Ordinal⋎u (Ssup⋎u α)
⦏Ssup⋎u_∈⋎u_thm⦎ =
	⊢ ∀ α⦁ (∀ β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒ (∀ β⦁ β ∈⋎u α ⇒ β ∈⋎u Ssup⋎u α)
⦏Ssup⋎u_lt⋎u_thm⦎ =
	⊢ ∀ α⦁ (∀ β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒ (∀ β⦁ β ∈⋎u α ⇒ β <⋎u Ssup⋎u α)
⦏Ssup⋎u_⊆⋎u_thm⦎ =
	⊢ ∀ α⦁ (∀ β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒ α Sub⋎u Ssup⋎u α
⦏Ssup⋎u_TrCl⋎u_thm⦎ =
	⊢ ∀ α⦁ (∀ β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒ Ssup⋎u α = TrCl⋎u α
⦏TrCl⋎u_ord⋎u_thm⦎ =
	⊢ ∀ α⦁ (∀ β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒ Ordinal⋎u (TrCl⋎u α)
=TEX

\ignore{
=SML
val Ssup⋎u_def = get_spec ⌜Ssup⋎u⌝;

set_goal ([], ⌜∀α⦁ (∀β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒ Ordinal⋎u (Ssup⋎u α)⌝);
a (REPEAT strip_tac);
a (rewrite_tac [(*get_spec ⌜Ordinal⋎u⌝, Transitive⋎u_def, *)get_spec ⌜Ssup⋎u⌝] THEN REPEAT strip_tac);
a (lemma_tac ⌜∀β⦁ β ∈⋎u Imagep⋎u Suc⋎u α ⇒ Ordinal⋎u β⌝);
(* *** Goal "1" *** *)
a (rewrite_tac[]);
a (REPEAT strip_tac);
a (asm_fc_tac []);
a (fc_tac [ord⋎u_suc⋎u_ord⋎u_thm]);
a (once_asm_rewrite_tac[]);
a strip_tac;
(* *** Goal "2" *** *)
a (fc_tac [ord⋎u_limit_thm]);
val Ssup⋎u_ord⋎u_thm = save_pop_thm "Ssup⋎u_ord⋎u_thm";

set_goal ([], ⌜∀α⦁ (∀β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒ (∀β⦁ β ∈⋎u α ⇒ β ∈⋎u (Ssup⋎u α))⌝);
a (REPEAT strip_tac);
a (rewrite_tac [get_spec ⌜Ssup⋎u⌝] THEN REPEAT strip_tac);
a (∃_tac ⌜Suc⋎u β⌝ THEN rewrite_tac [Suc⋎u_def]);
a (∃_tac ⌜β⌝ THEN asm_rewrite_tac [Suc⋎u_def]);
val Ssup⋎u_∈⋎u_thm = save_pop_thm "Ssup⋎u_∈⋎u_thm";

set_goal ([], ⌜∀α⦁ (∀β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒ (∀β⦁ β ∈⋎u α ⇒ β <⋎u (Ssup⋎u α))⌝);
a (REPEAT strip_tac);
a (rewrite_tac [get_spec ⌜$<⋎u⌝]
	THEN_TRY all_asm_fc_tac [Ssup⋎u_ord⋎u_thm, Ssup⋎u_∈⋎u_thm]
	THEN_TRY asm_rewrite_tac[]);
val Ssup⋎u_lt⋎u_thm = save_pop_thm "Ssup⋎u_lt⋎u_thm";

set_goal ([], ⌜∀α⦁ (∀β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒  α Sub⋎u (Ssup⋎u α)⌝);
a (rewrite_tac [get_spec ⌜$Sub⋎u⌝] THEN REPEAT strip_tac
	THEN_TRY all_asm_fc_tac [Ssup⋎u_lt⋎u_thm]);
val Ssup⋎u_⊆⋎u_thm = save_pop_thm "Ssup⋎u_⊆⋎u_thm";

set_goal([], ⌜∀α⦁ (∀β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒  Ssup⋎u α = TrCl⋎u α⌝);
a (REPEAT strip_tac);
a (LEMMA_T ⌜Set⋎u (Ssup⋎u α)⌝ asm_tac THEN1 rewrite_tac[Ssup⋎u_def]);
a (lemma_tac ⌜Set⋎u (TrCl⋎u α)⌝ THEN1 rewrite_tac[TrCl⋎u_def]);
a (ALL_ASM_UFC_⇔_T rewrite_tac [gsu_ext_axiom]);
a (rewrite_tac[Ssup⋎u_def, TrCl⋎u_def]);
a (REPEAT_N 4 strip_tac);
(* *** Goal "1" *** *)
a (var_elim_asm_tac ⌜e' = Suc⋎u e''⌝);
a (DROP_ASM_T ⌜e ∈⋎u Suc⋎u e''⌝ ante_tac
	THEN rewrite_tac [get_spec ⌜Suc⋎u⌝]
	THEN strip_tac
	THEN fc_tac [tc∈⋎u_incr_thm]
	THEN_TRY asm_rewrite_tac[]);
a (all_fc_tac [tc∈⋎u_trans_thm]); 
(* *** Goal "2" *** *)
a (cond_cases_tac ⌜e ∈⋎u α⌝);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜Suc⋎u e⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (all_fc_tac [tc∈⋎u_decomp_thm]);
a (lemma_tac ⌜e ∈⋎u Suc⋎u z⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.2.1" *** *)
a (lemma_tac ⌜Ordinal⋎u z⌝ THEN1 all_asm_fc_tac[]);
a (∨_left_tac THEN all_fc_tac [tc∈⋎u_ord⋎u_thm]);
(* *** Goal "2.2.2" *** *)
a (∃_tac ⌜Suc⋎u z⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
val Ssup⋎u_TrCl⋎u_thm = save_pop_thm "Ssup⋎u_TrCl⋎u_thm";

set_goal ([], ⌜∀α⦁ (∀β⦁ β ∈⋎u α ⇒ Ordinal⋎u β) ⇒ Ordinal⋎u (TrCl⋎u α)⌝);
a (REPEAT strip_tac);
a (ALL_FC_T (MAP_EVERY ante_tac) [Ssup⋎u_ord⋎u_thm]);
a (ALL_FC_T rewrite_tac [Ssup⋎u_TrCl⋎u_thm]);
val TrCl⋎u_ord⋎u_thm = save_pop_thm "TrCl⋎u_ord⋎u_thm";
=IGN
set_goal([], ⌜∀α⦁ (∀β⦁ β ∈⋎u α ⇒ Ordinal⋎u β)
	⇒ α Sub⋎u (Ssup⋎u α) ∧ ∀γ⦁ Ordinal⋎u γ ∧ α Sub⋎u γ ⇒ (Sup⋎u α) ≤⋎u γ⌝);
a (rewrite_tac (map get_spec [⌜$Sub⋎u⌝])
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (asm_fc_tac[]);
a (fc_tac[Ssup⋎u_ord⋎u_thm]);
a (fc_tac[]);
=TEX
}%ignore

I defined this ``strict supremum'' for use in defining the arithmetic operators over ordinals by transfinite recursion.
Later I realised that strict supremum is just the same as transitive closure if the operand is a set of ordinals, and decided that it would be nice to have a new form of the replacement principle, which resulted in the $ClIm$ function for defining operations over ordinals.
So I think now that strict supremum will prove to be redundant.

\subsection{Rank}

We define the rank of a set.

\subsubsection{The Consistency Proof}

This is a hangover from the days before I started to use automatic proofs based on recursion principles.

Before introducing the definition of rank we undertake the proof necessary to establish that the definition is conservative.
The key lemma in this proof is the proof that the relevant functional ``respects'' the membership relation.


=GFT
⦏respect⋎u_lemma⦎ =
	⊢ (λ f x⦁ ⋃⋎u (Imagep⋎u (Suc⋎u o f) x)) respects $∈⋎u
=TEX

\ignore{
=SML
set_goal([],⌜(λf⦁ λx⦁ ⋃⋎u (Imagep⋎u (Suc⋎u o f) x)) respects $∈⋎u⌝);
a (rewrite_tac [get_spec ⌜$respects⌝]
	THEN REPEAT strip_tac);
a (once_rewrite_tac [gsu_ext_conv ⌜⋃⋎u (Imagep⋎u (Suc⋎u o g) x) = ⋃⋎u (Imagep⋎u (Suc⋎u o h) x)⌝]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜e'⌝ THEN REPEAT strip_tac);
a (∃_tac ⌜e''⌝ THEN REPEAT strip_tac);
a (POP_ASM_T ante_tac
	THEN rewrite_tac[get_spec⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝]
	THEN strip_tac);
a (lemma_tac ⌜h e'' = g e''⌝
	THEN1 (REPEAT_N 2 (asm_fc_tac[tc_incr_thm])
		THEN asm_rewrite_tac[]));
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜e'⌝ THEN REPEAT strip_tac);
a (∃_tac ⌜e''⌝ THEN REPEAT strip_tac);
a (POP_ASM_T ante_tac
	THEN rewrite_tac[get_spec⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝]
	THEN strip_tac);
a (lemma_tac ⌜h e'' = g e''⌝
	THEN1 (REPEAT_N 2 (asm_fc_tac[tc_incr_thm])
		THEN asm_rewrite_tac[]));
a (asm_rewrite_tac[]);
val respect⋎u_lemma = pop_thm();
=TEX
}%ignore

Armed with that lemma we can now prove that the function which we will call ``rank'' exists (proof not shown).

\ignore{
=SML
set_goal([],⌜∃Rank⋎u⦁ ∀x⦁ Rank⋎u x = ⋃⋎u (Imagep⋎u (Suc⋎u o Rank⋎u) x)⌝);
a (∃_tac ⌜fix (λf⦁ λx⦁ ⋃⋎u (Imagep⋎u (Suc⋎u o f) x))⌝
	THEN strip_tac);
a (asm_tac gsu_wf_thm1);
a (asm_tac respect⋎u_lemma);
a (fc_tac [∀_elim ⌜λf⦁ λx⦁ ⋃⋎u (Imagep⋎u (Suc⋎u o f) x)⌝ (get_spec ⌜fix⌝)]);
a (asm_fc_tac []);
a (POP_ASM_T (rewrite_thm_tac o rewrite_rule [ext_thm]));
val _ = save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Rank⋎u⦎ : 'a GSU → 'a GSU
├────────────────────
│  ∀x⦁ Rank⋎u x = ⋃⋎u (Imagep⋎u (Suc⋎u o Rank⋎u) x)
■

\subsection{Ordinal Arithmetic}

Arithmetic operators are defined by transfinite induction.
Some machinery for this has already been provided, the principle tool being the operator \emph{ClIm} giving the transitive closure of the image of a set under a function.
In the inductive definitions the base case will be for the ordinal zero and will be given explicitly, the induction case will be obtained using \emph{ClIm} to obtain the closure of the set of values obtained by a function from the predecessors of the ordinal in question (i.e. its members).

If the function used in the definition is ``closure compatible'' (\emph{ClCo}) then an associative law for the operation can be obtained using general properties of the \emph{ClIm} operator.
It is therefore helpful to begin with some ordinal specific results about the \emph{ClIm} operator.

\subsubsection{Addition}

The difficulty of reasoning of course depends much upon the definition chosen.
I have tried more than one!

=SML
declare_infix (300, "+⋎u");
declare_infix (300, "--⋎u");
=TEX

\ignore{
=SML
CombI_prove_∃_rule "'gsu-rec3" ⌜∃$+⋎u:'a GSU → 'a GSU → 'a GSU⦁ ∀α β:'a GSU⦁ α +⋎u (CombI β)
	= if β =⋎u ∅⋎u then set⋎u α else ClIm⋎u ($+⋎u α) β⌝;
=TEX
}%ignore

ⓈHOLCONST
│ $⦏+⋎u⦎ : 'a GSU → 'a GSU → 'a GSU
├─────────────────
│  ∀α β⦁ α +⋎u β = if β =⋎u ∅⋎u then set⋎u α else ClIm⋎u ($+⋎u α) β
■

=GFT
⦏Set⋎u_plus⋎u_thm⦎ =
	⊢ ∀ α β⦁ Set⋎u (α +⋎u β)
⦏ord⋎u_set⋎u_thm⦎ =
	⊢ ∀ α⦁ Ordinal⋎u α ⇒ set⋎u α = α
⦏ord⋎u_eq⋎u_∅⋎u_thm⦎ =
	⊢ ∀ α⦁ Ordinal⋎u α ∧ α =⋎u ∅⋎u ⇒ α = ∅⋎u
⦏ord⋎u_plus⋎u_thm⦎ =
	⊢ ∀ α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ Ordinal⋎u (α +⋎u β)
⦏∅⋎u_plus⋎u_thm⦎ =
	⊢ ∀ α⦁ Ordinal⋎u α ⇒ ∅⋎u +⋎u α = α
⦏plus⋎u_∅⋎u_thm⦎ =
	⊢ ∀ α⦁ Set⋎u α ⇒ α +⋎u ∅⋎u = α
⦏plus⋎u_∅⋎u_thm2⦎ =
	⊢ ∀ α⦁ α +⋎u ∅⋎u =⋎u α
⦏plus⋎u_∅⋎u_thm3⦎ =
	⊢ ∀ α⦁ α +⋎u ∅⋎u = set⋎u α
⦏plus⋎u_∅⋎u_thm4⦎ =
	⊢ ∀ α⦁ Ordinal⋎u α ⇒ α +⋎u ∅⋎u = α
⦏plus⋎u_ur_thm⦎ =
	⊢ ∀ α x⦁ Set⋎u α ∧ x =⋎u ∅⋎u ⇒ α +⋎u x = α
⦏plus⋎u_ur_thm2⦎ =
	⊢ ∀ α x⦁ x =⋎u ∅⋎u ⇒ α +⋎u x =⋎u α
⦏plus⋎u_ur_thm3⦎ =
	⊢ ∀ α x⦁ x =⋎u ∅⋎u ⇒ α +⋎u x =⋎u set⋎u α
⦏ClCo⋎u_plus⋎u_thm⦎ =
	⊢ ∀ α⦁ ClCo⋎u ($+⋎u α)
⦏plus⋎u_eq_∅⋎u_thm⦎ =
	⊢ ∀ α β⦁ α +⋎u β =⋎u ∅⋎u ⇒ α =⋎u ∅⋎u ∧ β =⋎u ∅⋎u
⦏∈⋎u_ClIm⋎u_plus⋎u_thm⦎ =
	⊢ ∀ x α t⦁ Ordinal⋎u α ∧ Ordinal⋎u t ⇒
		(x ∈⋎u ClIm⋎u ($+⋎u α) t
		⇔ (∃ y⦁ y ∈⋎u t ∧ (x = α +⋎u y ∨ x ∈⋎u α +⋎u y)))
=TEX

\ignore{
=SML
val plus⋎u_def = get_spec ⌜$+⋎u⌝;

set_goal([], ⌜∀α β⦁ Set⋎u (α +⋎u β)⌝);
a (REPEAT strip_tac THEN rewrite_tac [plus⋎u_def, set⋎u_def]);
a (cond_cases_tac ⌜β =⋎u ∅⋎u⌝);
a (cond_cases_tac ⌜Set⋎u α⌝);
val Set⋎u_plus⋎u_thm = save_pop_thm "Set⋎u_plus⋎u_thm";

set_goal([], ⌜∀α⦁ Ordinal⋎u α ⇒ set⋎u α = α⌝);
a (REPEAT strip_tac THEN rewrite_tac [set⋎u_def]);
a (FC_T rewrite_tac [Set⋎u_ord⋎u_thm]);
val ord⋎u_set⋎u_thm = save_pop_thm "ord⋎u_set⋎u_thm";

set_goal([], ⌜∀α⦁ Ordinal⋎u α ∧ α =⋎u ∅⋎u ⇒ α = ∅⋎u⌝);
a (REPEAT strip_tac THEN fc_tac [Set⋎u_ord⋎u_thm] THEN gsu_ext_tac);
a (DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac [eq⋎u_ext_thm]);
val ord⋎u_eq⋎u_∅⋎u_thm = save_pop_thm "ord⋎u_eq⋎u_∅⋎u_thm";

set_goal ([], ⌜∀α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ Ordinal⋎u (α +⋎u β)⌝);
a (REPEAT ∀_tac);
a (wf_induction_tac gsu_wf_thm1 ⌜β⌝);
a (rewrite_tac [get_spec ⌜$+⋎u⌝]);
a (REPEAT strip_tac);
a (fc_tac [ord⋎u_set⋎u_thm]);
a (cases_tac ⌜t =⋎u ∅⋎u⌝ THEN asm_rewrite_tac[]);
a (REPEAT_N 2 (DROP_NTH_ASM_T 2 discard_tac));
a (lemma_tac ⌜∀γ⦁ Ordinal⋎u γ ∧ γ ∈⋎u t ⇒ Ordinal⋎u (α +⋎u γ)⌝);
(* *** Goal "1" *** *)
a (REPEAT strip_tac);
a (fc_tac [tc_incr_thm]);
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜∀ν⦁ ν ∈⋎u (Imagep⋎u ($+⋎u α) t) ⇒ Ordinal⋎u ν⌝);
(* *** Goal "2.1" *** *)
a (rewrite_tac []);
a (REPEAT strip_tac);
a (asm_rewrite_tac[]);
a (fc_tac[ord⋎u_∈⋎u_ord⋎u_thm]);
a (spec_nth_asm_tac 1 ⌜e⌝);
a (spec_nth_asm_tac 6 ⌜e⌝);
(* *** Goal "2.2" *** *)
a (fc_tac[TrCl⋎u_ord⋎u_thm]);
a (asm_rewrite_tac[ClIm⋎u_def]);
val ord⋎u_plus⋎u_thm = save_pop_thm "ord⋎u_plus⋎u_thm";

set_goal ([], ⌜∀α⦁ Set⋎u α ⇒ α +⋎u ∅⋎u = α⌝);
a (REPEAT strip_tac);
a (asm_rewrite_tac [get_spec ⌜$+⋎u⌝, set⋎u_def]);
val plus⋎u_∅⋎u_thm = save_pop_thm "plus⋎u_∅⋎u_thm";

set_goal ([], ⌜∀α⦁ α +⋎u ∅⋎u =⋎u α⌝);
a (REPEAT strip_tac);
a (rewrite_tac [get_spec ⌜$+⋎u⌝, set⋎u_def, get_spec ⌜$=⋎u⌝, sets_ext_clauses, get_spec ⌜X⋎u⌝]
	THEN PC_T1 "hol1" rewrite_tac[] THEN strip_tac);
a (cond_cases_tac ⌜Set⋎u α⌝ THEN swap_nth_asm_concl_tac 1);
a (FC_T rewrite_tac [Set⋎u_axiom]);
val plus⋎u_∅⋎u_thm2 = save_pop_thm "plus⋎u_∅⋎u_thm2";

set_goal ([], ⌜∀α x⦁ Set⋎u α ∧ x =⋎u ∅⋎u ⇒ α +⋎u x = α⌝);
a (REPEAT strip_tac THEN asm_rewrite_tac [get_spec ⌜$+⋎u⌝, set⋎u_def]);
val plus⋎u_ur_thm = save_pop_thm "plus⋎u_ur_thm";

set_goal ([], ⌜∀α x⦁ x =⋎u ∅⋎u ⇒ α +⋎u x =⋎u α⌝);
a (REPEAT strip_tac THEN asm_rewrite_tac [get_spec ⌜$+⋎u⌝, set⋎u_def]);
a (cond_cases_tac ⌜Set⋎u α⌝);
a (PC_T1 "hol1" rewrite_tac [get_spec ⌜$=⋎u⌝, sets_ext_clauses, get_spec ⌜X⋎u⌝]);
a (swap_nth_asm_concl_tac 1);
a (fc_tac [Set⋎u_axiom]);
val plus⋎u_ur_thm2 = save_pop_thm "plus⋎u_ur_thm2";

set_goal ([], ⌜∀α x⦁ x =⋎u ∅⋎u ⇒ α +⋎u x = set⋎u α⌝);
a (REPEAT strip_tac THEN asm_rewrite_tac [get_spec ⌜$+⋎u⌝, set⋎u_def]);
val plus⋎u_ur_thm3 = save_pop_thm "plus⋎u_ur_thm3";

set_goal ([], ⌜∀α⦁ α +⋎u ∅⋎u = set⋎u α⌝);
a (∀_tac);
a (accept_tac (rewrite_rule [] (list_∀_elim [⌜α⌝, ⌜∅⋎u⌝] plus⋎u_ur_thm3)));
val plus⋎u_∅⋎u_thm3 = save_pop_thm "plus⋎u_∅⋎u_thm3";

set_goal ([], ⌜∀α⦁ Ordinal⋎u α ⇒ α +⋎u ∅⋎u = α⌝);
a (REPEAT strip_tac);
a (all_fc_tac [Set⋎u_ord⋎u_thm]);
a (all_fc_tac [plus⋎u_∅⋎u_thm]);
val plus⋎u_∅⋎u_thm4 = save_pop_thm "plus⋎u_∅⋎u_thm4";

set_goal ([], ⌜∀x⦁ ¬ x =⋎u ∅⋎u ⇒ set⋎u x = x⌝);
a (strip_tac THEN rewrite_tac [eq⋎u_ext_thm] THEN strip_tac);
a (fc_tac [Set⋎u_axiom]);
a (fc_tac [set⋎u_fc_thm]);
val ne⋎u_∅⋎u_set⋎u_thm = save_pop_thm "ne⋎u_∅⋎u_set⋎u_thm";

set_goal ([], ⌜∀α:'a GSU⦁ Ordinal⋎u α ⇒ ∅⋎u +⋎u α = α⌝);
a (strip_tac);
a (wf_induction_tac gsu_wf_thm1 ⌜α⌝);
a (rewrite_tac [get_spec ⌜$+⋎u⌝]);
a (cond_cases_tac ⌜t =⋎u ∅⋎u⌝
	THEN1 (strip_tac THEN ALL_FC_T rewrite_tac [ord⋎u_eq_∅⋎u_thm] THEN rewrite_tac [set⋎u_def]));
a (strip_tac THEN fc_tac [Set⋎u_ord⋎u_thm]);
a (lemma_tac ⌜Set⋎u(ClIm⋎u ($+⋎u ∅⋎u) t)⌝ THEN1 rewrite_tac [Set⋎u_ClIm⋎u_thm]);
a (gsu_ext_tac THEN rewrite_tac[]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜Ordinal⋎u y⌝ THEN1 all_fc_tac []);
(* *** Goal "1.1" *** *)
a (all_asm_fc_tac[ord⋎u_∈⋎u_ord⋎u_thm]);
(* *** Goal "1.2" *** *)
a (lemma_tac ⌜∅⋎u +⋎u y = y⌝ THEN1 all_asm_fc_tac []);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜Ordinal⋎u y⌝ THEN1 all_fc_tac[ord⋎u_∈⋎u_ord⋎u_thm]);
a (lemma_tac ⌜∅⋎u +⋎u y = y⌝ THEN1 all_asm_fc_tac []);
a (lemma_tac ⌜e ∈⋎u ∅⋎u +⋎u y⌝);
(* *** Goal "2.1" *** *)
a (lemma_tac ⌜Transitive⋎u y⌝ THEN1 fc_tac [get_spec ⌜Ordinal⋎u⌝]);
a (lemma_tac ⌜Set⋎u y⌝ THEN1 fc_tac [Set⋎u_ord⋎u_thm]);
a (DROP_NTH_ASM_T 5 (asm_tac o (rewrite_rule [asm_rule⌜∅⋎u +⋎u y = y⌝])));
a (all_fc_tac [Tran_set_tc∈⋎u_thm]);
a (asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (POP_ASM_T (asm_tac o (rewrite_rule [asm_rule⌜∅⋎u +⋎u y = y⌝])));
a (lemma_tac ⌜Transitive⋎u t⌝ THEN1 fc_tac [get_spec ⌜Ordinal⋎u⌝]);
a (fc_tac [Transitive⋎u_def]);
a (LEMMA_T ⌜y ⊆⋎u t⌝ ante_tac THEN1 asm_fc_tac[]);
a (rewrite_tac [get_spec ⌜$⊆⋎u⌝] THEN strip_tac THEN asm_fc_tac[]);
(* *** Goal "3" *** *)
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
a (LEMMA_T ⌜∅⋎u +⋎u e = e⌝ rewrite_thm_tac);
a (lemma_tac ⌜Ordinal⋎u e⌝ THEN1 all_fc_tac[ord⋎u_∈⋎u_ord⋎u_thm]);
a (all_asm_fc_tac[]);
val ∅⋎u_plus⋎u_thm = save_pop_thm "∅⋎u_plus⋎u_thm";

set_goal([], ⌜∀α⦁ ClCo⋎u($+⋎u α)⌝);
a (strip_tac);
a (rewrite_tac[ClCo⋎u_def, plus⋎u_def]);
a (lemma_tac ⌜∀ y x
           ⦁ x ∈⋎u⋏+ y
               ⇒ (if x =⋎u ∅⋎u then set⋎u α else ClIm⋎u ($+⋎u α) x)
                 ∈⋎u⋏+ (if y =⋎u ∅⋎u then set⋎u α else ClIm⋎u ($+⋎u α) y)⌝
	THEN_LIST [strip_tac, REPEAT ∀_tac THEN pure_asm_rewrite_tac[]]);
a (gsu_induction_tac2 ⌜y⌝ THEN REPEAT strip_tac);
a (cond_cases_tac ⌜x =⋎u ∅⋎u⌝);
(* *** Goal "1" *** *)
a (cond_cases_tac ⌜t =⋎u ∅⋎u⌝);
(* *** Goal "1.1" *** *)
a (fc_tac [eq_∅⋎u_¬∈⋎u_thm]);
a (fc_tac [tc∈⋎u_decomp_thm] THEN asm_ufc_tac[]);
(* *** Goal "1.2" *** *)
a (fc_tac [tc∈⋎u_decomp_thm]);
(* *** Goal "1.2.1" *** *)
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
a (∨_left_tac THEN FC_T rewrite_tac [plus⋎u_ur_thm3]);
(* *** Goal "1.2.2" *** *)
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
a (REPEAT strip_tac);
a (rewrite_tac[plus⋎u_def]);
a (lemma_tac ⌜z ∈⋎u⋏+ t⌝ THEN1 fc_tac [tc∈⋎u_incr_thm]);
a (spec_nth_asm_tac 8 ⌜z⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (LEMMA_T ⌜¬ t =⋎u ∅⋎u⌝ rewrite_thm_tac);
(* *** Goal "2.1" *** *)
a (swap_nth_asm_concl_tac 1 THEN fc_tac [eq_∅⋎u_¬tc∈⋎u_thm]);
a (asm_ufc_tac[]);
(* *** Goal "2.2" *** *)
a (fc_tac [tc∈⋎u_decomp_thm]);
(* *** Goal "2.2.1" *** *)
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
a (∨_left_tac THEN asm_rewrite_tac [plus⋎u_def]);
(* *** Goal "2.2.2" *** *)
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
a (∨_right_tac THEN asm_rewrite_tac [plus⋎u_def]);
a (fc_tac [tc∈⋎u_incr_thm]);  
a (spec_nth_asm_tac 6 ⌜z⌝);
a (SPEC_NTH_ASM_T 1 ⌜x⌝ (strip_asm_tac o (rewrite_rule[asm_rule ⌜¬ x =⋎u ∅⋎u⌝])));
val ClCo⋎u_plus⋎u_thm = save_pop_thm "ClCo⋎u_plus⋎u_thm";

set_goal([], ⌜∀α β⦁ α +⋎u β =⋎u ∅⋎u ⇒ α =⋎u ∅⋎u ∧ β =⋎u ∅⋎u⌝);
a (REPEAT ∀_tac THEN rewrite_tac [plus⋎u_def]);
a (cond_cases_tac ⌜β =⋎u ∅⋎u⌝);
a (POP_ASM_T ante_tac);
(* *** Goal "1" *** *)
a (rewrite_tac [eq⋎u_ext_thm]);
(* *** Goal "2" *** *)
a (rewrite_tac [eq⋎u_ext_thm]);
a (REPEAT strip_tac);
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac [eq⋎u_ext_thm] THEN strip_tac);
a (spec_nth_asm_tac 1 ⌜α +⋎u u⌝);
a (spec_nth_asm_tac 1 ⌜u⌝);
val plus⋎u_eq_∅⋎u_thm = save_pop_thm "plus⋎u_eq_∅⋎u_thm";

set_goal([], ⌜∀(x:'a GSU) α t⦁ Ordinal⋎u α ∧ Ordinal⋎u t ⇒ (x ∈⋎u ClIm⋎u ($+⋎u α) t
		⇔ ∃ y⦁ y ∈⋎u t ∧ (x = α +⋎u y ∨ x ∈⋎u α +⋎u y))⌝);
a (REPEAT ∀_tac THEN rewrite_tac[]
	THEN REPEAT strip_tac
	THEN_TRY (∃_tac ⌜y⌝ THEN_TRY asm_rewrite_tac[])
);
(* *** Goal "1" *** *)
a (lemma_tac ⌜Ordinal⋎u y⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (lemma_tac ⌜Ordinal⋎u (α +⋎u y)⌝ THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
a (ALL_FC_T rewrite_tac [tc∈⋎u_ord⋎u_thm]);
(* *** Goal "2" *** *)
a (ALL_FC_T rewrite_tac [tc∈⋎u_incr_thm]);
val ∈⋎u_ClIm⋎u_plus⋎u_thm = save_pop_thm "∈⋎u_ClIm⋎u_plus⋎u_thm";

=TEX
}%ignore


\subsubsection{Another Experiment}

The number of ``cases'' of course makes a big difference to the complexity of proofs.
I pondered for a while about whether the conditional on emptyness of one operand in my definition of addition could be eliminated, and eventually came up with a scheme.

Rather than reworking lots of material with a new definition, I think it will be easy to prove the new definition equivalent to the old, so that I get to use either.

However, only a qualified equality is obtainable, which is not quite as simple to apply.

=GFT
⦏plus⋎u_def_thm⦎ =
   ⊢ ∀ α β⦁ Ordinal⋎u β ⇒ α +⋎u β = α ∪⋎u ClIm⋎u ($+⋎u α) β
=TEX

This does reduce the number of explicit case splits, but the union results in automatic case splits, and the associativity proof still has 10 cases.
Nevertheless, it does seem to be significantly easier using this characterisation of addition.

\ignore{
=SML
set_goal([], ⌜∀α β⦁ Ordinal⋎u β ⇒ α +⋎u β = α ∪⋎u ClIm⋎u ($+⋎u α) β⌝);
a (REPEAT strip_tac THEN rewrite_tac [plus⋎u_def]);
a (cond_cases_tac ⌜β =⋎u ∅⋎u⌝);
(* *** Goal "1" *** *)
a (ALL_FC_T rewrite_tac [ord⋎u_eq_∅⋎u_thm]);
a (rewrite_tac[∪⋎u_∅⋎u_set⋎u_thm]);
(* *** Goal "2" *** *)
a (gsu_ext_tac);
a (strip_tac THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.3" *** *)
a (all_fc_tac [∅⋎u_neq⋎u_∈⋎u_thm]);
a (∃_tac ⌜∅⋎u⌝ THEN asm_rewrite_tac[]);
a (rewrite_tac [plus⋎u_∅⋎u_thm3]);
a (lemma_tac ⌜e ∈⋎u set⋎u α⌝ THEN1 (rewrite_tac [set⋎u_def] THEN strip_tac));
a (ALL_FC_T rewrite_tac [tc∈⋎u_incr_thm]);
(* *** Goal "2.4" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.5" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
val plus⋎u_def_thm = save_pop_thm "plus⋎u_def_thm";
=TEX
}%ignore

The problem with this characterisation is that it does not come out very nicely if you use it in an extensional proof.
It expands into the use of both membership and the transitive closure of membership, both of which in the present context are really just the ordering relation on the ordinals.

Since we have an extensionality principle expressed in terms of the ordering on the ordinals, it might be useful to have an extensional characterisation of addition in the same spirit.

To achieve this it is desirable to define the property of (HOL) functions over sets that they map ordinals to ordinals.


ⓈHOLCONST
│ $⦏OrdMap⋎u⦎ : ('a GSU → 'a GSU) → BOOL
├─────────────────
│  ∀f⦁ OrdMap⋎u f ⇔ ∀α⦁ Ordinal⋎u α ⇒ Ordinal⋎u (f α)
■

We can then prove the following sufficient conditions for $ClIm⋎u$ to deliver an ordinal:

=GFT
⦏ClIm⋎u_ord⋎u_thm⦎ =
	⊢ ∀ f α⦁ OrdMap⋎u f ∧ Ordinal⋎u α ⇒ Ordinal⋎u (ClIm⋎u f α)
=TEX

The required characterisaton of $ClIm⋎u$ in terms of the ordering is then:

=GFT
⦏lt⋎u_ClIm⋎u_thm⦎ =
	⊢ ∀ α f β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ∧ OrdMap⋎u f
		⇒ (α <⋎u ClIm⋎u f β ⇔ (∃ δ⦁ δ <⋎u β ∧ α ≤⋎u f δ))
=TEX

\ignore{
=SML
val OrdMap⋎u_def = get_spec ⌜OrdMap⋎u⌝;

set_goal([], ⌜∀f α⦁ OrdMap⋎u f ∧ Ordinal⋎u α ⇒ Ordinal⋎u (ClIm⋎u f α)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [OrdMap⋎u_def, ClIm⋎u_def]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜∀β⦁ β ∈⋎u Imagep⋎u f α ⇒ Ordinal⋎u β⌝
	THEN1 REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜Ordinal⋎u e⌝ THEN1 all_asm_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (all_asm_fc_tac[] THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac [TrCl⋎u_ord⋎u_thm]);
val ClIm⋎u_ord⋎u_thm = save_pop_thm "ClIm⋎u_ord⋎u_thm";

set_goal([], ⌜∀α f β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ∧ OrdMap⋎u f ⇒
	(α <⋎u ClIm⋎u f β ⇔ ∃δ⦁ δ <⋎u β ∧ α ≤⋎u f δ)⌝);
a (REPEAT_N 3 strip_tac
	THEN_TRY asm_rewrite_tac[get_spec ⌜$<⋎u⌝, get_spec ⌜$≤⋎u⌝, ∈⋎u_ClIm⋎u_thm]);
a (strip_tac THEN fc_tac [OrdMap⋎u_def]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
a (all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm] THEN asm_fc_tac[] THEN contr_tac);
(* *** Goal "2" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
a (all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm] THEN asm_fc_tac[] THEN asm_rewrite_tac[]);
a (lemma_tac ⌜Transitive⋎u (f y)⌝ THEN1 all_fc_tac [ord⋎u_def]);
a (ALL_FC_T rewrite_tac [Tran_tc∈⋎u_thm]);
(* *** Goal "3" *** *)
a (all_fc_tac [ClIm⋎u_ord⋎u_thm]);
(* *** Goal "4" *** *)
a (all_fc_tac [tc∈⋎u_incr_thm]);
a (∃_tac ⌜δ⌝ THEN asm_rewrite_tac[]);
(* *** Goal "5" *** *)
a (all_fc_tac [ClIm⋎u_ord⋎u_thm]);
(* *** Goal "6" *** *)
a (all_fc_tac [tc∈⋎u_incr_thm]);
a (∃_tac ⌜δ⌝ THEN asm_rewrite_tac[]);
val lt⋎u_ClIm⋎u_thm = save_pop_thm "lt⋎u_ClIm⋎u_thm";
=TEX
}%ignore

Here are some examples of $OrdMap$s.

=GFT
⦏OrdMap⋎u_plus⋎u_thm⦎ = ⊢ ∀ α⦁ Ordinal⋎u α ⇒ OrdMap⋎u ($+⋎u α)
=TEX

A further characterisation of ordinal addition in terms of the ordering relation is then obtained.
This is a further candidate for the definition.
If it could be used as the definition there would be a saving in proof effort, so some consideration of whether this pattern of definition is more generally useful and could be supported by automatic consistency proof might be a good idea.

=GFT
⦏plus⋎u_def_thm2⦎ =
	⊢ ∀ β α γ⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒
		(γ <⋎u α +⋎u β ⇔ γ <⋎u α ∨ (∃ δ⦁ δ <⋎u β ∧ γ = α +⋎u δ))
=TEX


\ignore{
=SML
set_goal([], ⌜∀α⦁ Ordinal⋎u α ⇒ OrdMap⋎u ($+⋎u α)⌝);
a (REPEAT strip_tac THEN rewrite_tac [OrdMap⋎u_def]
	THEN REPEAT strip_tac);
a (ALL_FC_T rewrite_tac [ord⋎u_plus⋎u_thm]);
val OrdMap⋎u_plus⋎u_thm = save_pop_thm "OrdMap⋎u_plus⋎u_thm";

set_goal([], ⌜∀β α γ⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒
	(γ <⋎u α +⋎u β ⇔ γ <⋎u α ∨ ∃δ⦁ δ <⋎u β ∧ γ = α +⋎u δ)⌝);
a (∀_tac);
a (ordinal_induction_tac ⌜β⌝);
a (REPEAT_N 3 strip_tac THEN_TRY asm_rewrite_tac[get_spec ⌜$+⋎u⌝]);
a (lemma_tac ⌜Ordinal⋎u (α +⋎u t)⌝ THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
a (cond_cases_tac ⌜t =⋎u ∅⋎u⌝);
(* *** Goal "1" *** *)
a (REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (DROP_ASM_T ⌜γ <⋎u set⋎u α⌝ ante_tac);
a (lemma_tac ⌜Set⋎u α⌝ THEN1 all_fc_tac [Set⋎u_ord⋎u_thm]); 
a (FC_T asm_rewrite_tac [set⋎u_fc_thm]);
(* *** Goal "1.2" *** *)
a (DROP_ASM_T ⌜γ <⋎u α⌝ ante_tac);
a (lemma_tac ⌜Set⋎u α⌝ THEN1 all_fc_tac [Set⋎u_ord⋎u_thm]); 
a (FC_T asm_rewrite_tac [set⋎u_fc_thm]);
(* *** Goal "1.3" *** *)
a (DROP_ASM_T ⌜δ <⋎u t⌝ ante_tac);
a (all_fc_tac [eq_∅⋎u_¬∈⋎u_thm]);
a (asm_rewrite_tac[get_spec ⌜$<⋎u⌝]);
(* *** Goal "2" *** *)
a (REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (DROP_ASM_T ⌜γ <⋎u ClIm⋎u ($+⋎u α) t⌝
	(strip_asm_tac o (rewrite_rule[get_spec ⌜$<⋎u⌝])));
(* *** Goal "2.1.1" *** *)
a (lemma_tac ⌜Ordinal⋎u y⌝ THEN1 all_asm_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac [get_spec ⌜$<⋎u⌝]);
a (cond_cases_tac ⌜y =⋎u ∅⋎u⌝);
(* *** Goal "2.1.1.1" *** *)
a (lemma_tac ⌜Set⋎u y⌝ THEN1 all_asm_fc_tac [Set⋎u_ord⋎u_thm]);
a (LEMMA_T ⌜y = ∅⋎u⌝ rewrite_thm_tac THEN1 all_fc_tac [eq⋎u_eq_∅⋎u_thm]);
a (rewrite_tac [plus⋎u_∅⋎u_thm3]);
(* *** Goal "2.1.1.2" *** *)
a (lemma_tac ⌜Ordinal⋎u (α +⋎u y)⌝ THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
a (lemma_tac ⌜Set⋎u (α +⋎u y)⌝ THEN1 all_fc_tac [Set⋎u_ord⋎u_thm]);
a (gsu_ext_tac THEN REPEAT strip_tac);
(* *** Goal "2.1.1.2.1" *** *)
a (POP_ASM_T (strip_asm_tac o
	(rewrite_rule (fc_rule [plus⋎u_def_thm] [asm_rule ⌜Ordinal⋎u y⌝]))));
(* *** Goal "2.1.1.2.1.1" *** *)
a (lemma_tac ⌜∅⋎u ∈⋎u y⌝ THEN1 all_fc_tac [∅⋎u_neq⋎u_∈⋎u_thm]);
a (∃_tac ⌜∅⋎u⌝ THEN asm_rewrite_tac[]);
a (ALL_FC_T rewrite_tac [plus⋎u_∅⋎u_thm4]);
a (ALL_FC_T rewrite_tac [tc∈⋎u_incr_thm]);
(* *** Goal "2.1.1.2.1.2" *** *)
a (∃_tac ⌜y'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.1.2.1.3" *** *)
a (∃_tac ⌜y'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.1.2.2" *** *)
a (POP_ASM_T ante_tac
	THEN ALL_FC_T asm_rewrite_tac [plus⋎u_def_thm]
	THEN REPEAT strip_tac);
(* *** Goal "2.1.1.2.2.1" *** *)
a (∃_tac ⌜y'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.1.2.2.2" *** *)
a (∃_tac ⌜y'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.1.2" *** *)
a (lemma_tac ⌜Ordinal⋎u y⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (lemma_tac ⌜y <⋎u t⌝ THEN1 asm_rewrite_tac [get_spec ⌜$<⋎u⌝]);
a (spec_nth_asm_tac 12 ⌜y⌝);
a (lemma_tac ⌜Ordinal⋎u (α +⋎u y)⌝ THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
a (lemma_tac ⌜γ <⋎u α +⋎u y⌝
	THEN1 (all_fc_tac [tc∈⋎u_ord⋎u_thm]
		THEN asm_rewrite_tac[get_spec ⌜$<⋎u⌝]));
a (list_spec_nth_asm_tac 3 [⌜α⌝, ⌜γ⌝]);
(* *** Goal "2.1.2.1" *** *)
a (asm_fc_tac[]);
(* *** Goal "2.1.2.2" *** *)
a (lemma_tac ⌜δ <⋎u t⌝ THEN1 all_fc_tac [lt⋎u_trans_thm]);
a (∃_tac ⌜δ⌝ THEN asm_rewrite_tac[]);
a (cond_cases_tac ⌜δ =⋎u ∅⋎u⌝);
(* *** Goal "2.1.2.2.1" *** *)
a (ALL_FC_T rewrite_tac [plus⋎u_ur_thm3]);
(* *** Goal "2.1.2.2.2" *** *)
a (lemma_tac ⌜Ordinal⋎u δ⌝ THEN1 all_fc_tac [get_spec ⌜$<⋎u⌝]);
a (lemma_tac ⌜Ordinal⋎u (α +⋎u δ)⌝ THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
a (lemma_tac ⌜Set⋎u (α +⋎u δ)⌝ THEN1 all_fc_tac [Set⋎u_ord⋎u_thm]);
a (gsu_ext_tac THEN FC_T rewrite_tac [plus⋎u_def_thm] THEN REPEAT strip_tac);
(* *** Goal "2.1.2.2.2.1" *** *)
a (lemma_tac ⌜∅⋎u ∈⋎u δ⌝ THEN1 all_fc_tac [∅⋎u_neq⋎u_∈⋎u_thm]);
a (lemma_tac ⌜Set⋎u α⌝ THEN1 all_fc_tac [Set⋎u_ord⋎u_thm]);
a (∃_tac ⌜∅⋎u⌝ THEN ALL_FC_T asm_rewrite_tac [plus⋎u_∅⋎u_thm]);
a (ALL_FC_T rewrite_tac[tc∈⋎u_incr_thm]);
(* *** Goal "2.1.2.2.2.2" *** *)
a (∃_tac ⌜y'⌝ THEN asm_rewrite_tac []);
(* *** Goal "2.1.2.2.2.3" *** *)
a (∃_tac ⌜y'⌝ THEN asm_rewrite_tac []);
(* *** Goal "2.1.2.2.2.4" *** *)
a (∃_tac ⌜y'⌝ THEN asm_rewrite_tac []);
(* *** Goal "2.1.2.2.2.5" *** *)
a (∃_tac ⌜y'⌝ THEN asm_rewrite_tac []);
(* *** Goal "2.2" *** *)
a (POP_ASM_T ante_tac
	THEN asm_rewrite_tac [get_spec ⌜$<⋎u⌝, ∈⋎u_ClIm⋎u_plus⋎u_thm]
	THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a (lemma_tac ⌜∀φ⦁ φ ∈⋎u ClIm⋎u ($+⋎u α) t ⇒ Ordinal⋎u φ⌝
	THEN1 (REPEAT ∀_tac THEN asm_rewrite_tac[] THEN REPEAT strip_tac));
(* *** Goal "2.2.1.1" *** *)
a (lemma_tac ⌜Ordinal⋎u y⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (asm_rewrite_tac[] THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
(* *** Goal "2.2.1.2" *** *)
a (lemma_tac ⌜Ordinal⋎u y⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (lemma_tac ⌜Ordinal⋎u (α +⋎u y)⌝ THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
a (lemma_tac ⌜φ ∈⋎u α +⋎u y⌝ THEN1 all_fc_tac [tc∈⋎u_ord⋎u_thm]);
a (lemma_tac ⌜Ordinal⋎u φ⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
(* *** Goal "2.2.1.3" *** *)
a (lemma_tac ⌜OrdMap⋎u ($+⋎u α)⌝ THEN1 asm_fc_tac [OrdMap⋎u_plus⋎u_thm]);
a (all_fc_tac [ClIm⋎u_ord⋎u_thm]);
(* *** Goal "2.2.2" *** *)
a (lemma_tac ⌜∅⋎u ∈⋎u t⌝ THEN1 all_fc_tac [∅⋎u_neq⋎u_∈⋎u_thm]);
a (∃_tac ⌜∅⋎u⌝ THEN ALL_FC_T asm_rewrite_tac [plus⋎u_∅⋎u_thm4]);
a (ALL_FC_T rewrite_tac [tc∈⋎u_incr_thm]);
(* *** Goal "2.3" *** *)
a (POP_ASM_T ante_tac
	THEN asm_rewrite_tac [get_spec ⌜$<⋎u⌝, ∈⋎u_ClIm⋎u_plus⋎u_thm]
	THEN REPEAT strip_tac);
(* *** Goal "2.3.1" *** *)
a (asm_rewrite_tac[]);
a (cond_cases_tac ⌜δ =⋎u ∅⋎u⌝);
(* *** Goal "2.3.1.1" *** *)
a (ALL_FC_T asm_rewrite_tac [ord⋎u_set⋎u_thm]);
(* *** Goal "2.3.1.2" *** *)
a (lemma_tac ⌜∀φ⦁ φ ∈⋎u ClIm⋎u ($+⋎u α) δ ⇒ Ordinal⋎u φ⌝
	THEN1 (REPEAT ∀_tac THEN asm_rewrite_tac[] THEN REPEAT strip_tac));
(* *** Goal "2.3.1.2.1" *** *)
a (lemma_tac ⌜Ordinal⋎u δ⌝ THEN1 all_fc_tac [get_spec ⌜$<⋎u⌝]);
a (lemma_tac ⌜Ordinal⋎u y⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (asm_rewrite_tac[] THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
(* *** Goal "2.3.1.2.2" *** *)
a (lemma_tac ⌜Ordinal⋎u δ⌝ THEN1 all_fc_tac [get_spec ⌜$<⋎u⌝]);
a (lemma_tac ⌜Ordinal⋎u y⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (lemma_tac ⌜Ordinal⋎u (α +⋎u y)⌝ THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
a (lemma_tac ⌜φ ∈⋎u α +⋎u y⌝ THEN1 all_fc_tac [tc∈⋎u_ord⋎u_thm]);
a (lemma_tac ⌜Ordinal⋎u φ⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
(* *** Goal "2.3.1.2.3" *** *)
a (lemma_tac ⌜Ordinal⋎u δ⌝ THEN1 all_fc_tac [get_spec ⌜$<⋎u⌝]);
a (lemma_tac ⌜OrdMap⋎u ($+⋎u α)⌝ THEN1 asm_fc_tac [OrdMap⋎u_plus⋎u_thm]);
a (all_fc_tac [ClIm⋎u_ord⋎u_thm]);
(* *** Goal "2.3.2" *** *)
a (lemma_tac ⌜∀φ⦁ φ ∈⋎u ClIm⋎u ($+⋎u α) t ⇒ Ordinal⋎u φ⌝
	THEN1 (REPEAT ∀_tac THEN asm_rewrite_tac[] THEN REPEAT strip_tac));
(* *** Goal "2.3.2.1" *** *)
a (lemma_tac ⌜Ordinal⋎u y⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (asm_rewrite_tac[] THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
(* *** Goal "2.3.2.2" *** *)
a (lemma_tac ⌜Ordinal⋎u y⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (lemma_tac ⌜Ordinal⋎u (α +⋎u y)⌝ THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
a (lemma_tac ⌜φ ∈⋎u α +⋎u y⌝ THEN1 all_fc_tac [tc∈⋎u_ord⋎u_thm]);
a (lemma_tac ⌜Ordinal⋎u φ⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
(* *** Goal "2.3.2.3" *** *)
a (lemma_tac ⌜OrdMap⋎u ($+⋎u α)⌝ THEN1 asm_fc_tac [OrdMap⋎u_plus⋎u_thm]);
a (all_fc_tac [ClIm⋎u_ord⋎u_thm]);
(* *** Goal "2.3.3" *** *)
a (∃_tac ⌜δ⌝ THEN asm_rewrite_tac []);
a (ALL_FC_T rewrite_tac [get_spec ⌜$<⋎u⌝]);
a (cond_cases_tac ⌜δ =⋎u ∅⋎u⌝);
(* *** Goal "2.3.3.1" *** *)
a (lemma_tac ⌜Ordinal⋎u δ⌝ THEN1 all_fc_tac [get_spec ⌜$<⋎u⌝]);
a (all_fc_tac [ord⋎u_eq⋎u_∅⋎u_thm]);
a (var_elim_asm_tac ⌜δ = ∅⋎u⌝);
a (ALL_FC_T asm_rewrite_tac [plus⋎u_∅⋎u_thm4]);
a (ALL_FC_T rewrite_tac [ord⋎u_set⋎u_thm]);
(* *** Goal "2.3.3.2" *** *)
a (∨_left_tac);
a (asm_rewrite_tac [plus⋎u_def]);
val plus⋎u_def_thm2 = save_pop_thm "plus⋎u_def_thm2";
=TEX
}%ignore

=GFT
⦏plus⋎u_Suc⋎u_thm⦎ =
	⊢ ∀ α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ α +⋎u Suc⋎u β = Suc⋎u (α +⋎u β)
=TEX

\ignore{
=SML
set_goal([], ⌜∀α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ α +⋎u Suc⋎u β = Suc⋎u (α +⋎u β)⌝);
a (REPEAT ∀_tac);
a (ordinal_induction_tac ⌜β⌝ THEN REPEAT strip_tac);
a (lemma_tac ⌜Ordinal⋎u (Suc⋎u t)⌝ THEN1 all_fc_tac [ord⋎u_suc⋎u_ord⋎u_thm]);
a (FC_T rewrite_tac[plus⋎u_def_thm]);
a (gsu_ext_tac THEN REPEAT_N 3 strip_tac THEN_TRY asm_rewrite_tac[]
	THEN_TRY strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (∨_left_tac THEN ∨_right_tac);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∨_left_tac THEN ∨_right_tac);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (∨_right_tac);
a (FC_T rewrite_tac [plus⋎u_def_thm]);
(* *** Goal "4" *** *)
a (∨_left_tac);
a (var_elim_asm_tac ⌜y = t⌝);
a (cond_cases_tac ⌜t = ∅⋎u⌝);
(* *** Goal "4.1" *** *)
a (var_elim_asm_tac ⌜t = ∅⋎u⌝);
a (POP_ASM_T ante_tac);
a (lemma_tac ⌜Set⋎u α⌝ THEN1 all_fc_tac [Set⋎u_ord⋎u_thm]);
a (FC_T rewrite_tac [plus⋎u_∅⋎u_thm] THEN strip_tac);
a (all_fc_tac [tc∈⋎u_ord⋎u_thm]);
(* *** Goal "4.2" *** *)
a (∨_right_tac);
a (DROP_ASM_T ⌜e ∈⋎u⋏+ α +⋎u t⌝ ante_tac);
a (FC_T rewrite_tac[plus⋎u_def_thm] THEN strip_tac);
(* *** Goal "4.2.1" *** *)
a (all_fc_tac [∅⋎u_neq_∈⋎u_thm]);
a (∃_tac ⌜∅⋎u⌝ THEN asm_rewrite_tac[]);
a (∨_right_tac);
a (FC_T rewrite_tac [plus⋎u_∅⋎u_thm4] THEN strip_tac);
(* *** Goal "4.2.2" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "4.2.3" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "5" *** *)
a (∨_right_tac);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "6" *** *)
a (∨_right_tac);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "7" *** *)
a (∨_right_tac);
a (∃_tac ⌜t⌝ THEN asm_rewrite_tac[]);
a (∨_left_tac);
a (FC_T rewrite_tac[plus⋎u_def_thm] THEN strip_tac);
val plus⋎u_Suc⋎u_thm = save_pop_thm "plus⋎u_Suc⋎u_thm";
=TEX
}%ignore

This extensionality principle suggests a style of proof based on these inequalities, so it is useful to have more results about inequalities.

=GFT
⦏plus⋎u_mono_right_thm⦎ =
	⊢ ∀ α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ α ≤⋎u α +⋎u β
⦏plus⋎u_mono_right_thm2⦎ =
	⊢ ∀ α β γ⦁ Ordinal⋎u γ ∧ α <⋎u β ⇒ γ +⋎u α <⋎u γ +⋎u β
=TEX

Which help in the proof of associativity of addition:

=GFT
⦏plus⋎u_assoc_thm⦎ =
	⊢ ∀ γ α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ∧ Ordinal⋎u γ
		⇒ α +⋎u β +⋎u γ = (α +⋎u β) +⋎u γ
=TEX


\ignore{
=SML
set_goal([], ⌜∀α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ α ≤⋎u α +⋎u β⌝);
a (REPEAT strip_tac THEN asm_rewrite_tac [get_spec ⌜$≤⋎u⌝]);
a (ALL_FC_T rewrite_tac [ord⋎u_plus⋎u_thm]);
a (ALL_FC_T rewrite_tac [plus⋎u_def_thm]);
a (cond_cases_tac ⌜β = ∅⋎u⌝);
(* *** Goal "1" *** *)
a (fc_tac [Set⋎u_ord⋎u_thm]);
a (∨_right_tac THEN gsu_ext_tac THEN prove_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac [∅⋎u_neq_∈⋎u_thm]);
a (∨_left_tac THEN ∨_right_tac);
a (∃_tac ⌜∅⋎u⌝ THEN asm_rewrite_tac[] THEN ∨_left_tac);
a (fc_tac [Set⋎u_ord⋎u_thm]);
a (FC_T rewrite_tac [plus⋎u_∅⋎u_thm]);
val plus⋎u_mono_right_thm = save_pop_thm "plus⋎u_mono_right_thm";

=IGN
set_goal([], ⌜∀α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ⇒ α ≤⋎u β +⋎u α⌝);
a (REPEAT ∀_tac);
a (ordinal_induction_tac ⌜β⌝);
a (REPEAT strip_tac THEN rewrite_tac [≤⋎u_lt⋎u_thm2]);
a (lemma_tac ⌜Ordinal⋎u (t +⋎u α)⌝ THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
a (REPEAT strip_tac);
a (swap_asm_concl_tac ⌜¬ α <⋎u t +⋎u α⌝);
a (ALL_UFC_⇔_T rewrite_tac[plus⋎u_def_thm2]);
a (contr_tac);

a (lemma_tac ⌜¬ t = ∅⋎u⌝ THEN1 (contr_tac THEN var_elim_asm_tac ⌜t = ∅⋎u⌝)); 
(* *** Goal "1" *** *)
a (DROP_ASM_T ⌜¬ α = ∅⋎u +⋎u α⌝ ante_tac THEN ALL_FC_T rewrite_tac [∅⋎u_plus⋎u_thm]);
(* *** Goal "2" *** *)

=SML
set_goal([], ⌜∀α β γ⦁ Ordinal⋎u γ ∧ α <⋎u β ⇒ γ +⋎u α <⋎u γ +⋎u β⌝);
a (REPEAT ∀_tac);
a (ordinal_induction_tac ⌜γ⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜Ordinal⋎u α ∧ Ordinal⋎u β⌝
	THEN1 ALL_FC_T rewrite_tac [get_spec ⌜$<⋎u⌝]);
a (ALL_UFC_⇔_T rewrite_tac [plus⋎u_def_thm2]);
a (∨_right_tac);
a (∃_tac ⌜α⌝ THEN asm_rewrite_tac[]);
val plus⋎u_mono_right_thm2 = save_pop_thm "plus⋎u_mono_right_thm2";

=IGN
set_goal([], ⌜∀α β⦁ α ≤⋎u β ⇔ Ordinal⋎u α ∧ Ordinal⋎u β ∧
		∃γ⦁ Ordinal⋎u γ ∧ β = α +⋎u γ⌝);
a (REPEAT strip_tac THEN_TRY
	 (DROP_ASM_T ⌜α ≤⋎u β⌝ ante_tac
		THEN rewrite_tac [get_spec ⌜$≤⋎u⌝]
		THEN REPEAT strip_tac));
(* *** Goal "1" *** *)
a (lemma_tac ⌜α <⋎u β⌝ THEN1 asm_rewrite_tac [get_spec ⌜$<⋎u⌝]);

a (lemma_tac ⌜⌝
a (strip_asm_tac (∀_intro ⌜γ:'a GSU⌝(list_∀_elim [⌜γ:'a GSU⌝, ⌜α:'a GSU⌝, ⌜γ:'a GSU⌝] plus⋎u_def_thm2)));


(* *** Goal "1" *** *)
a (DROP_ASM_T ⌜Ordinal⋎u α⌝ ante_tac THEN POP_ASM_T ante_tac);
a (gsu_induction_tac ⌜α⌝);
a (REPEAT strip_tac);
a (∃_tac ⌜TrCl⋎u (Imagep⋎u (λυ⦁ εγ⦁ Ordinal⋎u γ ∧ β = υ +⋎u γ) t)⌝);
a (lemma_tac ⌜∀α⦁ α ∈⋎u (Imagep⋎u (λ υ⦁ ε γ⦁ Ordinal⋎u γ ∧ β = υ +⋎u γ) t) ⇒ Ordinal⋎u α⌝);
(* *** Goal "1.1" *** *)
a (REPEAT strip_tac);
a (POP_ASM_T (strip_asm_tac o (rewrite_rule[])));
a (asm_rewrite_tac []);
a (ε_tac ⌜ε γ⦁ Ordinal⋎u γ ∧ β = e +⋎u γ⌝);
a (lemma_tac ⌜e ∈⋎u β⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_trans_thm]);
a (lemma_tac ⌜Ordinal⋎u e⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (all_asm_fc_tac[]);
a (∃_tac ⌜γ⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (all_fc_tac [TrCl⋎u_ord⋎u_thm]);
a (REPEAT strip_tac);

a (lemma_tac ⌜Ordinal⋎u (t +⋎u TrCl⋎u (Imagep⋎u (λ υ⦁ ε γ⦁ Ordinal⋎u γ ∧ β = υ +⋎u γ) t))⌝
	THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
a (lemma_tac ⌜Set⋎u (t +⋎u TrCl⋎u (Imagep⋎u (λ υ⦁ ε γ⦁ Ordinal⋎u γ ∧ β = υ +⋎u γ) t))⌝ THEN1 asm_fc_tac [Set⋎u_ord⋎u_thm]);
a (lemma_tac ⌜Set⋎u β⌝ THEN1 asm_fc_tac [Set⋎u_ord⋎u_thm]);
a (gsu_ext_tac);
a (REPEAT strip_tac);
(* *** Goal "1.2.1" *** *)



(* *** Goal "2" *** *)
set_labelled_goal "2";
a (∃_tac ⌜∅⋎u⌝);
a (fc_tac [Set⋎u_ord⋎u_thm]);
a (FC_T asm_rewrite_tac [plus⋎u_∅⋎u_thm]);

(* *** Goal "3" *** *)
set_labelled_goal "3";
a (asm_rewrite_tac[] THEN all_fc_tac [plus⋎u_mono_right_thm]);


=SML
set_goal ([], ⌜∀γ α β⦁ Ordinal⋎u α ∧ Ordinal⋎u β ∧ Ordinal⋎u γ
		⇒ (α +⋎u (β +⋎u γ)) = ((α +⋎u β) +⋎u γ)⌝);
a (strip_tac);
a (gsu_induction_tac ⌜γ⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜Ordinal⋎u (β +⋎u t)⌝ THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
a (FC_T rewrite_tac [list_∀_elim [⌜α⌝, ⌜β +⋎u t⌝] plus⋎u_def_thm]);
a (FC_T rewrite_tac [list_∀_elim [⌜α +⋎u β⌝, ⌜t⌝] plus⋎u_def_thm]);
a (FC_T rewrite_tac [list_∀_elim [⌜β⌝, ⌜t⌝] plus⋎u_def_thm]);
a (FC_T rewrite_tac [list_∀_elim [⌜α⌝, ⌜β⌝] plus⋎u_def_thm]);
a (gsu_ext_tac);
a (∀_tac THEN rewrite_tac[]);
a (cond_cases_tac ⌜e ∈⋎u α⌝);
a (lemma_tac ⌜∀ u
           ⦁ u ∈⋎u t
               ⇒ α +⋎u β +⋎u u = (α +⋎u β) +⋎u u⌝ THEN1 REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜Ordinal⋎u u⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (asm_fc_tac[]);
(* *** Goal "2.3" *** *)
a (∃_tac ⌜y'⌝ THEN ASM_FC_T asm_rewrite_tac []);
a (∨_left_tac);
a (FC_T rewrite_tac [list_∀_elim [⌜α⌝, ⌜β⌝] plus⋎u_def_thm]);
(* *** Goal "2.4" *** *)
a (∃_tac ⌜y'⌝ THEN ASM_FC_T asm_rewrite_tac []);
a (∨_right_tac);
a (POP_ASM_T discard_tac THEN POP_ASM_T ante_tac
	THEN TOP_ASM_T (var_elim_asm_tac o concl));
a (LEMMA_T ⌜α +⋎u β +⋎u y' = (α +⋎u β) +⋎u y'⌝ rewrite_thm_tac
	THEN1 all_asm_fc_tac[]);
a (FC_T rewrite_tac [list_∀_elim [⌜α⌝, ⌜β⌝] plus⋎u_def_thm]);
(* *** Goal "2.5" *** *)
a (∃_tac ⌜y'⌝ THEN ASM_FC_T asm_rewrite_tac []);
a (∨_right_tac);
a (LEMMA_T ⌜α +⋎u β +⋎u y' = (α +⋎u β) +⋎u y'⌝ ante_tac
	THEN1 all_asm_fc_tac[]);
a (FC_T rewrite_tac [list_∀_elim [⌜α⌝, ⌜β⌝] plus⋎u_def_thm]);
a (STRIP_T (rewrite_thm_tac o map_eq_sym_rule));
a (lemma_tac ⌜Ordinal⋎u (y')⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (lemma_tac ⌜Ordinal⋎u (β +⋎u y')⌝ THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
a (lemma_tac ⌜Ordinal⋎u y⌝ THEN1 all_fc_tac [ord⋎u_tc∈⋎u_ord⋎u_thm]);
a (lemma_tac ⌜y <⋎u β +⋎u y'⌝
	THEN1 (asm_rewrite_tac [get_spec ⌜$<⋎u⌝]
		THEN all_fc_tac [tc∈⋎u_ord⋎u_thm]));
a ((LEMMA_T ⌜α +⋎u y <⋎u α +⋎u β +⋎u y'⌝ ante_tac
	THEN1 all_asm_fc_tac [plus⋎u_mono_right_thm2])
	THEN rewrite_tac [get_spec ⌜$<⋎u⌝]
	THEN REPEAT strip_tac
	THEN all_fc_tac [tc∈⋎u_incr_thm]);
(* *** Goal "2.6" *** *)
a (∃_tac ⌜y'⌝ THEN ASM_FC_T asm_rewrite_tac []);
a (∨_right_tac);
a (LEMMA_T ⌜α +⋎u β +⋎u y' = (α +⋎u β) +⋎u y'⌝ ante_tac
	THEN1 all_asm_fc_tac[]);
a (FC_T rewrite_tac [list_∀_elim [⌜α⌝, ⌜β⌝] plus⋎u_def_thm]);
a (STRIP_T (rewrite_thm_tac o map_eq_sym_rule));
a (lemma_tac ⌜Ordinal⋎u y'⌝ THEN1 all_fc_tac [ord⋎u_∈⋎u_ord⋎u_thm]);
a (lemma_tac ⌜Ordinal⋎u (β +⋎u y')⌝ THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
a (lemma_tac ⌜Ordinal⋎u y⌝ THEN1 all_fc_tac [ord⋎u_tc∈⋎u_ord⋎u_thm]);
a (lemma_tac ⌜y <⋎u β +⋎u y'⌝
	THEN1 all_fc_tac [tc∈⋎u_⇔_lt⋎u_thm]);
a (lemma_tac ⌜Ordinal⋎u (α +⋎u y)⌝ THEN1 all_fc_tac [ord⋎u_plus⋎u_thm]);
a (lemma_tac ⌜Ordinal⋎u e⌝ THEN1 all_fc_tac [ord⋎u_tc∈⋎u_ord⋎u_thm]);
a (lemma_tac ⌜e <⋎u α +⋎u y⌝
	THEN1 all_fc_tac [tc∈⋎u_⇔_lt⋎u_thm]);
a (lemma_tac ⌜α +⋎u y <⋎u α +⋎u β +⋎u y'⌝ 
	THEN1 all_asm_fc_tac [plus⋎u_mono_right_thm2]);
a (ALL_FC_T (MAP_EVERY(strip_asm_tac o (rewrite_rule [get_spec ⌜$<⋎u⌝]))) [lt⋎u_trans_thm]);
a (all_fc_tac [tc∈⋎u_incr_thm]);
(* *** Goal "2.7" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.8" *** *)
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.9" *** *)
a (∃_tac ⌜β +⋎u y⌝ THEN asm_rewrite_tac[]);
a (strip_tac);
(* *** Goal "2.9.1" *** *)
a (∨_right_tac);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac []);
a (∨_left_tac);
a (LEMMA_T ⌜α ∪⋎u ClIm⋎u ($+⋎u α) β = α +⋎u β⌝ rewrite_thm_tac
	THEN1 ALL_FC_T rewrite_tac [plus⋎u_def_thm]);
a (LEMMA_T ⌜α +⋎u β +⋎u y = (α +⋎u β) +⋎u y⌝ rewrite_thm_tac
	THEN1 all_asm_fc_tac[]);
(* *** Goal "2.10" *** *)
(* *** Goal "2.10" *** *)
a (∃_tac ⌜β +⋎u y⌝ THEN strip_tac);
(* *** Goal "2.10.1" *** *)
a (∨_right_tac);
a (∃_tac ⌜y⌝ THEN asm_rewrite_tac []);
(* *** Goal "2.10.2" *** *)
a (∨_right_tac);
a (POP_ASM_T ante_tac);
a (LEMMA_T ⌜α ∪⋎u ClIm⋎u ($+⋎u α) β = α +⋎u β⌝ rewrite_thm_tac
	THEN1 ALL_FC_T rewrite_tac [plus⋎u_def_thm]);
a (LEMMA_T ⌜α +⋎u β +⋎u y = (α +⋎u β) +⋎u y⌝ rewrite_thm_tac
	THEN1 all_asm_fc_tac[]);
val plus⋎u_assoc_thm = save_pop_thm "plus⋎u_assoc_thm";

add_rw_thms [Set⋎u_plus⋎u_thm, plus⋎u_∅⋎u_thm2] "'gsu-ord";
add_sc_thms [Set⋎u_plus⋎u_thm, plus⋎u_∅⋎u_thm2] "'gsu-ord";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-ord"];
=TEX
}%ignore

\subsubsection{Subtraction}

The following definition is of reverse subtraction, i.e. the right operand is subtracted from the left and is taken from the left of that operand so that the following lemma (as yet unproven) obtains:

=GFT desideratum
⦏--⋎u_lemma⦎ =
	∀α β⦁ α ≤⋎u β ⇒ α +⋎u (β --⋎u α) = β
=TEX

\ignore{
=IGN
set_goal([], ⌜∀α β:'a GSU⦁ α ≤⋎u β ⇒ ∃γ⦁  α +⋎u γ = β⌝);
a (REPEAT ∀_tac);
a (wf_induction_tac gsu_wf_thm1 ⌜β⌝);
a (strip_tac);
a (∃_tac ⌜Imagep⋎u (λu⦁ εγ⦁ α +⋎u γ = u) (Sep⋎u t (λν⦁ α ≤⋎u ν))⌝);
a (lemma_tac ⌜∀η⦁ η ∈⋎u Imagep⋎u (λ u⦁ ε γ⦁ α +⋎u γ = u) (Sep⋎u t (λ ν⦁ α ≤⋎u ν))
	⇔ ∃κ⦁ κ ∈⋎u t ∧ α ≤⋎u κ ∧ η = ε γ⦁ α +⋎u γ = κ⌝);
(* *** Goal "1" *** *)
a (strip_tac THEN rewrite_tac [Imagep⋎u_def]);
a (REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (∃_tac ⌜e⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜κ⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜$+⋎u⌝]);
a (rewrite_tac [gsu_ext_axiom]);

a (rewrite_tac [Imagep⋎u_def]);
a (cases_tac ⌜α = t⌝ THEN_TRY asm_rewrite_tac[]);

;

set_goal([], ⌜∃$--⋎u⦁ ∀α β:'a GSU⦁ α ≤⋎u β ⇒ α +⋎u (α --⋎u β) = β⌝);
a (∃_tac ⌜λα β⦁ if α ≤⋎u β then εγ⦁ α +⋎u γ = β else ∅⋎u⌝);
a (rewrite_tac[]);

frees⌜λα β⦁ if α ≤⋎u β then εγ⦁ α +⋎u γ = β else ∅⋎u⌝;
get_spec ⌜$≤⋎u⌝;
=TEX
}%ignore

ⓈHOLCONST
 $⦏--⋎u⦎ : 'a GSU → 'a GSU → 'a GSU
├
  T
■


\subsection{Proof Context}

In this section we define a proof context for ordinals.

\subsubsection{Proof Context}

Since almost everything is conditional there are few additional theorems to include:

=GFT
	Set⋎u_Suc⋎u_thm, ⊆⋎u_Suc⋎u_thm, ∈⋎u_Suc⋎u_thm, Set⋎u_ord⋎u_thm,
	Set⋎u_plus⋎u_thm, plus⋎u_∅⋎u_thm2, ord⋎u_∅⋎u_thm
=TEX

=IGN
add_pc_thms "'gsu-ord" ([]);
add_sc_thms [Set⋎u_Suc⋎u_thm, ⊆⋎u_Suc⋎u_thm, ∈⋎u_Suc⋎u_thm, Set⋎u_ord⋎u_thm,
	Set⋎u_plus⋎u_thm, plus⋎u_∅⋎u_thm2, ord⋎u_∅⋎u_thm] "'gsu-ord";
add_rw_thms [Set⋎u_Suc⋎u_thm, ⊆⋎u_Suc⋎u_thm, ∈⋎u_Suc⋎u_thm, Set⋎u_ord⋎u_thm,
	Set⋎u_plus⋎u_thm, plus⋎u_∅⋎u_thm2, ord⋎u_∅⋎u_thm] "'gsu-ord";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-ord"];
=SML
commit_pc "'gsu-ord";
=TEX

\section{Natural Numbers}

=SML
open_theory "gsu-ord";
force_new_theory "gsu-nat";
force_new_pc "'gsu-nat";
merge_pcs ["'savedthm_cs_∃_proof"] "'gsu-nat";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-ord", "'gsu-nat"];
=TEX

ⓈHOLCONST
 ⦏natural_number⋎u⦎ : 'a GSU → BOOL
├
  ∀s :'a GSU⦁ natural_number⋎u s ⇔ s = ∅⋎u ∨ (Successor⋎u s ∧ ∀t⦁ t∈⋎u s ⇒ t = ∅⋎u ∨ Successor⋎u t)
■

\subsubsection{Ordering the Natural Numbers}

To get an induction principle for the natural numbers we first define a well-founded ordering over them.
Since I don't plan to use this a lot I use the name $<⋎u⋎n$ (less than over the natural numbers defined in galactic set theory).

=SML
declare_infix(240,"<⋎u⋎n");
=TEX

ⓈHOLCONST
 $⦏<⋎u⋎n⦎ : 'a GSU → 'a GSU → BOOL
├
  ∀x y:'a GSU⦁ x <⋎u⋎n y ⇔ natural_number⋎u x ∧ natural_number⋎u y ∧ x ∈⋎u y
■

Now we try to find a better proof that the one above that this is well-founded.
And fail, this is just a more compact rendition of the same proof.

=SML
set_goal([],⌜well_founded $<⋎u⋎n⌝);
a (asm_tac gsu_wf_thm1);
a (fc_tac [wf_restrict_wf_thm]);
a (SPEC_NTH_ASM_T 1 ⌜λx y:'a GSU⦁ natural_number⋎u x ∧ natural_number⋎u y⌝ ante_tac
	THEN rewrite_tac[]);
a (lemma_tac ⌜$<⋎u⋎n = (λ x y:'a GSU⦁ (natural_number⋎u x ∧ natural_number⋎u y) ∧ x ∈⋎u y)⌝
	THEN1 (REPEAT_N 2 (once_rewrite_tac [ext_thm])
		THEN prove_tac[get_spec ⌜$<⋎u⋎n⌝]));
a (asm_rewrite_tac[]);
val wf_nat⋎u_thm = save_pop_thm "wf_nat⋎u_thm";
=TEX
This allows us to do well-founded induction over the natural number which the way I have implemented it is "course-of-values" induction.
However, for the sake of form I will prove that induction principle as an explicit theorem.
This is just what you get by expanding the definition of well-foundedness in the above theorem.
=SML
val nat⋎u_induct_thm = save_thm ("nat⋎u_induct_thm",
	(rewrite_rule [get_spec ⌜well_founded⌝] wf_nat⋎u_thm));
=TEX
Note that this theorem can only be used to prove properties which are true of all sets, so you have to make it conditional 
=INLINEFT
(natural_number⋎u n ⇒ whatever)
=TEX
I suppose I'd better do another one.
=SML
set_goal([], ⌜∀ p⦁ (∀ x⦁ natural_number⋎u x ∧ (∀ y⦁ y <⋎u⋎n x ⇒ p y) ⇒ p x)
	⇒ (∀ x⦁ natural_number⋎u x ⇒ p x)⌝);
a (asm_tac (rewrite_rule []
	(all_∀_intro (∀_elim ⌜λx⦁ natural_number⋎u x ⇒ p x⌝ nat⋎u_induct_thm))));
a (rewrite_tac [all_∀_intro (taut_rule ⌜a ∧ b ⇒ c ⇔ b ⇒ a ⇒ c⌝)]);
a (lemma_tac ⌜∀ p x⦁ (∀ y⦁ y <⋎u⋎n x ⇒ p y)
	⇔ (∀ y⦁ y <⋎u⋎n x ⇒ natural_number⋎u y ⇒ p y)⌝);
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜$<⋎u⋎n⌝]);
a (REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
val nat⋎u_induct_thm2 = save_pop_thm "nat⋎u_induct_thm2";
=TEX

I've tried using that principle and it too has disadvantages.
Because $<⋎u⋎n$ is used the induction hypothesis is more awkward to use (weaker) than it would have been if $∈⋎u$ had been used.
Unfortunately the proof of an induction theorem using plain set membership is not entirely trivial, so its proof has to be left til later.

=IGN
⦏nat⋎u_induct_thm2⦎ =
	⊢ ∀ p⦁ (∀ x⦁ natural_number⋎u x ∧ (∀ y⦁ y ∈⋎u x ⇒ p y) ⇒ p x)
		⇒ (∀ x⦁ natural_number⋎u x ⇒ p x)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ p⦁ (∀ x⦁ natural_number⋎u x ∧ (∀ y⦁ y ∈⋎u x ⇒ p y) ⇒ p x)
	⇒ (∀ x⦁ natural_number⋎u x ⇒ p x)⌝);
=IGN
a (asm_tac (rewrite_rule []
	(all_∀_intro (∀_elim ⌜λx⦁ natural_number⋎u x ⇒ p x⌝ nat⋎u_induct_thm))));
a (rewrite_tac [all_∀_intro (taut_rule ⌜a ∧ b ⇒ c ⇔ b ⇒ a ⇒ c⌝)]);
a (lemma_tac ⌜∀ p x⦁ ((∀ y⦁ y ∈⋎u x ⇒ p y) ⇒ natural_number⋎u x ⇒ p x)
	⇔ (∀ y⦁ y <⋎u⋎n x ⇒ natural_number⋎u y ⇒ p y) ⇒ natural_number⋎u x ⇒ p x⌝);
(* *** Goal "1" *** *)
a (rewrite_tac [get_spec ⌜$<⋎u⋎n⌝]);
a (REPEAT strip_tac THEN all_asm_fc_tac[]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
val nat⋎u_induct_thm2 = save_pop_thm "nat⋎u_induct_thm2";
=TEX
}%ignore

\subsection{Theorem 2.8}

The set of natural numbers.

\subsubsection{Natural Numbers are Ordinals}

=SML
set_goal ([], ⌜∀n⦁ natural_number⋎u n ⇒ Ordinal⋎u n⌝);
a (rewrite_tac [get_spec ⌜natural_number⋎u⌝, get_spec ⌜Successor⋎u⌝]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[ord⋎u_∅⋎u_thm]);
a (all_fc_tac [ord⋎u_suc⋎u_ord⋎u_thm]);
val ord⋎u_nat⋎u_thm = save_pop_thm "ord⋎u_nat⋎u_thm";
=TEX

\subsubsection{Members of Natural Numbers are Ordinals}

=SML
set_goal ([], ⌜∀n⦁ natural_number⋎u n ⇒ ∀m⦁ m ∈⋎u n ⇒ Ordinal⋎u m⌝);
a (REPEAT strip_tac);
a (REPEAT (all_fc_tac[ord⋎u_nat⋎u_thm, ord⋎u_∈⋎u_ord⋎u_thm]));
val ∈⋎u_nat⋎u_ord⋎u_thm = save_pop_thm "∈⋎u_nat⋎u_ord⋎u_thm";
=TEX

\subsubsection{A Natural Number is not a Limit Ordinal}

=SML
set_goal ([], ⌜∀n⦁ natural_number⋎u n ⇒ ¬ LimitOrdinal⋎u n⌝);
a (rewrite_tac [get_spec ⌜LimitOrdinal⋎u⌝, get_spec ⌜natural_number⋎u⌝]);
a (REPEAT strip_tac);
val nat⋎u_not_lim_thm = save_pop_thm "nat⋎u_not_lim_thm";
=TEX

\subsubsection{A Natural Number is zero or a Successor}

=SML
set_goal ([], ⌜∀n⦁ natural_number⋎u n ⇒ Successor⋎u n ∨ n = ∅⋎u⌝);
a (rewrite_tac [get_spec ⌜natural_number⋎u⌝]);
a (REPEAT strip_tac);
val nat⋎u_zero_or_suc⋎u_thm = save_pop_thm "nat⋎u_zero_or_suc⋎u_thm";
=TEX

\subsubsection{A Natural Number does not contain a Limit Ordinal}

=SML
set_goal ([], ⌜∀m n⦁ natural_number⋎u n ∧ m ∈⋎u n ⇒ ¬ LimitOrdinal⋎u m⌝);
a (rewrite_tac [get_spec ⌜LimitOrdinal⋎u⌝, get_spec ⌜natural_number⋎u⌝]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [∈⋎u_not_empty_thm]);
(* *** Goal "2" *** *)
a (all_asm_fc_tac[]);
val ∈⋎u_nat⋎u_not_lim_thm = save_pop_thm "∈⋎u_nat⋎u_not_lim_thm";
=TEX

\subsubsection{All Members of Natural Numbers are Natural Numbers}

=SML
set_goal ([], ⌜∀n⦁ natural_number⋎u n ⇒ ∀m⦁ m ∈⋎u n ⇒ natural_number⋎u m⌝);
a (rewrite_tac [get_spec ⌜natural_number⋎u⌝]);
a (REPEAT strip_tac THEN_TRY all_asm_fc_tac [∈⋎u_not_empty_thm]);
a (lemma_tac ⌜Transitive⋎u n⌝ THEN1
	 (REPEAT (all_fc_tac [get_spec ⌜Ordinal⋎u⌝, Successor⋎u_ord⋎u_thm])));
a (lemma_tac ⌜t ∈⋎u n⌝ THEN1 (EVERY [all_fc_tac [Transitive⋎u_def],
	POP_ASM_T ante_tac, rewrite_tac [gsu_relext_clauses], asm_prove_tac[]]));
a (all_asm_fc_tac[]);
val ∈⋎u_nat⋎u_nat⋎u_thm = save_pop_thm "∈⋎u_nat⋎u_nat⋎u_thm";
=TEX

=GFT
⦏nat⋎u_in_G∅⋎u_thm⦎ =
	⊢ ∀n⦁ natural_number⋎u n ⇒ n ∈⋎u Gx⋎u ∅⋎u
=TEX

\ignore{
=SML
set_goal ([], ⌜∀n⦁ natural_number⋎u n ⇒ n ∈⋎u Gx⋎u ∅⋎u⌝);
a (strip_tac THEN gen_induction_tac1 nat⋎u_induct_thm2);
a (fc_tac [nat⋎u_zero_or_suc⋎u_thm]);
(* *** Goal "1" *** *)
a (fc_tac [get_spec ⌜Successor⋎u⌝]);
a (lemma_tac ⌜t <⋎u⋎n n⌝
	THEN1 asm_rewrite_tac [get_spec ⌜$<⋎u⋎n⌝, get_spec ⌜Suc⋎u⌝]);
(* *** Goal "1.1" *** *)
a (lemma_tac ⌜t ∈⋎u n⌝
	THEN1 asm_rewrite_tac [get_spec ⌜Suc⋎u⌝]);
a (all_fc_tac [∈⋎u_nat⋎u_nat⋎u_thm]);
(* *** Goal "1.2" *** *)
a (asm_tac (∀_elim ⌜∅⋎u⌝ galaxy⋎u_Gx⋎u));
a (asm_rewrite_tac[]);
a (REPEAT (all_asm_fc_tac[GClose⋎u_Suc⋎u_thm]));
(* *** Goal "2" *** *)
a (asm_rewrite_tac[]);
val nat⋎u_in_G∅⋎u_thm = save_pop_thm "nat⋎u_in_G∅⋎u_thm";
=TEX
}%ignore

\subsubsection{The Existence of w}

This comes from the axiom of infinity, however, in galactic set theory we get that from the existence of galaxies, so the following proof is a little unusual.

=SML
set_goal ([], ⌜∃w⦁ ∀z⦁ z ∈⋎u w ⇔ natural_number⋎u z⌝);
a (∃_tac ⌜Sep⋎u (Gx⋎u ∅⋎u) natural_number⋎u⌝
	THEN rewrite_tac [gsu_opext_clauses]);
a (rewrite_tac [all_∀_intro (taut_rule ⌜(a ∧ b ⇔ b) ⇔ b ⇒ a⌝)]);
a strip_tac;
a (gen_induction_tac1 nat⋎u_induct_thm2);
a (fc_tac [nat⋎u_zero_or_suc⋎u_thm]);
(* *** Goal "1" *** *)
a (fc_tac [get_spec ⌜Successor⋎u⌝, nat⋎u_in_G∅⋎u_thm]);
(* *** Goal "2" *** *)
a (asm_rewrite_tac []);
val ω⋎u_exists_thm = save_pop_thm "ω⋎u_exists_thm";
=TEX

\subsection{Naming the Natural Numbers}

It will be useful to be able to have names for the finite ordinals, which are used as tags in the syntax:

ⓈHOLCONST
│ ⦏Nat⋎u⦎: ℕ → 'a GSU
├───────────
│       Nat⋎u 0 = ∅⋎u
│ ∧ ∀n⦁ Nat⋎u (n+1) = Suc⋎u (Nat⋎u n)
■

We will need to know that these are all distinct ordinals.

=GFT
⦏Set⋎u_Nat⋎u_lemma⦎ =
	⊢ ∀ n⦁ Set⋎u (Nat⋎u n)

⦏ord⋎u_nat⋎u_thm2⦎ =
	⊢ ∀ n⦁ Ordinal⋎u (Nat⋎u n)

⦏not_suc⋎u_nat⋎u_zero_thm⦎ =
	⊢ ∀ n⦁ ¬ Suc⋎u (Nat⋎u n) = ∅⋎u

⦏lt⋎u_sum_thm⦎ =
	⊢ ∀ x y⦁ x ≤ y ⇒ (∃ z⦁ x + z = y)

⦏nat⋎u_mono_thm⦎ =
	⊢ ∀ x y⦁ Nat⋎u x ≤⋎u Nat⋎u (x + y)

⦏nat⋎u_one_one_thm⦎ =
	⊢ ∀ x y⦁ Nat⋎u x = Nat⋎u y ⇒ x = y

⦏nat⋎u_one_one_thm2⦎ =
	⊢ ∀ x y⦁ Nat⋎u x = Nat⋎u y ⇔ x = y
=TEX

\ignore{
=SML
val Nat⋎u_def = get_spec ⌜Nat⋎u⌝;

set_goal([], ⌜∀n⦁ Set⋎u (Nat⋎u n)⌝);
a (strip_tac);
a (induction_tac ⌜n⌝ THEN asm_rewrite_tac [Nat⋎u_def]);
val Set⋎u_Nat⋎u_lemma = pop_thm ();

set_goal([], ⌜∀n⦁ Ordinal⋎u (Nat⋎u n)⌝);
a (strip_tac);
a (induction_tac ⌜n⌝);
a (rewrite_tac [get_spec ⌜Nat⋎u⌝, ord⋎u_∅⋎u_thm]);
a (rewrite_tac [get_spec ⌜Nat⋎u⌝]);
a (fc_tac [ord⋎u_suc⋎u_ord⋎u_thm]);
val ord⋎u_nat⋎u_thm2 = save_pop_thm "ord⋎u_nat⋎u_thm2";

set_goal([], ⌜∀n⦁ ¬ Suc⋎u (Nat⋎u n) = ∅⋎u⌝);
a (asm_tac ord⋎u_nat⋎u_thm2);
a (strip_asm_tac ∅⋎u_not_Suc⋎u_thm);
a strip_tac;
a (spec_nth_asm_tac 1 ⌜Nat⋎u n⌝);
val not_suc⋎u_nat⋎u_zero_thm = save_pop_thm "not_suc⋎u_nat⋎u_zero_thm";

set_goal([], ⌜∀x y:ℕ⦁ x ≤ y ⇒ ∃z⦁ x + z = y⌝);
a (REPEAT ∀_tac);
a (induction_tac ⌜y⌝);
(* *** Goal "1" *** *)
a (strip_tac THEN ∃_tac ⌜0⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (strip_tac THEN ∃_tac ⌜0⌝
	THEN (PC_T1 "lin_arith" asm_prove_tac[]));
(* *** Goal "3" *** *)
a (strip_tac THEN ∃_tac ⌜z + 1⌝
	THEN (PC_T1 "lin_arith" asm_prove_tac[]));
val lt⋎u_sum_thm = save_pop_thm "lt⋎u_sum_thm";

set_goal([], ⌜∀x y:ℕ⦁ Nat⋎u x ≤⋎u Nat⋎u (x + y)⌝);
a (REPEAT ∀_tac);
a (induction_tac ⌜y⌝);
(* *** Goal "1" *** *)
a (rewrite_tac [≤⋎u_lt⋎u_thm2, ord⋎u_nat⋎u_thm2]);
(* *** Goal "2" *** *)
a (rewrite_tac [get_spec ⌜Nat⋎u⌝,
	pc_rule1 "lin_arith" prove_rule [] ⌜x + y + 1 = (x + y) + 1⌝]);
a (asm_tac ≤⋎u_suc⋎u_thm);
a (asm_tac ord⋎u_nat⋎u_thm2);
a (spec_nth_asm_tac 1 ⌜x+y⌝);
a (asm_fc_tac []);
a (all_asm_fc_tac [≤⋎u_trans_thm]);
val nat⋎u_mono_thm = save_pop_thm "nat⋎u_mono_thm";

set_goal([], ⌜∀x y⦁ Nat⋎u x = Nat⋎u y ⇒ x = y⌝);
a (REPEAT ∀_tac);
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜y⌝] ≤_cases_thm));
(* *** Goal "1" *** *)
a (fc_tac [lt⋎u_sum_thm]);
a (POP_ASM_T ante_tac THEN induction_tac ⌜z⌝);
(* *** Goal "1.1" *** *)
a (rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1.2" *** *)
a (strip_tac);
a (SYM_ASMS_T rewrite_tac);
a (lemma_tac ⌜Nat⋎u x ≤⋎u Nat⋎u (x + z)⌝
	THEN1 rewrite_tac [nat⋎u_mono_thm]);
a (lemma_tac ⌜Nat⋎u (x + z) <⋎u Nat⋎u (x + z + 1)⌝);
(* *** Goal "1.2.1" *** *)
a (rewrite_tac [pc_rule1 "lin_arith" prove_rule [] ⌜x + z + 1 = (x + z) + 1⌝]);
a (rewrite_tac [get_spec ⌜Nat⋎u⌝]);
a (asm_tac (∀_elim ⌜x+z⌝ ord⋎u_nat⋎u_thm2));
a (FC_T rewrite_tac [lt⋎u_suc⋎u_thm]);
(* *** Goal "1.2.2" *** *)
a (all_fc_tac [≤⋎u_lt⋎u_trans_thm]);
a (POP_ASM_T ante_tac
	THEN (rewrite_tac [get_spec ⌜$<⋎u⌝])
	THEN REPEAT strip_tac);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac [wf_ul1]);
(* *** Goal "1.3" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "1.4" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [lt⋎u_sum_thm]);
a (POP_ASM_T ante_tac THEN induction_tac ⌜z⌝);
(* *** Goal "2.1" *** *)
a (rewrite_tac[] THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (strip_tac);
a (SYM_ASMS_T rewrite_tac);
a (lemma_tac ⌜Nat⋎u y ≤⋎u Nat⋎u (y + z)⌝
	THEN1 rewrite_tac [nat⋎u_mono_thm]);
a (lemma_tac ⌜Nat⋎u (y + z) <⋎u Nat⋎u (y + z + 1)⌝);
(* *** Goal "2.2.1" *** *)
a (rewrite_tac [pc_rule1 "lin_arith" prove_rule [] ⌜y + z + 1 = (y + z) + 1⌝]);
a (rewrite_tac [get_spec ⌜Nat⋎u⌝]);
a (asm_tac (∀_elim ⌜y+z⌝ ord⋎u_nat⋎u_thm2));
a (FC_T rewrite_tac [lt⋎u_suc⋎u_thm]);
(* *** Goal "2.2.2" *** *)
a (all_fc_tac [≤⋎u_lt⋎u_trans_thm]);
a (POP_ASM_T ante_tac
	THEN (rewrite_tac [get_spec ⌜$<⋎u⌝])
	THEN REPEAT strip_tac);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac [wf_ul1]);
(* *** Goal "2.3" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2.4" *** *)
a (asm_rewrite_tac[]);
val nat⋎u_one_one_thm = save_pop_thm "nat⋎u_one_one_thm";

set_goal([], ⌜∀x y⦁ Nat⋎u x = Nat⋎u y ⇔ x = y⌝);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (asm_fc_tac [nat⋎u_one_one_thm]);
val nat⋎u_one_one_thm2 = save_pop_thm "nat⋎u_one_one_thm2";

=IGN
set_goal([], ⌜∀x y⦁ Nat⋎u (x+y) = (Nat⋎u x) +⋎u (Nat⋎u y)⌝);
a (REPEAT ∀_tac);
a (induction_tac ⌜y⌝);
a (rewrite_tac[get_spec ⌜$+⋎u⌝, get_spec ⌜Nat⋎u⌝]);
a (rewrite_tac [pc_rule1 "lin_arith" prove_rule [] ⌜x + y + 1 = (x + y) + 1⌝]);
a (asm_rewrite_tac[get_spec⌜Nat⋎u⌝]);
=TEX
}%ignore

\subsection{Proof Context}

In this section we define a proof context for natural numbers.

=SML
add_pc_thms "'gsu-nat" ([nat⋎u_one_one_thm2]);
add_rw_thms [Set⋎u_Nat⋎u_lemma] "'gsu-nat";
add_sc_thms [Set⋎u_Nat⋎u_lemma] "'gsu-nat";

set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-ord", "'gsu-nat"];
commit_pc "'gsu-nat";
=TEX

\section{Sequences}

=SML
open_theory "gsu-ord";
force_new_theory "gsu-seq";
new_parent "gsu-fun";
force_new_pc "'gsu-seq";
merge_pcs ["'savedthm_cs_∃_proof"] "'gsu-seq";
set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun", "'gsu-ord", "'gsu-seq"];
=TEX

A sequence is a function whose domain is an ordinal.

ⓈHOLCONST
│ ⦏Seq⋎u⦎: 'a GSU → BOOL
├───────────
│       ∀s⦁ Seq⋎u s ⇔ Fun⋎u s ∧ Ordinal⋎u(Dom⋎u s)
■

The domain is also the length of the sequence.

ⓈHOLCONST
│ ⦏Length⋎u⦎: 'a GSU → 'a GSU
├───────────
│       Length⋎u = Dom⋎u
■

\subsubsection{Operations on Sequences}

A few operations over sequences are defined here, without proving any of their properties (which will be done as and when needed).

ⓈHOLCONST
│ ⦏Head⋎u⦎: 'a GSU → 'a GSU
├───────────
│       ∀s⦁ Head⋎u s = s ⋎u ∅⋎u
■

ⓈHOLCONST
│ ⦏Front⋎u⦎: 'a GSU → 'a GSU → 'a GSU
├───────────
│       ∀α s⦁ Front⋎u α s = α ◁⋎u s
■

ⓈHOLCONST
│ ⦏Back⋎u⦎: 'a GSU → 'a GSU → 'a GSU
├───────────
│       ∀α s⦁ Back⋎u α s = s o⋎u ((λ⋎u β⦁ β +⋎u α) (Dom⋎u s))
■

ⓈHOLCONST
│ ⦏Tail⋎u⦎: 'a GSU → 'a GSU
├───────────
│       ∀s⦁ Tail⋎u s = Back⋎u (Suc⋎u ∅⋎u) s
■

The symbol $@⋎u$ will be used for concatenation of sequences.

=SML
declare_infix(300,"@⋎u");
=TEX

ⓈHOLCONST
│ $⦏@⋎u⦎: 'a GSU → 'a GSU → 'a GSU
├───────────
│       ∀s t⦁ s @⋎u t = s ∪⋎u (t )
│
■


=GFT
=TEX

\ignore{
=IGN
stop;

val app_def = get_spec ⌜$@⋎u⌝;

set_goal([], ⌜∀s t u⦁ Seq⋎u s ∧ Seq⋎u t
		⇒ (u ∈⋎u s @⋎u t ⇔ u ∈⋎u s
			∨ (∃v⦁ v ∈⋎u t ∧ Fst⋎u v +⋎u Dom⋎u s = Fst⋎u u
				∧ Snd⋎u u = Snd⋎u v))⌝);
a (REPEAT strip_tac);



set_goal([], ⌜∀s t u⦁ Seq⋎u s ∧ Seq⋎u t ∧ Seq⋎u u
		⇒ (s @⋎u t) @⋎u u = s @⋎u t @⋎u u⌝);
a (rewrite_tac[app_def] THEN REPEAT strip_tac);
a (gsu_ext_tac THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜(λ p⦁ Fst⋎u p +⋎u Dom⋎u t ↦⋎u Snd⋎u p) e'⌝ THEN asm_rewrite_tac[]);
a (LEMMA_T ⌜∃ e
               ⦁ e ∈⋎u u
                   ∧ (λ p⦁ Fst⋎u p +⋎u Dom⋎u t ↦⋎u Snd⋎u p) e'
                     = (λ p⦁ Fst⋎u p +⋎u Dom⋎u t ↦⋎u Snd⋎u p) e⌝
	 rewrite_thm_tac
	THEN1 (∃_tac ⌜e'⌝ THEN asm_rewrite_tac[])); 

a (rewrite_tac[lambda⋎u_def]);
=TEX
}%ignore

ⓈHOLCONST
│ ⦏UnitSeq⋎u⦎: 'a GSU → 'a GSU
├───────────
│       ∀e⦁ UnitSeq⋎u e = ∅⋎u ↦⋎u e
■

ⓈHOLCONST
│ ⦏SeqCons⋎u⦎: 'a GSU → 'a GSU → 'a GSU
├───────────
│      ∀e s⦁ SeqCons⋎u e s = (UnitSeq⋎u e) @⋎u s
■

ⓈHOLCONST
│ ⦏SeqDisp⋎u⦎: 'a GSU LIST → 'a GSU
├───────────
│       SeqDisp⋎u [] = ∅⋎u
│ ∧	∀e s⦁ SeqDisp⋎u	(Cons e s) = SeqCons⋎u e (SeqDisp⋎u s)
■

=GFT
=TEX

\ignore{
=SML

=TEX
}%ignore

\subsubsection{Mapping Functions over Sequences}

A function can be mapped over a sequence using $RanMap⋎u$, so we don't need to define a sequence map operator.
We probably will need to know that the result of mapping something over a sequence is another sequence of the same length.
We already know that mapping over a relation preserves the domain of the relation, so this is trivial.

=GFT
⦏Seq⋎u_RanMap⋎u_thm⦎ = ⊢ ∀ f s⦁ Seq⋎u s ⇒ Seq⋎u (RanMap⋎u f s)
=TEX

\ignore{
=SML
val Seq⋎u_def = get_spec ⌜Seq⋎u⌝;

set_goal([], ⌜∀f s⦁ Seq⋎u s ⇒ Seq⋎u (RanMap⋎u f s)⌝);
a (rewrite_tac[Seq⋎u_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_asm_fc_tac [Fun⋎u_RanMap⋎u_thm] THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_asm_fc_tac [Fun⋎u_def]);
a (all_asm_fc_tac [Dom⋎u_RanMap⋎u_thm] THEN asm_rewrite_tac[]);
val Seq⋎u_RanMap⋎u_thm = save_pop_thm "Seq⋎u_RanMap⋎u_thm";
=TEX
}%ignore



\subsubsection{Proof Context}

=SML
add_pc_thms "'gsu-seq" ([]);
add_rw_thms [] "'gsu-seq";
add_sc_thms [] "'gsu-seq";

set_merge_pcs ["basic_hol", "'gsu-ax", "'gsu-fun", "'gsu-ord", "'gsu-seq"];
commit_pc "'gsu-seq";
=TEX

\section{Closing}

=SML
open_theory "gsu-ax";
force_new_theory "GSU";
new_parent "gsu-fun";
new_parent "gsu-ord";
new_parent "gsu-nat";
new_parent "gsu-seq";
force_new_pc "'GSU";
force_new_pc "GSU";

val rewrite_thms = ref ([]:THM list);

merge_pcs ["'gsu-ax", "'gsu-fun"(*, "'gsu-sumprod", "'gsu-fixp", "'gsu-lists"*),"'gsu-ord", "'gsu-nat", "'gsu-seq"]
	"'GSU";
commit_pc "'GSU";
merge_pcs ["rbjmisc", "'GSU"] "GSU";
commit_pc "GSU";
=TEX

%{\raggedright
%\bibliographystyle{fmu}
%\bibliography{rbj,fmu}
%} %\raggedright

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{gsu-ax.th}
\include{gsu-fun.th}
\include{gsu-ord.th}
\include{gsu-nat.th}
\include{gsu-seq.th}
\include{GSU.th}
}%\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
