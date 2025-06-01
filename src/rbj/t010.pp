=IGN
$Id: t010.doc,v 1.22 2012/11/24 20:22:24 rbj Exp $
=TEX
\documentclass[11pt,a4paper]{article}
%\usepackage{latexsym}
%\usepackage{ProofPower}
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

\title{Miscellaneous Tactics}
\author{Roger Bishop Jones}
\date{$ $Date: 2012/11/24 20:22:24 $ $}

\makeindex
\usepackage[unicode]{hyperref}

\begin{document}
\vfill
\maketitle
\begin{abstract}
Several structures providing tactics, tacticals, etc. for theories, forward chaining, backward chaining, theory trawling et.al.
\end{abstract}
\vfill

\begin{centering}

\href{http://www.rbjones.com/rbjpub/pp/doc/t010.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t010.pdf}

$ $Id: t010.doc,v 1.22 2012/11/24 20:22:24 rbj Exp $ $

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

\section{Introduction}

For context and motivation see \cite{rbjt000}.

Several structures are provided, each section below provides a signature and a structure matching the signature (though the code is not listed).

=SML
infix 4 AND_OR_T;
infix 4 AND_OR;
open_theory "basic_hol";
set_pc "basic_hol";
=TEX

To enable the use of square subset and three-bar equivalence (without the compliance tool) the following script is included:

=SML
val _ =	let open ReaderWriterSupport.PrettyNames;
	in add_new_symbols [ (["sqsubseteq2"], Value "⊑", Simple) ]
        end
handle _ => ();
val _ =	let open ReaderWriterSupport.PrettyNames;
	in add_new_symbols [ (["identical2"], Value "≡", Simple) ]
        end
handle _ => ();
=TEX

\section{Sundry Tacticals etc.}

=DOC
signature ⦏RbjTactics1⦎ = sig
=DESCRIBE
A canon is provided for use with backchaining, and an elaboration of the backchaining facilities which is intended to solve certain kinds of goal by repeated backchaining.
=ENDDOC

=DOC
val ⦏pc_canon⦎: string -> CANON -> CANON;
=DESCRIBE
Creates a CANON which executes in a specific proof context.
=ENDDOC

=DOC
val ⦏rule_canon⦎: (THM -> THM) -> CANON;
=DESCRIBE
Converts a rule into a CANON which yeilds a singleton list containing the result of applying the rule to the argument of the CANON.
=ENDDOC

=DOC
val ⦏⇒_T_canon⦎: CANON;
=DESCRIBE
If in $asms ⊢ conc$, $conc$ is a universally quantified implication, then $⇒\_T\_canon (asms ⊢ conc)$ is $[asms ⊢ conc]$, otherwise it is $[asms ⊢ conc ⇒ T]$.
=ENDDOC

=DOC
val ⦏⇔_FC_T⦎: (THM list -> TACTIC) -> THM list -> TACTIC;
=DESCRIBE
For doing forward chaining using $fc\_⇔\_canon$.
=ENDDOC

=DOC
val ⦏all_⇒_intro_canon⦎: CANON;
=DESCRIBE
This is $rule\_canon$ $all\_⇒\_intro$.
=SEEALSO
$rule\_canon$, $all\_⇒\_intro$
=ENDDOC

=DOC
val ⦏abc_canon⦎: CANON;
=DESCRIBE
A CANON for stripping theorems for backward chaining (used by $abc\_tac$ q.v.).
It removes universal quantifiers, splits conjunctions into two, undisharges implications repeatedly until these can no longer be done, then it discarges all the assumptions and closes the result.
=ENDDOC

=DOC
val ⦏abc_tac⦎: THM list -> TACTIC;
val ⦏asm_abc_tac⦎: THM list -> TACTIC;
=DESCRIBE
A backchaining tactic which preprocesses theorems using $abc\_canon$ and then repeatedly backchains, terminating only if the conclusion can be reduced to $T$ and discharged.
The $asm\_$ version uses the assumptions as rules or for reducing the conclusion to $T$.
=ENDDOC

=DOC
val ⦏map_eq_sym_rule⦎ : THM -> THM;
val ⦏list_map_eq_sym_rule⦎ : THM list -> THM list;
val ⦏SYM_ASMS_T⦎ : (THM list -> TACTIC) -> TACTIC;
=DESCRIBE
These are for turning round equations in order to use them for rewriting, when the equation is not at the top level.

$map\_eq\_sym\_rule$ turns round the equations in the conclusion of the theorem, wherever they occur.

$list\_map\_eq\_sym\_rule$ does the same thing to every one of a list of theorems.

$SYM\_ASMS\_T$ $thmltac$ applies $list\_map\_eq\_sym\_rule$ to the list of assumptions and then passes the result to $thmltac$.

=SEEALSO
$eq\_sym\_conv$, $eq\_sym\_rule$
=ENDDOC

=DOC
val ⦏split_pair_conv⦎ : TERM -> THM;
val ⦏split_pair_rewrite_tac⦎ : TERM list -> THM list -> TACTIC;
val ⦏map_uncurry_conv⦎ : CONV;
val ⦏map_uncurry_rule⦎ : THM -> THM;
=DESCRIBE
These facilities are to permit rewriting with the definition of or theorems about functions which take pairs as arguments, and are defined using paired abstraction or pattern matching on pairs.

$split\_pair\_conv$ $⌜tm⌝$ yields the theorem $⊢ tm = (Fst tm, Snd tm)$.

$split\_pair\_rewrite\_tac$, when supplied with a list of terms which have the type of ordered pairs, will expand each occurence of a term in the list to an explicit ordered pair using  $split\_pair\_conv$,
and will then apply $pure\_rewrite\_tac$ to the theorems.

$map\_uncurry\_conv$ takes a term and eliminates all occurences of $Uncurry$ in it by rewriting with the definition and beta reducing the result, and then eliminates all resulting terms of the form $(Fst tm, Snd tm)$ in favour of $tm$.

$map\_uncurry\_rule$ applies $map\_uncurry\_conv$ to the conclusion of a theorem.
The effect is to make a definition or theorem using pair patterns work for rewriting in cases where the argument is not supplied as an explicit pair, {\it provided that a paired abstraction was used in a universal quantification enclosing the equation}.
So if you want to formulate definitions and generalise them with this rule, use paired abstractions in the quantifiers.

=GFT Example
(concl o map_uncurry_rule) (asm_rule ⌜∀x y (v, w)⦁ A (x,y) (v,w) = x=v ∧ y=w⌝);
val it = ⌜∀ x y p⦁ A (x, y) p = x = Fst p ∧ y = Snd p⌝ : TERM
=TEX
=ENDDOC


=DOC
val ⦏rule_asm_tac⦎ : TERM -> (THM -> THM) -> TACTIC;
val ⦏rule_nth_asm_tac⦎ : int -> (THM -> THM) -> TACTIC;
=DESCRIBE
For transforming assumptions in situ.

=GFT Definitions
fun rule_asm_tac term rule = DROP_ASM_T term (strip_asm_tac o rule);
fun rule_nth_asm_tac int rule = DROP_NTH_ASM_T int (strip_asm_tac o rule);
=TEX
=ENDDOC

=DOC
val ⦏try⦎ : ('a -> 'a) -> ('a -> 'a);
=DESCRIBE
Intended for application to rules, but more generally applicable, $try f a$ is $f a$ unless an exception is raised during its evaluation, in which case it is $a$.
=GFT Definition
fun ⦏try⦎ f a = f a handle _ => a;
=TEX
=ENDDOC

=DOC
val ⦏ℝ_top_anf_tac⦎ : TACTIC;
=DESCRIBE
Convert real arithmetic subexpressions of the conclusion of the current goal to normal form.
=GFT Example
set_goal([], ⌜∀x y z:ℝ⦁ z = if x = y then (z +⋎R y) *⋎R x else x *⋎R (z -⋎R y)⌝);
a ℝ_top_anf_tac;
(* *** Goal "" *** *)

(* ?⊢ *)  ⌜∀ x y z⦁ z = (if x = y then x *⋎R y +⋎R x *⋎R z else ~⋎R x *⋎R y +⋎R x *⋎R z)⌝
=TEX
=GFT Definition
val ⦏ℝ_top_anf_tac⦎ = conv_tac (TOP_MAP_C ℝ_anf_conv);
=TEX
=ENDDOC

=DOC
val ⦏COND_CASES_T⦎ : TERM -> THM_TACTIC -> TACTIC;
val ⦏cond_cases_tac⦎ : TERM -> TACTIC;
val ⦏less_cases_conv⦎ : CONV;
val ⦏less_cases_rule⦎ : THM -> THM;
=DESCRIBE
A version of {\it CASES\_T} for use in rewriting conditional goals.
It does a case split assuming the term argument or its denial and then rewrites with that asssumption before applying the thm tactical argument.

A version of {\it cases\_tac} for use in rewriting conditional goals.
It does a case split assuming the argument or its denial and then rewrites with the un-stripped asssumption before stripping it into the assumptions. 
=GFT Example
set_goal([], ⌜x +⋎R y +⋎R z = if x = y ∧ y = z then x *⋎R (ℕℝ 3) else x +⋎R y +⋎R z⌝);
a (cond_cases_tac ⌜x = y ∧ y = z⌝);
(* *** Goal "" *** *)

(*  2 *)  ⌜x = y⌝
(*  1 *)  ⌜y = z⌝

(* ?⊢ *)  ⌜z + z + z = z * 3.⌝
=TEX
=GFT Definition
fun ⦏COND_CASES_T⦎ x tt = CASES_T x (fn y => TRY (rewrite_tac [y]) THEN (tt y));
fun ⦏cond_cases_tac⦎ x = COND_CASES_T x strip_asm_tac;
local 
fun less_suc_n_conv t =  
	let val (_, [m,sn]) = strip_app t;
	    val (_, [n,_]) = strip_app sn;
	in list_∀_elim [m, n] less_plus1_thm
	end;
in val less_cases_conv = (RIGHT_C plus1_conv) THEN_C less_suc_n_conv THEN_TRY_C (RIGHT_C less_cases_conv)
end;
=TEX
=ENDDOC

=SML
end; (* of signature RbjTactics1 *)
=TEX

=SML
structure ⦏RbjTactics1⦎ : RbjTactics1 = struct
=TEX

\ignore{
=SML
fun ⦏pc_canon⦎ string canon = strip_∧_rule o (pc_rule string (list_∧_intro o canon));

fun ⦏rule_canon⦎ rule thm = [rule thm];

fun ⦏⇒_T_canon⦎ thm =
	if is_⇒ ((snd o strip_∀) (concl thm))
	then [thm]
	else [⇒_intro ⌜T⌝ thm];

fun ⦏⇔_FC_T⦎ tac thms = GET_ASMS_T (tac o (fc_rule (flat (map fc_⇔_canon thms))));

val ⦏all_⇒_intro_canon⦎: CANON = rule_canon all_⇒_intro;

val ⦏abc_canon⦎ =
	REPEAT_CAN (
		simple_∀_rewrite_canon
		ORELSE_CAN (rule_canon undisch_rule)
		ORELSE_CAN ∧_rewrite_canon)
	THEN_CAN all_⇒_intro_canon
	THEN_CAN ⇒_T_canon;

fun ⦏abc_tac⦎ thml =
	let val thms = flat (map abc_canon thml)
	in REPEAT (accept_tac t_thm ORELSE (bc_tac thms))
	end;

fun ⦏asm_abc_tac⦎ thml (asms, conc) =
	abc_tac (thml @ (map asm_rule asms)) (asms, conc);
=TEX
Some functions which turn round equations before using them.
=SML
fun ⦏map_eq_sym_rule⦎ thm = conv_rule (ONCE_MAP_C eq_sym_conv) thm;
fun ⦏list_map_eq_sym_rule⦎ thms = map (fn th => map_eq_sym_rule th handle _=> th) thms;
fun ⦏SYM_ASMS_T⦎ tltt = GET_ASMS_T (tltt o list_map_eq_sym_rule);
=TEX
For rewriting with definitions which abstract over pairs:

=SML
fun ⦏split_pair_conv⦎ t = prove_rule [] ⌜ⓜt⌝ = (Fst ⓜt⌝, Snd ⓜt⌝)⌝;
fun ⦏split_pair_rewrite_tac⦎ tl thms =
	pure_once_rewrite_tac (map split_pair_conv tl)
	THEN TRY (pure_rewrite_tac thms);

local	val uncurry_thm = tac_proof (
		([], ⌜∀f⦁ Uncurry f = λp⦁ f (Fst p) (Snd p)⌝),
		rewrite_tac [ext_thm, uncurry_def]);
	val pair_lemma = nth 2 (strip_∧_rule pair_ops_def);
	val uc_conv = (simple_eq_match_conv1 uncurry_thm)
		THEN_C (λ_C ((RATOR_C β_conv) THEN_C β_conv));
in
	val ⦏map_uncurry_conv⦎ = MAP_C uc_conv THEN_C pure_rewrite_conv [pair_lemma]
end;

val ⦏map_uncurry_rule⦎ = conv_rule map_uncurry_conv;

fun ⦏rule_asm_tac term⦎ rule = DROP_ASM_T term (strip_asm_tac o rule);
fun ⦏rule_nth_asm_tac⦎ int rule = DROP_NTH_ASM_T int (strip_asm_tac o rule);

fun ⦏try⦎ f a = f a handle _ => a;
=TEX
A tactic for normal form conversion of real expressions.
=SML
val ⦏ℝ_top_anf_tac⦎ = conv_tac (TOP_MAP_C ℝ_anf_conv);
=TEX
A case splitting tactic for conditional goals.
=SML
fun ⦏COND_CASES_T⦎ x tt = CASES_T x (fn y => TRY (rewrite_tac [y]) THEN (tt y));
fun ⦏cond_cases_tac⦎ x = COND_CASES_T x strip_asm_tac;
local 
   fun less_suc_n_conv t =  
	let val (_, [m,sn]) = strip_app t;
	    val (_, [n,_]) = strip_app sn;
	in list_∀_elim [m, n] less_plus1_thm
	end;
   in fun ⦏less_cases_conv⦎ t = ((RIGHT_C plus1_conv) THEN_C less_suc_n_conv THEN_TRY_C (RIGHT_C less_cases_conv)) t
end;
val ⦏less_cases_rule⦎ = conv_rule less_cases_conv;
=TEX
}%ignore

=SML
end; (* of structure RbjTactics1 *)
=TEX

\section{Stripping With Failure}

=DOC
signature ⦏StripFail⦎ = sig
=DESCRIBE
This signature provides facilities for stripping assumptions which fail if the current goal remains unchanged.
This is so that tactics which generate new assumptions, e.g. $fc\_tac$ can be repeated until no new assumptions are generated.
=ENDDOC

=DOC
val ⦏check_asm_tac1⦎ : THM -> TACTIC;
=DESCRIBE
$check\_asm\_tac1$ is a similar to $check\_asm\_tac$ but will fail rather than leave the goal unchanged.

$check\_asm\_tac1\,thm$ checks the form of the theorem, $thm$,
and then takes the first applicable action from the following table:

{\centering
\begin{tabular}{|l|p{4in}|}\hline
$thm$ & action \\ \hline
$Γ ⊢ t$ & proves goal if its conclusion is $t$ \\ \hline
$Γ ⊢ T$ & as $fail\_tac$ \\ \hline
$Γ ⊢ F$ & proves goal\\ \hline
$Γ ⊢ ¬t$ & proves goal if $t$ in assumptions, fails if $¬t$ is in assumptions, else as $asm\_tac$\\ \hline
$Γ ⊢ t$ & proves goal if $¬t$ in assumptions, fails if $t$ is in assumptions, else as $asm\_tac$\\ \hline
\end{tabular}}

During the search through the assumptions in the last two cases,
$check\_asm\_tac1$ also checks to see whether any of the assumptions is
equal to the conclusion of the goal, and if so proves the goal.
It also checks to see if the conclusion of the theorem
is already an assumption, in which case the tactic fails.
When all the assumptions have been examined, if none of the
above actions is applicable, the conclusion of the theorem is
added to the assumption list.

=USES
Tactic programming.
=SEEALSO
$check\_asm\_tac$, $strip\_asm\_tac1$.
=ENDDOC

=DOC
val ⦏strip_asm_tac1⦎ : THM -> TACTIC;
=DESCRIBE
$strip\_asm\_tac1$ is a tactic for stripping down or otherwise transforming a theorem before adding it into the assumptions.

The transformations it undertakes are determined primarily by the current proof context which contains a conversion for stripping assumptions, but there are in addition a small number of effects which cannot be achieved by a conversion and are built into this tactic.

First the current stripping conversion will be applied repeatedly until it no longer applies.

Then the following simplification techniques will be tried.
Using $sat$ as an abbreviation for $strip\_asm\_tac$:
=GFT
sat (⊢ a ∧ b) 			→	sat (⊢ a) THEN sat (⊢ b)
sat (∃x⦁a)			→	sat (a[x'/x] ⊢ a[x'/x])
sat (⊢ a ∨ b)({Γ} t)		→	sat (a ⊢ a) ({Γ} t) ; sat (b ⊢ b) ({Γ} t)
=TEX

The effect is to break conjunctions into two separate theorems, to do a case split on disjunctions and to skolemise existentials.

After all of the available transformation techniques have been exhausted $strip\_asm\_tac$ then passes the theorems to $check\_asm\_tac1$ (q.v.) to discharge the goal or to generate additional assumptions.
=SEEALSO
$STRIP\_THM\_THEN$, used to implement this function.
$check\_asm\_tac1$, $strip\_tac$, $strip\-\_asm\-\_conv$.
=ENDDOC

=DOC
val ⦏strip_asms_tac1⦎ : THM list -> TACTIC;
=DESCRIBE
$strip\_asms\_tac1$ is a tactic for stripping down or otherwise transforming a list of theorems before adding them into the assumptions.

The effect is similar to applying $strip\_asm\_tac1$ to each of the theorems, except that it will fail only if every application of $strip\_asm\_tac1$ fails, i.e. if the total effect is null.

=SEEALSO
$STRIP\_THM\_THEN1$, used to implement this function.
$check\_asm\_tac1$, $strip\_tac$, $strip\-\_asm\-\_conv$.
=ENDDOC

=DOC
val ⦏AND_OR_T⦎ : TACTIC * TACTIC -> TACTIC;
val ⦏AND_OR⦎ : TACTIC * TACTIC -> TACTIC;
=DESCRIBE
$t1\ AND\_OR\_T\ t2$ has the same effect as $((TRY\ t1)\ THEN\ t2) ORELSE t1$ but is faster.
$AND\_OR$ is an alias for $AND\_OR\_T$.
=SEEALSO
$THEN$, $ORELSE$, $TRY$
=ENDDOC

=DOC
val ⦏∧_THEN_T1⦎ : (THM -> TACTIC) -> (THM -> TACTIC);
val ⦏∧_THEN1⦎ : (THM -> TACTIC) -> (THM -> TACTIC);
=DESCRIBE
Similar in effect to $∧\_THEN$ but will fail only if both the conjuncts fail.

A theorem tactical to apply a given theorem tactic to both conjuncts of 
a theorem of the form $Γ\ ⊢\ t1\ ∧\ t2$.
=GFT
∧_THEN1 thmtac (Γ ⊢ t1 ∧ t2) = thmtac (Γ ⊢ t1) AND_OR thmtac (Γ ⊢ t2)
=TEX
=SEEALSO
$∧\_THEN$
=ENDDOC

=DOC
val ⦏STRIP_THM_THEN1⦎ : THM_TACTICAL;
=DESCRIBE
$STRIP\_THM\_THEN1$ provides a general purpose way of
stripping or transforming theorems before
using them in a tactic proof.
$STRIP\_THM\_THEN1$ attempts to apply
the conversion held for the function in the current proof context, which is
extracted by $current\_ad\_st\_conv$.
to rewrite the theorem.
If that fails it attempts to apply a theorem tactical from the following list (in order):
=GFT
∧_THEN1,			∨_THEN,		SIMPLE_∃_THEN
=TEX
The conversion in the current proof context
got by $current\_ad\_st\_conv$ (q.v.)
is derived by applying $eqn\_cxt\_conv$ to an equational context in the proof context extracted by $get\_st\_eqn\_cxt$.

The function is partially evaluated with only the
theorem tactic and theorem arguments.
=SEEALSO
$STRIP\_THM\_THEN$
=ENDDOC

=DOC
val ⦏LIST_AND_OR_T⦎ : TACTIC list -> TACTIC;
=DESCRIBE
$SOME\_T$ is similar to $EVERY\_T$ except that it fails only if all the tactics fail.

$SOME\_T$ $tlist$ is a tactic that applies the head of $tlist$ to its subgoal, and
recursively applies the tail of $tlist$ to each resulting subgoal.
If any application of a tactic fails then the failure is ignored, but if no applications succeed then $SOME\_T$ will fail.

$SOME$ is NOT an alias for $SOME\_T$ (its a already a constructor).
$SOME$ $[]$ is equal to $fail\_tac$.
=EXAMPLE
=GFT
SOME [∀_tac, ∧_tac, ∀_tac] 
	is equivalent to
∀_tac AND_OR ∧_tac AND_OR ∀_tac
=TEX
=SEEALSO
$EVERY\_T$
=ENDDOC

=DOC
val ⦏MAP_LIST_AND_OR_T⦎ : ('a -> TACTIC) -> 'a list -> TACTIC;
val ⦏MAP_LIST_AND_OR⦎ : ('a -> TACTIC) -> 'a list -> TACTIC;
=DESCRIBE
$MAP\_LIST\_AND\_OR\_T$ is the same as $MAP\_EVERY\_T$ except that it will fail only if no resulting application of a tactic succeeds.

$MAP\_LIST\_AND\_OR\_T$ $mapf$ $alist$ maps $mapf$ over $alist$,
and then applies the resulting list of tactics to the goal
in sequence (in the same manner as $SOME$, q.v.).
$MAP\_LIST\_AND\_OR$ is an alias for $MAP\_LIST\_AND\_OR\_T$.
=SEEALSO
$MAP\_EVERY$
=ENDDOC

=SML
end; (* of signature StripFail *)
=TEX

=SML
structure StripFail : StripFail = struct
=TEX

\ignore{
=SML
fun ⦏check_asm_tac1⦎ (thm : THM) : TACTIC = (fn gl as (seqasms, conc) =>
	let	val t = concl thm;
	in	if t ~=$ conc
		then accept_tac thm
		else if is_t t
		then fail_tac
		else if is_f t
		then f_thm_tac thm
		else if is_¬ t
		then	let	val t' = dest_¬ t;
				fun aux (asm :: more) = (
					if t ~=$ asm
					then fail_tac
					else if asm ~=$ t'
					then accept_tac (¬_elim conc (asm_rule asm) thm)
					else if asm ~=$ conc
					then accept_tac (asm_rule asm)
					else aux more
				) | aux [] = asm_tac thm;
			in	aux seqasms
			end
		else	let	fun aux (asm :: more) = (
					if t ~=$ asm
					then fail_tac
					else if is_¬ asm andalso (dest_¬ asm) ~=$ t
					then accept_tac (¬_elim conc thm (asm_rule asm))
					else if asm ~=$ conc
					then accept_tac (asm_rule asm)
					else aux more
					) | aux [] = asm_tac thm;
			in	aux seqasms
			end
	end	gl
);
=TEX

=SML
fun ((tac1 : TACTIC) ⦏AND_OR_T⦎ (tac2 : TACTIC)) : TACTIC = (fn gl =>
	let	val (fok, (sgs1, pf)) = (true, tac1 gl) handle (Fail _) => (false, id_tac gl)
	in	let val (sgs2pfs2) = (map tac2 sgs1);
		in	(flat (map fst sgs2pfs2),
			pf o map_shape (map (fn (sgs, pf) => (pf, length sgs))sgs2pfs2))
		end handle (Fail _) =>
			if fok then (sgs1, pf) else fail_tac gl
	end
);
val op ⦏AND_OR⦎ = op AND_OR_T;
=TEX
=SML
fun ⦏∧_THEN_T1⦎ (ttac : THM -> TACTIC) : THM -> TACTIC = (fn thm => 
	let	val thm1 = ∧_left_elim thm;
		val thm2 = ∧_right_elim thm;
	in	ttac thm1 AND_OR ttac thm2
	end
	handle ex => divert ex "∧_left_elim" "∧_THEN1" 28032 
		[fn () => string_of_thm thm]
);
val ⦏∧_THEN1⦎ = ∧_THEN_T1;
=TEX

=SML
val ⦏STRIP_THM_THEN1⦎ : THM_TACTICAL = (fn ttac:THM_TACTIC => 
	fn thm :THM =>
	(FIRST_TTCL[CONV_THEN (current_ad_st_conv()),
		∧_THEN1, 
		∨_THEN, 
		SIMPLE_∃_THEN]
	ORELSE_TTCL
		FAIL_WITH_THEN "STRIP_THM_THEN1" 28003 
			[fn () => string_of_thm thm])
	ttac
	thm
);
=TEX
=SML
fun ⦏LIST_AND_OR_T⦎ (tacs : TACTIC list) :  TACTIC = (fn gl =>
	(fold (op AND_OR) tacs fail_tac) gl
);
=TEX
=SML
fun ⦏MAP_LIST_AND_OR_T⦎ (tacf : 'a -> TACTIC) (things : 'a list) : TACTIC = (
	LIST_AND_OR_T (map tacf things)
);
=TEX
=SML
val ⦏MAP_LIST_AND_OR⦎ : ('a -> TACTIC) -> 'a list -> TACTIC = MAP_LIST_AND_OR_T;
=TEX

=SML
val ⦏strip_asm_tac1⦎ = REPEAT_TTCL STRIP_THM_THEN1 check_asm_tac1;
val ⦏strip_asms_tac1⦎ = MAP_LIST_AND_OR strip_asm_tac1;
=TEX


}%ignore

=SML
end; (* of structure StripFail *)
=TEX

\section{Theories, Proof Contexts and Consistency}

\subsection{Specifications}

=DOC
signature ⦏PreConsisProof⦎ = sig
=DESCRIBE
This signature provide the wherewithal to conduct a consistency proof for a HOL constant specification before introducing the specification, so that the specification can be seen to be consistent and will appear in the theory listing as if no consistency proof had been necessary.

The signature also provides some procedures to incorporate exception handling require when a document is required to create or to recreate a theory, and must therefore first delete things which are not necessarily present, similarly for proof contexts and other functions for manipulating proof contexts.
=ENDDOC

\subsubsection{Doing Consistency Proofs before Axiomatic Descriptions}

=DOC
val ⦏save_cs_∃_thm⦎ : THM -> THM;
=DESCRIBE
This function may be used to provide to the system a theorem which establishes the consistency of a HOL constant specification about to be introduced.

To avoid getting theory listings in which the definitions of some constants are given using $ConstSpec$ I like to do any necessary consistency proofs before introducing the constant specification which needs them.
For this to do any good, the automatic consistency prover has to know that I done it.

If used in conjunction with the partial proof context $'savedthm\_cs\_∃\_conv$ the theorem will be used to establish the consistency of the specification avoid the need to place a consistency caveat on the stored form of the specification in the theory.
=SEEALSO
=ENDDOC

=DOC
(* Proof Context: ⦏'savedthm_cs_∃_proof⦎ *)
=DESCRIBE
This partial proof context contains only the existence prover $savedthm\_cs\_∃\_conv$ which attempts to ``prove'' the consistency of a specification by referring to a standard location in which the consistency theorem may have previously been saved.
=SEEALSO
$savedthm\_cs\_∃\_conv$, $save\_cs\_∃\_thm$
=ENDDOC

\subsubsection{Recursive Definitions without Constructors}

=DOC
val ⦏CombI_prove_∃_rule⦎ : string -> TERM -> THM;
=DESCRIBE
The provision for recursive definitions to be proven consistent is designed for recursion of types which have constructors, and is not therefore directly applicable to definitions by transfinite recursion in set theory.

However, with a small hack it can be applied to such definitions.

The basic observation is that it will work with a dummy constructor ($CombI$ will do) inserted in the place where a real constructor would normally be.
There are two problems with this.
The first is that you have to put this constructor in your recursive definitions where they look pretty stupid.
The second is that only one recursion pattern can be used with any dummy constructor, so if you want more than one recursion principle to be available you have to invent more dummy constructors, and your spec will look really stupid.

The fixes for these problemettes are, firstly to get the existence claim before entering the definition, for the definition with the constructor in it, and then rewrite it to eliminate the constructor and save it so that when you make the definition without the constructor the consistency result is to hand.
The second problem is fixed by having a distinct partial proof context for each recursion principle which uses the dummy constructor so that only one recursion principle using the dummy constructor is in scope when the consistency proof is obtained.

A special rule is made available here to simplify the operation of this procedure.

The basic method is as follows (presumes some familiarity with the existing mechanisms):

\begin{itemize}

\item prove a recursion theorem corresponding to the pattern of recursion under consideration, but for the argument to the function being defined on which recursion is taking place add the ``constructor'' \emph{CombI}.

\item create a partial proof context just for the recursion principle (see: $add\_∃\_cd\_thms$).

\item use $CombI\_prove\_∃\_rule$ to obtain and save the required consistency result, supplying as a parameter to it the name of a partial proof context containing just the relevant recursion principle.
This function expects to be given the term to be used for the definition except with the constructor \emph{CombI} applied.
It will save the result using $save\_cs\_∃\_thm$.

\item do the definition in the desired form (i.e. without the dummy constructor).

\end{itemize}

=SEEALSO
$add\_∃\_cd\_thm$,  $save\_cs\_∃\_thm$
=ENDDOC

\subsubsection{Existential Proofs}

=DOC
val ⦏∃_⇒_conv⦎ : CONV;
=DESCRIBE
Conversion that pushes an existential through an implication
where the bound variable is free in the antecedent:
=ENDDOC

=DOC
val ⦏prove_∃_⇒_conv⦎ : CONV;
=DESCRIBE
Conversion to prove the result of applying the basic existence proving conversion to a conditional function definition using $∃\_⇒\_conv$ to push the existential for the function value through the condition and then discarding the antecedent.
=ENDDOC

\subsubsection{Force New Theory}

=DOC
val ⦏force_new_theory⦎ : string -> unit;
=DESCRIBE
This is just to save the exception handling which otherwise has to appear at the top of every document which creates a \Product theory.

It deletes the old theory (if present, from your previous build, by using $force\_delete\_theory$) and all its children and starts the theory afresh.
=SEEALSO
$force\_delete\_theory$, $force\_new\_pc$
=ENDDOC

\subsubsection{Proof Contexts}

=DOC
val ⦏force_new_pc⦎ : string -> unit;
=DESCRIBE
This is just to save the exception handling which otherwise has to appear at the top of every document which creates a \Product proof context.

It deletes the old proof context (if present, from your previous build, using $delete\_pc$) and starts the proof context afresh.
=SEEALSO
$force\_new\_theory$, $delete\_pc$
=ENDDOC

=DOC
val ⦏add_pc_thms⦎ : string -> THM list -> unit;
val ⦏add_pc_thms1⦎ : string -> THM list -> unit;
=DESCRIBE
These function allows you to add theorems to a proof context.
{\it add\_pc\_thms} adds them for all three purposes (stripping conclusions and assumptions and rewriting).
{\it add\_pc\_thms1} omits assumption stripping.
=SEEALSO
$add\_rw\_thms$, $add\_sc\_thms$, $add\_st\_thms$
=ENDDOC

\subsubsection{Output Stats}

=DOC
val ⦏output_stats⦎ : string -> unit;
=DESCRIBE
Writes the current values of the profiling statistics to a file as a LaTeX table.
=SEEALSO
$get\_stats$
=ENDDOC


=SML
end; (* of signature PreConsisProof *)
=TEX

\subsection{Implementation}

=SML
structure ⦏PreConsisProof⦎ : PreConsisProof = struct
=TEX

\subsection{Partial Primitive Recursive Definitions}

This functionality is now to be incorporated into \Product and is therefore removed (a patch has been applied).

For each item of clausal definition material we hold:
\begin{enumerate}
\item
The list of data constructor recognisers.
These are the generic terms which must be matchable to the actual argument.
\item
The number of free variables there should be in the use of the constructor (e.g. 2 for $Cons$, 0 for $Nil$).
\item
An instance of the most general type of the function's argument.
\item
A list of dummy arguments for each ``constructor'', to allow dummy
conjuncts to be created.
\item
The actual theorem.
The theorem is an equation, whose LHS is of the form:
\begin{itemize}
\item
Universally quantify by one predicate per ``constructor'',
\item
Existentially quantify by function, $f$,
\item
one conjunct per constructor, in same order as predicates.
\item
Each conjunct will universally quantified in the order that
the the free variables of the subterm to which $f$ is first applied, that is a recognised argument by the data constructor
recogniser.
\item
The body of the conjunct will be the associated predicate
applied to each available use of $f$ and its arguments,
the first being the recognised argument.
\end{itemize}
 
\end{enumerate}

=SML
val lthy = get_current_theory_name ();
val _ = open_theory "basic_hol";
val _ = push_merge_pcs ["'propositions","'paired_abstractions"];
=TEX
To make certain functions independent of proof context changes we need to create a (temporary) build proof context equivalent
to the supplied ``predicates'', in the fields that matter.
As we have not commited the sources, we have to do this the hard way:
=SML
fun lget x = fst(hd x);
val _ = new_pc "build_predicates";
val _ = set_rw_eqn_cxt ((lget o get_rw_eqn_cxt) "'propositions" @
		(lget o get_rw_eqn_cxt) "'paired_abstractions")
		"build_predicates";
val _ = set_sc_eqn_cxt ((lget o get_sc_eqn_cxt) "'propositions" @
		(lget o get_sc_eqn_cxt) "'paired_abstractions")
		"build_predicates";
val _ = set_st_eqn_cxt ((lget o get_st_eqn_cxt) "'propositions" @
		(lget o get_st_eqn_cxt) "'paired_abstractions")
		"build_predicates";
val _ = set_rw_canons ((lget o get_rw_canons) "'propositions" @
		(lget o get_rw_canons) "'paired_abstractions")
		"build_predicates";
=TEX

Flatten a paired structure:
=SML
val ⦏strip_pair⦎ :TERM -> TERM list = strip_leaves dest_pair;
=TEX
Flatten a conjunction structure ($strip_∧$ only flattens to the right):
=SML
val ⦏full_strip_∧⦎ : TERM -> TERM list = strip_leaves dest_∧;
=TEX

We wish to ``mark'' some terms, to prevent stripping going too far.
We use $pp'TS$ as a marker.

``mark'' a term:
=SML
local
	val ci = ⌜pp'TS:BOOL → BOOL⌝;
in
fun ⦏mark⦎ (tm:TERM):TERM = mk_app(ci,tm)
end;
=TEX

=SML
val _ = delete_pc "build_predicates";
val _ = pop_pc();
val _ = open_theory lthy;
=TEX

Conversion (written by rda) that pushes an existential through an implication
where the bound variable is free in the antecedent:

=SML
val ⦏∃_⇒_conv⦎ : CONV = (
	let	val ⦏∃_⇒_lemma⦎ = prove_rule[]
			⌜∀p q⦁ (∃f⦁q ⇒ p f) ⇔ (q ⇒ ∃f⦁p f)⌝;
	in	fn tm =>
		let	val (f, b) = dest_simple_∃ tm;
			val (q, pf) = dest_⇒ b;
			val p = mk_simple_λ(f, pf);
			val thm1 = list_∀_elim[p, q] ∃_⇒_lemma;
			val thm2 = conv_rule(LEFT_C(BINDER_C (RIGHT_C β_conv))) thm1;
			val thm3 = conv_rule(RIGHT_C(RIGHT_C(BINDER_C β_conv))) thm2;
			val thm4 = simple_eq_match_conv thm3 tm;
		in	thm4
		end
	end
);
=TEX

Conversion (written by rda) to prove the result of applying the basic existence proving conversion to a conditional function definition using the above conversion to push the existential for the function value through the condition and then discarding the antecedent.

=SML
val ⦏prove_∃_⇒_conv⦎ : CONV = (fn tm =>
	let	val thm1 = tac_proof (([], tm),
				REPEAT strip_tac
			THEN	conv_tac ∃_⇒_conv
			THEN	⇒_T discard_tac
			THEN	conv_tac basic_prove_∃_conv);
		val thm2 = ⇔_t_intro thm1;
	in	thm2
	end
);
=TEX

\ignore{
=SML
fun ⦏force_new_theory⦎ name =
  let val _ = force_delete_theory name handle _ => ();
  in new_theory name
end;
=TEX

=SML
fun ⦏force_new_pc⦎ name =
  let val _ = delete_pc name handle _ => ();
  in new_pc name
end;
=TEX

=SML
fun ⦏add_pc_thms⦎ pc thms =
		(add_rw_thms thms pc;
		add_sc_thms thms pc;
 		add_st_thms thms pc);
=TEX

=SML
fun ⦏add_pc_thms1⦎ pc thms =
		(add_rw_thms thms pc;
		add_sc_thms thms pc);
=TEX
}

A new value of type $ref THM$ called $saved\_cs\_∃\_thm$ is used to store consistency results.

=SML
val saved_cs_∃_thm = ref t_thm;
=TEX

=SML
fun save_cs_∃_thm thm = (saved_cs_∃_thm := thm; thm);
=TEX

I also have a special partial proof context with a consistency prover which knows to look for the consistency proof in this special place.
This is the consistency prover:

=SML
fun ⦏savedthm_cs_∃_conv⦎ x =
	if x =$ (concl(!saved_cs_∃_thm))
	then (⇔_t_intro (!saved_cs_∃_thm)) handle _ => (* eq_ *) refl_conv x
	else (* eq_ *) refl_conv x;
=TEX


Store the above in a proof context:

=SML
val _ = force_new_pc ⦏"'prove_∃_⇒_conv"⦎;
val _ = set_cs_∃_convs [prove_∃_⇒_conv, ONCE_MAP_C (pure_once_rewrite_conv [let_def] THEN_C (MAP_C β_conv))] "'prove_∃_⇒_conv";
val _ = commit_pc "'prove_∃_⇒_conv";
=TEX

=SML
val _ = force_new_pc ⦏"'savedthm_cs_∃_proof"⦎;
val _ = set_cs_∃_convs [prove_∃_⇒_conv, savedthm_cs_∃_conv] "'savedthm_cs_∃_proof";
val _ = set_pr_conv basic_prove_conv "'savedthm_cs_∃_proof";
val _ = set_pr_tac basic_prove_tac "'savedthm_cs_∃_proof";
val _ = commit_pc "'savedthm_cs_∃_proof";
=IGN
current_ad_cs_∃_conv();
=TEX

=SML
local	val lthy = get_current_theory_name ();
	val _ = open_theory "combin";
	val CombI_def = get_spec ⌜CombI⌝;
	val _ = open_theory lthy
in
fun CombI_prove_∃_rule pc tm =
	let val tmthm = pc_rule pc basic_prove_∃_rule tm
	in save_cs_∃_thm (rewrite_rule [CombI_def] tmthm)
	end
end;
=TEX


\ignore{
=IGN
local fun format_stat (name, value) = "\\statentry{" ^ name ^ "," ^ (Int.toString value) ^ "}\n";
in fun output_stats filename = 
	let val out_strm = open_out filename
	    and stats = get_stats();
	    val total = Int.toString (fold (fn ((s,i1),i2) => i1+i2) stats 0)
	    val	output_string = concat(map format_stat stats @ ["\\stattotal{" ^ total ^ "}"])
	in output (out_strm, "=TEX\n");
	   output (out_strm, output_string);
	   close_out out_strm
	end;
end;

local fun format_stat (name, value) = "$" ^ name ^ "$ & " ^ (Int.toString value) ^ "\\\\\n";
in fun output_stats filename = 
	let val out_strm = open_out filename
	    and stats = get_stats();
	    val total = fold (fn ((s,i1),i2) => i1+i2) stats 0
	    val	output_string = concat(map format_stat (stats @ [("Total", total)]))
	in output (out_strm, "=TEX\n");
	   output (out_strm, output_string);
	   close_out out_strm
	end;
end;
=SML
local fun format_stat (name, value) = "$" ^ name ^ "$ & " ^ (Int.toString value) ^ "\\\\\n";
in fun output_stats filename = 
	let val out_strm = open_out filename
	    and stats = get_stats();
	    val total = Int.toString (fold (fn ((s,i1),i2) => i1+i2) stats 0)
	    val	output_string = concat(map format_stat stats) ^ "\\hline\nTotal & " ^ total ^ "\\\\\\hline"
	in output (out_strm, "=TEX\nInference Rule & Count\\\\\\hline\n");
	   output (out_strm, output_string);
	   close_out out_strm
	end;
end;

=IGN
fun apfops opf (op1, op2) =
	if is_Nil op1
	then force_value op2
	else	if is_Nil op2
		then force_value op1
		else opf (force_value op1, force_value op2); 

fun s_op opf sd1 sd2 =
	let	val sdom = (map fst sd1) cup (map fst sd2);
		val oppairs = map (fn x => (x, (lassoc5 sd1 x, lassoc5 sd2 x))) sdom
	in map (fn (s, i) => (s, apfops opf i)) oppairs
	end; 

fun aps f t =
	let	val oldstats = get_stats();
	    	val newstats = (init_stats(); f t; get_stats())
	in	set_stats(s_op op+ oldstats newstats); newstats
	end; 

=IGN
output_stats "stats_test_file.doc";
=TEX

}%ignore

=SML
end; (* of structure PreConsisProof *)
=TEX

\section{Unifying Forward Chaining}

\subsection{Specifications}

=DOC
signature ⦏UnifyForwardChain⦎ = sig
=DESCRIBE
This is the signature of facilities for forward chaining based on unification rather than matching.
=ENDDOC

=DOC
val ⦏simple_⇒_unify_mp_rule1⦎ : THM -> THM -> THM ;
=DESCRIBE
A unifying Modus Ponens rule for an implicative theorem.
=FRULE 1 Rule
⇒_unify_mp_rule1
├
Γ1 ⊢ ∀ x1 ...⦁ t1 ⇒ t2;
Γ2 ⊢ ∀ y1 ...⦁ t1'
├
Γ1 ∪ Γ2 ⊢ ∀ z1 ...⦁ t2'
=TEX
where $t1'$ is unifiable with $t1$.
Type instantiation and substitution is permitted for the $x⋎i$ in $t1$, the and $y⋎i$ in $t1'$ and instantiation of the type variables in $t1$ which do not occur in Γ1 and those in $t1'$ which do not occur in Γ2.
$t2'$ is obtained from $t2$ by applying to it the substitution to $t1$ required for its unification.
The $z⋎i$ will be the variables free in t2' which were not previously free either in $t2$ or $t1'$.
No type instantiation or substitution will occur in the assumptions of either theorem.

Pairs are not supported in the bindings.
=FAILURE
7044	Cannot match ?0 and ?1
7045	?0 is not of the form `Γ ⊢ ∀ x1 ... xn ⦁ u ⇒ v`
=ENDDOC

=DOC
val ⦏⇒_unify_mp_rule1⦎ : THM -> THM -> THM ;
=DESCRIBE
A matching Modus Ponens rule for an implicative theorem, supporting paired abstraction.
=FRULE 1 Rule
⇒_unify_mp_rule1
├
Γ1 ⊢ ∀ x1 ...⦁ t1 ⇒ t2;
Γ2 ⊢ ∀ y1 ...⦁ t1'
├
Γ1 ∪ Γ2 ⊢ ∀ z1 ...⦁ t2'
=TEX
where $t1'$ is unifiable with $t1$.
Type instantiation and substitution is permitted for the $x⋎i$ in $t1$, the and $y⋎i$ in $t1'$ and instantiation of the type variables in $t1$ which do not occur in Γ1 and those in $t1'$ which do not occur in Γ2.
$t2'$ is obtained from $t2$ by applying to it the substitution to $t1$ required for its unification.
The $z⋎i$ will be the variables free in t2' which were not previously free either in $t2$ or $t1'$.
No type instantiation or substitution will occur in the assumptions of either theorem.

Pairs are supported in the bindings.
=FAILURE
7044	Cannot match ?0 and ?1
7045	?0 is not of the form `Γ ⊢ ∀ x1 ... xn ⦁ u ⇒ v`
=ENDDOC

=DOC
val ⦏unify_forward_chain_rule⦎ : THM list -> THM list -> THM list;
val ⦏ufc_rule⦎ : THM list -> THM list -> THM list;
=DESCRIBE
This is a rule which uses a list of possibly universally
quantified implications and a list of
other theorems to infer new theorems, using
=INLINEFT
⇒_unify_mp_rule1
. (
=INLINEFT
ufc_rule
=TEX
\ is an alias for
=INLINEFT
unify_forward_chain_rule
=TEX
.)
=INLINEFT
ufc_rule imps ants
=TEX
\ returns the list of all theorems which may be derived by
applying
=INLINEFT
⇒_unify_mp_rule1
=TEX
\ to a theorem from $imps$ and one from $ants$.
As a special case, if any theorem to be returned is determined
to have $⌜F⌝$ as its conclusion, the first such found wil be returned as a singleton list.
In order to work well in conjunction with
=INLINEFT
fc_canon
=TEX
\ and
=INLINEFT
ufc_tac
=TEX
\ the theorems returned by
=INLINEFT
⇒_unify_mp_rule1
=TEX
\ are transformed as follows:

\begin{enumerate}
\item
Theorems of the form:
=INLINEFT
⊢ ∀ x⋎1 ...⦁ t⋎1 ⇒ t⋎2 ⇒ ... ⇒ ¬t⋎k ⇒ F
=TEX
\ have their final implication changed to
=INLINEFT
t⋎k
=TEX
.
\item
Theorems of the form:
=INLINEFT
⊢ ∀ x⋎1 ...⦁ t⋎1 ⇒ t⋎2 ⇒ ... ⇒ t⋎k ⇒ F
=TEX
\ have their final implication changed to
=INLINEFT
⇒\¬t⋎k
=TEX
.
\item
All theorems are universally quantified over all the variables which
appear free in their conclusions but not in their assumptions
(using
=INLINEFT
all_∀_intro
=TEX
).
\end{enumerate}
Note that the use of
=INLINEFT
⇒_unify_mp_rule1
=TEX
\ gives some control over the number of results generated, since
variables which appear free in $imps$ are not considered as candidates
for instantiation.

The rule does not check that the theorems in its first argument
are (possible universally) quantified implications.
Theorems which are not of this form will be ignored.
=SEEALSO
$unify\_forward\_chain\_tac$, $forward\_chain\_canon$.
=ENDDOC

=DOC
val ⦏UFC_T1⦎ :
	(THM -> THM list) -> (THM list -> TACTIC) -> THM list -> TACTIC;
val ⦏ALL_UFC_T1⦎ :
	(THM -> THM list) -> (THM list -> TACTIC) -> THM list -> TACTIC;
val ⦏ASM_UFC_T1⦎ : 
	(THM -> THM list) -> (THM list -> TACTIC) -> THM list -> TACTIC;
val ⦏ALL_ASM_UFC_T1⦎ : 
	(THM -> THM list) -> (THM list -> TACTIC) -> THM list -> TACTIC;
=DESCRIBE
These are tacticals which use theorems whose conclusions are
implications, or from which implications can be derived,
to reason forwards from the assumptions of a goal.

The description of 
=INLINEFT
ufc_tac
=TEX
\ should be consulted for the basic forward chaining algorithms used.
The significance of the final argument and of the presence or absence of
=INLINEFT
ASM
=TEX
\ and
=INLINEFT
ALL
=TEX
\ in the name is exactly as for
=INLINEFT
fc_tac
=TEX
\ and its relatives.

The tacticals allow variation of the canonicalisation function
used to obtain implications from the argument theorems and of
the tactic generating function used to process the theorems derived
by the forward inference.
The canonicalisation function to use is the first argument
and the tactic generating function is the second.
(Related tacticals with names ending in
=INLINEFT
T
=TEX
\ rather than
=INLINEFT
T1
=TEX
\ are also available for the simpler case when
wants to use the same canonicalisation function as
=INLINEFT
fc_tac
=TEX
\ and just to vary the tactic generating function.)

\paragraph{Examples}

If the theorem argument comprises only implications
which are to be used without canonicalisation, one might use:
=INLINEFT
UFC_T1 id_canon (MAP_LIST_AND_OR strip_asm_tac)
=TEX
.

If one has an instance of $t1$ as an assumption and one wishes to
use the bi-implication in a theorem of the form
=INLINEFT
⊢ t1 ⇒ (t2 ⇔ t3)
=TEX
\ for rewriting, one might use
=INLINEFT
UFC_T1 id_canon rewrite_tac
=TEX
.

=SEEALSO
$ufc\_tac$, $asm\_ufc\_tac$, $bc\_tac$, $UFC\_T$.
=ENDDOC

=DOC
val ⦏UFC_T⦎ :
	(THM list -> TACTIC) -> THM list -> TACTIC;
val ⦏ALL_UFC_T⦎ :
	(THM list -> TACTIC) -> THM list -> TACTIC;
val ⦏ASM_UFC_T⦎ :
	(THM list -> TACTIC) -> THM list -> TACTIC;
val ⦏ALL_ASM_UFC_T⦎ :
	(THM list -> TACTIC) -> THM list -> TACTIC;
val ⦏ALL_UFC_⇔_T⦎ :
	(THM list -> TACTIC) -> THM list -> TACTIC;
val ⦏ALL_ASM_UFC_⇔_T⦎ :
	(THM list -> TACTIC) -> THM list -> TACTIC;
=DESCRIBE
These are tacticals which use theorems whose conclusions are
implications, or from which implications can be derived,
to reason forwards from the assumptions of a goal.
(The tacticals with
=INLINEFT
UFC
=TEX
\ are aliases for the corresponding ones with
=INLINEFT
UNIFY_FORWARD_CHAIN
=TEX
.)

The description of 
=INLINEFT
ufc_tac
=TEX
\ should be consulted for the basic forward chaining algorithms used.
The significance of the final argument and of the presence or absence of
=INLINEFT
ASM
=TEX
\ and
=INLINEFT
ALL
=TEX
\ in the name is exactly as for
=INLINEFT
ufc_tac
=TEX
\ and its relatives.

The tacticals allow variation of
the tactic generating function used to process the theorems derived
by the forward inference.
The tactic generating function to be used is given as the first
argument.

\paragraph{Examples}
=INLINEFT
ufc_tac
=TEX
\ is the same as:
=INLINEFT
UFC_T strip_asm_tac1
=TEX
.

To rewrite the goal with the results of the forward inference one
could use
=INLINEFT
UFC_T rewrite_tac
=TEX
.
=SEEALSO
$ufc\_tac$, $asm\_ufc\_tac$, $UFC\_T1$.
=ENDDOC

=DOC
val ⦏ufc_tac⦎ : THM list -> TACTIC;
val ⦏all_ufc_tac⦎ : THM list -> TACTIC;
val ⦏asm_ufc_tac⦎ : THM list -> TACTIC;
val ⦏all_asm_ufc_tac⦎ : THM list -> TACTIC;
val ⦏all_ufc_⇔_tac⦎ : THM list -> TACTIC;
val ⦏all_asm_ufc_⇔_tac⦎ : THM list -> TACTIC;
val ⦏all_ufc_⇔_rewrite_tac⦎ : THM list -> TACTIC;
val ⦏all_asm_ufc_⇔_rewrite_tac⦎ : THM list -> TACTIC;
=DESCRIBE
These are tactics which use theorems whose conclusions are
implications, or from which implications can be derived using
the canonicalisation function
=INLINEFT
fc_canon
=TEX
, q.v., to reason forwards from the assumptions of a goal.

The basic step is to take a theorem of the form
=INLINEFT
Γ ⊢ t1 ⇒ t2
=TEX
\ and an assumption of the form
=INLINEFT
t1'
=TEX
\ where $t1'$ is unifiable with $t1$ and to deduce the
corresponding instance of $t2'$. The new theorem,
=INLINEFT
Δ ⊢ t2'
=TEX
\ say, may then be stripped into the assumptions.

In the case of
=INLINEFT
ufc_tac
=TEX
\ the implicative theorem is always derived from the list
of theorems given as an argument.
In the case of
=INLINEFT
asm_ufc_tac
=TEX
\ the assumptions are also used.
In all of the tactics the rule 
=INLINEFT
fc_canon
=TEX
\ is used to derive an implicative canonical form from the
candidate implicative theorems.
Normally combination of an implicative theorem and an assumption
is then tried in turn and all resulting theorems are stripped into
the assumptions of the goal.
However, if the chaining results contain a theorem whose conclusion is ⌜F⌝ then the first such found will be stripped
into the assumptions, and all other theorems discarded.

If one of the implications has the form
=INLINEFT
t1 ⇒ t2 ⇒ t3
=TEX
\ or
=INLINEFT
t1 ∧ t2 ⇒ t3
=TEX
\ and if assumptions matching $t1$ and $t2$ are available,
=INLINEFT
ufc_tac
=TEX
\ or
=INLINEFT
asm_ufc_tac
=TEX
\ will derive an intermediate implication
=INLINEFT
t2 ⇒ t3
=TEX
\ and
=INLINEFT
asm_ufc_tac
=TEX
\ could then be used to derive $t3$.
The variants with $all\_$ may be used to derive $t3$ directly without
generating any intermediate implications in the assumptions.
They work like the corresponding tactic without $all\_$ but any theorems
which are derived which are themselves implications are not stripped into
the assumptions but instead are used recursively to derive further theorems.
When no new implications are derivable all of the non-implicative theorems
derived during the process are stripped into the assumptions.

Note that the use of
=INLINEFT
fc_canon
=TEX
\ implies that conversions from the
proof context are applied to generate implications.
E.g., in an appropriate proof-context covering set theory,
=INLINEFT
a ⊆ b
=TEX
\ might be treated as the implication
=INLINEFT
∀x⦁x ∈ a ⇒ x ∈ b
=TEX
.
Also variables which appear free in a theorem are not considered as candidates
for instantiation
(in order to give some control over the number of results generated).
The tacticals,
=INLINEFT
UFC_T1
=TEX
\ and 
=INLINEFT
ASM_UFC_T1
=TEX
\ may be used to avoid the use of
=INLINEFT
fc_canon
=TEX
.

For example, the tactic:
=GFT
asm_ufc_tac[] THEN asm_ufc_tac[]
=TEX
will prove the goal:
=GFT
{p x, ∀x⦁p x ⇒ q x, ∀x⦁q x ⇒ r x} r x.
=TEX

The variants with $⇔$ in the name use $fc\_⇔\_canon$ instead of $fc\_canon$ for processing the rules so that a concluding equivalence is not broken into implications and the results of forward chaining can be used for rewriting (however, this still won't work unless there are outer quantifiers to prevent the equivalence from being broken up when stripped into the assumptions).

All of these tactics add the results into the assumptions using $strip_asms_tac1$ and therefore fail if no new assumptions are added (unless the goal is discharged), except the ones whose name includes $rewrite$ which attempt the rewrite the conclusion of the goal with the results instead of stripping them into the assumptions.

=SEEALSO
$bc\_tac$,
$UFC\_T$,
$ASM\_UFC\_T$,
$UFC\_T1$,
$ASM\_UFC\_T1$.
=ENDDOC

=SML
end; (* of signature UnifyForwardChain *)
=TEX

\subsection{Implementation}

=SML
structure ⦏UnifyForwardChain⦎ : UnifyForwardChain = struct
=TEX

\ignore{
=SML
val ⦏was_theory⦎ = get_current_theory_name ();
val _ = open_theory "basic_hol";
val _ = set_merge_pcs ["'propositions", "'simple_abstractions"];
=TEX
}%ignore

In $unify\_⇒\_mp_rule$ the two theorems will be unified as necessary to permit inference by modus ponens.
Only variables universally quantified at the outer level will be candidates for instantiation, and in each of the premises only type variables which do not appear in the assumptions will be elegible for instantiation.
The two theorems are stripped of their outer universal quantifiers and the antecedent of the first (which must be an implication) will also be stripped of universal quantifiers and will then be unified with the second (without permitting substitution for the quanitifiers on the antecedent).
If this suceeds the consequent is inferred (after adding quantifiers as necessary to the second theorem and instantiating the quantifiers as necessary in the first theorem).
Then any variables which are free in the result but were previously bound are rebound.

\ignore{

=SML
open Resolution; open Unification; open StripFail; open RbjTactics1

fun ⦏simple_⇒_unify_mp_rule1⦎ ith ath =
 let	val s1 = ⇒_elim ith ath;
 in
	s1
 end handle (Fail _) =>
	let
	val (iasms, iconc) = dest_thm ith;
	val (aasms, aconc) = dest_thm ath;
	fun ttys t =  map mk_vartype (term_tyvars t);
	fun ittys (asms, conc) =  (ttys conc) drop
		(fn x => present (op =:) x (list_union (op =:) (map ttys asms)));
	val iityvs = ittys (iasms, iconc);
	val aityvs = ittys (aasms, aconc);
	val (ivars, barei) = strip_∀ iconc;
	val (avars, barea) = strip_∀ aconc;
	val (ai, c) = dest_⇒ barei;
	val (aivars, bareai) = strip_∀ ai;
	val subs = new_subs 40;
	val ((ityi, ites) , (atyi, ates)) =
		term_unify subs [] [] (
			(bareai, ivars, iityvs),
			(barea, avars, aityvs));
	val _ = init_subs subs;
	fun laux [] t = t
	|   laux ((nt1, t1)::tl) t = if t1 =$ t then nt1 else laux tl t;
	val ites2 = map (laux ites) ivars;
	val ates2 = map (laux ates) avars;
	val ni = list_∀_elim ites2 (inst_type_rule ityi ith);
	val na = list_∀_elim ates2 (inst_type_rule atyi ath);
	val naithm = list_∀_intro aivars na;
	val othm = ⇒_elim ni naithm;
	val ccfrees = frees (concl othm);
	val cafrees = list_union (op =$) (map frees (asms othm));
	val bindvars = ccfrees drop (fn x => (present (op =$) x cafrees))
	in (list_∀_intro bindvars othm)
end;
=IGN
simple_⇒_unify_mp_rule1 (asm_rule ⌜a ⇒ b⌝) (asm_rule ⌜a:BOOL⌝);
simple_⇒_unify_mp_rule1 (asm_rule ⌜∀x v⦁ ((λz⦁z)x, v) = y ⇒ x⌝) (asm_rule ⌜∀a b⦁ ((λq⦁q)a:BOOL, b)=y⌝);
simple_⇒_unify_mp_rule1 (asm_rule ⌜∀ (y:'a) (x:'a) ($<<:'a→'a→BOOL) (X:'a SET)⦁
				Snd (TranClsr (X, $<<)) x y ⇒ ¬ x ∈ X ⇒ F⌝)
		 (asm_rule ⌜Snd (TranClsr (X:'a SET, $<<:'a→'a→BOOL)) (x'':'a) (x':'a):BOOL⌝);
simple_⇒_unify_mp_rule1 (asm_rule ⌜∀x y (X:'a SET)⦁ x ∈ X ⇒ y ∈ X ⇒ {x; y} ∈ ℙ X⌝)
	(asm_rule ⌜(y:'a) ∈ X⌝);
simple_⇒_unify_mp_rule1 (hd(fc_canon (asm_rule ⌜∀ A:'a SET
           ⦁ (∀ x:'a⦁ x ∈ A ⇒ x ∈ X) ∧ ¬ (∀ x:'a⦁ ¬ x ∈ A)
               ⇒ (∃ x:'a⦁ x ∈ A ∧ (∀ y:'a⦁ y ∈ A ∧ ¬ y = x ⇒ ¬ y << x))⌝)))
	(asm_rule ⌜∀ x:'a⦁ x ∈ A ⇒ x ∈ X⌝);
simple_⇒_unify_mp_rule1 (hd(fc_canon (asm_rule ⌜∀ (G: ('a→'b)→('a→'b)) (X:'a SET) ($<<: 'a→'a→BOOL)
     ⦁ FunctRespects G (X, $<<)
         = (∀ g h x
         ⦁ x ∈ X ⇒ (∀ y⦁ y ∈ X ∧ y << x ⇒ g y = h y) ⇒ G g x = G h x)⌝)))
	(asm_rule ⌜∀ (G: ('a→'b)→('a→'b)) (X:'a SET) ($<<: 'a→'a→BOOL)⦁
		FunctRespects G (X, $<<):BOOL⌝);
=SML
val ⦏all_∀_uncurry_rule⦎ = conv_rule(TRY_C all_∀_uncurry_conv);

fun ⦏⇒_unify_mp_rule1⦎ (thm1 : THM) : THM -> THM = (
let	val thm1' = all_∀_uncurry_rule thm1;
	val r' = simple_⇒_unify_mp_rule1 thm1'
		handle complaint =>
		pass_on complaint "simple_⇒_unify_mp_rule1"
			"⇒_unify_mp_rule1";
in
	(fn (thm2 : THM) =>
	r' thm2
	handle complaint => reraise complaint "⇒_unify_mp_rule1")
end);
=IGN
⇒_unify_mp_rule1 (asm_rule ⌜∀(x, y):ℕ × ℕ⦁ y = x * x ⇒ y ≥ 0 ∧ q⌝) (asm_rule ⌜∀v w q:ℕ⦁ v = w * w⌝);
⇒_unify_mp_rule1 (asm_rule ⌜∀(x, y):ℕ × ℕ⦁ y = x * x ⇒ y ≥ 0 ∧ q⌝) (asm_rule ⌜∀v w q:ℕ⦁ v = w * w⌝);
⇒_unify_mp_rule1 (asm_rule ⌜∀ y x $<< X⦁ Snd (TranClsr (X, $<<)) x y ⇒ ¬ x ∈ X ⇒ F⌝)
		 (asm_rule ⌜Snd (TranClsr (X, $<<)) x'' x'⌝);
⇒_unify_mp_rule1 ((hd o fc_canon o asm_rule) ⌜∀ X $<< G (x:'a)
           ⦁ x ∈ X ∧ UniquePartFixp (TcUpTo (X, $<<) x) G
               ⇒ (∀ f⦁ PartFunEquiv (TcUpTo (X, $<<) x) (G f) f ⇒ UniqueVal (X, $<<) G x = f x)⌝)
	(asm_rule ⌜x'' ∈ (X:'a SET)⌝);
⇒_unify_mp_rule1 (asm_rule ⌜∀(x, y) (X:'a SET)⦁ x ∈ X ⇒ y ∈ X ⇒ {x; y} ∈ ℙ X⌝)
	(asm_rule ⌜(y:'a) ∈ X⌝);
⇒_unify_mp_rule1 (hd(fc_canon (asm_rule ⌜∀ A
           ⦁ (∀ x⦁ x ∈ A ⇒ x ∈ X) ∧ ¬ (∀ x⦁ ¬ x ∈ A)
               ⇒ (∃ x⦁ x ∈ A ∧ (∀ y⦁ y ∈ A ∧ ¬ y = x ⇒ ¬ y << x))⌝)))
	(asm_rule ⌜∀ x⦁ x ∈ A ⇒ x ∈ X⌝);
=SML
local
val ⦏¬_convs⦎ = map
	(fn t => simple_eq_match_conv1
		(all_∀_intro (tac_proof(([], t), simple_taut_tac))))
	[⌜¬t ⇒ F ⇔ t⌝, ⌜t ⇒ F ⇔ ¬t⌝];
in
fun ⦏unify_forward_chain_rule⦎ (imps : THM list) (ants : THM list) : THM list = (
let	val imp_rules = mapfilter ⇒_unify_mp_rule1 imps;
	fun aux1 acc _ [] = (acc
	) | aux1 acc (i :: il) (al as (a :: _)) = (
		(let val res = i a
		in
		if concl res =$ mk_f
		then [res]
		else
		(aux1 (res::acc) il al)
		end)
		handle Fail _ => aux1 acc il al
	) | aux1 acc [] (_ :: al) = (aux1 acc imp_rules al
	);
	fun aux2 thm = (
		case dest_term (concl thm) of
			D∀ (x, b) => (
				let val th = aux2 (asm_rule b);
				in ∀_intro x (prove_asm_rule (∀_elim x thm) th)
				end
		) |	D⇒ (a, b) => (
				(conv_rule(FIRST_C ¬_convs) thm)
				handle Fail _ =>
				let val th = aux2 (asm_rule b);
				in ⇒_intro a (prove_asm_rule(undisch_rule thm) th)
				end
		) |	_ => fail "" 99999 []
	);
	fun aux3 th = aux2 th handle Fail _ => th;
in	map aux3 (aux1 [] imp_rules ants)
end);
end;

val ⦏ufc_rule⦎ : THM list -> THM list -> THM list = unify_forward_chain_rule;

=IGN
ufc_rule [(asm_rule ⌜∀(x, y):ℕ × ℕ⦁ y = x * x ⇒ y ≥ 0 ∧ q⌝)] [(asm_rule ⌜∀v w q:ℕ⦁ v = w * w⌝)];
ufc_rule [(asm_rule ⌜∀ y x $<< X⦁ Snd (TranClsr (X, $<<)) x y ⇒ x ∈ X⌝)]
		 [(asm_rule ⌜Snd (TranClsr (X, $<<)) x'' x'⌝)];
ufc_rule [asm_rule⌜∀ X $<< G x
           ⦁ x ∈ X ∧ UniquePartFixp (TcUpTo (X, $<<) x) G
               ⇒ (∀ f⦁ PartFunEquiv (TcUpTo (X, $<<) x) (G f) f ⇒ UniqueVal (X, $<<) G x = f x)⌝]
	[asm_rule ⌜x'' ∈ X⌝,
	asm_rule ⌜UniquePartFixp (TcUpTo (X, $<<) x'') G⌝];
ufc_rule [(asm_rule ⌜∀(x, y) (X:'a SET)⦁ x ∈ X ⇒ y ∈ X ⇒ {x; y} ∈ ℙ X⌝)]
	[asm_rule ⌜(y:'a) ∈ X⌝];
ufc_rule [(asm_rule ⌜∀(x:'a, y:'b) (X:'a SET) (Y:'b SET)⦁ x ∈ X ⇒ y ∈ Y ⇒ {x, y} ∈ ℙ (X × Y)⌝)]
	[asm_rule ⌜(y:'b) ∈ X⌝];
ufc_rule [tac_proof (([], ⌜∀(x:'a, y:'b) (X:'a SET) (Y:'b SET)⦁ x ∈ X ⇒ y ∈ Y ⇒ {x, y} ∈ ℙ (X × Y)⌝),
	(REPEAT strip_tac
	THEN asm_rewrite_tac[sets_ext_clauses, get_spec ⌜$×⌝]
	THEN REPEAT strip_tac THEN asm_rewrite_tac[]))]
	[asm_rule ⌜(y:'b) ∈ X⌝];
ufc_rule [(asm_rule ⌜∀(X:'a SET) (x:'a)⦁ x ∈ X ⇒ ∃y⦁ y ∈ X ⇒ {x, y} ∈ ℙ (X × X)⌝)]
	[asm_rule ⌜(y:'a) ∈ X⌝];
ufc_rule [(asm_rule ⌜∀(X:'a SET) (x:'a)⦁ ∃y⦁ x ∈ X ⇒ y ∈ X ⇒ {x, y} ∈ ℙ (X × X)⌝)]
	[asm_rule ⌜(y:'a) ∈ X⌝];
ufc_rule (fc_canon (asm_rule ⌜∀ A
           ⦁ (∀ x⦁ x ∈ A ⇒ x ∈ X) ∧ ¬ (∀ x⦁ ¬ x ∈ A)
               ⇒ (∃ x⦁ x ∈ A ∧ (∀ y⦁ y ∈ A ∧ ¬ y = x ⇒ ¬ y << x))⌝))
	[asm_rule ⌜∀ x⦁ x ∈ A ⇒ x ∈ X⌝];
ufc_rule (fc_canon (asm_rule ⌜∀ G (X, $<<)
     ⦁ FunctRespects G (X, $<<)
         = (∀ g h x
         ⦁ x ∈ X ⇒ (∀ y⦁ y ∈ X ∧ y << x ⇒ g y = h y) ⇒ G g x = G h x)⌝))
	[asm_rule ⌜FunctRespects G (X, $<<):BOOL⌝];
fc_rule (fc_canon (asm_rule ⌜∀ G (X, $<<)
     ⦁ FunctRespects G (X, $<<)
         = (∀ g h x
         ⦁ x ∈ X ⇒ (∀ y⦁ y ∈ X ∧ y << x ⇒ g y = h y) ⇒ G g x = G h x)⌝))
	[asm_rule ⌜FunctRespects G (X, $<<):BOOL⌝];
ufc_rule (fc_canon (asm_rule ⌜∀ (G: ('a→'b)→('a→'b)) (X:'a SET, $<<: 'a→'a→BOOL)
     ⦁ FunctRespects G (X, $<<)
         = (∀ g h x
         ⦁ x ∈ X ⇒ (∀ y⦁ y ∈ X ∧ y << x ⇒ g y = h y) ⇒ G g x = G h x)⌝))
	[asm_rule ⌜∀ (G: ('a→'b)→('a→'b)) (X:'a SET, $<<: 'a→'a→BOOL)⦁
		FunctRespects G (X, $<<):BOOL⌝];
=TEX

=SML
fun ⦏UFC_T1⦎
	(can : THM -> THM list)
	(ttac : THM list -> TACTIC)
	(thms : THM list)
	: TACTIC = (fn gl as (asms, _) =>
	let	val asmthms = map asm_rule asms;
	in	ttac(ufc_rule(flat(map can thms)) asmthms) gl
	end
);
=TEX
=SML
fun ⦏ASM_UFC_T1⦎
	(can : THM -> THM list)
	(ttac : THM list -> TACTIC)
	(thms : THM list)
	: TACTIC = (fn gl as (asms, _) =>
	let	val asmthms = map asm_rule asms;
	in	ttac(ufc_rule(flat(map can (thms@asmthms))) asmthms) gl
	end
);

val ⦏UFC_T⦎ = UFC_T1 fc_canon;
val ⦏ASM_UFC_T⦎ = ASM_UFC_T1 fc_canon;

val ⦏ufc_tac⦎ : THM list -> TACTIC = UFC_T strip_asms_tac1;
val ⦏asm_ufc_tac⦎ : THM list -> TACTIC = ASM_UFC_T strip_asms_tac1;

fun ⦏ALL_UFC_T1⦎ (can : CANON) (ttac : THM list -> TACTIC) (ths : THM list) : TACTIC = (
	let	fun aux1 acc [] = acc
		|   aux1 (imps, others) (th :: more) = (
			if is_⇒ (snd(strip_∀(concl th)))
			then aux1 (th :: imps, others) more
			else aux1 (imps, th :: others) more
		);
		fun aux2 acc imps = (
			UFC_T1 id_canon (fn thl =>
				let	val (imps, others) = aux1 ([], acc) thl;
				in	if	is_nil imps
					then	ttac others
					else	aux2 others imps
				end
			) imps
		);
		val ths' = flat (map can ths);
	in	aux2 [] (ths' drop (not o is_⇒ o snd o strip_∀ o concl))
	end
);
val ⦏ALL_UFC_T⦎ : (THM list -> TACTIC) -> THM list -> TACTIC = ALL_UFC_T1 fc_canon;

fun ⦏ALL_ASM_UFC_T1⦎ (can : CANON) (ttac : THM list -> TACTIC) (thms : THM list) : TACTIC = (
	GET_ASMS_T (fn asm_thms => ALL_UFC_T1 can ttac (thms @ asm_thms)));
fun ⦏ALL_ASM_UFC_T⦎ (ttac : THM list -> TACTIC) (ths : THM list) : TACTIC = (
	GET_ASMS_T (fn thl => ALL_UFC_T ttac (thl @ ths)));

val ⦏all_ufc_tac⦎ : THM list -> TACTIC = ALL_UFC_T strip_asms_tac1;
val ⦏all_asm_ufc_tac⦎ : THM list -> TACTIC = ALL_ASM_UFC_T strip_asms_tac1;

val ⦏ALL_UFC_⇔_T⦎ = ALL_UFC_T1 fc_⇔_canon;
val ⦏ALL_ASM_UFC_⇔_T⦎ = ALL_ASM_UFC_T1 fc_⇔_canon;

val ⦏all_ufc_⇔_tac⦎ = ALL_UFC_⇔_T strip_asms_tac1;
val ⦏all_asm_ufc_⇔_tac⦎ = ALL_ASM_UFC_⇔_T strip_asms_tac1;

val ⦏all_ufc_⇔_rewrite_tac⦎ = ALL_UFC_⇔_T rewrite_tac;
val ⦏all_asm_ufc_⇔_rewrite_tac⦎ = ALL_ASM_UFC_⇔_T rewrite_tac;
=TEX
} %ignore

=SML
end; (* of structure UnifyForwardChain *)
=TEX

\section{Embedding Languages}

In this section facilities for very simple deep embeddings are provided.
In the intended applications an easily readable grammar is more important than an efficient parser, so we provide a simple recursive descent parser which is parameterised by a grammar coded into a HOL term.


=DOC
signature ⦏ParseComb⦎ = sig
=DESCRIBE

This signature provides combinators for a simple parser.
It is only for small bits of language, so it expects the input to be a list.
The output, on the other hand is generated by a collection of constructors supplied as a parameter.

=ENDDOC

=DOC
exception parse_fail of int;

type 'a ⦏ptree⦎;
type 'a ⦏pt_pack⦎;
type 'a parser = 'a pt_pack -> 'a list -> 'a ptree * 'a list;
=DESCRIBE
This \emph{'a ptree} is an abstract type of parse trees.
A \emph{PtreePack} is a record type of constructors for parse trees.
=ENDDOC

=DOC

val ⦏alt_parse⦎: 'a parser list -> 'a parser;
val ⦏seq_parse⦎: 'a parser list -> 'a parser; 
val ⦏opt_parse⦎: 'a parser -> 'a parser;  
val ⦏star_parse⦎: 'a parser -> 'a parser;  
val ⦏plus_parse⦎: 'a parser -> 'a parser; 
=DESCRIBE

=ENDDOC

=SML
end; (* of signature ParseComb *)
=TEX

=SML
structure ⦏ParseComb⦎:ParseComb = struct

exception parse_fail of int;

datatype 'a tree = MkTree of 'a * 'a tree list;

type 'a ptree = int * 'a tree;

type 'a pt_pack = {	mk_plit:'a -> 'a ptree,
			mk_plist: 'a ptree list -> 'a ptree,
			mk_palt: int * 'a ptree -> 'a ptree,
			mk_popt: 'a ptree OPT -> 'a ptree};

type 'a parser = 'a pt_pack -> 'a list -> 'a ptree * 'a list;

datatype 'a pttag = Ptint of int | Ptlit of 'a | Ptnone; 

fun mk_ptp (mk_tree: ('a pttag) * 'b list -> 'b) = {
	mk_plit = fn l => mk_tree (Ptlit l, []),
	mk_plist = fn ptl => mk_tree (Ptnone, ptl),
	mk_palt = fn (i, pt) => mk_tree (Ptint i, [pt]),
	mk_popt = fn pto => mk_tree (Ptnone, (fn Nil => [] | Value pt => [mk_tree (Ptnone, [pt])])pto ) 
};

fun alt_parse (pl:'a parser list) (ptp as {mk_palt, ...}: 'a pt_pack) (li:'a list) =
	let fun aux (pl as (hp::tpl)) n j = (let val (pt, rli) = hp ptp li in (mk_palt (n, pt), rli) end
			handle parse_fail k => aux tpl (n+1) (if j < k then j else k))
	    |   aux [] n i = raise parse_fail i
	in aux pl 0 (length li)
	end;

fun seq_parse pl (ptp as {mk_plist, ...}:'a pt_pack) li =
	let fun aux (p, (ptl, li)) = let val (npt, rli) = p ptp li in (npt::ptl, rli) end
	    val (ptl, nli) = revfold aux pl ([], li)
	in (mk_plist (rev ptl), nli)
	end;

fun opt_parse p (ptp as {mk_popt, ...}:'a pt_pack) li =
	let val (pt, nli) = p ptp li
	in (mk_popt (Value pt), nli)
	end handle parse_fail i => (mk_popt Nil, li);

fun star_parse (p:'a parser) (ptp as {mk_plist, ...}:'a pt_pack) li =
	let	fun aux1 li =	let val (pt, rli) = p ptp li
				in ([pt], rli)
				end handle parse_fail i => ([], li)
		fun aux2 li =
			let val (ptl, rli) = aux1 li
			in	case ptl of
					[] => ([], rli)
				|	ptl =>	let val (ptl2, sli) = aux2 rli
					in (ptl @ ptl2, sli)
					end
			end
	    val (ptl, nli) = aux2 li
	in (mk_plist (rev ptl), nli)
	end;

fun plus_parse (p:'a parser) (ptp as {mk_plist, ...}:'a pt_pack) li =
	let	fun aux1 li =	let val (pt, rli) = p ptp li
				in ([pt], rli)
				end handle parse_fail i => ([], li)
		fun aux2 li =
			let val (ptl, rli) = aux1 li
			in	case ptl of
					[] => ([], rli)
				|	ptl =>	let val (ptl2, sli) = aux2 rli
					in (ptl @ ptl2, sli)
					end
			end
	    val (ptl, nli) = aux2 li
	in (mk_plist (rev ptl), nli)
	end;

end; (* of structure ParseComb *)
=TEX

=DOC
signature ⦏Grammar⦎ = sig
=DESCRIBE
This signature provides access to grammars for a simple parser.
A grammar consists of a list of phrase definitions.
A phrase definition consists of a phrase name and an expression.
An expression is either:
\begin{enumerate}
\item a literal (not sure what that is at the moment)
\item a choice among a list of expressions
\item a list of expressions
\item an expression to be permitted any number of times, with an optional list separator and an option to allow zero times.
\end{enumerate}
We require functions for constructing, discriminating and destructing

=ENDDOC

=DOC
 
=DESCRIBE

=ENDDOC

=SML
end; (* of signature Grammar *)
=TEX


=IGN
structure Grammar:Grammar = struct

datatype ''a Gpdef =
	  Glit of ''a
	| Gname of string
	| Galts of ''a Gpdef list
	| Gseq of ''a Gpdef list
	| Crep of {phrase: ''a Gpdef, separator:''a Gpdef OPT, allowempty:bool};

datatype ''a Gptree = Gpfail | Gpalt of int * ''a Gptree | Gplit of ''a | Gplist of (''a Gptree list);

fun	parse grammar (Glit li) (l as h::t) = if h = li then (Gplit h, t) else (Gpfail, l)
|	parse grammar (Gname n) (l as h::t) =
		let val phrase = lassoc5 grammar n
		in case phrase of Value p => parse grammar p l
		                  |  Nil => (Gpfail, l)
		end
|	parse grammar (Galts []) (l as h::t) = (Gpfail, l)
|	parse grammar (Galts (a as ha::ta)) (l as h::t) =
		case (parse grammar ha l) of
			(Gpfail, _) => parse grammar (Galts ta) l
		|	(Gpalt (j, pt), r) => (Gpalt (j+1, pt), r)
|	parse grammar (Gseq (a as ha::ta)) (l as h::t) =
		case (parse grammar ha l) of
			(Gpfail, m) => case 
		|	(Gpalt (j, pt), r) => (Gpalt (j+1, pt), r)
		

;


end (* of structure Grammar *) ;

=TEX


\section{Trawling for Useful Theorems}

=DOC
signature ⦏Trawling⦎ = sig
=DESCRIBE
The functions in this signature search the ancestors of the current theory for theorems which do something with the current goal, i.e. which rewrite the conclusion, backward chain from it, or forward chain from the assumptions.
=ENDDOC

=DOC
datatype ⦏THMDET⦎ = Spec of TERM | Thm of (string * string);
val ⦏on_conc⦎ : (TERM -> 'a) -> 'a;
val ⦏on_asms⦎ : (TERM list -> 'a) -> 'a;
val ⦏rew_thms⦎ : TERM -> ((int * THMDET) * THM) list;
val ⦏rew_specs⦎ : TERM -> ((int * THMDET) * THM) list;
val ⦏bc_thms⦎ : TERM -> ((int * THMDET) * THM) list;
val ⦏fc_thms⦎ : TERM list -> ((int * THMDET) * THM) list;
val ⦏all_fc_thms⦎ : TERM list -> ((int * THMDET) * THM) list;
val ⦏todo⦎ : unit -> {bc: int, fc: int, rw: int};
val ⦏td_thml⦎ : THMDET list -> THM list;
=DESCRIBE
$on\_conc$ and $on\_asms$ apply their arguments respectively to the conclusion or the list of assmuptions of the current goal.

$rew\_thms$, $rew\_specs$, $bc\_thms$ retrieve respectively theorems ($thms$) or specifications ($specs$) which can be used to sucessfully rewrite ($rew$) or backchain from ($bc$) the term supplied as an argument.

$fc\_thms$ and $all\_fc\_thms$, when supplied with a list of assumptions, retrieve theorems which will yield results using $fc\_tac$ and $all\_fc\_tac$.

$todo()$ returns a count of how many theorems or specifications are applicable to the current goal, classified according to the method of application.
$bc$ = back chaining, $fc$ = forward chaining, $rw$ = rewriting.
=ENDDOC

=SML
end; (* of signature Trawling *)
=TEX

=SML
structure ⦏Trawling⦎ : Trawling = struct
=TEX

\ignore{
=SML

val avoid_theories = ref ["min", "log", "misc", "sets", "combin", "pair", "list"];
val avoid_constants = ref [""];
val avoid_specs: string list ref = ref [""];

datatype THMDET =
		Spec of TERM
	|	Thm of (string * string);

fun is_defined_constant s =
	let val theoryname = get_const_theory s;
	    val defn = get_defn theoryname s
	in true
	end
	handle _ => false;

fun defined_consts t =
	let val consts = term_consts t
	in filter
		(fn x => not ((fst x) mem !avoid_constants)
		andalso is_defined_constant (fst x))
	   consts
	end;

fun defined_const_names t = map fst (defined_consts t);

fun on_conc f = f (snd (top_goal()));

fun on_asms f =
	let val (asms, concl) = top_goal()
	in f asms
	end;

fun on_goal f =
	let val (asms, concl) = top_goal()
	in  flat(map f (concl :: asms))
	end;

fun term_const_specs t =
	let fun gs (s,t) =
		let val c = mk_const (s,t)
		in (if	s mem !avoid_specs orelse
			(get_const_theory s) mem !avoid_theories
		   then []
		   else [(Spec c, get_spec c)]) handle _ => []
		end
	in flat (map gs (term_consts t))
	end;

fun const_theories t = list_cup (map (fn x => [get_const_theory x]) (defined_const_names t));

fun ancestor_theories t = filter (fn x => not (x mem !avoid_theories)) (get_ancestors t);

fun thy_thms t = map (fn (s,thm) => (Thm(t, hd s), thm)) (get_thms t);

fun const_thms t = flat(map thy_thms (const_theories t));

fun ancestor_thms t = flat(map thy_thms (ancestor_theories t));

fun rewriting_thm t thm =
	let val t' = pure_once_rewrite_conv [thm] t
	in true
	end handle _ => false;

local open RbjTactics1 in
fun srewriting_thm t thm = rewriting_thm t (map_eq_sym_rule thm) handle _ => false;
end;

fun fc_thm ts thm =
	let val thms = fc_rule (fc_canon thm) (map asm_rule ts)
	in (fn [] => false | _ => true) thms
	end handle _ => false;

fun all_fc_thm ts thm =
	let val (gl, pr) = all_fc_tac [thm] (ts, ⌜F⌝)
	in if length gl = 1 andalso length (fst (hd gl)) = length ts
		then false else true
	end handle _ => false;

fun bc_thm c thm =
	let val (gl, pr) = bc_tac [thm] ([], c)
	in if length gl = 1 andalso (snd (hd gl)) =$ c
		then false else true
	end handle _ => false;

fun numthms n [] = []
|   numthms n ((thmdets, thm)::t) = ((n, thmdets), thm):: (numthms (n+1) t);

fun rew_specs t =
	let val thms = term_const_specs t
	in numthms 1 (filter ((rewriting_thm t) o snd) thms)
	end;

fun terml_const_specs tl = flat (map term_const_specs tl);

fun fc_specs ts =
	let val thms = terml_const_specs ts
	in numthms 1 (filter ((fc_thm ts) o snd) thms)
	end;

fun bc_specs t =
	let val thms = term_const_specs t
	in numthms 1 (filter ((bc_thm t) o snd) thms)
	end;

fun rew_thms t =
	let val thms = (ancestor_thms "-") @ (term_const_specs t)
	in numthms 1 (filter ((rewriting_thm t) o snd) thms)
	end;

fun srew_thms t =
	let val thms = (ancestor_thms "-") @ (term_const_specs t)
	in numthms 1 (filter ((srewriting_thm t) o snd) thms)
	end;

fun fc_thms tl =
	let val thms = (ancestor_thms "-") @ (terml_const_specs tl)
	in numthms 1 (filter ((fc_thm tl) o snd) thms)
	end;

fun all_fc_thms tl =
	let val thms = (ancestor_thms "-") @ (terml_const_specs tl)
	in numthms 1 (filter ((all_fc_thm tl) o snd) thms)
	end;

fun bc_thms t =
	let val thms = (ancestor_thms "-") @ (term_const_specs t)
	in numthms 1 (filter ((bc_thm t) o snd) thms)
	end;

fun rew_thms2 t =
	let val thms = (ancestor_thms "-") @ (term_const_specs t)
	in numthms 1 (flat (map (fn (sl, th) =>
		[(sl, (th, (snd o dest_eq)(concl (pure_once_rewrite_conv [th] t))))]
		handle _ => []) thms))
	end;

fun rew_thms3 t =
	let val thms = (ancestor_thms "-") @ (term_const_specs t)
	in numthms 1 (flat (map (fn (sl, th) =>
		[(sl, (snd o dest_eq)(concl (pure_once_rewrite_conv [th] t)))]
		handle _ => []) thms))
	end;

fun const_rewrite_conv t =
	let val thms = map snd (rew_thms t)
	in rewrite_conv thms t
	end;

fun with_conc_thms f =
	let fun ff t = f (map snd (rew_thms t))
	in on_conc ff
	end;

fun with_conc_specs f =
	let fun ff t = f (map snd (rew_specs t))
	in on_conc ff
	end;

fun td_thm (Thm (thyn, thmn)) = get_thm thyn thmn
|   td_thm (Spec s) = get_spec s;

fun td_thml tdl = map td_thm tdl;

fun numl2tdl tdsl nl =
 map (fn chose => (snd o fst o chose) tdsl) (map (fn n=> nth (n-1)) nl);

fun todo () =
	let val rw = length (on_conc rew_thms)
	    val bc = length (on_conc bc_thms)
	    val fc = length (on_asms fc_thms)
	in {rw = rw, bc = bc, fc = fc}
	end;
=TEX
}%ignore

=SML
end; (* of structure Trawling *)
=TEX

\section{For Inductive and Coinductive Definitions}

\subsection{Some Handy SML functions}

The following functions have been moved here from \cite{rbjt007}.

=SML
fun lfoldl f a [] = a
|  lfoldl f a (h::t) = lfoldl f (f (a, h)) t;

fun lfoldr f a [] = a
|  lfoldr f a (h::t) = f (a, (lfoldr f h t));

fun ⦏list_s_enter⦎ [] d = d
|   list_s_enter ((s,v)::t) d = list_s_enter t (s_enter s v d); 

fun ⦏list_to_sdict⦎ l = list_s_enter l initial_s_dict;

fun ⦏list_pos⦎ e [] = 0
|   list_pos e (h::t) =
	if h = e
	then 1
	else	let val p = list_pos e t 
		in if p = 0 then 0 else p+1
		end;

val ⦏strip_→_type⦎ = strip_spine_right dest_→_type;

fun ⦏list_mk_×_type⦎ (h::t) = lfoldr mk_×_type h t;

fun ⦏match_mk_app⦎ (f, a) = mk_app(f, a) handle _ => ⌜ⓜf⌝ ⓜa⌝⌝;

fun ⦏list_match_mk_app⦎ (f, al) = lfoldl match_mk_app f al;

fun ⦏mk_tree_type⦎ ty = mk_ctype ("TREE", [ty]);

fun ⦏mk_tree⦎ t tl =
	let val tt = type_of t
	in mk_app (
		mk_const ("MkTree", mk_→_type (mk_×_type (tt, mk_ctype("LIST", [tt])), mk_tree_type tt)),
		tl)
	end;

fun ⦏dest_tree⦎ tr = dest_app tr;

fun ⦏list_mk_tree⦎ t tl = mk_tree t (mk_list tl);

fun ⦏dest_tree_list⦎ tr = let val (t, l) = dest_tree tr in (t, dest_list l) end;
=TEX

=SML
fun gen_type_map cf vf ty =
	let fun aux (Vartype v) = vf v
	|       aux (Ctype (s, tl)) = cf s ((map (aux o dest_simple_type)) tl)
	in aux (dest_simple_type ty)
	end;

local fun front_last [e] = ([], e)
      |   front_last (f::t) = 
	   let val (f2, l) = front_last t
	   in (f::f2, l)
	   end
in fun ⦏front⦎ x = let val (f,l) = front_last x in f end
   fun ⦏last⦎ x = let val (f,l) = front_last x in l end
   fun ⦏right_rotate_list⦎ [] = []
   |   right_rotate_list [e] = [e]
   |   right_rotate_list x = let val (f,l) = front_last x in l :: f end
   fun ⦏left_rotate_list⦎ [] = []
   |   left_rotate_list [e] = [e]
   |   left_rotate_list (h::t) = t @ [h]
end;
=TEX

\subsection{False Equations Between Set Displays}

The following code defines a conversion for transforming (into $⌜F⌝$) false equations between set displays.

=SML
infix symdiff;

fun x ⦏symdiff⦎ y = (x diff y) cup (y diff x);

fun dest_enum l =
	(fn DEnumSet els => els
	|  D∅ t => []) (dest_term l);

fun enum_eq_sdiff t =
	let val DEq (lhs, rhs) = dest_term t
	in (dest_enum lhs) symdiff (dest_enum rhs)
	end;

fun ⦏false_enum_eq_conv⦎ t =
	let val (dt :: _) = enum_eq_sdiff t
	in 
		tac_proof(([], ⌜ⓜt⌝ ⇔ F⌝),
			rewrite_tac [sets_ext_clauses]
			THEN ¬_in_tac
			THEN ∃_tac dt THEN prove_tac[])
	end handle _ => fail_conv t;

val ⦏false_enum_eq_tac⦎ = conv_tac (MAP_C false_enum_eq_conv); 
=TEX
=IGN
(* This hack for conditional rewriting was done in response to
a question on the ProofPower mailing list and is included here
in case I need at sometime to do anything similar *)

open_theory "ℝ";

fun thm_eqn_cxt1 (thm : THM) : TERM * CONV = (
let	val cnv = simple_eq_match_conv thm
	val lhs = fst(dest_eq(snd(strip_∀ (concl thm))));
in
	(lhs, cnv)
end);

fun cond_rewrite_canon thm = [strip_⇒_rule (all_∀_elim thm)];

val cond_rewrite_conv = prim_rewrite_conv
	empty_net
	cond_rewrite_canon
	(Value thm_eqn_cxt1)
	MAP_C
	[];

cond_rewrite_conv [ℝ_over_times_over_thm] ⌜2./3.*4./5.⌝;

fun cond_rewrite_tac thm (asml, conc) =
	let val thm2 = cond_rewrite_conv [thm] conc
	in  MAP_EVERY (fn p => (LEMMA_T p
		(fn q => MAP_EVERY asm_tac (forward_chain_rule [thm] [q]))))
		(asms thm2)
		(asml, conc)
	end;

set_goal ([], ⌜2./3.*4./5. = 0.⌝);
a(cond_rewrite_tac ℝ_over_times_over_thm);
=TEX
\twocolumn[\section{INDEX}\label{INDEX}]
{\small\printindex}

\end{document}
