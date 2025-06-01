=TEX
\ignore{
=VDUMP t045i.tex
Last Change $ $Date: 2011/10/25 09:10:46 $ $

$ $Id: t045.doc,v 1.9 2011/10/25 09:10:46 rbj Exp $ $
=TEX
}%ignore

\subsection{Motivations}

I aim also to cast some light on the following concepts and the relationships between them:

\begin{itemize}
\item referential transparency and opacity
\item extensionality and intensionality
\item truth functionality
\end{itemize}

Furthermore, it should be admitted that there are methodological messages inℝ my agenda.

Of these the first is simply that the use of appropriate formal languages in the investigation of topics such as this can improve understanding.
The second it that by contrast with devising special languages (such as modal logics) for investigating specific issues, the use of a general purpose formal language is more flexible, and is appropriate for the kind of discussion found, for example, in Quine's \emph{Reference and Modality} \cite{quineRM}.
This message speaks against Carnap's abandonment of Russelian universalism in favour of a pluralism inspired by Hilbert.
It is natural to move onward, as I intend for the discussion here, from the discussion of the meaning and logic of modalities into a consideration of metaphysics.
Both for this purpose and for Carnap's purpose of aiding and abetting the formalisation of science, it may be questioned whether our formal languages need the modal vocabulary at all.
I hope to close with some discussion of the advantages of dealing with physics and metaphysics formally using general purpose abstract formal systems without any fixed modal vocabulary.

There is of course an extensive literature on these topics, with which I have limited acquaintance.
The study of the modal concepts of goes back to antiquity at least as far as Aristotle's Organon.
It has, with all other aspects of formal logic, been greatly advanced in modern times.

\subsection{Scope}

This document is at present in an ``early-life crisis'' under which its scope is likely to change.

For our present purposes it may suffice to consider the history as beginning with Frege in his discussion of `Sinn und Bedeutung'\cite{fregeTPWF,fregeSM}.

Formal propositional modal logics were first studied by C.I.Lewis, initially motivated by objections to the use of material implication in \emph{Principia Mathematica}, and first publishing on the topic in his `A Survey of Symbolic Logic' of 1918\cite{lewisSSL}.
The concepts of analyticity and necessity were later to become central to the philosophy of Rudolf Carnap\cite{carnap47}.
Carnap became engaged in controversy with Quine, who was skeptical about the coherence of modal systems, particularly of quantification into modal contexts\cite{quineRM}.
At the same time Ruth Barcan Marcus was publishing on first and second order systems of quantified modal logic.

I refer specifically to Quine's `Reference and Modality' and to the two previous papers of which that paper is an amalgam \cite{copigould,quineNEN,quinePIML,quineRM,quineLPOV}.

The next staging point in the discussion is with Kripke \cite{kripkeNN}.
Finally, historically speaking, we come to Williamson \cite{williamson2010}.

Though there is little explicit discussion of Carnap, his philosophical attitude, or something not so very far removed from it, underlies the entire work, which consists in a consideration of the various writings from a perspective similar to that of Carnap, one in which formal notations play a systematic and central role somewhat different from the manner in which they have typically been deployed since.
The principal differences with Carnap are my return to a more universalist pragmatic, by comparison with Caranap's mature pluralism.
Carnap would I think have understood the pragmatic reasons for this shift of emphasis.
The influence of Carnap extends beyond the perspective from which these historical developments are viewed, for when I leave the history behind and give my sketch of how to do without the modal concepts, the picture I paint, though differing greatly in detail from what Carnap might have said at the end of his life, is nevertheless in the spirit of his enterprise.

\subsection{Methods, Languages and Tools}

I had originally intended to include material on this topic in this document, but have now decided to have a separate document on that topic.
That document will be \emph{Formal Semantics and Deductive Methods}\cite{rbjt047}.

\section{Modal Reasoning in Higher Order Logic}

The approach we adopt here may be presented in relation to Frege's terminology.


\ignore{
=SML
open_theory "rbjmisc";
force_new_theory "t045";
force_new_pc ⦏"'t045"⦎;
merge_pcs ["'prove_∃_⇒_conv", "'savedthm_cs_∃_proof"] "'t045";
set_merge_pcs ["rbjmisc", "'t045"];
=TEX
}%ignore

The logical operators available in our logic are operations over truth values (values of type BOOL).
It is of course well known that the operations of the classical propositional logic are truth functional.

In this our logic corresponds to Frege's Begriffschrift and the values which we perceive ourselves as manipulating are his \emph{bedeutung}, specifically in the case of BOOLean terms (which are our formulae), the truth values $T$ and $F$.

Frege talks about natural language in which there are contexts in which the meaning of an expression differs from its meaning in the normal or customary context.
In such indirect contexts a phrase designates what would in a customary context be its \emph{sense}.
For Frege there are two kinds of context which radically affect the interpretation of expressions occurring in these contexts.

There are many different kinds of indirect context, but we are here interested only in the indirect contexts which are created by the modal concepts \emph{necessarily} and \emph{possibly}, so that we can draw from these particular contexts an idea of what kind of thing a `sense' must be in order for it to be a suitable basis form judgements of this kind.
The classic understanding of these modal concepts is in terms of `possible worlds'.
They operate rather like quantifiers over possible worlds, and for their application to make sense we therefore require them to be applied to things whose values may vary from one possible world to the next.

Our language provides a heirarchy of types of objects which are naturally though of as fixed in some absolute sense, rather than contingent.




Modal operators are not truth functional, and therefore must operate on propositions rather than their truth values.
This does not prevent them from being rendered in an extensional logic such as HOL.
The modal operators are said to be non-extensional or intensional from a point of view in which intension and extension are understood as similar to sense and reference.
The sense of a formula is then considered to be the proposition it expresses, and the reference is the truth value of the proposition.
An operator is extensional if it operates on the extension, the reference, the truth value, and intensional if it must be considered as operating on the intension, the sense.

The meaning of extensional in relation to higher order logic is related but distinct.
Our higher order logic is called extensional because it has functions in the domain of discourse and equality of functions is extensional, i.e. two functions are the same if they have the same extension.
The extension in question is the graph of the function.
Two functions are extensionally equal if they have the same domain and give the same result for every value in the domain.

We introduce a new type of entities which are our `possible worlds'.

=SML
new_type("W", 0);
=IGN
val W_def = new_type_defn(["W"], "W", [], tac_proof(([],⌜∃x:ℕ⦁(λy:ℕ⦁T)x⌝), ∃_tac ⌜εx:ℕ⦁T⌝ THEN rewrite_tac[] THEN strip_tac));

set_goal([], ⌜∃MkWorld:ℕ→W⦁ OneOne MkWorld⌝);
a (strip_asm_tac W_def);
a (fc_tac [type_lemmas_thm]);
a (∃_tac ⌜abs⌝ THEN asm_rewrite_tac[get_spec ⌜OneOne⌝]);
a (POP_ASM_T ante_tac THEN rewrite_tac[] THEN strip_tac);
a (REPEAT ∀_tac);

a (LEMMA_T ⌜x1 = rep(abs x1)⌝ once_rewrite_thm_tac THEN1 asm_rewrite_tac[]);
a (LEMMA_T ⌜x2 = rep(abs x2)⌝ once_rewrite_thm_tac THEN1 asm_rewrite_tac[]);

a (REPEAT strip_tac);
a (SYM_ASMS_T once_rewrite_tac);
a (SPEC_NTH_ASM_T 2 ⌜x1⌝ ante_tac);
a (rewrite_tac[]);
a (strip_tac);
a (once_asm_rewrite_tac[]);

a (STRIP_T once_rewrite_thm_tac);

 once_rewrite_thm_tac);
set_flag("pp_show_HOL_types", false);
=TEX

In a modal context values may be rigid or flexible.
Rigid values are the same in every possible world, flexible values vary across the possible worlds.
Flexible values are therefore functions whose domain is the type of possible worlds, and we introduce a type abbreviation for these types.

=SML
declare_type_abbrev ("⦏FLEX⦎", ["'a"], ⓣW → 'a⌝);
=TEX

Propositions are then flexible booleans:

=SML
declare_type_abbrev ("⦏PROP⦎", [], ⓣBOOL FLEX⌝);
=TEX

Necessitation may be defined over this notion of proposition as follows:

ⓈHOLCONST
│ ⦏⦈⦎ : PROP → PROP
├──────
│ ∀s⦁ ⦈ s = λw:W⦁ ∀v⦁ s v
■

Note that this is a propositional operator and therefore yields a proposition rather than a truth value.
The proposition is a function over possible worlds (an assignment of a truth value in every possible world) but it is a constant valued function, it yields the same truth value in every possible world.

When we assert a modal proposition we are asserting its truth not in all possible worlds but in the actual world.
To do this we first introduce a name for this world, and then define a `form of judgement' which asserts truth in the actual world.

For our present purposes we don't care what the actual world is, so the constant may be introduced as follows:

ⓈHOLCONST
│ ⦏actual_world⦎ : W
├──────
│ T
■

To assert a proposition is semantically analogous to the form `that p is true', in which it is implicit that truth is asserted in this, the actual world.
Formally that is ⌜p actual\_world ⇔ T⌝ which is logically equivalent to ⌜p actual\_world⌝.

ⓈHOLCONST
│ $⦏Ξ⋎s⦎ : PROP → BOOL
├──────
│ ∀p⦁ Ξ⋎s p ⇔ p actual_world
■

=SML
declare_alias("Ξ", ⌜Ξ⋎s⌝);
declare_prefix(5, "Ξ");
declare_prefix(5, "Ξ⋎s");
=TEX

\subsection{Lifting Logical Vocabulary}

The logical constants available to us \emph{ab inito} are operators over truth values.
To work with these modal notions we need to have similar operations defined over propositions.

Logical operations, such as conjunction, are fixed across all possible worlds, but must operate on propositions which may not be fixed.
It is therefore necessary to lift these operations to operate on propositions, propagating any contingency in their operands.
This is done \emph{pointwise}, i.e. the value of the result of an operation in some possible world is obtained from the values of the operands in that possible world.
A great deal of our desired vocabulary needs to be lifted in this rather mechanical way from operating over truth values to operating over propositions.

Since we have a higher order logic at our disposal, the operation of lifting is definable for arbitrary values of a given type.
To that end we define a number of operators which can be used to achieve this effect.

=SML
declare_postfix (400, "⋏↾");
declare_postfix (400, "⋏↿");
=TEX

ⓈHOLCONST
│ $⦏0⋏↾⦎ : 'b → ('a → 'b)
├──────
│ ∀t:'b⦁ 0⋏↾ t = λx:'a⦁ t
■

ⓈHOLCONST
│ $⦏1⋏↾⦎ : ('b → 'c) → (('a → 'b) → ('a → 'c))
├──────
│ ∀f⦁ 1⋏↾ f = λg⦁ λx⦁ f (g x)
■

ⓈHOLCONST
│ $⦏2⋏↾⦎ : ('b → 'c → 'd) → (('a → 'b) → ('a → 'c) → ('a → 'd))
├──────
│ ∀f⦁ 2⋏↾ f = λg h⦁ λx⦁ f (g x) (h x)
■

We can alias these all to the postfix superscript harpoon.

\ignore{
=SML
val l_defs = list_∧_intro (map get_spec [⌜0⋏↾⌝, ⌜1⋏↾⌝, ⌜2⋏↾⌝]);
=TEX
}%ignore

=SML
declare_alias ("⋏↿", ⌜0⋏↾⌝);
declare_alias ("⋏↾", ⌜1⋏↾⌝);
declare_alias ("⋏↾", ⌜2⋏↾⌝);
=TEX

and then use them to define a new set of propositional operators.
For present purposes these are opertors over type \emph{PROP} but it will be convenient later for the types to be more general.

=SML
declare_type_abbrev("GPROP", [], ⓣ'a → BOOL⌝);
=TEX

ⓈHOLCONST
│ ⦏T⋏↿⦎ ⦏F⋏↿⦎ 			:GPROP;
│ ⦏¬⋏↾⦎				:GPROP → GPROP;
│ ⦏∧⋏↾⦎ ⦏∨⋏↾⦎ ⦏⇒⋏↾⦎ ⦏⇔⋏↾⦎		:GPROP → GPROP → GPROP
├──────
│	T⋏↿ = T ⋏↿ 	∧ F⋏↿ = F ⋏↿	∧ ¬⋏↾ = ($¬) ⋏↾
│ ∧	∧⋏↾ = ($∧) ⋏↾	∧ ∨⋏↾ = ($∨) ⋏↾
│ ∧	⇒⋏↾ = ($⇒) ⋏↾	∧ ⇔⋏↾ = ($⇔) ⋏↾
■

which we can then alias back to the undecorated names:

=SML
declare_alias("¬", ⌜¬⋏↾⌝);
declare_alias("∧", ⌜∧⋏↾⌝);
declare_alias("∨", ⌜∨⋏↾⌝);
declare_alias("⇒", ⌜⇒⋏↾⌝);
declare_alias("⇔", ⌜⇔⋏↾⌝);
=TEX

In case we have to use the constant names we may as well have the fixities declared.

=SML
declare_prefix(50, "¬⋏↾");
declare_infix(40, "∧⋏↾");
declare_infix(30, "∨⋏↾");
declare_infix(20, "⇒⋏↾");
declare_infix(10, "⇔⋏↾");
=TEX

The following obvious theorem is useful in proving tautologies in this propositional language.
It eliminates operators over propositions in favour of operators over truth values

=GFT
⦏mprop_clauses⦎ =
   ⊢ ∀ w p q
     ⦁ (T⋏↿ w ⇔ T)
         ∧ (F⋏↿ w ⇔ F)
         ∧ ((¬ p) w ⇔ ¬ p w)
         ∧ ((p ∧⋏↾ q) w ⇔ p w ∧ q w)
         ∧ ((p ∨⋏↾ q) w ⇔ p w ∨ q w)
         ∧ ((p ⇒⋏↾ q) w ⇔ p w ⇒ q w)
         ∧ ((p ⇔⋏↾ q) w ⇔ p w ⇔ q w)
=TEX

\ignore{
=IGN
set_flag("pp_use_alias", false);
=SML
val Ξ_def = get_spec ⌜$Ξ⌝;

set_goal([], ⌜
	∀w p q⦁ (T⋏↿ w ⇔ T)
	∧	(F⋏↿ w ⇔ F)
	∧	((¬ p) w ⇔ ¬ (p w))
	∧	((p ∧ q) w ⇔ p w ∧ q w)
	∧	((p ∨ q) w ⇔ p w ∨ q w)
	∧	((p ⇒ q) w ⇔ (p w ⇒ q w))
	∧	((p ⇔ q) w ⇔ (p w ⇔ q w))
	⌝);
a (rewrite_tac[get_spec ⌜T⋏↿⌝, l_defs ]);
val mprop_clauses = save_pop_thm "mprop_clauses";

add_pc_thms "'t045" [mprop_clauses];
set_merge_pcs ["rbjmisc", "'t045"];
=TEX
}%ignore

Now that we have negation over propositions we can define possibility in terms of necessity.

ⓈHOLCONST
│ ⦏⦇⦎ : PROP → PROP
├──────
│ ∀s⦁ ⦇ s = ¬ ⦈ (¬ s)
■

ⓈHOLCONST
│ ⦏=⋏↾⦎	:'a FLEX → 'a FLEX → PROP
├──────
│  =⋏↾ = $= ⋏↾
■

=IGN
declare_alias ("=", ⌜=⋏↾⌝);
=SML
declare_infix (200, "=⋏↾");
=TEX

Because they bind variables, the quantifiers are themselves higher order operators and cannot be lifted in the same way.
It is nevertheless straightforward.
Note that because these definitions are given in a polymorphic higher-order logic, they define quantifiers of any finite order, not merely first-order quantifiers.
The order of the type to which the type variable \emph{'a} is instantiated determines the order of the quantifier.

ⓈHOLCONST
│ ⦏∀⋏↾⦎	:(('a FLEX) → PROP) → PROP
├──────
│  ∀⋏↾ = λf w⦁ $∀ (λx⦁ f x w)
■

=SML
declare_alias ("∀", ⌜∀⋏↾⌝);
declare_binder "∀⋏↾";
=TEX

ⓈHOLCONST
│ ⦏∃⋏↾⦎	:(('a FLEX) → PROP) → PROP
├──────
│  ∃⋏↾ = λf⦁ ¬ $∀ (λx⦁ ¬ f x)
■

=SML
declare_alias ("∃", ⌜∃⋏↾⌝);
declare_binder "∃⋏↾";
=TEX

=GFT
⦏⦇⦈⋏↾_thm⦎ =	⊢ ∀ w p⦁ (⦈ p w ⇔ (∀ w2⦁ p w2)) ∧ (⦇ p w ⇔ (∃ w2⦁ p w2))
⦏Eq⋏↾_thm⦎ =	⊢ ∀ w x y⦁ (x =⋏↾ y) w ⇔ x w = y w
⦏∀∃⋏↾_thm⦎ =		⊢ ∀ w p⦁ ($∀ p w ⇔ (∀ x⦁ p x w)) ∧ ($∃ p w ⇔ (∃ x⦁ p x w))
=TEX

\ignore{
=SML
val Eq⋏↾_def = get_spec ⌜$=⋏↾⌝;
val ⦈_def = get_spec ⌜$⦈⌝;
val ⦇_def = get_spec ⌜$⦇⌝;
val ∀⋏↾_def = get_spec ⌜$∀⋏↾⌝;
val ∃⋏↾_def = get_spec ⌜$∃⋏↾⌝;

set_goal([], ⌜∀(w:W) p⦁ (⦈ p w ⇔ ∀w2⦁ p w2)
		∧	(⦇ p w ⇔ ∃w2⦁ p w2)⌝);
a (rewrite_tac [⦇_def, ⦈_def, l_defs]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
val ⦇⦈⋏↾_thm = save_pop_thm "⦇⦈⋏↾_thm";

set_goal([], ⌜
	∀(w:W) x (y:'a FLEX)⦁ 
		((x =⋏↾ y) w ⇔ x w = y w)
	⌝);
a (rewrite_tac [Eq⋏↾_def, l_defs]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
val Eq⋏↾_thm = save_pop_thm "Eq⋏↾_thm";

set_goal([], ⌜
	∀(w:W) (p:'a FLEX → PROP)⦁ 
		($∀ p w ⇔ ∀x⦁ p x w)
	∧	($∃ p w ⇔ ∃x⦁ p x w)
	⌝);
a (rewrite_tac [∀⋏↾_def, ∃⋏↾_def, l_defs]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val ∀∃⋏↾_thm = save_pop_thm "∀∃⋏↾_thm";

add_pc_thms "'t045" [⦇⦈⋏↾_thm, Eq⋏↾_thm, ∀∃⋏↾_thm, mprop_clauses];
set_merge_pcs ["rbjmisc", "'t045"];
=TEX
}%ignore

\subsection{Laws}

The following results are now provable, demonstrating the consistency of the definitions with the semantics of the modal logic S5.

First we have modus ponens and the axioms of the propositional logic lifted over type BOOL FLEX.

=GFT
⦏Ξmp_thm⦎ =	Ξ A, Ξ A ⇒ B ⊢ Ξ B
⦏Ξax1_thm⦎ =	⊢ Ξ p ⇒ q ⇒ p
⦏Ξax2_thm⦎ =	⊢ Ξ (p ⇒ q ⇒ r) ⇒ (p ⇒ q) ⇒ p ⇒ r
⦏Ξax3_thm⦎ =	⊢ Ξ (¬ p ⇒ ¬ q) ⇒ q ⇒ p
=TEX

\ignore{
=SML
set_goal([⌜Ξ A⌝, ⌜Ξ A ⇒ B⌝], ⌜Ξ B⌝);
a (REPEAT (POP_ASM_T ante_tac));
a (rewrite_tac [get_spec ⌜$Ξ⌝]);
val Ξmp_thm = save_pop_thm "Ξmp_thm";

set_goal([], ⌜Ξ p ⇒ (q ⇒ p)⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝] THEN contr_tac);
val Ξax1_thm = save_pop_thm "Ξax1_thm";

set_goal([], ⌜Ξ (p ⇒ q ⇒ r) ⇒ ((p ⇒ q) ⇒ (p ⇒ r))⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝] THEN contr_tac);
val Ξax2_thm = save_pop_thm "Ξax2_thm";

set_goal([], ⌜Ξ (¬ p ⇒ ¬ q) ⇒ (q ⇒ p)⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝] THEN contr_tac);
val Ξax3_thm = save_pop_thm "Ξax3_thm";

=IGN
set_goal([], ⌜Ξ T⋏↿⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝]);
val Ξ_T_thm = save_pop_thm "Ξ_T_thm";

set_goal([], ⌜Ξ A ∧ B ⇒ A⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝] THEN contr_tac);
val Ξ_ABA_thm = save_pop_thm "Ξ_ABA_thm";
=TEX
}%ignore

Arbitrary propositional tautologies are therefore true under the definitions given.

The necessitation rule talks about the deductive system, which we have not formalised, so we cannot express it.
It should nevertheless be true of this system.

Next we have the modal axioms.
The modal operators quantify over all possible worlds, without reference to an accessibility relation so the will correspond to S5.
The following list of theorems proven in this system contains all but one of the candidate axioms listed at the Stanford Encyclopaedia entry on modal logic and the names used are taken from there (apart from adding `A' in front of the numeric names and adding `\_thm' after them all).
One does not need them all, of course, but we prove from the semantic definitinos

=GFT
⦏distrib_thm⦎ =	⊢ Ξ ⦈ (A ⇒ B) ⇒ ⦈ A ⇒ ⦈ B
⦏D_thm⦎ =		⊢ Ξ ⦈ A ⇒ ⦇ A
⦏M_thm⦎ =		⊢ Ξ ⦈ A ⇒ A
⦏A4_thm⦎ =		⊢ Ξ ⦈ A ⇒ ⦈ (⦈ A)
⦏B_thm⦎ =		⊢ Ξ A ⇒ ⦈ (⦇ A)
⦏A5_thm⦎ =		⊢ Ξ ⦇ A ⇒ ⦈ (⦇ A)
⦏⦈M_thm⦎ =	⊢ Ξ ⦈ (⦈ A ⇒ A)
⦏C4_thm⦎ =		⊢ Ξ ⦈ (⦈ A) ⇒ ⦈ A
⦏C_thm⦎ =		⊢ Ξ ⦇ (⦈ A) ⇒ ⦈ (⦇ A)
=TEX

\ignore{
=SML
set_goal([], ⌜Ξ ⦈(A ⇒ B) ⇒ ⦈ A ⇒ ⦈ B⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝] THEN prove_tac[]);
val distrib_thm = save_pop_thm "distrib_thm";

set_goal([], ⌜Ξ (⦈ A) ⇒ ⦇ A⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝] THEN prove_tac[]);
val D_thm = save_pop_thm "D_thm";

set_goal([], ⌜Ξ (⦈ A) ⇒ A⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝] THEN prove_tac[]);
val M_thm = save_pop_thm "M_thm";

set_goal([], ⌜Ξ (⦈ A) ⇒ (⦈ (⦈ A))⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝] THEN prove_tac[]);
val A4_thm = save_pop_thm "A4_thm";

set_goal([], ⌜Ξ A ⇒ (⦈ (⦇ A))⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝] THEN prove_tac[]);
val B_thm = save_pop_thm "B_thm";

set_goal([], ⌜Ξ (⦇ A) ⇒ (⦈ (⦇ A))⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝] THEN prove_tac[]);
val A5_thm = save_pop_thm "A5_thm";

set_goal([], ⌜Ξ ⦈((⦈ A) ⇒ A)⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝] THEN prove_tac[]);
val ⦈M_thm = save_pop_thm "⦈M_thm";

set_goal([], ⌜Ξ (⦈ (⦈ A)) ⇒ (⦈ A)⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝] THEN prove_tac[]);
val C4_thm = save_pop_thm "C4_thm";

set_goal([], ⌜Ξ (⦇ (⦈ A)) ⇒ (⦈ (⦇ A))⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝] THEN prove_tac[]);
val C_thm = save_pop_thm "C_thm";
=TEX
}%ignore

=GFT
⦏BF_thm⦎ =	⊢ Ξ ⦇ (∃ x⦁ A) ⇒ (∃ x⦁ ⦇ A)
⦏CBF_thm⦎ =	⊢ Ξ (∃ x⦁ ⦇ A) ⇒ ⦇ (∃ x⦁ A)
=TEX

\ignore{
=SML
set_goal([], ⌜Ξ (⦇ ((∃x:'a FLEX⦁ A x))) ⇒ ((∃x:'a FLEX⦁ (⦇ (A x))))⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝] THEN prove_tac[]);
val BF_thm = save_pop_thm "BF_thm";

set_goal([], ⌜Ξ ((∃x:'a FLEX⦁ (⦇ (A x)))) ⇒ (⦇ ((∃x:'a FLEX⦁ A x)))⌝);
a (rewrite_tac [get_spec ⌜$Ξ⌝] THEN prove_tac[]);
val CBF_thm = save_pop_thm "CBF_thm";
=TEX
}%ignore

\subsection{Further Vocabulary}

=SML
declare_infix(210, ">⋏↾");
=TEX

ⓈHOLCONST
│ $⦏>⋏↾⦎ :  ℕ FLEX → ℕ FLEX → PROP
├──────
│ $>⋏↾ = $> ⋏↾
■

=SML
declare_alias(">", ⌜$>⋏↾⌝);
=TEX

=GFT
⦏gt⋏↾_thm⦎ =	⊢ ∀l r w⦁ (l >⋏↾ r) w = l w > r w
=TEX

\ignore{
=SML
val gt⋏↾_def = get_spec ⌜$>⋏↾⌝;

set_goal([], ⌜∀l r w⦁ (l >⋏↾ r) w = l w > r w⌝);
a (rewrite_tac [gt⋏↾_def, l_defs, ext_thm]);
val gt⋏↾_thm = save_pop_thm "gt⋏↾_thm";
=TEX
}%ignore


\section{Quine on Reference and Modality}

\ignore{
=SML
open_theory "t045";
force_new_theory "t045q";
force_new_pc ⦏"'t045q"⦎;
merge_pcs ["'prove_∃_⇒_conv", "'savedthm_cs_∃_proof"] "'t045q";
set_merge_pcs ["rbjmisc", "'t045", "'t045q"];
=TEX
}%ignore


With some formal machinery in hand we now come to consider some of the reservations expressed by Quine in his `Reference and Modality' \cite{quineRM}.
This essay is a fusion of two earlier essays dating from 1943 and 1947, first published in 1953 substantially updated as of 1961 and subject to a correction in 1980.
It represents Quine's considered and mature opinions in 1961.

The controversy arising from this paper was accompanied and followed by significant further advances in technical studies of modal logics, the highly influential semantic treatment of modal logics due to Kripke first appeared in the late 1950's, but seems to have had no impact on Quine's paper.
The principal innovation in Kripke's work is the so called `frame semantics' in which the scope of modal quantifiers is constrained by an accessibility relation between frames.
This is most significant in allowing these formal systems to be applied to modalities other than necessity, and will not be discussed in this essay.
Kripke is also associated with the concept of rigidity (of designators) which we will touch upon in later sections.

A central theme is the logical difficulties arising from referential opacity, particularly but not exclusively when this is engendered by modal concepts.
The present methods are purely semantic, and enable us to cast light on the kinds of thing which might possibly be meant by the various difficult sentences considered by Quine, and to determine whether the sentences are true when understood in these ways.
This is possible because we have an expressive higher order logic in which the relevant concepts can be formally defined together with a tool which checks specifications to ensure that they are well formed and that they represent conservative extensions over the previous theory.
This means that the expressions we put forward have a definite meaning, however strange that might be.
The tool also supports formal reasoning.
It will aid and abet the construction of detailed formal proofs, will confirm the correctness of the proofs and make a definitive and reliable listing of the results obtained together with the definitions in the context of which they were derived (see Appendix \ref{t045q}).

Our method is exclusively semantic, and the examples which Quine considers involving mention of syntax will therefore not be considered.
This also creates a distance between the considerations of modality here and those of Carnap, who took analyticity as the principle notion and sometimes defined necessity in terms of analyticity.
If we take necessity as a property of semantic entities which we call propositions, then the it is less difficult to discover conditions under which substitution can take place even in referentially opaque contexts.

\subsection{Substitution and Opacity}

Quine mentions first a general principle to which problems of opacity give rise to exceptions.

This is the principle of \emph{substitutivity}\index{substitutivity}, which is that equal terms may be substituted \emph{salva-veritate}.
To this principle he finds exceptions in quotations and in other contexts, but claims that the basis is solid, that whatever is true of something is true of anything equal to it.
This second statement of the principle suggests a manner of resolution, which is that the procedure be limited to cases in which what is said is said of the person or thing referred to by the term rather than of the term itself.
The term `purely referential' is introduced for those occurrences of a term which do nothing more than designate and which therefore can be replaced by any other method of referring (purely) to that same designatum.

\begin{itemize}


\item[(3)] Cicero = Tully

Quine's central theme consists in identifying those circumstances in which an identity does not warrant a substitution.
The possibility of there being different kinds of identity is less thoroughly considered.
He does note the preference of Church for variables ranging over intensions, but raises objections to this which we will consider later.

To confirm Quine's observations in our formal sandbox we have to chose exactly what meaning is to be given to the identity.
There are two dimensions of choice which affect this.
The first is how the names are to be construed.
They can be construed as sense or reference, which will be reflected in our model by whether or not they have the FLEX type which we use for intensions, the signficance of which is that the reference may vary from one world to the next.
If they are not intensions, then they must be what later came to be known as rigid designators, and substitution in some referentially opaque contexts will be acceptable.
I say `some' here because it is not clear that in natural English the referentially opaque contexts all behave in the same manner in relation to substitutions.
We are confining our attention to opaque contexts in which the opacity arises from the use of some propositional operator, such as a modal operator, or from the expression of a propositional attitude.
Implicit in these terms is the idea that they all have in common that they concern propositions, and it is easy to assume that just one notion of proposition is required in the explanation of each of these contexts.
This probably is not the case in natural English, and some of Quine's examples suffice to bring this out even though he does not use them for this purpose.

It is not an issue for Quine because once he has established that a simple identity does not justify a substitution, he does not consider whether something stronger would.
However, we find with our model that a necessary identity does justify the substitution.
This is connected to the later doctrine that the necessity follows from the rigidity of the names, for an identity between rigid designators must be a necessary identity.
Thus rigidy is a special case of the more general justification of necessary identity.
But does this always allow substitution into opaque contexts.
It does seem to do so for the modal contexts, but propositional attitudes may be less objective.
Even if the identity between Cicero and Tully is necessary, we may not be free to infer from a belief about Cicero a belief about Tully.
This is moot in the case that the believer does not know the identity.

If there is a single objective notion of proposition at stake, and our model of propositions as FLEX values is good, then we can show that a necessary identity does legitimate substitution in opaque contexts.

The formal development will stick with a single notion of proposition despite these considerations.

Let us first introduce Cicero and Tully.

\ignore{
=IGN
set_goal([], ⌜∃Cicero Tully:IND FLEX⦁ ¬ Cicero = Tully ∧ Ξ Cicero =⋏↾ Tully⌝);
a (strip_asm_tac infinity_axiom);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜Onto⌝]);
a (strip_tac);
a (∃_tac ⌜λz⦁ if z = actual_world then y else f y⌝);
a (∃_tac ⌜λz⦁ y⌝);
a (rewrite_tac [ext_thm] THEN REPEAT strip_tac);
a (∃_tac ⌜λz⦁ y⌝);

=TEX
}%ignore

The names are introduced as unspecified constants and we will reason from various assumptions about them.
That we take names to be of type FLEX admits the possibility that a name might not name the same individual in every possible world.

ⓈHOLCONST
│ ⦏Cicero⦎ ⦏Tully⦎ ⦏Cataline⦎ ⦏Phillip⦎ ⦏Tegucicalpa⦎ ⦏Mexico⦎ ⦏Honduras⦎: IND FLEX
├──────
│ T
■

ⓈHOLCONST
│ ⦏Capital_of⦎ ⦏Location_of⦎ : IND FLEX → IND FLEX
├──────
│ T
■

Relations are maps from flexible individuals delivering propositions.

ⓈHOLCONST
│ $⦏denounced⦎ : IND FLEX → IND FLEX → PROP
├──────
│ T
■

=SML
declare_infix(200,"denounced");
=TEX

We also introduce a type abbreviation for propositional attitudes.
A propositional attitude is a function which takes some flex value and a proposition and returns a proposition (a BOOL FLEX).

=SML
declare_type_abbrev("PA", [], ⓣ'a FLEX → PROP → PROP⌝);
=TEX

The following are propositional attitudes.

ⓈHOLCONST
│ ⦏unaware⦎ ⦏believes⦎: PA
├──────
│ T
■

=SML
declare_infix(200, "unaware");
declare_infix(200, "believes");
=TEX

Quine's illustrates the opacity in the context of propositional attitudes by observations which we may formalise as:

\ignore{
=SML
set_goal([], ⌜Ξ Phillip unaware (Tully denounced Cataline) ∧ ⦈ (Tully =⋏↾ Cicero)
		⇒ Phillip unaware (Cicero denounced Cataline)
⌝);
a (rewrite_tac [Ξ_def]);
a (REPEAT strip_tac);
a (LEMMA_T ⌜Cicero = Tully⌝ asm_rewrite_thm_tac THEN1 asm_rewrite_tac [ext_thm]);
val QT09a = save_pop_thm "QT09a";
=TEX
}%ignore

\item[(9)] Phillip is unaware that Tully denounced Cataline (true)

\ignore{

=IGN
declare_infix(150, "unaware_");
declare_infix(150, "denounced_");

stop;
set_goal([⌜∃x⦁ ¬ x = actual_world⌝], ⌜∃ phillip $unaware_ tully $denounced_ cataline⦁ Ξ phillip unaware_ (tully denounced_ cataline) ∧ (tully =⋏↾ cicero)
		∧ ¬  phillip unaware_ (cicero denounced_ cataline)
⌝);
a (rewrite_tac [Ξ_def]);
a (REPEAT strip_tac);
a (LEMMA_T ⌜Cicero = Tully⌝ asm_rewrite_thm_tac THEN1 asm_rewrite_tac [ext_thm]);
val QT09a = save_pop_thm "QT09a";
=TEX
}%ignore



\item[(10)] Phillip believes that Tegucigalpa is in Mexico (true)
\item[(10b)] Tegucigalpa is the capital of the Honduras (true)
\item[(11)] Phillip is unaware that Cicero denounced Cataline (false)
\item[(12)] Phillip believes that the capital of the Honduras is in Mexico (false)

=GFT
⦏QT15a⦎ = ⊢ Ξ ⦈ ((9 > 7) ⋏↿)
=TEX

\ignore{
=SML
set_goal([], ⌜Ξ ⦈ ((9 > 7)⋏↿)⌝);
a (rewrite_tac [Ξ_def, l_defs] THEN PC_T1 "lin_arith" rewrite_tac[]);
val QT15a = save_pop_thm "QT15a";
=TEX
}%ignore

=GFT
⦏QT15b⦎ =	⊢ Ξ ⦈ (9 ⋏↿ >⋏↾ 7 ⋏↿)
=TEX

\ignore{
=SML
set_goal([], ⌜Ξ ⦈ (9 ⋏↿ >⋏↾ 7 ⋏↿)⌝);
a (rewrite_tac [Ξ_def, l_defs, gt⋏↾_thm] THEN PC_T1 "lin_arith" rewrite_tac[]);
val QT15b = save_pop_thm "QT15b";
=TEX
}%ignore

\item[(15)] 9 is necessarily greater than 7 (true)


\item[(16)] necessarily if there is life on the evening star there is life on the evening star (false)
\item[(17)] the number of planets is possibly less than 7 (true)
\item[(18)] the number of planets is necessarily greater than 7 (false)
\item[(19)] necessarily if there is life on the evening star there is life on the morning star (false)
\item[(20)] 9 is possibly less than 7 (false)
\item[(24)] 9 = the number of planets (true)
\item[(25)] the evening star = the morning star (true)
\end{itemize}

For an example we introduce a FLEX value which it a collection of planets.
We don't say what they are, we just give it the type $ℕ FLEX$ which is that of a number which varies between possible worlds.

=SML
new_type ("BODIES", 0);
=TEX


ⓈHOLCONST
│ ⦏Planets⦎ ⦏Moons⦎:(BODIES SET)FLEX
├──────
│  T
■

ⓈHOLCONST
│ ⦏≤⋏↾⦎: ℕ FLEX → ℕ FLEX → PROP
├──────
│  ≤⋏↾ = $≤ ⋏↾
■

ⓈHOLCONST
│ ⦏Size⋏↾⦎: ('a SET) FLEX → ℕ FLEX
├──────
│  Size⋏↾ = Size ⋏↾
■

=SML
declare_infix(210, "≤⋏↾");
declare_alias ("≤", ⌜$≤⋏↾⌝);
declare_alias ("#", ⌜Size⋏↾⌝);
=TEX

=GFT
⦏≤⋏↾_thm⦎ =	⊢ ∀ x y w⦁ (x ≤ y) w ⇔ x w ≤ y w 
⦏Size⋏↾_thm⦎ =	⊢ ∀ s w⦁ # s w = # (s w)
=TEX


\ignore{
=SML
val ≤⋏↾_def = get_spec ⌜$≤⋏↾⌝;
val Size⋏↾_def = get_spec ⌜Size⋏↾⌝;

set_goal([], ⌜∀x y w⦁ (x ≤⋏↾ y) w = x w ≤ y w⌝);
a (rewrite_tac[≤⋏↾_def, l_defs]);
val ≤⋏↾_thm = save_pop_thm "≤⋏↾_thm";

set_goal([], ⌜∀s w⦁ Size⋏↾ s w = #(s w)⌝);
a (rewrite_tac[Size⋏↾_def, l_defs]);
val Size⋏↾_thm = save_pop_thm "Size⋏↾_thm";
=TEX
}%ignore

\subsection{Quantification and Opacity}

Quine now goes on to say that not only does substitution into opaque contexts fail, but also quantification.
The discussion begins with existential generalisation, and the problem arises in seeking some \emph{entity} to justify an existential generalisation enclosing an opaque context.

\begin{itemize}
\item[(29)] Something is such that Phillip is unaware that it denounced Catiline (nonesense)
\item[(30)] ∃x⦁ (x is necessarily greater than 7) (nonesense)
\item[(31)] ∃x⦁ (necessarily if there is life on the evening star there is life on x) (nonesense)
\item[(32)] x = $\sqrt{x}$ + $\sqrt{x}$ + $\sqrt{x}$ ≠ $\sqrt{x}$ (entails x = 9)
\item[(33)] there are exactly x planets (does not entail x = 9)
\item[(34)] if there is life on the evening star, there is life on x (can only be necessary in relation to a particular description of x)
\end{itemize}

=GFT
⦏NumPlanets_thm⦎ = ⊢ Ξ (∃ x⦁ ⦈ (# Planets ≤ x))
=TEX

\ignore{
=SML
set_goal ([], ⌜Ξ ∃x⦁ ⦈ ((Size⋏↾ Planets) ≤ x)⌝);
a (rewrite_tac [Ξ_def]);
a (∃_tac ⌜(Size⋏↾ Planets)⌝ THEN rewrite_tac[≤⋏↾_thm, Size⋏↾_thm]);
val NumPlanets_thm = save_pop_thm "NumPlanets_thm";
=TEX
}%ignore


\subsection{Reconciling Quantification and Modality}

Here are four theorems which tell us in different ways sufficient conditions for substitution into opaque or indirect contexts.

The first is the most straightforward statement of the principle, which is that when two intensions are necessarily equal they can be substituted into a necessitation:

=GFT
⦏modal_subst_thm⦎ =
	⊢ ∀ P⦁ Ξ (∀ x⦁ ∀ y⦁ ⦈ (x =⋏↾ y) ⇒ (⦈ (P x) ⇔ ⦈ (P y)))
=TEX

In the indirect or opaque context of the necessitation on the left, the identity between the $x$ and $y$ says that in the current world these two identifiers take the same value.
The necessitation then generalises that claim to all possible worlds.
So, to say that two intensions are necessarily equal is to say that in every possible world the value taken by the two intensions is the same.
Since our intensions are in fact extensional this entails that the two extensions are equal.

Before looking at other informative ways of saying the same thing, we note that this is a general principle about substitution into opaque contexts and so we can replace the necessitation on the right with a variable ranging over all propositional operators:

=GFT
⦏opaque_subst_thm⦎ =
	⊢ ∀ PoP⦁ Ξ (∀ x⦁ ∀ y⦁ ⦈ (x =⋏↾ y) ⇒ (PoP (P x) ⇔ PoP (P y)))
=TEX

This theorem tells us that necessarily equal modal values can be substituted in the context of any function over propositions.
In other words, a modal equality gives a modal truth value (which is a proposition) from two modal values.
That proposition will be true in any possible world in which the two modal values are contingently equal.
If that proposition is necessary then the two modal values are identical simpliciter, not contingently.

If we step outside the modal context, in Frege's terms from an indirect context to a standard one, then a simple equation suffices to identify two intensions abosolutely, not just contingently, which is shown by the following theorem:

=GFT
⦏fixed_neceq_thm⦎ =
	⊢ ∀x y⦁ x = y ⇒ (Ξ ⦈ (x =⋏↾ y))
=TEX


We can also drop out of the modal context locally to invoke the standard equality rather than the modal equality:

=GFT
⦏fixed_neceq_thm2⦎ =
	⊢ Ξ (∀ x⦁ ∀ y⦁ (x = y) ⋏↿ ⇒ ⦈ (x =⋏↾ y))
=TEX

In this case the postfix $⋏↿$ operator lifts a truth value to a proposition, and hence creates a context on its left where a truth value rather than a proposition is expected, which is supplied by the standard equality applied to the two intensional values.


\ignore{
set_goal([], ⌜∀P⦁ Ξ (∀x y⦁ ⦈ (x =⋏↾ y) ⇒ (⦈ (P x) ⇔ ⦈ (P y)))⌝);
a (rewrite_tac [Ξ_def] THEN REPEAT_N 4 strip_tac);
a (LEMMA_T ⌜x = x'⌝ rewrite_thm_tac THEN1 asm_rewrite_tac [ext_thm]);
val modal_subst_thm = save_pop_thm "modal_subst_thm";

set_goal([], ⌜∀PoP:PROP→PROP⦁ Ξ (∀x y⦁ ⦈ (x =⋏↾ y) ⇒ (PoP (P x) ⇔ PoP(P y)))⌝);
a (rewrite_tac [Ξ_def] THEN REPEAT_N 4 strip_tac);
a (LEMMA_T ⌜x = x'⌝ rewrite_thm_tac THEN1 asm_rewrite_tac [ext_thm]);
val opaque_subst_thm = save_pop_thm "opaque_subst_thm";

set_goal([], ⌜(∀x y⦁ x = y ⇒ Ξ ⦈ (x =⋏↾ y))⌝);
a (rewrite_tac [Ξ_def] THEN REPEAT_N 4 strip_tac THEN asm_rewrite_tac[]);
val fixed_neceq_thm = save_pop_thm "fixed_neceq_thm";

set_goal([], ⌜Ξ(∀x y⦁ (x = y)⋏↿ ⇒ ⦈ (x =⋏↾ y))⌝);
a (rewrite_tac [Ξ_def, l_defs] THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
val fixed_neceq_thm2 = save_pop_thm "fixed_neceq_thm2";
=TEX
}%ignore

\subsubsection{Intensions}

Having discussed the problems Quine moves to something like analysis of the viable options for quantified modal logics, with a critique of some of the then recent attempts to effect the combination.

In discussing the ideas of Carnap and Church to the effect that the problem of substitution into modal contexts should be addressed by quantifying over intensional rather than extensional values, Quine puts forward an argument which he seems to think rules this out.

I shall look at some aspects of this in greater detail than might otherwise be necessary because it does provide an example of how formalisation exposes issues which may otherwise be overlooked.

Before doing this, it may be noted that an argument along the lines given here should have been sufficient earlier for Quine to abandon his attempt to sanitise substitution into modal contexts by eliminating entities which have more than one synonymy class of referring expressions, for it is a demonstration that there could be no such entities.

Quine secures the effect using a definite description operator to obtain from an arbitrary expression A an expression which refers to the same individual but is not `intensionally' the same as that individual.

It is taken to be immediately apparent that the equation he offers is indeed true:

=GFT
(35)	A = ιx⦁ p ∧ x = A	
=TEX

Even though \emph{p} is said to be contingently but not necessarily true.
In a classical non-modal quantification this is indeed easily seen to be true.

\begin{itemize}
\item[(36)] necessarily (x = x)
\item[(37)] ~ necessarily (p ∧ x = x)
\item[(38)] ∀x y⦁ x = y ⇒ necessarily x = y
\end{itemize}

In the course of his discussion Quine considers the proposal that variables quantified into a modal context should range over essences.
Against that he cites the following:

\ignore{
=SML
set_goal([], ⌜∃ι:('a → BOOL) → 'a⦁ ∀x⦁ ι (λy:'a⦁ y = x) = x⌝);
a (∃_tac ⌜λ(p:'a → BOOL)⦁ εy⦁ p y⌝);
a (rewrite_tac[ext_thm] THEN REPEAT strip_tac);
a (ε_tac ⌜ε y⦁ y = x⌝);
a (∃_tac ⌜x⌝ THEN rewrite_tac[]);
save_cs_∃_thm(pop_thm());
=TEX
}%ignore

The following defines the non-modal definite description operator.

ⓈHOLCONST
│ ⦏ι⦎: ('a → BOOL) → 'a
├──────
│ ∀x⦁ ι(λy⦁ y = x) = x 
■

=SML
declare_binder("ι");
=TEX

Using this definition we can prove:

=GFT
⦏QT35a⦎ = ⊢ p ⇒ A = (ι x⦁ p ∧ x = A)
=TEX

\ignore{
=SML
val ι_def = get_spec ⌜$ι⌝;

set_goal([], ⌜p ⇒ A = ιx⦁ p ∧ x = A⌝);
a (strip_tac THEN asm_rewrite_tac[ι_def]);
val QT35a = save_pop_thm "QT35a";
=TEX
}%ignore

This holds whatever kind of thing A is.
But the similarity with (35) is superficial, for here `p' is of type BOOL, and cannot be contingently true, and so the identity on the right is also not contingently true.

In order to express this in a way which makes the question of analyticity meaningful (which in our syntax-free treatment becomes the question of necessity) we must have `p' as a proposition rather than a truth value, and for this purpose we need a modal definite description which operates on a propositional function rather than a truth valued function.

Such an operator may be defined thus:

\ignore{
=SML
set_goal([], ⌜∃ι⋏↾⋏?:('a FLEX → PROP) → 'a FLEX⦁ ∀x⦁ ι⋏↾⋏? (λy:'a FLEX⦁ y =⋏↾ x) = x⌝);
a (∃_tac ⌜λ(p:'a FLEX → PROP)⦁ λw⦁ εy⦁ p (λv⦁y) w⌝);
a (rewrite_tac[ext_thm] THEN REPEAT strip_tac);
a (ε_tac ⌜ε y⦁ y = x x'⌝);
a (∃_tac ⌜x x'⌝ THEN rewrite_tac[]);
save_cs_∃_thm(pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏ι⋏↾⋏?⦎: ('a FLEX → PROP) → 'a FLEX
├──────
│ ∀x⦁ ι⋏↾⋏? (λy⦁ y =⋏↾ x) = x
■

=IGN
declare_alias("ι", ⌜ι⋏↾⋏?⌝);
=SML
declare_binder("ι⋏↾⋏?");
=TEX

Using this definition the above result no longer obtains, since p now appears in a modal context.
The best we can do is:

=GFT
⦏QT35b⦎ = ⊢ Ξ ⦈ p ⇒ A =⋏↾ (ι⋏↾⋏? x⦁ p ∧ x =⋏↾ A)
=TEX

\ignore{
=SML
val ι⋏↾⋏q_def = get_spec ⌜$ι⋏↾⋏?⌝;

set_goal([], ⌜Ξ (⦈ p) ⇒ A =⋏↾ ι⋏↾⋏? x⦁ p ∧ x =⋏↾ A⌝);
a (asm_rewrite_tac[Ξ_def] THEN strip_tac);
a (lemma_tac ⌜p = T⋏↿⌝ THEN asm_rewrite_tac [ext_thm, l_defs]);
a (lemma_tac ⌜∀x⦁ (T⋏↿ ∧ x =⋏↾ A) = (x =⋏↾ A)⌝ THEN1 asm_rewrite_tac [ext_thm, l_defs]);
a (lemma_tac ⌜(λx⦁ T⋏↿ ∧ x =⋏↾ A) = (λx⦁ x =⋏↾ A)⌝ THEN1
	(asm_rewrite_tac [ext_thm] THEN strip_tac THEN asm_rewrite_tac[]));
a (asm_rewrite_tac[ι⋏↾⋏q_def]);
val QT35b = save_pop_thm "QT35b";
=TEX
}%ignore

\ignore{
=SML
set_goal([], ⌜∃ι⋏↾:('a FLEX → PROP) → 'a FLEX⦁ ∀p x w⦁ (∃y⦁ p y w) ∧ (∀y⦁ p y w ⇒ y w = x) ⇒ ι⋏↾ p w = x⌝);
a (∃_tac ⌜λ(p:'a FLEX → PROP)⦁ λw⦁ εx⦁ (∃y⦁ p y w) ∧ ∀y⦁ p y w ⇒ y w = x⌝);
a (rewrite_tac[ext_thm] THEN REPEAT strip_tac);
a (ε_tac ⌜ε x⦁ (∃ y⦁ p y w) ∧ (∀ y⦁ p y w ⇒ y w = x)⌝);
(* *** Goal "1" *** *)
a (∃_tac ⌜x⌝ THEN REPEAT strip_tac THEN asm_fc_tac[]);
a (∃_tac ⌜y⌝ THEN strip_tac);
(* *** Goal "2" *** *)
a (asm_fc_tac[]);
a (SYM_ASMS_T rewrite_tac);
save_cs_∃_thm(pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏ι⋏↾⦎: ('a FLEX → PROP) → 'a FLEX
├──────
│ ∀p x w⦁ (∃y⦁ p y w) ∧ (∀y⦁ p y w ⇒ y w = x) ⇒ ι⋏↾ p w = x
■

=SML
declare_alias("ι", ⌜ι⋏↾⌝);
declare_binder("ι⋏↾");
=TEX

=GFT
⦏QT35c⦎ = ⊢ Ξ p ⇒ A =⋏↾ (ι⋏↾ x⦁ p ∧ x =⋏↾ A)
=TEX

\ignore{
=SML
val ι⋏↾_def = get_spec ⌜$ι⋏↾⌝;

set_goal([], ⌜Ξ p ⇒ A =⋏↾ ι⋏↾ x⦁ p ∧ x =⋏↾ A⌝);
a (asm_rewrite_tac[Ξ_def] THEN strip_tac);
a (strip_asm_tac (list_∀_elim [⌜λx⦁ p ∧ x =⋏↾ A⌝, ⌜A actual_world⌝, ⌜actual_world⌝] ι⋏↾_def));
(* *** Goal "1" *** *)
a (POP_ASM_T (strip_asm_tac o (rewrite_rule[])));
a (spec_nth_asm_tac 1 ⌜A⌝);
(* *** Goal "2" *** *)
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule[])));
(* *** Goal "3" *** *)
a (asm_rewrite_tac[]);
val QT35c = save_pop_thm "QT35c";
=TEX
}%ignore

He concludes that a quantified modal logic must involve some kind of essentialism.
I think the present treatment of modal logic, and various previous quantified modal logics subsequent to Quine's essay show that this conclusion is mistaken.

Here are two results in our system which at least superficially correspond to conditions which Quine seems to think entail such an essentialism:

=GFT
⦏QT36⦎ =
	⊢ Ξ ⦈ (x =⋏↾ x)

⦏QT37a⦎ = p = (λ w⦁ w = actual_world)
	⊢ Ξ p ∧ (x =⋏↾ x) ⇔ (x =⋏↾ x)

⦏QT37b⦎ = ¬ w1 = actual_world, p = (λ w⦁ w = actual_world)
	⊢ Ξ ¬ ⦈ p ∧ x =⋏↾ x
=TEX

The first theorem asserts the necessity of the reflexivity of identity.
The second asserts a contingent identity between that principle and its conjunction with some arbitrary contingent truth.
In the the theorem, we assume that there is at least one non-actual possible world, in order to show that the conjunction with a contingent truth does not yield a necessary truth.

This does not however betray an essentialist element in our formal model.

\ignore{
=SML
set_goal([], ⌜Ξ ⦈ (x =⋏↾ x)⌝);
a (rewrite_tac[Ξ_def]);
val QT36 = save_pop_thm "QT36";

set_goal([⌜p = λw:W⦁ w = actual_world⌝], ⌜Ξ p ∧ (x =⋏↾ x) ⇔ (x =⋏↾ x)⌝);
a (asm_rewrite_tac[Ξ_def]);
val QT37a = save_pop_thm "QT37a";

set_goal([⌜¬ w1 = actual_world⌝, ⌜p = λw:W⦁ w = actual_world⌝], ⌜Ξ ¬ ⦈ p ∧ (x =⋏↾ x)⌝);
a (asm_rewrite_tac[Ξ_def] THEN strip_tac);
a (∃_tac ⌜w1⌝ THEN asm_rewrite_tac[]);
val QT37b = save_pop_thm "QT37b";
=TEX
}%ignore

=GFT
⦏QT28a⦎ = ⊢ ∀ x y⦁ x = y ⇒ (Ξ ⦈ (x ⋏↿ =⋏↾ y ⋏↿))
⦏QT28b⦎ = ⊢ ∀ x y⦁ x = y ⇒ (Ξ ⦈ (x =⋏↾ y))
=TEX

\ignore{
=SML
set_goal([], ⌜∀x y:'a⦁ x = y ⇒ Ξ ⦈ (x ⋏↿ =⋏↾ y ⋏↿)⌝);
a (REPEAT strip_tac THEN asm_rewrite_tac[Eq⋏↾_def, l_defs, Ξ_def]);
val QT28a = save_pop_thm "QT28a";

set_goal([], ⌜∀x y⦁ x = y ⇒ Ξ ⦈ (x =⋏↾ y)⌝);
a (REPEAT strip_tac THEN asm_rewrite_tac[Eq⋏↾_def, l_defs, Ξ_def]);
val QT28b = save_pop_thm "QT28b";


=TEX
}%ignore

\subsection{Attributes}

\section{Rigidity}

\ignore{
=SML
open_theory "t045";
set_merge_pcs ["rbjmisc", "'t045"];
=TEX
}%ignore

To allow the ontology to be contingent, we must make provision for a possible world to determine an ontology or domain of discourse.

=SML
val CTG_def = new_type_defn(["CTG"], "CTG", ["'a"],
	tac_proof (([], ⌜($∃:('a→BOOL)→BOOL)(λx⦁ (λy⦁T)x)⌝), conv_tac (rewrite_conv[])));
=TEX

=GFT
⦏CTG_def⦎ = ⊢ ∃ f⦁ TypeDefn (λ y⦁ T) f
=TEX

ⓈHOLCONST
│ ⦏Domain⦎: 'a CTG SET FLEX
├──────
│ T
■


\ignore{
=SML
force_new_theory "t045k";
force_new_pc ⦏"'t045k"⦎;
merge_pcs ["'prove_∃_⇒_conv", "'savedthm_cs_∃_proof"] "'t045k";
set_merge_pcs ["rbjmisc", "'t045", "'t045k"];
=TEX
}%ignore

The notion of rigid designator was introduced by Kripke.
A designator is (weakly) rigid if it designates the same entity in any possibly world in which that entity exists.
A designator is strongly rigid if the entity always exists.
A designator is contingent if it is not rigid.

ⓈHOLCONST
│ ⦏Rigid⦎:'a FLEX → PROP
├──────
│ ∀x⦁ Rigid x = λw⦁ ∀v u⦁ x v = x u 
■

=GFT
⦏rigid_subst_thm⦎ = ⊢ Ξ (∀ x⦁ ∀ y⦁ Rigid x ∧ (x = y) ⋏↿ ⇒ ⦈ (P x ⇔ P y))
⦏rigid_subst_thm2⦎ = ⊢ (∃ w⦁ ¬ w = actual_world)
       ⇒ ¬ (∀ P⦁ Ξ (∀ x⦁ ∀ y⦁ Rigid x ∧ x =⋏↾ y ⇒ ⦈ (P x ⇔ P y)))
=TEX

\ignore{
=SML
val Rigid_def = get_spec ⌜Rigid⌝;
set_goal([], ⌜Ξ (∀⋏↾ x y⦁ Rigid x ∧ (x = y)⋏↿ ⇒ ⦈ (P x ⇔ P y))⌝);
a (rewrite_tac [Ξ_def, Rigid_def, get_spec ⌜$⋏↿⌝] THEN REPEAT_N 3 strip_tac
	THEN asm_rewrite_tac[]);
val rigid_subst_thm = save_pop_thm "rigid_subst_thm";

set_goal([], ⌜(∃w:W⦁ ¬ w = actual_world) ⇒ ¬ ∀P⦁ Ξ (∀x y:ℕ FLEX⦁ Rigid x ∧ (x =⋏↾ y) ⇒ ⦈ (P x ⇔ P y))⌝);
a (rewrite_tac [Ξ_def, Rigid_def] THEN REPEAT strip_tac);
a (∃_tac ⌜λx: ℕ FLEX⦁ λw⦁ x w > 2⌝ THEN rewrite_tac[] THEN strip_tac);
a (∃_tac ⌜λv:W⦁ 3⌝ THEN rewrite_tac[] THEN strip_tac);
a (∃_tac ⌜λv:W⦁ if v = actual_world then 3 else 1⌝ THEN PC_T1 "lin_arith" rewrite_tac[] THEN strip_tac);
a (∃_tac ⌜w⌝ THEN PC_T1 "lin_arith" asm_rewrite_tac[] THEN strip_tac);
val rigid_subst_thm2 = save_pop_thm "rigid_subst_thm2";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏∀⋎c⦎: (('a CTG + ONE)FLEX → PROP) → PROP
├──────
│ ∀p⦁ ∀⋎c p = λw⦁ ∀fc⦁ IsR (fc w) ∨ OutL (fc w) ∈ Domain w ⇒ p fc w
■

=IGN
declare_alias("∀", ⌜∀⋎c⌝);
=SML
declare_binder "∀⋎c";
=TEX

We can now give an improved formal account of rigidity.


ⓈHOLCONST
│ ⦏Rigid⋎c⦎: ('a CTG + ONE)FLEX → PROP
├──────
│ ∀x⦁	Rigid⋎c x = λw⦁ ∃y⦁ ∀v⦁
│		if y ∈ Domain v then x v = InL y else x v = InR One
■

\ignore{
=SML
val Rigid⋎c_def = get_spec ⌜Rigid⋎c⌝;

set_goal([], ⌜Ξ (∀⋏↾ x y⦁ Rigid⋎c x ∧ (x = y)⋏↿ ⇒ ⦈ (P x ⇔ P y))⌝);
a (rewrite_tac [Ξ_def, Rigid⋎c_def, get_spec ⌜$⋏↿⌝] THEN REPEAT_N 3 strip_tac
	THEN asm_rewrite_tac[]);
val Rigid⋎c_subst_thm = save_pop_thm "Rigid⋎c_subst_thm";

=IGN
set_goal([], ⌜(∃w:W⦁ ¬ w = actual_world) ⇒ ¬ ∀P⦁ Ξ (∀x y:(ℕ CTG + ONE) FLEX⦁ Rigid⋎c x ∧ (x =⋏↾ y) ⇒ ⦈ (P x ⇔ P y))⌝);
a (rewrite_tac [Ξ_def, Rigid⋎c_def] THEN REPEAT strip_tac);
a (∃_tac ⌜λx: ℕ FLEX⦁ λw⦁ x w > 2⌝ THEN rewrite_tac[] THEN strip_tac);
a (∃_tac ⌜λv:W⦁ 3⌝ THEN rewrite_tac[] THEN strip_tac);
a (∃_tac ⌜λv:W⦁ if v = actual_world then 3 else 1⌝ THEN PC_T1 "lin_arith" rewrite_tac[] THEN strip_tac);
a (∃_tac ⌜w⌝ THEN PC_T1 "lin_arith" asm_rewrite_tac[] THEN strip_tac);
val Rigid_subst_thm2 = save_pop_thm "Rigid_subst_thm2";
=TEX
}%ignore


ⓈHOLCONST
│ ⦏StronglyRigid⋎c⦎: ('a CTG + ONE)FLEX → PROP
├──────
│ ∀x⦁	StronglyRigid⋎c x = λw⦁ ∃y⦁ ∀v⦁ x v = InL y
■

=GFT
=TEX

\ignore{
=SML
val StronglyRigid⋎c_def = get_spec ⌜StronglyRigid⋎c⌝;
set_goal([], ⌜Ξ (∀⋏↾ x y⦁ StronglyRigid⋎c x ∧ (x = y)⋏↿ ⇒ ⦈ (P x ⇔ P y))⌝);
a (rewrite_tac [Ξ_def, StronglyRigid⋎c_def, get_spec ⌜$⋏↿⌝] THEN REPEAT_N 3 strip_tac
	THEN asm_rewrite_tac[]);
val StronglyRigid⋎c_subst_thm = save_pop_thm "StronglyRigid⋎c_subst_thm";

=IGN
set_goal([], ⌜(∃w:W⦁ ¬ w = actual_world) ⇒ ¬ ∀P⦁ Ξ (∀x y:(ℕ CTG+ONE) FLEX⦁ StronglyRigid⋎c x ∧ (x =⋏↾ y) ⇒ ⦈ (P x ⇔ P y))⌝);
a (rewrite_tac [Ξ_def, StronglyRigid⋎c_def] THEN REPEAT strip_tac);
a (∃_tac ⌜λx:(ℕ CTG+ONE) FLEX⦁ λw⦁ x w > 2⌝ THEN rewrite_tac[] THEN strip_tac);
a (∃_tac ⌜λv:W⦁ 3⌝ THEN rewrite_tac[] THEN strip_tac);
a (∃_tac ⌜λv:W⦁ if v = actual_world then 3 else 1⌝ THEN PC_T1 "lin_arith" rewrite_tac[] THEN strip_tac);
a (∃_tac ⌜w⌝ THEN PC_T1 "lin_arith" asm_rewrite_tac[] THEN strip_tac);
val rigid_subst_thm2 = save_pop_thm "rigid_subst_thm2";
=TEX
}%ignore



\section{Possibilism and Actualism}

This section is based in Timothy Williamson's discussion \cite{williamson2010}, in which because of confusion which he notes in the usage of the terms `possibilism' and `actualism' he adopts a new nomenclature to which a more definite meaning can be attached, viz. `necessitism' and `contingentism'.

So far as I understand it at this early stage, his addresses the possibility that the difference between the positions might be in some sense verbal by considering interpretations of the language which allow the point of view of one to be expressed in the language of the other, but finds an asymmetry suggesting that the language of the contingentist is unable to fully interpret the language of the necessist.

In the first instance I embed the modal system which he presents in his appendix.
A new theory \emph{t045w} is created for this purpose.

We proceed in a similar manner, which is to loosely define a single interpretation of the language and to define the operators of the language in terms of that loosely defined interpretation so that the theorems provable are just those which are true in any interpretation satisfying the loose definition, and hence those which are valid under the intended semantics.

\ignore{
=SML
open_theory "t045";
force_new_theory "t045w";
force_new_pc ⦏"'t045w"⦎;
merge_pcs ["'prove_∃_⇒_conv", "'savedthm_cs_∃_proof"] "'t045w";
set_merge_pcs ["rbjmisc", "'t045", "'t045w"];
=TEX
}%ignore

=GFT
⦏NNE_thm⦎ = ⊢ Ξ ⦈ (∀ x⦁ ⦈ (∃ y⦁ x =⋏↾ y))
=TEX

\ignore{
=SML
set_goal([], ⌜Ξ ⦈ ∀x⦁ ⦈ ∃y⦁ x =⋏↾ y⌝);
a (rewrite_tac [Ξ_def] THEN prove_tac[]);
val NNE_thm = save_pop_thm "NNE_thm";
=TEX
}%ignore

A contemporary debate appears to have risen from some of the technical choices involved in the construction of quantified modal logics.

The specific issue which gives rise to (or at least, connects with) the debate is the question whether an interpretation of a quantified modal logic should have a single domain of discourse or separate domains for each possible world.

The simplest arrangement is that existence does not vary from one possible world to the next, though the satisfiability of predicates may.
The more complex arrangement is that existence is contingent.

In our general setting we can speak of and quantify over specific or modal values, the specific values being like rigid designators in referring to the same individual in every possible world, the modal values on the other hand (like descriptions) might possibly refer to different values in different worlds.

We need a new type of proposition, indexed by a possible world and a stack of possible worlds:

=SML
declare_type_abbrev("PROPW", [], ⓣW × W LIST → BOOL⌝);
=TEX

\paragraph{Equality}


ⓈHOLCONST
│ ⦏=⋎w⦎: 'a CTG → 'a CTG → PROPW
├──────
│ ∀x y⦁ =⋎w x y = λ(w, s)⦁ x = y ∧ x ∈ Domain w
■

=SML
declare_alias("=", ⌜=⋎w⌝);
declare_infix(200, "=⋎w");
=TEX

\paragraph{Propositional Operators}

The previous definitions for lifted BOOLean operators will suffice in this context.

\paragraph{Quantification}

We need to be able to quantify over the contingents.
For the Williams logic this must be a more rigidly first order quantification (i.e. over individuals not over modal intensions).

ⓈHOLCONST
│ ⦏∃⋎w⦎: ('a CTG → PROPW) → PROPW
├──────
│ ∀p⦁ ∃⋎w p = λ(w, s)⦁ ∃fc:'a CTG⦁ fc ∈ Domain w ∧ p fc (w, s)
■

ⓈHOLCONST
│ ⦏∀⋎w⦎: ('a CTG → PROPW) → PROPW
├──────
│ ∀p⦁ ∀⋎w p = λ(w, s)⦁ ∀fc:'a CTG⦁ fc ∈ Domain w ⇒ p fc (w, s)
■

=GFT
⦏∃⋎w∀⋎w_thm⦎ =
   ⊢ ∀ p w s⦁
	∃⋎w p (w, s) ⇔ (∃ fc⦁ fc ∈ Domain w ∧ p fc (w, s)
     ∧ (∀⋎w p (w, s) ⇔ (∀ fc⦁ fc ∈ Domain w ⇒ p fc (w, s))))
=TEX

\ignore{
=SML
val ∃⋎w_def = get_spec ⌜∃⋎w⌝;
val ∀⋎w_def = get_spec ⌜∀⋎w⌝;

set_goal([], ⌜
	∀p w s⦁	∃⋎w p (w,s) = ∃fc:'a CTG⦁ fc ∈ Domain w ∧ p fc (w, s)
∧		∀⋎w p (w,s) = ∀fc:'a CTG⦁ fc ∈ Domain w ⇒ p fc (w, s)
⌝);
a (rewrite_tac [∃⋎w_def, ∀⋎w_def]);
val ∃⋎w∀⋎w_thm = save_pop_thm "∃⋎w∀⋎w_thm";
=TEX
}%ignore

=SML
declare_binder("∃⋎w");
declare_binder("∀⋎w");
=TEX


ⓈHOLCONST
│ ⦏⦇⋎w⦎: PROPW → PROPW
├──────
│ ∀p⦁ ⦇⋎w p = λ(w, s)⦁ ∃w2⦁ p (w2, s)
■

ⓈHOLCONST
│ ⦏⦈⋎w⦎: PROPW → PROPW
├──────
│ ∀p⦁ ⦈⋎w p = λ(w, s)⦁ ∀w2⦁ p (w2, s)
■

=SML
declare_alias("⦇", ⌜⦇⋎w⌝);
declare_alias("⦈", ⌜⦈⋎w⌝);
=TEX

=GFT
⦏⦇⋎w⦈⋎w_thm⦎ =
   ⊢ ∀ p w s⦁
	 ⦇ p (w, s) ⇔ (∃ w2⦁ p (w2, s)
∧	(⦈ p (w, s) ⇔ (∀ w2⦁ p (w2, s))))
=TEX

\ignore{
=SML
val ⦇⋎w_def = get_spec ⌜⦇⋎w⌝;
val ⦈⋎w_def = get_spec ⌜⦈⋎w⌝;

set_goal([], ⌜
	∀p w s⦁	⦇⋎w p (w, s) = (∃w2⦁ p (w2, s))
	 ∧	⦈⋎w p (w, s) = (∀w2⦁ p (w2, s))
⌝);
a (rewrite_tac [⦇⋎w_def, ⦈⋎w_def]);
val ⦇⋎w⦈⋎w_thm = save_pop_thm "⦇⋎w⦈⋎w_thm";
=TEX
}%ignore


ⓈHOLCONST
│ ⦏⋏∧⦎: PROPW → PROPW
├──────
│ ∀p⦁ ⋏∧ p = λ(w, s)⦁ p (w, Cons w s)
■

ⓈHOLCONST
│ ⦏⋎∨⦎: PROPW → PROPW
├──────
│ ∀p w w2 s⦁ ⋎∨ p (w, []) = p (w, [])
│  ∧ ⋎∨ p (w, Cons w2 s) = p (w2, s)
■

=GFT
⦏⋏∧_thm⦎ = ⊢ ∀ p w s⦁ ⋏∧ p (w, s) ⇔ p (w, Cons w s)
=TEX

\ignore{
=SML
val ⋏∧_def = get_spec ⌜⋏∧⌝;
val ⋎∨_def = get_spec ⌜ ⋎∨⌝;

set_goal([], ⌜∀p w s⦁ ⋏∧ p (w, s) = p (w, Cons w s)⌝);
a (rewrite_tac[⋏∧_def]);
val ⋏∧_thm = save_pop_thm "⋏∧_thm";

add_pc_thms "'t045w" [∃⋎w∀⋎w_thm, ⦇⋎w⦈⋎w_thm, ⋏∧_thm, ⋎∨_def];
set_merge_pcs ["rbjmisc", "'t045", "'t045w"];
=TEX
}%ignore


=SML
declare_infix (5, "Ξ⋎w");
=TEX

ⓈHOLCONST
│ $⦏Ξ⋎w⦎: PROPW LIST → PROPW → BOOL
├──────
│ ∀lp p⦁ (lp Ξ⋎w p) ⇔ ∀(w, s)⦁ (∀x⦁ x ∈⋎L lp ⇒ x (w,s)) ⇒ p (w,s)
■

=IGN
declare_alias("Ξ", ⌜Ξ⋎w⌝);
declare_infix (5, "Ξ");
=TEX


\paragraph{Propositional Logic}

\ 

=GFT
⦏Ξ⋎w_mp_thm⦎ =	⊢ [A; A ⇒ B] Ξ⋎w B
⦏Ξ⋎w_ax1_thm⦎ =	⊢ [] Ξ⋎w p ⇒ q ⇒ p
⦏Ξ⋎w_ax2_thm⦎ =	⊢ [] Ξ⋎w (p ⇒ q ⇒ r) ⇒ (p ⇒ q) ⇒ p ⇒ r
⦏Ξ⋎w_ax3_thm⦎ =	⊢ [] Ξ⋎w (¬ p ⇒ ¬ q) ⇒ q ⇒ p
=TEX

\ignore{
=SML
set_goal([], ⌜[A; A ⇒ B] Ξ⋎w B⌝);
a (prove_tac [get_spec ⌜$Ξ⋎w⌝]);
a (spec_nth_asm_tac 1 ⌜A⌝);
a (spec_nth_asm_tac 2 ⌜A ⇒ B⌝);
val Ξ⋎w_mp_thm = save_pop_thm "Ξ⋎w_mp_thm";

set_goal([], ⌜[] Ξ⋎w p ⇒ (q ⇒ p)⌝);
a (rewrite_tac [get_spec ⌜$Ξ⋎w⌝] THEN contr_tac);
val Ξ⋎w_ax1_thm = save_pop_thm "Ξ⋎w_ax1_thm";

set_goal([], ⌜[] Ξ⋎w (p ⇒ q ⇒ r) ⇒ ((p ⇒ q) ⇒ (p ⇒ r))⌝);
a (rewrite_tac [get_spec ⌜$Ξ⋎w⌝] THEN contr_tac);
val Ξ⋎w_ax2_thm = save_pop_thm "Ξ⋎w_ax2_thm";

set_goal([], ⌜[] Ξ⋎w (¬ p ⇒ ¬ q) ⇒ (q ⇒ p)⌝);
a (rewrite_tac [get_spec ⌜$Ξ⋎w⌝] THEN contr_tac);
val Ξ⋎w_ax3_thm = save_pop_thm "Ξ⋎w_ax3_thm";

=IGN
set_goal([], ⌜[] Ξ⋎w T⋏↿⌝);
a (rewrite_tac [get_spec ⌜$Ξ⋎w⌝] THEN REPEAT strip_tac);
val Ξ⋎w_T_thm = save_pop_thm "Ξ⋎w_T_thm";

set_goal([], ⌜[] Ξ⋎w A ∧ B ⇒ A⌝);
a (rewrite_tac [get_spec ⌜$Ξ⋎w⌝] THEN contr_tac);
val Ξ⋎w_ABA_thm = save_pop_thm "Ξ⋎w_ABA_thm";
=TEX
}%ignore


\paragraph{S5}

\ 

=GFT
⦏distrib⋎w_thm⦎ =	⊢ [] Ξ⋎w ⦈⋎w (A ⇒ B) ⇒ ⦈⋎w A ⇒ ⦈⋎w B
⦏D⋎w_thm⦎ =	⊢ [] Ξ⋎w ⦈⋎w A ⇒ ⦇⋎w A
⦏M⋎w_thm⦎ =	⊢ [] Ξ⋎w ⦈⋎w A ⇒ A
⦏A4⋎w_thm⦎ =	⊢ [] Ξ⋎w ⦈⋎w A ⇒ ⦈⋎w (⦈⋎w A)
⦏B⋎w_thm⦎ =	⊢ [] Ξ⋎w A ⇒ ⦈⋎w (⦇⋎w A)
=TEX

\ignore{
=SML
set_goal([], ⌜[] Ξ⋎w ⦈⋎w(A ⇒ B) ⇒ ⦈⋎w A ⇒ ⦈⋎w B⌝);
a (prove_tac[get_spec ⌜$Ξ⋎w⌝] THEN asm_rewrite_tac[]
	THEN prove_tac[]);
val distrib⋎w_thm = save_pop_thm "distrib⋎w_thm2";

set_goal([], ⌜[] Ξ⋎w (⦈⋎w A) ⇒ ⦇⋎w A⌝);
a (rewrite_tac [get_spec ⌜$Ξ⋎w⌝] THEN prove_tac[]);
val D⋎w_thm = save_pop_thm "D⋎w_thm";

set_goal([], ⌜[] Ξ⋎w (⦈⋎w A) ⇒ A⌝);
a (rewrite_tac [get_spec ⌜$Ξ⋎w⌝] THEN prove_tac[]);
val M⋎w_thm = save_pop_thm "M⋎w_thm";

set_goal([], ⌜[] Ξ⋎w (⦈⋎w A) ⇒ (⦈⋎w (⦈⋎w A))⌝);
a (rewrite_tac [get_spec ⌜$Ξ⋎w⌝] THEN prove_tac[]);
val A4⋎w_thm = save_pop_thm "A4⋎w_thm";

set_goal([], ⌜[] Ξ⋎w A ⇒ (⦈⋎w (⦇⋎w A))⌝);
a (rewrite_tac [get_spec ⌜$Ξ⋎w⌝] THEN prove_tac[]);
val B⋎w_thm = save_pop_thm "B⋎w_thm";

set_goal([], ⌜[] Ξ⋎w (⦇⋎w A) ⇒ (⦈⋎w (⦇⋎w A))⌝);
a (rewrite_tac [get_spec ⌜$Ξ⋎w⌝] THEN prove_tac[]);
val A5⋎w_thm = save_pop_thm "A5⋎w_thm";

set_goal([], ⌜[] Ξ⋎w ⦈⋎w((⦈⋎w A) ⇒ A)⌝);
a (rewrite_tac [get_spec ⌜$Ξ⋎w⌝] THEN prove_tac[]);
val ⦈M⋎w_thm = save_pop_thm "⦈M⋎w_thm";

set_goal([], ⌜[] Ξ⋎w (⦈⋎w (⦈⋎w A)) ⇒ (⦈⋎w A)⌝);
a (rewrite_tac [get_spec ⌜$Ξ⋎w⌝] THEN prove_tac[]);
val C4⋎w_thm = save_pop_thm "C4⋎w_thm";

set_goal([], ⌜[] Ξ⋎w (⦇⋎w (⦈⋎w A)) ⇒ (⦈⋎w (⦇⋎w A))⌝);
a (rewrite_tac [get_spec ⌜$Ξ⋎w⌝] THEN prove_tac[]);
val C⋎w_thm = save_pop_thm "C⋎w_thm";
=TEX
}%ignore

\ignore{
=SML
open_theory "t045";
commit_pc "'t045";
force_new_pc "⦏t045⦎";
merge_pcs ["rbjmisc", "'t045"] "t045";
commit_pc "t045";
=TEX
}%ignore

\ignore{
=SML
open_theory "t045q";
commit_pc "'t045q";
force_new_pc "⦏t045q⦎";
merge_pcs ["t045", "'t045q"] "t045q";
commit_pc "t045q";

open_theory "t045k";
commit_pc "'t045k";
force_new_pc "⦏t045k⦎";
merge_pcs ["t045", "'t045k"] "t045k";
commit_pc "t045k";

open_theory "t045w";
commit_pc "'t045w";
force_new_pc "⦏t045w⦎";
merge_pcs ["rbjmisc", "'t045w"] "t045w";
commit_pc "t045w";
set_flag("pp_use_alias", true);
=TEX
}%ignore

\section{Naming and Necessity}

This section contains notes on some ideas for an analysis of Kripke's \emph{Naming and Necessity} \cite{kripkeNN}.
It may not ultimately belong in this document.

It is easy to show that the concepts of \emph{analyticity}, \emph{necessity} and \emph{a priority} as used in this document are not all the same as those used by some other philosophers.
This is as one would expect.
The other conceptions of interest here are those of Carnap (primarily) and possibly also Frege.

The main difference of interest here is in the concept of analyticity.

Now the analysis I am thinking of here, to be done formally if possible, is to define the two sets of conceptions formally so that the relationship between the two can be established, and in particular so that Kripke's metaphysical conclusions can be expressed in the language of Carnap.

Ultimately the question at stake is the status of Kripkean metaphysics.
Kripke talks of this in essentialist terms, and of necessity \emph{de re} rather than \emph{de dicto}, but the question still remains whether the conclusions are objective necessary claims about reality, or whether they are \emph{verbal}.

A test of this is whether they survive translation into a different vocabulary.

A problem here is making this into something substantial, for it is two easy to guarantee no necessity \emph{de re} in Carnap's conception, for the connection between necessity and analyticity is transparent.

