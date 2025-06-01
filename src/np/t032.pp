=TEX
\def\rbjidtADCdoc{$$Id: t032.doc,v 1.4 2012/02/14 20:44:22 rbj Exp $$}

This document has not really been started yet.

Here are some notes on what it might contain.

For the purposes of this analytic history the single most important concern is what Leibniz contributed to out understanding of the concept of logical truth.
For this we consider primarily the most fundamental parts of his metaphysics, which we do partly through the perspective of Bertrand Russell \cite{russellPL}, whose own philosophy of Logical Atomism was influenced by Leibniz and will be considered later.

Leibniz contributed also to our ideas about the applications of logic, through his ``universal characteristic'' and ``calculus ratiocinator''.
Some kind of analysis of his ideas in this area would be nice.

\section{Leibniz On Identity}

This just shows the triviality of the identity of indiscernibles in our logical context, and raises the question, what more substantive point is Leibniz making and has it any substance?

It is clear that Leibniz's intention was not to forumlate such trivial principles as are found here.
He intends that distinct individuals always differ in some substantive way (using that term informally).
The real problem here is whether this can be captured formally in HOL, and this section at present does not make offer any elightenment on that topic.

=SML
open_theory "misc2";
force_new_theory "leibniz01";
set_pc "misc2";
=TEX

In higher order logic an identity of indiscernables (though probably not Leibniz's) is a trivial principle.

Its formulation is:

=GFT
	∀x y⦁ (∀P⦁ P(x) ⇔ P(y)) ⇒ x = y
=TEX

Here is a long-winded transcript of a ProofPower proof session:

=SML
set_goal([], ⌜∀x y⦁ (∀P⦁ P(x) ⇔ P(y)) ⇒ x = y⌝);
=GFT ProofPower output
(* *** Goal "" *** *)

(* ?⊢ *)  ⌜∀ x y⦁ (∀ P⦁ P x ⇔ P y) ⇒ x = y⌝
=TEX

Strip the goal.

=SML
a (REPEAT strip_tac);
=GFT ProofPower output
(* *** Goal "" *** *)

(*  1 *)  ⌜∀ P⦁ P x ⇔ P y⌝

(* ?⊢ *)  ⌜x = y⌝
=TEX

Instantiate the assumption using the predicate
=INLINEFT
⌜$= y⌝
=TEX
.
\footnote{This is the predicate ``equal to y'', or $⌜λx. y = x⌝$}:
=SML
a (spec_asm_tac ⌜∀ P⦁ P x ⇔ P y⌝ ⌜$= y⌝);
=GFT ProofPower output
(* *** Goal "" *** *)

(*  2 *)  ⌜∀ P⦁ P x ⇔ P y⌝
(*  1 *)  ⌜y = x⌝

(* ?⊢ *)  ⌜x = y⌝
=TEX

The instantiation yields:
=GFT
	⌜y = x ⇔ y = y⌝
	⇔ ⌜(y = x ⇒ y = y) ∧ (y = y ⇒ y = x)⌝
	⇔ ⌜(¬y = x ∨ y = y) ∧ (y = x ∨ ¬y = y)⌝
	⇔ ⌜(¬y = x ∨ T) ∧ (y = x ∨ F)⌝
	⇔ ⌜(y = x)⌝
=TEX
of which the last is the new assumption shown above.

Rewrite the conclusion with the assumptions (giving $⌜x = x⌝$ which is automatically discharged).

=SML
a (asm_rewrite_tac[]);
=GFT ProofPower output
Tactic produced 0 subgoals:
Current and main goal achieved
=TEX

Save the theorem.
=SML
val ⦏leibniz_identity⦎ = save_pop_thm "leibniz_identity";
=GFT ProofPower output
Now 0 goals on the main goal stack
val leibniz_identity = ⊢ ∀ x y⦁ (∀ P⦁ P x ⇔ P y) ⇒ x = y : THM
=TEX

So, in this context, that indiscernibles are identical is an elementary consequence of the fact that for every entity `e' there is a predicate `equal to e' which is satisfied only by e.

Leibniz intended by his principle something more substantial, which is harder to capture.

\section{The Calculus Ratiocinator}

This section is primarily based on what is said about Leibniz in the book written by Lukasievicz on Aristotles syllogistic, I have not checked this out against Leibniz's own writings, though it seems plausible from what I have read.

Leibniz's calculus is an arithmetisation of Aristotle's syllogistic.
That such an arithmetisation will have the power which Leibniz attributes to it is certainly not the case, but my concern here is just to build a model which is similar to the arithmetic interpretation and allows us to check the extent to which it properly captures the relevant parts of Aristotle's logic.
Since useful groundwork on this is done in my formal treatment of Aristotle\cite{rbjt028}, I will make use of some of that material by making this document logically dependent upon it, and making the theory which is here developed a child of one of the my models of Aristotle.


\subsection{Leibniz's Interpretation of Aristotle's Syllogistic}\label{LIAS}

The rationale for Leibniz's interpretation of propositions depends upon his conceptual atomism.
This is the idea that concepts can be classified as either \emph{simple} or \emph{complex} and that complex concepts are defined ultimately (though possibly indirectly) in terms of simple concepts, by limited means.
The limited means consist of negation of simple concepts and conjunction.
It is further assumed that simple concepts are logically independent of each other, and that none of them is always true or always false (possibly this should be read necessarily true or necessarily false).

Given this simple idea of what concepts are, conceptual inclusion is decidable provided that we know which concepts are simple and we know the definitions of all the complex concepts.
Conceptual inclusion corresponds to the A form of proposition, the I form is also decidable, and the other two are defined in terms of those two.

Leibniz arithmetises this by assuming that each simple concept is given a unique prime number, and that complex concepts are then represented by two numbers.
The first of these two numbers is the product of the primes of the simple concepts which occur positively in the definition of the complex concept (when this has been expanded out so that it no longer mentions any complex concepts and therefore consists of a conjunction of simple concepts or their negations).
The second number is the product of the primes which code the simple concepts whose negations appear in the expanded definition.

Arithetisation is not essential, any equivalent way of coding up the information about which simple concepts or negations of simple concepts appear in the definition of a complex concept will do, and reasoning will be simpler if the problem of obtaining prime factorisations is sidestepped.
We need not know how simple concepts are represented, and we can represent a conjunction as a list of conjuncts.

There is a small awkwardness if we want equality of concepts to be the same thing as equality of the representation and hence obtain:

=GFT
	A a B and B a A entails A = B
=TEX

If we just used two pairs of lists of simple concepts then the same concept would have multiple representatives, and pairs of lists which overlapped would not represent concepts at all.
We could use a pair of sets of simple concepts, but then we have the possibility of infinite sets and we still might have overlap.
A function from simple concepts into the type BOOL+ONE where the BOOL component represents negative or positive presence of the simple concept gets the identity correct but might allow infinite numbers of simple concepts.
This is a possible point of divergence from Leibniz, but I'm going to try this one.


=SML
open_theory "aristotle";
force_new_theory "leibniz02";
=TEX

\ignore{
=SML
force_new_pc ⦏"'leibniz02"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'leibniz02";
set_merge_pcs ["misc2", "'leibniz02"];
=TEX
}%ignore

\subsubsection{Semantics}

We will allow that any type be used as the simple concepts, so that all the rules we can establish will be correct in the finite case and in the infinite case.

=SML
declare_type_abbrev("TermL", [], ⓣ'a → TTV⌝);
=TEX

$TTV$ is a type with just three elements which may be thought of as truth values.
Their names are $pTrue$, $pFalse$ and $pU$.
I will use $pTrue$ to make a positively occurring simple concept, $pFalse$ to mark a negated simple concept.
$pU$ marks a simple concept which does not occur in the relevant complex concept.


The predicate $Some$ will be true iff a TTV does not have the value $pU$.

ⓈHOLCONST
│ ⦏Some⦎ : TTV → BOOL
├──────
│ ∀x⦁ Some x = ¬ x = pU
■

The predicate $IsPos$ will be true iff a BOOL+ONE has the value $pTrue$.

ⓈHOLCONST
│ ⦏IsPos⦎ : TTV → BOOL
├──────
│ ∀x⦁ IsPos x ⇔ x = pTrue
■


\ignore{
=SML
val Some_def = get_spec ⌜Some⌝;
val IsPos_def = get_spec ⌜IsPos⌝;
=TEX
}%ignore

\subsubsection{Predication}

``o'' is already in use for functional composition, so we will use ``u'' instead and then use an alias to permit us to write this as ``o'' (type inference will usually resolve any ambiguity).

To render these in HOL we first declare the relevant letters as infix operators:

They predication operators are defined as follows:

=SML
declare_infix (300, "a");
declare_infix (300, "e");
declare_infix (300, "i");
declare_infix (300, "u");
=TEX

ⓈHOLCONST
│ $⦏a⦎ : TermL → TermL → BOOL
├──────
│ ∀A B⦁ A a B ⇔ ∀x⦁ (B x = pTrue ⇒ A x = pTrue) ∧ (B x = pFalse ⇒ A x = pFalse)
■

ⓈHOLCONST
│ $⦏i⦎ : TermL → TermL → BOOL
├──────
│ ∀A B⦁ A i B ⇔ ∀x⦁ A x = B x ⇒ A x = pU
■

ⓈHOLCONST
│ $⦏e⦎ : TermL → TermL → BOOL
├──────
│ ∀A B⦁ A e B ⇔ ¬ A i B
■

ⓈHOLCONST
│ $⦏u⦎ : TermL → TermL → BOOL
├──────
│ ∀A B⦁ A u B ⇔ ¬ A a B
■

=SML
declare_alias("o", ⌜$u⌝);
=TEX

Note that as defined above these come in complementary pairs, $a$ being the negation of $o$ and $e$ of $i$.
If we had negation we could manage with just two predication operators.

\subsubsection{The Laws of Immediate Inference}

Though in the source of this kind of ``literate script'' are to be found the scripts for generating and checking the proofs of all the theorems presente, it will not be my practice to expose these scripts in the printed version of the document.
These scripts are not usually intelligible other than in that intimate man-machine dialogue which they mediate, and sufficient knowledge for most purposes of the structure of the proof will be found in the detailed lemmas proven (since the level of proof automation is modest).

However, I will begin by exposing some of the scripts used for obtaining proofs of syllogisms in this model, to give the reader an impession of the level of complexity and kind of obscurity involved in this kind of formal work,
I will not attempt sufficient explanation to make these scripts intelligible, they are best understood in the interactive environment, all the scripts are available for readers who want to run them.

Most readers are expected to skip over the gory details, the philosophical points at stake do not depend on the details of the proofs.

Before addressing the laws of immediate inference
\footnote{in which I followed Strawson \cite{strawson52}, though I can now cite \href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o3102c.htm}{Aristotle, Prior Analytic, Book 1, Part 2.}
\cite{aristotleL325}}
I devise a tactic for automating simple proofs in this domain.

The following elementary tactic expands the goal by applying the definitions of the operators and then invokes a general tactic for the predicate calculus.
A rule is also defined using that tactic for direct rather than interactive proof.

=SML
val ⦏syll_tacL⦎ = REPEAT (POP_ASM_T ante_tac)
	THEN rewrite_tac (map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝])
	THEN REPEAT strip_tac THEN all_asm_fc_tac []
	THEN_TRY asm_rewrite_tac[];
fun ⦏syll_ruleL⦎ g = tac_proof (g, syll_tacL);	
val ⦏syll_tacLb⦎ = REPEAT (POP_ASM_T ante_tac)
	THEN rewrite_tac (map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝])
	THEN contr_tac THEN asm_fc_tac[];
fun ⦏syll_ruleLb⦎ g = tac_proof (g, syll_tacLb);	
=TEX

\paragraph{Simple Conversion}

\ignore{
=SML
set_goal([⌜A e B⌝], ⌜B e A⌝);
a (syll_tacL);
a (∃_tac ⌜x⌝ THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
val e_conv_thm = save_pop_thm "e_conv_thm"; 

set_goal([⌜A i B⌝], ⌜B i A⌝);
a (syll_tacL);
a (DROP_NTH_ASM_T 1 (asm_tac o eq_sym_rule));
a (asm_fc_tac[]);
val i_conv_thm = save_pop_thm "i_conv_thm"; 
=TEX
}%ignore

=GFT
val ⦏e_conv_thm⦎ = A e B ⊢ B e A : THM
val ⦏i_conv_thm⦎ = A i B ⊢ B i A : THM
=TEX

\paragraph{Conversion Per Accidens}

These are OK.

=IGN
set_goal([⌜A a B⌝], ⌜B i A⌝);
a (syll_tacLb);
a (spec_nth_asm_tac 1 ⌜q:'a⌝ THEN ∃_tac ⌜q:'a⌝ THEN asm_rewrite_tac[]);

set_goal([⌜A e B⌝], ⌜B o A⌝);
a (syll_tacLb);
a (swap_asm_concl_tac ⌜¬ A x = B x⌝ THEN asm_rewrite_tac[]);


val ai_conv_thm = save_thm ("ai_conv_thm", syll_ruleL([⌜A a B⌝], ⌜B i A⌝));
val eo_conv_thm = save_thm ("eo_conv_thm", syll_ruleL([⌜A e B⌝], ⌜B u A⌝));
=TEX

=GFT
val ⦏ai_conv_thm⦎ = A a B ⊢ B i A : THM
val ⦏eo_conv_thm⦎ = A e B ⊢ B o A : THM
=TEX

\paragraph{Obversion}

For these we need to define an operation of complementation on terms.

ⓈHOLCONST
│ ⦏Complement⦎ : TermL → TermL
├──────
│ ∀A α⦁ (Complement A) α =
		if A α = pTrue then pFalse
		else if A α = pFalse then pTrue
		else pU 
■

We will use ``\verb!~!'' as a shorthand for ``Complement''.

=SML
declare_alias ("~", ⌜Complement⌝);
=TEX

\ignore{
=SML
add_pc_thms "'leibniz02" [get_spec ⌜Complement⌝];
set_merge_pcs ["misc2", "'leibniz02"];
val ⦏syll_tacLb⦎ = REPEAT (POP_ASM_T ante_tac) THEN rewrite_tac (map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝])
	THEN contr_tac THEN asm_fc_tac[];
fun ⦏syll_ruleLb⦎ g = tac_proof (g, syll_tacLb);	
=TEX
}%ignore

\ignore{
=IGN
val ae_obv_thm = save_thm ("ae_obv_thm", syll_ruleL([⌜A a B⌝], ⌜A e ~B⌝));
val iu_obv_thm = save_thm ("iu_obv_thm", syll_ruleLb([⌜A i B⌝], ⌜A u ~B⌝));
=TEX
}%ignore

Only two of the obversions are valid.

=GFT
val ae_obv_thm = A a B ⊢ A e ~ B : THM
val iu_obv_thm = A i B ⊢ A o ~ B : THM
=TEX

\subsubsection{The Square of Opposition}

=GFT
ao_contrad_thm = ⊢ A a B ⇔ ¬ A o B
ei_contrad_thm = ⊢ A e B ⇔ ¬ A i B
ae_contrar_thm = ⊢ ¬ (A a B ∧ A e B)
io_subcont_thm = ⊢ A i B ∨ A o B
ai_subalt_thm = ⊢ A a B ⇒ A i B
eo_subalt_thm = ⊢ A e B ⇒ A o B
=TEX

\ignore{
=IGN
val ao_contrad_thm = save_thm ("ao_contrad_thm", syll_ruleL ([], ⌜(A a B) ⇔ ¬ (A o B)⌝));
val ei_contrad_thm = save_thm ("ei_contrad_thm", syll_ruleL ([], ⌜(A e B) ⇔ ¬ (A i B)⌝));

set_goal ([], ⌜¬ (A a B ∧ A e B)⌝);
a (syll_tacL);
val ae_contrar_thm = save_pop_thm "ae_contrar_thm";

set_goal ([], ⌜A i B ∨ A u B⌝);
a (syll_tacL);
val io_subcont_thm = save_pop_thm "io_subcont_thm";

set_goal ([], ⌜A a B ⇒ A i B⌝);
a (syll_tacL);
val ai_subalt_thm = save_pop_thm "ai_subalt_thm";

set_goal ([], ⌜A e B ⇒ A u B⌝);
a (syll_tacL);
val eo_subalt_thm = save_pop_thm "eo_subalt_thm";
=TEX
}%

\subsubsection{The Syllogisms}

First we make a \emph{mapkit}.

=SML
val sLmapkit:mapkit = mkSimpMapkit ⓣTermL⌝ [⌜$a⌝,⌜$e⌝,⌜$i⌝,⌜$u⌝];
=TEX

Then we apply this in generating and proving the syllogisms.

=SML
proveGoals syll_tacL "" (mkGoals sLmapkit syllogism_data1);
proveGoals syll_tacL "" (mkGoals sLmapkit syllogism_data2);
proveGoals syll_tacL "" (mkGoals sLmapkit syllogism_data3);
=TEX

The theorems are also displayed in the theory listing in \thyref{leibniz02}


\section{Metaphysics}\label{LMETAPHYSICS}

This is an adaptation of the model of Aristotelian logic and metaphysics in section \ref{METAPHYSICSII}, to reflect the most crucial differences between Aristotle and Leibniz.

Russell \cite{russellPL} represents Leibniz as having adhered rather strictly to Aristotle's logic with bad consequences for his metaphysics, in particular he sees the idea of monads as having arisen from the idea that all propositions have subject/predicate form.
This is something into which I hope to look more closely in due course.

However, our analysis of Aristole suggests that if his metaphysics is so construed as to make his logic sound, then existence is necessary, and this view is incorporated into our model (which may go too far in this matter).
For Leibniz however the position on existence is pretty clear.
Existence of substantial individuals is the only thing which is contingent, all else is necessary.

The following model is therefore an exploration of what happens if we tweak the underlying model to ensure exactly that.
One thing that we should expect, is that the syllogisms which exhibit the ``existential fallacy'' will no longer be sound.
The second thing which seems to flow from that is the irrelevance of the essential/accidental distinction which is possibly the most important feature of Aristotelian metaphysics.
In \ref{METAPHYSICSII} I assume that this distinction is intended to correspond to that between necessary and contingent truth (though this may be tendentious, I am not aware of explicit textual support for it).
This can no longer be done, and I therefore abandon Aristotelian metaphysics altogether returning to a treatment of the syllogism less influenced by metaphysics.

The connection with Grice and Codd is no longer relevant so that material also is excised.

=SML
open_theory "misc2";
force_new_theory "leibniz03";
force_new_pc "`leibniz03";
=TEX

\ignore{
=SML
force_new_pc ⦏"'leibniz03"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'leibniz03";
set_merge_pcs ["misc2", "'leibniz03"];
=TEX
}%ignore

\subsection{The Subject Matter}

Once the essential/accidental distinction is discarded, we are left with a metaphysic in which the key distinction is between individual substances and predicates.

We take an individual to be something which is only truly predicable of itself, and other predicates as collections of individuals, once again accounting for (essential) predication as set inclusion (having represented an individual as a unit set).
This subset relation is fixed, but the individual substances which are the extensions of predicates are themselves contingent.

=SML
new_type ("ISUB", 0);
=TEX

Let us take a new type for a fixed population of predicates.

=SML
new_type ("PRED", 0);
=TEX

Whose extension is fixed.

ⓈHOLCONST
│ ⦏extension⦎ : PRED → ISUB ℙ
├──────
│ T
■

However, the extension is defined in terms of individual substances whose existence is contingent, and so we still have the possibility of distinguishing essential predication from accidental, according to whether inclusion obtains on the full extension, or merely on the extensions restricted to the individuals which actually exist.

A possible world is therefore a collection of individuals.

=SML
declare_type_abbrev ("W", [], ⓣISUB ℙ⌝);
=TEX

We to distinguish one possible world which is the actual world:

ⓈHOLCONST
│ ⦏actual_world⦎ : W
├──────
│ T
■

Subjects and predicates are just things of type {\it PRED}.

\subsection{Predication}

Though the retreat from accidental predication simplifies matters I will retain a presentation of the syllogism similar to that in Section \ref{METAPHYSICSII}, for the sake of its readability.

So I separate out the quantifier by defining {\it All} and {\it Some} appropriately, and retain the postfix negator even though only one kind of predication is now available.
(in fact I could define the two kinds of predication because the I still have available two kinds of extension, but the modal operators suffice to express the distinction between the two kinds of predication).

I will then treat the modal operators as operators over propositions, and introduce the syllogism as a kind of judgement.

The type of the primitive copulas is:

=SML
declare_type_abbrev("COPULA", [], ⓣISUB → PRED → (W → BOOL)⌝);
=TEX

The first parameter is an individual substance rather than a PRED, the quantifying operato will arrange for each of the relevant individuals to be supplied.

\paragraph{Propositions}

=SML
declare_type_abbrev ("MPROP", [], ⓣW → BOOL⌝);
=TEX

\paragraph{Complementation}

The distinction between affirmative and negative is achieved by a postfix negation so we can say ``is not'', or ``are not'' (which in this models would be synonyms, so we will go with ``are'' only.

=SML
declare_postfix (100, "not");
=TEX

ⓈHOLCONST
│ $⦏not⦎ : COPULA → COPULA
├──────
│ ∀pred⦁ pred not = λpa t w⦁ ¬ pred pa t w 
■

\paragraph{Quantifiers}

The quantifiers expect to be supplied with a copula and a term.
The quantifier then predicates using the copula the term of everything or something in the domain of quantification (which is the subject term).
The copulas are defined below.

=IGN
declare_prefix(400, "All");
declare_prefix(400, "Some");
=TEX

ⓈHOLCONST
│ ⦏All⦎ : PRED → (ISUB → PRED → MPROP) → PRED → MPROP
├──────
│ ∀ s r p⦁ All s r p = λw⦁ ∀z⦁ z ∈ extension s ∧ z ∈ w ⇒ r z p w
■

ⓈHOLCONST
│ ⦏Some⦎ : PRED → (ISUB → PRED → MPROP) → PRED → MPROP
├──────
│ ∀ s r p⦁ Some s r p = λw⦁ ∃z⦁ z ∈ extension s ∧ z ∈ w ∧ r z p w
■

\paragraph{Predication}

For essential predication it is necessary that the individual and the predicate are both of the same category and then reduces under our model to set membership.
In effect. since the non-substantial individuals are tagged with their category, we need only deal separately with the distinction between substantial and non-substantial and the set inclusion will ensure a match in the non-substantial categories.

ⓈHOLCONST
│ ⦏are⦎ : ISUB → PRED → MPROP
├──────
│ ∀ i t⦁ are i t = λw⦁ i ∈ extension t
■

\paragraph{Modal Operators}

In this model the model operators are operators over propositions.

ⓈHOLCONST
│ ⦏⦇⦎ : MPROP → MPROP
├──────
│ ∀p⦁ ⦇ p = λw⦁ ∃w'⦁ p w' 
■

ⓈHOLCONST
│ ⦏⦈⦎ : MPROP → MPROP
├──────
│ ∀p⦁ ⦈ p = λw⦁ ∀w'⦁ p w' 
■

\subsection{Propositional Operators}

Though the truth functional propositional operators do not feature in the syllogism it is nevertheless useful to have them in giving a full account of Aristotle's logic and they are therefore here defined.

That these propositional operators are ``truth functional'', in a context in which propositions are not regarded as denoting truth values requires a little explanation perhaps.
Our propositions are families of truth values indexed by possible worlds, i.e. functions from possible worlds to truth values, or in the context of a two valued logic (which Aristotle's seems to be), sets of possible worlds.
In this context the usual truth functional operators can be expressed by mapping the usual operator over the set of possible worlds, i.e. the result in every possible world is the result of applying the truth functional operator to the values of the propositions in that possible world.
These also correspond to the obvious set theoretic operation if the propositions are thought of as sets of possible worlds, i.e. intersetion for conjunction, complementation for negation.

The symbols for the operators are already in use, so we define the operations using decorated variants of the symbols and use an alias to allow the undecorated symbol to be used.


ⓈHOLCONST
│ ⦏¬⋎a⦎ : MPROP → MPROP
├──────
│ ∀p⦁ ¬⋎a p = λw⦁ ¬ (p w) 
■

=SML
declare_alias ("¬", ⌜¬⋎a⌝);
=TEX

=SML
declare_infix(220, "∧⋎a");
=TEX

ⓈHOLCONST
│ $⦏∧⋎a⦎ : MPROP → MPROP → MPROP
├──────
│ ∀p q⦁ (p ∧⋎a q) = λw⦁ (p w) ∧ (q w) 
■

=SML
declare_alias ("∧", ⌜$∧⋎a⌝);
=TEX

=SML
declare_infix(210, "⇒⋎a");
=TEX

ⓈHOLCONST
│ $⦏⇒⋎a⦎ : MPROP → MPROP → MPROP
├──────
│ ∀p q⦁ (p ⇒⋎a q) = λw⦁ p w ⇒ q w 
■

=SML
declare_alias ("⇒", ⌜$⇒⋎a⌝);
=TEX

=SML
declare_infix(200, "⇔⋎a");
=TEX

ⓈHOLCONST
│ $⦏⇔⋎a⦎ : MPROP → MPROP → MPROP
├──────
│ ∀p q⦁ (p ⇔⋎a q) = λw⦁ p w ⇔ q w 
■

=SML
declare_alias ("⇔", ⌜$⇔⋎a⌝);
=TEX

\subsection{Quantification}

The Grice/Code analysis makes use of quantifiers, particularly existential quantification.
To verify the formulae in this context we therefore need to define modal version of the quantifiers. 

=SML
declare_binder "∀⋎a";
=TEX

ⓈHOLCONST
│ $⦏∀⋎a⦎ : (PRED → MPROP) → MPROP
├──────
│ ∀mpf⦁ $∀⋎a mpf = λw⦁ ∀t⦁ mpf t w
■
=SML
declare_alias ("∀", ⌜$∀⋎a⌝);
=TEX

=SML
declare_binder "∃⋎a";
=TEX

ⓈHOLCONST
│ $⦏∃⋎a⦎ : (PRED → MPROP) → MPROP
├──────
│ ∀mpf⦁ $∃⋎a mpf = λw⦁ ∃t⦁ mpf t w
■
=SML
declare_alias ("∃", ⌜$∃⋎a⌝);
=TEX

\subsection{Judgements}

I'm not yet clear what to offer here, so for the present I will define two kinds of sequent, which will be displayed with the symbols $Ξ$ asnd $Π$. the former being a kind of contingent material implication and the latter a necessary implication.

Both form of judgement seem suitable for expressing the rules of the syllogism at first glance but which can also be used for conversions.

The first expresses a contingent entailment, that if some arbitrary finite (possibly empty) collection of premises are contingently true, then some conclusion will also be true.
Since the consequence is material, and the premisses might be contingent, the conclusion might also be contingent.
One might hope that if the rules of the syllogism are applied and the premises are necessary, then so will be the conclusions. 

=SML
declare_infix(100, "Ξ");
=TEX

ⓈHOLCONST
│ $⦏Ξ⦎ : MPROP LIST → MPROP → BOOL
├──────
│ ∀lp c⦁ lp Ξ c ⇔ Fold (λp t⦁ p actual_world ∧ t) lp T ⇒ c actual_world
■

This one says that in every possible world the premises entail the conclusion (still material).

=SML
declare_infix(100, "Π");
=TEX

ⓈHOLCONST
│ $⦏Π⦎ : MPROP LIST → MPROP → BOOL
├──────
│ ∀lp c⦁ lp Π c ⇔ ∀w⦁ Fold (λp t⦁ p w ∧ t) lp T ⇒ c w
■

In the present context the choice between the two is probably immaterial, since we know no more about the actual world than any other, so anything that we can prove to be true contingently, we can also prove to be true necessarily.

\subsection{Conversions}

\paragraph{Premisses, their Modes and Conversions}

See: \href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o3102c.htm#2}{Prior Analytics Book 1 Part 2 Paragraph 2}.

\begin{quote}
First then take a universal negative with the terms A and B.

If no B is A, neither can any A be B. For if some A (say C) were B, it would not be true that no B is A; for C is a B.

But if every B is A then some A is B. For if no A were B, then no B could be A. But we assumed that every B is A.

Similarly too, if the premiss is particular. For if some B is A, then some of the As must be B. For if none were, then no B would be A. But if some B is not A, there is no necessity that some of the As should not be B; e.g. let B stand for animal and A for man. Not every animal is a man; but every man is an animal.
\end{quote}

These work out fine for {\it izz}, so I will do those first, and then show that they fail for {\it hazz} and {\it is}.

The first and third conversions are most useful when expressed as an equation, since our proof system is based primarily on rewriting using equations.

=GFT
⦏are_not_lemma⦎ =
	⊢ All B (are not) A = All A (are not) B
⦏some_are_lemma⦎ =
	⊢ Some B are A = Some A are B
=TEX

These we also supply as our Aristotelian judgements, together with the second which does not give an equation.
The second conversion embodies the existential fallacy, and therefore is not provable here.

=GFT
⦏are_conv1⦎ = ⊢
	[All B (are not) A] Π All A (are not) B

⦏are_conv2⦎ = ⊢
	[All B izz A] Π Some A izz B

⦏are_conv3⦎ = ⊢
	[Some B izz A] Π Some A izz B
=TEX

\ignore{
=SML
set_goal([], ⌜All B (are not) A = All A (are not) B⌝);
a (rewrite_tac [ext_thm]);
a (strip_tac THEN rewrite_tac [get_spec ⌜All⌝]);
a (contr_tac);
(* *** Goal "1" *** *)
a (POP_ASM_T (strip_asm_tac o (rewrite_rule (map get_spec [⌜are⌝, ⌜$not⌝]))));
a (asm_fc_tac[]);
a (POP_ASM_T (strip_asm_tac o (rewrite_rule (map get_spec [⌜are⌝, ⌜$not⌝]))));
val are_not_lemma = save_pop_thm "are_not_lemma";

set_goal([], ⌜Some B are A = Some A are B⌝);
a (rewrite_tac [ext_thm]);
a (strip_tac THEN rewrite_tac (map get_spec [⌜Some⌝, ⌜are⌝]));
a (contr_tac);
a (spec_nth_asm_tac 1 ⌜z⌝);
val some_are_lemma = save_pop_thm "some_are_lemma";

set_goal([], ⌜[All B (are not) A] Π All A (are not) B⌝);
a (rewrite_tac (map get_spec [⌜$Π⌝, ⌜$⇔⋎a⌝]));
a (strip_tac THEN rewrite_tac [get_spec ⌜Fold⌝, get_spec ⌜All⌝, are_not_lemma]);
val are_conv1 = save_pop_thm "are_conv1";

=IGN
set_goal([], ⌜[All B izz A] Π  Some A izz B⌝);
a (rewrite_tac (map get_spec [⌜$Π⌝]));
a (strip_tac THEN rewrite_tac [get_spec ⌜Fold⌝, get_spec ⌜All⌝, get_spec ⌜Some⌝, get_spec ⌜izz⌝]);
a (REPEAT strip_tac);
a (∃_tac ⌜(Fst B, MemOf (Snd B))⌝ THEN asm_rewrite_tac[]);
a (SPEC_NTH_ASM_T 1 ⌜(Fst B, MemOf (Snd B))⌝ (rewrite_thm_tac o (rewrite_rule[])));
val izz_conv2 = save_pop_thm "izz_conv2";
=SML

set_goal([], ⌜[Some B are A] Π  Some A are B⌝);
a (rewrite_tac (map get_spec [⌜$Π⌝]));
a (strip_tac THEN rewrite_tac [get_spec ⌜Fold⌝, get_spec ⌜Some⌝, get_spec ⌜are⌝]);
a (REPEAT strip_tac);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
val are_conv3 = save_pop_thm "are_conv3";
=TEX
}%ignore

\subsection{Modal Conversions}

\paragraph{Prior Analytics Book 1 Part 3}

See: \href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/aristotl/o3103c.htm}{Universal and Possible Premisses and their Conversions}.

These are the conversions in relation to necessity and possibility described by Aristotle:

\begin{enumerate}
\item If it is necessary that no B is A, it is necessary also that no A is B.
\item If all or some B is A of necessity, it is necessary also that some A is B.
\item If it is possible that all or some B is A, it will be possible that some A is B.
\item and so on
\end{enumerate}

So in this section Aristotle only offers variants of the previous conversions with either ``possible'' or ``necessary'' attached to both premiss and conclusion.

We can prove generally that modal operators can be introduced into a conversion:

=GFT
⦏⦇_conv⦎ =
	⊢ [P] Π Q ⇒ [⦇ P] Π ⦇ Q

⦏⦈_conv⦎ =
	⊢ [P] Π Q ⇒ [⦈ P] Π ⦈ Q
=TEX

\ignore{
=SML
set_goal([], ⌜[P] Π Q ⇒ [⦇ P] Π ⦇ Q⌝);
a (rewrite_tac (map get_spec [⌜$Π⌝, ⌜Fold⌝, ⌜⦇⌝]));
a (REPEAT strip_tac);
a (∃_tac ⌜w'⌝ THEN asm_fc_tac[]);
val ⦇_conv = save_pop_thm "⦇_conv";

set_goal([], ⌜[P] Π Q ⇒ [⦈ P] Π ⦈ Q⌝);
a (rewrite_tac (map get_spec [⌜$Π⌝, ⌜Fold⌝, ⌜⦈⌝]));
a (REPEAT strip_tac);
a (asm_ufc_tac[] THEN asm_rewrite_tac[]);
val ⦈_conv = save_pop_thm "⦈_conv";
=TEX
}%ignore

Now according to Leibniz all predication is necessary, only existence is contingent.
However, the contingency of existence means that this must be interpreted as a claim about predicates applied only to individuals.


=GFT
⦏⦇AllBareA_thm⦎ = ⊢ [] Π ⦇ (All B are A)
=TEX

\ignore{
=SML
set_goal([], ⌜[] Π ⦇ (All B are A)⌝);
a (rewrite_tac  (map get_spec [⌜$Π⌝, ⌜Fold⌝, ⌜$⦇⌝])
	THEN REPEAT strip_tac);
a (∃_tac ⌜extension A⌝);
a (rewrite_tac [get_spec ⌜All⌝, get_spec ⌜are⌝, ∈_in_clauses]
	THEN REPEAT strip_tac);
val ⦇AllBareA_thm = save_pop_thm "⦇AllBareA_thm";
=IGN
set_goal([⌜∀A B⦁ [All A are B] Π ⦈ (All A are B)⌝], ⌜∀A B⦁ [] Π ⦈ (All A are B)⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac  (map get_spec [⌜$Π⌝, ⌜Fold⌝, ⌜$⦈⌝])
	THEN REPEAT strip_tac);
a (∃_tac ⌜extension A⌝);
a (rewrite_tac [get_spec ⌜All⌝, get_spec ⌜are⌝, ∈_in_clauses]
	THEN REPEAT strip_tac);
val ⦇AllBareA_thm = save_pop_thm "⦇AllBareA_thm";
=TEX
}%ignore


The upshot is that to show that our model captures the necessity of predication (in the sense in which this is conceivable), we need a way to talk about individuals.

ⓈHOLCONST
│ ⦏individual⦎ : PRED → MPROP
├──────
│ ∀A⦁ individual A = λw⦁ ∃a⦁ extension A = {a}
■

=GFT
⦏⦇AarenotA_thm⦎ = ⊢ [] Π ⦇ (All A (are not) A)
=IGN
⦏are_⦇_thm⦎ = ⊢ [All A are B] Π ⦇ (All A are B)
⦏not_⦈_are_thm⦎ = ⊢ [] Ξ (¬ ⦈ (All A are B))
⦏⦈_are_thm2⦎ = ⊢ [⦈ (All A are B)] Π All A are B
⦏not_⦈_are_thm2⦎ = ⊢ [] Π (¬ ⦈ (All A are B))
=TEX

There are many theorems which one would naturally prove at this point, to facilitate further proofs and proof automation, which are not expressible syllogistically.
Proof automation depends heavily on the demonstration of equations, so that proof may proceed by rewriting.
But syllogisms are not suitable for this.

The natural way to proceed in such a case is to continue in this theory doing things which support proofs of syllogisms without being restrained to syllogisms, and then to have a separate theory in which the syllogistic claims are presented.
Some reflection is desirable on what the philosophical objectives are and what course will best contribute to those purposes.

\ignore{
=SML
set_goal([], ⌜[] Ξ ⦇ (All A (are not) A)⌝);
a (rewrite_tac  (map get_spec [⌜$Ξ⌝, ⌜Fold⌝, ⌜$⦇⌝])
	THEN REPEAT strip_tac);
a (∃_tac ⌜{}⌝);
a (rewrite_tac [get_spec ⌜All⌝, get_spec ⌜are⌝, get_spec ⌜$not⌝, ∈_in_clauses]
	THEN REPEAT strip_tac);
val ⦇AarenotA_thm = save_pop_thm "⦇AarenotA_thm";

=IGN

set_goal([], ⌜¬[All A are B] Ξ ⦈ (All  A are B)⌝);
a (rewrite_tac  (map get_spec [⌜$Ξ⌝, ⌜Fold⌝, ⌜⦈⌝, ⌜All⌝, ⌜are⌝])
	THEN REPEAT strip_tac);
val are_⦈_thm = save_pop_thm "are_⦈_thm";

set_goal([], ⌜¬[All A are B] Π ⦈ (All  A are B)⌝);
a (rewrite_tac  (map get_spec [⌜$Π⌝, ⌜Fold⌝, ⌜⦈⌝, ⌜All⌝, ⌜are⌝])
	THEN REPEAT strip_tac);
a (∃_tac ⌜actual_world⌝ THEN REPEAT strip_tac);
val are_⦈_thm = save_pop_thm "are_⦈_thm";


set_goal([], ⌜[] Ξ ¬ ⦈ (All A hazz B)⌝);
a (rewrite_tac  (map get_spec [⌜$Ξ⌝, ⌜Fold⌝, ⌜⦈⌝, ⌜All⌝, ⌜izz⌝, ⌜$¬⋎a⌝, ⌜hazz⌝]));
a (REPEAT strip_tac);
a (∃_tac ⌜λw⦁ {}⌝ THEN rewrite_tac[] THEN strip_tac);
a (∃_tac ⌜(Fst A, MemOf(Snd A))⌝ THEN rewrite_tac[]);
val not_⦈_hazz_thm = save_pop_thm "not_⦈_hazz_thm";

set_goal([], ⌜[⦈ (All A izz B)] Π All A izz B⌝);
a (rewrite_tac  (map get_spec [⌜$Π⌝, ⌜Fold⌝, ⌜⦈⌝, ⌜All⌝, ⌜izz⌝])
	THEN REPEAT strip_tac);
val ⦈_izz_thm2 = save_pop_thm "⦈_izz_thm2";

set_goal([], ⌜[⦈ (All A hazz B)] Π All A izz B⌝);
a (rewrite_tac  (map get_spec [⌜$Π⌝, ⌜Fold⌝])
	THEN REPEAT strip_tac);
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac (map get_spec [⌜⦈⌝, ⌜All⌝, ⌜hazz⌝])
	THEN strip_tac);
a (∃_tac ⌜λw⦁ {}⌝ THEN rewrite_tac[] THEN strip_tac);
a (lemma_tac ⌜∃d⦁ d ∈ PeSet (Snd A)⌝ THEN1 rewrite_tac[]);
a (∃_tac ⌜(Fst A, d)⌝ THEN asm_rewrite_tac[]);
val ⦈_hazz_thm2 = save_pop_thm "⦈_hazz_thm2";

set_goal([], ⌜[All A izz B] Π ⦈ (All  A izz B)⌝);
a (rewrite_tac  (map get_spec [⌜$Π⌝, ⌜Fold⌝, ⌜⦈⌝, ⌜All⌝, ⌜izz⌝])
	THEN REPEAT strip_tac);
val izz_⦈_thm2 = save_pop_thm "izz_⦈_thm2";

set_goal([], ⌜[] Π ¬ ⦈ (All A hazz B)⌝);
a (rewrite_tac  (map get_spec [⌜$Π⌝, ⌜Fold⌝, ⌜⦈⌝, ⌜All⌝, ⌜izz⌝, ⌜$¬⋎a⌝, ⌜hazz⌝]));
a (REPEAT strip_tac);
a (∃_tac ⌜λw⦁ {}⌝ THEN rewrite_tac[] THEN strip_tac);
a (∃_tac ⌜(Fst A, MemOf(Snd A))⌝ THEN rewrite_tac[]);
val not_⦈_hazz_thm2 = save_pop_thm "not_⦈_hazz_thm2";
=TEX
}%ignore

Here are some general modal results which I have not noticed in Aristotle as yet.

=GFT
⦏⦈_elim_thm⦎ =
	⊢ [⦈ P] Ξ P
⦏⦇_intro_thm⦎ =
	⊢ [P] Ξ ⦇ P
⦏⦈_⦇_thm⦎ =
	⊢ [⦈ P] Ξ ⦇ P
=TEX

\ignore{
=SML
set_goal([], ⌜[⦈ P] Ξ P⌝);
a (rewrite_tac (map get_spec [⌜$Ξ⌝, ⌜Fold⌝, ⌜$⦈⌝]) THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
val ⦈_elim_thm = save_pop_thm "⦈_elim_thm";

set_goal([], ⌜[P] Ξ ⦇ P⌝);
a (rewrite_tac (map get_spec [⌜$Ξ⌝, ⌜Fold⌝, ⌜$⦇⌝]) THEN contr_tac THEN asm_fc_tac[]);
val ⦇_intro_thm = save_pop_thm "⦈_intro_thm";

set_goal([], ⌜[⦈ P] Ξ ⦇ P⌝);
a (rewrite_tac (map get_spec [⌜$Ξ⌝, ⌜Fold⌝, ⌜$⦈⌝, ⌜$⦇⌝]) THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
val ⦈_⦇_thm = save_pop_thm "⦈_⦇_thm";
=TEX
}%ignore

\subsection{Other Conversions}

The following coversions relate to the square of opposition, but I have not yet discovered where they appear in Aristotle.
They work for all the copulas, so I have used a free variable for the copulas.

=GFT
¬_All_conv_thm =
	⊢ (¬ All A cop B) = Some A (cop not) B
¬_All_not_conv_thm2 =
	⊢ (¬ All A (cop not) B) = Some A cop B
¬_Some_conv_thm =
	⊢ (¬ Some A cop B) = All A (cop not) B
¬_Some_not_conv_thm =
	⊢ (¬ Some A (cop not) B) = All A cop B
=TEX

They are contraries out of Aristotles square of opposition

\ignore{
=SML
set_goal([], ⌜(¬ All A cop B) = Some A (cop not) B⌝);
a (rewrite_tac (map get_spec [⌜All⌝, ⌜Some⌝, ⌜$not⌝, ⌜¬⋎a⌝]));
a (rewrite_tac[ext_thm] THEN contr_tac THEN asm_fc_tac[]);
val ¬_All_conv_thm = save_pop_thm "¬_All_conv_thm";

set_goal([], ⌜(¬ All A (cop not) B) = Some A cop B⌝);
a (rewrite_tac (map get_spec [⌜All⌝, ⌜Some⌝, ⌜$not⌝, ⌜¬⋎a⌝]));
a (rewrite_tac[ext_thm] THEN contr_tac THEN asm_fc_tac[]);
val ¬_All_not_conv_thm2 = save_pop_thm "¬_All_not_conv_thm2";

set_goal([], ⌜(¬ Some A cop B) = All A (cop not) B⌝);
a (rewrite_tac (map get_spec [⌜All⌝, ⌜Some⌝, ⌜$not⌝, ⌜¬⋎a⌝]));
a (rewrite_tac[ext_thm] THEN contr_tac THEN asm_fc_tac[]);
val ¬_Some_conv_thm = save_pop_thm "¬_Some_conv_thm";

set_goal([], ⌜(¬ Some A (cop not) B) = All A cop B⌝);
a (rewrite_tac (map get_spec [⌜All⌝, ⌜Some⌝, ⌜$not⌝, ⌜¬⋎a⌝]));
a (rewrite_tac[ext_thm] THEN contr_tac THEN asm_fc_tac[]);
val ¬_Some_not_conv_thm = save_pop_thm "¬_Some_not_conv_thm";
=TEX
}%ignore

Normally theorems like this would be proved closed, but it looks less Aristotelian without the quantifiers and we can imagine they are schemata.
To use them it will usually be desirable to close them, which is easily done, e.g.:

=SML
all_∀_intro ¬_Some_not_conv_thm;
=TEX

=GFT ProofPower output
val it = ⊢ ∀ A cop B⦁ (¬ Some A (cop not) B) = All A cop B : THM
=TEX

\subsection{Syllogisms}

The abolition of accidental predication should result in a syllogistic logic which corresponds to Aristotle, though the contingency of existence means that the existential fallacies really are fallacies.

We can, by methods similar to those used above obtain automatic proofs of the syllogisms which are valid in this model.

The details are omitted, but the valid syllogisms have been proven and stored in the theory, see: \thyref{leibniz03}.

\ignore{
=SML
fun 	⦏opfun_from_char⦎ cop "a" s p = ⌜All ⓜs⌝ ⓜcop⌝ ⓜp⌝⌝
|	opfun_from_char cop "e" s p = ⌜All ⓜs⌝ (ⓜcop⌝ not) ⓜp⌝⌝
|	opfun_from_char cop "i" s p = ⌜Some ⓜs⌝ ⓜcop⌝ ⓜp⌝⌝
|	opfun_from_char cop "o" s p = ⌜Some ⓜs⌝ (ⓜcop⌝ not) ⓜp⌝⌝;

fun ⦏opfuntrip_from_text⦎ cop s =
	let val [a, b, c] = (map (opfun_from_char cop) o vowels_from_string) s;
	in (a, b, c)
	end;

fun ⦏opfuntrip_from_text_cc⦎ (cop1,cop2) s =
	let val [v1, v2, v3] = vowels_from_string s;
	    val [a, b, c] = [opfun_from_char cop1 v1, opfun_from_char cop2 v2, opfun_from_char ⌜hazz⌝ v3];
	in (a, b, c)
	end;
=TEX

The following functions construct a syllogism.

=SML
val ⦏figures⦎ = figurest;

fun ⦏mk_are_syll⦎ vt (a, b, c, d) (f1, f2, f3) =
	⌜[ⓜf1 a b⌝; ⓜf2 c d⌝] Π
		ⓜf3 (mk_var("𝕊", vt)) (mk_var("P", vt))⌝⌝;

fun ⦏mk_cop_syllp⦎ cop (s, n) =
	([], mk_are_syll ⓣPRED⌝ (nth (n-1) (figures ⓣPRED⌝)) (opfuntrip_from_text cop s));

fun ⦏mk_cop_syllp_cc⦎ cc (s, n) =
	([], mk_are_syll ⓣPRED⌝ (nth (n-1) (figures ⓣPRED⌝)) (opfuntrip_from_text_cc cc s));

fun ⦏mk_are_syllp⦎ (s, n) = mk_cop_syllp ⌜are⌝ (s, n);

val ⦏syll_are_tac2⦎ =
	asm_prove_tac (map get_spec [⌜$Π⌝, ⌜All⌝, ⌜Some⌝, ⌜are⌝, ⌜$not⌝, ⌜Fold⌝])
	THEN contr_tac THEN REPEAT_N 2 (all_asm_fc_tac[])
	THEN (spec_nth_asm_tac 1 ⌜z:ISUB⌝)
	THEN REPEAT_N 2 (all_asm_fc_tac[]);

fun ⦏syll_are_rule2⦎ g = tac_proof(g, syll_are_tac2);

val ⦏sps_are1⦎ = syll_prove_and_store mk_are_syllp "_are";

val ⦏valid_are_sylls⦎ = map (sps_are1 syll_are_tac2) syllogism_data1;
=IGN
set_goal(mk_are_syllp ("Baroco", 2));
a (syll_are_tac2);

=TEX

}%ignore
