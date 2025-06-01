=IGN
$Id: t001.doc,v 1.16 2009/10/05 09:18:19 rbj Exp $
=TEX
\def\rbjidtAABdoc{$$Id: t001.doc,v 1.16 2009/10/05 09:18:19 rbj Exp $$}

\section{Logical Truth}

To model the fundamental notion of ``logical truth'', we consider various ways in which the semantics of languages can be formally defined.
There are many ways of doing this.
The choice of how to render the semantics may be part of the process of defining a language or class of languages.
Definitions of logical truth are then specific to classes of languages which have the same kind of formal semantics.

\subsection{Bare-Boned Truth-Conditions}\label{Bare-Boned Truth-Conditions}

\ignore{
\subsection{Technical Prelude}

First of all, we must give the the ML commands to  introduce the new theory ``analytic'' as a child of the theory ``hol''.

=SML
open_theory "misc2";
force_new_theory "t001a";
set_merge_pcs["misc21"];
=TEX
}%ignore


\subsection{Types}

The following ``primitive'' types are introduced:

=SML
new_type("S",0);  (* sentences *) 
new_type("C",0);  (* contexts *)
new_type("W",0);  (* possible worlds *)
new_type("P",0);  (* propositions *)
=TEX

\subsection{The Semantics}

The semantics of our language comes in two parts.
A semantic map which delivers propositions, the meanings of sentences in context,
and a propositional evaluation map, which extracts truth conditions from a proposition.

The purpose of this document is not to consider the semantics of any particular language but to reason about semantics and concepts defined in terms of semantics.
We could have used variables for the semantics, but this time I decided to use loosely defined constants.
So the following definitions only tell you the type of the semantic map and the evaluation map, they don't tell you anything more than that, so any results we subsequently obtain using these definitions will hold good for any language with a semantics of the type stipluated here.

ⓈHOLCONST
│ ⦏sm⦎ : S × C → P
├──────
│ T
■

ⓈHOLCONST
│ ⦏pem⦎ : P × W → TTV
├──────
│ T
■

Note that $TTV$ is a type consisting of three `truth' values, whose names are: $pTrue$, $pFalse$ and $pU$.

\subsection{Necessity}

A proposition is `necessarily t' if it takes truth value `t' in every possible world.

ⓈHOLCONST
│ ⦏necessarily⦎ : TTV → P → BOOL
├──────
│ ∀t:TTV; p:P⦁ necessarily t p ⇔ ∀w:W⦁ pem(p, w) = t
■

A proposition is {\it necessary} (simpliciter) if it is {\it necessarily t} for some truth value {\it t}.

ⓈHOLCONST
│ ⦏necessary⦎ : P → BOOL
├──────
│ ∀p:P⦁ necessary p ⇔ ∃t⦁ necessarily t p
■

ⓈHOLCONST
│ ⦏contingent⦎ : P → BOOL
├──────
│ ∀p:P⦁ contingent p ⇔ ∃w1 w2⦁ ¬ pem(p, w1) = pem(p, w2)
■

\subsection{True in Virtue of Meaning}

A common definition of ``analytic'' is as `true in virtue of meaning', so we will now try to formalise that idea. 
If the truth value of a sentence can be ascertained from its meaning only, i.e. without taking into account any `extra-linguistic fact' (in Quine's words), i.e. without knowing anything about what possible world is actual.
This can only be known if it takes the same truth value in every possible world.

This can be generalised to an arbitrary truth value.

Therefore we define:

=SML
declare_infix (300, "by_meaning");
=TEX

ⓈHOLCONST
│ $⦏by_meaning⦎ : TTV → (S × C) → BOOL
├──────
│ ∀t:TTV; s:S; c:C⦁ t by_meaning (s, c) ⇔ ∀p⦁ pem (sm(s, c), p) = t
■

\subsection{Expresses a Necessary Proposition}

My preferred definition of analyticity is that a sentence is analytic if the proposition it expresses is necessarily true.
Again we generalise to an arbitrary truth value.
I'll make this infix as well.

=SML
declare_infix (300, "analytic");
=TEX

ⓈHOLCONST
│ $⦏analytic⦎ : TTV → (S × C) → BOOL
├──────
│ ∀t:TTV; s:S; c:C⦁ t analytic (s, c) ⇔ necessarily t (sm(s, c))
■

Now we prove that these two conception of analyticity are the same.

The proof is trivial, exanding the relevant definitions yields a universally quantified identity equation (apart from the names of the bound variables).
In the following proof script, the necessary rewriting is broken into two stages to show the identity.

=SML
set_goal([], ⌜∀t s c⦁ t analytic (s,c) ⇔ t by_meaning (s, c)⌝);
a (pure_rewrite_tac (map get_spec [⌜$analytic⌝, ⌜$by_meaning⌝, ⌜necessarily⌝]));
=GFT
(* *** Goal "" *** *)

(* ?⊢ *)  ⌜∀ t s c⦁ (∀ w⦁ pem (sm (s, c), w) = t) = (∀ p⦁ pem (sm (s, c), p) = t)⌝
=SML
a (rewrite_tac[]);
val analyticity_lemma1 = save_pop_thm "analyticity_lemma1";
=TEX

\section{KANT'S DEFINITION OF ANALYTICITY}

\subsection{First Shot}

Kant defined analyticity only for "subject predicate" sentences, and some have therefore supposed this to be less general than more recent formulations.
However, asssuming only that the notion of analyticity is to be preserved by logical equivalence we can show that Kant's definition is equivalent to the preceding ones.

There is an awkwardness in generalising this notion to three truth values, so I will do it only for the one.

We will first define predicate inclusion.

=SML
declare_infix (300, "contains");
=TEX

ⓈHOLCONST
│ $⦏contains⦎ : ('a → BOOL) → ('a → BOOL) → BOOL
├──────
│ ∀P Q⦁ P contains Q ⇔ ∀x⦁ Q x ⇒ P x
■

$P\ contains\ Q$ is a way of writing a subject predicate assertion in which the subject is $Q$ and the predicate is $P$ (this is Aristotelian terminology, we don't use predication in this way in modern logic).

Now we show that every judgement is equivalent to one in "subject predicate" form:

=GFT
kantian_lemma =
	⊢ ∀ SS⦁ ∃ P Q⦁ SS ⇔ P contains Q
=TEX

=SML
set_goal([], ⌜∀SS⦁ ∃P Q⦁ SS ⇔ P contains Q⌝);
a (strip_tac THEN ∃_tac ⌜λx⦁ SS⌝ THEN ∃_tac ⌜λx⦁ T⌝);
a (rewrite_tac [get_spec ⌜$contains⌝]);
val kantian_lemma =  save_pop_thm "kantian_lemma";
=TEX

This lemma may be applied generally, thus:

=SML
val ℕ_gt_trans = ∀_elim ⌜∀x y z:ℕ⦁ x > y ∧ y > z ⇒ x > z⌝ kantian_lemma;
=TEX
yields:
=GFT
val ℕ_gt_trans =
   ⊢ ∃ P Q⦁ (∀ x y z⦁ x > y ∧ y > z ⇒ x > z) ⇔ P contains Q
=TEX

However, this is smoke and mirrors, because though it appears to be saying something about propositions, it is really about truth values.
i.e. we have proven that every sentence has the same truth value as some sentence in subject predicate form, i.e. that there is a false sentence and a true sentence in subject predicate form.

To have a relevance to the scope of Kant's definition of analyticity we need some real metatheoretic reasoning in which we talk about meanings of judgements.

\subsection{Fuller Treatment}

The treatment in the previous section is not wholly convincing.

A sufficient reason for this is that the central thesis is not itself formalised.
Insofar as there is any doubt about the thesis it therefore fails to improve the situation, and the question arises whether the theorems proven really establish the intended result.

The thesis is that, under certain provisos, Kant's definition of analyticity is equivalent to a definition along the lines of "true in virtue of meaning".
However, it seems probable that the conditions under which Kant's definition holds good differ significantly from those in which the other definition is applicable.
To formulate the thesis it is therefore necessary to establish some sufficient (and preferably necessary) conditions for both definitions to be applicable.

The required result is a general result covering a class of descriptive languages, and I think this will be better expressed if we abandon the previous methods of formalising in relation to some loosely specified but fixed (constant) language, and talk about languages using variables.

I will therefore start from scratch but replicate the same basic idea of what a descriptive language is.

Kant talks about "judgements", I will treat these as sentences in context.


\ignore{
\subsection{Technical Prelude}

First of all, we must give the the ML commands to  introduce the new theory ``t001b'' as a child of the theory ``hol''.

=SML
open_theory "misc2";
force_new_theory "t001b";
set_merge_pcs["misc21"];
=TEX
}%ignore

\subsection{Types}

In this version type variables will be used where constants were previously used, as follows:

\begin{itemize}
\item['S] Sentences
\item['C] Contexts
\item['P] Propositions
\item['W] Possible Worlds
\end{itemize}

\subsection{The Semantics}

The semantics of a `descriptive' language comes in two parts.
A semantic map which delivers propositions, the meanings of sentences in context,
and a propositional evaluation map, which extracts truth conditions from a proposition.

The purpose of this document is not to consider the semantics of any particular language but to reason about semantics and concepts defined in terms of semantics.

The following type abbreviations give the type of the semantics of a descriptive language.

=SML
(* Semantic Map *)
declare_type_abbrev ("SM", ["'C", "'P", "'S"], ⓣ'S × 'C → 'P⌝);

(* Propositional Evaluation Map *)
declare_type_abbrev ("PEM", ["'P", "'W"], ⓣ'P × 'W → BOOL⌝);

(* Language *)
declare_type_abbrev ("LAN", ["'C", "'P", "'S", "'W"], ⓣ('C, 'P, 'W)SM × ('P, 'W)PEM⌝);
=TEX

\subsection{Necessity}

A proposition is `necessary' if it takes truth value `T' in every possible world, the definition is parameterised by a propositional evaluation map.

ⓈHOLCONST
│ ⦏necessary⦎ : ('P, 'W)PEM → 'P → BOOL
├──────
│ ∀pem (p:'P)⦁ necessary pem p ⇔ ∀w:'W⦁ pem(p, w) = T
■

ⓈHOLCONST
│ ⦏contradictory⦎ : ('P, 'W)PEM → 'P → BOOL
├──────
│ ∀pem (p:'P)⦁ contradictory pem p ⇔ ∀w:'W⦁ pem(p, w) = F
■

ⓈHOLCONST
│ ⦏contingent⦎ : ('P, 'W)PEM → 'P → BOOL
├──────
│ ∀pem (p:'P)⦁ contingent pem p ⇔ ∃w1 w2:'W⦁ ¬ pem(p, w1) = pem(p, w2)
■



[to be completed!]
