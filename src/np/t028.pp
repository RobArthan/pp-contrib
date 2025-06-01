=IGN
val _ =
	let open ReaderWriterSupport.PrettyNames;
	in add_new_symbols [ (["identeq"], Value "\233", Simple) ]
end;
=TEX

\ignore{
=VDUMP t028i.tex
Last Change $ $Date: 2012/01/23 21:40:02 $ $

$ $Id: t028.doc,v 1.33 2012/01/23 21:40:02 rbj Exp $ $
=TEX
}%ignore

\def\rbjidtACIdoc{$$Id: t028.doc,v 1.33 2012/01/23 21:40:02 rbj Exp $$}

My purpose here is to use formal models to aid in understanding the philosophies of Plato\index{Plato} and Aristotle\index{Aristotle|bf}, both in relation to their contribution generally to the areas of interest, philosophical logic, semantics and metaphysics, and also more specifically in relation to the extent to which these philosophers laid the ground for the distinction which was later expressed in Hume's fork.

In doing this I began with some enquiries into Aristotle's metaphysics published by Code\index{Code} \cite{code88} and produced from this a preliminary model (Section \ref{METAPHYSICSI}).
In these an important defect is that the model does not support the u-p syllogisms on which Code's analysis depends more heavily than one might have expected, and also does not allow for modal operators, which not only enter into Code's material but are also important for the kinds of comparison with later philosophers which I had hoped to undertake.
I have also failed at this stage to bring out the distinction between Plato and Aristotle.
Perhaps more important is that I did not arrive at a good understanding of Code and the model is therefore unlikely to fully reflect his intensions.
It is also the case that the method I adopted for the analysis of Code is one which he would have been likely to question.
His paper does briefly discuss unfavourably the interpretation of Aristotle in terms of modern idom such as that of set theory.
It is an important part of my objectives in this document to discuss this kind of formal exgetics, and hopefully to explain contra Code why the use of modern set theoretic language is appropriate and helpful in the analysis of materials which could not have been originally conceived in such terms.

I then went back from the Metaphysics to the Organon\index{Aristotle!organon} and used formal models to come to a better understanding of Aristotle's formal syllogistic logic (Section \ref{ORGANON}).
In this seven models of increasing sophistication were produced and formed the basis for undertaking a further model of the metaphysics which incorporated the u-p syllogisms and modal operators (Section \ref{METAPHYSICSII}).
All of this is preliminary to addressing the real issues, which has not yet seriously begun.

\subsection{Preliminary Formalities}

In the document several different formal models are presented.
By and large they are independent, but a some features are common and are therefore presented here for use in all the models.

=SML
open_theory "misc2";
force_new_theory "aristotle";
=TEX

\ignore{
=IGN
force_new_pc ⦏"'ariscat"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'ariscat";
set_merge_pcs ["misc2", "'ariscat"];
=SML
set_pc "misc2";
=TEX
}%ignore

We define inequality:

=SML
declare_infix (300, "≠");
=TEX

ⓈHOLCONST
│ $⦏≠⦎ : 'a → 'a → BOOL
├──────
│ ∀x y⦁ x ≠ y ⇔ ¬ x = y
■

\section{Metaphysics (I)}\label{METAPHYSICSI}

In this section we consider some material on Aristotle's Metaphysics \cite{aristotleMetap} which originated in work of Grice and Code \cite{code88} and came to me from a \href{http://rbjones.com/pipermail/hist-analytic_rbjones.com/2009q2/000258.html}{posting of J.L. Speranza} on the hist-analytic mailing list.
Code's paper is also partially available at \href{http://books.google.co.uk/books?id=sHWK4Lz37sAC&printsec=frontcover#PPA411,M1}{Google Books}.

What Speranza posted was the list of formulae which are named below as c01 through c31 (though not exactly as given, I have massaged them to be acceptable to HOL and also have quantified over all free variables).

The analysis in this section is independent of the preceding analysis of Aristotle's syllogism, and considers predication from a rather different point of view, which hangs around the distinction between essential and accidental predication.
In the next section I will produce another model in which essence and accident are combined with a full treatment of modal syllogism so that some conclusions might be drawn about the relationship between essence and necessity in Aristotelean philosophy.

A new theory is needed which I will call ``ariscat'' which is created here:

=SML
open_theory "aristotle";
force_new_theory "ariscat";
=TEX

\ignore{
=SML
force_new_pc ⦏"'ariscat"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'ariscat";
set_merge_pcs ["misc2", "'ariscat"];
=TEX
}%ignore

\subsection{The Grice/Code/Speranza Formulae}

This work began with an attempt to analyse using {\Product} a set of formulae posted by J.L. Speranza to the \href{http://www.hist-analytic.org/}{hist-analytic mailing list}.
These were a Speranzan transcript of formulae published in a paper by Code \cite{code88}, the work presented in that paper having begun with some joint work with H.P.~Grice \cite{grice88}.

The following material labelled ``Code/Speranza'' began as a transcription from Speranza's email, and was later updated when Speranza pointed me to the partial availability of the Code paper on Google Books.
I then put back some of the detail missed in the Speranza version, enclosed in square brackets, and enclosed in curly braces some of the material which Speranza had added to Code's.

The terminology used is Grice's.
Code uses ``Is'' and ``Has'' instead of ``izz'' and ``hazz'' (which were coined by Grice and used by Speranza).
Aristotle's originals have been translated as ``SAID OF'' and ``IN'', according to Cohen (\href{http://faculty.washington.edu/smcohen/433/GriceCode.pdf}{Grice and Code on IZZing and HAZZing}).

The material is interspersed with a formalisation in \ProductHOL.
I have adopted some of Code's headings for sections.

\subsection{References to Plato}

By footnote in Code.

\begin{description}
\item[30]
	$Phaedo.\ 102 B 8 C-1$ with C10ff (cf. B 4-6)
\end{description}


\subsection{Aristotelian References}

These are gathered together temporarily and will later be distributed as footnotes.

\begin{description}
\item[$Cat.\ 1^a$, 12--15]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o1101i.htm}{Equivocally, Univocally and Derivatively.}
\item[$Cat.\ 1^b5$, 3b12]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o1101i.htm}{}
\item[$Cat.\ 2^a$, 19--34]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o1102i.htm}{Presence and Predication.}
\item[$Cat.\ 3^a$, 15--20]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o1103i.htm}{Subclasses and Predicability.}
\item[$Cat.\ 10^a$, 27ff.]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o1110i.htm}{Opposite, Contrary, Privative, Positive.}
\item[$De.\ Int.$ 7, $17^a$9--40]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o2107i.htm}{Universal and Individual Subjects.}
\item[$Post.\ An.\ A4,\ 73^a$34--$^b5$]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o4104i.htm}{What are the premisses of demonstration.}
	Distinguishing essential and accidental predication.
\item[$Metap.\ I1,\ 1059^a10-14$]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/m11001i.htm}{The One}.
\item[$Metap.\ Δ9,\ 1018^a1-4$]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/m1509i.htm}{Same and Different}.
	`Socrates' and `musical Socrates' are thought to be the same; but `Socrates' is not predicable of more than one subject, and 		therefore we do not say 'every Socrates' as we say 'every man'.
\item[$Metap.\ Δ18,\ 1022^a25-27$]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/m1518i.htm}{In Virtue Of}.
	Admissibility of self-predication of particulars.
\item[$Metap.\ Δ23,\ 1023^a11-13$]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/m1523c.htm}{Having and Being}.
	Two kinds of predication.
\item[$Metap.\ Z5$]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/m1705i.htm}{Only substance is definable.}
\item[$Metap.\ Z6, 1032^a4-6$]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/m1706i.htm}{Each thing and its essence are one and the same.}
\item[$Metap.\ Z8, 1034^a7$]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/m1708c.htm#2}{different in virtue of their matter}
\item[$Metap.\ Z11, 1037^a33-^b4$]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/m1711i.htm}{Formulae, Parts, Substance and Essence.}
\item[$Topics.\ H(VII) 1, 152^b25-29$]
	\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o1711i.htm}{Numerical identity.}
\end{description}


\subsection{Formal Principles}

We begin with ``Formal Principles'' which we take as implicit definitions of two kinds of Aristotelian predication.

=GFT Code/Speranza
[(A) Formal Principles]

[FP1] 1. A izz A.
[FP2] 2. (A izz B & B izz C) --> A izz C.
[FP3] 3. A hazz B -> -(A izz B).
[FP4] 4. A hazz B iff A hazz Some-Thing [something] that izz B.
=TEX

The modelling in \ProductHOL will be entirely conservative, so we provide explicit definitions for ``izz'' and ``hazz'' and prove that they satisfy these principles and suffice also for the definitions and theorems which follow.

If the formal development is complete the definitions will have been shown to be sufficient.
In order to test whether the principles suffice I will attempt to proceed on these alone, though I suspect that will not be possible.
Failing that I will offer informal arguments to the contrary (a formal argument would require ascent to a metatheory which would involve too much work).

In order to define these concepts we have to decide what they are about, and this is not straightforward.

\subsubsection{Categories}

Aristotle has a system of categories, and these seem central to the topic.
Much hangs on what these are, and to get a nice structure to our theory it seems advisable to do a bit of ``category theory'' first.
Of course this is not at all the same thing as the branch of mathematics which now goes by that name, but the choice of name for the mathematics was not entirely quixotic and at some point it might be interesting to think about the relationship between the two kinds of category theory.

Among these categories that of substances plays a special role.
Substances can be particular in which case they correspond to some individual, or not, in which case they are sets of individuals.
The particulars of the other categories are attributes, and the non-individuals are sets of attributes.
I don't think you can have singleton sets, so we can model all these categories as sets of sets in which the singleton sets are the individuals.
Attributes can also be considered as sets of individual substances and so there is a type difference between the category of substances and the other categories.

The following introduce new types and type abbreviations for modelling Aristotle's categories.

\begin{description}
\item ACAT is a type of attribute categories
\item ISUB is a type of individual substances
\item CATM is the type of the things which are in categories.

This is a `disjoint union', which means that there are two kinds of thing which one finds in categories, either a set of individual substances (using singleton sets to represent individual substances), or a set of properties of individual substances tagged with an attribute category.

\item CAT is a type abbreviation for a notion of category which is either an attribute category or some other category (which will stand for the category of substances).

\end{description}

There are some oversimplifications here which I am hoping will not be too serious for a useful first cut.

\begin{description}
\item[Modal Operators]
The main one is that this general approach will not permit the definition of modal operators, which are used by Code.
Whether there is real need for them seems to me doubtful, but if necessary a modal model could be provided.

\item[Empty Sets]
The second is that I have not excluded empty sets, and hence that there can be predicates with null extensions.
This is in fact consistent with Code's ``principles'', but we find that his definitions are written as if there were no empty predicates, even though this is not entailed by the principles.
Where Code's definitions presume non-emptiness of predicates I have chosen another definition which does not.
Some of the theorems are then unprovable.

\item[Extensionality]
Intracategorial equality will be extensional.
That appears to be what is required, so it probably isn't a problem!

\item[Predicability]
Aristotle defines particulars in terms of Predicability, they are the impredicables.
Its not clear how to deal with this, and it appears to be in terminological conflict with Code, who appears to use use ``predicable'' to mean ``truly predicable''.
Code has the general principle ``A izz A'' which implicitly asserts that everything is truly predicable of itself.
\end{description}

=SML
new_type(⦏"ACAT"⦎, 0);
new_type(⦏"ISUB"⦎, 0);
declare_type_abbrev (⦏"CATM"⦎, [], ⓣISUB ℙ + (ACAT × (ISUB → BOOL)ℙ)⌝);
declare_type_abbrev (⦏"CAT"⦎, [], ⓣONE + ACAT⌝);
=TEX

We name the category of substances.

ⓈHOLCONST
│ ⦏CatSubs⦎ : CAT
├──────
│ CatSubs = InL One
■

Now we define various operators over categories and their constituents which suffice for the development of an appropriate theory, in the context of which rest of the Aristotelian terminology will we hope prove definable.

First ``projection'' functions which yield the constituents of $MCAT$s.

ⓈHOLCONST
│ ⦏Cat⦎ : CATM → CAT
├──────
│ ∀x⦁ Cat x = if IsL x then CatSubs else InR(Fst (OutR x))
■

ⓈHOLCONST
│ ⦏IndvSet⦎ : CATM → ISUB ℙ
├──────
│ ∀x⦁ IndvSet x = OutL x
■

ⓈHOLCONST
│ ⦏AttrSet⦎ : CATM → (ISUB → BOOL)ℙ
├──────
│ ∀x⦁ AttrSet x = Snd(OutR x)
■

This one turns out handy.

ⓈHOLCONST
│ ⦏CatSet⦎ : CATM → (ISUB + (ISUB → BOOL))ℙ
├──────
│ ∀x⦁ CatSet x =
│	if Cat x = CatSubs
│	then {y | ∃z⦁ z ∈ IndvSet x ∧ y = InL z}
│	else {y | ∃z⦁ z ∈ AttrSet x ∧ y = InR z}
■

With these definitions in place we get a useful characterisation of identity for elements of $CATM$.

=GFT
catm_eq_lemma =
	⊢ ∀ A B⦁ A = B ⇔ Cat A = Cat B ∧ CatSet A = CatSet B
=TEX

\ignore{
=SML
set_goal([], ⌜∀A B⦁ A = B ⇔ Cat A =  Cat B ∧ CatSet A = CatSet B⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜Cat⌝, get_spec ⌜CatSet⌝]);
a (strip_asm_tac (∀_elim ⌜A⌝ sum_cases_thm) THEN asm_rewrite_tac[]
	THEN REPEAT_N 3 (TRY strip_tac)
	THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (POP_ASM_T (asm_tac o eq_sym_rule)
	THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜IsL B⌝);
(* *** Goal "2.1" *** *)
a (swap_nth_asm_concl_tac 2
	THEN asm_rewrite_tac[get_spec ⌜CatSubs⌝]);
(* *** Goal "2.2" *** *)
a (swap_nth_asm_concl_tac 2
	THEN rewrite_tac[asm_rule ⌜IsL B⌝, sets_ext_clauses, get_spec ⌜IndvSet⌝]);
a (strip_tac);
a (lemma_tac ⌜¬ y = OutL B⌝);
(* *** Goal "2.2.1" *** *)
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[get_spec ⌜InL⌝]);
a (GET_ASM_T ⌜IsL B⌝ (rewrite_thm_tac o (rewrite_rule [sum_clauses])));
(* *** Goal "2.2.2" *** *)
a (swap_nth_asm_concl_tac 1 THEN rewrite_tac[sets_ext_clauses]);
a (swap_nth_asm_concl_tac 1);
(* *** Goal "2.2.2.1" *** *)
a (strip_tac THEN ∃_tac ⌜InL x⌝ THEN asm_rewrite_tac[]);
a (contr_tac THEN asm_fc_tac[] THEN_TRY all_var_elim_asm_tac);
a (spec_nth_asm_tac 2 ⌜x⌝);
(* *** Goal "2.2.2.2" *** *)
a (strip_tac THEN ∃_tac ⌜InL x⌝ THEN asm_rewrite_tac[]);
a (contr_tac THEN asm_fc_tac[] THEN_TRY all_var_elim_asm_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "3" *** *)
a (POP_ASM_T (asm_tac o eq_sym_rule) THEN asm_rewrite_tac[]);
(* *** Goal "4" *** *)
a (lemma_tac ⌜¬ IsL B⌝);
(* *** Goal "4.1" *** *)
a (swap_nth_asm_concl_tac 2
	THEN asm_rewrite_tac[get_spec ⌜CatSubs⌝]);
(* *** Goal "4.2" *** *)
a (swap_nth_asm_concl_tac 2
	THEN rewrite_tac[asm_rule ⌜¬ IsL B⌝, sets_ext_clauses, get_spec ⌜IndvSet⌝]);
a (strip_tac);
a (lemma_tac ⌜¬ z = OutR B⌝);
(* *** Goal "4.2.1" *** *)
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[get_spec ⌜InR⌝]);
a (LEMMA_T ⌜IsR B⌝ (rewrite_thm_tac o (rewrite_rule [sum_clauses])));
a (DROP_ASM_T ⌜¬ IsL B⌝ ante_tac
	THEN strip_asm_tac (∀_elim ⌜B⌝ sum_cases_thm)
	THEN asm_rewrite_tac[]);
(* *** Goal "4.2.2" *** *)
a (asm_rewrite_tac[get_spec ⌜CatSubs⌝, get_spec ⌜AttrSet⌝]);
a (lemma_tac ⌜¬ Snd z = Snd(OutR B)⌝
	THEN1 swap_asm_concl_tac ⌜¬ z = OutR B⌝);
(* *** Goal "4.2.2.1" *** *)
a (LEMMA_T ⌜z = (Fst z, Snd z)⌝ pure_once_rewrite_thm_tac THEN1 prove_tac[]);
a (pure_asm_rewrite_tac[]);
a (LEMMA_T ⌜Fst z = Fst (OutR B)⌝ rewrite_thm_tac);
a (swap_asm_concl_tac ⌜InR (Fst z) = (if IsL B then CatSubs else InR (Fst (OutR B)))⌝);
a (asm_rewrite_tac[]);
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac [sets_ext_clauses]);
a (swap_nth_asm_concl_tac 1);
a (strip_tac THEN ∃_tac ⌜InR x⌝ THEN asm_rewrite_tac[]);
a (REPEAT strip_tac THEN_TRY all_var_elim_asm_tac);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (spec_nth_asm_tac 1 ⌜z'⌝);
(* *** Goal "4.2.2.2.2" *** *)
a (strip_tac THEN ∃_tac ⌜InR x⌝ THEN asm_rewrite_tac[]);
a (REPEAT strip_tac THEN_TRY all_var_elim_asm_tac);
(* *** Goal "4.2.2.2.2.1" *** *)
a (∃_tac ⌜x⌝);
a (asm_rewrite_tac []);
(* *** Goal "4.2.2.2.2.2" *** *)
a (∃_tac ⌜z'⌝);
a (asm_rewrite_tac []);
val catm_eq_lemma = save_pop_thm "catm_eq_lemma";
=TEX
}%ignore

\subsubsection{Predication}

Now we can define predication.
We do this in terms of Grice's $izz$ and $hazz$.

=SML
declare_infix (300, "izz");
declare_infix (300, "hazz");
=TEX

ⓈHOLCONST
│ $⦏izz⦎ : CATM → CATM → BOOL
├──────
│ ∀A B⦁ A izz B ⇔ Cat A = Cat B ∧ CatSet A ⊆ CatSet B
■

ⓈHOLCONST
│ $⦏hazz⦎ : CATM → CATM → BOOL
├──────
│ ∀A B⦁ A hazz B ⇔ Cat A = CatSubs ∧ ¬ Cat B = CatSubs
│	∧ ∃a⦁ a ∈ AttrSet B ∧ ∀s⦁ s ∈ IndvSet A ⇒ a s
■

That was reasonably neat, but the definition of $izz$ isn't terribly convenient for proving things.
Lets have some $izz$ lemmas:

=GFT
izz_lemma1 =
    ⊢ ∀ A B⦁ Cat A = CatSubs ⇒ (A izz B ⇔ Cat B = CatSubs ∧ IndvSet A ⊆ IndvSet B)

izz_lemma2 =
    ⊢ ∀ A B⦁ Cat B = CatSubs ⇒ (A izz B ⇔ Cat A = CatSubs ∧ IndvSet A ⊆ IndvSet B)

izz_lemma3 =
    ⊢ ∀ A B⦁ ¬ Cat A = CatSubs ⇒ (A izz B ⇔ Cat B = Cat A ∧ AttrSet A ⊆ AttrSet B)

izz_lemma4 =
    ⊢ ∀ A B⦁ ¬ Cat B = CatSubs ⇒ (A izz B ⇔ Cat B = Cat A ∧ AttrSet A ⊆ AttrSet B)
=TEX

\ignore{
=SML
set_goal([], ⌜∀A B⦁ Cat A = CatSubs ⇒ (A izz B ⇔ Cat B = CatSubs ∧ IndvSet A ⊆ IndvSet B)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜$izz⌝, get_spec ⌜CatSet⌝]); 
a (strip_tac THEN_TRY asm_rewrite_tac[] THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[sets_ext_clauses] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜(InL x):ISUB + (ISUB → BOOL)⌝);
(* *** Goal "1.1" *** *)
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "1.2" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[sets_ext_clauses] THEN REPEAT strip_tac);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
a (all_asm_fc_tac[]);
val izz_lemma1 = save_pop_thm "izz_lemma1";

set_goal([], ⌜∀A B⦁ Cat B = CatSubs ⇒ (A izz B ⇔ Cat A = CatSubs ∧ IndvSet A ⊆ IndvSet B)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜$izz⌝, get_spec ⌜CatSet⌝]); 
a (strip_tac THEN_TRY asm_rewrite_tac[] THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[sets_ext_clauses] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜(InL x):ISUB + (ISUB → BOOL)⌝);
(* *** Goal "1.1" *** *)
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "1.2" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[sets_ext_clauses] THEN REPEAT strip_tac);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
a (all_asm_fc_tac[]);
val izz_lemma2 = save_pop_thm "izz_lemma2";

set_goal([], ⌜∀A B⦁ ¬ Cat A = CatSubs ⇒ (A izz B ⇔ Cat B = Cat A ∧ AttrSet A ⊆ AttrSet B)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜$izz⌝, get_spec ⌜CatSet⌝]); 
a (strip_tac THEN_TRY asm_rewrite_tac[] THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[sets_ext_clauses]);
a (DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[] THEN strip_tac THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜(InR x):ISUB + (ISUB → BOOL)⌝);
(* *** Goal "1.1" *** *)
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "1.2" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[sets_ext_clauses] THEN REPEAT strip_tac);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
a (all_asm_fc_tac[]);
val izz_lemma3 = save_pop_thm "izz_lemma3";

set_goal([], ⌜∀A B⦁ ¬ Cat B = CatSubs ⇒ (A izz B ⇔ Cat B = Cat A ∧ AttrSet A ⊆ AttrSet B)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[get_spec ⌜$izz⌝, get_spec ⌜CatSet⌝]); 
a (strip_tac THEN_TRY asm_rewrite_tac[] THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[sets_ext_clauses] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜(InR x):ISUB + (ISUB → BOOL)⌝);
(* *** Goal "1.1" *** *)
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "1.2" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac 
	THEN SYM_ASMS_T rewrite_tac
	THEN asm_rewrite_tac[sets_ext_clauses]
	THEN REPEAT strip_tac);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
a (all_asm_fc_tac[]);
val izz_lemma4 = save_pop_thm "izz_lemma4";
=TEX
}%ignore

\subsubsection{The Principles in HOL}

Here are the HOL versions of the Code ``Principles''.

The following is a bit of program in a programming language called SML, which stands for ``Standard Meta Language''!
It names various terms in HOL, the name on the left `c01' (short for `conjecture 1'), the term on the right quoted in ``Quine corners''.
\footnote{``Quine corners'' are a notation originally used by Quine for Godel numbers, i.e., in Quine's use `⌜43⌝' is a friendly way of writing doen the Godel number of the numeral `43'.
In ProofPower HOL these corners are used to refer to HOL terms in the metalanguage SML.
In HOL, a formula is a term of type ⓣBOOL⌝ (the opening ⓣ is used when quoting a type rather than a term).}

=SML
val c01 = ⌜∀A⦁ A izz A⌝;
val c02 = ⌜∀A B C⦁ A izz B ∧ B izz C ⇒ A izz C⌝;
val c03 = ⌜∀A B⦁ A hazz B ⇒ ¬ A izz B⌝;
val c04 = ⌜∀A B⦁ A hazz B ⇔ ∃C⦁ A hazz C ∧ C izz B⌝;
=TEX

One would expect this set of principles to be sufficient to characterise {\it izz} and {\it hazz} (i.e. sufficient to derive any other true facts about them) but this seems doubtful.

Here are some supplementary conjectures.

=SML
val c01b = ⌜∀A⦁ ¬ A hazz A⌝;
val c03b = ⌜∀A B⦁ A izz B ⇒ ¬ A hazz B⌝;
val c03c = ⌜∀A B⦁ A hazz B ⇒ ¬ A = B⌝;
val c04a = ⌜∀A B C⦁ A hazz B ∧ B izz C ⇒ A hazz C⌝;
val c04b = ⌜∀A B C⦁ A izz B ∧ B hazz C ⇒ A hazz C⌝;
=TEX

Of the supplementaries:

\begin{itemize}
\item c01b is derivable from c03 and c01.
\item c03b is the contrapositive of c03.
\item c03c would be derivable for Code once he has defined equality, it is provable for us now because we have a primitive equality.
\item c04a is a preferable formulation of the right-left implication in c04, and we have used it to prove c04.
\item c04b is an obvious further transitivity-like property, which does not look like it's provable from the stipulated principles.
\end{itemize}

\ignore{
=SML
set_goal([], c01);
a (REPEAT ∀_tac THEN_TRY rewrite_tac [get_spec ⌜$izz⌝]);
val l01 = save_pop_thm "l01";

set_goal([], c01b);
a (REPEAT ∀_tac THEN_TRY rewrite_tac [get_spec ⌜$hazz⌝] THEN contr_tac);
val l01b = save_pop_thm "l01b";

set_goal([], c02);
a (REPEAT ∀_tac THEN_TRY rewrite_tac [get_spec ⌜$izz⌝]
	THEN REPEAT strip_tac
	THEN_TRY asm_rewrite_tac[]
	THEN all_asm_fc_tac[⊆_trans_thm]);
val l02 = save_pop_thm "l02";

set_goal([], c03);
a (REPEAT ∀_tac THEN_TRY rewrite_tac [get_spec ⌜$izz⌝, get_spec ⌜$hazz⌝] THEN contr_tac);
a (DROP_NTH_ASM_T 5 ante_tac
	THEN DROP_NTH_ASM_T 5 ante_tac
	THEN asm_rewrite_tac[]);
val l03 = save_pop_thm "l03";

set_goal([], c03b);
a (REPEAT ∀_tac THEN_TRY rewrite_tac [get_spec ⌜$izz⌝, get_spec ⌜$hazz⌝] THEN REPEAT strip_tac);
a (asm_rewrite_tac[]);
val l03b = save_pop_thm "l03b";

set_goal([], c03c);
a (REPEAT ∀_tac THEN_TRY rewrite_tac [get_spec ⌜$izz⌝, get_spec ⌜$hazz⌝] THEN contr_tac);
a (all_var_elim_asm_tac);
val l03c = save_pop_thm "l03c";

set_goal([], c04a);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$hazz⌝, get_spec ⌜CatSet⌝]
	THEN contr_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [izz_lemma2]);
(* *** Goal "2" *** *)
a (all_asm_fc_tac[]);
a (all_fc_tac [list_∀_elim [⌜B⌝] izz_lemma3]);
a (POP_ASM_T ante_tac THEN rewrite_tac [sets_ext_clauses]
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
a (∃_tac ⌜a⌝ THEN contr_tac);
val l04a = save_pop_thm "l04a";

set_goal([], c04);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜B⌝ THEN asm_rewrite_tac[l01]);
(* *** Goal "2" *** *)
a (all_fc_tac [list_∀_elim [⌜A⌝, ⌜C⌝] l04a]);
val l04 = save_pop_thm "l04";

set_goal([], c04b);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$hazz⌝, get_spec ⌜CatSet⌝]
	THEN contr_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [izz_lemma2]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 1 ⌜a⌝);
a (FC_T (MAP_EVERY ante_tac) [get_spec ⌜$izz⌝]);
a (strip_tac THEN asm_rewrite_tac [get_spec ⌜CatSet⌝, sets_ext_clauses]
	THEN strip_tac);
a (∃_tac ⌜InL s⌝ THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜s⌝ THEN REPEAT strip_tac);
(* *** Goal "2.2" *** *)
a (contr_tac THEN asm_fc_tac[]);
a (all_var_elim_asm_tac);
val l04b = save_pop_thm "l04b";
=TEX
}%ignore

=GFT Proven Theorems
l01	= ⊢ ∀ A⦁ A izz A
l01b 	= ⊢ ∀ A⦁ ¬ A hazz A
l02	= ⊢ ∀ A B C⦁ A izz B ∧ B izz C ⇒ A izz C
l03	= ⊢ ∀ A B⦁ A hazz B ⇒ ¬ A izz B
l03b 	= ⊢ ∀ A B⦁ A izz B ⇒ ¬ A hazz B
l03c 	= ⊢ ∀ A B⦁ A hazz B ⇒ ¬ A = B
l04a	= ⊢ ∀ A B C⦁ A hazz B ∧ B izz C ⇒ A hazz C
l04	= ⊢ ∀ A B⦁ A hazz B ⇔ (∃ C⦁ A hazz C ∧ C izz B) 
l04b 	= ⊢ ∀ A B C⦁ A izz B ∧ B hazz C ⇒ A hazz C
=TEX

\subsection{Total Definitions}

=GFT Code/Speranza
[(B) Total Definitions]

{6. (A hazz B & A is a particular) -> there is a C such that (C =/= A) & (A izz B).}

[D1] 7. A is predicable of B iff ((B izz A) ∨ (B hazz Something that izz A).
[D2] 8. A is essentially predicable [L-predicable] of B iff B izz A.
[D3] 9. A is accidentally predicable [H-predicable] of B iff B hazz something that izz A.
[D4] 10. A = B iff A izz B & B izz A.
[D5] 11. A is an individual iff (Nec)(For all B) B izz A -> A izz B
[D6] 12. A is a particular iff (Nec)(For all B) A is predicable of B -> (A izz B & B izz A)
[D7] 13. A is a universal iff
		(Poss) (There is a B) A is predicable of A[B] & -(A izz B & B izz A)
=TEX

There is a certain amount of duplication of terminology here, since essential and accidental predication seem to be just $izz$ and $hazz$ backwards.
I'm not so happy with the ``ables'' here, for what is clearly meant is ``truly predicable'', which is not quite the same thing.
Better names would be simply ``is\_essentially'' and ``is\_accidentally'', lacking the ambiguity of ``able'' (but then they would have to be the other way round, exactly the same as $izz$ and $hazz$).

Anyway here are the definitions (keeping the names (more or less) as they were for the present):

=SML
declare_infix (300, "predicable_of");
declare_infix (300, "essentially_predicable_of");
declare_infix (300, "accidentally_predicable_of");
=TEX

ⓈHOLCONST
│ $⦏essentially_predicable_of⦎ : CATM → CATM → BOOL
├──────
│ ∀A B⦁ A essentially_predicable_of B ⇔ B izz A
■

ⓈHOLCONST
│ $⦏accidentally_predicable_of⦎ : CATM → CATM → BOOL
├──────
│ ∀A B⦁ A accidentally_predicable_of B ⇔ B hazz A
■

Aristotelian predication is then:

ⓈHOLCONST
│ $⦏predicable_of⦎ : CATM → CATM → BOOL
├──────
│ ∀A B⦁ A predicable_of B ⇔ A essentially_predicable_of B ∨ A accidentally_predicable_of B
■

Because we have not precluded empty predicates Code's definition will not do, and we have to make ``individual'' primitive, insisting on an individual being a singleton.

ⓈHOLCONST
│ ⦏individual⦎ : CATM → BOOL
├──────
│ ∀A⦁ individual A ⇔ ∃a⦁ CatSet A = {a}
■

According to Code's definition a particular is a substantial individual, we also have to use a more direct statemant of that principle.

ⓈHOLCONST
│ ⦏particular⦎ : CATM → BOOL
├──────
│ ∀A⦁ particular A ⇔ individual A ∧ Cat A = CatSubs
■

Again we have a problem with Code's definition and therefore define a universal as a non-particular.

ⓈHOLCONST
│ ⦏universal⦎ : CATM → BOOL
├──────
│ ∀A⦁ universal A ⇔ ¬ particular A
■

=SML
val c06 = ⌜∀A B⦁ A hazz B ∧ particular A ⇒ ∃C⦁ C ≠ A ∧ A izz B⌝; 
val c06n = ⌜¬ ∀A B⦁ A hazz B ∧ particular A ⇒ ∃C⦁ C ≠ A ∧ A izz B⌝; 
val c07 = ⌜∀A B⦁ A predicable_of B ⇔ (B izz A) ∨ ∃C⦁ B hazz C ∧ C izz A⌝;
val c08 = ⌜∀A⦁ A essentially_predicable_of B ⇔ B izz A⌝;
val c09 = ⌜∀A⦁ A accidentally_predicable_of B ⇔ ∃C⦁ B hazz C ∧ C izz A⌝;
val c10 = ⌜∀A B⦁ A = B ⇔ A izz B ∧ B izz A⌝;
val c11 = ⌜∀A B⦁ individual A ⇔ □(∀B⦁ B izz A ⇒ A izz B)⌝;
val c12 = ⌜∀A⦁ particular A ⇔ □(∀B⦁ A predicable_of B ⇒ A izz B ∧ B izz A)⌝;
val c13 = ⌜∀A⦁ universal A ⇔ ♢(∃B⦁ (A predicable_of B ∧ ¬(A izz B ∧ B izz A)))⌝;
=TEX

\ignore{
=SML
set_goal([], c06n);
a (strip_tac);
a (∃_tac ⌜InL {εi:ISUB⦁T}⌝);
a (strip_tac);
a (∃_tac ⌜InR ((εc:ACAT⦁T), {λi⦁T})⌝);
a (rewrite_tac[get_spec ⌜$hazz⌝, get_spec ⌜Cat⌝, get_spec ⌜CatSubs⌝,
	get_spec ⌜$izz⌝, get_spec ⌜AttrSet⌝, get_spec ⌜particular⌝, get_spec ⌜individual⌝,
	get_spec ⌜CatSet⌝, get_spec ⌜IndvSet⌝]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜λ i⦁ T⌝ THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜InL (ε i⦁ T)⌝ THEN rewrite_tac[sets_ext_clauses]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜ε i⦁ T⌝ THEN rewrite_tac[]);
val l06n = save_pop_thm "l06n";

set_goal([], c07);
a (REPEAT ∀_tac);
a (rewrite_tac [get_spec ⌜$predicable_of⌝, get_spec ⌜$essentially_predicable_of⌝,
		get_spec ⌜$accidentally_predicable_of⌝]);
a (rewrite_tac [list_∀_elim [⌜B⌝, ⌜A⌝] l04]);
val l07 = save_pop_thm "l07";

set_goal([], c08);
a (rewrite_tac [get_spec ⌜$essentially_predicable_of⌝]);
val l08 = save_pop_thm "l08";

set_goal([], c09);
a (REPEAT ∀_tac);
a (rewrite_tac [get_spec ⌜$accidentally_predicable_of⌝, list_∀_elim [⌜B⌝, ⌜A⌝] l04]);
val l09 = save_pop_thm "l09";

set_goal([], c10);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$izz⌝, catm_eq_lemma]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (all_fc_tac [pc_rule1 "hol1" prove_rule [] ⌜∀a b⦁ a ⊆ b ∧ b ⊆ a ⇒ a = b⌝]);
val l10 = save_pop_thm "l10";
=TEX
}%ignore

=GFT
l05 	= ⊢ ∀ x⦁ form x ⇒ universal x
l06n 	= ⊢ ¬ (∀ A B⦁ A hazz B ∧ particular A ⇒ (∃ C⦁ C ≠ A ∧ A izz B))
l07 	= ⊢ ∀ A B⦁ A predicable_of B ⇔ B izz A ∨ (∃ C⦁ B hazz C ∧ C izz A)
l08 	= ⊢ ∀ A⦁ A essentially_predicable_of B ⇔ B izz A
l09 	= ⊢ ∀ A⦁ A accidentally_predicable_of B ⇔ (∃ C⦁ B hazz C ∧ C izz A)
l10	= ⊢ ∀ A B⦁ A = B ⇔ A izz B ∧ B izz A
=TEX

c06 is false (see l06n), probably a typo.
However, I couldn't work out what was intended.

c11-13 are not provable in our model because of the existence of empty predicates (and the lack of modal operators).

\subsection{Partial Definitions}

=GFT Code/Speranza
[(C) Partial Definitions]

[D8] 14. If A is Some Thing [a this somewhat], A is an  individual.
[D9] 15. If A is a [(seperable) Platonic] Form,
		A is Some Thing [a this somewhat] and Universal.
=TEX

\ignore{
=SML
set_goal ([],⌜∃SomeThing⦁ ∀x⦁ SomeThing x ⇒ individual x⌝);
a (∃_tac ⌜individual⌝ THEN rewrite_tac[]);
save_cs_∃_thm(pop_thm());
=TEX
}%ignore

This is D8/c14.

ⓈHOLCONST
│ ⦏SomeThing⦎ : CATM → BOOL
├──────
│ ∀x⦁ SomeThing x ⇒ individual x
■

A form is a non-substantial individual.

\ignore{
=SML
set_goal ([],⌜∃form⦁ ∀x⦁ form x ⇒ SomeThing x ∧ universal x⌝);
a (∃_tac ⌜λx⦁ SomeThing x ∧ universal x⌝ THEN rewrite_tac[]);
save_cs_∃_thm(pop_thm());
=TEX
}%ignore

This is D9/c15

ⓈHOLCONST
│ ⦏form⦎ : CATM → BOOL
├──────
│ ∀x⦁ form x ⇒ SomeThing x ∧ universal x
■

\subsection{Ontological Theorems}

=GFT Code/Speranza
[(D) Ontological Theorems]

[T1] 16. A is predicable of B iff (B izz A) v (B hazz Some Thing that Izz A).
[T2] 17. A is essentially predicable [L-predicable] of A.
[T3] 18. A is accidentally predicable [H-predicable] of B ->  A =/= B
[T4] A is not accidentally predicable [H-predicable] of A
{19. - (A is accidentally predicable of B) -> A =/= B.}
[T5] 20. A is a particular -> A is an individual.
	[Note that the converse of T5 is not a theorem]
[T6] 21. A is a particular -> No Thing [nothing] that is Not Identical with A izz A.
[T7] 22. No Thing is both particular & a [(separable) Platonic] Form.
[T8] 23. A is a (seperable Platonic) Form -> nothing that is not identical with A izz A.
[T9] 24. A is a particular -> there is no (seperable Platonic) form B such that A izz B.
[T10] 25. A is a (seperable Platonic) form
		-> ((A is predicable of B & A =/= B) -> B hazz A)
[T11] 26. (A is a (seperable Platonic) form & B is a particular)
		-> (A is predicable of B iff B hazz A).
=TEX

=SML
val c05 = ⌜∀x⦁ universal x ⇒ form x⌝;
val c05b = ⌜∀x⦁ form x ⇒ universal x⌝;
val c16 = ⌜∀A B⦁ A predicable_of B ⇔ (B izz A) ∨ ∃C⦁ (B hazz C ∧ C izz A)⌝;
val c17 = ⌜∀A⦁ A essentially_predicable_of A⌝;
val c18 = ⌜∀A⦁ A accidentally_predicable_of B ⇒ A ≠ B⌝;
val c19 = ⌜∀A⦁ ¬ A accidentally_predicable_of A⌝;
val c20 = ⌜∀A⦁ particular A ⇒ individual A⌝;
val c21 = ⌜∀A⦁ particular A ⇒ ¬ ∃C⦁ C ≠ A ∧ C izz A⌝;
val c22 = ⌜¬ ∃A⦁ particular A ∧ form A⌝;
val c23 = ⌜∀A⦁ form A ⇒ ¬ ∃C⦁ C ≠ A ∧ C izz A⌝;
val c23b = ⌜∀A⦁ form A ⇒ individual A⌝;
val c24a = ⌜∀ A B⦁ particular A ∧ individual B ∧ A izz B ⇒ particular B⌝;
val c24 = ⌜∀A⦁ particular A ⇒ ¬ ∃B⦁ form B ∧ A izz B⌝;
val c24b = ⌜∀A⦁ particular A ⇒ ¬ form A⌝;
val c25 = ⌜∀A B⦁ form A ⇒ A predicable_of B ∧ A ≠ B ⇒ B hazz A⌝;
val c26 = ⌜∀A B⦁ form A ∧ particular B ⇒ (A predicable_of B ⇔ B hazz A)⌝;
=TEX

\ignore{
=SML
=IGN
set_goal([], c06n);
a (strip_tac);
a (∃_tac ⌜InL{εx:ISUB⦁T}:CATM⌝ THEN strip_tac);
a (∃_tac ⌜InR((εx:ACAT⦁T), {λx:ISUB⦁T}):CATM⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac (map get_spec [⌜$hazz⌝, ⌜Cat⌝, ⌜CatSubs⌝]));
a (∃_tac ⌜λx:ISUB⦁T⌝);
a (rewrite_tac (map get_spec [⌜AttrSet⌝]));
(* *** Goal "2" *** *)
a (rewrite_tac (map get_spec [⌜particular⌝, ⌜individual⌝]) THEN strip_tac);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜InL(ε x:ISUB⦁ T):ISUB + (ISUB → BOOL)⌝);
a (rewrite_tac [get_spec ⌜CatSet⌝, get_spec ⌜Cat⌝, get_spec ⌜IndvSet⌝, sets_ext_clauses]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜ε x:ISUB⦁ T⌝);
a (rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (rewrite_tac [get_spec ⌜Cat⌝]);
(* *** Goal "3" *** *)
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac[get_spec ⌜$izz⌝, get_spec ⌜Cat⌝, get_spec ⌜CatSubs⌝]);
val l06n = save_pop_thm "l06n";
=SML

set_goal([], c16);
a (rewrite_tac [map_eq_sym_rule l04]);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$predicable_of⌝,
	get_spec ⌜$essentially_predicable_of⌝, get_spec ⌜$accidentally_predicable_of⌝]);
val l16 = save_pop_thm "l16";

set_goal([], c17);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$essentially_predicable_of⌝, l01]);
val l17 = save_pop_thm "l17";

set_goal([], c18);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$accidentally_predicable_of⌝, get_spec ⌜$≠⌝]);
a (strip_tac THEN fc_tac [l03c]);
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
val l18 = save_pop_thm "l18";

set_goal([], c19);
a (rewrite_tac [get_spec ⌜$accidentally_predicable_of⌝, l01b]);
val l19 = save_pop_thm "l19";

set_goal([], c20);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$particular⌝]
	THEN contr_tac);
val l20 = save_pop_thm "l20";

=IGN
set_goal([], c21);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$particular⌝]
	THEN contr_tac);
val l21 = save_pop_thm "l21";
=SML

set_goal([], c22);
a (contr_tac);
a (fc_tac [get_spec ⌜form⌝]);
a (fc_tac [get_spec ⌜universal⌝]);
val l22 = save_pop_thm "l22";

set_goal([], c23b);
a (REPEAT strip_tac THEN fc_tac [get_spec ⌜form⌝]);
a (fc_tac [get_spec ⌜SomeThing⌝, get_spec ⌜universal⌝]);
val l23b = save_pop_thm "l23b";

set_goal([], c24a);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜particular⌝, get_spec ⌜individual⌝,
		get_spec ⌜$izz⌝]
	THEN strip_tac THEN strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜a'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (SYM_ASMS_T rewrite_tac);
val l24a = save_pop_thm "l24a";

set_goal([], c24);
a (contr_tac THEN fc_tac [get_spec ⌜form⌝]);
a (fc_tac [get_spec ⌜SomeThing⌝, get_spec ⌜universal⌝, get_spec ⌜particular⌝, get_spec ⌜individual⌝]);
a (all_fc_tac [l24a]);
val l24 = save_pop_thm "l24";

=IGN
set_goal([], c25b);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$predicable_of⌝, get_spec ⌜$accidentally_predicable_of⌝,
	get_spec ⌜$essentially_predicable_of⌝, get_spec ⌜$izz⌝] THEN strip_tac
	THEN fc_tac [get_spec ⌜form⌝]);
a (fc_tac [get_spec ⌜SomeThing⌝, get_spec ⌜universal⌝]);
a (DROP_ASM_T ⌜¬ particular A⌝ (strip_asm_tac o (rewrite_rule [get_spec ⌜particular⌝])));
a (REPEAT strip_tac);
a (rewrite_tac[get_spec ⌜$hazz⌝] );

a (rewrite_tac [get_spec ⌜$predicable_of⌝, get_spec ⌜$accidentally_predicable_of⌝, get_spec ⌜$essentially_predicable_of⌝,
	get_spec ⌜$izz⌝]
	THEN contr_tac);
a (DROP_ASM_T ⌜Cat B = CatSubs⌝ ante_tac);
a (asm_rewrite_tac[]);
val l25 = save_pop_thm "l25";
=SML

set_goal([], c26);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜particular⌝] THEN strip_tac
	THEN fc_tac [get_spec ⌜form⌝, get_spec ⌜SomeThing⌝]);
a (fc_tac [get_spec ⌜SomeThing⌝, get_spec ⌜universal⌝]);
a (DROP_ASM_T ⌜¬ particular A⌝ (strip_asm_tac o (rewrite_rule [get_spec ⌜particular⌝])));
a (rewrite_tac [get_spec ⌜$predicable_of⌝, get_spec ⌜$accidentally_predicable_of⌝, get_spec ⌜$essentially_predicable_of⌝,
	get_spec ⌜$izz⌝]
	THEN contr_tac);
a (DROP_ASM_T ⌜Cat B = CatSubs⌝ ante_tac);
a (asm_rewrite_tac[]);
val l26 = save_pop_thm "l26";
=TEX
}%ignore

These are the ones I have proved.

=GFT
l16 	= ⊢ ∀ A B⦁ A predicable_of B ⇔ B izz A ∨ (∃ C⦁ B hazz C ∧ C izz A)
l17 	= ⊢ ∀ A⦁ A essentially_predicable_of A
l19 	= ⊢ ∀ A⦁ ¬ A accidentally_predicable_of A
l20 	= ⊢ ∀ A⦁ individual A ⇒ particular A
l22 	= ⊢ ¬ (∃ A⦁ particular A ∧ form A)
l23b 	= ⊢ ∀ A⦁ form A ⇒ individual A
l24a 	= ⊢ ∀ A B⦁ particular A ∧ individual B ∧ A izz B ⇒ particular B
l24 	= ⊢ ∀ A⦁ particular A ⇒ ¬ (∃ B⦁ form B ∧ A izz B)
l26 	= ⊢ ∀ A B⦁ form A ∧ particular B ⇒ (A predicable_of B ⇔ B hazz A)
=TEX

T6/c21, T8/c23, T10/c25 are all unprovable because of the existence of empty predicates.

\subsection{Platonic Principles and Theorems}

This section is a bit of a mess.
I now see that the reason for this is that Code is now presenting a different theory here, which is Aristotle's conception of Plato's metaphysics.
This explains why these principles at least augment (and possibly contradict) concepts which have already been defined.
In our method, which involves, for the sake of ensuring consistency, the use of only conservative extensions, this cannot be done simply by adding new principles.
We have to develop two systems in separate theories in which the differences of conception between Aristotle and Aristotle's conception of Plato are investigated in distinct contexts (though we could place in a single parent theory the elements which are common to both).

This will be considered later.


=GFT Code/Speranza
[(E) Platonic Principle]

[PP1] 5. Each universal is a (seperable Platonic) form.
[PP2] 27. (A is particular & B is a universal & predicable of A)
	-> there is a C such that (A =/= C  & C is essentially predicable of A)
=TEX

=SML
val c05 = ⌜∀x⦁ universal x ⇒ form x⌝;
val c05b = ⌜∀x⦁ form x ⇒ universal x⌝;
val c27 = ⌜∀A B⦁ particular A ∧ universal B ∧ B predicable_of A
		⇒ ∃C⦁ (A ≠ C ∧ C essentially_predicable_of A)⌝;
=TEX

\ignore{
=SML
set_goal([], c05b);
a (REPEAT strip_tac THEN fc_tac [get_spec ⌜form⌝]);
val l05b = save_pop_thm "l05b";

=IGN
set_goal([], c27);
a (REPEAT strip_tac THEN fc_tac [get_spec ⌜form⌝]);
val l05b = save_pop_thm "l05b";
=TEX
}%ignore

c05 is not provable, its converse c05b is.
c27 is not provable, since it would require that there be more than one particular and we have no reason to believe that to be the case.

=GFT
l05b 	= ⊢ ∀ x⦁ form x ⇒ universal x
=TEX

=GFT Code/Speranza
[(F) Platonic Theorem]

{28. If there are particulars, of which universals are predicable,
	not every universal is Some Thing.}
[PT1] 29. Each universal is Some Thing [a this somewhat].
[PT2] 30. If A is a particular, there is no B such that
	(A =/= B &  B is essentially predicable of A).
[PT3] 31. (A is predicable of B & A =/= B) -> A is accidentally predicable of B.
=TEX

=SML
val c28 = ⌜(∃P⦁ particular P ∧ ∃U⦁ universal U ∧ U predicable_of P)
		⇒ ¬ (∀U⦁ universal U ⇒ thing U)⌝;
val c29 = ⌜∀U⦁ universal U ⇒ thing U⌝;
val c30 = ⌜∀A⦁ particular A ⇒ ¬ ∃B⦁ (A ≠ B ∧ B essentially_predicable_of A)⌝;
val c31 = ⌜∀A B⦁ A predicable_of B ∧ A ≠ B ⇒ A accidentally_predicable_of B⌝;
=TEX

\ignore{
=SML

=IGN
set_goal([], c06n);
a (strip_tac);
a (∃_tac ⌜InL{εx:ISUB⦁T}:CATM⌝ THEN strip_tac);
a (∃_tac ⌜InR((εx:ACAT⦁T), {λx:ISUB⦁T}):CATM⌝ THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac (map get_spec [⌜$hazz⌝, ⌜Cat⌝, ⌜CatSubs⌝]));
a (∃_tac ⌜λx:ISUB⦁T⌝);
a (rewrite_tac (map get_spec [⌜AttrSet⌝]));
(* *** Goal "2" *** *)
a (rewrite_tac (map get_spec [⌜particular⌝, ⌜individual⌝]) THEN strip_tac);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜InL(ε x:ISUB⦁ T):ISUB + (ISUB → BOOL)⌝);
a (rewrite_tac [get_spec ⌜CatSet⌝, get_spec ⌜Cat⌝, get_spec ⌜IndvSet⌝, sets_ext_clauses]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜ε x:ISUB⦁ T⌝);
a (rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (rewrite_tac [get_spec ⌜Cat⌝]);
(* *** Goal "3" *** *)
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac[get_spec ⌜$izz⌝, get_spec ⌜Cat⌝, get_spec ⌜CatSubs⌝]);
val l06n = save_pop_thm "l06n";
=TEX
}%ignore

These are the ones I have proved.

=GFT
l06n =	⊢ ¬ (∀ A B⦁ A hazz B ∧ particular A ⇒ (∃ C⦁ C ≠ A ∧ A izz B))
=TEX

\subsection{Some Comments on The Conjectures}

The main problem with the conjectures is that as a group they are inconsistent.
Consequently, one cannot find definitions which are consistent with all the conjectures.

So first I will expose some of the most obvious contradications which flow from the conjectures.

\begin{enumerate}
\item From 5 and 15 we conclude that form and universal are coextensive.
I think it may be that this is part of the Platonic view but not of the Aristotelian one.

\end{enumerate}

Here are some observations on specific conjectures (now out of date).

\begin{description}

\item[c01]
Note here that this is quantified over everything, and hence over individuals, whereas Aristotle describes individuals as thing of which one may predicate, but which are not themselves predicable.
Perhaps this inderdiction applies to $hazz$ but not to $izz$, to accidental but not essential predication.
(We should add the rule ⌜¬ A hazz A⌝ which is easy to prove.)
I don't know any more detail about Aristotle's attitude towards predication by individuals.
If one cannot, where do we stand when we do, as in ``Socrates is Socrates'' and ``Socrates is Aristotle''.
Anyway, if these were to have a truth value (which surely they do) then the truth value will be as in this rule.

\item[c02]
Behind the scenes this is transitivity of set inclusion.

\item[c03]
This is because {\it izz} is intracategorial and {\it hazz} is intercategorial.
An obvious but useful corrolary is that they are not equal (c03b).

\item[c04]
This, and most of the other theorems involving existential quantification, is rather odd.
Its proof depends on the conjecture $c04a$, which we have proven, and which involves no existential quantification, but its content is not significantly greater than that rule.
From right to left $l04$ is $l04b$ (you just pull out the existential and it turns into a universal).
From left to right $l04$ is trivial, since $B$ serves as a witness for the existential.

Ideally we would be working with claims which are expressible syllogistically, i.e. without benefit of quantifiers.
We can make an exception for universals on the left, since these are interconvertible with the conjecture with free variables instead which we can think of as schemata.
Where an existential quantifier appears in a negative context it will turn universal if pulled out to the top level and can therefore be dispensed with.
Elsewhere its worth asking whether the content is significant (including, as here, one half of the content implicit in putting an existential under an equivalence).

$co4b$ is an obvious similar result to $c04a$.

\item[c05]
According to my definition this is the wrong way round.

\item[c06]
As it stands this is provably false since we have $⌜A hazz B⌝$ on the left, which entails that $A$ and $B$ are not of the same category, and $⌜A izz B⌝$ in the right, which entails that they are of the same category.

\item[c07]
This, at the expense of using an existential, nevertheless tells us nothing that is not immediate from the definitions.

\item[c08]
Is just our definition.

\item[c09]
This turns into $c04$ (apart from the variable names) once you expand the definition of {\it accidentally\_predicable\_of}.

\item[c10]
Behind the scenes, {\it izz} is set inclusion, so this is obvious.

\item[c11-13]
These contain modal operators which cannot be defined using this model.

\item[c14-c15]
I've not worked out what a ``thing'' is.
Not even sure that I should have rendered Speranza's version using that term.
However, I do think I know that {\it particular} and {\it universal} are opposites (contradictories), and hence I could conclude from these two conjectures that there can be no {\it forms} since they entail that a form is both individual and universal.
Sounds like I have the wrong end of some stick or other.

\item[c16]
I don't know enough about ``thing''s to prove this one.

\item[c17]
This is $c01$ in other words.

\item[c18]
This is $c03b$ in other words.

\item[c19]

This is the contrapositive of the claim that {\it accidentally\_predicable\_of} is reflexive, which is false.
Would be true for {\it essentially\_predicable\_of}, but we already have that stated directly as c17.

\item[c20]
Immediate from my definitions.

\item[c21]
This turns out to be false under my definitions, because I have not excluded the possibility of an empty predicate.
However, one wonders why this should be excluded.

If I go over to a model adquate for modal operators then it will be easy to exclude this possibility.

\item[c21]
Fails for same reason as c20, though I could fix this by making the definition of {\it universal} insist on more than one member.

\item[c23]
I don't know why this should be true.
Any particular which partakes of a form contradicts it.

\item[c24]
This is not true in the present model, because we might have only one particular, and hence no non-trivial forms.

\item[c25-c26]
These two tell me that forms are not substance, but attributes, which contradicts c24 which tells us that there are subtantial forms (if particulars are substances). 

\item[c27]
I don't see why this should be true.

\item[c28-c29]
These two together entail that no universal is predicable of any particular.

\item[c30]
This says that nothing is essentially predicable of a particular except itself.

\item[c31]
This is a stronger version of c30 which says that, even if something isn't particular, nothing but itself is essentially predicable of it.

\end{description}

\section{The Organon}\label{ORGANON}

\href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/oi.htm}{The Organon} is a collection of 6 books by Aristotle which form the main part of his work on Logic.
The first of these is \href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o11i.htm}{the Categories} \cite{aristotleL325}, on which Aristotle's Metaphyics depends.
The Metaphysics, at least the parts involved in the Grice/Code analysis \cite{grice88,code88}, is concerned with predication, which is also central to the formal core of Aristotle's logic, the theory of the syllogism, presented in the \href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o31i.htm}{Prior Analytic, Book 1} \cite{aristotleL325}.

Aristotle's account of syllogistic logic covers modal reasoning.
In attempting to understand Aristotelian essentialism, one of the key problems is to establish the relationship between the two distinctions between necessary and contingent proposition, and between essential and accidental predication.

Though Code \cite{code88} does not conceive of himself as engaged in formalising Aristotle in a modern predicate logic, his presentation seems much closer to predicate logic than to syllogistic logic.
I would like to understand the metaphysics if possible in terms of the kind of logic which Aristotle had at his disposal.
To explore the extent to which this might be possible, some models of syllogistic logic might be helpful.

When we look at the syllogism with particular concern for the notion of predication involved, we find that the Grice's ``izz/hazz'' distinction (in Aristotle ``said of'' and ``in'') is not relevant.
In this respect predication is simpler in the syllogism, but instead we have an orthogonal distinction into four kinds of predication according to whether the subject is universal or particular, and whether the predication is affirmative or negative, over which are later added the modal operators.


The semantics of the syllogism remains a matter of controversy in some respects.
The majority of the syllogisms held to be valid by Aristotle would be valid if universal and particular propositions were translated as universal and existential quantification in a modern predicate logic.
Four of the syllogisms held to be valid by Aristotle would not be sound under such an interpretation.
These four are distinguished by having universal premises but a particular conclusion.
I propose to call these the \emph{universal-particular}\index{universal-particular} syllogisms, which I may abbreviate \emph{u-p}\index{u-p}.

There are three most common approaches to the u-p syllogisms:

\begin{enumerate}
\item Consider them to be fallacious (possibly admitting the implicature).
\item Consider Aristotle's formal logic to be concerned exclusively with non-empty terms.
\item Consider universal propositions to be, in effect, the conjunction of a universal and an existential quantification.
\end{enumerate}

However, it now seems that none of these are correct and that the approach closest to Aristotle's text may be to have existential import in assertions (whether universal or particular) and absent from denials.

\subsection{Models and Their Significance}

Three different methods of analysis are illustrated in a very simple way in application to the laws of direct inference and the assertoric (i.e. non-modal) syllogistic.

These consisting in interpreting or modelling \emph{aspects} of Aristotelian logic using modern languages and tools.
It is important to understand that the construction of an interpretation or a model says by itself nothing about Aristotelian logic until the author makes a claim about the relationship between the model and the thing modelled.
It is never the intention that a model should be in all respects similar to the original.

In producing these models I prepare the model first, with only a vague sense of what it might be good for, and then make certain comparisons, and describe the results.
Thus the first two interpretations, which may be called translations or reductions, serve only to reduce the question of truth or provability in Aristotelian logic to that of truth or provability in some other notation or deductive system.

This they do incompletely.
The first interpretation fails to demonstrate a subset of the syllogisms (those which I here refer to as u-p syllogisms).
Its purpose is therefore primarily to show that the most naive interpretations of Aristotle's language fail to validate his reasoning, and thereby to cast doubt on such interpretations.

The next set of models may also be understood in similar ways, but they can also be considered as attempts to capture the truth conditions of categorical assertions.
The evaluation of these models is based again in the first instance on the correspondence between truth and provability between the model and the original.
Only one of these models fails to show significant differences in these respects from Aristotle.
It is therefore only in respect of the last of the models that we are motivated to enquire closer into the fidelity of the truth-conditional semantics which they exhibit.

The claims made for the models are very limited, and the purposes of the models are:

\begin{itemize}
\item to exhibit certain methods and consider their merits
\item to provide a basis for formal reasoning using a modern proof tool in a manner consistent with Aristotle's logic
\item to provide a basis for an exploration of Aristotle's metaphyics using the same tools and methods
\end{itemize}

Three methods of modelling are used.
These methods may be described as:

\begin{itemize}
\item translation
\item shallow embedding
\item deep embedding
\end{itemize}

In a translation syntax is not preserved, the aristotelian assertions are translated into some other form altogether.

In an embedding of either depth, an attempt is made to preserve and work with the original syntax, though in practice there may be alterations to the syntax to enable the analysis to be undertaken using some preferred software for formal analysis.
In this document the software is {\Product}.

A series of mappings into HOL have been used to evaluate these possibilities:

\begin{enumerate}
\item a set theoretic interpretation (Section \ref{STI})
\item an interpretation in propositional logic (Section \ref{IP})
\item a naive predicate calculus interpretation (Section \ref{NIPC})
\item predicate calculus with no empty terms (Section \ref{PCNET})
\item existential import in universals (Section \ref{IEIU})
\item existential import in affirmations (Section \ref{IEIA})
\item reasoning about deep embeddings
\item modal syllogisms (by non-emptyness) (Section \ref{MODSYLL})
\end{enumerate}

Of these the first two are simplistic translations.
The categorical propositions are mapped to sentences in HOL which resemble set theory, or the predicate calculus and by this means is obtained a partial reduction of the decision problem for truth of syllogisms.

The next three are `shallow embeddings'.
This means that the established representation of categorical assertions in the AEIO form is retained as syntax, so no translation of syntax is involved.
These are given meaning by defining constants in HOL named `a', `e', `i', and `o' to capture the truth conditions of the four forms.
This involves in the first instance a choice of type for the term variables and then the definition of these forms as functions from two such values to the type BOOL.

The interpretation is then evaluated by proving the soundness of various laws and syllogisms represented syntactically much as they are in the relevant literature.

Of these three shallow embeddings, the first two are based upon Strawson \cite{strawson52}.
The third benefits from discussion on the \emph{phil-logic} mailing list, and in particular on advice on the interpretation of Aristotle from Drake O'Brien supported by textual references which convinced me that neither of the Strawsonian interpretations could be correct.%
\footnote{This seems to be the accepted interpretation among contemporary scholars, and was described bt Terence Parsons in his online ``Overview of Aristotle's Logic'' (no longer available).}
These two points are firstly that Aristotle cannot be construed as presuming non-emptyness of terms (or as committing an existential fallacy), and that existential import is associated with the quality of the proposition, attaching to affirmative but not to negative propositions.

To facilitate comparison between the different interpretations the following list of `features' will be checked.
These are the various rules which might or might not be valid.
My aim is to check which of these hold in each interpretation and then to summarise the results in a table.

\begin{itemize}
\item Laws of immediate inference.

These fall into the following categories:

\begin{itemize}
\item Simple conversion.
\item Conversions per accidens.
\item Obversion.
\item Contraposition and inversion.
\item The square of opposition.
\end{itemize}

\item The syllogisms.
\end{itemize}

The present treatment was based firstly on the wikipedia account of \href{http://en.wikipedia.org/wiki/Syllogism}{Aristotle's Logic}, secondly on Strawson \cite{strawson52} from whom I first obtained the syllogisms not in Aristotle and began incorporation of direct inference, and then from Spade\cite{spade2002} I obtained the names for the extra syllogisms and a fuller account of how the syllogisms can be derived which is not yet reflected in the following.
Using these sources I didn't get very close to the real Aristotle.
Drake O'Brien, in discussion on \emph{phil-logic} helped get be closer.

The main interest at present is the sequence of models which contributes to the formulation of an integrated model for the syllogism and the metaphysics in Section \ref{METAPHYSICSII}.

\subsection{Preliminaries}

\subsubsection{Generating the Syllogisms}\label{syllogisms}

This following presentation of the forms of syllogism is based primarily on \href{http://en.wikipedia.org/wiki/Syllogism}{the one at wikipedia}.

In the following several different interpretations of the syllogism are formalised as shallow semantic embeddings in HOL.
Part of the evaluation of these interpretations consists in demonstrating that certain syllogisms are sound relative to the particular versions of the semantics.
This is done by constructing a conjecture in HOL which will be true if the syllogism is sound, and then proving that the conjecture is true (i.e. proving the corresponding theorem).
This procedure does not amount to a proof of the soundness of the syllogisms relative to the semantics, but gives almost the same level of confidence.
A standard soundness proof would require a `deep embedding', which would involve formalisation of the syntax of the syllogism and of the semantics as a relation between the syntax and the models.
This would be considerably more arduous, and would not deliver comparably greater insights.

Before looking at alternative semantics for the syllogistic some machinery for generating syllogisms which will be used throughout is provided in this section.

Structurally a syllogism consists of two premises and a conclusion.
The premises and conclusion are propositions, each of which is built from two terms in one of four ways.
The different interpretations of the syllogism are obtained by chosing different types for the terms and different ways of constructing the propositions from the terms.
For some purposes distinct ways of combining the propositions to form the completed syllogism will be necessary.

The information determining a particular interpretation will therefore be certain values in the metalanguage:

\begin{itemize}
\item[mkAT] a function which converts a name to a term of that name (having type: $ⓜstring -> TERM⌝$)
\item[mkAP] a function which takes a propositional form and delivers a proposition constructor taking two terms and delivering a proposition (having type: $ⓜstring -> (TERM * TERM) -> TERM⌝$)
\item[mkAS] a function which takes a list of propositions (the premises) and a single proposition (the conclusion) and delivers a syllogism as a sequent goal (having type: $ⓜ(TERM list * TERM) -> GOAL⌝$)
\end{itemize}

A choice about the semantics will be encapsulated as a record having these three components.

=SML
type mapkit =
	{mkAT:string -> TERM,
	 mkAP:string -> (TERM * TERM) -> TERM,
	 mkAS:(TERM list * TERM) -> GOAL};
=TEX

There are four forms of predication which are normally presented as infix operators over terms using the vowels ``a'', ``e'', ``i'', ``o''.

These are to be construed as follows:

\begin{center}
\begin{tabular}[]{ | l | l |}
\hline
HOL term & Meaning\\
\hline
⌜A a B⌝ & All A are B\\
⌜A e B⌝ & All A are not B\\
⌜A i B⌝ & An A is B\\
⌜A o B⌝ & An A is not B\\
\hline
\end{tabular}
\end{center}

Though exactly what these mean remains controversial and is a principle point of variation in the interpretations presented here.

Syllogisms come in four figures, according to the configuration of variables in the premises:

\begin{quote}
\begin{itemize}
\item[Figure 1] M-P, S-M $⊢$ S-P
\item[Figure 2] P-M, S-M $⊢$ S-P
\item[Figure 3] M-P, M-S $⊢$ S-P
\item[Figure 4] P-M, M-S $⊢$ S-P
\end{itemize}
\end{quote}

Where S, P and M are the subject, predicate and middle term respectively. 

The following function generates a list of four quadruples of HOL variables which correspond to the four figures of syllogisms.
It is parameterised by the HOL type used for predicates to that it can be re-used when we change the representation type.

=SML
fun ⦏figureS⦎ mkt = 
	let val M = mkt "M"
	    and P = mkt "P"
	    and S = mkt "𝕊"
	in [(M,P,S,M), (P,M,S,M), (M,P,M,S), (P,M,M,S)]
	end;
=TEX

In most cases terms are mapped to variables of appropriate types for the chosen semantics.
The following function when given a type will return a term constructor mapping term names to variables of that type.

=SML
fun ⦏mkATvar⦎ tt s = mk_var(s,tt);
=TEX

For these cases the list of figures with the relevant terms is obtained by this function:

=SML
fun ⦏figurest⦎ tt = figureS (mkATvar tt);
=TEX

and the following function when instantiated to some type will give the nth figure with terms as variables of that type.
=SML
fun ⦏nthfig⦎ tt n = nth n (figurest tt);
=TEX

These four figures are then repeated for each combination of the four types of premise in each of the premises and the conclusion.
This gives $4 × 4 × 4 × 4 = 256$ possibilities, of which 19 were held to be valid by Aristotle, four of them u-p syllogisms.

The use of vowels for the predicators allows the valid cases to be named using names in which the vowels tell you the form of the syllogism (if you also know the figure).
The first vowel tells you the kind of syllogism in the first premise, the second vowel that in the second premise, and the third vowel that in the conclusion.

In the following table the names in square brackets are for u-p syllogisms.
The names followed by exclamation marks are ``subalternate mood'', they do not appear in aristotle but are valid in the models here for which the u-p syllogisms hold
\footnote{This I got from Spade \cite{spade2002}.}.

\begin{center}
\begin{tabular}[]{| l | l | l | l |}
\hline
Figure 1 &	Figure 2	&	Figure 3 &	Figure 4\\
\hline 
Barbara &	Cesare 	&	[Darapti] &	[Bramantip]\\
Celarent &	Camestres &	Disamis 	&	Camenes\\
Darii 	&	Festino 	&	Datisi 	&	Dimaris\\
Ferio 	&	Baroco 	&	[Felapton] &	[Fesapo]\\
Barbari!	&	Cesaro!  	&	Bocardo 	&	Fresison\\
Celaront!	&	Camestrop! 	&	Ferison 	&	Camenop! \\
\hline
\end{tabular}
\end{center}

A syllogism may be identified either by the name in the above table (for the valid syllogisms), or by the three vowels, and the figure.

The above table is captured by the following definitions in our metalanguage:

We now define a data structure from which the valid syllogisms can be generated.
With the model we are using only the 15 non-u-p syllogisms.
They are shown in the following data structure.

=SML
val ⦏syllogism_data1⦎ = 
	[("Barbara", 1),
	("Celarent", 1),
	("Darii", 1),
	("Ferio", 1),
	("Cesare", 2),
	("Camestres", 2),
	("Festino", 2),
	("Baroco", 2),
	("Disamis", 3),
	("Datisi", 3),
	("Bocardo", 3),
	("Ferison", 3),
	("Camenes", 4),
	("Dimaris", 4),
	("Fresison", 4)];
=IGN
map mk_syllp1 syllogism_data1;
=TEX

The rest of the table consists of ``universal-particular''\index{universal-particular} syllogisms, i.e. syllogisms with universal premises but a particular conclusion.

The following four u-p\index{u-p} syllogisms were held to be valid by Aristotle (the ones in square brackets in the table).

=SML
val ⦏syllogism_data2⦎ = 
	[("Darapti", 3),	
	("Felapton", 3),
	("Bramantip", 4),
	("Fesapo", 4)];
=TEX

The following five further syllogisms are also sound, though not noted as such by Aristotle (the ones followed by exclamation marks in the table).

=SML
val ⦏syllogism_data3⦎ = 
	[("Barbari", 1),
	("Celaront", 1),
	("Cesaro", 2),
	("Camestrop", 2),
	("Camenop", 4)];
=TEX

We now assume available the triple of constructors mentioned above and define a function which converts syllogism identification in the form of a string of three vowels and a number in the range 1-4 into a syllogism.
This is parameterised by a \emph{mapkit} so that we can use it to deliver several different interpretations of the syllogism.

=SML
fun ⦏vowels_from_string⦎ s = filter (fn x => x mem (explode "aeiou")) (explode s);

fun ⦏mkSyll⦎ (sk:mapkit) (s, n) = 
	let val [pa, pb, co] = vowels_from_string s
	    val (a,b,c,d) = nth (n-1) (figureS (#mkAT sk))
	    val pl = [#mkAP sk pa (a,b), #mkAP sk pb (c,d)]
	    val c = #mkAP sk co (#mkAT sk "𝕊", #mkAT sk "P")
	in #mkAS sk (pl, c)
	end;
=TEX

We can then map this operation over the a list of syllogism data as follows:

=SML
fun ⦏mkGoals⦎ sk = map (fn (s,n) => (s, mkSyll sk (s, n)));
=TEX

If we further supply a proof tactic and a labelling suffix then we can prove a whole list of goals and store the results in the current theory.

=SML
fun ⦏proveGoals⦎ tac suff = map 
	(fn (s,g) =>
		(s,
		 save_thm (s^suff, tac_proof (g, tac))
			handle _ => t_thm));
=TEX

=SML
fun ⦏proveSylls⦎ sk tac suff sd = proveGoals tac suff (mkGoals sk sd);
=TEX

The following functions take a string which is the name of a syllogism extract the vowels which occur in it and convert them into the corresponding predication operator to give a triple of operators.

=SML
fun ⦏op_from_char⦎ ot c = mk_const (if c = "o" then "u" else c, ot);

fun ⦏optrip_from_text⦎ ot s =
	let val [a, b, c] = (map (op_from_char ot) o vowels_from_string) s;
	in (a, b, c)
	end;
=TEX


\paragraph{A Common Special Case}

The most common pattern is that:

\begin{itemize}
\item Terms are mapped to variables of some type.
\item Propositions are formed using infix operators {\it a, e, i, o}.
\item Syllogisms are sequents, the premises in the assumptions.
\end{itemize}

The following constructs a mapkit for such cases when supplied with the type of the term variables, and the four proposition constructors.

=SML
fun ⦏mkSimpMapkit⦎ ty opl =
	let val mkcop = fn s => snd (find (combine (explode "aeio") opl) (fn (n,v) => n = s))
	in
		{mkAT = fn s => mk_var(s, ty),
		mkAP = fn s => fn (l,r) => mk_app(mk_app (mkcop s, l), r),
		mkAS = fn x => x}
	end;
=TEX

\subsubsection{The Square of Opposition}

\begin{table}[hb]
\begin{center}
\begin{tabular}{|c|c|c|}
\hline
A & contraries & E \\
\hline
subalternates & contradictories & subalternates \\
\hline
I & subcontraries & O \\
\hline
\end{tabular}
\caption{The square of Opposition 1}
\label{tab:soo1}
\end{center}
\end{table}

The relationships between corners of the square of opposition have the following names:

\begin{table}[hb]
\begin{center}
\begin{tabular}{l l}
contradictories & A and B are contradictories if $⌜A ⇔ ¬B⌝$\\
contraries & A and B are contraries if they are not both true.\\
subcontraries & A and B are sub-contraries if they are not both false.\\
subalternates & B is subalternate to A if A implies B\\
\end{tabular}
\caption{The square of Opposition 2}
\label{tab:soo2}
\end{center}
\end{table}

The full set of relationships exhibited by the square is:

\begin{table}[hb]
\begin{center}
\begin{tabular}{l l}
ao\_contrad & contradictories\\
ei\_contrad & contradictories\\
ae\_contrar & contraries\\
io\_subcont & subcontraries\\
ai\_subalt & subalternates\\
eo\_subalt & subalternates\\
\end{tabular}
\caption{The square of Opposition 3}
\label{tab:soo3}
\end{center}
\end{table}

The goal conclusions for theorems expressing compliance are (details of syntax will vary between interpretations):

=GFT SML
val ao_contrad = ⌜A a B ⇔ ¬ A o B⌝;
val ei_contrad = ⌜A e B ⇔ ¬ A i B⌝;
val ae_contrar = ⌜¬ (A a B ∧ A e B)⌝;
val io_subcont = ⌜A i B ∨ A o B⌝;
val ai_subalt = ⌜A a B ⇒ A i B⌝;
val eo_subalt = ⌜A e B ⇒ A o B⌝;
=TEX

This provides a compact way of comparing different interpretations of the assertoric forms.

The principal point of difference is in subalternation which fails when the quantifiers are interpreted in the modern sense and empty terms are admitted.
One remedy for this defect might be to add existential import to the universal quantifier, but this by itself would cause the contradictories to fail.
Another remedy is to add existential import to the universal and define the particular modes through the contradictories.

Peter Strawson enumerates 14 laws of immediate inference, not all of which seem to have been embraced by Aristotle.
The list nevertheless provides a good collection against which an interpretation of the propositions can be evaluated, along with the 24 syllogisms.

The following table shows the correspondence between the numbers used by Strawson, the names used here, and a fuller name.

\begin{table}[hb]
\begin{center}
\begin{tabular}{|l|l|l|}
\hline
i & e\_conv & conversion\\
\hline
ii & i\_conv & \\
\hline
iii & ai\_conv & \\
\hline
iv & eo\_conv & \\
\hline
v & ae\_obv & obversion\\
\hline
vi & ea\_obv & \\
\hline
vii & io\_obv & \\
\hline
viii & oi\_obv & \\
\hline
ix & ao\_contrad & contradiction\\
\hline
x & ei\_contrad & \\
\hline
xi & ae\_contrar & contrary\\
\hline
xii & io\_subcontrar & subcontrary\\
\hline
xiii & ai\_subalt & subalternate\\
\hline
xiv & eo\_subalt & \\
\hline
\end{tabular}
\end{center}
\caption{Laws of Immediate Inference}
\label{tab:laws}
\end{table}


\subsubsection{Are The Syllogisms Tautologous?}

This section is a kind of preliminary skirmish provoked by some discussions on \href{http://philo.at/cgi-bin/mailman/listinfo/phil-logic}{phil-logic} in which one or two specific questions are addressed.

The question which provoked this section was:

\begin{itemize}
\item Are the valid syllogisms tautologous?
\end{itemize}

This is complex because it depends on a view about the semantics of the syllogism and also upon what particular notion of tautology is in play.

Two related questions come from remarks by P.V.Spade.
P.V. Spade, in a thumbnail history of logic \cite{spade2002} remarks that some later peripatetics attempted to show that stoic propositional logic was simply the syllogism in other clothes, and others that the two are in some sense equivalent.

\begin{itemize}
\item Is there any sense in which the syllogism can be said to encompass Stoic propositional logic?
\item Is there any sense in which the syllogism might be seen to be equivalent to Stoic propositional logic?
\end{itemize}

I have no knowledge of Stoic propositional logic, and this section is therefore concerned with the relationship between the syllogism and modern propositional logic, which I presume is a superset (probably but not necessarily proper) of Stoic propositional logic.

I distinguish three notions of tautology (though this is not intended to be an exhaustive list) on which something can be said in this connection.

\begin{itemize}
\item[propositional] A valid sentence of the propositional calculus.
\item[first order] A valid sentence of first order logic.
\item[analytic] A sentence whose truth conditions assign truth to it in every situation or interpretation consistent with the meanings of the language in which it is expressed.
\end{itemize}

The connection between these is in the notions of truth function and truth condition.
The first two are notions of truth functional tautology.
In both languages the truth value of a sentence is a function of the truth values of the atomic sentences it contains, and a sentence is tautologous if that truth function is the one which always delivers the value ``true''.
In the second of these two the notion of truth function is slightly more complex and some explanation may be necessary of how the quantifiers can be so construed.
It may be noted however that it is a thesis of Wittgenstein's Tractatus\cite{wittgenstein1921} that logical truth in general is tautologous.
In the last case the restriction to truth functions (i.e. functions which take truth values as arguments and deliver truth values as results) is dropped, allowing that the essential element is that the relevant part of the semantics can be rendered as \emph{truth conditions} in which the result is a truth value but the argument need not be, and that it is of the essence of the concept tautology to single out from truth functions or conditions in general those which always deliver the truth value `true'.

In relation to these three notions of tautology, one thinks naturally of categorical propositions as involving quantification, and therefore, of syllogisms, if tautologous being so at best as first order validities, but in any case, if sound, as analytic.
These intuitions do not support a connection between syllogisms and propositional tautologies.

The connection we illustrate here is obtained via elementary set theory.
The intuition behind this is that Aristotelian predication is analogous to set inclusion, taking terms to denote their extensions (and singular terms as denoting singleton sets), together with complementation and negation.
This works except for the problematic univeral-particular syllogisms which infer particular conclusions from universal premises.
A connection with propositional logic can be obtained from this, since the elementary set theory required for this interpretation is a boolean algebra, as is the propositional calculus.

Partial reductions to set theory and propositional logic are exhibited in sections \ref{STI} and \ref{IP}.
The reduction to set theory is semantically more plausible than the second step to proposional logic, and provides an account of those u-p syllogisms, which are not accounted for by the propositional reduction.

We obtain kind of reduction of the decision problem for the non-u-p syllogisms to the decision problem for truth functional tautologies, but only in a very informal sense, since there are only a small finite set of valid syllogisms (though schemata) and so the decision problem is trivial.
For this reason syllogistic logic cannot be as expressive as a modern propositional logic, but conceivably might be closer to Stoic propositional logic.

The first step, to set theory is illustrated in the Wikpedia article on the syllogism, which gives Venn diagrams for all 24 ``valid'' syllogisms.

Though it is convenient to think of this as a two stage reduction, in the following implementation the two different reductions are generated independently.

\subsection{Interpretation in Set Theory}\label{STI}

=SML
open_theory "aristotle";
force_new_theory "syllog1";
=TEX

\ignore{
=SML
force_new_pc ⦏"'syllog1"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'syllog1";
set_merge_pcs ["misc2", "'syllog1"];
=TEX
}%ignore

Under the proposed mapping terms of the syllogism are mapped to propositions.
The term ``Mortal'' may be thought of as being mapped to the proposition ``x is Mortal''.

Thus the Barbara syllogism:

\begin{itemize}
\item All As are Bs
\item All Bs are Cs	
\item =========
\item All As are Cs
\end{itemize}

might be rendered set theoretically as:

=INLINEFT
(A ⊆ B ∧ B ⊆ C) ⇒ (A ⊆ C)
=TEX

where A, B and C are subsets of some universal set.

However, since we are working here in a sequent calculus we can render the theorems closely to the original as:

=GFT
   [A ⊆ B,
    B ⊆ C]
  ⊢ A ⊆ C
=TEX

A set theoretic presentation of the non-u-p syllogisms can be obtained by assuming that the sets are not empty, but no similarly plausible account of these syllogisms is available in propositional logic.


Here is a table describing the proposed mappings:

\begin{center}
\begin{tabular}[]{ | l | l | c | c |}
\hline
Aristotle & Meaning & Set Theory & Propositional Analogue\\
\hline
A a B & All A are B & A ⊆ B & A ⇒ B \\
A e B & All A are not B & 
=INLINEFT
A⊆~B
=TEX
 & A ⇒ ¬B \\
A i B & An A is B & 
=INLINEFT
¬(A⊆~B)
=TEX
 & ¬(A ⇒ ¬B)  \\
A o B & An A is not B & ¬(A ⊆ B) & ¬(A ⇒ B) \\
\hline
\end{tabular}
\end{center}

These mappings can be encapsulated as two `mapkits'.

First the set theory mapping:

=SML
val st_mkAP = 
	let	fun a (su, pr) = ⌜ⓜsu⌝ ⊆ ⓜpr⌝⌝
		fun e (su, pr) = ⌜ⓜsu⌝ ⊆ ~ ⓜpr⌝⌝
		fun i (su, pr) = ⌜¬ ⓜsu⌝ ⊆ ~ ⓜpr⌝⌝
		fun u (su, pr) = ⌜¬ ⓜsu⌝ ⊆ ⓜpr⌝⌝
	in fn s => case s of "a" => a | "e" => e | "i" => i | "o" => u
	end;

declare_type_abbrev("TermS", [], ⓣ'a SET⌝);

val st_mapkit:mapkit =
	{	mkAT = fn s => mk_var(s, ⓣTermS⌝),
		mkAP = st_mkAP,
		mkAS = fn x => x};
=TEX

\subsubsection{Generating The Propositions}

This section is mainly given over to short programs in our metalanguage the end effect of which is to secure the proof of the 15 theorems of set theory and 15 propositional tautologies which are obtained from non-u-p syllogisms by this naive transformation.

The results are visible in the ``theorems'' section of the theory listing in \thyref{syllog1}, and this section can be safely skipped by anyone whose interest is purely philosophical.

Mostly this uses functionality devised in the previous section to achieve two slightly different sets of theorems.

The following functions take a string which is the name of a syllogism, extract the vowels which occur in it and convert them into the corresponding propositional formula to give a triple of propositions.


giving the following list of ``goals'':

=GFT
val it =
   [  ([⌜M ⊆ P⌝, ⌜𝕊 ⊆ M⌝], ⌜𝕊 ⊆ P⌝),
      ([⌜M ⊆ ~ P⌝, ⌜𝕊 ⊆ M⌝], ⌜𝕊 ⊆ ~ P⌝),
      ([⌜M ⊆ P⌝, ⌜¬ 𝕊 ⊆ ~ M⌝], ⌜¬ 𝕊 ⊆ ~ P⌝),
      ([⌜M ⊆ ~ P⌝, ⌜¬ 𝕊 ⊆ ~ M⌝], ⌜¬ 𝕊 ⊆ P⌝),
      ([⌜P ⊆ ~ M⌝, ⌜𝕊 ⊆ M⌝], ⌜𝕊 ⊆ ~ P⌝),
      ([⌜P ⊆ M⌝, ⌜𝕊 ⊆ ~ M⌝], ⌜𝕊 ⊆ ~ P⌝),
      ([⌜P ⊆ ~ M⌝, ⌜¬ 𝕊 ⊆ ~ M⌝], ⌜¬ 𝕊 ⊆ P⌝),
      ([⌜P ⊆ M⌝, ⌜¬ 𝕊 ⊆ M⌝], ⌜¬ 𝕊 ⊆ P⌝),
      ([⌜¬ M ⊆ ~ P⌝, ⌜M ⊆ 𝕊⌝], ⌜¬ 𝕊 ⊆ ~ P⌝),
      ([⌜M ⊆ P⌝, ⌜¬ M ⊆ ~ 𝕊⌝], ⌜¬ 𝕊 ⊆ ~ P⌝),
      ([⌜¬ M ⊆ P⌝, ⌜M ⊆ 𝕊⌝], ⌜¬ 𝕊 ⊆ P⌝),
      ([⌜M ⊆ ~ P⌝, ⌜¬ M ⊆ ~ 𝕊⌝], ⌜¬ 𝕊 ⊆ P⌝),
      ([⌜P ⊆ M⌝, ⌜M ⊆ ~ 𝕊⌝], ⌜𝕊 ⊆ ~ P⌝),
      ([⌜¬ P ⊆ ~ M⌝, ⌜M ⊆ 𝕊⌝], ⌜¬ 𝕊 ⊆ ~ P⌝),
=TEX

\subsubsection{Proving the Syllogisms}

Here is a proof tactic for the non-u-p syllogisms under the set theory interpretation.

=SML
val st_tac = REPEAT (POP_ASM_T ante_tac)
		THEN PC_T1 "hol1" rewrite_tac []
		THEN prove_tac[];
=TEX

We now apply this to the non-u-p syllogisms, saving the results in the theory (\thyref{syllog1}).

=SML
proveSylls st_mapkit st_tac "" syllogism_data1;
=TEX

We now adjust the set theoretic reduction to deliver u-p syllogisms by including a non-emptyness assumption and obtain proofs of the nine syllogisms valid u-p syllogisms.


giving the following list of ``goals'':

=GFT
val it =
   [  ([⌜¬ {} ∈ {M; 𝕊; P}⌝, ⌜M ⊆ P⌝, ⌜M ⊆ 𝕊⌝], ⌜¬ 𝕊 ⊆ ~ P⌝),
      ([⌜¬ {} ∈ {M; 𝕊; P}⌝, ⌜M ⊆ ~ P⌝, ⌜M ⊆ 𝕊⌝], ⌜¬ 𝕊 ⊆ P⌝),
      ([⌜¬ {} ∈ {M; 𝕊; P}⌝, ⌜P ⊆ M⌝, ⌜M ⊆ 𝕊⌝], ⌜¬ 𝕊 ⊆ ~ P⌝),
      ([⌜¬ {} ∈ {M; 𝕊; P}⌝, ⌜P ⊆ ~ M⌝, ⌜M ⊆ 𝕊⌝], ⌜¬ 𝕊 ⊆ P⌝),
      ([⌜¬ {} ∈ {M; 𝕊; P}⌝, ⌜M ⊆ P⌝, ⌜𝕊 ⊆ M⌝], ⌜¬ 𝕊 ⊆ ~ P⌝),
      ([⌜¬ {} ∈ {M; 𝕊; P}⌝, ⌜M ⊆ ~ P⌝, ⌜𝕊 ⊆ M⌝], ⌜¬ 𝕊 ⊆ P⌝),
      ([⌜¬ {} ∈ {M; 𝕊; P}⌝, ⌜P ⊆ ~ M⌝, ⌜𝕊 ⊆ M⌝], ⌜¬ 𝕊 ⊆ P⌝),
      ([⌜¬ {} ∈ {M; 𝕊; P}⌝, ⌜P ⊆ M⌝, ⌜𝕊 ⊆ ~ M⌝], ⌜¬ 𝕊 ⊆ P⌝),
      ([⌜¬ {} ∈ {M; 𝕊; P}⌝, ⌜P ⊆ M⌝, ⌜M ⊆ ~ 𝕊⌝], ⌜¬ 𝕊 ⊆ P⌝)]
: (TERM list * TERM) list
=TEX

We now apply this to the non-u-p syllogisms, saving the results in the theory.

The following code generates the goals for proving the above syllogisms from the previously defined data structure desribing the valid syllogisms, generates and checks formal proofs and saves the resulting theorems in the current theory. 

=SML
val st2_mapkit:mapkit =
	{	mkAT = fn s => mk_var(s, ⓣTermS⌝),
		mkAP = st_mkAP,
		mkAS = fn (ps, c) => (⌜¬ ({}:'a SET) ∈ {M; 𝕊; P}⌝::ps, c)};
=TEX

=SML
val st2_tac = REPEAT (POP_ASM_T ante_tac)
		THEN PC_T1 "hol1" rewrite_tac [] THEN prove_tac[];
=TEX

=SML
proveSylls st2_mapkit st2_tac "" (syllogism_data2 @ syllogism_data3);
=TEX

The full set of syllogisms may be found in the theory (\thyref{syllog1}).

\subsection{Propositional Interpretation}\label{IP}

=SML
open_theory "aristotle";
force_new_theory "syllog2";
=TEX

\ignore{
=SML
force_new_pc ⦏"'syllog2"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'syllog2";
set_merge_pcs ["misc2", "'syllog2"];
=TEX
}%ignore

The term ``Mortal'' may be thought of as being mapped to the proposition ``x is Mortal''.

Thus the Barbara syllogism:

\begin{itemize}
\item All As are Bs
\item All Bs are Cs	
\item =========
\item All As are Cs
\end{itemize}

is rendered in the propositional calculus as:

=INLINEFT
(A ⇒ B ∧ B ⇒ C) ⇒ (A ⇒ C)
=TEX

where A, B and C are boolean values or propositions.

However, since we are working here in a sequent calculus we can render the theorems closely to the original as:

=GFT
   [A ⇒ B,
    B ⇒ C]
  ⊢ A ⇒ C
=TEX

The propositional logic mapping is determined as follows:

=SML
declare_type_abbrev("TermP", [], ⓣBOOL⌝);

val pl_mapkit:mapkit =
	let fun a (su, pr) = ⌜ⓜsu⌝ ⇒ ⓜpr⌝⌝
		fun e (su, pr) = ⌜ⓜsu⌝ ⇒ ¬ ⓜpr⌝⌝
		fun i (su, pr) = ⌜¬ (ⓜsu⌝ ⇒ ¬ ⓜpr⌝)⌝
		fun u (su, pr) = ⌜¬( ⓜsu⌝ ⇒ ⓜpr⌝)⌝
	in {	mkAT = fn s => mk_var(s, ⓣTermP⌝),
		mkAP = fn s => case s of
			"a" => a
		|	"e" => e 
		|	"i" => i 
		|	"o" => u,
		mkAS = fn x => x}
	end;
=TEX

giving the following list of ``goals'':

=GFT
val it =
   [([⌜M ⇒ P⌝, ⌜𝕊 ⇒ M⌝], ⌜𝕊 ⇒ P⌝),
      ([⌜M ⇒ ¬ P⌝, ⌜𝕊 ⇒ M⌝], ⌜𝕊 ⇒ ¬ P⌝),
      ([⌜M ⇒ P⌝, ⌜¬ (𝕊 ⇒ ¬ M)⌝], ⌜¬ (𝕊 ⇒ ¬ P)⌝),
      ([⌜M ⇒ ¬ P⌝, ⌜¬ (𝕊 ⇒ ¬ M)⌝], ⌜¬ (𝕊 ⇒ P)⌝),
      ([⌜P ⇒ ¬ M⌝, ⌜𝕊 ⇒ M⌝], ⌜𝕊 ⇒ ¬ P⌝),
      ([⌜P ⇒ M⌝, ⌜𝕊 ⇒ ¬ M⌝], ⌜𝕊 ⇒ ¬ P⌝),
      ([⌜P ⇒ ¬ M⌝, ⌜¬ (𝕊 ⇒ ¬ M)⌝], ⌜¬ (𝕊 ⇒ P)⌝),
      ([⌜P ⇒ M⌝, ⌜¬ (𝕊 ⇒ M)⌝], ⌜¬ (𝕊 ⇒ P)⌝),
      ([⌜¬ (M ⇒ ¬ P)⌝, ⌜M ⇒ 𝕊⌝], ⌜¬ (𝕊 ⇒ ¬ P)⌝),
      ([⌜M ⇒ P⌝, ⌜¬ (M ⇒ ¬ 𝕊)⌝], ⌜¬ (𝕊 ⇒ ¬ P)⌝),
      ([⌜¬ (M ⇒ P)⌝, ⌜M ⇒ 𝕊⌝], ⌜¬ (𝕊 ⇒ P)⌝),
      ([⌜M ⇒ ¬ P⌝, ⌜¬ (M ⇒ ¬ 𝕊)⌝], ⌜¬ (𝕊 ⇒ P)⌝),
      ([⌜P ⇒ M⌝, ⌜M ⇒ ¬ 𝕊⌝], ⌜𝕊 ⇒ ¬ P⌝),
      ([⌜¬ (P ⇒ ¬ M)⌝, ⌜M ⇒ 𝕊⌝], ⌜¬ (𝕊 ⇒ ¬ P)⌝),
      ([⌜P ⇒ ¬ M⌝, ⌜¬ (M ⇒ ¬ 𝕊)⌝], ⌜¬ (𝕊 ⇒ P)⌝)] : (TERM list * TERM) list
=TEX

The following tactic suffices for proving propositional tautologies.

=SML
val pl_tac = REPEAT (POP_ASM_T ante_tac)
		THEN REPEAT strip_tac;
=TEX

We now apply this to the non-u-p syllogisms, saving the results in the theory.

=SML
val valid_psylls = proveSylls pl_mapkit pl_tac "" syllogism_data1;
=TEX

This is the resulting value.
=GFT
val valid_psylls =
   [("Barbara", M ⇒ P, 𝕊 ⇒ M ⊢ 𝕊 ⇒ P),
      ("Celarent", M ⇒ ¬ P, 𝕊 ⇒ M ⊢ 𝕊 ⇒ ¬ P),
      ("Darii", M ⇒ P, ¬ (𝕊 ⇒ ¬ M) ⊢ ¬ (𝕊 ⇒ ¬ P)),
      ("Ferio", M ⇒ ¬ P, ¬ (𝕊 ⇒ ¬ M) ⊢ ¬ (𝕊 ⇒ P)),
      ("Cesare", P ⇒ ¬ M, 𝕊 ⇒ M ⊢ 𝕊 ⇒ ¬ P),
      ("Camestres", P ⇒ M, 𝕊 ⇒ ¬ M ⊢ 𝕊 ⇒ ¬ P),
      ("Festino", P ⇒ ¬ M, ¬ (𝕊 ⇒ ¬ M) ⊢ ¬ (𝕊 ⇒ P)),
      ("Baroco", P ⇒ M, ¬ (𝕊 ⇒ M) ⊢ ¬ (𝕊 ⇒ P)),
      ("Disamis", ¬ (M ⇒ ¬ P), M ⇒ 𝕊 ⊢ ¬ (𝕊 ⇒ ¬ P)),
      ("Datisi", M ⇒ P, ¬ (M ⇒ ¬ 𝕊) ⊢ ¬ (𝕊 ⇒ ¬ P)),
      ("Bocardo", ¬ (M ⇒ P), M ⇒ 𝕊 ⊢ ¬ (𝕊 ⇒ P)),
      ("Ferison", M ⇒ ¬ P, ¬ (M ⇒ ¬ 𝕊) ⊢ ¬ (𝕊 ⇒ P)),
      ("Camenes", P ⇒ M, M ⇒ ¬ 𝕊 ⊢ 𝕊 ⇒ ¬ P),
      ("Dimaris", ¬ (P ⇒ ¬ M), M ⇒ 𝕊 ⊢ ¬ (𝕊 ⇒ ¬ P)),
      ("Fresison", P ⇒ ¬ M, ¬ (M ⇒ ¬ 𝕊) ⊢ ¬ (𝕊 ⇒ P))] : (string * THM) list
=TEX

.. which is a list of name/theorem pairs of the tautologies corresponding to each syllogism.

The theorems are also displayed in the theory listing in \thyref{syllog2}

Some words about the very limited signficance of this little exercise would be appropriate here!

\subsection{Naive Interpretation in Predicate Calculus}\label{NIPC}

=SML
open_theory "aristotle";
force_new_theory "syllog3";
=TEX

\ignore{
=SML
force_new_pc ⦏"'syllog3"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'syllog3";
set_merge_pcs ["misc2", "'syllog3"];
=TEX
}%ignore

\subsubsection{Semantics}

Aristotle's syllogistic logic is concerned with inferences between judgements considered as predications.
A predication in Aristotle affirms a {\it predicate} of some {\it subject}, but by contrast with more recent notions of predication the subject need not be an individual, the kinds of things which appear as predicates may also appear as subjects, and the relationship expressed seems closer to a modern eye to set inclusion than to what we now regard as predication.
Since subject and predicate are for present purposes the same kind of thing, it is useful to have a name for that kind of thing, and I will use the name {\it property}.

There are four kinds of predication which we have here to account for, which we will do by offering definitions which provide a good model for syllogistic logic, i.e. one in which the syllogisms held to be true by Aristotle are in fact true.
Before providing these definitions we must decide what kind of thing are the terms which are related by Aristotelian predication.
 
In HOL the most natural answer to this is ``boolean valued functions'' which are objects of type $ⓣ'a → BOOL⌝$ for some type of individuals which we can leave open by using the type variable $ⓣ'a⌝$.
This provides a simple model of Aristotle's non-u-p syllogistic reasoning.
Four of the syllogisms which Aristotle considered valid fail under this conception of predicate, because among the objects of type $ⓣ'a → BOOL⌝$ is the function $⌜λx:'a⦁ F⌝$ which corresponds to a predicate with empty extension and does not admit inference from the universal to the existential (unless the universal is interpreted specially).

=SML
declare_type_abbrev("Term2", [], ⓣ'a → BOOL⌝);
=TEX

\subsubsection{Predication}

``o'' is already in use for functional composition, so we will use ``u'' instead and then use an alias to permit us to write this as ``o'' (type inference will usually resolve any ambiguity).

The predication operators are defined as follows:
=SML
declare_infix (300, "a");
declare_infix (300, "e");
declare_infix (300, "i");
declare_infix (300, "u");
=TEX

ⓈHOLCONST
│ $⦏a⦎ : Term2 → Term2 → BOOL
├──────
│ ∀A B⦁ A a B ⇔ ∀x⦁ A x ⇒ B x
■

ⓈHOLCONST
│ $⦏e⦎ : Term2 → Term2 → BOOL
├──────
│ ∀A B⦁ A e B ⇔ ∀x⦁ A x ⇒ ¬ B x
■

ⓈHOLCONST
│ $⦏i⦎ : Term2 → Term2 → BOOL
├──────
│ ∀A B⦁ A i B ⇔ ∃x⦁ A x ∧ B x
■

ⓈHOLCONST
│ $⦏u⦎ : Term2 → Term2 → BOOL
├──────
│ ∀A B⦁ A u B ⇔ ∃x⦁ A x ∧ ¬ B x
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
val ⦏syll_tac⦎ = asm_prove_tac (map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝]);
fun ⦏syll_rule⦎ g = tac_proof (g, syll_tac);	
=TEX

\paragraph{Simple Conversion}

Using the above tactic thus:

=SML
val e_conv_thm = save_thm ("e_conv_thm", syll_rule([⌜A e B⌝], ⌜B e A⌝));
val i_conv_thm = save_thm ("i_conv_thm", syll_rule([⌜A i B⌝], ⌜B i A⌝));
=TEX

The following two theorems are obtained.
=GFT
val e_conv_thm = A e B ⊢ B e A : THM
val i_conv_thm = A i B ⊢ B i A : THM
=TEX

The following two theorems show that the other obvious conversions are false.

\ignore{
=SML
set_goal([], ⌜∃A B⦁ A a B ∧ ¬ B a A⌝);
a (∃_tac ⌜λx⦁F⌝ THEN ∃_tac ⌜λx⦁T⌝ THEN syll_tac);
val a_not_conv_thm = save_pop_thm "a_not_conv_thm";

set_goal([], ⌜∃A B:Term2⦁ A o B ∧ ¬ B o A⌝);
a (∃_tac ⌜λx⦁T⌝ THEN ∃_tac ⌜λx⦁F⌝ THEN syll_tac);
val o_not_conv_thm = save_pop_thm "o_not_conv_thm";
=TEX
}%ignore

=GFT
a_not_conv_thm = ⊢ ∃ A B⦁ A a B ∧ ¬ B a A
o_not_conv_thm = ⊢ ∃ A B⦁ A o B ∧ ¬ B o A
=TEX

\paragraph{Conversion Per Accidens}

These don't work here because they rely upon the u-p syllogisms.

\paragraph{Obversion}

For these we need to define an operation of complementation on terms.

ⓈHOLCONST
│ ⦏Complement⦎ : Term2 → Term2
├──────
│ ∀A α⦁ (Complement A) α ⇔ ¬ (A α) 
■

We will use ``\verb!~!'' as a shorthand for ``complement''.

=SML
declare_alias ("~", ⌜Complement⌝);
=TEX

\ignore{
=SML
add_pc_thms "'syllog3" [get_spec ⌜Complement⌝];
set_merge_pcs ["misc2", "'syllog3"];
=TEX
}%ignore

\ignore{
=SML
val ae_obv_thm = save_thm ("ae_obv_thm", syll_rule([⌜A a B⌝], ⌜A e ~B⌝));
val ea_obv_thm = save_thm ("ea_obv_thm", syll_rule([⌜A e B⌝], ⌜A a ~B⌝));

set_goal([⌜A i B⌝], ⌜A u ~B⌝);
a (syll_tac);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val io_obv_thm = save_pop_thm "io_obv_thm";

set_goal([⌜A u B⌝], ⌜A i ~B⌝);
a (syll_tac);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val oi_obv_thm = save_pop_thm "oi_obv_thm";
=TEX
}%ignore

=GFT
ae_obv_thm = 	A a B ⊢ A e ~ B
ea_obv_thm = 	A e B ⊢ A a ~ B
io_obv_thm = 	A i B ⊢ A o ~ B
oi_obv_thm = 	A o B ⊢ A i ~ B
=TEX

\paragraph{Contraposition and Inversion}

\subsubsection{The Square of Opposition}


=GFT
ao_contrad_thm = ⊢ A a B ⇔ ¬ A o B
ei_contrad_thm = ⊢ A e B ⇔ ¬ A i B
¬ae_contrar_thm = ⊢ ¬ (∀ A B⦁ ¬ (A a B ∧ A e B))
¬io_subcont_thm = ⊢ ¬ (∀ A B⦁ A i B ∨ A o B)
¬ai_subalt_thm = ⊢ ¬ (∀ A B⦁ A a B ⇒ A i B)
¬eo_subalt_thm = ⊢ ¬ (∀ A B⦁ A e B ⇒ A o B)
=TEX

\ignore{
=SML
val ao_contrad_thm = save_thm ("ao_contrad_thm", syll_rule ([], ⌜(A a B) ⇔ ¬ (A o B)⌝));
val ei_contrad_thm = save_thm ("ei_contrad_thm", syll_rule ([], ⌜(A e B) ⇔ ¬ (A i B)⌝));

set_goal ([], ⌜¬ ∀A B ⦁ ¬ (A a B ∧ A e B)⌝);
a (syll_tac);
a (∃_tac ⌜λx⦁F⌝ THEN rewrite_tac[]);
val ¬ae_contrar_thm = save_pop_thm "¬ae_contrar_thm";

set_goal ([], ⌜¬ ∀A B ⦁ A i B ∨ A u B⌝);
a (strip_tac);
a (∃_tac ⌜λx⦁F⌝);
a (rewrite_tac [get_spec ⌜$i⌝, get_spec ⌜$u⌝]);
val ¬IU_thm = save_pop_thm "¬IU_thm";

set_goal ([], ⌜¬ ∀A B ⦁ A a B ⇒ A i B⌝);
a (strip_tac);
a (∃_tac ⌜λx⦁F⌝);
a (rewrite_tac [get_spec ⌜$i⌝, get_spec ⌜$a⌝]);
val ¬ai_subalt_thm = save_pop_thm "¬ai_subalt_thm";

set_goal ([], ⌜¬ ∀A B ⦁ A e B ⇒ A u B⌝);
a (strip_tac);
a (∃_tac ⌜λx⦁F⌝);
a (rewrite_tac [get_spec ⌜$e⌝, get_spec ⌜$u⌝]);
val ¬eo_subalt_thm = save_pop_thm "¬eo_subalt_thm";
=TEX
}%


\subsubsection{The Syllogisms}

The fifteen valid non-u-p syllogisms are true under this semantics and can be proven formally with ease.

\subsubsection{Generating Syllogisms}

First we make a \emph{mapkit}.

=SML
val s1mapkit:mapkit = mkSimpMapkit ⓣTerm2⌝ [⌜$a⌝,⌜$e⌝,⌜$i⌝,⌜$u⌝];
=TEX

Then we apply this in generating and proving the non u-p syllogisms.

=SML
proveGoals syll_tac "" (mkGoals s1mapkit syllogism_data1);
=TEX

This is the resulting value.
=GFT
val valid_sylls = [
	("Barbara", M a P, 𝕊 a M ⊢ 𝕊 a P),
	("Celarent", M e P, 𝕊 a M ⊢ 𝕊 e P),
	("Darii", M a P, 𝕊 i M ⊢ 𝕊 i P),
	("Ferio", M e P, 𝕊 i M ⊢ 𝕊 o P),
	("Cesare", P e M, 𝕊 a M ⊢ 𝕊 e P),
	("Camestres", P a M, 𝕊 e M ⊢ 𝕊 e P),
	("Festino", P e M, 𝕊 i M ⊢ 𝕊 o P),
	("Baroco", P a M, 𝕊 o M ⊢ 𝕊 o P),
	("Disamis", M i P, M a 𝕊 ⊢ 𝕊 i P),
	("Datisi", M a P, M i 𝕊 ⊢ 𝕊 i P),
	("Bocardo", M o P, M a 𝕊 ⊢ 𝕊 o P),
	("Ferison", M e P, M i 𝕊 ⊢ 𝕊 o P),
	("Camenes", P a M, M e 𝕊 ⊢ 𝕊 e P),
	("Dimaris", P i M, M a 𝕊 ⊢ 𝕊 i P),
	("Fresison", P e M, M i 𝕊 ⊢ 𝕊 o P)
] : (string * THM) list
=TEX

The theorems are also displayed in the theory listing in \thyref{syllog3}

\subsection{Predicate Calculus Without Empty Terms}\label{PCNET}

There is more than one way in which the semantics of the syllogism can be modified to make the inference from ``All As are Bs'' to ``Some As are Bs'' sound.
One way would be to change the meaning of ``All''.
This would interfere with the square of opposition by making diagonal entries no longer contradictories.
From this I initially inferred that the exclusion of empty predicates is a better approach.
\footnote{This seemed then to be endorsed by Robin Smith in the \href{http://plato.stanford.edu/entries/aristotle-logic/}{Stanford Encyclopaedia of Philosophy} \cite{smithAL2009}.}

We can then prove valid 24 forms of syllogism.

For the most concise statement of the results of the exercise, the reader should refer directly to the theory listing in \thyref{syllog4}.

=SML
open_theory "aristotle";
force_new_theory "syllog4";
=TEX

\ignore{
=SML
force_new_pc ⦏"'syllog4"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'syllog4";
set_merge_pcs ["misc2", "'syllog4"];
=TEX
}%ignore

\subsubsection{Semantics}

The key to getting the u-p syllogisms into the model is the adoption of a type for the variables in the syllogisms which does not include empty predicates.
We could do this by defining a new type which is a sub-type of the propositional functions, but it is simpler to use another type-abbreviation as follows.

Instead of using a propositional function, which might be unsatisfiable, we use an ordered pair.
The pair consists of one value, a value for which the predicate is true, and a propositional function.
The predicate $(v, pf)$ is then to be considered true of some value $x$ {\it either} if $x$ is $v$ {\it or} if $pf$ is true of $x$. 

=SML
declare_type_abbrev("Term3", [], ⓣ'a × ('a → BOOL)⌝);
=TEX

\subsubsection{Predication}

To work with this new type for the predicates we define a function which will convert this kind of predicate into the old kind, as follows:

ⓈHOLCONST
│ ⦏p⦎ : Term3 → ('a → BOOL)
├──────
│ ∀A⦁ p A = λx⦁ let (v,f) = A in x = v ∨ f x 
■

The resulting values have the same type as the old, but they will never have empty extension.

The following principle can be proven (proof omitted):

\ignore{
=SML
set_goal([], ⌜∀A⦁ ∃v⦁ (p A) v⌝);
a (strip_tac);
a (∃_tac ⌜Fst A⌝ THEN rewrite_tac [get_spec ⌜p⌝, let_def]);
val p_∃_lemma = save_pop_thm "p_∃_lemma";
=TEX
}%ignore

=GFT
p_∃_lemma =
	⊢ ∀ A⦁ ∃v⦁ p A v
=TEX

This principle is what we need to prove the u-p syllogisms.

It should be noted that there is no complementation operation on terms of this type and that the obversions will therefore fail.

We then proceed in a similar manner to the first model, using the function $p$ to convert the new kind of predicate into the old.

They predication operators are then defined.
Note that the differences are small and uniform.
The type $ⓣPROP⌝$ is changed to $ⓣTerm3⌝$ and the function $p$ is invoked before applying a predicate.

=SML
declare_infix (300, "a");
declare_infix (300, "e");
declare_infix (300, "i");
declare_infix (300, "u");
=TEX

ⓈHOLCONST
│ $⦏a⦎ : Term3 → Term3 → BOOL
├──────
│ ∀A B⦁ A a B ⇔ ∀x⦁ p A x ⇒ p B x
■

ⓈHOLCONST
│ $⦏e⦎ : Term3 → Term3 → BOOL
├──────
│ ∀A B⦁ A e B ⇔ ∀x⦁ p A x ⇒ ¬ p B x
■

ⓈHOLCONST
│ $⦏i⦎ : Term3 → Term3 → BOOL
├──────
│ ∀A B⦁ A i B ⇔ ∃x⦁ p A x ∧ p B x
■

ⓈHOLCONST
│ $⦏u⦎ : Term3 → Term3 → BOOL
├──────
│ ∀A B⦁ A u B ⇔ ∃x⦁ p A x ∧ ¬ p B x
■

=SML
declare_alias("o", ⌜$u⌝);
=TEX

With these defined we can now produce a `mapkit' for translating the syllogisms under this semantics.

=SML
val s2_mapkit:mapkit = mkSimpMapkit ⓣTerm3⌝ [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝];
=TEX

\subsubsection{Laws of Immediate Inference}


The same tactic used for proof of the syllogisms in the previous model still works with this model (with the new definitions), but does not prove the u-p syllogisms.

To obtain proofs of these other syllogisms we need to make use of the lemma we proved about $p$, {\it p\_∃\_lemma}.
This we do by instantiating it for each of the variables which appear in the syllogisms and supplying these for use in the proof.

=SML
val ⦏syll_tac2⦎ =
	(MAP_EVERY (fn x => strip_asm_tac (∀_elim x p_∃_lemma))
		[⌜M:Term3⌝, ⌜P:Term3⌝, ⌜𝕊:Term3⌝, ⌜A:Term3⌝, ⌜B:Term3⌝])
	THEN asm_prove_tac (map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝]);

fun ⦏syll_rule2⦎ g = tac_proof(g, syll_tac2);
=TEX

\paragraph{Simple Conversion}


=SML
val ⦏e_conv⦎ = ([⌜A e B⌝], ⌜B e A⌝);
val ⦏i_conv⦎ = ([⌜A i B⌝], ⌜B i A⌝);
=TEX

=SML
val e_conv_thm = save_thm ("e_conv_thm", syll_rule2 e_conv);
val i_conv_thm = save_thm ("i_conv_thm", syll_rule2 i_conv);
=TEX

=GFT
val e_conv_thm = A e B ⊢ B e A : THM
val i_conv_thm = A i B ⊢ B i A : THM
=TEX

In this version of the semantics, ``a'' and ``o'' conversion is neither provable nor refutable.
In the previous version, since the universe is a HOL type there is at least one individual, and contradictory predicates are allowed, we can use these two to disprove the two conversions.
With this semantics there is no empty predicate, and we cannot know that there are two distinct predicates.

\paragraph{Conversion Per Accidens}

=SML
val ⦏sg_03⦎ = ([⌜A a B⌝], ⌜B i A⌝);
val ⦏sg_04⦎ = ([⌜A e B⌝], ⌜B u A⌝);
=TEX

=SML
val ai_conv_thm = save_thm ("ai_conv_thm", syll_rule2 sg_03);
val eo_conv_thm = save_thm ("eo_conv_thm", syll_rule2 sg_04);
=TEX

=GFT
val ai_conv_thm = A a B ⊢ B i A : THM
val eo_conv_thm = A e B ⊢ B o A : THM
=TEX

\paragraph{Obversion}

We have been unable to define a complementation operation and the obversions listed by Strawson cannot even be expressed in this representation.

=IGN
val ⦏sg_05⦎ = ([⌜A a B⌝], ⌜A e ~ B⌝);
val ⦏sg_06⦎ = ([⌜A e B⌝], ⌜A a ~ B⌝);
val ⦏sg_07⦎ = ([⌜A i B⌝], ⌜A o ~ B⌝);
val ⦏sg_08⦎ = ([⌜A o B⌝], ⌜A i ~ B⌝);
=TEX

=IGN
val ai_conv_thm = save_thm ("ai_conv_thm", syll_rule2 sg_03);
val eo_conv_thm = save_thm ("eo_conv_thm", syll_rule2 sg_04);
=TEX

=IGN
val ai_conv_thm = A a B ⊢ B i A : THM
val eo_conv_thm = A e B ⊢ B o A : THM
=TEX

\paragraph{The Square of Opposition}

=SML
val ⦏sg_09⦎ = ([]:TERM list, ⌜A a B ⇔ ¬ A u B⌝);
val ⦏sg_10⦎ = ([]:TERM list, ⌜A e B ⇔ ¬ A i B⌝);
val ⦏sg_11⦎ = ([]:TERM list, ⌜¬ (A a B ∧ A e B)⌝);
val ⦏sg_12⦎ = ([]:TERM list, ⌜A i B ∨ A u B⌝);
val ⦏sg_13⦎ = ([⌜A a B⌝], ⌜A i B⌝);
val ⦏sg_14⦎ = ([⌜A e B⌝], ⌜A u B⌝);
=TEX

=SML
val sg_09_thm = save_thm ("sg_09_thm", syll_rule2 sg_09);
val sg_10_thm = save_thm ("sg_10_thm", syll_rule2 sg_10);
val sg_11_thm = save_thm ("sg_11_thm", syll_rule2 sg_11);
val sg_12_thm = save_thm ("sg_12_thm", syll_rule2 sg_12);
val sg_13_thm = save_thm ("sg_13_thm", syll_rule2 sg_13);
val sg_14_thm = save_thm ("sg_14_thm", syll_rule2 sg_14);
=TEX

\subsubsection{The Valid Syllogisms}

The valid syllogisms have been described in Section \ref{syllogisms}.

All twenty four syllogisms are true under this semantics and have been proven.
The actual theorems are shown in the theory listing in \thyref{syllog4}.

To implement a mapping corresponding to the above semantics we must create a matching \emph{mapkit} as follows:

=SML
val ⦏mods_mapkit⦎:mapkit = mkSimpMapkit ⓣTerm3⌝ [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝];
=TEX

\subsubsection{Proving the Syllogisms}

The resulting translation yields goals which look exactly like the previous versions but have the meanings defined in this context.
They are proven and stored in the theory listing (see Appendix \ref{syllog4}) by the following:

=SML
proveSylls mods_mapkit syll_tac2 "" (syllogism_data1 @ syllogism_data2 @ syllogism_data3);
=TEX

\subsection{Existential Import in Universals}\label{IEIU}

A more complete description of this interpretation, which is taken from Strawson \cite{strawson52} though not endorsed by him, is that existential import in relation both to the subject and the complement of the predicate, is present in universals and is absent from particular assertions.
This combination is though by Strawson to be unsatisfactory primarily I believe because of its poor correspondence with any plausible account of the ordinary usage of the terms involved, however it appears also to be in poor correspondence with Aristotle.
The difficulties can be traced to Strawson's acceptance of all four obversions, which appear not to have been endorsed by Aristotle.
These obversions lead to the equivalence of contrapositives, and create a symmetry between subject and predicate in consequence of which presuppositions or implications of non emptyness attach both to subject and predicate.

My aim here is to confirm what Strawson says about this, which is that it satisfies all 14 laws and 28 syllogisms.
He writes as if it were the only interpretation of this kind (i.e. not involving existential presuppositions rather than implications) which meet this requirement, on which I am sceptical but have not come to a definite conclusion.

=SML
open_theory "aristotle";
force_new_theory "syllog5";
=TEX

\ignore{
=SML
force_new_pc ⦏"'syllog5"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'syllog5";
set_merge_pcs ["misc2", "'syllog5"];
=TEX
}%ignore

\subsubsection{Semantics}

Aristotle's syllogistic logic is concerned with inferences between judgements considered as predications.
A predication in Aristotle affirms a {\it predicate} of some {\it subject}, but by contrast with more recent notions of predication the subject need not be an individual, the kinds of things which appear as predicates may also appear as subjects, and the relationship expressed seems closer to a modern eye to set inclusion than to what we now regard as predication.
Since subject and predicate are for present purposes the same kind of thing, it is useful to have a name for that kind of thing, and I will use the name {\it property}.

There are four kinds of predication which we have here to account for, which we will do by offering definitions which provide a good model for syllogistic logic, i.e. one in which the syllogisms held to be true by Aristotle are in fact true.
Before providing these definitions we must decide what kind of thing are the terms which are related by Aristotelian predication.
 
In HOL the most natural answer to this is ``boolean valued functions'' which are objects of type $ⓣ'a → BOOL⌝$ for some type of individuals which we can leave open by using the type variable $ⓣ'a⌝$.
This provides a simple model of Aristotle's non-u-p syllogistic reasoning.
Four of the syllogisms which Aristotle considered valid fail under this conception of predicate, because among the objects of type $ⓣ'a → BOOL⌝$ is the function $⌜λx:'a⦁ F⌝$ which corresponds to a predicate with empty extension and does not admit inference from the universal to the existential (unless the universal is interpreted specially).

=SML
declare_type_abbrev("Term2", [], ⓣ'a → BOOL⌝);
=TEX

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
│ $⦏a⦎ : Term2 → Term2 → BOOL
├──────
│ ∀A B⦁ A a B ⇔ (∀x⦁ A x ⇒ B x) ∧ (∃x⦁ A x) ∧ (∃x⦁ ¬ B x)
■

ⓈHOLCONST
│ $⦏e⦎ : Term2 → Term2 → BOOL
├──────
│ ∀A B⦁ A e B ⇔ (∀x⦁ A x ⇒ ¬ B x) ∧ (∃x⦁ A x) ∧ (∃x⦁ B x)
■

ⓈHOLCONST
│ $⦏i⦎ : Term2 → Term2 → BOOL
├──────
│ ∀A B⦁ A i B ⇔ (∃x⦁ A x ∧ B x) ∨ ¬ (∃x⦁ A x) ∨ ¬ (∃x⦁ B x)
■

ⓈHOLCONST
│ $⦏u⦎ : Term2 → Term2 → BOOL
├──────
│ ∀A B⦁ A u B ⇔ (∃x⦁ A x ∧ ¬ B x) ∨ ¬ (∃x⦁ A x) ∨ ¬ (∃x⦁ ¬ B x)
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
val ⦏syll_tac3⦎ = asm_prove_tac (map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝]);
fun ⦏syll_rule3⦎ g = tac_proof (g, syll_tac3);	
=TEX

\paragraph{Simple Conversion}

=SML
val e_conv_thm = save_thm("e_conv_thm", syll_rule3 ([⌜A e B⌝], ⌜B e A⌝));
val i_conv_thm = save_thm("i_conv_thm", syll_rule3 ([⌜A i B⌝], ⌜B i A⌝));
=TEX

The following two theorems are obtained.
=GFT
⦏e_conv_thm⦎ =  A e B ⊢ B e A
⦏i_conv_thm⦎ =  A i B ⊢ B i A
=TEX

The following two theorems show that the other obvious conversions are also false.
Note that the theorems are not polymorphic, they are proven specifically for terms of type $ℕ → BOOL$ (though any type of more than one element would do).

\ignore{
=SML
set_goal([], ⌜∃A B:ℕ → BOOL⦁ A a B ∧ ¬ B a A⌝);
a (REPEAT (POP_ASM_T ante_tac) THEN rewrite_tac (map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝]));
a (∃_tac ⌜λx⦁ x = 0⌝ THEN ∃_tac ⌜λx⦁ x = 0 ∨ x = 1⌝ THEN prove_tac[]);
a (∃_tac ⌜2⌝ THEN PC_T1 "lin_arith" prove_tac[]);
a (∃_tac ⌜1⌝ THEN PC_T1 "lin_arith" prove_tac[]);
val ¬a_conv_thm = save_pop_thm "¬a_conv_thm";

set_goal([], ⌜∃A B:ℕ → BOOL⦁ A u B ∧ ¬ B u A⌝);
a (REPEAT (POP_ASM_T ante_tac) THEN rewrite_tac (map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝]));
a (∃_tac ⌜λx⦁ x = 0 ∨ x = 1⌝ THEN ∃_tac ⌜λx⦁ x = 0⌝ THEN prove_tac[]);
a (SPEC_NTH_ASM_T 2 ⌜1⌝ ante_tac THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a (SPEC_NTH_ASM_T 2 ⌜1⌝ ante_tac THEN rewrite_tac[]);
(* *** Goal "3" *** *)
a (∃_tac ⌜2⌝ THEN PC_T1 "lin_arith" prove_tac[]);
val ¬o_conv_thm = save_pop_thm "¬o_conv_thm";
=TEX
}%ignore

=GFT
¬a_conv_thm = ⊢ ∃ A B⦁ A a B ∧ ¬ B a A
¬o_conv_thm = ⊢ ∃ A B⦁ A o B ∧ ¬ B o A
=TEX

\paragraph{Conversion Per Accidens}

These come out OK.

=SML
val ai_conv_thm = save_thm ("ai_conv_thm", syll_rule3([⌜A a B⌝], ⌜B i A⌝));
val eo_conv_thm = save_thm ("eo_conv_thm", syll_rule3([⌜A e B⌝], ⌜B u A⌝));
=TEX

=GFT
val ⦏ai_conv_thm⦎ = A a B ⊢ B i A : THM
val ⦏eo_conv_thm⦎ = A e B ⊢ B o A : THM
=TEX

\paragraph{Obversion}

For these we need to define an operation of complementation on terms.

ⓈHOLCONST
│ ⦏Complement⦎ : Term2 → Term2
├──────
│ ∀A α⦁ (Complement A) α ⇔ ¬ (A α) 
■

We will use ``\verb!~!'' as a shorthand for ``Complement''.

=SML
declare_alias ("~", ⌜Complement⌝);
=TEX

\ignore{
=SML
add_pc_thms "'syllog5" [get_spec ⌜Complement⌝];
set_merge_pcs ["misc2", "'syllog5"];
=TEX
}%ignore

\ignore{
=SML
set_goal([⌜A a B⌝], ⌜A e ~B⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac(map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝]));
val ae_obv_thm = save_pop_thm "ae_obv_thm";

set_goal([⌜A e B⌝], ⌜A a ~B⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac(map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝]));
val ea_obv_thm = save_pop_thm "ea_obv_thm";

set_goal([⌜A i B⌝], ⌜A u ~B⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac(map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝]));
val io_obv_thm = save_pop_thm "io_obv_thm";

set_goal([⌜A u B⌝], ⌜A i ~B⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac(map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝]));
val oi_obv_thm = save_pop_thm "oi_obv_thm";
=TEX
}%ignore

=GFT
ae_obv_thm = 	A a B ⊢ A e ~ B
ea_obv_thm = 	A e B ⊢ A a ~ B
io_obv_thm = 	A i B ⊢ A o ~ B
oi_obv_thm = 	A o B ⊢ A i ~ B
=TEX

\paragraph{Contraposition and Inversion}

\subsubsection{The Square of Opposition}

This is complete with this semantics.

=GFT
ao_contrad_thm = ⊢ A a B ⇔ ¬ A o B
ei_contrad_thm = ⊢ A e B ⇔ ¬ A i B
ae_contrar_thm = ⊢ ¬ (A a B ∧ A e B)
io_subcont_thm = ⊢ A i B ∨ A o B
ai_subalt_thm = ⊢ A a B ⇒ A i B
eo_subalt_thm = ⊢ A e B ⇒ A o B
=TEX

\ignore{
=SML
val ao_contrad_thm = save_thm ("ao_contrad_thm", syll_rule3 ([], ⌜(A a B) ⇔ ¬ (A o B)⌝));
val ei_contrad_thm = save_thm ("ei_contrad_thm", syll_rule3 ([], ⌜(A e B) ⇔ ¬ (A i B)⌝));

set_goal ([], ⌜¬ (A a B ∧ A e B)⌝);
a (syll_tac3);
val ae_contrar_thm = save_pop_thm "ae_contrar_thm";

set_goal ([], ⌜A i B ∨ A u B⌝);
a (syll_tac3);
val io_subcont_thm = save_pop_thm "io_subcont_thm";

set_goal ([], ⌜A a B ⇒ A i B⌝);
a (syll_tac3);
val ai_subalt_thm = save_pop_thm "ai_subalt_thm";

set_goal ([], ⌜A e B ⇒ A u B⌝);
a (syll_tac3);
val eo_subalt_thm = save_pop_thm "eo_subalt_thm";
=TEX
}%


\subsubsection{The Syllogisms}

First we make a \emph{mapkit}.

=SML
val s3mapkit:mapkit = mkSimpMapkit ⓣTerm2⌝ [⌜$a⌝,⌜$e⌝,⌜$i⌝,⌜$u⌝];
=TEX

Then we apply this in generating and proving the syllogisms.

=SML
proveGoals syll_tac3 "" (mkGoals s3mapkit syllogism_data1);
proveGoals syll_tac3 "" (mkGoals s3mapkit syllogism_data2);
proveGoals syll_tac3 "" (mkGoals s3mapkit syllogism_data3);
=TEX

\ignore{
=IGN
set_goal([], ⌜¬ ∀P M 𝕊⦁ P e M ∧ M i 𝕊 ⇒ 𝕊 o P⌝);
a (REPEAT(POP_ASM_T ante_tac) THEN rewrite_tac (map get_spec [⌜$e⌝, ⌜$i⌝, ⌜$u⌝]));
a contr_tac;
a (LIST_SPEC_NTH_ASM_T 1 [⌜λx⦁ T⌝, ⌜λx⦁ F⌝, ⌜λx⦁ T⌝] ante_tac);
a (rewrite_tac[]);
val ¬_Fresison = save_pop_thm "¬_Fresison";

set_goal([], ⌜¬ ∀P M 𝕊⦁ P i M ∧ M a 𝕊 ⇒ 𝕊 i P⌝);
a (REPEAT(POP_ASM_T ante_tac) THEN rewrite_tac (map get_spec [⌜$e⌝, ⌜$i⌝, ⌜$a⌝]));
a contr_tac;
a (LIST_SPEC_NTH_ASM_T 1 [⌜λx⦁ F⌝, ⌜λx⦁ T⌝, ⌜λx⦁ T⌝] ante_tac);
a (rewrite_tac[]);
val ¬_Dimaris = save_pop_thm "¬_Dimaris";

set_goal([], ⌜¬ ∀P M 𝕊⦁ P a M ∧ M e 𝕊 ⇒ 𝕊 e P⌝);
a (REPEAT(POP_ASM_T ante_tac) THEN rewrite_tac (map get_spec [⌜$e⌝, ⌜$a⌝]));
a contr_tac;
a (LIST_SPEC_NTH_ASM_T 1 [⌜λx⦁ T⌝, ⌜λx⦁ T⌝, ⌜λx⦁ F⌝] ante_tac);
a (rewrite_tac[]);
val ¬_Camenes = save_pop_thm "¬_Camenes";
=TEX
}%ignore

Three of the 24 generally accepted syllogisms prove unsound under this semantics: Camenes, Dimaris and Fresison. 

=GFT
¬_Fresison = ⊢ ¬ (∀ P M 𝕊⦁ P e M ∧ M i 𝕊 ⇒ 𝕊 o P)
¬_Dimaris = ⊢ ¬ (∀ P M 𝕊⦁ P i M ∧ M a 𝕊 ⇒ 𝕊 i P)
¬_Camenes = ⊢ ¬ (∀ P M 𝕊⦁ P a M ∧ M e 𝕊 ⇒ 𝕊 e P)
=TEX

for the record the counterexamples which disprove these syllogisms are all combinations of unversal (U) and empty (E) terms as follows.

=GFT
		P	M	S
Fresison	U	E	U
Dimaris	E	U	U
Camenes	U	U	E
=TEX


The theorems are also displayed in the theory listing in \thyref{syllog5}


\subsection{Existential Import in Affirmations}\label{IEIA}

This is my present best attempt at an interpretation which correponds closely to Aristotle.

=SML
open_theory "aristotle";
force_new_theory "syllog6";
=TEX

\ignore{
=SML
force_new_pc ⦏"'syllog6"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'syllog6";
set_merge_pcs ["misc2", "'syllog6"];
=TEX
}%ignore

\subsubsection{Semantics}

Aristotle's syllogistic logic is concerned with inferences between judgements considered as predications.
A predication in Aristotle affirms a {\it predicate} of some {\it subject}, but by contrast with more recent notions of predication the subject need not be an individual, the kinds of things which appear as predicates may also appear as subjects, and the relationship expressed seems closer to a modern eye to set inclusion than to what we now regard as predication.
Since subject and predicate are for present purposes the same kind of thing, it is useful to have a name for that kind of thing, and I will use the name {\it property}.

There are four kinds of predication which we have here to account for, which we will do by offering definitions which provide a good model for syllogistic logic, i.e. one in which the syllogisms held to be true by Aristotle are in fact true.
Before providing these definitions we must decide what kind of thing are the terms which are related by Aristotelian predication.
 
In HOL the most natural answer to this is ``boolean valued functions'' which are objects of type $ⓣ'a → BOOL⌝$ for some type of individuals which we can leave open by using the type variable $ⓣ'a⌝$.
This provides a simple model of Aristotle's non-u-p syllogistic reasoning.
Four of the syllogisms which Aristotle considered valid fail under this conception of predicate, because among the objects of type $ⓣ'a → BOOL⌝$ is the function $⌜λx:'a⦁ F⌝$ which corresponds to a predicate with empty extension and does not admit inference from the universal to the existential (unless the universal is interpreted specially).

=SML
declare_type_abbrev("Term2", [], ⓣ'a → BOOL⌝);
=TEX

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
│ $⦏a⦎ : Term2 → Term2 → BOOL
├──────
│ ∀A B⦁ A a B ⇔ (∀x⦁ A x ⇒ B x) ∧ ∃x⦁ A x
■

ⓈHOLCONST
│ $⦏e⦎ : Term2 → Term2 → BOOL
├──────
│ ∀A B⦁ A e B ⇔ (∀x⦁ A x ⇒ ¬ B x)
■

ⓈHOLCONST
│ $⦏i⦎ : Term2 → Term2 → BOOL
├──────
│ ∀A B⦁ A i B ⇔ (∃x⦁ A x ∧ B x)
■

ⓈHOLCONST
│ $⦏u⦎ : Term2 → Term2 → BOOL
├──────
│ ∀A B⦁ A u B ⇔ (∃x⦁ A x ∧ ¬ B x) ∨ ¬ (∃x⦁ A x)
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
val ⦏syll_tac6⦎ = asm_prove_tac (map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝]);
fun ⦏syll_rule6⦎ g = tac_proof (g, syll_tac6);	
val ⦏syll_tac6b⦎ = REPEAT (POP_ASM_T ante_tac)
	THEN rewrite_tac (map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝])
	THEN contr_tac THEN asm_fc_tac[];
fun ⦏syll_rule6b⦎ g = tac_proof (g, syll_tac6b);	
=TEX

\paragraph{Simple Conversion}

=SML
val e_conv_thm = save_thm ("e_conv_thm", syll_rule6([⌜A e B⌝], ⌜B e A⌝));
val i_conv_thm = save_thm ("i_conv_thm", syll_rule6([⌜A i B⌝], ⌜B i A⌝));
=TEX

=GFT
val ⦏e_conv_thm⦎ = A e B ⊢ B e A : THM
val ⦏i_conv_thm⦎ = A i B ⊢ B i A : THM
=TEX

\paragraph{Conversion Per Accidens}

These are OK.

=SML
val ai_conv_thm = save_thm ("ai_conv_thm", syll_rule6([⌜A a B⌝], ⌜B i A⌝));
val eo_conv_thm = save_thm ("eo_conv_thm", syll_rule6([⌜A e B⌝], ⌜B u A⌝));
=TEX

=GFT
val ⦏ai_conv_thm⦎ = A a B ⊢ B i A : THM
val ⦏eo_conv_thm⦎ = A e B ⊢ B o A : THM
=TEX

\paragraph{Obversion}

For these we need to define an operation of complementation on terms.

ⓈHOLCONST
│ ⦏Complement⦎ : Term2 → Term2
├──────
│ ∀A α⦁ (Complement A) α ⇔ ¬ (A α) 
■

We will use ``\verb!~!'' as a shorthand for ``Complement''.

=SML
declare_alias ("~", ⌜Complement⌝);
=TEX

\ignore{
=SML
add_pc_thms "'syllog6" [get_spec ⌜Complement⌝];
set_merge_pcs ["misc2", "'syllog6"];
val ⦏syll_tac6b⦎ = REPEAT (POP_ASM_T ante_tac) THEN rewrite_tac (map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝])
	THEN contr_tac THEN asm_fc_tac[];
fun ⦏syll_rule6b⦎ g = tac_proof (g, syll_tac6b);	
=TEX
}%ignore

\ignore{
=SML
val ae_obv_thm = save_thm ("ae_obv_thm", syll_rule6([⌜A a B⌝], ⌜A e ~B⌝));
val iu_obv_thm = save_thm ("iu_obv_thm", syll_rule6b([⌜A i B⌝], ⌜A u ~B⌝));
=TEX
}%ignore

Only two of the obversions are valid.

=GFT
val ae_obv_thm = A a B ⊢ A e ~ B : THM
val iu_obv_thm = A i B ⊢ A o ~ B : THM
=TEX

\subsubsection{The Square of Opposition}

This is complete with this semantics.

=GFT
ao_contrad_thm = ⊢ A a B ⇔ ¬ A o B
ei_contrad_thm = ⊢ A e B ⇔ ¬ A i B
ae_contrar_thm = ⊢ ¬ (A a B ∧ A e B)
io_subcont_thm = ⊢ A i B ∨ A o B
ai_subalt_thm = ⊢ A a B ⇒ A i B
eo_subalt_thm = ⊢ A e B ⇒ A o B
=TEX

\ignore{
=SML
val ao_contrad_thm = save_thm ("ao_contrad_thm", syll_rule6 ([], ⌜(A a B) ⇔ ¬ (A o B)⌝));
val ei_contrad_thm = save_thm ("ei_contrad_thm", syll_rule6 ([], ⌜(A e B) ⇔ ¬ (A i B)⌝));

set_goal ([], ⌜¬ (A a B ∧ A e B)⌝);
a (syll_tac6);
val ae_contrar_thm = save_pop_thm "ae_contrar_thm";

set_goal ([], ⌜A i B ∨ A u B⌝);
a (syll_tac6);
val io_subcont_thm = save_pop_thm "io_subcont_thm";

set_goal ([], ⌜A a B ⇒ A i B⌝);
a (syll_tac6);
val ai_subalt_thm = save_pop_thm "ai_subalt_thm";

set_goal ([], ⌜A e B ⇒ A u B⌝);
a (syll_tac6);
val eo_subalt_thm = save_pop_thm "eo_subalt_thm";
=TEX
}%


\subsubsection{The Syllogisms}

First we make a \emph{mapkit}.

=SML
val s6mapkit:mapkit = mkSimpMapkit ⓣTerm2⌝ [⌜$a⌝,⌜$e⌝,⌜$i⌝,⌜$u⌝];
=TEX

Then we apply this in generating and proving the syllogisms.

=SML
proveGoals syll_tac6 "" (mkGoals s6mapkit syllogism_data1);
proveGoals syll_tac6 "" (mkGoals s6mapkit syllogism_data2);
proveGoals syll_tac6 "" (mkGoals s6mapkit syllogism_data3);
=TEX

The theorems are also displayed in the theory listing in \thyref{syllog6}

\ignore{

\subsection{Reasoning About Semantics}

A shallow embedding is a relatively easy way of interpreting a language so as to get proof support for it using a tool like {\Product}.

Insofar as there is any translation to be done, this is done in our metalanguage Standard ML, but the principle semantic content is rendered through the definition of the constants which correspond to the construtors of the target language, which is done in our object language, which is {\ProductHOL}.
Our metalanguage is purely computational, we cannot prove theorems in the metalanguage.
This means that a shallow embedding is good for reasoning \emph{in} the embedded language, but not good for reasoning \emph{about} it, i.e. not good for metatheory.

If we want to be able to do metatheory, then we model more aspects of the language in our object language.
This gives is a deep embedding (if you want to think in terms of embeddings at all rather than thinking in a more purely metatheoretic way).
In a deep embedding, rather than representing the target language using HOL TERMs which have the same meaning and similar syntax, we chose a representation in HOL of the abstract syntax and define a semantic mapping in HOL, so that we are then able to reason in our object language HOL about the other object language which is the target of our investigation.

If we are heading in this direction there is a further abstraction we can take.
Instead of defining a specific semantic mapping, we can reason generally about the properties of such mappings.
This is analogous to the manner in which Kripke models of modal logics are used.
The semantics is then paramaterised by some accessibility relation over the possible worlds, and one can then establish relationships between the properties satisfied by the accessibilty relation and the theorems which are true in the modal logic (and hence the axioms necessary to provide a complete deductive system).

The principle reason for doing this here, apart from illustrating methods, is so that when we come to treat modal syllogisms we can keep as much as possible of the modelling independent of which particular interpretation of the syllogisms is adopted, and the results will then be more likely to be applicable when the notion of the syllogism is complicated as we venture into metaphysics and distiguish, for example, between accidental and essential predication.

\subsubection{Syntax}

Categorical propositions have a simple structure.
In the simplest presentation they consist of two term variables operated on by one of the operators A, E, I, O.
A more elaborate presentation is desirable when we come to 

}%ignore

\subsection{Modal Syllogisms}\label{MODSYLL}

The language of syllogistic logic does not have operators over propositions.
The only operators are the ones which apply predicates to subjects.

The modalities are perhaps therefore better thought of as kinds of judgements rather than as operations on propositions.
This would give us three kinds of judgement, which assert a predication contingently, necessarily or possibly.

It is natural to consider the modal aspects in terms of possible worlds, and I will model it first in those terms (not knowing whether this will provide a good model of Aristotle's conception of modality).
The propositional functions could then be modelled as functions from possible worlds to non-empty propositional functions.

The following first attempt at a modal syllogism is poorly representative of Aristotle, since, it appears, considered two definitions of possibilty in terms of necessity, but based his work on modal syllogisms primarily on one which does not correspond to the modern usage which is implicit in the treatment given here.
It is to be expected therefore that any examination of the results obtained here will differ from Aristotle's views substantially because of this different conception of necessity.
In due course I will add another kind of modal judgement which will be closer to the one principally investigated by Aristotle.

Aristotle's principle definition of `possibly P' was:
\begin{quote}
not necessarily P and not necessarily not P
\end{quote}

This corresponds more closely with the concept `contingent' or its modern counterpart, `synthetic' than with contemporary usage of `possible', though the contemporary rendering which corresponds to Aristotle's other notion of possibility is a pre-Kripkean one in which we assume a fixed set of possible worlds with modal operators quantifying over the whole.

\ignore{
One respect in which the treatment of the syllogism so far looks odd to the modern eye is the lack of consideration of constants.

We have a language which only has variables, even though Aristotle does use syllogistic reasoning with concrete predicates and subjects.
This lack bevomes more significant when modalities are introduced, for we expect necessities to flow from contraints on the extension of constants which are fixed across the possible worlds (i.e. the meanings of concepts are to be held fixed, even though their extensions may vary across possible worlds).

So I proposed in modelling modal syllogisms to bring the semantics closer to a modern model theory by allowing for constants.
This will be reflected in the definition of ``possible world'' which will include an assignment of values to constants.
}%ignore

I adapt the treatment of u-p syllogisms by treating predicates as parameterised by a possible world.

Rather than using a type variable (which is what I did for the two preceding treatments) I will use two new type constants for individual aubstances and possible worlds.

It may suffice for the reader to refer directly to the theory listing in \thyref{modsyllog}.

=SML
open_theory "aristotle";
force_new_theory "modsyllog";
=TEX

\ignore{
=SML
force_new_pc ⦏"'modsyllog"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'modsyllog";
set_merge_pcs ["misc2", "'modsyllog"];
=TEX
}%ignore

\subsubsection{Semantics}

The complexity required in the semantics of modal operators depends upon other features of the language in which they occur.
Because the language of the syllogism is very simple, having neither propositional operators nor variables for individuals a very simple semantics may suffice.
When we come to consider the metaphyics there will be some increase in the complexity of the other features of the language, and also a greater premium on getting the semantics to correspond intuitively with the content of the metaphysics, but at this stage we will adopt the simplest semantic model which seems likely to secure the results expressible in our restrictied language.

So are now talking about predicates parameterised by possible worlds.
Furthermore, we will model this with a fixed set to individuals, independent of the possible world.
Possible worlds differ only in the extension of predicates.

First some new types, ``I'' for individual substances, ``W'' for possible worlds:

=SML
new_type (⦏"I"⦎,0);
new_type (⦏"W"⦎,0);
=TEX

Then a type abbreviation for the predicates:

=SML
declare_type_abbrev("MPROP", [], ⓣW → I × (I → BOOL)⌝);
=TEX

\subsubsection{Predication}

To work with this new type for the predicates we define a function which will convert this kind of predicate into the old kind, as follows:

ⓈHOLCONST
│ ⦏p⦎ : MPROP → (W → I → BOOL)
├──────
│ ∀A⦁ p A = λw x⦁ let (v,f) = A w in x = v ∨ f x
■

The following principle can be proven (proof omitted):

\ignore{
=SML
set_goal([], ⌜∀A w⦁ ∃v⦁ (p A) w v⌝);
a (REPEAT ∀_tac);
a (∃_tac ⌜Fst (A w)⌝ THEN rewrite_tac [get_spec ⌜p⌝, let_def]);
val p_∃_lemma = save_pop_thm "p_∃_lemma";
=TEX
}%ignore

=GFT
p_∃_lemma =
	⊢ ∀ A w⦁ ∃ v⦁ p A w v
=TEX

This principle is what we need to prove the u-p syllogisms.

We then proceed in a similar manner to the other models, using the function $p$ to convert the new kind of predicate into the old.

They predication operators are then defined.
Note that the differences are small and uniform.
The type $ⓣTerm3⌝$ is changed to $ⓣMPROP⌝$ and the function $p$ is invoked before applying a predicate.

Now we think of a predication as being a set of possible worlds, or BOOLean valued function over possible worlds.

=SML
declare_infix (300, "a");
declare_infix (300, "e");
declare_infix (300, "i");
declare_infix (300, "u");
=TEX

ⓈHOLCONST
│ $⦏a⦎ : MPROP → MPROP → W → BOOL
├──────
│ ∀A B w⦁ (A a B) w ⇔ ∀x⦁ p A w x ⇒ p B w x
■

ⓈHOLCONST
│ $⦏e⦎ : MPROP → MPROP → W → BOOL
├──────
│ ∀A B w⦁ (A e B) w ⇔ ∀x⦁ p A w x ⇒ ¬ p B w x
■

ⓈHOLCONST
│ $⦏i⦎ : MPROP → MPROP → W → BOOL
├──────
│ ∀A B w⦁ (A i B) w ⇔ ∃x⦁ p A w x ∧ p B w x
■

ⓈHOLCONST
│ $⦏u⦎ : MPROP → MPROP → W → BOOL
├──────
│ ∀A B w⦁ (A u B) w ⇔ ∃x⦁ p A w x ∧ ¬ p B w x
■

=SML
declare_alias("o", ⌜$u⌝);
=TEX

We now have to define some additional constants for the forms of judgement, which will assert the predications either of the actual world or of some or all possible worlds.

First I define a constant (rather loosely) to be the actual world:

ⓈHOLCONST
│ ⦏actual_world⦎ : W
├──────
│ T
■

Then the two modal judgement forms:

ⓈHOLCONST
│ ⦏♢⦎ : (W → BOOL) → BOOL
├──────
│ ∀s⦁ ♢ s ⇔ ∃w⦁ s w
■
□
ⓈHOLCONST
│ ⦏□⦎ : (W → BOOL) → BOOL
├──────
│ ∀s⦁ □ s ⇔ ∀w⦁ s w
■

Aristotle's other notion of possibility is:

ⓈHOLCONST
│ ⦏♢⋎a⦎ : (W → BOOL) → BOOL
├──────
│ ∀s⦁ ♢⋎a s ⇔ ¬ (∀w⦁ s w) ∧ ¬ (∀w⦁ ¬ s w)
■

Finally the non-modal judgements also need a judgement forming constant.

ⓈHOLCONST
│ ⦏Ξ⦎ : (W → BOOL) → BOOL
├──────
│ ∀s⦁ Ξ s ⇔ s actual_world
■

Special difficulties are raised by reasoning with $♢⋎a$ and to help with these difficulties it is useful to have negation as a kind of propositional operator in this modal logic.

=SML
declare_prefix (350, "¬⋎m");
=TEX

ⓈHOLCONST
│ $⦏¬⋎m⦎ : (W → BOOL) → (W → BOOL)
├──────
│ ∀x⦁ ¬⋎m x = λw⦁ ¬ (x w)
■

Though this constant is distinct from the non-modal negation, we might as well drop the subscript where no ambiguity arises.

=SML
declare_alias ("¬", ⌜$¬⋎m⌝);
=TEX

\subsubsection{Laws of Immediate Inference}

Before looking at the conversions there are some general rules which may be helpful for us though these probably are not in Aristotle.

\ignore{
=SML
set_goal([⌜□X⌝], ⌜♢X⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜□⌝, get_spec ⌜♢⌝, get_spec ⌜Ξ⌝]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
val □♢_thm = save_pop_thm "□♢_thm";

set_goal([⌜□X⌝], ⌜ΞX⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜□⌝, get_spec ⌜♢⌝, get_spec ⌜Ξ⌝]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
val □Ξ_thm = save_pop_thm "□Ξ_thm";

set_goal([⌜ΞX⌝], ⌜♢X⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜□⌝, get_spec ⌜♢⌝, get_spec ⌜Ξ⌝]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜actual_world⌝ THEN strip_tac);
val Ξ♢_thm = save_pop_thm "Ξ♢_thm";

set_goal([⌜♢⋎a X⌝], ⌜♢X⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜□⌝, get_spec ⌜♢⌝, get_spec ⌜♢⋎a⌝, get_spec ⌜Ξ⌝]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜w'⌝ THEN strip_tac);
val ♢⋎a♢_thm = save_pop_thm "♢⋎a♢_thm";

set_goal([⌜♢⋎a X⌝], ⌜¬□X⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [get_spec ⌜□⌝, get_spec ⌜♢⌝, get_spec ⌜♢⋎a⌝, get_spec ⌜Ξ⌝]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜w⌝ THEN strip_tac);
val ♢⋎a¬□_thm = save_pop_thm "♢⋎a¬□_thm";

set_goal([], ⌜♢⋎a X ⇔ ♢⋎a (¬⋎m X)⌝);
a (rewrite_tac [get_spec ⌜♢⋎a⌝, get_spec ⌜$¬⋎m⌝]
	THEN prove_tac[]);
val ♢⋎a¬⋎m_thm = save_pop_thm "♢⋎a¬⋎m_thm";
=TEX
}%ignore

=GFT
□♢_thm = 	□ X ⊢ ♢ X
□Ξ_thm = 		□ X ⊢ Ξ X
Ξ♢_thm = 		Ξ X ⊢ ♢ X
♢⋎a♢_thm =	♢⋎a X ⊢ ♢ X
♢⋎a¬□_thm =	♢⋎a X ⊢ ¬ □ X
♢⋎a¬⋎m_thm =	⊢ ♢⋎a X ⇔ ♢⋎a (¬⋎m X)
=TEX

\paragraph{Simple Conversion}

\ignore{
=SML
set_goal([⌜Ξ (A e B)⌝], ⌜Ξ(B e A)⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac (map get_spec [⌜Ξ⌝, ⌜$e⌝])
	THEN contr_tac);
a (asm_fc_tac[]);
val e_conv_thm = save_pop_thm "e_conv_thm";

set_goal([⌜Ξ (A i B)⌝], ⌜Ξ(B i A)⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac (map get_spec [⌜Ξ⌝, ⌜$i⌝])
	THEN contr_tac);
a (asm_fc_tac[]);
val i_conv_thm = save_pop_thm "i_conv_thm";

set_goal([⌜□ (A e B)⌝], ⌜□(B e A)⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac (map get_spec [⌜□⌝, ⌜$e⌝])
	THEN contr_tac);
a (asm_fc_tac[]);
val □e_conv_thm = save_pop_thm "□e_conv_thm";

set_goal([⌜□ (A i B)⌝], ⌜□(B i A)⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac (map get_spec [⌜□⌝, ⌜$i⌝])
	THEN contr_tac);
a (asm_fc_tac[]);
a (spec_nth_asm_tac 2 ⌜w⌝);
a (asm_fc_tac[]);
val □i_conv_thm = save_pop_thm "□i_conv_thm";

set_goal([⌜♢ (A e B)⌝], ⌜♢(B e A)⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac (map get_spec [⌜♢⌝, ⌜$e⌝])
	THEN contr_tac);
a (spec_nth_asm_tac 1 ⌜w⌝);
a (asm_fc_tac[]);
val ♢e_conv_thm = save_pop_thm "♢e_conv_thm";

set_goal([⌜♢ (A i B)⌝], ⌜♢(B i A)⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac (map get_spec [⌜♢⌝, ⌜$i⌝])
	THEN contr_tac);
a (spec_nth_asm_tac 1 ⌜w⌝);
a (asm_fc_tac[]);
val ♢i_conv_thm = save_pop_thm "♢i_conv_thm";

set_goal([⌜♢⋎a (A e B)⌝], ⌜♢⋎a (B e A)⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac (map get_spec [⌜♢⋎a⌝, ⌜□⌝, ⌜$e⌝])
	THEN contr_tac);
a (asm_fc_tac[]);
a (spec_nth_asm_tac 1 ⌜w':W⌝);
a (asm_fc_tac[]);
val ♢⋎a_e_conv_thm = save_pop_thm "♢⋎a_e_conv_thm";

set_goal([⌜♢⋎a (A i B)⌝], ⌜♢⋎a (B i A)⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac (map get_spec [⌜♢⋎a⌝, ⌜$i⌝])
	THEN contr_tac);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 1 ⌜w:W⌝);
a (spec_nth_asm_tac 6 ⌜x'⌝);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 1 ⌜w':W⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
val ♢⋎a_i_conv_thm = save_pop_thm "♢⋎a_i_conv_thm";

set_goal([], ⌜♢⋎a (A a B) ⇔ ♢⋎a (A u B)⌝);
a (rewrite_tac (map get_spec [⌜♢⋎a⌝, ⌜□⌝, ⌜$a⌝, ⌜$u⌝])
	THEN prove_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜w':W⌝ THEN asm_prove_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜w:W⌝ THEN asm_prove_tac[]);
val ♢⋎a_ao_conv_thm = save_pop_thm "♢⋎a_ao_conv_thm";

set_goal([], ⌜♢⋎a (A e B) ⇔ ♢⋎a (A i B)⌝);
a (rewrite_tac (map get_spec [⌜♢⋎a⌝, ⌜□⌝, ⌜$e⌝, ⌜$i⌝])
	THEN prove_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜w':W⌝ THEN asm_prove_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜w:W⌝ THEN asm_prove_tac[]);
val ♢⋎a_ei_conv_thm = save_pop_thm "♢⋎a_ei_conv_thm";

set_goal([⌜□ (A e B)⌝], ⌜♢(B e A)⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac (map get_spec [⌜♢⌝, ⌜□⌝, ⌜$e⌝])
	THEN contr_tac);
a (spec_nth_asm_tac 1 ⌜w:W⌝);
a (asm_fc_tac[]);
val □♢e_conv_thm = save_pop_thm "□♢e_conv_thm";

set_goal([⌜□ (A e B)⌝], ⌜Ξ(B e A)⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac (map get_spec [⌜Ξ⌝, ⌜□⌝, ⌜$e⌝])
	THEN contr_tac);
a (asm_fc_tac[]);
val □Ξe_conv_thm = save_pop_thm "□Ξe_conv_thm";
=TEX
}%ignore

=GFT
e_conv_thm = Ξ (A e B) ⊢ Ξ (B e A)
i_conv_thm = Ξ (A i B) ⊢ Ξ (B i A)
□e_conv_thm = □ (A e B) ⊢ □ (B e A)
□i_conv_thm = □ (A i B) ⊢ □ (B i A)
♢e_conv_thm = ♢ (A e B) ⊢ ♢ (B e A)
♢i_conv_thm = ♢ (A i B) ⊢ ♢ (B i A)
♢⋎a_e_conv_thm = ♢⋎a (A e B) ⊢ ♢⋎a (B e A)
♢⋎a_i_conv_thm = ♢⋎a (A i B) ⊢ ♢⋎a (B i A)
♢⋎a_ao_conv_thm = ⊢ ♢⋎a (A a B) ⇔ ♢⋎a (A o B)
♢⋎a_ei_conv_thm = ⊢ ♢⋎a (A e B) ⇔ ♢⋎a (A i B)
□♢e_conv_thm = □ (A e B) ⊢ ♢ (B e A)
□Ξe_conv_thm = □ (A e B) ⊢ Ξ (B e A)
=TEX

In this version of the semantics, ``a'' and ``o'' conversion is neither provable nor refutable.
In the previous version (the one not admitting the u-p syllogisms), since the universe is a HOL type there is at least one individual, and contradictory predicates are allowed, we can use these two to disprove the two conversions.
With this semantics there is no empty predicate, and we cannot know that there are two distinct predicates.

\paragraph{Conversion Per Accidens}

\ignore{
=SML
set_goal([⌜Ξ (A a B)⌝], ⌜Ξ (B i A)⌝);
a (REPEAT (POP_ASM_T ante_tac) THEN rewrite_tac (map get_spec [⌜♢⌝, ⌜□⌝, ⌜Ξ⌝, ⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝])
	THEN contr_tac THEN asm_fc_tac[]);
a (strip_asm_tac (list_∀_elim [⌜A⌝, ⌜actual_world⌝] p_∃_lemma));
a (asm_fc_tac[]);
val Ξai_conv_thm = save_pop_thm "Ξai_conv_thm";

set_goal([⌜Ξ (A e B)⌝], ⌜Ξ (B u A)⌝);
a (REPEAT (POP_ASM_T ante_tac) THEN rewrite_tac (map get_spec [⌜♢⌝, ⌜□⌝, ⌜Ξ⌝, ⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝])
	THEN contr_tac THEN asm_fc_tac[]);
a (strip_asm_tac (list_∀_elim [⌜B⌝, ⌜actual_world⌝] p_∃_lemma));
a (spec_nth_asm_tac 2 ⌜v⌝);
a (asm_fc_tac[]);
val Ξeo_conv_thm = save_pop_thm "Ξeo_conv_thm";

set_goal([⌜□ (A a B)⌝], ⌜♢ (B i A)⌝);
a (REPEAT (POP_ASM_T ante_tac) THEN rewrite_tac (map get_spec [⌜♢⌝, ⌜□⌝, ⌜Ξ⌝, ⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝])
	THEN contr_tac THEN asm_fc_tac[]);
a (strip_asm_tac (list_∀_elim [⌜A⌝, ⌜actual_world⌝] p_∃_lemma));
a (asm_fc_tac[]);
val □♢ai_conv_thm = save_pop_thm "□♢ai_conv_thm";

set_goal([⌜□ (A e B)⌝], ⌜♢ (B u A)⌝);
a (REPEAT (POP_ASM_T ante_tac) THEN rewrite_tac (map get_spec [⌜♢⌝, ⌜□⌝, ⌜Ξ⌝, ⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝])
	THEN contr_tac THEN asm_fc_tac[]);
a (strip_asm_tac (list_∀_elim [⌜B⌝, ⌜actual_world⌝] p_∃_lemma));
a (spec_nth_asm_tac 2 ⌜actual_world⌝);
a (spec_nth_asm_tac 1 ⌜v⌝);
a (asm_fc_tac[]);
val □♢eo_conv_thm = save_pop_thm "□♢eo_conv_thm";
=TEX
}%ignore

=GFT
Ξai_conv_thm = 	Ξ (A a B) ⊢ Ξ (B i A)
Ξeo_conv_thm = 	Ξ (A e B) ⊢ Ξ (B o A)
□♢ai_conv_thm = 	□ (A a B) ⊢ ♢ (B i A)
□♢eo_conv_thm = 	□ (A e B) ⊢ ♢ (B o A)
=TEX

\subsubsection{The Valid Modal Syllogisms}

The valid syllogisms have been described in Section \ref{syllogisms}.

All nineteen syllogisms supposed valid by Aristotle are true under this semantics and have been proven.
A further five\footnote{Which I got from Strawson \cite{strawson52}.} have also been proven, giving a total of 24.
When combinations of modal operators are added to this the number gets quite large, so, rather than proving all the valid cases I will prove sufficient to enable the rest to be automatically proven.

This will involve some theorems which are not strictly syllogistic.

The actual theorems proved are shown in the theory listing in \thyref{modsyllog}.

Because of the modal operators the generation of the syllogisms is more complicated.
The generation functions are adapted to allow a single modal operator to be applied to each of the premises and the conclusion.



=SML
fun ⦏mk_pred⦎ q s p = mk_app(mk_app (q, s), p);

fun ⦏mk_syll⦎ vt (a,b,c,d) (q1, q2, q3) =
	([mk_pred q1 a b, mk_pred q2 c d],
		mk_pred q3 (mk_var("𝕊", vt)) (mk_var("P", vt)));

fun ⦏mk_relt⦎ t = mk_ctype ("→", [t, mk_ctype ("→", [t, ⓣBOOL⌝])]);

fun ⦏mk_syllp⦎ vt (s, n) =
	mk_syll vt (nth (n-1) (figurest vt)) (optrip_from_text (mk_relt vt) s);
=IGN
val ⦏mk_syllp1⦎ = mk_syllp ⓣTERM⌝;
=SML
fun ⦏syll_prove⦎ msp suff tac (a,n) =
	let val thm = tac_proof (msp (a,n), tac) handle _ => t_thm
	in (concat [a, suff], thm)
	end;

fun ⦏syll_prove_and_store⦎ msp suff tac (a,n) =
	let val res = syll_prove msp suff tac (a,n);
	    val _ = save_thm res
	in res 
	end;
=TEX

=SML
fun ⦏map_goal⦎ f (st, t) = (map f st, f t);

fun ⦏mk_modt⦎ vt = mk_ctype ("→", [vt,
	mk_ctype ("→", [vt, (mk_ctype ("→", [ⓣW⌝, ⓣBOOL⌝]))])]);

fun ⦏mk_modsyll⦎ vt (s, n) =
	mk_syll vt (nth (n-1) (figurest vt)) (optrip_from_text (mk_modt vt) s);

fun ⦏modgoal⦎ (mo1, mo2, mo3) ([p1,p2], c) =
	([mk_app (mo1, p1), mk_app (mo2, p2)], mk_app (mo3, c));

fun ⦏mk_modsyllp⦎ mot p = modgoal mot (mk_modsyll ⓣMPROP⌝ p);
=TEX

This defines the function {\it mk\_modsyllp} whose type is shown:

=GFT
val mk_modsyllp = fn: TERM * TERM * TERM -> string * int -> TERM list * TERM
=TEX

in which the {\it TERM} parameters are modal operators the next argument is a pair consisting of a string which is the name of a syllogism and a number which is the number of the figure.
The result is a goal for proof.

An example of its use is:

=SML
mk_modsyllp (⌜□⌝,⌜Ξ⌝,⌜♢⌝) ("Barbara", 1);
=TEX

which yields:

=GFT
val it = ([⌜□ (M a P)⌝, ⌜□ (𝕊 a M)⌝], ⌜□ (𝕊 a P)⌝) : TERM list * TERM
=TEX

\subsubsection{General Results}

The logic of the modal operators is completely independent of the logic of the syllogism.
The relevant results can be stated and proven in HOL concisely, but these statements are not in the language of the syllogism.

There are in effect just seven modal truths, each of which appears in 24 forms, one for each of the valid non-modal syllogisms.

Rather than proving all 192 theorems (counting the non-modal truths in this modal model), I prove the eight proformas expressed in HOL.
From these eight all 192 theorems can be obtained by proving (a special form of) one of the valid syllogisms and instantiating one of the general modal rules using it.

I omit the details of the metalanguage scripts which automate all this.

\ignore{
To get the required general results we define a new kind of pseudo-judgement `G' (for general).

=SML
val G = ⌜(λx:W → BOOL⦁ x w)⌝;
val GS = ⌜∀w:W⦁ ⓜG⌝ FP ∧ ⓜG⌝ SP ⇒ ⓜG⌝ CS⌝;
fun modal_generalisation (a,b,c) =
	⌜∀FP SP CS⦁ ⓜGS⌝ ⇒ (ⓜa⌝ FP) ∧ (ⓜb⌝ SP) ⇒ (ⓜc⌝ CS)⌝;
=TEX

=SML
mk_modsyllp (G,G,G) ("Barbara", 1);
val general_syllogs = map ((map_goal (snd o dest_eq o concl o rewrite_conv[]))
			o (mk_modsyllp (G,G,G)))
	(syllogism_data1 @ syllogism_data2 @ syllogism_data3);
=TEX


=SML
fun AW_COND_T tac (asms, conc) =
	if snd (dest_app conc) = ⌜actual_world⌝
	then tac ⌜actual_world⌝ (asms, conc)
	else tac ⌜w:W⌝ (asms, conc);

val mod_gen_tac = REPEAT ∀_tac
	THEN rewrite_tac (map get_spec [⌜♢⌝, ⌜□⌝, ⌜Ξ⌝])
	THEN REPEAT strip_tac
	THEN (AW_COND_T (fn x => REPEAT
		(((SPEC_NTH_ASM_T 1 x ante_tac) ORELSE_T (GET_NTH_ASM_T 1 ante_tac))
			THEN POP_ASM_T discard_tac)))
	THEN REPEAT strip_tac
	THEN_TRY ∃_tac ⌜w:W⌝
	THEN REPEAT strip_tac;

fun mod_gen_rule t = tac_proof(([],t), mod_gen_tac);
=TEX
}%ignore

The following lists the valid modal forms.
In each tuple the three entries give the modalities of the first and second premise and the conclusion respectively.
Taking any valid syllogism and applying modal operators using one of the patterns in this table will give a valid modal syllogism.

=SML
val mod_gen_params =
	[(⌜□⌝, ⌜□⌝, ⌜□⌝),
	 (⌜□⌝, ⌜□⌝, ⌜♢⌝),
	 (⌜□⌝, ⌜□⌝, ⌜Ξ⌝),
	 (⌜♢⌝, ⌜□⌝, ⌜♢⌝),
	 (⌜□⌝, ⌜♢⌝, ⌜♢⌝),
	 (⌜□⌝, ⌜Ξ⌝, ⌜Ξ⌝),
	 (⌜Ξ⌝, ⌜□⌝, ⌜Ξ⌝),
	 (⌜Ξ⌝, ⌜Ξ⌝, ⌜Ξ⌝)];
=TEX

\ignore{
=SML
val mod_gen_terms = map modal_generalisation mod_gen_params;

val mod_gens = map mod_gen_rule mod_gen_terms;

fun mod_gen_name (x,y,z) = concat
	(["mod_gen_"] @ [fst (dest_const x), fst (dest_const y), fst (dest_const z)]);

val mod_gen_thms = map
	(save_thm o (fn x => (mod_gen_name x, rewrite_rule [] (mod_gen_rule (modal_generalisation x)))))
	mod_gen_params;
=TEX
}%ignore

The set of general HOL theorems which facilitate the proofs of these modal syllogisms is as follows:

=GFT ProofPower Theorems
val mod_gen_thms =
   [⊢ ∀ FP SP CS⦁ (∀ w⦁ FP w ∧ SP w ⇒ CS w) ⇒ □ FP ∧ □ SP ⇒ □ CS,
      ⊢ ∀ FP SP CS⦁ (∀ w⦁ FP w ∧ SP w ⇒ CS w) ⇒ □ FP ∧ □ SP ⇒ ♢ CS,
      ⊢ ∀ FP SP CS⦁ (∀ w⦁ FP w ∧ SP w ⇒ CS w) ⇒ □ FP ∧ □ SP ⇒ Ξ CS,
      ⊢ ∀ FP SP CS⦁ (∀ w⦁ FP w ∧ SP w ⇒ CS w) ⇒ ♢ FP ∧ □ SP ⇒ ♢ CS,
      ⊢ ∀ FP SP CS⦁ (∀ w⦁ FP w ∧ SP w ⇒ CS w) ⇒ □ FP ∧ ♢ SP ⇒ ♢ CS,
      ⊢ ∀ FP SP CS⦁ (∀ w⦁ FP w ∧ SP w ⇒ CS w) ⇒ □ FP ∧ Ξ SP ⇒ Ξ CS,
      ⊢ ∀ FP SP CS⦁ (∀ w⦁ FP w ∧ SP w ⇒ CS w) ⇒ Ξ FP ∧ □ SP ⇒ Ξ CS,
      ⊢ ∀ FP SP CS⦁ (∀ w⦁ FP w ∧ SP w ⇒ CS w) ⇒ Ξ FP ∧ Ξ SP ⇒ Ξ CS]
: THM list
=TEX

In the above theorems the variables {\it FP}, {\it SP}, {\it CS}, stand respectively for {\it first premise}, {\it second premise}, {\it conclusion of syllogism} and range over modal propositions (which have type ⓣW → BOOL⌝).

\subsubsection{Proving the Syllogisms}

I then prove the 24 non-modal syllogisms in the required form and infer forward using the above 8 theorems to obtain a total of 192 theorems true in this model of the modal syllogism.

Details of scripts omitted.

\ignore{
=SML
fun ⦏modsps⦎ mods = syll_prove (mk_modsyllp mods);
fun ⦏valid_modsylls⦎ mods suff tac = map (modsps mods suff tac)
	(syllogism_data1 @ syllogism_data2 @ syllogism_data3);
=TEX

The same tactic used for proof of the syllogisms in the previous model still works with this model (with the new definitions), but does not prove the u-p syllogisms.

To obtain proofs of these other syllogisms we need to make use of the lemma we proved about $p$, {\it p\_∃\_lemma}.
This we do by instantiating it for each of the variables which appear in the syllogisms and supplying these for use in the proof.

=SML
val ⦏modsyll_G_tac⦎ =
	(MAP_EVERY strip_asm_tac
		(map (fn x => (list_∀_elim [x, ⌜w:W⌝] p_∃_lemma))
		[⌜M:MPROP⌝, ⌜P:MPROP⌝, ⌜𝕊:MPROP⌝])
	THEN (asm_prove_tac (map get_spec [⌜$a⌝, ⌜$e⌝, ⌜$i⌝, ⌜$u⌝])));

fun ⦏modsyll_G_rule⦎ g = tac_proof(g, modsyll_G_tac);
=TEX

I just run this over a few combinations of modal operators to see which it will prove.

=SML
val valid_G_modsylls1 = valid_modsylls (G,G,G) "" modsyll_G_tac;
val valid_G_modsylls2 = map
	((∀_intro ⌜w:W⌝)
		o (rewrite_rule [prove_rule [] ⌜∀A B C⦁ (A ⇒ B ⇒ C) ⇔ (A ∧ B ⇒ C)⌝])
		o (rewrite_rule [])
		o all_⇒_intro
		o snd)
	valid_G_modsylls1;

val valid_G_modsylls = map (undisch_rule
		o undisch_rule
		o (rewrite_rule [prove_rule [] ⌜∀A B C⦁ (A ∧ B ⇒ C) ⇔ (A ⇒ B ⇒ C)⌝])
		o all_∀_elim)
	(fc_rule mod_gen_thms valid_G_modsylls2);
=TEX
}%ignore

The automated proof the yields the expected 192 modal syllogisms, of which we display only the first few (and do not save them in the theory):

=GFT
val valid_G_modsylls =
   [Ξ (P a M), Ξ (M e 𝕊) ⊢ Ξ (𝕊 o P), Ξ (P a M), □ (M e 𝕊) ⊢ Ξ (𝕊 o P),
      □ (P a M), Ξ (M e 𝕊) ⊢ Ξ (𝕊 o P), □ (P a M), ♢ (M e 𝕊) ⊢ ♢ (𝕊 o P),
      ♢ (P a M), □ (M e 𝕊) ⊢ ♢ (𝕊 o P), □ (P a M), □ (M e 𝕊) ⊢ Ξ (𝕊 o P),
      □ (P a M), □ (M e 𝕊) ⊢ ♢ (𝕊 o P), □ (P a M), □ (M e 𝕊) ⊢ □ (𝕊 o P),
      Ξ (P a M), Ξ (𝕊 e M) ⊢ Ξ (𝕊 o P), Ξ (P a M), □ (𝕊 e M) ⊢ Ξ (𝕊 o P),
      □ (P a M), Ξ (𝕊 e M) ⊢ Ξ (𝕊 o P), □ (P a M), ♢ (𝕊 e M) ⊢ ♢ (𝕊 o P),
      ♢ (P a M), □ (𝕊 e M) ⊢ ♢ (𝕊 o P), □ (P a M), □ (𝕊 e M) ⊢ Ξ (𝕊 o P),
      □ (P a M), □ (𝕊 e M) ⊢ ♢ (𝕊 o P), □ (P a M), □ (𝕊 e M) ⊢ □ (𝕊 o P),
      Ξ (P e M), Ξ (𝕊 a M) ⊢ Ξ (𝕊 o P), Ξ (P e M), □ (𝕊 a M) ⊢ Ξ (𝕊 o P),
      □ (P e M), Ξ (𝕊 a M) ⊢ Ξ (𝕊 o P), □ (P e M), ♢ (𝕊 a M) ⊢ ♢ (𝕊 o P),
...
=TEX

=SML
length valid_G_modsylls;
=GFT
val it = 192 : int
=TEX
=TEX

\subsection{Demonstrative Truth}

An important part of Aristotle's philosophy is his concept of demonstrative science.

A proof is demonstrative if it proceeds from first principles and is deductively sound.
Truths established in this way are necessary because the first principles must be essential and hence necessary and sound deduction preserves necessity.

If we understand Hume's ``intuitively certain'' as a reference to the criteria for Aristotle's first principles, and understand Hume as using the term `demonstrative' in the same sense as Aristotle, then it is plausible that Hume's ``truths of reason'' are the same as Aristotle's truths of demonstrative science.

It is tempting to use the word demonstrative for `truths of reason' though in Aristotle and Hume the first principles do not count as demonstrable.
This follows modern logic in using concepts such as `theorem' and `valid sentence' which apply to logical axioms as well as results deduced from them. 
It is tempting also to identify these concepts with the concept of analyticity.
This last point is aided by the connection in Aristotle between essential truth (which must be posessed by the first principles) and definition, which seems close, and which distinguishes his accidental predications from essential predications.
A weak point in this is the question of the first principles of the various sciences, and the doubts one can reasonably have about whether Aristotle's essential truth must be analytic.

However, we now expect deductive systems to be incomplete, and hence that not all analytic propositions are provable.
However, the incompleteness may arise from adopting a fixed set of first principles, rather from incompleteness of deduction.
In this case, the availability of an open set of first principles makes completeness in principle possible.
To sustain this principle in relation to set theory, for example, we would have to regard ourselves as having some definition of the concept of set relative to which the present axioms (say those of ZFC) are essential, and relative to which extensions as necessary to prove progressively more difficult results can also be seen to be essential.
This is not entirely implausible.
This is close to the rationale for large cardinal axioms.
The informal description of the cumulative hierarchy as the domain of set theory involves the idea that the construction of well-founded sets from other well-founded sets of lesser rank proceeds indefinitely, and hence any axiom which states that a set of a certain rank exists must be true.

Does formal modelling contribute anything to this discussion?

The above discussion involves ideas which belong to Aristotle's metaphysics rather than his logic.
So a fuller formal analysis of these ideas will have to wait until we get to the Metaphysics.

However some aspects may be considered here.
For example, we need to know that from necessary premises only necessary premises are derivable by syllogisms.

\section{Metaphysics (II)}\label{METAPHYSICSII}

In this section I offer a single model integrating Modal Syllogisms with the distinction between essential and accidental predication.

My interest is primarily in the extent to which may be found in Aristotle's philosophy a precursor of Hume's fork or the modern distinctions between analytic and synthetic or necessary and contingent propositions.
I see three Aristotelian ideas which have some relevance.

\begin{itemize}
\item the distinction between necessary and contingent propositions
\item the distinction between essential and accidental predication
\item the notion of demonstrability
\end{itemize}

It is only when we combine the syllogism with the metaphyics that we can explore the relationship between these various concepts.

I will give higher priority in this model to good structure while remaining faithful to Aristotle.
It is not the purpose of this model to further investigate the position in relation to Aristotle of Grice, Codd or Speranza.

I have constructed this model to give a good correspondence between necessary truth and essential predication.
If the model is successful in that respect it remains to consider whether it is consistent with the philosophy of Aristotle.
I do not know whether Aristotle talked about the relationship between essence and necessity.

I also hope that the model may help to explore the question of whether demonstrable truth, or rather the truths which are either ``intuitively or demonstrably certain'' to use Hume's words, coincides with necessary truth.

=SML
open_theory "aristotle";
force_new_theory "syllmetap";
=TEX

\ignore{
=SML
force_new_pc ⦏"'syllmetap"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'syllmetap";
set_merge_pcs ["misc2", "'syllmetap"];
=TEX
}%ignore

\subsection{Semantics}

In my first metaphysical model the main question in relations to subject matter was ``what are subjects and predicates'', to which a model of Aristotelian categories gives an answer.
The introduction of modality makes it necessary to consider something like possible worlds.
These were left uninterpreted in the modal treatment of the syllogism, but now that we expose the distinction between essential and accidental predication is it desirable to identify possible worlds with that which is accidental.

What is accidental is the extension of individual attributes, and this gives our concept of possible world.

It is convenient at this point to consider the question of extensionality.

According to Grice/Codd/Speranza, essential predicates are extensional:

=INLINEFT
              A izz B ∧ B izz A ⇒ A = B
=TEX


but I know no reason to suppose that accidental predication is, and it seems counter-intuitive that it should be.
Consequently the modelling of an accidental predicate using a BOOLean valued function in HOL (in which functions are extensional) is inappropriate.
So I will separate out the extension from the individual attribute.

Individuals belong to categories, and are collected together in groups which determine the nature of essential predication within that category.
The simplest way of getting the right structure is to use some type of tags to differentiate individuals within a category, using the same collection of tags in each category (with the unintended effect of ensuring that each category has the same number of individuals, which I hope will have a significant effect on the resulting theory).
The individuals are then represented by an ordered pair consisting of a category and a tag.

For most purposes the number of categories is not important, though we must have a category of substances, so a completely undifferentiated new type might have sufficed.
However, it turns out that some things don't work, and its useful to have at least one non-substantial category in order to prove that they don't work.
So I introduce a new type of non-substantial (attribute) categories (so we get at least one) and then make the type of categories by adding one more.

=SML
new_type ("ACAT", 0);
new_type ("TAG", 0);
=TEX

=SML
declare_type_abbrev("CAT", [], ⓣONE+ACAT⌝);
=TEX

One of the categories will be the category of substance, it doesn't matter which one but we might as well use the odd One on the left of the sum (so you can test for substance using {\it IsL}).

ⓈHOLCONST
│ ⦏Category_of_Substance⦎ : CAT
├──────
│ Category_of_Substance = InL One
■

An individual will therefore be modelled as an ordered pair consisting of a tag and a category.
This is captured by the following type abbreviation.

=SML
declare_type_abbrev ("I", [], ⓣCAT × TAG⌝);
=TEX

A possible world is then an assignment of extensions to individual attributes, where an extension is a set of particulars.
Since we only want individual attributes, we do not use type {\it I} for the domain.
Particulars always belong to the category of substance, so we only need a set of tags in the result, the category is implicit.

=SML
declare_type_abbrev ("W", [], ⓣACAT × TAG → TAG SET⌝);
=TEX

This does include an assignement of extensions to particulars, but this plays no role, only intefering with the identity criteria for possible worlds, which do not feature in the theory.

I need to distinguish one possible world which is the actual world:

ⓈHOLCONST
│ ⦏actual_world⦎ : W
├──────
│ T
■

Since the individuals are pairs it might be handy to have appropriately named projection funtions which extract the two components:

ⓈHOLCONST
│ ⦏category⦎ : I → CAT;
│ ⦏tag⦎ : I → TAG
├──────
│ ∀ct⦁	category ct = Fst ct
│   ∧	tag ct = Snd ct 
■

Finally the question of what subjects and predicates are can be determined.
I will call them {\it TermM}s and they are either a set of particulars or a set of attributes.
To allow for complementation I add a boolean component, which if true indicates a complement.

The sets in this case must be non-empty if we are to retain the u-p syllogisms (in default of a different universal).
The method used in my model of the modal syllogism in Section \ref{MODSYLL} will not do here, because (at least according to Code) we need an extensionality result, so I have instead introduced
\footnote{The definition has been placed in a separate document, \cite{rbjt006}.}
 for this purpose a new type ({\it NESET}) of non-empty sets which will give us both the u-p syllogisms and extensionality (for essential predication, not for accidental predication).

A term is therefore modelled as either a non-empty set of individual substances or a non-empty set of individual attributes.

=SML
declare_type_abbrev (⦏"TermM"⦎, [], ⓣ(CAT × TAG NESET)⌝);
=TEX

ⓈHOLCONST
│ ⦏mk_SubsTerm⦎ : TAG ℙ → TermM
├──────
│ ∀s⦁ mk_SubsTerm s = (Category_of_Substance, NeSet s)
■

ⓈHOLCONST
│ ⦏mk_AttrTerm⦎ : CAT × TAG ℙ → TermM
├──────
│ ∀s⦁ mk_AttrTerm s = (Fst s, NeSet (Snd s))
■

It may be useful to have a name for the predicate encompassing all substance.

ⓈHOLCONST
│ ⦏Substance⦎ : TermM
├──────
│ Substance = mk_SubsTerm Universe
■

\subsection{Predication}

The syllogism comes with four kinds of predication (a, e, i, o), and the metaphysics with three (izz, hazz and izz or hazz).
Combining these would give twelve combinations.

To simplify a bit I will separate out the quantifier but defining {\it All} and {\it Some} appropriately, and provide a postfix negator for izz an hazz.

I will then treat the modal operators as operators over propositions, and introduce the syllogism as a kind of judgement.

The type of the primitive copulas is:

=SML
declare_type_abbrev("COPULA", [], ⓣI → TermM → (W → BOOL)⌝);
=TEX

The first parameter is an individual substance or attribute rather than a TermM, the quantifying operator will arrange for each of the relevant individuals or attributes to be supplied.

\paragraph{Propositions}

=SML
declare_type_abbrev ("MPROP", [], ⓣW → BOOL⌝);
=TEX

\paragraph{Complementation}

The distinction between affirmative and negative is achieved by a postfix negation so we can say ``izz not'', ``hazz not'' or ``are not''.

=SML
declare_postfix (100, "not");
=TEX

ⓈHOLCONST
│ $⦏not⦎ : COPULA → COPULA
├──────
│ ∀pred⦁ pred not = λpa t w⦁ ¬ pred pa t w 
■

\paragraph{Quantifiers}

The following function is used by both quantifiers to check if something is in the range of quantification.

Think of a TermM as denoting a set of individuals, this is a test for membership of that set.
The complications are because substances and attributes have different types in this model.

=SML
declare_infix(300, "InTermM");
=TEX

ⓈHOLCONST
│ $⦏InTermM⦎ : I → TermM → BOOL
├──────
│ ∀ c1t c2ts ⦁ c1t InTermM c2ts ⇔ Fst c1t = Fst c2ts ∧ Snd c1t ∈ PeSet (Snd c2ts)
■

=GFT
interm_∃_lemma =
	⊢ ∀ t⦁ ∃ j⦁ j InTermM t
=TEX

\ignore{
=SML
set_goal([], ⌜∀t⦁ ∃j⦁ j InTermM t⌝);
a (strip_tac);
a (∃_tac ⌜(Fst t, MemOf (Snd t))⌝ THEN rewrite_tac[get_spec ⌜$InTermM⌝]);
val interm_∃_lemma = save_pop_thm "interm_∃_lemma";
=TEX
}%ignore

We then use that membership test in defining the quantifiers.
The quantifiers expect to be supplied with a copula and a term.
The quantifier then predicates using the copula the term of everything or something in the domain of quantification (which is the subject term).
The copulas are defined below.

=IGN
declare_prefix(400, "All");
declare_prefix(400, "Some");
=TEX

ⓈHOLCONST
│ ⦏All⦎ : TermM → (I → TermM → MPROP) → TermM → MPROP
├──────
│ ∀ s r p⦁ All s r p = λw⦁ ∀z⦁ z InTermM s ⇒ r z p w
■

ⓈHOLCONST
│ ⦏Some⦎ : TermM → (I → TermM → MPROP) → TermM → MPROP
├──────
│ ∀ s r p⦁ Some s r p = λw⦁ ∃z⦁ z InTermM s ∧ r z p w
■

\paragraph{Predicators}

For essential predication it is necessary that the individual and the predicate are both of the same category and then reduces under our model to set membership.
In effect. since the non-substantial individuals are tagged with their category, we need only deal separately with the distinction between substantial and non-substantial and the set inclusion will ensure a match in the non-substantial categories.

ⓈHOLCONST
│ ⦏izz⦎ : I → TermM → MPROP
├──────
│ ∀ j t⦁ izz j t = λw⦁ j InTermM t
■

For accidental predication the subject term must be substantial and the predicate may not be.
We then need some member of the predicate to be attributable to the substance.

ⓈHOLCONST
│ ⦏hazz⦎ : I → TermM → MPROP
├──────
│ ∀ c1t c2ts⦁ hazz c1t c2ts = λw⦁
│	Fst c1t = Category_of_Substance
│ ∧ 	¬ Fst c2ts = Category_of_Substance
│ ∧	(∃b⦁ b ∈ PeSet (Snd c2ts) ∧ (Snd c1t) ∈ w (OutR(Fst c2ts), b))
■

=GFT
not_izz_and_hazz_lemma1 =
	⊢ ∀ pa t w⦁ ¬ (izz pa t w ∧ hazz pa t w)
=TEX

\ignore{
=SML
set_goal([], ⌜∀pa t w⦁ ¬ (izz pa t w ∧ hazz pa t w)⌝);
a (rewrite_tac [get_spec ⌜$izz⌝, get_spec ⌜$hazz⌝, get_spec ⌜$InTermM⌝]);
a (contr_tac);
a (DROP_NTH_ASM_T 4 ante_tac THEN asm_rewrite_tac[]);
val not_izz_and_hazz_lemma1 = save_pop_thm "not_izz_and_hazz_lemma1";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏are⦎ : I → TermM → MPROP
├──────
│ ∀ pa t⦁ are pa t = λw⦁ izz pa t w ∨ hazz pa t w	
■

=GFT
⦏are_izz_neq_hazz_lemma⦎ =
	⊢ ∀ pa t w⦁ are pa t w ⇔ ¬ (izz pa t w ⇔ hazz pa t w)

⦏All_are_izz_or_hazz_lemma⦎ =
	⊢ ∀ A B w⦁ All A are B w ⇔ All A izz B w ∨ All A hazz B w

⦏Some_are_izz_or_hazz_lemma⦎ =
	⊢ ∀ A B w⦁ Some A are B w ⇔ Some A izz B w ∨ Some A hazz B w

⦏All_are_not_lemma⦎ =
	⊢ ∀ A B w ⦁ All A (are not) B w ⇔ All A (izz not) B w ∧ All A (hazz not) B w
=TEX

\ignore{
=SML
set_goal([], ⌜∀pa t w⦁ are pa t w ⇔ ¬ (izz pa t w ⇔ hazz pa t w)⌝);
a (rewrite_tac [get_spec ⌜$are⌝]);
a (REPEAT ∀_tac);
a (cond_cases_tac ⌜izz pa t w⌝ THEN contr_tac);
a (asm_tac not_izz_and_hazz_lemma1 THEN asm_fc_tac[]);
val are_izz_neq_hazz_lemma = save_pop_thm "are_izz_neq_hazz_lemma";
=TEX
}%ignore

\ignore{
=SML
set_goal([], ⌜∀A B w ⦁ (All A are B) w ⇔ (All A izz B w ∨ (All A hazz B) w)⌝);
a (REPEAT ∀_tac);
a (rewrite_tac [get_spec ⌜are⌝, get_spec ⌜All⌝, get_spec ⌜$InTermM⌝, ext_thm]);
a (contr_tac THEN_TRY asm_rewrite_tac[] THEN_TRY all_asm_fc_tac[]);
a (POP_ASM_T (strip_asm_tac o (rewrite_rule [get_spec ⌜$hazz⌝])));
a (spec_nth_asm_tac 11 ⌜z'⌝);
a (POP_ASM_T (strip_asm_tac o (rewrite_rule [get_spec ⌜$izz⌝])));
a (POP_ASM_T (strip_asm_tac o (rewrite_rule [get_spec ⌜$InTermM⌝])));
a (lemma_tac ⌜Fst B = Fst A⌝ THEN1 SYM_ASMS_T rewrite_tac);
a (lemma_tac ⌜Fst B = Category_of_Substance⌝ THEN1 SYM_ASMS_T rewrite_tac);
a (REPEAT_N 9 (POP_ASM_T discard_tac) THEN asm_rewrite_tac[]);
val All_are_izz_or_hazz_lemma = save_pop_thm "All_are_izz_or_hazz_lemma";

set_goal([], ⌜∀A B w ⦁ (Some A are B) w ⇔ (Some A izz B w ∨ (Some A hazz B) w)⌝);
a (REPEAT ∀_tac);
a (rewrite_tac [get_spec ⌜are⌝, get_spec ⌜Some⌝, get_spec ⌜$InTermM⌝, ext_thm]);
a (contr_tac THEN_TRY asm_rewrite_tac[] THEN_TRY all_asm_fc_tac[]);
val Some_are_izz_or_hazz_lemma = save_pop_thm "Some_are_izz_or_hazz_lemma";

set_goal([], ⌜∀A B w ⦁ (All A (are not) B) w ⇔ (All A (izz not) B w ∧ (All A (hazz not) B) w)⌝);
a (REPEAT ∀_tac);
a (rewrite_tac [get_spec ⌜are⌝, get_spec ⌜All⌝, get_spec ⌜$InTermM⌝, get_spec ⌜$not⌝, ext_thm]);
a (contr_tac THEN_TRY asm_rewrite_tac[] THEN_TRY all_asm_fc_tac[]);
val All_are_not_lemma = save_pop_thm "All_are_not_lemma";
=TEX
}%ignore

\paragraph{Modal Operators}

In this model the model operators are operators over propositions.

ⓈHOLCONST
│ ⦏♢⦎ : MPROP → MPROP
├──────
│ ∀p⦁ ♢ p = λw⦁ ∃w'⦁ p w' 
■

ⓈHOLCONST
│ ⦏□⦎ : MPROP → MPROP
├──────
│ ∀p⦁ □ p = λw⦁ ∀w'⦁ p w' 
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
│ $⦏∀⋎a⦎ : (TermM → MPROP) → MPROP
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
│ $⦏∃⋎a⦎ : (TermM → MPROP) → MPROP
├──────
│ ∀mpf⦁ $∃⋎a mpf = λw⦁ ∃t⦁ mpf t w
■
=SML
declare_alias ("∃", ⌜$∃⋎a⌝);
=TEX
⊢
\subsection{Judgements}

I'm not yet clear what to offer here, so for the present I will define two kinds of sequent, which will be displayed with the symbols $⊢$ asnd $⊨$. the former being a kind of contingent material implication and the latter a necessary implication.

Both form of judgement seem suitable for expressing the rules of the syllogism at first glance but which can also be used for conversions.

The first expresses a contingent entailment, that if some arbitrary finite (possibly empty) collection of premises are contingently true, then some conclusion will also be true.
Since the consequence is material, and the premisses might be contingent, the conclusion might also be contingent.
One might hope that if the rules of the syllogism are applied and the premises are necessary, then so will be the conclusions. 

=SML
declare_infix(100, "⊢");
=TEX

ⓈHOLCONST
│ $⦏⊢⦎ : MPROP LIST → MPROP → BOOL
├──────
│ ∀lp c⦁ lp ⊢ c ⇔ Fold (λp t⦁ p actual_world ∧ t) lp T ⇒ c actual_world
■

This one says that in every possible world the premises entail the conclusion (still material).

=SML
declare_infix(100, "⊨");
=TEX

ⓈHOLCONST
│ $⦏⊨⦎ : MPROP LIST → MPROP → BOOL
├──────
│ ∀lp c⦁ lp ⊨ c ⇔ ∀w⦁ Fold (λp t⦁ p w ∧ t) lp T ⇒ c w
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
⦏izz_not_lemma⦎ =
	⊢ All B (izz not) A = All A (izz not) B
⦏some_izz_lemma⦎ =
	⊢ Some B izz A = Some A izz B
=TEX

These we also supply as our Aristotelian judgements, together with the second which does not give an equation.
The second conversion embodies the u-p syllogisms.

=GFT
⦏izz_conv1⦎ = ⊢
	[All B (izz not) A] ⊨ All A (izz not) B

⦏izz_conv2⦎ = ⊢
	[All B izz A] ⊨ Some A izz B

⦏izz_conv3⦎ = ⊢
	[Some B izz A] ⊨ Some A izz B
=TEX

\ignore{
=SML
set_goal([], ⌜All B (izz not) A = All A (izz not) B⌝);
a (rewrite_tac [ext_thm]);
a (strip_tac THEN rewrite_tac [get_spec ⌜All⌝]);
a (contr_tac);
(* *** Goal "1" *** *)
a (POP_ASM_T (strip_asm_tac o (rewrite_rule (map get_spec [⌜izz⌝, ⌜$not⌝]))));
a (asm_fc_tac[]);
a (POP_ASM_T (strip_asm_tac o (rewrite_rule (map get_spec [⌜izz⌝, ⌜$not⌝]))));
val izz_not_lemma = save_pop_thm "izz_not_lemma";

set_goal([], ⌜Some B izz A = Some A izz B⌝);
a (rewrite_tac [ext_thm]);
a (strip_tac THEN rewrite_tac (map get_spec [⌜Some⌝, ⌜izz⌝]));
a (contr_tac);
a (spec_nth_asm_tac 1 ⌜z⌝);
val some_izz_lemma = save_pop_thm "some_izz_lemma";

set_goal([], ⌜[All B (izz not) A] ⊨ All A (izz not) B⌝);
a (rewrite_tac (map get_spec [⌜$⊨⌝, ⌜$⇔⋎a⌝]));
a (strip_tac THEN rewrite_tac [get_spec ⌜Fold⌝, get_spec ⌜All⌝, izz_not_lemma]);
val izz_conv1 = save_pop_thm "izz_conv1";

set_goal([], ⌜[All B izz A] ⊨  Some A izz B⌝);
a (rewrite_tac (map get_spec [⌜$⊨⌝]));
a (strip_tac THEN rewrite_tac [get_spec ⌜Fold⌝, get_spec ⌜All⌝, get_spec ⌜Some⌝, get_spec ⌜izz⌝, get_spec ⌜$InTermM⌝]);
a (REPEAT strip_tac);
a (∃_tac ⌜(Fst B, MemOf (Snd B))⌝ THEN asm_rewrite_tac[]);
a (SPEC_NTH_ASM_T 1 ⌜(Fst B, MemOf (Snd B))⌝ (rewrite_thm_tac o (rewrite_rule[])));
val izz_conv2 = save_pop_thm "izz_conv2";

set_goal([], ⌜[Some B izz A] ⊨  Some A izz B⌝);
a (rewrite_tac (map get_spec [⌜$⊨⌝]));
a (strip_tac THEN rewrite_tac [get_spec ⌜Fold⌝, get_spec ⌜Some⌝, get_spec ⌜izz⌝, get_spec ⌜$InTermM⌝]);
a (REPEAT strip_tac);
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
a (SYM_ASMS_T rewrite_tac);
val izz_conv3 = save_pop_thm "izz_conv3";
=TEX
}%ignore

Now we look at {\it hazz}.

The following theorems state that the two equational conversions are both false for {\it hazz}.

=GFT
⦏not_hazz_not_lemma⦎ =
	⊢ ¬ (∀ A B⦁ All B (hazz not) A = All A (hazz not) B)

⦏not_some_hazz_lemma⦎ =
	⊢ ¬ (∀ A B⦁ Some B hazz A = Some A hazz B)
=TEX

Aristotle's second conversion also fails for {\it hazz}, because in incorporates an application of the third in effect.
If we simplify by removing the final flip we get:

=GFT
⦏hazz_conv2⦎ =
	⊢ [All A hazz B] ⊨ Some A hazz B
=TEX

\ignore{
=SML
set_goal([], ⌜¬ ∀A B⦁ All B (hazz not) A = All A (hazz not) B⌝);
a (strip_tac);
a (∃_tac ⌜(Category_of_Substance, εs:TAG NESET⦁T)⌝ THEN strip_tac);
a (∃_tac ⌜(InR (εs:ACAT⦁T), εs:TAG NESET⦁T)⌝);
a (rewrite_tac [ext_thm, get_spec ⌜All⌝, get_spec ⌜hazz⌝, get_spec ⌜$not⌝, get_spec ⌜$InTermM⌝]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜λw:ACAT×TAG⦁ Universe⌝ THEN rewrite_tac [] THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜(Category_of_Substance, MemOf(ε s⦁ T))⌝ THEN rewrite_tac [] THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (rewrite_tac [get_spec ⌜Category_of_Substance⌝]);
val not_hazz_not_lemma = save_pop_thm "not_hazz_not_lemma";

set_goal([], ⌜¬ ∀A B⦁ Some B hazz A = Some A hazz B⌝);
a (strip_tac);
a (∃_tac ⌜(Category_of_Substance, εs:TAG NESET⦁T)⌝ THEN strip_tac);
a (∃_tac ⌜(InR (εs:ACAT⦁T), εs:TAG NESET⦁T)⌝);
a (rewrite_tac [ext_thm, get_spec ⌜Some⌝, get_spec ⌜hazz⌝, get_spec ⌜$InTermM⌝]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜λw:ACAT×TAG⦁ Universe⌝ THEN rewrite_tac [] THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (∃_tac ⌜(Category_of_Substance, MemOf(ε s⦁ T))⌝ THEN rewrite_tac [] THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (rewrite_tac [get_spec ⌜Category_of_Substance⌝]);
val not_some_hazz_lemma = save_pop_thm "not_some_hazz_lemma";

set_goal([], ⌜[All A hazz B] ⊨  Some A hazz B⌝);
a (rewrite_tac (map get_spec [⌜$⊨⌝]));
a (strip_tac THEN rewrite_tac [get_spec ⌜Fold⌝, get_spec ⌜All⌝, get_spec ⌜Some⌝, get_spec ⌜hazz⌝, get_spec ⌜$InTermM⌝]);
a (REPEAT strip_tac);
a (∃_tac ⌜(Fst A, MemOf (Snd A))⌝ THEN asm_rewrite_tac[]);
a (SPEC_NTH_ASM_T 1 ⌜(Fst A, MemOf (Snd A))⌝ (rewrite_thm_tac o (rewrite_rule[])));
val hazz_conv2 = save_pop_thm "hazz_conv2";
=TEX
}%ignore

Since {\it is} is the conjunction of {\it izz} and {\it hazz} it is likely that it would yeild similar results to {\it hazz}.

\subsection{Modal Conversions}

\paragraph{Prior Analytics Book 1 Part 3}

See: \href{http://texts.rbjones.com/rbjpub/philos/classics/aristotl/o3103c.htm}{Universal and Possible Premisses and their Conversions}.

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
⦏♢_conv⦎ =
	⊢ [P] ⊨ Q ⇒ [♢ P] ⊨ ♢ Q

⦏□_conv⦎ =
	⊢ [P] ⊨ Q ⇒ [□ P] ⊨ □ Q
=TEX

\ignore{
=SML
set_goal([], ⌜[P] ⊨ Q ⇒ [♢ P] ⊨ ♢ Q⌝);
a (rewrite_tac (map get_spec [⌜$⊨⌝, ⌜Fold⌝, ⌜♢⌝]));
a (REPEAT strip_tac);
a (∃_tac ⌜w'⌝ THEN asm_fc_tac[]);
val ♢_conv = save_pop_thm "♢_conv";

set_goal([], ⌜[P] ⊨ Q ⇒ [□ P] ⊨ □ Q⌝);
a (rewrite_tac (map get_spec [⌜$⊨⌝, ⌜Fold⌝, ⌜□⌝]));
a (REPEAT strip_tac);
a (asm_ufc_tac[] THEN asm_rewrite_tac[]);
val □_conv = save_pop_thm "□_conv";
=TEX
}%ignore

=GFT
⦏□_izz_thm⦎ = ⊢ [□ (All A izz B)] ⊢ All A izz B
⦏□_hazz_thm⦎ = ⊢ [□ (All A hazz B)] ⊢ All A izz B
⦏izz_□_thm⦎ = ⊢ [All A izz B] ⊢ □ (All A izz B)
⦏not_□_hazz_thm⦎ = ⊢ [] ⊢ (¬ □ (All A hazz B))

⦏□_izz_thm2⦎ = ⊢ [□ (All A izz B)] ⊨ All A izz B
⦏□_hazz_thm2⦎ = ⊢ [□ (All A hazz B)] ⊨ All A izz B
⦏izz_□_thm2⦎ = ⊢ [All A izz B] ⊨ □ (All A izz B)
⦏not_□_hazz_thm2⦎ = ⊢ [] ⊨ (¬ □ (All A hazz B))
=TEX

$□\_hazz\_thm$ is a bit odd.
Really what I wanted to prove was that no accidental predication is necessary, but I have no negation in the syllogism, so I just proved that if an accidental predication were necessary then it would be essential.
Then I went back and defined negation so permitting a direct denial that any accidental predication is necessary.

There are many theorems which one would naturally prove at this point, to facilitate further proofs and proof automation, which are not expressible syllogistically.
Proof automation depends heavily on the demonstration of equations, so that proof may proceed by rewriting.
But syllogisms are not suitable for this.

The natural way to proceed in such a case is to continue in this theory doing things which support proofs of syllogisms without being restrained to syllogisms, and then to have a separate theory in which the syllogistic claims are presented.
Some reflection is desirable on what the philosophical objectives are and what course will best contribute to those purposes.

\ignore{
=SML
set_goal([], ⌜[□ (All A izz B)] ⊢ All A izz B⌝);
a (rewrite_tac  (map get_spec [⌜$⊢⌝, ⌜Fold⌝, ⌜□⌝, ⌜All⌝, ⌜izz⌝])
	THEN REPEAT strip_tac);
val □_izz_thm = save_pop_thm "□_izz_thm";

set_goal([], ⌜[□ (All A hazz B)] ⊢ All A izz B⌝);
a (rewrite_tac  (map get_spec [⌜$⊢⌝, ⌜Fold⌝])
	THEN REPEAT strip_tac);
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac (map get_spec [⌜□⌝, ⌜All⌝, ⌜hazz⌝])
	THEN strip_tac);
a (∃_tac ⌜λw⦁ {}⌝ THEN rewrite_tac[get_spec ⌜$InTermM⌝] THEN strip_tac);
a (lemma_tac ⌜∃d⦁ d ∈ PeSet (Snd A)⌝ THEN1 rewrite_tac[]);
a (∃_tac ⌜(Fst A, d)⌝ THEN asm_rewrite_tac[]);
val □_hazz_thm = save_pop_thm "□_hazz_thm";

set_goal([], ⌜[All A izz B] ⊢ □ (All  A izz B)⌝);
a (rewrite_tac  (map get_spec [⌜$⊢⌝, ⌜Fold⌝, ⌜□⌝, ⌜All⌝, ⌜izz⌝])
	THEN REPEAT strip_tac);
val izz_□_thm = save_pop_thm "izz_□_thm";

set_goal([], ⌜[] ⊢ ¬ □ (All A hazz B)⌝);
a (rewrite_tac  (map get_spec [⌜$⊢⌝, ⌜Fold⌝, ⌜□⌝, ⌜All⌝, ⌜izz⌝, ⌜$¬⋎a⌝, ⌜hazz⌝]));
a (REPEAT strip_tac);
a (∃_tac ⌜λw⦁ {}⌝ THEN rewrite_tac[get_spec ⌜$InTermM⌝] THEN strip_tac);
a (∃_tac ⌜(Fst A, MemOf(Snd A))⌝ THEN rewrite_tac[]);
val not_□_hazz_thm = save_pop_thm "not_□_hazz_thm";

set_goal([], ⌜[□ (All A izz B)] ⊨ All A izz B⌝);
a (rewrite_tac  (map get_spec [⌜$⊨⌝, ⌜Fold⌝, ⌜□⌝, ⌜All⌝, ⌜izz⌝])
	THEN REPEAT strip_tac);
val □_izz_thm2 = save_pop_thm "□_izz_thm2";

set_goal([], ⌜[□ (All A hazz B)] ⊨ All A izz B⌝);
a (rewrite_tac  (map get_spec [⌜$⊨⌝, ⌜Fold⌝])
	THEN REPEAT strip_tac);
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac (map get_spec [⌜□⌝, ⌜All⌝, ⌜hazz⌝])
	THEN strip_tac);
a (∃_tac ⌜λw⦁ {}⌝ THEN rewrite_tac[get_spec ⌜$InTermM⌝] THEN strip_tac);
a (lemma_tac ⌜∃d⦁ d ∈ PeSet (Snd A)⌝ THEN1 rewrite_tac[]);
a (∃_tac ⌜(Fst A, d)⌝ THEN asm_rewrite_tac[]);
val □_hazz_thm2 = save_pop_thm "□_hazz_thm2";

set_goal([], ⌜[All A izz B] ⊨ □ (All  A izz B)⌝);
a (rewrite_tac  (map get_spec [⌜$⊨⌝, ⌜Fold⌝, ⌜□⌝, ⌜All⌝, ⌜izz⌝])
	THEN REPEAT strip_tac);
val izz_□_thm2 = save_pop_thm "izz_□_thm2";

set_goal([], ⌜[] ⊨ ¬ □ (All A hazz B)⌝);
a (rewrite_tac  (map get_spec [⌜$⊨⌝, ⌜Fold⌝, ⌜□⌝, ⌜All⌝, ⌜izz⌝, ⌜$¬⋎a⌝, ⌜hazz⌝]));
a (REPEAT strip_tac);
a (∃_tac ⌜λw⦁ {}⌝ THEN rewrite_tac[get_spec ⌜$InTermM⌝] THEN strip_tac);
a (∃_tac ⌜(Fst A, MemOf(Snd A))⌝ THEN rewrite_tac[]);
val not_□_hazz_thm2 = save_pop_thm "not_□_hazz_thm2";
=TEX
}%ignore

Here are some general modal results which I have not noticed in Aristotle as yet.

=GFT
⦏□_elim_thm⦎ =
	⊢ [□ P] ⊢ P
⦏♢_intro_thm⦎ =
	⊢ [P] ⊢ ♢ P
⦏□_♢_thm⦎ =
	⊢ [□ P] ⊢ ♢ P
=TEX

\ignore{
=SML
set_goal([], ⌜[□ P] ⊢ P⌝);
a (rewrite_tac (map get_spec [⌜$⊢⌝, ⌜Fold⌝, ⌜$□⌝]) THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
val □_elim_thm = save_pop_thm "□_elim_thm";

set_goal([], ⌜[P] ⊢ ♢ P⌝);
a (rewrite_tac (map get_spec [⌜$⊢⌝, ⌜Fold⌝, ⌜$♢⌝]) THEN contr_tac THEN asm_fc_tac[]);
val ♢_intro_thm = save_pop_thm "□_intro_thm";

set_goal([], ⌜[□ P] ⊢ ♢ P⌝);
a (rewrite_tac (map get_spec [⌜$⊢⌝, ⌜Fold⌝, ⌜$□⌝, ⌜$♢⌝]) THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
val □_♢_thm = save_pop_thm "□_♢_thm";
=TEX
}%ignore

\subsection{Other Conversions}

The following conversions relate to the square of opposition, but I have not yet discovered where they appear in Aristotle.
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

Normally theorems like this would be proved closed, but it looks more Aristotelian without the quantifiers and we can imagine that they are schemata.
To use them it will usually be desirable to close them, which is easily done, e.g.:

=SML
all_∀_intro ¬_Some_not_conv_thm;
=TEX

=GFT ProofPower output
val it = ⊢ ∀ A cop B⦁ (¬ Some A (cop not) B) = All A cop B : THM
=TEX

\subsection{Syllogisms for Essential Predication}

Though the usual syllogisms are not valid for predication in general, the problems are confined to accidental predication.
We can, by methods similar to those used above obtain automatic proofs of the 24 valid syllogisms restricted to essential predication.

The details are omitted, but the 24 izz syllogisms have been proven and stored in the theory, see: \thyref{syllmetap}.

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
fun ⦏mk_izz_syll⦎ vt (a, b, c, d) (f1, f2, f3) =
	⌜[ⓜf1 a b⌝; ⓜf2 c d⌝] ⊨
		ⓜf3 (mk_var("𝕊", vt)) (mk_var("P", vt))⌝⌝;

fun ⦏mk_cop_syllp⦎ cop (s, n) =
	([], mk_izz_syll ⓣTermM⌝ (nth (n-1) (figurest ⓣTermM⌝)) (opfuntrip_from_text cop s));

fun ⦏mk_cop_syllp_cc⦎ cc (s, n) =
	([], mk_izz_syll ⓣTermM⌝ (nth (n-1) (figurest ⓣTermM⌝)) (opfuntrip_from_text_cc cc s));

fun ⦏mk_izz_syllp⦎ (s, n) = mk_cop_syllp ⌜izz⌝ (s, n);

fun ⦏mk_izzhazz_syllp⦎ (s, n) = mk_cop_syllp_cc (⌜izz⌝, ⌜hazz⌝) (s, n);
fun ⦏mk_hazzizz_syllp⦎ (s, n) = mk_cop_syllp_cc (⌜hazz⌝, ⌜izz⌝) (s, n);

val ⦏syll_izz_tac2⦎ =
	(MAP_EVERY (fn x => strip_asm_tac (∀_elim x interm_∃_lemma))
		[⌜M:TermM⌝, ⌜P:TermM⌝, ⌜𝕊:TermM⌝, ⌜A:TermM⌝, ⌜B:TermM⌝])
	THEN asm_prove_tac (map get_spec [⌜$⊨⌝, ⌜All⌝, ⌜Some⌝, ⌜izz⌝, ⌜$not⌝, ⌜Fold⌝]);

val ⦏syll_izzhazz_tac⦎ =
	(MAP_EVERY (fn x => strip_asm_tac (∀_elim x interm_∃_lemma))
		[⌜M:TermM⌝, ⌜P:TermM⌝, ⌜𝕊:TermM⌝, ⌜A:TermM⌝, ⌜B:TermM⌝])
	THEN rewrite_tac (map get_spec [⌜$⊨⌝, ⌜All⌝, ⌜Some⌝, ⌜izz⌝, ⌜hazz⌝, ⌜$not⌝, ⌜Fold⌝])
	THEN contr_tac;

val ⦏syll_izzhazz_tac2⦎ = 	syll_izzhazz_tac
	THEN (REPEAT_N 3 (asm_fc_tac[]));

fun ⦏syll_izz_rule2⦎ g = tac_proof(g, syll_izz_tac2);

fun ⦏syll_izzhazz_rule2⦎ g = tac_proof(g, syll_izzhazz_tac2);

val ⦏sps_izz1⦎ = syll_prove_and_store mk_izz_syllp "_izz";
val ⦏sps_izzhazz1⦎ = syll_prove_and_store mk_izzhazz_syllp "_ih";
val ⦏sps_hazzizz1⦎ = syll_prove_and_store mk_hazzizz_syllp "_hi";

val ⦏valid_izz_sylls⦎ = map (sps_izz1 syll_izz_tac2)
	(syllogism_data1 @ syllogism_data2 @ syllogism_data3);
=IGN
(*
val ⦏valid_izzhazz_sylls⦎ = map (sps_izzhazz1 syll_izzhazz_tac2)
	(syllogism_data1 @ syllogism_data2 @ syllogism_data3);
*)
val ⦏valid_hazzizz_sylls⦎ = map (sps_hazzizz1 syll_izzhazz_tac2)
	(syllogism_data1 @ syllogism_data2 @ syllogism_data3);

set_goal(mk_izzhazz_syllp ("Barbara", 1));
a syll_izzhazz_tac;
(* *** Goal "1" *** *)
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (asm_fc_tac[]);
a (DROP_NTH_ASM_T 12 (strip_asm_tac o (rewrite_rule [get_spec ⌜$InTermM⌝])));


a (contr_tac THEN REPEAT_N 3 (asm_fc_tac[]));

=TEX

}%ignore

\subsection{Some Accidental Syllogisms}

\ignore{
=SML
=TEX
}%ignore

=GFT
=TEX

\subsection{Grice and Code}

I now review the Grice/Code analysis under the revised interpretation of {\it izz} and {\it hazz}.

On my first attempt I did not notice till rather late that the material covered both Aristotle's and Plato's metaphysics, which are not wholly compatible.
To do this using only conservative extension we have to use a different context for the parts of the treatment which might be incompatible.
Three new theories will therefore be introduced, respectively covering:

\begin{itemize}
\item[gccom] material common to Aristotle and Plato
\item[gcaris] material specific to Aristotle
\item[gcplato] material specific to Plato
\end{itemize}

All three theories are in the context of theory {\it syllmetap} which is an integrated model of both the modal syllogism and the metaphysics, incorporating the u-p syllogisms, which makes slightly more sense in the context of the metaphysics than otherwise.

\subsubsection{Common Material}

=SML
force_new_theory "gccon";
=TEX

The following results are now provable:

=GFT
⦏FP1⦎ =	⊢ [] ⊨ All A izz A 
⦏FP2⦎ =	⊢ [All A izz B; All B izz C] ⊨ All A izz C
⦏FP3⦎ =	⊢ [All A hazz B] ⊨ ¬ (All A izz B)
⦏FP4a⦎ =	⊢ [All A hazz B; All B izz C] ⊨ All A hazz C
⦏FP4⦎ =	⊢ [] ⊨ All A hazz B ⇔ (∃⋎a C⦁ All A hazz C ∧ All C izz B)
=TEX

These are not very Aristotelian.
It would seem more Aristotelian to have:

=GFT
⦏FP3b⦎ =
	⊢ [All A hazz B] ⊨ Some A (izz not) B
=TEX

\ignore{
=SML
set_goal([], ⌜[] ⊨ All A izz A⌝);
a (syll_izz_tac2);
val FP1 = save_pop_thm "FP1";

set_goal([], ⌜[All A izz B; All B izz C] ⊨ All A izz C⌝);
a (syll_izz_tac2);
val FP2 = save_pop_thm "FP2";

val ⦏syll_hizz_tac⦎ =
	(MAP_EVERY (fn x => strip_asm_tac (∀_elim x interm_∃_lemma))
		[⌜M:TermM⌝, ⌜P:TermM⌝, ⌜𝕊:TermM⌝, ⌜A:TermM⌝, ⌜B:TermM⌝])
	THEN asm_prove_tac (map get_spec [⌜$⊨⌝, ⌜All⌝, ⌜Some⌝, ⌜izz⌝, ⌜hazz⌝, ⌜$not⌝, ⌜$¬⋎a⌝, ⌜Fold⌝]);


set_goal([], ⌜[All A hazz B] ⊨ ¬ All A izz B⌝);
a (syll_hizz_tac);
a (asm_fc_tac[]);
a (∃_tac ⌜j'''⌝ THEN asm_rewrite_tac[get_spec ⌜$InTermM⌝]);
a (swap_nth_asm_concl_tac 2 THEN asm_rewrite_tac[]);
val FP3 = save_pop_thm "FP3";

val FP3b = save_thm("FP3b", rewrite_rule [all_∀_intro ¬_All_conv_thm] FP3);

set_goal([], ⌜[All A hazz B; All B izz C] ⊨ All A hazz C⌝);
a (rewrite_tac (map get_spec [⌜$⊨⌝, ⌜Fold⌝, ⌜All⌝, ⌜izz⌝, ⌜hazz⌝]) THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [get_spec ⌜$InTermM⌝])));
a (asm_fc_tac[]);
a (SPEC_NTH_ASM_T 5 ⌜(Fst B, b)⌝ (strip_asm_tac o (rewrite_rule[])));
a (swap_nth_asm_concl_tac 4 THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule [get_spec ⌜$InTermM⌝])));
a (asm_fc_tac[]);
a (SPEC_NTH_ASM_T 5 ⌜(Fst B, b)⌝ (strip_asm_tac o (rewrite_rule[])));
a (∃_tac ⌜b⌝ THEN (SYM_ASMS_T rewrite_tac));
val FP4a = save_pop_thm "FP4a";


set_goal([], ⌜[] ⊨ (All A hazz B ⇔ ∃ C⦁ (All A hazz C) ∧ (All C izz B))⌝);
a (rewrite_tac (map get_spec [⌜$⊨⌝, ⌜Fold⌝, ⌜$⇔⋎a⌝, ⌜$∃⋎a⌝, ⌜$∧⋎a⌝]) THEN REPEAT_N 3 strip_tac);
(* *** Goal "1" *** *)
a (strip_tac THEN ∃_tac ⌜B⌝ THEN asm_rewrite_tac[all_∀_intro (rewrite_rule (map get_spec [⌜$⊨⌝, ⌜Fold⌝]) FP1)]);
(* *** Goal "2" *** *)
a (rewrite_tac (map get_spec [⌜All⌝, ⌜izz⌝, ⌜hazz⌝]) THEN strip_tac);
a (POP_ASM_T (strip_asm_tac o (rewrite_rule [get_spec ⌜$InTermM⌝])));
a (REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (asm_fc_tac[]);
a (SPEC_NTH_ASM_T 6 ⌜(Fst t, b)⌝ (strip_asm_tac o (rewrite_rule[])));
a (swap_nth_asm_concl_tac 4 THEN asm_rewrite_tac[]);
(* *** Goal "2.3" *** *)
a (asm_fc_tac[]);
a (SPEC_NTH_ASM_T 6 ⌜(Fst t, b)⌝ (strip_asm_tac o (rewrite_rule[])));
a (∃_tac ⌜b⌝ THEN (SYM_ASMS_T rewrite_tac));
val FP4 = save_pop_thm "FP4";
=TEX
}%ignore

The above rendition of FP4 may not be true to the intention of Code.
I possibly he might have intended that C be an individual.

To prove that more interesting result I need to define ``individual''.

ⓈHOLCONST
│ ⦏individual⦎ : TermM → BOOL
├──────
│ ∀A⦁ individual A ⇔ ∃b⦁ Snd A = NeSet{b}
■

Since the above is a regular predicate, we need something to convert an ordinary proposition into a modal proposition to use it in the context of modal syllogisms.

ⓈHOLCONST
│ ⦏Mp⦎ : BOOL → MPROP
├──────
│ ∀p⦁ Mp p = λw⦁ p
■

The revised principle is then:

=GFT
FP4b = ?⊢ [] ⊨ (All A hazz B ⇔ ∃ C⦁ Mp(individual C) ∧ (All A hazz C) ∧ (All C izz B))
=TEX

However, this is false in our model, since there need be no single attribute which is posessed by every substance which izz A.
Consider the claim that all paints have colour.
This may be true even if there is no individual colour which every paint hazz.
However, if this stronger claim is not what Code intended, then what did he mean?
Surely not the theorem I actually proved as FP4, since that is too trivial to be worth mentioning.

If we require A to be an individual we get a result:

=GFT
⦏FP4c⦎ =
   ⊢ [Mp (individual A)]
       ⊨ (All A hazz B
         ⇔ (∃ C⦁ Mp (individual C) ∧ All A hazz C ∧ All C izz B))
=TEX

\ignore{
=SML
set_goal([], ⌜[Mp(individual A)] ⊨ (All A hazz B ⇔ ∃ C⦁ Mp(individual C) ∧ (All A hazz C) ∧ (All C izz B))⌝);
a (rewrite_tac (map get_spec [⌜$⊨⌝, ⌜Fold⌝, ⌜$⇔⋎a⌝, ⌜$∃⋎a⌝, ⌜$∧⋎a⌝, ⌜Mp⌝, ⌜individual⌝, ⌜hazz⌝, ⌜izz⌝, ⌜All⌝, ⌜$InTermM⌝]) 
	THEN REPEAT_N 5 strip_tac);
(* *** Goal "1" *** *)
a (SPEC_NTH_ASM_T 1 ⌜(Fst A, MemOf (Snd A))⌝ (strip_asm_tac o (rewrite_rule[])));
a (∃_tac ⌜(Fst B, NeSet {b'})⌝ THEN asm_rewrite_tac[]);
a (strip_tac);
(* *** Goal "1.1" *** *)
a (∃_tac ⌜b'⌝ THEN rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (REPEAT strip_tac);
(* *** Goal "1.2.1" *** *)
a (∃_tac ⌜b'⌝ THEN asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 3 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.2.2" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "2.1" *** *)
a (ASM_FC_T (MAP_EVERY ante_tac) [] THEN asm_rewrite_tac[]
	THEN contr_tac);
(* *** Goal "2.2" *** *)
a (asm_fc_tac[]);
a (LEMMA_T ⌜Fst(Fst t, b'') = Fst t⌝ asm_tac THEN1 rewrite_tac[]);
a (LEMMA_T ⌜Snd(Fst t, b'') ∈ PeSet (Snd t)⌝ asm_tac THEN1 rewrite_tac[asm_rule ⌜b'' ∈ PeSet (Snd t)⌝]);
a (spec_nth_asm_tac 9 ⌜(Fst t, b'')⌝);
a (REPEAT_N 2 (POP_ASM_T ante_tac)
	THEN rewrite_tac[]
	THEN strip_tac);
a (strip_tac THEN swap_nth_asm_concl_tac 6 THEN asm_rewrite_tac[]);
(* *** Goal "2.3" *** *)
a (asm_fc_tac[]);
a (LEMMA_T ⌜Fst(Fst t, b'') = Fst t⌝ asm_tac THEN1 rewrite_tac[]);
a (LEMMA_T ⌜Snd(Fst t, b'') ∈ PeSet (Snd t)⌝ asm_tac THEN1 rewrite_tac[asm_rule ⌜b'' ∈ PeSet (Snd t)⌝]);
a (spec_nth_asm_tac 9 ⌜(Fst t, b'')⌝);
a (POP_ASM_T ante_tac THEN POP_ASM_T ante_tac THEN rewrite_tac[] THEN STRIP_T (asm_tac o eq_sym_rule)
	THEN strip_tac);
a (∃_tac ⌜b''⌝ THEN asm_rewrite_tac []);
val FP4c = save_pop_thm "FP4c";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Individual⦎ : TermM → MPROP
├──────
│ ∀A⦁ Individual A = □ ∀⋎a B⦁ All B izz A ⇒⋎a All A izz B
■

Now on the face of it, in the context of our present model, the modal operator in this definition is irrelevant.
This because all essential predication is necessary.

The following theorem confirms that intuition.

=GFT
individual_lemma1 =
	⊢ ∀ A⦁ Individual A = (∀ B⦁ All B izz A ⇒ All A izz B)
=TEX

We can also show that the Code definition is equivalent to our own:

=GFT
individual_lemma2 =
	⊢ Individual A = Mp (individual A) 
=TEX

In addition to the apparently spurious invocation of necessity, the Code definition depends upon the u-p syllogisms.

Our own primitive definition is couched in terms of the underlying model, and so in terms of that model we would have to regard as a primitive rather than a defined concept (this may be the best way to think of it).


\ignore{
=SML
set_goal ([], ⌜∀A⦁ Individual A = ∀⋎a B⦁ All B izz A ⇒⋎a All A izz B⌝);
a (rewrite_tac [get_spec ⌜Individual⌝, get_spec ⌜□⌝, ext_thm]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[] THEN POP_ASM_T ante_tac);
a (rewrite_tac (map get_spec [⌜$⇒⋎a⌝, ⌜$∀⋎a⌝, ⌜All⌝, ⌜izz⌝]));
val individual_lemma1 = save_pop_thm "individual_lemma1";

set_goal ([], ⌜Individual A = Mp (individual A)⌝);
a (rewrite_tac [individual_lemma1]);
a (rewrite_tac (map get_spec [⌜Mp ⌝, ⌜individual⌝, ⌜izz⌝, ⌜$InTermM⌝, ⌜$⇒⋎a⌝, ⌜$∀⋎a⌝]));
a (rewrite_tac (map get_spec [⌜Mp ⌝, ⌜individual⌝, ⌜All⌝, ⌜izz⌝, ⌜$InTermM⌝, ⌜$⇒⋎a⌝, ⌜$∀⋎a⌝]));
a (rewrite_tac [ext_thm] THEN contr_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜∃b c⦁ ¬ b = c ∧ b ∈ PeSet(Snd A) ∧ c ∈ PeSet(Snd A)⌝
	THEN1 (∃_tac ⌜MemOf (Snd A)⌝ THEN rewrite_tac[]));
(* *** Goal "1.1" *** *)
a (spec_nth_asm_tac 1 ⌜MemOf (Snd A)⌝);
a (POP_ASM_T (strip_asm_tac o (rewrite_rule [NeSet_ext_thm])));
(* *** Goal "1.1.1" *** *)
a (∃_tac ⌜z⌝ THEN asm_rewrite_tac[]);
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "1.1.2" *** *)
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (spec_nth_asm_tac 5 ⌜(Fst A, NeSet{b})⌝);
(* *** Goal "1.2.1" *** *)
a (DROP_NTH_ASM_T 3 (strip_asm_tac o (rewrite_rule[])));
(* *** Goal "1.2.2" *** *)
a (DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac[]);
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
(* *** Goal "1.2.3" *** *)
a (lemma_tac ⌜Fst (Fst A, c) = Fst A⌝ THEN1 rewrite_tac[]);
a (lemma_tac ⌜Snd (Fst A, c) ∈ PeSet (Snd A)⌝ THEN1 asm_rewrite_tac[]);
a (spec_nth_asm_tac 3 ⌜(Fst A, c)⌝);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
a (swap_nth_asm_concl_tac 7 THEN asm_rewrite_tac []);
 (* *** Goal "2" *** *)
a (SPEC_NTH_ASM_T 4 ⌜(Fst t, MemOf(Snd t))⌝ (strip_asm_tac o (rewrite_rule[])));
a (DROP_NTH_ASM_T 3 ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (DROP_ASM_T  ⌜Snd z ∈ PeSet (Snd A)⌝ ante_tac THEN asm_rewrite_tac[]);
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac []);
a (SPEC_NTH_ASM_T 3 ⌜(Fst t, MemOf(Snd t))⌝ (strip_asm_tac o (rewrite_rule[])));
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
a (STRIP_T (rewrite_thm_tac o eq_sym_rule));
val individual_lemma2 = save_pop_thm "individual_lemma2";
=TEX
}%ignore

Now we come to the Code definition of particular:

ⓈHOLCONST
│ ⦏particular⦎ : TermM → MPROP
├──────
│ ∀A⦁ particular A = □ ∀⋎a B⦁ All B are A ⇒⋎a All A izz B ∧⋎a All B izz A
■

A particular is an individual substance and one would have thought that a definition closer to saying that directly might have been a good idea.
In this case in our model the modal operator is not redundant, because without it the definiens would be true if A were an individual attribute which contingently has an empty extension (i.e. is true of no substance), which is possible in this model.
However, this cannot be true of necessity unless A is substantial.

Code might have used a similar device to define substantial:

ⓈHOLCONST
│ ⦏substantial⦎ : TermM → MPROP
├──────
│ ∀A⦁ substantial A = □ ∀⋎a B⦁ All B are A ⇒⋎a All B izz A
■

and then defined a particular as a substantial individual.
Alternatively substantial might be taken as primitive to avoid the use of a modal operator.
Again, Code's definition relies on the u-p syllogisms.

Code's definition of universal is:

ⓈHOLCONST
│ ⦏universal⦎ : TermM → MPROP
├──────
│ ∀A⦁ universal A = ♢ ∃⋎a B⦁ All B are A ∧⋎a ¬⋎a (All A izz B ∧⋎a All B izz A)
■

I think the intension is that a universal is anything except a particular, in which case that would be a better way to define it.
However, in this model, this definition will be true of any non-individual, unless the $⌜♢⌝$ is changed to $⌜□⌝$.

\paragraph{Ontological Theorems}

T1-T3 are essentially redundant definitions so I will omit them and not use the additional vocabulary on this pass.


\section{Conclusions}
