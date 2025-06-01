=TEX
\ignore{
=VDUMP t047i.tex
Last Change $ $Date: 2011/05/16 21:40:17 $ $

$ $Id: t047.doc,v 1.1 2011/05/16 21:40:17 rbj Exp $ $
=TEX
}%ignore


\cite{rbjt028,rbjt037,rbjt045,rbjt046}


\subsection{Background}

This document should be understood in the context of certain important parts of the philosophical programmes of Gottfried Wilhelm Leibniz and Rudolf Carnap, particularly those part which are concerned with the application of formal logic to problems in philosophy and science.

In Leibniz this concern appears in his ideas for a \emph{universal characteristic} and a \emph{calculus ratiocinator}, the first showing how broad was Leibniz's conception  of the scope of applicability of formal logic, and the latter his belief in the possibility of mechanisation.
Leibniz had ideas whose time had not yet come, the logic of his day was not sufficient to the task and had been derided by Descartes, the technology available for computation fell well short of what would be needed.

Rudolf Carnap by contrast, was born into a new era in which a completely new kind of logic had evolved which was adequate for the formalisaton of any sound deductive argument, he studied under Gottl\"{o}b Frege, one of the pioneers of the new logic, and was inspired by Russell's \emph{Principia Mathematica}\cite{russell10} and by the philosophical programme which he described in \emph{Our Knowledge of the External World as, a Field for Scientific Method in Philosophy}\cite{russell1921}.


\section{Models of Abstract Semantics}

I'm going to start here with some minimalistic models of certain kinds of abstract semantics.

There are two related notions of primary concern here.
Firstly \emph{model theoretic semantics}\index{semantics!model~theoretic} and \emph{truth conditional semantics}\index{semantics!truth~conditional}.
These are so similar from an abstract point of view, that right now I don't know the difference between them and I am expecting it to emerge as the modelling proceeds.
There is however a difference in the kinds of application domain in which these terms are used and this gives us a toehold on the differences.

A model theoretic semantics is typically a semantics for a \emph{logic}, which tells us what the \emph{logical} truths are within that logic.
It does this by defining truth of a formula relative to an interpretation of the non-logical vocabulary in the language which must be consistent with any constraints imposed by the meaning of the terms (which contraints might arise from `implicit definition' using appropriate axioms). 

The term `truth conditional semantics' is more appropriate to a language in which contingent propositions can be expressed.
It does this by defining truth of a formula relative to a possible state of affairs, which fixes the contingent references of names in the language in a manner consistent with their meaning.

There is another kind of `semantics' which might be confused with either of these, which originates with Tarski \cite{tarskiCTFL,tarski56} and is called by him a \emph{definition of truth}\index{definition!truth}\index{truth!definition~of}.
This is sometimes explicitly identified with `truth conditional semantics' and so my rejection of the identification may possibly be controversial.
The distinction which I perceive is that a definition of the true sentences in a language, if that language expresses contingent claims, tells us only the contingent truth values of sentences, it does not tell the truth values of the sentences under conditions which do not hold.
The distinction between the abstract entity defined and other information implicit in the definition is important here, for it may be that though the entity defined is merely a set of true sentences, the form of the definition is applicable equally is other possible situations or worlds, so that there is implicit in the definition the full truth conditions.
Methodologically nevertheless the distinction is important.
One could meet Tarski's conditions of material adequacy by means of a definition which is only contingently adequate, and would if interpreted in other situations would give an incorrect account of the truth values of the sentences.


=SML
open_theory "rbjmisc";
force_new_theory "⦏t047⦎";
=TEX

\ignore{
=SML
force_new_pc ⦏"'t047"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'t047";
set_merge_pcs ["rbjmisc", "'t047"];
set_flag ("pp_use_alias", true);
=TEX
}%ignore

The following model dates from 1997.

A descriptive language is a 6-tuple consisting of:

\begin{enumerate}
\item A set of sentences S.
\item A set of contexts C.
\item A set of possible worlds W.
\item A set of proposions P.
\item A semantic map m ∈ (S × C) → P.
\item A propositional evaluation map v ∈ (P × W) → {T,F,U}. 
\end{enumerate}

Where T, F, and U are three arbitrary but distinct sets which represent the truth values true, false and undefined.

This is encapsulated in the following type abbreviation:

=SML
new_type ("S", 0);
new_type ("C", 0);
new_type ("W", 0);
new_type ("P", 0);
=TEX

=SML
declare_type_abbrev("BOOLU", [], ⓣBOOL + ONE⌝);
=TEX

ⓈHOLCONST
│ m: (S × C) → P
├──────
│ T
■

ⓈHOLCONST
│ v: (P × W) → BOOLU
├──────
│ T
■

ⓈHOLCONST
│ Necessarily : BOOLU → P → BOOL
├──────
│ ∀t p⦁ Necessarily t p ⇔ ∀w⦁ v (p,w) = t
■

ⓈHOLCONST
│ Necessary : P → BOOL
├──────
│ ∀p⦁ Necessary p ⇔ ∃t⦁ Necessarily t p
■

ⓈHOLCONST
│ Contingent : P → BOOL
├──────
│ ∀p⦁ Contingent p ⇔ ∃w1 w2⦁ ¬ v(p, w1) = v(p, w2)
■

ⓈHOLCONST
│ Analytic : S × C → BOOL
├──────
│ ∀sc⦁ Analytic sc ⇔ Necessary (m sc)
■

\ignore{
=SML
val Necessarily_def = get_spec ⌜Necessarily⌝;
val Necessary_def = get_spec ⌜Necessary⌝;
val Contingent_def = get_spec ⌜Contingent⌝;

set_goal([], ⌜∀p⦁ Necessary p ⇔ ¬ Contingent p⌝);
a (rewrite_tac[Necessary_def, Necessarily_def, Contingent_def]);
a (REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (prove_∃_tac);
val NeccNotCont_thm = save_pop_thm "NeccNotCont_thm";
=TEX
}%ignore

\section{Glossary}

At present this glossary is lifted from other documents and correspondence, and is in a very preminary state.
I am not yet decided whether to have a glossary as such, rather than including these definitions in the narrative linked to from the index.
 
\paragraph{truth conditional semantics}\index{semantics!truth~conditional}

A truth conditional semantics is one which gives for each 
sentence in some language the conditions under which that 
sentence is true.
To do this one must identify the intended subject matter as 
a range of possibilities in the context of which sentences 
of the language are to be understood.  In the specific case 
of some ordinary first order language a ``possibility'' in this 
sense would be a structure or interpretation of the 
language.  For a language in which contingent propositions 
are expressed, a ``possibility'' would be something like a 
``possible world''.

A truth conditional semantics can be completely "abstract" 
if the semantics is formulated by constructing a model of 
the space of possibilities in some abstract domain, most 
likely in the domain of some set theory.
A truth conditional semantics is then the definition of a 
mapping from the sentences of the language, together with 
any necessary disambiguating context, to the set of 
possibilities under which that sentence would be true.
This could alternatively be a boolean valued function over 
the possibilities, exactly what mathematical representation 
is chosen is unimportant.

Now it seems to me that natural languages are not used 
exclusively in such a way as to lead us to expect that a 
truth conditional semantics would fully describe the meaning 
(or use) of the language, and so if one does attempt a truth 
conditional semantics, it will be a partial analysis of the 
semantics of the language.
More importantly, it is doubtful that natural languages are 
used in sufficiently regular way for there to be definite and 
objective truth conditions for sentences in the languages.
Even if these difficulties were not present, the sheer 
complexity of natural languages may well make a complete 
model of the truth conditions practically infeasible. 

However, it is possible that the construction of a truth 
conditional partial semantics for a natural language may be 
helpful in understanding that language even if it is not the 
whole story.

\paragraph{denotational semantics}\index{semantics!denotational}

A denotational semantics (as I here propose to use the 
term), is a semantics in which not only sentences but also 
all other grammatical categories are given meaning in a 
similar manner.
In a truth conditional semantics the sentences are given 
meanings as functions yielding truth values.
In a denotational semantics the grammatical constituents of 
sentences are also given meanings, not of the same kind, but 
of similar kinds, and these are called the denotations of 
the words or phrases.

In this Frege's distinction between sinn and bedeutung must 
be born in mind,
(though the crucial distinction here is not exactly that 
distinction). 
The denotation is not the thing which the phrase refers to, 
firstly because the phrase by itself will often not refer to 
any particular thing at all, for lack of context, and 
secondly because the phrase may occur in a ``indirect'' context.

\paragraph{compositionality}\index{compositionality}

Finally we come to compositionality.
A denotational semantics is compositional if it defines the 
denotation of some phrase exclusively in terms of the 
denotations of its constituents without need to refer to the 
constituent itself.

\paragraph{Compositionality Conjecture}\index{compositionality!conjecture}

\begin{enumerate}
\item  That any language (or part or aspect of a language) 
which can be given a truth conditional semantics, can also 
be given a denotational semantics.

\item  That any denotational semantics can be rendered 
compositionally without affecting the truth conditions of the 
sentences (this might involve changes to the denotations of 
other syntactic categories). 
\end{enumerate}

\subsubsection{Frege}\index{Frege}

A difficulty with modal operators is that they treat certain expressions in a radically different manner to the way in which non modal operators work.

This distinction is discussed in Frege \cite{fregeSM,fregeTPWF} even though he is not there concerned with the modal operators.
His vocabulary is therefore important.

\paragraph{sinn}\index{sinn}

This German word central to Frege's ideas about semantics is usually translated into English as `sense', but seems close to what is sometimes intended by `intension' which is in turn close to the meaning of `meaning'.
It is however used by Frege in contrast to Bedeutung, which is most directly translated as `meaning'.

\paragraph{bedeutung}\index{bedeutung}

This German word, also central to Frege's writings on semantics, is most directly translated as `meaning', but is distinct from contemporary English usage of `meaning' so that Frege's usage is now probably better rendered in English as `reference' or possibly `denotation'.

\paragraph{sense}\index{sense}

This is a literal transation of `sinn'.
We will use this only in discussion of Frege, and will use more specific terminology elsewhere.

\paragraph{meaning}\index{meaning}

This is a literal translation of `bedeutung' but we will instead use the term `reference' and the term `meaning' will be used with a less definite more contemporary sense sensitive to context.

\paragraph{mean}\index{mean}

This in contemporary English would be the relationship between an expression and its sense, but cannot be used in that way when discussing Frege.
Frege's term is `express' which is also good for contemporary English and will therefore be preferred in this document.

\paragraph{designate}\index{designate}

An expression is said to designate its `bedeutung', or reference.

\paragraph{express}\index{express}

This is the relationship between some expression and its sense.

\paragraph{reference}\index{reference}

This is both a noun and a verb and corresponds to Frege's `bedeutung' and to his use of `mean'.

\paragraph{denotation}\index{denotation}

This term is similar to `reference' and `bedeutung', but its use in denotation semantics is ambivalent and in that context the denotation would more likely to be sense than reference, and possibly might be a context relativised sense (so that well-formed syntactic expressions may be assigned a denotation independently of context);

\paragraph{designator}\index{designator}

A designator is some expression which denotes, or refers.
A referring expression.

\paragraph{use}\index{use}

In normal or customary `use' words are used to speak about their \emph{bedeutung} or referent.
Sometimes however we use words when our intention is to refer to the \emph{sinn} or sense of the word.
The distinction bewteen use and mention seems to be what Frege has in mind here though he does not make use of those words.
Instead he distinguishes between customary and indirect sinn and bedeutung.

\paragraph{mention}\index{mention}

When we use indirect speech we mention the words or concepts rather than make use of them in a direct way, and when words are mentioned then their bedeutung is called an indirect bedeutung, and is the same as the direct sinn.

\paragraph{direct}\index{direct}

When recounting what someone else has said, the use of `direct speech' consists in quoting literally (using quotation marks) their words.
This is contrasted with indirect speech.

\paragraph{indirect}\index{indirect}

When recounting what someone else has said, the use of `indirect speech' consists in offering some paraphrase of what was said rather than a literal quotation.
Such indirect speech usually begins `that', the use of which indicates that the following proposition is being mentioned rather than used, i.e. that the proposition is not itself asserted but is instead being spoken of in some way.

The context created by `that' and any other context in which the reference of a subordinate proposition cannot be taken to be a truth value is called by Frege `indirect', and in such a context the Sinn and Bedeutung of the expression differs from that in other contexts.
In an indirect context the `Bedeutung' is what the `Sinn' would have been in a customary context, i.e. the sense of the expression.

\paragraph{customary}\index{customary}

Words, expressions or propositions which are not to be understood indirectly are said to have `customary' sinn and bedeutung.

\subsubsection{Quine}

\paragraph{purely referential}\index{purely~referential}

An occurence of a designator is purely referential if substitution of any other designator which designates the same object will not change the truth value of the sentence in which it occurs.
Sometimes this may be abbreviated simply to \emph{referential}.

\paragraph{referential transparency}\index{referential!transparency}

A context in a sentence suitable for a designator is said to be \emph{referentially transparent} a designator occurring in that context would be purely referential.

\paragraph{referential opacity}\index{referential!opacity}

A context in a sentence suitable for a designator is said to be \emph{referentially opaque} a designator occurring in that context would not be purely referential.

\subsubsection{Kripke}

\paragraph{rigid designator}\index{designator!rigid}

A designating expression is rigid if it denotes the same object in every possible world in which that object exists.

\paragraph{strongly rigid designator}\index{designator!strongly~rigid}

A designating expression is strongly rigid if it rigidly designates a necessary object.

\subsection{Some Methodological Preliminaries}

My discussion of this topic will involve the use of a proof assistant called {\Product} competent to check formal specifications written in its own dialect of Higher Order Logic (essentially a polymorphically typed version of Church's formulation of the Simple Theory of Types\cite{church40}), and to assist in the construction and checking of fully formal proofs in this logical system.

The most common way of using the methods of modern logic to investigate modal systems is to furnish a syntax, semantics and deductive system for some language involving modal operators and then to obtain various results about that system (starting with soundness and possibly completeness).

In this example we proceed in a different manner, since the logic at our disposal is capable of defining all the required concepts.
The procedure is to define necessitation as an operator over propositions and then to investigate the issues in a theory which is based on that definition.

Our logic is organised as a sequent calculus, the theorems having a list of assumptions and a single conclusion each of which is a TERM of type BOOL, such terms serving in our logic the role more typically assigned to `formulae'.
There are just two values of type BOOL which are called `T' and `F'.



\ignore{
=SML
add_pc_thms "'t047" [];
set_merge_pcs ["rbjmisc", "'t047"];
=TEX
}%ignore


\ignore{
=SML
commit_pc "'t047";

force_new_pc "⦏t047⦎";
merge_pcs ["rbjmisc", "'t047"] "t047";
commit_pc "t047";

force_new_pc "⦏t0471⦎";
merge_pcs ["rbjmisc1", "'t047"] "t0471";
commit_pc "t0471";
=TEX


=SML
set_flag ("subgoal_package_quiet", false);
set_flag ("pp_use_alias", true);
=TEX
}%ignore


