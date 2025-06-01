=TEX
\def\rbjidtADAdoc{$$Id: t030.doc,v 1.9 2015/04/23 09:58:07 rbj Exp $$}

\section{Introduction}

{\it This is barely started and isn't worth reading yet!}

\subsection{Preliminary Ideas}

The following aspects of these works are those which first strike me as significant for this history.

\begin{enumerate}
\item Russell on Leibniz (this is to appear in \cite{rbjt032} but there might be connections with material here).
\item Russell on Denoting (connection with Frege on sinn and bedeutung and Grice on vacuous names \cite{rbjt037}).
\item Russell's theory of types
\item Russell on incomplete symbols and logical fictions
\item Russell's logical atomism
\item Wittgenstein's Tractatus (connection with Carnap).
\end{enumerate}

More generally and vaguely:

\begin{enumerate}
\item the conceptions of analytic method
\item the conception of logical truth and of The Fork.
\item semantics, truth functional, truth conditional.
\item metaphysics
\end{enumerate}

\subsubsection{Logical Atomism}

From Russell's introductory remarks one can easily get the impression that Russell is giving a presentation of some of Wittgenstein's ideas.
In the main, however, Russell's logical atomism is an account of his theory of logical types, which predates any contrubution from Wittgenstein.
Wittgenstein's contribution (to Russell's conception of Logical Atomism) seems primarily semantic/metaphysical insight.
I put these together since it seems to me that what comes across as metaphysics is better construed non-metaphysically as semantics, this constituting a softening of the doctrines.
One might say, that the question is addressed ``what must the world be like in order for it to be spoken of in this way'', and the step from there to model teory is not so great.
Of course Wittgenstein would not have liked it, just as he rejected Russell's characterisation of his Tractatus as concerning idealised languages.


\subsubsection{The Tractatus, truth functions and conditions} 

Wittgenstein's Tractatus seems to me, in those small parts which I have so far found to be intelligible, to centre around the two ideas, firstly that propositions express truth functions of atomic propositions, and secondly that logical truths are tautologies.
Wittgenstein's treatment of this yields only a narrow conception of logical truth, easily seen to be equivalent to first order validity.
But he has in mind analyticity.
And a full conception of analyticity can be seen to fall under this same idea, the idea of something which allways evaluates to true.
Wittgenstein's treatment is defective, there are huge holes, the whole of mathematics and the examples, such as colour exclusion, of atomic propositions which are not logically independent (or at least, not analytically dependent).

\subsubsection{}

In the period immediately after the completion by Whitehead and Russell of Principia Mathematica there were attempts to draw out from this achievement some philosophical lessons.
The most conspicuous figure in this is Wittgenstein and his contribution was the Tractacus Logico-Philosophicus \cite{wittgenstein1921}.
Russell, appearing to follow in his wake (though prior to the publication of the Tractatus) gave lectures on Logical Atomism \cite{russellPLA,russell1956}.
\footnote{Two other relevant documents of a more technical nature are worth mentioning here, to get a sense of how the technical content of these philosophical works relates to that appearing in the emergent discipline of mathematical logic.
These are \cite{schonfinkelCL,wiener1914}.
These connect with specific features of the Tractatus and Logical Atomism respectively.}

\section{Notes on Russell}

This section contains some rough notes on relevant parts of Russell's writings.

\subsection{Principia Mathematica}

\subsubsection{Preface}

Note that in their Preface Whitehead and Russell point out that:

\begin{quote}
The explanation of the hierarchy of types given in the Introduction differs slightly from that given in *12 of the body of the work.
The latter explanation is stricter and is that which is assumed throughout the rest of the book.
\end{quote}

He does not go into further detail at this point, but I believe the difference consists in the omission in the Introduction of mention of the ramifications to the type system.

\subsubsection{Introduction to First Edition}

\subsubsection{Ch. II. The Theory of Logical Types}

This is a representation of the ideas first presented in \cite{russell08}.

Russell opens by recognising that the theory of types was adopted because it appears to resolve the known paradoxes, but claims nevertheless that the theory is consonent with ``common sense'' and is ``inherently credible'' for which reason it is presented first in its own right before its credentials in resolving the paradoxes are discussed.

\paragraph{I. The Vicious Circle Principle}

Vicious circles of the kind Russell here considers, arise from the supposition that some collection of objects may have members ``which can only be defined by means of the collection as a whole''.
Such a collection is to be regarded (possibly following Cantor) as an illegitimate totality, and any proposition involving such a totality is meaningless.

In the following discussion it appears that Russell supposes that objects under consideration are created by their definition, and that this can only be accomplished if all the entities referred to (even through quantification) in the definition exist prior to the object being defined.

The vicious circle principle is then stated:

\begin{quote}
``Whatever involves \emph{all} of a collection must not be one of the collection.''
\end{quote}

Already by the time that \emph{Principia Mathematica} is published Russell has found this principle to be too heavy handed, and has found it necessary to mitigate its effects by adopting the axiom of reducibility.

It is worth discussing briefly how this proposal looks from a contemporary perspective, and then noting when some of these contemporary insights first appear.

First consider some distinctions which Russell does not appear to note:

\begin{itemize}
\item[i.] that between defining some totality and defining some element of it.
\item[ii.] between various kinds of involvement, e.g. between \emph{containing} and \emph{being defined in terms of}.
\item[iii.] that between circularity and vicious circularity.
\end{itemize}

Thus, one might suppose that if some totality is already definite, to pick out an element of the totality by means of reference to the whole does not involve circularity and should not be problematic.
If we have some account of an ontology which does not depend upon some particular method of defining elements of the totality, we may then introduce a notation in which definitions may be expressed in a manner which presumes that the totality itself is already in place and can be quantified over.
In this case however, there can be no presumption that formulation of a definition brings into being or in itself establishes the existence of the thing defined, there is a need to establish either individually or for general kinds of definition that the objects defined do exist in the totality in question.
If we define an object by definite description, then we must be assured that some single thing satisfies that description in the already defined domain of discourse, if by indefinite description, that at least one thing satisfies the description.

Even if the totality in question is already definite, circularity in a definition may be a problem, but in many cases will not be.
Given such a definite totality the acceptability of circularity in definitions is a matter which is resolved by a proof of the existence in the totality of an element which conforms to (satisfies) the definition.

Russell's principle will seem to many heavy handed (perhaps not to constructivists), and though Russell has to moderate the effects of the principle by adopting the axiom of reducibility, he does not offer or justify a moderation of the principle itself.
The effect of Russell's axiom of reducibility is generally held to be to make his system equivalent to a simple rather than a ramified type theory.
The simple type theory can be understood as achieving its effect not through prohibition of circularity of definitions (as understood by Russell, i.e. as disallowing quantifiction over the type of the object defined) but by ensuring the well-foundedness of the underlying ontology.
Well-foundedness prevents an object involving the whole of a totality of which it is a member, in another sense, in the sense that the transitive closure of the membership relation may not be reflexive.
 
\emph{[More and better discussion is needed here.]}

\paragraph{II. The Nature of Propositional Functions}

Russell begins the discussion of propositional function as if he did not have a notation for functional abstraction, and as if a function were written in exactly the same way as we would write the body of a functional abstraction.
His discussion sounds as if he has confused the function with the body of such a functional abstraction for quite some time, until he finally draws the distinction, and introduces his notation for functional abstraction.
This work of course precedes the advent of the lambda-calculus so the terminology I used was not available to him, and my understanding of the status of variable binding constructs is not well understood by me.
Russell was previously acquainted with Frege Grundlagen in which there is notation for conceptual abstraction.

Russell defines a propositional function as a proposition which contains a free (\emph{real} in his terminology) variable.
Russell has a notation for class abstraction, and a variety of other variable binding constructs such as universal and existential quantifiers and definite description, but at this point he enters into the discussion of functions as if he had no notation for functional abstraction.

He talks at first of propositional functions as we would today talk about formulae containing free variables.
This he does at the outset when he identifies the \emph{essential characteristic} of propositional functions as \emph{ambiguity}.
This is connected with the fact that a propositional function (as he now speaks of it) can be asserted, and that such an assertion is to be understood as asserting something about an undetermined individual.

A function is only determinate if each of its values is determinate, which they will be only if (though not necessarily if) they do not involve the function.
This is an application of the vicious circle principle.
The function presupposes its values, but is not presupposed by them.
Thus ``Socrates is mortal'' is presupposed by buy does not presuppose the propositional function ``x is mortal''.
The latter might possibly involve vicious circularity even though some of its instances do not.

Now Russell introduces his notation for functional abstraction \footnote{Chapter II section II, p40 second paragraph}, which consists in putting a circumflex over the variable to be bound, in the course of making the distinction between the function itself and an indeterminate value of the function.
Nevertheless he continues to regard the function itself, rather than the formula with the free variable, as ambiguously denoting one of its instances.
Of course, we would now take the functional abstraction as denoting the function, and the body before the abstraction possibly as denoting an ambiguous instance (though we explain this more precisely by allowing that it denotes only in a context in which the value of the variable has been determined).

Because of the vicious circle principle, we will have to say that for some values of its argument a propositional function has no value (for example, the argument cannot be the propositional function itself.
The range of significance of the function consists of the collection of values for which the function is significant.

\paragraph{III. Definition and Systematic Ambiguity of Truth and Falsehood}

Truth and Falsehood as predicates must be considered confined to a single type of argument for the sake of compliance with the vicious circle principle as is supposed necessary for the avoidance of contradictions.
Their informal use should therefore be construed as exemplifying systematic ambiguity and as asserting implicitly that particular instance necessary for the argument to which they are applied.

\paragraph{IV. Why a Given Function requires Arguments of a Certain Type}

Russell explains this in terms of the essence of functions, which he has given as ambiguity.
By this he means what we would today describe as the fact that a function must be supplied with an argument.

The use of a variable function symbol in the body of an expression determines the type which an argument to the function defined by that body must have.

\paragraph{V. The Hierarchy of Functions and Propositions}

From the above considerations we find ourselves with a hierarchy of functions of ascending type.
The individuals, functions over individuals, functions over functions of individuals, and so on.

This picture must be further complicated because the functions over individuals do not together constitute a legitimate totality, and must themselves be divided into a hierarchy.

Russell's description of what is now called his ramified type system is very sketchy, particularly in the introductions where you might expect it to be spelled out fully\footnote{But note that he says in his preface that the fuller account is to be found in *12}, it is necessary to look into the body of the work for further enlightenment, which might even then leave room for doubt.
Combined with the lack of explicit type annotations arising from the use of systematic ambiguity, this makes it not straightforward to extract a precise account of the ramified type system and leaves doubt for any particular proposal as to whether it is what Whitehead and Russell intended.
The secondary literature is sometimes also imprecise or inaccurate in presenting what Whitehead and Russell do say.

Whitehead and Russell are most explicit in their description of how the order of a propositional function is determined.
However, it is clear that the order is a coarser classification than the types.
The information which Russell supplies about types consists only in the general principle that a type is the range of significance of a propositional function, and in various additional observations suggesting when types are distinct.

Russell's talk about functions is exclusively about propositional functions, which may have multiple arguments, in which case they are relations.
Propositional functions are only of the same type if they take the same number of arguments and the types of the arguments are the same.
There are no functions which deliver values other than propositions, but there are individuals.

It is clear that propositions (not just propositional functions), and individuals, do not constitute a totality and are not all of the same order.
In these cases the order is determined by the maximum order of the bound variables which occur in their definition.
A reservation is present in relation to individuals, since a definition of an individual which involves quantifiers must be a description, which is an incomplete symbol, and the possibility arises that this might negate the rationale for giving an order to an individual.
Be that as it may, a propositional function which takes an individual as an argument must have a type distinct from one which takes a proposition in the same place and this leads us to the following account of Russell's ramified type heirarchy.

A type is: 
 
\begin{enumerate}
\item The type of Propositions of order n (for any natural number n>0)
\item The type of Individuals of order n (in which there remains some doubt about whether n may be other than 1)
\item A type of propositional functions of order n over a finite sequence of arguments of specified types (where n must be greater than the order of every argument).
\end{enumerate}

\paragraph{Hylton's Possible Misreading}

The following issue I first came across when reading Peter Hylton's excellent volume on Russell's early work \cite{hyltonREAP}.
At first I went along with Hylton since the passage he cited seemed unambiguous, but further rummaging lead me to doubt that Russell had meant what Hylton (and I) took him to mean.
First I describe the issue as it appeared to me on first reading Hylton.
Then I explain my grounds for believing Hylton to have misunderstood Russell.

The above account of the type distinctions envisaged by Russell seems to be incomplete.
A discussion of the additional conditions may be found in \cite{hyltonREAP} p305.
Russell's remarks suggest that more information about the type of bound variables in the definition should influence the type of the definiens%
\footnote{`First order propositions are not all of the same type, since, as was explained in *9, two propositions which do not contain the same number of apparent variables cannot be of the same type.' Principia Mathematica \cite{russell10} *12, p162.}%
.
To incorporate this into the system would complicate all three clauses in the above definition, since the types of both propositions and individuals might then have to include the types of bound variables occuring in the definition, and the type of propositional functions would also have to include this information.
In each case this would either involve a set or a multi-set of types of apparent variables (but possibly only the multiplicity).

This last elabortion, though evidently thought desirable by Russell, is difficult to motivate.
Without it, the type system is well motivated first by the need to ensure that arguments to propositional functions must match in number and kind the use of the real variables in the definition otherwise nonsense will ensue, and by the dictates of the vicious circle principle which is incorporated through the concept of order.
Having ensured compliance with the vicious circle principle by incorporation of order in to the type, further information about the types of apparent variables in the definition seems to serve no purpose, and if included potentially makes the information about order redundant (the order of a propositional function is obtained by adding one to the maximum order of the real and apparent variables in its definition).

On the matter of whether Russell really intended the number of quantifiers in a definition to affect its type, I have followed through the text more carefully and come to doubt that he did.
There is of course reason to doubt it because he does not offer any reason for such an elaboration.
The passage cited by Hylton (\cite{russell10} *12, p162) itself refers elsewhere (*9) for the explanation, and does not explicitly speak of quantifiers.
It speaks of \emph{apparent variables} which include those bound by quantifiers, but also the variables for the arguments of a propositional function (even when they are not circumflexed).
There is reason to believe that he intends here \emph{only} the variables for arguments, not quantified variables.

When we look back to *9 to discover why Russell might think the \emph{number} of quantifiers relevant, there does not appear to be any explanation.
What we do find (\cite{russell10} *9, p128) is a discussion of how the propositional variables in sections *1-*5 `are necessary elementary propositions' and that the primitive propositions must be restated for first order propositions and analogues of the propositions in *2-*5 obtained by `merely repeating the same proofs'.
It follows he says that the process can be repeated to obtain a similar theory for propositions with two apparent variables so on indefinitely.
By this process he says, `propositions of any order can be reached'.
This is a little odd, for there are two distinct directions of movement here, adding an extra quantified variable of the same type would not by his own account change the order of a proposition, though one can of course progress through the orders by progressively increasing the order of even a single quantified variable in the propositional.
What does change the type, but not necessarily the order, is the movement from propositions to propositional functions, and that of adding additional apparent variables as arguments rather than for quantification.
Section *9 does not therefore supply a rationale for considering the number of apparent variables relevant to the order of a proposition, or of a propositional function, or even any further grounds for our belief that Russell held the number to be relevant.
However, here and later in sections *10 and *11 (on the theory of one and two apparent variables respectively), we see that the subject matter does the relevant numbers of quantified variables, and also that number of argument places in propositional functions, and offers nothing to confirm the idea that type distinctions arise merely from the presence of greater numbers of quantifiers.

\paragraph{Fuller Treatment of the Ramified Type System}

A full account of the ramified type system, by today's standards would also involve a more formal statement of the above definition, a semantics assigning domains to the types, and an account of well-typed formulae of the theory of types.
I may make some steps in this direction in the formal materials below, but this is of lesser interest than other aspects of Russell's philosophy and may therefore not happen.
(of course, this has already been done many times)

\paragraph{Predicativity}

The term predicative has had many uses since it was introduced by Russell, apparently in 1906.
Feferman provides an extended account in \cite{fefermanP} in \cite{shapiroHPML}.

Apparently Russell at first used the term for propositional functions which defines a class (one whose extension exists), by contrast with the kinds of function whose extension is incoherent, which he called impredicative.
The general idea that predicativity priginally meant no more than consistency is worth bearing in mind, for this is potentially a much more liberal notion of predicativity than those which have succeeded it.

In Principia Russell uses the term in a quite different way, which is important because of the role it plays in the formulation of the axiom or reducibility.
A propositional function is predicative if its order is no greater than is required by the types of its arguments, i.e. if it does not quantify over any type of higher order than the highest of its arguments.

\subsection{Part I}

\subsubsection{Section A The Theory of Deduction}

\subsubsection{Section B Theory of Apparent Variables}

\paragraph{*9 Extension of the Theory of Deduction from Lower to Higher Types of Propositions}

Here Russell talks about typical ambiguity and justifies its use.

He also provides more information about the type system, and it is here that he refers to (from *12) for an explanation of his talk about the effect of the multiplicity of apparent variables on the type of a propositional function (in *12).

\paragraph{*12 The Hierarchy of Types and the Axiom of Reducibility}

\section{Preliminary Observations}

At the core of both Russell's atomism and Wittgenstein is the metaphysical idea that the world consists of a collection of facts.
\footnote{I need to find out where this idea first appeared.}

This is probably one of the ideas Russell took from Wittgenstein.
Though this features in both systems, its has a different role in each.
Wittgenstein's exploitation of this idea is more thorough and systematic than Russell's.
In Wittgenstein the fundamental insight is that propositions express truth functions of atomic propositions, and that logical truths (which Wittgenstein seems to identify with analytic propositions) are those which are tautologous (i.e. true whatever the truth values of the atomic propositions, i.e. whatever are the atomic facts).
Together with the insistence that the atomic facts are logically independent, we have a faulty account of analyticity, but a good account of the semantics of first order logic.
Without this general insistence on logical independence of atomics, we have a conception of semantics which is important and influential.

Russell builds his logical atomism around the same core, atomic facts.
But its clear firstly that the simple idea that propositions are truth functional does not inspire him, and that he has important objectives which are absent in Wittgenstein.
The pure logical semantics we find commuted in simplistic way into metaphysics by Wittgenstein tells us little or nothing about what the things are which are related by atomic propositions.       

\subsection{Schematic Variables}

It is explicit in PM, under the heading of ``typical ambiguity'', that the propositions therein are to be regarded as schemas.
This works by omission of type information from variables, and it intension is that a formula can be read with any assignment
of types which is type correct (though that idea is not precisely defined).

It is also the case that Russell's use of ``incomplete symbols'' does involve the use of certain symbolic expressions in ways which
can only be understood by syntactic elimination of the symbol together with some of the syntactic context in which they occur,
The best known example of the use of incomplete symbols arises from Russell's theory of desriptions, described in his classic paper {\it On Denoting}.
Even more significant perhaps in PM is the use of incomplete symbols to effect Russell's `no classes' treatment of set theoretic terminology.

It has been further suggested that PM makes use of {\it schematic variables}, and in particular when names such as {\it f} appear unbound
they are not to be regarded as free functional variables varying over propositional functions of some type, but as schematic variable
varying of syntactic expressions.
I have so far seen no convincing evidence for this point of view, which is seems to me is contradicted (though not quite explicitly) by what Russell says about variables on page of PM.

The evidence I have seen adduced is that certain propositions in *20 only make sense with such a schematic interpretation rather than as containing real functional variables.

I probe this a little here using {\Product}.
Of course, this tool does not implement the logic of PM, it implements a polymorphic version of Church's Simple Type Theory.
However, for the issues at hand I think this may be close enough.
The propositions in question concern the elimination of set theoretic vocabulary.
*20.07 defines the application of a propositional variable to class, and must be regarded as expressing a syntactic transformation.
The definiendum involves a symbol for a class.
Since classes do not exist, this cannot be an object language variable, all of which range over individuals or propositional functions.
It therefore seems that the definition shows a stage in the elimination of class terminology in favour of terminology not involving classes.
It is the application here which is being eliminated.
However, there seems no reason to regard the propositional function being applied on the right as schematic.

When expressed in {\Product} the point of *20.07 is largely lost.
What is says is, that when some function is asserted of all classes (of a type), that should be read as asserting it of all predicative functions (over that type).

=SML
open_theory "rbjmisc";
force_new_theory "PM01";
set_pc "rbjmisc1";

declare_type_abbrev("CLASS", ["'a"], ⓣ'a → BOOL⌝);

val PM20p07 = ⌜(∀α:IND CLASS⦁f(α)) = ∀φ:IND → BOOL⦁ f(φ)⌝;
=TEX

\section{The Tractatus}

I will begin by attempting to present a formal model of (aspects of) Wittgenstein's Tractatus\cite{wittgenstein1921}.

=SML
open_theory "rbjmisc";
force_new_theory "tract01";
set_pc "rbjmisc1";
=TEX

\subsection{The World}

Wittgenstein says that a world consists of facts rather than things, that it is all the facts, that these tell us both what is the case and what is not the case, that they are ``in logical space'' and that they are logically independent.

I take this to be analogous to atomic propositions, the requirement that we know both what is and is not the case is satisfied if we have all the true atomic proposition, without any negated propositions, and this also best meets the requirement for logical independence.
We do not know here what a fact is so the information we have here is best caputured by a type constructor or a function (depending on whether we think the facts will be a type or a set).

I will assume that it will be a type (this can probably be arranged).
WIttgenstein, has implicitly alluded to possible worlds in 1.21 (though is not necessarily `ontologically committed'), and we might think of the type ⓣ('a)WORLD⌝ being the type of all possibile worlds whose facts have type ⓣ'a⌝.

=SML
declare_type_abbrev("WORLD", ["'a"], ⓣ'a ℙ⌝);
=TEX

The world is then, something of type ⓣ('a)WORLD⌝, which I will refrain from introducing until we know more about what a fact is.

\subsection{States of Affairs}

A state of affairs is some combination of objects.

=SML
new_type("OBJECT", 0);
=TEX

It must therefore involve a collection of objects possibly with some information about how they are combined (allowing that the same set of objects might be combined in more that one way).

Because we later find other kinds of object which have similar structure to states of affairs, we will use the same type constructor in each case, applying the constructor to different types as appropriate.

In order to give structure to a collection we must first distinguish the elements of the collection and then supply some recipe for 

=SML
declare_type_abbrev("CONSTRUCTION", ["'a", "'b", "'c"], ⓣ('a → 'b + ONE) ×'c⌝);
=TEX

In the above definition, a {\it CONSTRUCTION}, is a type constructor of which the first type parameter is a type of indexes or tags, the the second a type of things.
This represents collections of objects which are indexed rather than an unstructured, allowing the same object to be used more than once, and allowing that an object be supplied for inclusion in the structure in some specific place.
The third type parameter is the type of the information indicating how the constuents are to be combined to form the whole.

\subsection{Thoughts and Propositions}

The things which stand for objects in propositions are names.

=SML
new_type("NAME", 0);
=TEX

\subsection{Propositions as Truth Functions - I}

Wittgenstein introduces a single truth functional connective, which is a generalised distributed denial (generalised Scheffer stroke).
\footnote{The non-generalised version was discovered by Scheffer, the generalised version was presented by Schonfinkel in his paper on combinatory logic (presented in 1920, published in 1924 \cite{schonfinkelCL,heijenoort67}).}

This is readily defined in HOL.
We define it as an operator on sets of functions, since that allow us to use set displays as the arguments.

ⓈHOLCONST
│ N: (BOOL)ℙ → BOOL
├
│ ∀s⦁ N s ⇔ ∀p⦁ p ∈ s ⇒ ¬ p
■

We can then prove that all the usual logical connectives are definable in terms of ⌜N⌝.
The following theorems show that the logical constants in HOL are equivalent to expressions in N.

=GFT
N_¬_thm = ⊢ ∀ p⦁ (¬ p) = N {p}
N_∧_thm = ⊢ ∀ p q⦁ (p ∧ q) = N {N {p}; N {q}}
=TEX

\ignore{
=SML
set_pc "rbjmisc1";
set_goal([],⌜∀p⦁ ¬ p ⇔ N{p}⌝);
a (prove_tac [get_spec ⌜N⌝]);
val N_¬_thm = save_pop_thm "N_¬_thm";

set_goal([],⌜∀p q⦁ p ∧ q ⇔ N{N{p}; N{q}}⌝);
a (rewrite_tac [map_eq_sym_rule N_¬_thm]);;
a (prove_tac[get_spec ⌜N⌝]);
val N_∧_thm = save_pop_thm "N_∧_thm";

set_goal([],⌜∀pf⦁ $∀ pf ⇔ N{p | ∃x⦁ p = N{pf x}}⌝);
a (strip_tac);
a (once_rewrite_tac [map_eq_sym_rule (∀_elim ⌜pf⌝ η_axiom)]);
a (rewrite_tac [map_eq_sym_rule N_¬_thm]);;
a (rewrite_tac[get_spec ⌜N⌝]);
a (REPEAT strip_tac);
a (asm_fc_tac[]);
a (spec_nth_asm_tac 1 ⌜¬ pf x⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
val N_∀_thm = save_pop_thm "N_∀_thm";

=IGN
set_goal([],⌜∀pf⦁ $∃ pf ⇔ N{N{p | ∃x⦁ p = N{pf x}}⌝);
=TEX
}%ignore

ⓈHOLCONST
│ M: ('a → BOOL) → BOOL
├
│ ∀f⦁ M f ⇔ ∀x⦁ ¬ f x
■

=GFT
M_¬_thm = ⊢ ∀ p⦁ (¬ p) = M (λ x⦁ p)
M_∧_thm =
   ⊢ ∀ p q⦁ (p ∧ q) = M (λ x⦁ if x then M (λ x⦁ p) else M (λ x⦁ q))
M_∀_thm = ⊢ ∀ pf⦁ $∀ pf = M (λ x⦁ ¬ pf x)
M_∃_thm = ⊢ ∀ pf⦁ $∃ pf = M (λ x⦁ M (λ x⦁ pf x))
=TEX

\ignore{
=SML
set_pc "rbjmisc1";
set_goal([], ⌜∀p⦁ ¬ p ⇔ M(λx⦁p)⌝);
a (prove_tac [get_spec ⌜M⌝]);
val M_¬_thm = save_pop_thm "M_¬_thm";

set_goal([],⌜∀p q⦁ p ∧ q ⇔ M(λx⦁ if x then M(λx⦁p) else M(λx⦁q))⌝);
a (rewrite_tac [get_spec ⌜M⌝]);
a (REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜T⌝);
a (spec_nth_asm_tac 1 ⌜F⌝);
val M_∧_thm = save_pop_thm "M_∧_thm";

set_goal([],⌜∀pf⦁ $∀ pf ⇔ M(λx⦁ ¬ pf x)⌝);
a (strip_tac);
a (once_rewrite_tac [map_eq_sym_rule (∀_elim ⌜pf⌝ η_axiom)]);
a (rewrite_tac[get_spec ⌜M⌝]);
val M_∀_thm = save_pop_thm "M_∀_thm";

set_goal([],⌜∀pf⦁ $∃ pf ⇔ M (λx⦁ M (λx⦁ pf x))⌝);
a (strip_tac);
a (once_rewrite_tac [map_eq_sym_rule (∀_elim ⌜pf⌝ η_axiom)]);
a (prove_tac[get_spec ⌜M⌝]);
val M_∃_thm = save_pop_thm "M_∃_thm";
=TEX
}%ignore

\subsection{Propositions}



ⓈHOLCONST
│ N⋎2: (BOOL)ℙ → BOOL
├
│ ∀s⦁ N s ⇔ ∀p⦁ p ∈ s ⇒ ¬ p
■


%\section{Russell's Logical Atomism}

%\section{Emil Post on Propositional Logic}

