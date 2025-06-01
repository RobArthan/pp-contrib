=TEX
\def\rbjidtACJdoc{$$Id: t029.doc,v 1.8 2011/02/12 09:30:49 rbj Exp $$}


\ignore{
For two and a half thousand years mathematicians and philosophers have both used {\it reason} 
to draw conclusions in their respective domains of interest.
Consistently, there has been a great difference between the levels of success in reliably
securing knowledge by that means.

Mathematicians have gradually accumulated over that period a very considerable body of knoweldge
rarely subject to challenge.
Philosophers, though employing comparable industry have found reason impotent for resolving
many philosophical issues.
}

This is a kind of {\it analytic} history of philosophical analysis.
It is intended to be analytic in a specific sense, in adopting a method of {\it logical analysis} which is articulated as a central part of the philosophical posture which I have called {\it Metaphysical Positivism}\cite{rbjb000}.
We may think of the history as proceeding by the construction of {\it rational reconstructions} of various historical conceptions of philosophical analysis and related matters.
The adoption of the cited method of logical analysis determines the way in which these rational constructions are undertaken.

This results in the rational constructions being undertaken by the construction of abstract models.
Though it is not essential to the method, these abstract models are defined using formal notations.
The formal specifications of these models, and various proofs in relation to them, are checked by computer in various respects (syntactic well formedness and type correctness of terms and formulae, correctness of proofs).

In presenting these, I have attempted to provide for readers approaching at three different levels.

At the first level, it is hoped that the main philosophical ideas will be intelligible independently of the formal material which provides the detail in the various analyses.
At the second level, a reading of the formal materials, consisting of definitions and theorems (but not the proofs), will provide detailed support for the philosophical conclusions and will permit a greater depth of understanding of the issues.
A third level is available for anyone wishing to understanding the details of proofs, to further progress the analysis in any area, or to address other problems using the same methods and tools.

For a reading at the first level it is intended that it will suffice to read the first and last chapters of each part and the first and last sections of other chapters, omitting part three in its entirety.
For a reading at the second level the entire text is relevant, though many parts are independent and a detailed account of the dependencies will be supplied.
At the third level the reader should install the software used for this development and the scripts which constitute the formal part of the book, make reference to various other documents, and acquire a full understanding of the methods and results by interaction with the proof support software.

Readers hoping eventually for an in depth understanding might possibly find it useful to read through at level one first, and then take in the formal material on a second pass.
Alternatively this plan might be adopted chapter by chapter, or exclusively for those particular topics which may interest them.

In this introductory chapter Sections \ref{PhilosophicalIntroduction} to \ref{AOPI} are intended for readers at all levels.
To understand the formal materials it will also be necessary to read Section \ref{UTFM}.
For hands on work see Section \ref{DIYG}.

\section{Philosophical Introduction}\label{PhilosophicalIntroduction}

This analytic history of philosophical analysis is written with a specific terminus in mind, the method of lgical analysis which comes with {\it Metaphysical Positivism}\cite{rbjb000}.
The perspective from which the history is viewed is that of Metaphysical Positivism, the concepts and methods used in the analysis come from the same source, the history as a whole is offered as an extended exemplar of the methods, and involves an exposition of the methods, their philosophical underpinnings and their historical origins.

In this introductory material I hope to provide a sufficient introduction to the methods so that the reader will be able to understand what follows, and to give a description of the coverage of the material which follows and how it fits into the story which I seek to present.

The work is not a presentation of wisdom already realised, and is not a scholarly exercise in the normal sense which is now associated with that phrase.
It is a record of an exploration intended to cast light on the origins of a philosophical viewpoint which I have acquired during the course of a lifetime in which among other preoccupations these matters have featured.
The application of the proposed method to historical investigations is new, and it remains to be seen how much light it casts.

\subsection{Some Preliminary Philosophical Orientation}

The epicentre of {\it Metaphysical Positivism} is the distinction between {\it truths of reason} and {\it matters of fact} which is sometimes known as {\it Hume's Fork}.
Truths of reason are also called {\it logical truths}, {\it analytic truths}, and {\it logically necessary truths}, all these being synonymous in the conceptual scheme of {\it metaphysical positivism}.

A discussion of the history of philosophical logic will involve us in consideration of diverse usage of these and other important terms.
We therefore need a method which allows us to separate our language from that of the various historical figures who feature in the history.

This method is ``The Method of Formal Logical Analysis'', which makes use of formal abstract models of the theories of philosophers to provide precise analyses of their usage.

\section{Formal Methods}
\subsection{Formal Methods in Philosophy}

At least three kinds of work are described by philosophers as constituting ``formal philosophy''
\footnote{This discussion is primarily based on the accounts by philosophers of their involvement in formal philosophy published in \cite{hendricks2005,hendricks2006}.}
.
\begin{enumerate}
\item the use of mathematics in addressing philosophical problems
\item the use of metamathematics or meta-logic in addressing philosophical problems
\item the conduct of philosophy using formal deductive arguments where possible.
\end{enumerate}

Of these the first two dominate.

I will expand this discussion, but this document will primarily be concerned with explaining one approach to item 3.

\subsection{Formal Methods in Information Engineering}

\section{An Overview of Part I}\label{AOPI}

This is a rather selective history focusing on developments which are significant in the history of ideas which underpins the formal analytic method under consideration, and which prove interesting in the light of that kind of analysis.

The most central topic in the first volume is that of logical truth, which itself is not often directly addressed, but which is related to quite a number of other concepts.

Some precursors of our present conception of logical truth are:
\begin{itemize}
\item[Plato] The distinction between the world of forms and the world of appearances
\item[Aristotle] The syllogism and modal syllogism and the distinction between necessary and contingent truth, the distinction between essential and accidental and the metaphysics on which that depends.
\item[Leibniz] Leibniz's conception of the distinction between necessary and contingent truth, his conception of analysis, the ideas behind his {\it calculus ratiocinator}.
\item[Hume] Hume's fork.
\item[Kant] Kant's conceptions of analyticity and necessity.
\item[Frege] Semantics and Logic.
\item[Russell and Wittgenstein] The conception of logical truth as tautological and the metaphysics of logical atomism.
\end{itemize}

The provisional list of chapters is:

\begin{enumerate}
\item Introduction (this document \cite{rbjt029})
\item Plato and Aristotle \cite{rbjt028}
\item Leibniz \cite{rbjt032}
\item Hume and Kant \cite{rbjt033}
\item Frege
\item Russell and Wittgenstein \cite{rbjt030}
\end{enumerate}

I would like to maximise the connectedness of this, and in this I see a couple of spines of development.
The first is Aristotle-Leibniz-Russell.
The second perhaps Plato-Hume-Frege-Wittgenstein.
I don't know whether much can be made of this, the inter-relationship are complex, but some simplified view may contribute to their clarification.

\section{Understanding The Formal Models}\label{UTFM}

\ignore{
=SML
open_theory "rbjmisc";
force_new_theory "fmphil";
=TEX
}%ignore

\subsection{Languages}

Two formal languages are used in this document.
One is a language, called HOL for Higher Order Logic, with a deductive system sufficient for the formal development of mathematics, or for other applications susceptible of formalisations.

The other is a metalanguage known as SML, which stands for Standard Meta-Language.
This is used for giving executive instructions to software which provides support for use of the HOL language and for the construction and verification of formal proofs in the HOL logic.

To understand the specifications it is not necessary to understand the metalanguage SML, it is used in the specifications only for very elementary purposes (typically for introducing a new type or controlling some aspect of the concrete syntax) which we can be understood without any general understanding of the metalanguage.
If it comes to doing proofs, a fuller understanding of the metalanguage is desirable and more information is provided in Section \ref{DIYG}.

We therefore confine ourselves here to explaining the specification language HOL, a variety of Higher Order Logic.
To understand specifications in HOL the reader needs to know about the {\it semantics} of HOL and that is what I aim to present here.

\subsection{Abstract Ontology}

The first thing we need to understand in relation to the semantics is what the language is about, and this may be read as concerning the underlying ontology.
There is no single answer to this question, but the method which we have adopted and of whose description this account of HOL forms a part, is a a method based on abstract modelling.
We therefore present HOL as a language for talking about pure well-founded sets.

\subsection{HOL Types}

HOL is a type theory, based a simply typed lambda calculus.

As such you may think in the first instance of the types as consisting of a type of individuals, a type of propositions, and a hierarchy of types obtained by forming functions spaces from available types.
In Russell's theory of types the individuals were intended as concrete and contingent entities so that the necessary axiom of infinite was held even by Russell to be contingent.
In our case we consider the individuals to be some infinite collection of abstract entities, and the axiom of infinity is not contingent.

\subsection{HOL Terms}

The principle language used here (apart from English) is a language (and logic) called HOL.
HOL is an acronym for Higher Order Logic, of which there are many different varieties, and is also widely used for a specific variant of higher order logic which has been implemented in several computer programs providing support for formal specification and proof.

For full details of this language you would need to refer to the documentation which comes with these tools \cite{ds/fmu/ied/spc001} or some of the papers published about them.
See below (Section \ref{ProofPower}) for information relating to the tool used for producing this document, \ProductHOL.

The language HOL is a direct descendent of Russell's {\it Theory of Types}\cite{russell1908, heijenoort67}, the logic which he and Whitehead used in {\it Principia Mathematica}\cite{russell1913}.
To get from Russell's {\it Theory of Types} to HOL you do the following (names in brackets give credit to the person who thought of the step):

\begin{itemize}
\item discard the ramifications (Ramsey \cite{ramsey25})
\item simplify by basing on typed lambda-calculus (Church \cite{church40})
\item add polymorphism (Gordon/Milner \cite{gordon87,milner78})
\end{itemize}

To do serious work you need a proof tool, see (Section \ref{ProofPower}).

The following are the most important features of this language/logic which distinguish it from those typically considered by philosophers.

\begin{itemize}
\item It is a foundation system, i.e. it suffices for the development of mathematics by conservative extension (definitions) alone.
\item It has a type system, and allows new types to be defined.
\item It is supported by computer software which checks specifications, assists in constructing proofs and rigorously checks proofs.
\end{itemize}

\subsection{Methods}

The principle technique used here is a method which has some of the theoretical merits of a meta-theoretic treatment, but is less arduous and provides better support for reasoning in the object language.

We imagine ourself devising a formal language in which to talk about Aristotle's metaphysics, and in which to formalise the kind of metaphysical arguments which are found in Aristotle.
To do this rigorously, we need to deal first with the semantics of the language, and establish a deductive system which is sound with respect to that semantics.

A standard formal treatment of this material would involve a specification of the syntax of an appropriate language, the development of semantics, probably as some kind of model theory, the specification of a deductive system for the language and a proof of soundness of that system (this would be a version of Aristotle's Syllogistic logic).
This is feasible with the languages and tools we are using, but arduous.
The results would be good for metatheory, but not necessarily convenient for conducting proofs in the language thus defined, i.e. for reasoning in the new object language.

There is another manner of proceeding which better suits our present purposes.
This consists in extending our already available language, using the definitional facilities and the flexibility in its syntax (e.g. fixity declarations) to create a language extension which looks something like and behaves exactly like the intended object language.

We begin with something like model theory, defining new data types which model the kinds of things that the new language is to be about.
The constructs in the language are then given definitions in terms of these new data types.
By deduction within HOL we are then able to prove results which correspond to results in the intended object language.

There is a technical term for this kind of treatment of languages in HOL, they are called {\it shallow semantic embeddings}, and this term indicates that the expressions of the target language are represented by expressions in HOL which are syntactically similar (though perhaps not identical) to those of the intended object language, and which do have the same meaning as the target language expressions.
For a fuller description of this kind of method (used in theoretical computer science) see \cite{gordon88}.

If you have not come across this kind of thing before this probably does not make much sense at this point, but I hope that eventually the material which follows will provide an intelligible example of this method.

\subsubsection{Schemas and Higher Order Quantification}

Much of the semi-formal material which we are trying to fully formalise involves general talk about the kinds of things which are found in categories.
Possibly the formulae are intended as schemas in a first order predicate calculus.
This is not the way we will treat them, so a few words explaining why not are in order here.

We are working here in a higher-order logic.
In a first-order logic, it is not possible for quantify over anything but individuals.
In first order set theory we get around that restriction by having ``individuals'' which are surrogates for all kinds of higher order objects.
In set theory we can, by quantifying over the individuals encompass objects which represent properties of functions of every conceivable type.
Some pragmatic issues remain which we need not go into here.

When a first-order formalisation is attempted without benefit of the machinery of set theory, it often proves necessary to use schemata, which are a syntactic surrogate for quantification over higher types.
A well known example is the theory PA, a first order version of Peano's axioms for arithmetic.
Peano himself formulated his axioms for arithmetic before first order logic was invented, before indeed the foundational problems which provoked the development of type theories.
His axiom of induction involved quantification over properties along the following lines:

=GFT
	⊢ ∀p⦁ p(0) ∧ (∀x⦁ p(x) ⇒ p(x + 1)) ⇒ ∀x⦁ p(x)
=TEX

Which we may paraphrase:
\begin{quote}
for all properties {\it p}, if {\it p} holds for 0 and, whenever {\it p} is true of some natural number, it is true also of its successor, then {\it p} will be true of all natural numbers
\end{quote}

In the first order formalisation of Peano Arithmetic, known as PA, we cannot quantify over properties, so we use instead an axiom schemata, which lifts the quantification into the metalanguage and changes from quantifying over numbers to quantifying over formulae.
Thus we have instead something like:

=GFT
	⊢ P(0) ∧ (∀x⦁ P(x) ⇒ P(x + 1)) ⇒ ∀x⦁ P(x)
=TEX

Where $P$ is not a predicate in the object language, but a syntactic function in the metalanguage which yields formula.
This first order axiom schema describes an infinite set of properly first order axioms obtained by substituting arbitrary formulae (in which $0$ occurs) for $P(0)$, and corresponding formulae for $P(x)$ and $P(x+1)$ in which $x$ and $x+1$ respectively replace occurrences of $0$ in the original formula.

\subsubsection{Features of The Language}

The following features of the language are methodologically significant:

[to be supplied]


\section{Do It Yourself Guide}\label{DIYG}

\subsection{The Software}
\subsection{ProofPower}\label{ProofPower}

The tool used for preparation of this document, for checking the syntax and type correctness of the formal specifications, for assisting in the construction of formal proofs, and for checking the resulting proofs in detail is \Product.

This document is a {\it literate script}.
This means that it is a {\it script} intended for processing by machine, which is also intended to be humanly intelligible (i.e. literate).

The source for the document is machine processed in two distinct ways.
The formal content is extracted and processed by the proof tool \Product, which understands two main languages, the first, HOL, a kind of higher order logic suitable for the formal development of mathematics and for applications of formalised logic and/or mathematics.
The second is a functional programming language called SML, in which instructions may be given to \Product on how to process the formal specifications.
This includes instructions on how to construct and check formal proofs of conjectures in HOL.

\Product come with a library of already defined mathematical concepts and of theorems proven in the context of these definitions, which are organised into a hierarchy of theories in which a theory may make use of the definitions made and theorems proven in any of its ancestors.
As \Product processes a document it augments the theory hierarchy with the new material.
Listings of the theories can be obtained for inclusion at the end of the document.

The other way of processing the source is for the purpose of obtaining a humanly readable document, typically in PDF format, of which this is an example.
While the document is being written, the author enters into an interactive dialogue with the proof tool in which new definitions or modifications to existing definitions are checked for grammatical correctness and type-correctness.
Proofs of conjecture are developed interactively in such a session using a ``goal package'' which permits the user to work backwards from the goal he is attempting to prove.
The end result of such proof development is a script in the metalanguage SML which provides to \Product a prescription for constructing a proof, which is checked for correctness on-the-fly.
This will be rerun when the complete document is later processed in batch.

Document preparation uses the \LaTeX package augmented by facilities provided by \Product, various aspects such as the formatting of formal text, the creation of contents lists, indexes and bibliographies being thereby facilitated.

\subsection{Documentation}

\subsection{The Scripts}

