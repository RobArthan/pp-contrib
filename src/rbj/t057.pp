=IGN
$Id: t057.doc $
=TEX
\documentclass[11pt,a4paper]{article}
%\usepackage{latexsym}
%\usepackage{ProofPower}
\usepackage{rbj}
\ftlinepenalty=9999
\usepackage{A4}
\usepackage{etoolbox}
\patchcmd{\thebibliography}{\section*{\refname}}{}{}{}
\patchcmd{\thebibliography}{\addcontentsline{toc}{section}{\refname}}{}{}{}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}
\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{Formal Architectural Modelling}
\makeindex
\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=red, citecolor=blue, filecolor=blue, linkcolor=blue}

\author{Roger Bishop Jones}
\date{\ }

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
Some notes on methods for formal verification of system architecture in the context of Model Based Systems Engineering.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2020-12-26

Last Change $ $Date: 2021-01-10 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t057.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t057.pdf}

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

This PDF is hyperlinked to facilitate navigation around the document.%
\footnote{Links within the document are coloured blue, external URLs are coloured red.
If you read the document in Acrobat Reader on a mac, command left-arrow is the back key. You can get a back arrow on the toolbar by: right click on toolbar -> page navigation tools -> previous view}

These are notes I put together while looking at the ideas presented in \cite{dickerson08,dickerson2020architecture}, particularly on the idea of ``model theoretic'' approaches to giving mathematical precision to architecture definitions.
I have had some difficulty in getting a clear understanding of what is intended.
Probably partly because of knowing too little of important background context, particularly in relation to the relevant standards work of ISO/IEC WG42 and a fuller acquaintance with UML, SysML and Common Logic.
Such as I have in in section \ref{admt}

The second part, in section {\ref{fmasv}}, is a presentation of how I think about system architecture and the problem of reasoning mathematically about whether some formally defined architecture would suffice to build a system meeting formally specified requirements.
The formal parts of this account is undertaken in Higher Order Logic (HOL) using the {\ProductHOL} dialect of Church's Simple Theory of Types, supported by the \Product{} toolset.

This approch to the development of secure and safety critical systems was used by ICL in the decade around 1990, at first using the Cambridge HOL proof tool\cite{gordon93} and later the ICL {\Product} tools.
A simplified example of the application of these methods to secure systems and discussion of some of the methodological issues may be found in \cite{jones92}.

Work in this vein was provoked by the US DoD, who had been convinced by their academic consultants at the time that the best way to ensure that the computer systems handling highly classified materials were secure would be to mathematically prove that they are, and that, because of the great complexity of such systems, no proof could be trusted unless machine verified.
I understand that the USA advised the British government that if we were to continue to have access to their confidential intelligence, then our computer systems would have to operate to similar standards, and a program of work was then sponsored by GCHQ/CESG to establish a UK capability to develop and formally verify secure computing systems.
Similar considerations (though less exacting) were later applied to safety critical defence procurements in the UK and embodied in DEF STAN 00-55.

The main problem with this idea is that, even with the best available computer support, formal mathematical proof is very labour intensive.
As soon as the systems get non-trivial this is an insuperable obstacle.
Since then proof technology has advanced, and the {\Product} tools which I still use, now fall short of the state of the art except possibly in certain areas.
Computer verified proofs have now been undertaken for some of the most difficult mathematical results such as the four colour theorem, but I believe are still not practical for other than relatively simple computer systems.
This will probably remain the case until we have serious machine intelligence, which I think is still over the horizon.

There was a book \cite{mackenzie} published around this area by Donald Mackenzie, then I think a professor of sociology at Edinburgh University.
He sent a research associate to interview me, and the transcript of the interview can found online \cite{rbjp006}.

I personally am an enthusiast for the mechanisation of formal mathematics and its application to engineering design, but I am sangine about its feasibility pro-tem.
I do find that when I am able to treat formally a topic which had previously had a less rigorous treatment, lots of valuable detail emerges which was previously obscure.
Nevertheless, it is not clear to me that such methods could appear in a general standard for architectural modelling, though I might be less sceptical if I new more about the relevant context, particularly SysML and Common Logic.
Some of the work we undertook with {\Product} does support the formal treatment of graphical notations.
The ClawZ project, undertaken by Lemma1 under contract to QinetiQ delivered several iterations of a program which translated simulink diagrams into formal specifications in the Z language, which could then be processed by {\Product}\footnote{Project documentation, much of it formal specifications in \ProductZ{}, is available at \url{https://www.lemma-one.com/clawz_docs/clawz_docs.html}.}.

\pagebreak
\section{Architectural Design using Model Theory}\label{admt}

Though I appreciate that an understanding of models contributes to a working competence in the use of formal notations, I have so far been unable to get a grip on the proposed use of model theory in the presentation of mathematical models of system architecture.

I do have a working understanding some of the ways in which formal notations can be used in systems architecture and design, and would if necessary be able to give less formal prose descriptions of the same mathematical models, in neither case would I expect to see any explicit mention of model theory.

I think for me to properly engage with these ideas I would need to see something like the ADAS example worked through both by the methods which I understand (so that I do actually understand the problem being modelled) and also using the model theoretic methods advocated.
That's probably not going to happen!

I was puzzled by the insistence on \emph{relational} structures, which I would expect to make complex modelling more difficult and less easy to understand.
Some more detailed technical observations in that area follow.

\ignore{
This is an interesting idea, if I understand correctly the intent is to offer, instead of parallel formal and informal definitions of the architecture, an informal definition rendered mathematical through model theory.

It is not usual to connect the idea of using mathematical models in science and engineering with the branch of mathematical logic known as ``model theory'', in which the term `model' has a very specific meaning rather than a general sense.
In that context, the models are exclusively models of theories (in the mathematical sense), and that notion of model specifically means ``interpretation of the theory in which all the sentences of the theory are satisfied''.
Though rather specific in that way, this notion has a generality in enabling a meaning to be associated with any theory, generally as a class of structures.
But this is nevertheless, rather different to what is normally though of in science and engineering as a mathematical model.
A sense of the difference may be seen by comparing Hodges SEP article on model theory \cite{hodgesSEPMT} with the wikipedia page on mathematical model \cite{rbjw012}.
Of course, the former is a more scholarly discussion, but the main point of the comparison is that they are not really talking about the same kind of thing.

Mathematics is normally undertaken in natural prose augmented by mathematical notation, and its not clear to me what extra value is obtained by invoking model theory.
A model theoretic definition defines a collection (set or class) of structures (in first order model theory the models would always be a proper class, which limits what can be done with them).
To take english prose as made precise by its models, the signature must be known, as well as the meaning of any parts of the sentence not in the signature.
(The distinction between `logical' and `non-logical' vocabulary is crucial but arbitrary.) 
Interpreting some sentence S, model theoretically, with a signature L, gives just the same result as the set or class abstraction $\{L\ |\ S\}$ which, if formality is to be minimised, might be expressed as ``the collection of structures with signature L such that S''.
In writing informal mathematical definitions however, we are not constrained to defining collections of structures.

Its therefore unclear to me how the invocation of model theory adds value to the situation in which an informal architectural description can be made precise either by an informal mathematical model or by a formal specification.

In the approach I talk about below, the kind of mathematical entity which is adopted for a model of a system architecture is an ordered pair providing a collection of component or subsystem specifications and a constructor function which shows how these components are combined to give the system.
This is not the kind of mathematical entity which one would expect to arise from a ``model theoretic definition'' as that term is defined by Hodges.
}%ignore


\subsection{Relational Structures}

I'm puzzled why the constraint to \emph{relational} structures.
This would simplify metatheory, but at the expense of making the specifications more complex and opaque.
Thus the relation: $a^2 + b^2 = c^2$, since it has four instances of function application would have to be rendered using the corresponding relation symbols and existential quantifications:
=GFT
	∃w x y z⦁ Re(a, 2, w) ∧ Re(b, 2, x)  ∧ Re(c, 2, y) ∧ Ra(w, x, z) ∧ z = y
=TEX
In which \emph{Re} is the relationship of exponentiation ($Re(x, y, z) %equiv% x^y = z$) and \emph{Ra} that of addition ($Ra(x, y, z) %equiv% x + y = z$).

Commenting specifically on the interpretation given in \cite{dickerson2020architecture} IIIB, there are some difficulties.
Sentence (1), assuming that $P_1$ and $P_2$ are intended to be relations, is not a syntactically valid sentence of the predicate calculus, since it applies the relationship `=' to two atomic formulae.
It would be valid if $`⇔'$ were used instead of `=' or if $P_1$ and $P_2$ were function names rather than relation names, but then one would not have a strictly \emph{relational} structure.

For a model of the concept of orthogonality, I should myself be looking for something talking about vectors, rather than a relationship between scalars.
In a vector space the notion of orthogonality is definable thus:
=GFT
	orthogonal (x,y) ⇔ x.y = 0
=TEX

Here, though ``orthogonal'' is itself a relationship, the language we have used involves functions, and so goes beyond the first order predicate logic into the first order functional calculus.

Even for hard core model theory as a theoretical discipline, the constraint to relational signatures does not seem to be thought a worthwhile simplification of the theory, and, for example, in Hodges\cite{hodgesSMT} we are immediately given a definition of structure which includes operations (functions) as well as relations, relational structures receiving only a passing mention.

In IIIC, SYMBOL and REFERENT are said to be related by a model theoretic \emph{interpretation map}.
In \cite{hodgesSMT} interpretation is of one (model theoretic) structure in another, and so neither is syntactic and the two are similar kinds of abstract object.
Is it intended that both SYMBOL and REFERENT are model theoretic structures, or is some other notion of interpretation intended?

\pagebreak
\section{A Formal Model of Architectural Specification and Verification}\label{fmasv}

\subsection{Architecture and Ontology}

In what follows I present an approach to architectural modelling and verification, in which the primary aim is to cast some light on how mathematical models can be used to define an architecture in a sufficiently precise way as to permit the correctness of the architecture (as a way of realising a system meeting a clearly defined requirement) to be mathematically proven.

In many of the established methods for formal development, the behaviours of the system are modelled formally, but there is no single mathematical entity which represents the system as a whole.
Consequently, it is not possible to state in the formal notation the propositions of greatest interest.
The implementation method may be said to be \emph{by refinement}, and the correctness of refinement will then be established by proving a number of separate propositions (verification conditions) which are syntactically generated from the script of the formal specification.
There are many variations on this theme.

If a sufficiently expressive formal notation is used (or even with appropriate use of informal mathematics), it is possible to have a single type of entity providing models for the class of systems under consideration, to formulate the requirements as a property of such entities, and to clearly state and mathematically prove the correctness of the model corresponding to some proposed design or implementation of a system meeting the requirement.

This is an advantage arising from thinking of a mathematical or formal model as an abstract entity, rather than as a body of text.
The method, which is exemplified below in an abstract treatment of architectural modelling (and in many more substantial exemplars elsewhere), assumes such an ontologically complete formal treatment.

For the sake of generality nothing is assumed, in the following model, about the nature of the system being modelled, except insofar as it is presumed that the system will be complex and its behaviour will effectively be determined by that of its various subsystems or components and by the manner in which these have been combined into a whole.
The problem of realising the required behaviour may therefore be approached by identification of a collection of parts, description of how these parts are to be assembled into the whole, and stipulating the requirements on those parts which suffice to ensure that the resulting whole behaves in a manner consistent with the requirements for the system as a whole.

No assumptions are made about the nature of the requirements, either for the whole system, or for the subsystems or components.
We therefore consider these requirements to be properties (i.e. BOOLean valued functions) of mathematical entities which are considered as models of potential candidates.
(This is convenient because {\Product} supports a Higher Order Logic, but a typed set theory would be equally expressive and in that context requirements would be represented as a set.)
The definition of these properties is part of the system requirements analysis (at the top level) and the architectural design process (at the next level).
The kinds of abstract object which are candidates are determined in the process of formalising the requirement.
In order that the requirement can be thus defined, it must be the case that we are talking of the system model as being a single abstract entity, rather than, say, a collection of formal definitions.

An important advantage of this method of mathematical modelling, by contrast with methods such as those advocated for use with the specification languages Z and VDM, is that the set of acceptable implementation models is explicit.
If acceptable implementations are obtainable by a process of refinement, then the meaning of the specification is dependent on exactly what refinement process is deemed acceptable, and there may be questions about what kinds of refinement will preserve critical properties.

\subsection{Model Theory and Higher Order Logic}

I'm not intending here a scholarly account of models of higher order logic, but rather an informal discussion at level appropriate for someone trying to understand how \ProductHOL{} works for systems design\footnote{For a full and formal account of the semantics of \ProductHOL{} see Arthan\cite{ds/fmu/ied/spc001,ds/fmu/ied/spc002},
also available at \url{https://www.lemma-one.com/ProofPower/specs/specs.html}}.

The specifications which follow are formalised in {\ProductHOL}, a polymorphic variant of Church's Simple Theory of Types \cite{churchSTT}, a language and logic closely based on that of the Cambridge HOL system designed and implemented by Gordon et.al.\cite{gordon93} (originally for use in the verification of digital hardware).
An account of the semantics of this formal logic is ``model theoretic'' insofar as it describes the models of the theory.
This is quite a bit different to the model theory of first order logic.

It is worthwhile to have an elementary understanding of this to fully understand specifications in Higher Order Logic, but the main flavour of writing specifications, or constructing and reasoning about ``mathematical models'' in this system is rather closer to that of writing a program (in a somewhat exotic programming language) than of doing model theory.
By that I mean, that a specification in this system feels like (with good reason) a series of definitions, and intuitively one is thinking of the nature of the particular objects one is defining rather than considering any structures which may be formed with them.

Partly this strictly definitional idiom is motivated by the desire to ensure that the specification is consistent, and hence that the specification as a whole does indeed have a model.
That requirement is fulfilled by a style of formal mathematics similar to that advocated by Frege \cite{frege1980} and Russell \cite{russellPRM,russell10}.
The idea here is most clearly articulated by Gottl\"ob Frege's (`logicist') dictum that:

\begin{quote}
Mathematics = Logic + Definitions
\end{quote}

Since Frege, philosophers (other than hard core logicists) have generally considered this to require a notion of logic somewhat stronger than they were willing to accept, but a more general acceptance has nevertheless accrued to the variant:

\begin{quote}
Mathematics = Set-theory + Definitions
\end{quote}

To which one may add that Higher Order Logic with infinity and choice, is a sufficient alternative to set theory to cope with a large part of mathematics (including more than enough for systems engineering).

\ignore{
This is a perspective on mathematics which is consistent with the conduct of mathematics in the 20th Century, but which contrasts with the more formalistic perspective inspired by David Hilbert of much work in mathematical logic, including the thinking of Wilfred Hodges on Model Theory \cite{hodgesSEPMT,hodgesSMT}, which underpins the architectural thinking of Charles Dickerson et. al.\cite{dickerson08,dickerson2020architecture}.
}%ignore

Higher Order Logic, construed under the `standard' semantics, is \emph{quasi-categorical}, i.e. it has only one model (up-to-isomorphism) at any cardinality.
A typical specification will involve a large vocabulary of interdefined names, and the general ethos is more similar to that of programming languages, in which names, for data structures, functions or procedures, are \emph{defined} rather than axiomatically constrained.
This contrasts with the more algebraic flavour typical of model theory, in which the signature of the models is constrained by a set of axioms en bloc.

The rationale for this is twofold.
First, this does make specifications easier to understand.
Secondly, it enables consistency of the specification to be ensured.
Normally a discipline of specification by \emph{conservative extension} is adopted.
This means that, each additional `axiom' is introduced to constrain one or more new constants, and it is established that the extension to the theory thus obtained does not eliminate any of the previous models of the theory, but just extends the signature with new values.
This is done by proving prior to the extension (often but not always automatically) that there already exist values which might be given to the new names which satisfy the axiom used to introduce them.
The axiom which introduces the new names need not uniquely determine their values however.
This allows for what I like to call `loose specifications', but which have sometimes been called `partial definitions' to the derision of Hodges in \cite{hodgesSEPMT} who considers this nonsensical.
Notwithstanding that opinion, these conservative but incomplete constraints are registered in the theory as `definitions', whereas, if a non conservative extension is undertaken (which is very rare and tends to be deprecated) that is shown baldly as an axiom.

The primitive logic is very small and has a minimal signature, but most specifications will make use of a library of theories defining a range of mathematical entities or data types with appropriate relations, functions and operations over them, and even a small specification such as the one below will have a fairly rich signature just because of the formal context in which it occurs.
However, specifications, including those in the libary, are structured into a heirarchy of HOL theories, using that latter term in this context as a concept not dissimilar to a module in a programming language.
One may therefore think of each separate HOL theory as being specified in a fixed linguistic context and think of the models of that theory separately as structures whose signature corresponds to the various names introduced in that HOL theory.

Such theories can be separately listed, and the signature and the constraints imposed by the theory on the values of the names in the signature can be read off the theory listing.
Of course, these are not relational sinatures or structures.
This may be seen for the specification undertaken below which is listed in appendix \ref{Theory1}.
The signature of the theory may be read from the earlier parts of the theory listing, notably, the type abbreviations, type definitions and constant names shown with their type.
The constraints, determining which structures with that signature are models of the theory, are shown either as \emph{definitions} in the case that they have been shown to be conservative, or otherwise as \emph{axioms}.

\subsection{The Formal Model}

The following simple formal model is provided using the specification language \ProductHOL{}, an implementation of Higher Order Logic supported by the {\Product} proof tool.
This is not an example of architecture specification, but a model of the process, in which architectural models are mentioned, and reasoned about, but not exhibited or exemplified.

=SML
open_theory "hol";
force_new_theory "⦏arch⦎";
set_pc "hol1";
=TEX

\subsubsection{System Requirements}

We place no constraint on the type used to model the system.
The type used must yield sufficiently precise models for it to be definite whether or not any instance of that type does or does not model a system meeting the requirement.
The type will therefore be determined during the requirements phase of the project.
In the following \ProductHOL{} model this type will be represented by the type variable $'sys$.

A statement of requirement is a property of systems or subsystems.
This is reflected in the following \emph{type abbreviation}, in which the type abbreviation REQ is parameterised by the type of system under consideration.

=SML
declare_type_abbrev(⦏"REQ"⦎,
	["'sys"], ⓣ'sys → BOOL⌝);
=TEX

It may be desirable to distinguish between critical or key requirements, each of which will be a predicate or propositional function, in which case the system requirements would be modelled as a pair of such predicates.
For present purposes we will address only the critical requirements, which are the ones which may warrant detailed formal verification.

\subsubsection{Architecture}

An architecture is the highest level of system design, exhibiting the top-level structure of a system implemented to meet a previously defined system requirement.

An architecture shows how systems of the required kind can be constructed.
It does so by identifying a number of components, stipulating the requirements which each of those components must satisfy, and providing a method for fitting together the components to forn a system of the required kind.
We assume that the subsystems or components of an architecture are of uniform type and are given names so that we can ensure that the correct requirement is applied to each component of the structure, and that the component is fitted in the right place into the whole.
Indexed collections are modelled using a set of names and a function from names to values, as seen in the following type abbreviation.

=SML
declare_type_abbrev(⦏"IC"⦎,
	["'el"], ⓣ(STRING SET × (STRING → 'el))⌝);
=TEX

The ``fitting together'' is modelled by a construction function which takes as an argument models of all the subsystems and delivers a model for the system which would result from using those components.
The following type abbreviation defines a type for such constructions, as a function from an indexed set of (models of) components to (a model of) the system built from from those components in the prescribed way.
The type abbreviation here shows that the type of such a constructor depends on the type of components (which we are supposing uniform, which can always be ensured by using a disjoint union if necessary) and the type of the resulting system.

=SML
declare_type_abbrev(⦏"CST"⦎, ["'sys", "'comp"],
			     ⓣ'comp IC → 'sys⌝);
=TEX

An architecture is then the combination of such a construction with the specifications of the components necessary for the resulting system to meet its requirement.
The component specifications are also supplied as an indexed set, the indexes (names) corresponding to those used in the indexed set of components required by the construction function.

=SML
declare_type_abbrev(⦏"ARCH"⦎, ["'sys", "'comp"],
			      ⓣ('comp) REQ IC × ('sys,'comp)CST⌝);
=TEX

The architecture is ``correct'' if applying the construction to components which meet their requirement will always result in a system which satisfies the system requirement.
Note that this is a higher order function and that in Church's variant of Higher Order Logic, function application is rendered by juxtaposition and does not require brackets round a single argument.
Application of the following function to a system requirement yields a property of architectures, viz. the property of being a correct way of building a system meeting the requirement.

ⓈHOLCONST
│ $⦏correct⦎ : ('sys)REQ → ('sys,'comp)ARCH → BOOL
├──────
│ ∀ arch req⦁ correct req arch ⇔
    ∀comps:'comp IC⦁
    		 (∀name:STRING⦁ name ∈ Fst (Fst arch) ⇒ name ∈ Fst comps
    	    	 ∧ (Snd (Fst arch) name)(Snd comps name))
		 ⇒ req (Snd arch comps)
■

\subsubsection{Composition}

This process is not exclusive to the top level, but can be iterated to give ever more detailed design.
At any stage the sequence of design steps undertaken can be gathered together to yield a single architecture for the system as a whole which reflects all the detail thus far elaborated.
If each step in that process is correct, then the resulting composition will also be correct.
We would therefore expect to be able to define in terms of this model the effect of composing two design steps where one designs a component or subsystem required by a previous design step, and then to be able to prove that if the two design steps are correct then so will be the result of the composition.

To reason about this kind of iterated composition it will be necessary to assume that sucessive stages in design composition yield systems of the same type (otherwise the result of a single composition would not have uniformly typed components).

ⓈHOLCONST
│ $⦏compose⦎ : ('sys,'comp)ARCH → STRING → ('comp,'comp)ARCH → ('sys,'comp)ARCH
├──────
│ ∀ (sarch:('sys,'comp)ARCH) n (carch:('comp,'comp)ARCH) ⦁ compose sarch n carch =
  let ((snames, sprops), scst) = sarch
  in let ((cnames, cprops), ccst) = carch
  in let newnames = (snames\{n}) ∪ cnames
  in let newspecs = (newnames, λs⦁ if s ∈ cnames then cprops s else sprops s)
  in let newcst = (λcis:'comp IC⦁
     	 let ssn = ccst (cnames, Snd cis)
	 in scst (snames, λm⦁ if m = n then ssn else (Snd cis) m))
  in	 (newspecs, newcst)
■

The composition method meets the following condition:
=GFT
composition_correct_thm = ⊢ ∀req sa ca n⦁
	     (Fst (Fst sa)) ∩ (Fst (Fst ca)) = {}
	     ∧ correct req sa
	     ∧ n ∈ (Fst (Fst sa))
	     ∧ correct (Snd (Fst sa) n) ca
	     ⇒ correct req (compose sa n ca)
=TEX

This has been proven, and the proof script is part of the source of this document, but the printing has been suppressed.
This document is a literate script from which the formal materials can be extracted and run through {\Product}.
The resulting theory can then be listed, and is shown in appemdix \ref{Theory1}.

\pagebreak
\appendix
\ignore{
\section{Partial Proof Log}
The proof system is a sequent calculus.
Each intermediate goal is displayed as a series of numbered assumptions followed by a conclusion, which is to be shown to follow from the assumptions.
Not all intermediate goals are shown in the log.
The commands to the prover are in Standard ML a functional language originally devised by Milner et.al.\cite{gordon79} for use in the LCF proof assistant and later used by Gordon for HOL \cite{gordon88} and ICL for \Product{}.
{\tiny
=SML
set_goal([], ⌜∀req sa ca n⦁
	     (Fst (Fst sa)) ∩ (Fst (Fst ca)) = {}
	     ∧ correct req sa ∧ n ∈ (Fst (Fst sa))
	     ∧ correct (Snd (Fst sa) n) ca
	     ⇒ correct req (compose sa n ca)⌝);

a (REPEAT ∀_tac
  THEN rewrite_tac ((map get_spec [⌜compose⌝,⌜correct⌝])@[let_def])
  THEN REPEAT strip_tac);
a (spec_nth_asm_tac 4 ⌜Fst (Fst sa),
                     (λ m
                       ⦁ if m = n
                         then Snd ca (Fst (Fst ca), Snd comps)
                         else Snd comps m)⌝);
=GFT Hol output
(* *** Goal "1" *** *)

(*    7 *)⌜∀ x⦁ ¬ (x ∈ Fst (Fst sa) ∧ x ∈ Fst (Fst ca))⌝
(*    6 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst sa)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst sa) name (Snd comps name))
               ⇒ req (Snd sa comps)⌝
(*    5 *)⌜n ∈ Fst (Fst sa)⌝
(*    4 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst ca)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst ca) name (Snd comps name))
               ⇒ Snd (Fst sa) n (Snd ca comps)⌝
(*    3 *)⌜∀ name
           ⦁ name ∈ Fst (Fst sa) ∧ ¬ name = n ∨ name ∈ Fst (Fst ca)
               ⇒ name ∈ Fst comps
                 ∧ (if name ∈ Fst (Fst ca)
                     then Snd (Fst ca) name
                     else Snd (Fst sa) name)
                   (Snd comps name)⌝
(*    2 *)⌜name ∈ Fst (Fst sa)⌝
(*    1 *)⌜¬ name
               ∈ Fst
                 (Fst (Fst sa),
                     (λ m
                       ⦁ if m = n
                         then Snd ca (Fst (Fst ca), Snd comps)
                         else Snd comps m))⌝

(* ?⊢ *)⌜req
             (Snd
                 sa
                 (Fst (Fst sa),
                     (λ m
                       ⦁ if m = n
                         then Snd ca (Fst (Fst ca), Snd comps)
                         else Snd comps m)))⌝
=SML
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
=GFT ProofPower output
(* *** Goal "2" *** *)
(*    7 *)⌜∀ x⦁ ¬ (x ∈ Fst (Fst sa) ∧ x ∈ Fst (Fst ca))⌝
(*    6 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst sa)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst sa) name (Snd comps name))
               ⇒ req (Snd sa comps)⌝
(*    5 *)⌜n ∈ Fst (Fst sa)⌝
(*    4 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst ca)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst ca) name (Snd comps name))
               ⇒ Snd (Fst sa) n (Snd ca comps)⌝
(*    3 *)⌜∀ name
           ⦁ name ∈ Fst (Fst sa) ∧ ¬ name = n ∨ name ∈ Fst (Fst ca)
               ⇒ name ∈ Fst comps
                 ∧ (if name ∈ Fst (Fst ca)
                     then Snd (Fst ca) name
                     else Snd (Fst sa) name)
                   (Snd comps name)⌝
(*    2 *)⌜name ∈ Fst (Fst sa)⌝
(*    1 *)⌜¬ Snd
               (Fst sa)
               name
               (Snd
                   (Fst (Fst sa),
                       (λ m
                         ⦁ if m = n
                           then Snd ca (Fst (Fst ca), Snd comps)
                           else Snd comps m))
                   name)⌝

(* ?⊢ *)⌜req
             (Snd
                 sa
                 (Fst (Fst sa),
                     (λ m
                       ⦁ if m = n
                         then Snd ca (Fst (Fst ca), Snd comps)
                         else Snd comps m)))⌝
=SML
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
a (spec_nth_asm_tac 3 ⌜name⌝ THEN_TRY asm_rewrite_tac[]);
=GFT Hol output
(* *** Goal "2.1" *** *)

(*    7 *)⌜∀ x⦁ ¬ (x ∈ Fst (Fst sa) ∧ x ∈ Fst (Fst ca))⌝
(*    6 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst sa)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst sa) name (Snd comps name))
               ⇒ req (Snd sa comps)⌝
(*    5 *)⌜name ∈ Fst (Fst sa)⌝
(*    4 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst ca)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst ca) name (Snd comps name))
               ⇒ Snd (Fst sa) name (Snd ca comps)⌝
(*    3 *)⌜∀ name'
           ⦁ name' ∈ Fst (Fst sa) ∧ ¬ name' = name ∨ name' ∈ Fst (Fst ca)
               ⇒ name' ∈ Fst comps
                 ∧ (if name' ∈ Fst (Fst ca)
                     then Snd (Fst ca) name'
                     else Snd (Fst sa) name')
                   (Snd comps name')⌝
(*    2 *)⌜¬ req
               (Snd
                   sa
                   (Fst (Fst sa),
                       (λ m
                         ⦁ if m = name
                           then Snd ca (Fst (Fst ca), Snd comps)
                           else Snd comps m)))⌝
(*    1 *)⌜¬ name ∈ Fst (Fst ca)⌝

(* ?⊢ *)⌜Snd (Fst sa) name (Snd ca (Fst (Fst ca), Snd comps))⌝

=SML
a (var_elim_nth_asm_tac 2);
a (spec_nth_asm_tac 4 ⌜(Fst (Fst ca), Snd comps)⌝);
=GFT ProofPower output
(* *** Goal "2.1.1" *** *)

(*    9 *)⌜∀ x⦁ ¬ (x ∈ Fst (Fst sa) ∧ x ∈ Fst (Fst ca))⌝
(*    8 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst sa)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst sa) name (Snd comps name))
               ⇒ req (Snd sa comps)⌝
(*    7 *)⌜name ∈ Fst (Fst sa)⌝
(*    6 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst ca)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst ca) name (Snd comps name))
               ⇒ Snd (Fst sa) name (Snd ca comps)⌝
(*    5 *)⌜∀ name'
           ⦁ name' ∈ Fst (Fst sa) ∧ ¬ name' = name ∨ name' ∈ Fst (Fst ca)
               ⇒ name' ∈ Fst comps
                 ∧ (if name' ∈ Fst (Fst ca)
                     then Snd (Fst ca) name'
                     else Snd (Fst sa) name')
                   (Snd comps name')⌝
(*    4 *)⌜¬ req
               (Snd
                   sa
                   (Fst (Fst sa),
                       (λ m
                         ⦁ if m = name
                           then Snd ca (Fst (Fst ca), Snd comps)
                           else Snd comps m)))⌝
(*    3 *)⌜¬ name ∈ Fst (Fst ca)⌝
(*    2 *)⌜name' ∈ Fst (Fst ca)⌝
(*    1 *)⌜¬ name' ∈ Fst (Fst (Fst ca), Snd comps)⌝

(* ?⊢ *)⌜Snd (Fst sa) name (Snd ca (Fst (Fst ca), Snd comps))⌝

=SML
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
=GFT ProofPower output
(* *** Goal "2.1.2" *** *)

(*    9 *)⌜∀ x⦁ ¬ (x ∈ Fst (Fst sa) ∧ x ∈ Fst (Fst ca))⌝
(*    8 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst sa)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst sa) name (Snd comps name))
               ⇒ req (Snd sa comps)⌝
(*    7 *)⌜name ∈ Fst (Fst sa)⌝
(*    6 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst ca)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst ca) name (Snd comps name))
               ⇒ Snd (Fst sa) name (Snd ca comps)⌝
(*    5 *)⌜∀ name'
           ⦁ name' ∈ Fst (Fst sa) ∧ ¬ name' = name ∨ name' ∈ Fst (Fst ca)
               ⇒ name' ∈ Fst comps
                 ∧ (if name' ∈ Fst (Fst ca)
                     then Snd (Fst ca) name'
                     else Snd (Fst sa) name')
                   (Snd comps name')⌝
(*    4 *)⌜¬ req
               (Snd
                   sa
                   (Fst (Fst sa),
                       (λ m
                         ⦁ if m = name
                           then Snd ca (Fst (Fst ca), Snd comps)
                           else Snd comps m)))⌝
(*    3 *)⌜¬ name ∈ Fst (Fst ca)⌝
(*    2 *)⌜name' ∈ Fst (Fst ca)⌝
(*    1 *)⌜¬ Snd (Fst ca) name' (Snd (Fst (Fst ca), Snd comps) name')⌝

(* ?⊢ *)⌜Snd (Fst sa) name (Snd ca (Fst (Fst ca), Snd comps))⌝

=SML
a (spec_nth_asm_tac 5 ⌜name'⌝);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
a (DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac[]);
a (REPEAT strip_tac);

=GFT ProofPower output
(* *** Goal "2.2" *** *)

(*    9 *)⌜∀ x⦁ ¬ (x ∈ Fst (Fst sa) ∧ x ∈ Fst (Fst ca))⌝
(*    8 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst sa)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst sa) name (Snd comps name))
               ⇒ req (Snd sa comps)⌝
(*    7 *)⌜n ∈ Fst (Fst sa)⌝
(*    6 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst ca)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst ca) name (Snd comps name))
               ⇒ Snd (Fst sa) n (Snd ca comps)⌝
(*    5 *)⌜∀ name
           ⦁ name ∈ Fst (Fst sa) ∧ ¬ name = n ∨ name ∈ Fst (Fst ca)
               ⇒ name ∈ Fst comps
                 ∧ (if name ∈ Fst (Fst ca)
                     then Snd (Fst ca) name
                     else Snd (Fst sa) name)
                   (Snd comps name)⌝
(*    4 *)⌜name ∈ Fst (Fst sa)⌝
(*    3 *)⌜¬ req
               (Snd
                   sa
                   (Fst (Fst sa),
                       (λ m
                         ⦁ if m = n
                           then Snd ca (Fst (Fst ca), Snd comps)
                           else Snd comps m)))⌝
(*    2 *)⌜name ∈ Fst comps⌝
(*    1 *)⌜(if name ∈ Fst (Fst ca)
               then Snd (Fst ca) name
               else Snd (Fst sa) name)
             (Snd comps name)⌝

(* ?⊢ *)⌜Snd
             (Fst sa)
             name
             (if name = n
                 then Snd ca (Fst (Fst ca), Snd comps)
                 else Snd comps name)⌝

=SML
a (POP_ASM_T ante_tac
  THEN (spec_nth_asm_tac 8 ⌜name⌝)
  THEN asm_rewrite_tac[]
  THEN strip_tac);
a (spec_nth_asm_tac 7 ⌜(Fst (Fst ca), Snd comps)⌝);
=GFT ProofPower output
(* *** Goal "2.2.1" *** *)

(*   12 *)⌜∀ x⦁ ¬ (x ∈ Fst (Fst sa) ∧ x ∈ Fst (Fst ca))⌝
(*   11 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst sa)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst sa) name (Snd comps name))
               ⇒ req (Snd sa comps)⌝
(*   10 *)⌜n ∈ Fst (Fst sa)⌝
(*    9 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst ca)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst ca) name (Snd comps name))
               ⇒ Snd (Fst sa) n (Snd ca comps)⌝
(*    8 *)⌜∀ name
           ⦁ name ∈ Fst (Fst sa) ∧ ¬ name = n ∨ name ∈ Fst (Fst ca)
               ⇒ name ∈ Fst comps
                 ∧ (if name ∈ Fst (Fst ca)
                     then Snd (Fst ca) name
                     else Snd (Fst sa) name)
                   (Snd comps name)⌝
(*    7 *)⌜name ∈ Fst (Fst sa)⌝
(*    6 *)⌜¬ req
               (Snd
                   sa
                   (Fst (Fst sa),
                       (λ m
                         ⦁ if m = n
                           then Snd ca (Fst (Fst ca), Snd comps)
                           else Snd comps m)))⌝
(*    5 *)⌜name ∈ Fst comps⌝
(*    4 *)⌜¬ name ∈ Fst (Fst ca)⌝
(*    3 *)⌜Snd (Fst sa) name (Snd comps name)⌝
(*    2 *)⌜name' ∈ Fst (Fst ca)⌝
(*    1 *)⌜¬ name' ∈ Fst (Fst (Fst ca), Snd comps)⌝

(* ?⊢ *)⌜Snd
             (Fst sa)
             name
             (if name = n
                 then Snd ca (Fst (Fst ca), Snd comps)
                 else Snd comps name)⌝

=SML
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
=GFT ProofPower output
(* *** Goal "2.2.2" *** *)

(*   12 *)⌜∀ x⦁ ¬ (x ∈ Fst (Fst sa) ∧ x ∈ Fst (Fst ca))⌝
(*   11 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst sa)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst sa) name (Snd comps name))
               ⇒ req (Snd sa comps)⌝
(*   10 *)⌜n ∈ Fst (Fst sa)⌝
(*    9 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst ca)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst ca) name (Snd comps name))
               ⇒ Snd (Fst sa) n (Snd ca comps)⌝
(*    8 *)⌜∀ name
           ⦁ name ∈ Fst (Fst sa) ∧ ¬ name = n ∨ name ∈ Fst (Fst ca)
               ⇒ name ∈ Fst comps
                 ∧ (if name ∈ Fst (Fst ca)
                     then Snd (Fst ca) name
                     else Snd (Fst sa) name)
                   (Snd comps name)⌝
(*    7 *)⌜name ∈ Fst (Fst sa)⌝
(*    6 *)⌜¬ req
               (Snd
                   sa
                   (Fst (Fst sa),
                       (λ m
                         ⦁ if m = n
                           then Snd ca (Fst (Fst ca), Snd comps)
                           else Snd comps m)))⌝
(*    5 *)⌜name ∈ Fst comps⌝
(*    4 *)⌜¬ name ∈ Fst (Fst ca)⌝
(*    3 *)⌜Snd (Fst sa) name (Snd comps name)⌝
(*    2 *)⌜name' ∈ Fst (Fst ca)⌝
(*    1 *)⌜¬ Snd (Fst ca) name' (Snd (Fst (Fst ca), Snd comps) name')⌝

(* ?⊢ *)⌜Snd
             (Fst sa)
             name
             (if name = n
                 then Snd ca (Fst (Fst ca), Snd comps)
                 else Snd comps name)⌝
=SML
a (spec_nth_asm_tac 8 ⌜name'⌝);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[] THEN strip_tac);
a (DROP_NTH_ASM_T 3 ante_tac THEN asm_rewrite_tac[]);
=GFT ProofPower output
(* *** Goal "2.2.3" *** *)

(*   11 *)⌜∀ x⦁ ¬ (x ∈ Fst (Fst sa) ∧ x ∈ Fst (Fst ca))⌝
(*   10 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst sa)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst sa) name (Snd comps name))
               ⇒ req (Snd sa comps)⌝
(*    9 *)⌜n ∈ Fst (Fst sa)⌝
(*    8 *)⌜∀ comps
           ⦁ (∀ name
               ⦁ name ∈ Fst (Fst ca)
                   ⇒ name ∈ Fst comps ∧ Snd (Fst ca) name (Snd comps name))
               ⇒ Snd (Fst sa) n (Snd ca comps)⌝
(*    7 *)⌜∀ name
           ⦁ name ∈ Fst (Fst sa) ∧ ¬ name = n ∨ name ∈ Fst (Fst ca)
               ⇒ name ∈ Fst comps
                 ∧ (if name ∈ Fst (Fst ca)
                     then Snd (Fst ca) name
                     else Snd (Fst sa) name)
                   (Snd comps name)⌝
(*    6 *)⌜name ∈ Fst (Fst sa)⌝
(*    5 *)⌜¬ req
               (Snd
                   sa
                   (Fst (Fst sa),
                       (λ m
                         ⦁ if m = n
                           then Snd ca (Fst (Fst ca), Snd comps)
                           else Snd comps m)))⌝
(*    4 *)⌜name ∈ Fst comps⌝
(*    3 *)⌜¬ name ∈ Fst (Fst ca)⌝
(*    2 *)⌜Snd (Fst sa) name (Snd comps name)⌝
(*    1 *)⌜Snd (Fst sa) n (Snd ca (Fst (Fst ca), Snd comps))⌝

(* ?⊢ *)⌜Snd
             (Fst sa)
             name
             (if name = n
                 then Snd ca (Fst (Fst ca), Snd comps)
                 else Snd comps name)⌝
=SML
a (cases_tac ⌜name = n⌝ THEN asm_rewrite_tac[]);
val composition_correct_thm = save_pop_thm "composition_correct_thm";
=GFT ProofPower ouput
Tactic produced 0 subgoals:
Current and main goal achieved
val it = (): unit
Now 0 goals on the main goal stack
val composition_correct_thm =
   ⊢ ∀ req sa ca n
     ⦁ Fst (Fst sa) ∩ Fst (Fst ca) = {}
           ∧ correct req sa
           ∧ n ∈ Fst (Fst sa)
           ∧ correct (Snd (Fst sa) n) ca
         ⇒ correct req (compose sa n ca): THM
=TEX
}%tiny
}%ignore

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{arch.th}
}%\let


\section{Bibliography}\label{Bibliography}

{\raggedright
\bibliographystyle{rbjfmu}
\bibliography{rbj,fmu}
} %\raggedright

\twocolumn[\section{Index of Formal Names}\label{index}]
{\small\printindex}

\end{document}
