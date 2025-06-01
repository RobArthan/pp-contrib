=IGN
$Id: t002.doc,v 1.7 2009/05/21 08:59:45 rbj Exp $
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
%\usepackage{hyperref}
\ftlinepenalty=9999
\usepackage{A4}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}

\newcommand{\ignore}[1]{}

\title{The Formalisation of Physics}
\author{Roger Bishop Jones}
\date{\ }

\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

\makeindex

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
This document provides an example illustrating a method of formalising physical theories, together with a discussion of some aspects of {\it semantic positivism}.
\end{abstract}
\vfill

\begin{centering}

{\footnotesize

Created 2004/07/15

Last Change $ $Date: 2009/05/21 08:59:45 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t002.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t002.pdf}

$ $Id: t002.doc,v 1.7 2009/05/21 08:59:45 rbj Exp $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize

\end{centering}

\thispagestyle{empty}
\end{titlepage}
\newpage
\addtocounter{page}{1}
%\section{DOCUMENT CONTROL}
%\subsection{Contents list}
\tableofcontents
%\newpage
%\subsection{Document cross references}

\subsection*{To Do}
\begin{itemize}

\item Much.

\end{itemize}

%{\raggedright
%\bibliographystyle{fmu}
%\bibliography{rbj,fmu}
%} %\raggedright

\newpage
\section{Introduction}\label{Introduction}

This document was originally begun to illustrate a method of formalisation of scientific theories, and to compare and contrast that method with the corresponding methods and doctrines of the philosophy of {\it logical positivism} as represented by the philosophy of Rudolf Carnap.

From this preliminary work has appeared a connection with certain proposed fairly radical changes to the way in which Physics is taught.
The principle advocate of these changes is David Hestenes who, after a lifetime of working on the applications of geometric algebra in Physics now proposes that the mathematics of Physics should be simplified by the use of geometric algebra and geometric calculus as a uniform mathematical framework for physics in place of the bewildering diversity of mathematical theories at present employed.

The unnecessary complexity which Hestenes considers so detrimental to the teaching of physics contributes to the cost of formalising physics, and the reasons for teaching physics using geometric algebra are also reasons for formalising physics using geometric algebra.

A principle difference between the methods advocated here and those of Carnap is that the proposed approach follows much more closely than ever Carnap did, received accounts of mathematics and physics.
The innovation is primarily simply in the formality, the mathematics and physics is not intended for the kind of radical change which is implicit in Carnap's phenomenalistic approach (this can be said without any close inspection of the details of his phenomenalism simply because physics is not phenomenalistic).
Even Carnap's physicalistic language (with which I am not familiar) seems unlikely to be anywhere near as close received mathematical physics as we aim to be, if only because Carnap does not seem to see the separate development of mathematics as something one which his formalisation of physics should be based.

The upshot of this is that this essay at formal physics is expected as soon as possible to be replaced by one which is based on the geometric calculus.

\section{Philosophical Preliminaries}

\subsection{Carnap's Methods for Formalising Scientific Theories}

The following description is based on a reading of Carnap's ``Philosophy and Logical Syntax'' (1935) and a superficial acquaintance with his ``Meaning and Necessity'' (1947, 56), i.e. on some of his explanations of methods rather than his own application to phenomenalistic or physicalistic languages.

Carnap advocated that object languages be defined using meta-languages and that such a language definition consists of the following:
\begin{itemize}
\item Formation Rules: the definition of the syntactic rules of well-formedness for sentences in the object language.
\item Transformation Rules: rules of inference which together define the relation of immediate consequence.  Rules are either L-rules (logical) or P-rules (physical) the former capturing logical consequence the latter laws of physics.
\end{itemize}

All these rules are defined in the metalanguage.
The rules then permit the derivation of conclusions in the object language, which will be L-valid (logical, necessary or analytic truths) if they can be derived from L-rules alone, and otherwise P-valid or synthetic truths.

In his later work Carnap addressed semantic issues, the semantics also being provided by rules specified in some metalanguage.
I don't know what he said about the connection between the syntactic and the semantic rules, but I will suppose for present purposes that he recognised the desirability of demonstrating that the syntactic rules respect the semantic rules so that they permit only the derivation of the relevant kinds of truths.

I observe here that I have seen no trace of the Frege's idea that one begins with a logic and then proceeds (at least so far as mathematics) by definition, where definitions are rather special things, not just arbitrary rules.
It is clear that Carnap is aware of this feature of Frege's thought (having studied under Frege), and it is present in some of his own accounts of the new logic and the status of mathematics, but it is not conspicuous in some of his accounts of the methods he advocated, for example in Carnap35.

\subsection{The Present Method}

The present method is drawn from one subculture of the community of researchers in the Computer Science subdiscipline engaged in applying {\it formal methods} to the verifiction of computer software and hardware.
These methods are based on the advances in Mathematical Logic which took place during the twentieth century, but these methods have been adapted, primarily in pragmatic rather than fundamental ways, to meet the needs of computer science and information systems engineering.
The approach to these matters to be described is best exemplified by the work of the Automated Reasoning Group at the University of Cambridge, and more specifically, of the Hardware Verification Group.

The approach involves the use of a {\it logical foundation system}.
A logical foundation system is a logical system which is sufficiently ``strong'' that a substantial body of mathematics can be developed within that logical system {\it using only conservative extensions} to the logic.
It exemplifies the idea of Frege and Russell that ``mathematics = logic + definitions''.
The first logical foundation systems were the logical sysetem of Frege (though unfortunately inconsistent) and Russell's Theory of Types.
Since then the most widely used foundation system has been Zermelo-Fraenkel set theory.
The foundation system adopted by the Cambridge HVG, and implemented as a computer program supporting formal specification and proof, was a variant of Higher Order Logic, derived from Russell's Theory of Types after simplification first by Ramsey and then by Church, further modified by Gordon who added Milner style polymorphism and appropriate definitional mechanisms while implementing the logic as an LCF-like proof assistant.

The machine support for this logical system is not our present concern.
Its methodological implications are.

The method for formalising some physical theory corresponding to Carnap's method above is as follows.
The formalisation of a physical theory is undertaken in several stages:

\begin{enumerate}
\item define the syntax and semantics of the primitive logical system
\item demonstrate the soundness of the logical system
\item define a rich vocabulary of logical and mathematical concepts and prove various results involving these concepts
\item define various applied concepts, culminating in the definition of an abstract model of the intended physical system, incorporating by definition the proposed physical laws (i.e. define an appropriate base class of abstract models and define the subclass of those models which satisfy the proposed laws as expressed in terms of that base class).
\item derive consequences of the physical theory by reasoning about the abstract model
\end{enumerate}

Of these steps only steps 1 and 2 are conducted in a meta-language.
Thereafter progress is achieved by definitions (which are a special kind of new axiom expressed in the object language), and by derivation in the deductive system of the object language.

Most of the work takes place in the object language, the preliminary metalinguistic work concerns only the primitive logic, which is very simple indeed (3 primitive type constructors, 3 primitive logical constants, 5 axioms, 7 rules), and is undertaken only once, different applications requiring no change to this primitive logic.
This system was defined in the early eighties and has been in use worldwide for a wide variety of applications ever since.
Resort to the metalanguage used for definition of the language is therefore very rare indeed, all language extensions required for new applications taking place by definition or other conservative extensions in the object language.

This method:
\begin{itemize}
\item is {\it foundationalist} in that it is based on the use of a ``logical foundation system''
\item minimises resort to metalanguage, which is not required for the development of new applications
\item involves no distinction between L concepts and P concepts
\item results in an entirely analytic formal theory (all theorems are analytic
\footnote{
A sentence is analytic if its truth follows from its meaning alone.
The theorems of any deductive system which has been shown to be sound with respect to its semantics are therefore analytic.
}
 truths)
\end{itemize}

The connection with the real world is accomplished entirely informally, by claims in plain English about which physical systems the abstract models reflect.
For the application of these models, even if they are theories of physics, it is not necessary to assert that the theories are ``true''.
It suffices to state what evidence has been gathered to establish the fidelity or utility of the model.

In the remainder of this paper formalisation of Newtonians laws of motion and gravitation is undertaken.
This involves aswering the question of what the universe must be like in order for Newton's laws to hold.
Contrary to common practice among positivists the author prefers not to reserve the word ``metaphysics'' for the synthetic a priori, or for nonesense.
There are various aspects of the formalisation of Newton's laws which might be considered metaphysical.
Questions about the nature of space and time, about what are the constituents of the universe, for example, might be considered metaphysics.
However, in {\it semantic positivism} the nature of metaphysics and the lines of demarcation between it and other disciplines are of no great importance, in particular they play no role in distinguishing a good from a bad scientific theory, and no role more generally in distinguishing meaningful from meaningless sentences.

The method illustrated by the paper suffices to give {\it abstract} meaning to concepts, which in turn suffices to determine which sentences involving those concepts are analytically, logically, or necessarily true.
Concrete semantics, where concepts are intended to refer to the real world, is more difficult to establish, and can probably only be supplied informally rather than formally.
That a scientific theory is significant is considered primarily a pragmatic matter.
Does it turn out to be useful?

\subsection{Other Issues}

\begin{itemize}
\item Foundationalism in respect of a priori truths.
\item The role of semantic ascent in determining analyticity.
\item The character and role of ``metaphysics''.
\item The fuzzy boundaries between logic, mathematics, metaphysics and physics.
\end{itemize}

\subsection{What is the point of formalising physics?}

There are lots of different answers to this question, many of which I am not well qualified to articulate.
Nevertheless I am going to mention as many as I can think of, and I'm going to try to bring out the ways in which these different reasons for formalising physical theories may result in different approaches to the formalisation, in different ideas about what questions are {\it interesting} and {\it valuable} and in criteria for evaluating success.

I use these different perspectives to help clarify the nature of my own interests and enterprise.

\subsubsection{Russell and Carnap}

Carnap's own work on formalisation and his philosophical programme as a whole seemed to have been inspired by Russell's achievement (with Whitehead) in {\it Principia Mathematica} and with by Russell's idea that philosophy could be made into a ``scientific'' discipline by the new methods of logic.

On page 13 of the Schilpp volume (Library of Living Philosophers) Carnap says:

\begin{quotation}
``Whereas Frege had the strongest influence on me in the 
fields of logic and semantics, in my philosophical thinking
in general I learned most from Bertrand Russell.''
\end{quotation}

Futher down the page he gives a quote from Russell which includes:

\begin{quotation}
``The study of logic becomes the central study in philosophy:
it gives the method of research in philosophy just as
mathematics gives the method in physics...
All this supposed knowledge in the traditional systems must
be swept away, and a new beginning must be made. . . .
To the large and still growing body of men engaged in the
pursuit of science, . . .

``The new method, successful already
in such time-honored problems as number, infinity, continuity,
space and time, should make an appeal which the older methods
have wholly failed to make. The one and only condition,
I believe, which is necessary in order to secure for
philosophy in the near future an achievement surpassing
all that has hitherto been accomplished by philosophers,
is the creation of a school of men with scientific
training and philosophical interests, unhampered by
the traditions of the past, and not misled by the
literary methods of those who copy the ancients in
all except their merits.''
\end{quotation}

Carnap then says:

\begin{quotation}
``I felt as if this idea had been addressed to me personally.
To work in this spirit would be my task from now on!
And indeed henceforth the application of the new logical
instrument for the purpose of analysing scientific concepts
and of clarifying philosophical problems has been the
essential aim of my philosophy ever since.''
\end{quotation}

Carnap appears to have viewed the formalisation of phenomenalistic and physicalistic languages as ways of doing scientifically oriented philosophy, and of illuminating ,for example, questions in epistemology.
He didn't conceive of formalisation as a method for doing {\it metaphysics}, because the conception of metaphysics which he shared with the other logical positivists, and with most other positivists, made metaphysics into, by definition, not something anyone would want to do ({\it nonesense}).

Now so far as {\it semantic positivism} is concerned, the position is liberalised.
Firstly there is no inclination to {\it define} metaphysics in such a way as to marginalise it.
Secondly there is a recognition of the importance of limits in what can be formalised, of the tendency for mathematisation or formalisation, once realised, to transfer a subject matter out of philosophy into some special science, and of the particular interest of philosophy in just those problem domains which resists the kind of systematisation which renders them scientific.

Where is the positivism here?
Has not {\it semantic} positivism been liberalised beyond the point of properly being called positivism at all?
The positivism remains in the recognition that pathology is possible and pervasive.
The method proposed is to study the limits of formalisation, to study how these limits may be extended, to understand how questions can be made definite which previously were not, and to give particular attention to those problems which are close enough to those which can be treated rigorously that we can hope that they may be brought into the fold. 

\subsubsection{Mathematicians}

Newton's laws of motion and gravitation form the basis for a substantial body of mathematical theory and for widely applicable mathematical methods.

In these kinds of applications it is typical to consider not the significance of Newton's Laws for the Universe as a whole, but rather their implications in idealised models of fragments of the Universe.
Typically, an application is underpinned by what may be called ``modelling assumptions''.
Such assumptions are counterfactual idealisations which make tractable a theory which might otherwise be too complex to be applicable, while remaining close enough to reality for the resulting theory to give acceptably accurate predictions for a worthwhile range of applications.

The kinds of models which are worth investigating from this point of view are likely to be quite different from those which are of interest to a cosmologist, or a metaphysician.

\subsubsection{Physicists}




\subsubsection{Computer Scientists and Information Engineers}

The step for science and engineering from mathematisation to formalisation, is more likely to be motivated by engineering 

\subsubsection{Metaphysicians}

For the kind of metaphysics which I have in mind here, the significance of Newton's Laws is in what they entail about how the Universe might be.

From this point of view, the kind of counterfactual but pragmatic ``modelling assumption'' which occurs in applied mathematics is not of interest.
From my metaphysical stance, the interest is in questions like ``what might the universe be like if Newton's laws were true''?
The assumption that there are just three bodies make it possible to obtain interesting and applicable mathematics from Newton's laws, but this is not the kind of assumption which is likely to yield interesting metaphysical conclusions.

A mathematician reasoning about particulate Newtonian Universes may naturally assume that the number of particles in the Universe is finite, but a metaphysician is likely to want to know what constraints on the cardinality of a particulate universe flow from Newton's Laws.
Whether this question yeilds interesting or applicable mathematical theories is not his concern.

\section{Technical Preliminaries}\label{TechnicalPreliminaries}


\subsection{Newton's Laws of Motion}

Newton gave three laws of motion as follows:

\begin{enumerate}

\item Every object persists in its state of rest or uniform motion unless it is compelled to change that state by forces impressed upon it.

\item Force is equal to the change in momentum (mV) per change in time. (for a constant mass, force equals mass times acceleration, F = ma)

\item For every action there is an equal and opposite reaction.

\end{enumerate}

\ignore{
\begin{enumerate}
\item Every body will remain at rest, or in a uniform state of motion unless acted upon by a force.
\item When a force acts upon a body, it imparts an acceleration proportional to the force and inversely proportional to the mass of the body and in the direction of the force.
\item Every action has an equal and opposite reaction.
\end{enumerate}
}

\subsection{Technical Prelude}

First of all, we must give the the ML commands to  introduce the new theory ``t002a'' as a child of the theory ``hol'' adding the parent ``diffgeom''.
The latter provides some elements of differential geometry required in this application.

=SML
open_theory "hol";
force_new_theory "t002a";
new_parent "diffgeom";
=TEX

\subsection{Some Mathematics}

The mathematics used for this example has been developed in the \ProductHOL language using the \Product system.
Since this development, a modern variant of the kind of work undertaken by Russell and Whitehead in {\it Principia Mathematica} proceeds from a small set of primitive axioms and rules via a large number of definitions and proofs, it is fairly extended, and an account of this development is beyond the scope of this document.

The concepts to be employed in this example will be given an informal explanation, and all the formal treatment is available online to anyone who is interested in digging deeper.

The mathematical theory required for the formalisation of Newton's laws falls within the field of differential geometry.
It is usual to suppose Newton's laws formulated in a three dimensional euclidean space.
In fact the concept of {\it normed real vector space} suffices for our present purposes, and we have available to us a {\it type constructor} (NVS) which yeilds a type of normed real vector spaces over some type of vector.
The first attempts have therefore been to express Newton's laws as properties of normed real vector spaces.

It is intended that this will be superceded by treatments based upon geometric algebra and the geometric calculus as soon as this becomes feasible.

\subsection{Space and Time}

It is desirable philosophically to give close attention to the logic of arguments about space and time, and this requires the adoption of a mathematical framework which does not unduly prejudice our conception of the nature of space and time.
In particular it should not interfere with the coherence of reasoning about whether space-time is Galilean or relativistic, or the question of whether it is curved or flat. 
The preliminary work here was simply directed to formalisation of Newtonian physics, and therefore did not seek a neutral context in which one can reason about special or general relativity.

It is normally understood that Newton's laws are to be understood in the context of the universe conceived as a three dimensional Euclidean space and that the spatial dimensions and time are all openended continuum.
These dimensions are naturally modelled by the real line which is represented in \ProductHOL by the type $ⓣℝ⌝$.
It is also necessary to have a measure of distance available, and the required mathematical theory is therefore that of a normed real vector space.

Normed real vector spaces are available to us via the type constructor $ⓣ'a NVS⌝$ which for each type $ⓣ'a⌝$ gives a type of normed vector spaces in which the elements are vectors whose type is $ⓣ'a⌝$.
In fact, Newton's laws can be expressed in terms of any normed real vector space, but the small additional extra complexity arising in such a formulation makes it preferable for the purposes of this example to work specifically with the specific normed vector space of interest which is named $⌜ℝ⋏3⋎NVS⌝$.
The relevant operations are bundled up in this structure, and to maximise clarity in the exposition we give names to these operations here:

=SML
declare_infix (300, "+⋎v");
declare_infix (300, "-⋎v");
declare_infix (310, "*⋎sv");
=TEX
ⓈHOLCONST
│ ⦏$+⋎v⦎ ⦏$-⋎v⦎ : ℝ⋏3 → ℝ⋏3 → ℝ⋏3;
│ ⦏~⋎v⦎ : ℝ⋏3 → ℝ⋏3;
│ ⦏$*⋎sv⦎ : ℝ → ℝ⋏3 → ℝ⋏3;
│ ⦏0⋎v⦎ : ℝ⋏3;
│ ⦏d⋎v⦎ : ℝ⋏3 → ℝ
├──────
│ ∀ x y r⦁
│  	x +⋎v y = Plus⋎N x y ℝ⋏3⋎NVS
│ ∧	~⋎v x = Minus⋎N x ℝ⋏3⋎NVS
│ ∧	x -⋎v y = Subtract⋎N x y ℝ⋏3⋎NVS
│ ∧	r *⋎sv x = Scale⋎N r x ℝ⋏3⋎NVS
│ ∧	0⋎v =  0⋎N ℝ⋏3⋎NVS
│ ∧	d⋎v x = Norm⋎N x ℝ⋏3⋎NVS
■
=SML
declare_type_abbrev ("V", [], ⓣℝ⋏3⌝); 
=TEX

\section{Universes}\label{Universes}

Two different notions of what a {\it Universe} is are provided, and ultimately the formulation of the theory will use both of them.

These two different models of the universe are convenient for discussing distinct features of interest, and before proceding to the formal definitions I will give an informal description of the models together with an indication of the factors which motivate consideration of these models.

One feature which these two models share is that the universe is particulate.
Matter is concentrated in finite lumps at certain points, rather than continuously distributed with a finite but varying density over certain areas of space.
This aspect of the models is chosen primarily for simplicity, since many of the methodological and philosophical points which concern me can be more readily illustrated without the additional complexity which arises from consideration of the possibility of continuously distributed matter.

The two models are constructed in the following ways:
\begin {enumerate}
\item The universe is considered as a temporal continuum of instantaneous states.

The motivation for this model is the ideal that the laws of physics should enable us, given the state of the universe at some time {\it t}, to predict the state at any subsequent time {\it t'}.
Contemporary fundamental physics typically denies this principle, which amounts to the claim that the universe is deterministic.
The denial however, sustains interest in the concept of determinism, and this kind of model is suitable for consideration of this matter, and more generally in the question of what information is necessary and sufficient to fully determine the state of the universe at some instant in time.
In this matter it may prove that the identity of the physical entities which constitute the universe is not among the information which is needed to construct a viable physical theory, and this information is absent from the first of our models.
In this respect the model may be thought of as Humean.

\item The universe is considered as a set of concrete entities, each having its own history.

The first kind of model provides a doubtful basis for an answer to the question of what are (or what may be) the constituents of the universe, and worse, is awkward for the formulation of physical laws which tell us about the behaviour of individuals over time.
If one knows simply which points of space are occupied at each moment in time, and the mass of the particle which occupies that point in space-time, then a law which talks about movement or acceleration of particles is not straightforward to interpret.

This second notion of universe therefore contains more information than is present in the first, and some of the information is temporally extended.
The extra information is essentially about identity, it is about which collections of instants of particles all belong to the same particle.

\end{enumerate}

\subsection{Version 1}

In this version the {\it state} of a universe at some time is defined, and a {\it universe} is then defined as a map from time to the state at that time.

\subsubsection{State}

The universe consists of a set of material particles in a three dimensional Euclidean space, each particle having at any time three spatial coordinates, a mass and three velocity components.
Particles have no size, and no two particles may have the same coordinates.
The state of the universe at some specific time may therefore be thought of as a partial function from coordinates to the mass and velocity attributes.
This we model using a total function over the coordinate space, the absence of a particle at that point being modeled by the function yielding zero mass and zero velocity.
The requirement that this relation be a partial function is expressed by the property {\it State}.

=SML
declare_type_abbrev ("STATE⋎1", [], ⓣV → ℝ × V⌝); 
=TEX

Mass must be positive, and to ensure that no superfluous information is present, we require that whenever the mass is zero, so is the velocity.
These requirements are expressed by the following property:

ⓈHOLCONST
│ ⦏State⋎1⦎ : STATE⋎1 → BOOL
├──────
│ ∀ s ⦁ State⋎1 s ⇔
│	∀v⦁	let (mass, vel) = s v
│		in mass ≥ 0⋎R
│		∧ (mass = 0⋎R ⇒ vel = 0⋎v)
■

\subsubsection{Histories}

A universe may then be modelled by its history.
We take time to be a continuum, bounded neither above nor below.
A universe is then a function from the reals to instantaneous states.

I will introduce an abbreviation ($UV⋎1$) for the type of a universe:
=SML
declare_type_abbrev ("UV⋎1", [], ⓣℝ → STATE⋎1⌝); 
=TEX
A universe ($Uv⋎1$) is an object of that type which always yields a bona-fide $State⋎1$.

ⓈHOLCONST
│ ⦏Uv⋎1⦎ : UV⋎1 → BOOL
├──────
│ ∀ uv⦁ Uv⋎1 uv ⇔ ∀t⦁ State⋎1 (uv t)
■

\subsection{Version 2}\label{Version2}

We now define a model of the universe in which the constituents of the universe are a set of particle trajectories.
In this case the universe is not defined as a history of instantaneous states, but as a collection of particles.

=SML
declare_type_abbrev ("PARTICLE", [], ⓣℝ × (ℝ → V)⌝); 
declare_type_abbrev ("UV⋎2", [], ⓣPARTICLE LIST⌝);
=TEX

Each element of the list represents the history of a single particle.
It consists of an ordered pair of which the first element is the mass of the particle, and the second is a function giving the coordinates of the particle at each point in time.

In this notion of universe it is not implicit, as it is in the earlier one, that no two particles can occupy the same point in space at the same time.
However, it is implicit that particles in a limited sense persist over time, and also that the number of particles is finite, and that the total mass of the particles in the universe is finite and does not vary.
There is still no constraint on continuity of motion.

\subsection{Consistency and Well Formedness of Universes}

ⓈHOLCONST
│ ⦏Conformant⦎: UV⋎1 → UV⋎2 → BOOL
├──────
│ ∀ uv1 uv2⦁ Conformant uv1 uv2 ⇔
│ ∀t v m p⦁ uv1 t p = (m, v) ⇔
│	∃tr vh⦁ (m, tr) ∈⋎L uv2
│	∧ tr t = p
│	∧ VDeriv ℝ⋏3⋎NVS tr = vh
│	∧ vh t = v
■

\subsection{Laws}

A physical property or law ({\it Pp}) is a non-trivial property of universes.
The definition is parameterised by a property which may be thought of as the property of being a ``possible universe'', exemplified by {\it Uv} as defined above, or by the property $λw:UV⋎2⦁T$.

ⓈHOLCONST
│ ⦏Pp⦎ : ('u → BOOL) → ('u → BOOL) → BOOL
├──────
│ ∀tuv puv ⦁ Pp tuv puv ⇔
│	  (∀uv ⦁ puv uv ⇒ tuv uv)
│	∧ (∃uv ⦁ puv uv)
│	∧ (∃uv ⦁ tuv uv ∧ ¬ puv uv) 
■

\section{The Laws of Physics}\label{TheLawsofPhysics}

I now attempt to formalise versions of Newtons laws.

Again two versions are offered, the first a fairly direct formalization of Newtons laws of motion and gravitation, incorporating the assumption (not Newton's) that there are not forces but gravitational forces.
After noting the difficulties which arise from having no forces other than those due to gravity, a second force is introduced to show how the difficulty can be overcome.

\subsection{Newtonian}

Newtons laws of motion and of gravitation state:
\begin{itemize}
\item That the acceleration of a particle is proportional to the force applied to the particle.
\item That there is a force of gravitational attraction between two particles whose magnitude is proportional to the product of their masses and inversely proportional to the square of the distance between them.
\end{itemize}

This first formalised model of the universe assumes further that the only forces are gravitational.

First we define the force of gravitational attraction between two particles.

A gravitational constant is introduced, but for our present purposes need not be given a value.

ⓈHOLCONST
│ ⦏Gc⦎ : ℝ
├──────
│ T
■

We also have a short range repulsive force, which comes into operation when two particles ``collide''.
As the distance gets smaller the repulsive force becomes stronger than gravitational attraction and ultimately prevents two particles from ever meeting.

The gravitational attraction between two particles is defined.
This is done via the field strength.
First we define the gravitational field at one point induced by a mass at some other point.

ⓈHOLCONST
│ ⦏Flds⦎ : ℝ × V → V
├──────
│ ∀ mass pos⦁
│	Flds (mass, pos) =
│	  if pos = 0⋎v
│	     then 0⋎v
│	     else
│		let d = d⋎v pos
│		in let mag = (Gc *⋎R mass) / (d ^⋎N 2)
│		    in ((mag / d) *⋎sv pos)
■

To get the total strength of the gravitational field at some point the components of the field due to each particle must be added together.

ⓈHOLCONST
│ ⦏Fldstot⦎ : PARTICLE LIST → ℝ → V → V
├──────
│ ∀ p lp t pos⦁
│	Fldstot [] t pos = 0⋎v
│ ∧	Fldstot (Cons p lp) t pos = (Flds (Fst p, (Snd p t) -⋎v pos))
│		+⋎v (Fldstot lp t pos)
■

We then obtain the history of the acceleration of a particle (as predicted by Newton's laws):

ⓈHOLCONST
│ ⦏GAccHist⦎ : PARTICLE LIST → PARTICLE → (ℝ → V)
├──────
│ ∀ ma: ℝ; ta: ℝ → V; pl t⦁
│	GAccHist pl (ma, ta) t = Fldstot pl t (ta t)
■

We need to total up the forces on each particle to express the required laws.
For a single particle this is done as follows.
The function takes a particle and a list of particles, the list supplied is the entire Universe.
It is not necessary to remove the particle from the universe before performing this summation, because the gravitational force has been defined to be zero between two coincident particles.

We want to require that the acceleration of the particles is determined by the force applied the particle following Newton's law:
\begin{itemize}
\item F = ma
\end{itemize}

That function is then mapped over all the particles in the state to yield a list of acceleration histories.

ⓈHOLCONST
│ ⦏GAccHistl⦎ : PARTICLE LIST → (ℝ → V) LIST
├──────
│ ∀ lp⦁ GAccHistl lp = Map (GAccHist lp) lp
■

We have thus determined what the acceleration of the particles should be according to Newton's laws of motion and gravitation.
In order to assert that they are what they should be, we need to be able to extract from the trajectories in the particles the acceleration of the particles.
This requires twice differentiating the position histories.
The possibility arises that the particle trajectories are not twice differentiable, and it is important that we assert differentiability rather than assume it.
To make this possible, instead of attempting to define a function on PARTICLEs which yields the acceleration history, we define a relation between functions and acceleration histories which is true if the acceleration history is the second differential of the trajectory.

The relation $VDeriv$ (defined elsewhere) gives the relation between a function (from the reals to some normed vector space) and its nth derivative.
Applying $VDeriv 2$ to the trajectories of the particles will give us their accelerations.

ⓈHOLCONST
│ ⦏AccHist⦎ : PARTICLE → (ℝ → V) → BOOL
├──────
│ ∀ p ah⦁  AccHist p ah = (VNthDeriv 2 ℝ⋏3⋎NVS (Snd p) = ah)
■

ⓈHOLCONST
│ ⦏AccHistpl⦎ : (PARTICLE × (ℝ → V))LIST → BOOL
├──────
│∀ pah pahl⦁  (AccHistpl []  ⇔ T)
│ ∧ (AccHistpl (Cons pah pahl)
│		 ⇔ AccHist (Fst pah) (Snd pah) ∧ (AccHistpl pahl))
■

ⓈHOLCONST
│ ⦏AccHistl⦎ : PARTICLE LIST → (ℝ → V) LIST → BOOL
├──────
│∀ pl al⦁ AccHistl pl al ⇔ AccHistpl (Combine pl al)
■

Now we express the property of $UV⋎2$ which states that it complies with Newton's laws.

ⓈHOLCONST
│ ⦏Newtonian⋎2⦎ : UV⋎2 → BOOL
├──────
│ ∀ uv2⦁ Newtonian⋎2 uv2 ⇔ AccHistl uv2 (GAccHistl uv2)
■

To express a similar property in relation to $UV⋎1$ we use the conformance relation between  $UV⋎1$ and $UV⋎1$.
The effect of this conformance relation is to require that there is some way of collecting together the occupied points in the instantaneous states to yeild particle trajectories which are continuous and twice differentiable, and which comply with Newton's laws.

ⓈHOLCONST
│ ⦏Newtonian⋎1⦎ : UV⋎1 → BOOL
├──────
│ ∀ uv1⦁ Newtonian⋎1 uv1 ⇔ 
│	∃ uv2⦁ Conformant uv1 uv2 ∧ Newtonian⋎2 uv2
■

=SML
new_conjecture (["Pp_Newtonian"], ⌜Pp (λw⦁T) Newtonian⌝);
=TEX
=IGN
set_goal ([], ⌜Pp (λw⦁T) Newtonian⌝);
a (rewrite_tac (map get_spec [
	⌜Newtonian⌝,
	⌜Pp⌝])
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜[]:UV⋎2⌝
 THEN rewrite_tac (map get_spec [
	⌜Acchistl⌝,
	⌜Newtonian⌝,
	⌜Pp⌝,
	⌜$U2AccHist⌝,
	⌜Fold⌝,
	⌜Combine⌝,
	⌜Map⌝
]));
(* *** Goal "2" *** *)
a (∃_tac ⌜[(1⋎R, λx⦁(1⋎R, 1⋎R, 1⋎R)); (1⋎R, λx⦁(0⋎R, 0⋎R, 0⋎R))]:UV⋎2⌝
 THEN rewrite_tac (map get_spec [
	⌜Acchistl⌝,
	⌜$U2AccHist⌝,
	⌜Fold⌝,
	⌜Combine⌝,
	⌜Map⌝])
 THEN REPEAT strip_tac);
a (rewrite_tac (map get_spec [
	⌜$PartAccHist⌝])
	THEN REPEAT strip_tac);
a (rewrite_tac (map get_spec [
	⌜$Map2Deriv⌝]));
a (REPEAT_N 4 strip_tac);
a (rewrite_tac (map get_spec [
	⌜$MapDeriv⌝,
	⌜$Deriv⌝,
	⌜Leftproj⌝,
	⌜Acchist⌝,
	⌜Ftothist⌝,
	⌜Fhist⌝,
	⌜Gfv⌝
]));
a (rewrite_tac[let_def]);
a (rewrite_tac[get_spec ⌜$+⋎tr⌝]);
if_thm;

a (rewrite_tac[list_∀_elim [⌜1⋎R⌝, ⌜1⋎R⌝, ⌜1⋎R⌝, ⌜1⋎R⌝, ⌜1⋎R⌝, ⌜1⋎R⌝] (get_spec ⌜$+⋎tr⌝)]);

get_spec ⌜let_def⌝;
rewrite_
a (rewrite_tac (map get_spec [
	⌜Acchistl⌝,
	⌜Newtonian⌝,
	⌜Pp⌝,
	⌜$U2AccHist⌝,
	⌜Fold⌝,
	⌜Combine⌝,
	⌜Map⌝,
	⌜$PartAccHist⌝,
	⌜Acchist⌝,
	⌜$MapDeriv⌝,
	⌜$Deriv⌝,
	⌜Leftproj⌝
]));

a (rewrite_tac (map get_spec [
	⌜$PartAccHist⌝,
	⌜Acchist⌝,
	⌜$Map2Deriv⌝,
	⌜$MapDeriv⌝,
	⌜$Deriv⌝,
	⌜Leftproj⌝
])
	THEN REPEAT strip_tac);
a (rewrite_tac (map get_spec [
	⌜$Map2Deriv⌝,
	⌜$MapDeriv⌝,
	⌜$Deriv⌝,
	⌜Leftproj⌝])
	THEN strip_tac);
a (∃_tac ⌜0⋎R⌝);
a strip_tac;
a (∃_tac ⌜1⋎R⌝);
a strip_tac;
a (rewrite_tac[get_spec ⌜ℕℝ⌝]);
a (once_rewrite_tac[get_spec ⌜1⋎R⌝]);
a (rewrite_tac[]);
a (REPEAT strip_tac);
a (swap_nth_asm_concl_tac 1);
a (REPEAT strip_tac);

a strip_tac;
a strip_tac;
get_spec ⌜ℕℝ⌝;
	THEN rewrite_tac[]);

 THEN REPEAT strip_tac);
a (rewrite_tac (map get_spec [
	⌜$MapDeriv⌝])
 THEN REPEAT strip_tac);
a (rewrite_tac (map get_spec [
	⌜$Deriv⌝])
 THEN REPEAT strip_tac);
a (rewrite_tac (map get_spec [
	⌜Leftproj⌝])
 THEN REPEAT strip_tac);
a (rewrite_tac[list_∀_elim [⌜λ x:ℝ⦁ (1⋎R, 1⋎R, 1⋎R)⌝, ⌜λ x:ℝ⦁ (1⋎R, 1⋎R, 1⋎R)⌝](get_spec ⌜Leftproj⌝)
]);
set_flag ("pp_show_HOL_types", false);
get_flags();
a strip_tac;
=TEX

\subsection{Collision Avoidance}

A more realistic model may be produced by including a force of repulsion which occurs at short differences, and from a macroscopic perspective results in particles bouncing off each other if they come close to collision.

A constant is required for this repulsive force.

ⓈHOLCONST
│ ⦏Rc⦎ : ℝ
├──────
│ T
■


The magnitude of the repulsive force is:


{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{t002a.th}
}  %\let

\twocolumn[\section{Index}\label{index}]
{\small\printindex}

\end{document}

=SML
output_theory{out_file="t002a.th.doc", theory="t002a"};
=IGN
