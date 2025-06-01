=IGN
$Id: t000.doc,v 1.15 2011/04/25 19:51:22 rbj Exp $
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\usepackage{A4}
\def\N{\mathbb{N}}
\def\D{\mathbb{D}}
\def\B{\mathbb{B}}
\def\R{\mathbb{R}}
\def\Z{\mathbb{Z}}
\def\Q{\mathbb{Q}}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}
\newcommand{\ignore}[1]{}

\tabstop=0.4in

\makeindex
\title{Introduction to Work in Progress}
\author{Roger Bishop Jones}
\date{\ }

\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=red, citecolor=blue, filecolor=black, linkcolor=blue}

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
A description of the problems I am working on and an index to the documents in which that work is progressing.
\end{abstract}
\vfill
\begin{centering}
{\footnotesize

Created 2004/10/03

Last Change $ $Date: 2011/04/25 19:51:22 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t000.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t000.pdf}

$ $Id: t000.doc,v 1.15 2011/04/25 19:51:22 rbj Exp $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnote
\end{centering}
\thispagestyle{empty}
\end{titlepage}
\newpage
\addtocounter{page}{1}
%\section{DOCUMENT CONTROL}
%\subsection{Contents list}
{\parskip=0pt\tableofcontents}
%\newpage

\newpage
\section{Introduction}

The documents described here form a collection bound primarily by the technologies which have been used to produce them, and consist of documents which include formal material in Higher Order Logic processed by {\Product} and which are prepared using \LaTeX and delivered in PDF. 
They are all incomplete, and show me in sceptical mode (i.e. seeking knowledge, with uncertain results).
Gradually however, these attempts have become more substantial, and ongoing work is now conceived of as falling in one substantial project in formal philosophy.

As well as an informal overview, this document contains abstracts from each document.
%, document references
%, a complete set of theory listings and a consolidated index, so that for each formal name defined the document in which it is defined can readily be located.
%There is a flaw in this at present, since you only discover the theory and its not obvious how to get from the theory name to the document reference.

For the record, some information about the various earlier materials is retained.

\subsection{Central Themes}

The work is conceived of as a continuation of the ideas and programmes most particularly of Leibniz and Carnap.
The Leibniz connection is most conspicuous in the use of mechanical support for reasoning in formal notations, in the ideals of a universal characteristic and a calculus ratiocinator.

Apart from those important connections the work is more aligned to positivism and Rudolf Carnap than to rationalism and Leibniz.

\subsection{Active Threads}

My thinking now runs primarily along two lines.

The first is methodological, and the second foundational.

\paragraph{Methodological}

I am beginning to find ways of applying mechanised formal methods to problems in philosophy, even to philosophical exegesis.
In this it is apparent that `shallow embedding' is a key technique.
This trend is exemplified in \cite{rbjt028,rbjt037,rbj045,rbj046}.

I would like to give a good account of the methods used in these documents, together with any issues which arise in giving the philosophical underpinnings for the methods.

\paragraph{Foundational}

There is a foundational thread, which though not wholly disconnected from the methodological one, has its own independent motivation.
This has two heads.
The most active of these is the search for suitable non-well-founded foundation for use in mechanised applications of formal methods.
The point at which this is moving forward is in the work directed towards an illative lambda-calculus in \cite{rbjt041}.

A subsidiary one, recognising that consistency strength is better derived from well-founded foundations, is concerned with the semantics of well-founded set theory.
My ideas in this area have not been formally treated and are not well documented.

\ignore{

My present `focus' is on work intended eventually to form a book whose current title is ``Analyses of Analysis'' \cite{rbjb001, rbjb003, rbjb002}.
This will appear here as a series of documents corresponding to the chapters of the intended book.
What these are is not settled.
The enterprise as a whole is intended as a widely scoped systematic and substantially formal philosophical system.
There is expected to be a substantial part which consists of formal historical exegesis, intended both to exemplify methods and to trace their origins.
However, the point of it all is the more forward looking material which at this point largely defies description (not least because of my own tenuous grasp on the materials in which I am most interested).
This latter material has been lately spoken of by me as ``X-Logic'' but I have expanded my conception of X-Logic so greatly that it can not longer plausibly be described as a logic. 
I have reverted to thinking of this as a philosophical system.

The exegetical aspects I have at present in mind are:

\begin{itemize}
\item Plato and Aristotle \cite{rbjt028}
\item Leibniz
\item Hume and Kant
\item Frege
\item Russell and Wittgenstein's Tractatus \cite{rbjt030}
\item Carnap
\item Grice
\end{itemize}

However, what to do from Frege onwards is pretty much an open book.

Grice appears in consequence of the influence of Speranza.
The connection (what connection you ask?) between Grice and Carnap is explored by Speranza and I in collaborative attempt to synthesise \emph{A Conversation Between Carnap and Grice}\cite{rbjp008}.

There is a purpose which will gradually refine this conception of the coverage.
This formal book is to provide substance behind a plain prose articulation of a philosophy of ``metaphysical positivism'', it will exemplify methods articulated in that book \cite{rbjt029}, and will provide technical backing for some of the claims informally presented in that book.

}%ignore



\subsection{Earlier Work}

Some of the problems are themselves inherently unformalisable, and so the application of formal methods is expected to yield only incomplete models.
The underlying methodological thesis is that even problems which cannot be formally modelled may be illuminated by the study of formalisable near neighbours.
This is one way of looking at some of the work which takes place in set theory at present, though set theorists may not look at their work in that way.
No originality is claimed for this approach to philosophy.

The philosophical objectives may further be described as:
\begin{enumerate}
\item Something rather vague about semantics, one element of which is a certain kind of analysis of the concept of analyticity.
\item Concrete ontology.
\item Abstract ontology.
\item X-Logic.
\end{enumerate}

\paragraph{Semantics}

On the concept of analyticity the study of which is represented here only by the empty shell of one document \cite{rbjt001}, I shall say no more at present.

The main thrust of my interest in semantics is in the foundations of abstract semantics.
For me this is the semantics of set theory, and my approach to this topic is through the study of membership structures \cite{rbjt004}, also scarcely begun.

The work I have done in historical exegesis is looking like analysis by shallow embedding (a kind of semantic technique) and in my cogitations about how to provide some description of the languages, methods and tools for a philosophical audience it has come to seem a good idea to present HOL in some detail particularly emphasising its merits for the purposes of doing things like shallow embeddings.
This has given me motivation for a document \cite{rbjt038} not yet off the starting blocks in which an exposition of HOL starting from Church's 1940 paper \cite{church40} is combined with an exposition of how good it is for doing a certain kind of semantics.

The notion of proposition is becoming more important to me, perhaps even central to the theoretical philosophy, and the proposition is a semantic entity, but this I think will be mainly discussed under the heading `X-Logic'.

\paragraph{Concrete Ontology}

Concrete ontology is concerned with what can be known about what concrete entities there are in the Universe.
My interest in this began when I attempted to produce an example of how to formalise a scientific theory, and I began to be interested in the metaphysical problems which arise in the course of attempting to formalise fundamental laws of physics.
My results of my failed attempts to formalise Newtonian physics are to be found in \cite{rbjt002}.
I started this intent to minimise my involvement in the underlying mathematics, but was provoked into attempting a more serious approach to the mathematics by Rob Arthan, who started for me the work on differential geometry which can now be found in \cite{rbjt003}.

My present feeling is that this is an interesting area but one in which I may not be able to make enough progress to be worthwhile.
If time were no obstacle my inclination now would be to approach the problem via the theory of general relativity, in particular via formalisation of aspects of \cite{hawking73}, supported by a development of differential geometry following reasonably closely chapter 2 of that book.

\paragraph{Abstract Ontology}

The question what can be known about what abstract objects do or may exist was to be addressed primarily through the formal study of membership structures \cite{rbjt004}, and at present seems the domain most likely to receive my serious attention.
However, this area too is hardly begun, and scarcely progressing, because of various matters which seem to me to require attention before this work can have much hope of success.
Various other work on set theory is now present, some of it making some use of the material on membership structure (but not much).

There are now quite a few documents on non-well founded set theory, which form a chronological sequence of work which I began in the autumn 2006 and continued (with some interruptions) through to the autumn of 2008.
This began with some exploratory work on the formalisation of NF and NFU in HOL in \cite{rbjt019}, an educational exercise.
This lead me to experiment with non-well-founded ontologies more generally and directly without using NF.
There is a document on this here, \cite{rbjt021} but it doesn't get anywhere because I switched to Isabelle and the fullest formal treatment of that topic is therefore elsewhere \cite{jones06a} with an informal discussion here \cite{rbjp011}.
I gave two talks on Poly-sets at the Centre for Mathematical Sciences in Cambridge in 2007, the first at one of Thomas Forster's set theory seminars and the second at the NF anniversary workshop shortly after (not quite the same talk) overheads \cite{rbjo003} and notes \cite{rbjn003} are on-line.
These talks present the Poly-sets and also speculate about the approach which I was had in mind to follow and which I did indeed spend about a year (elapsed) on from autumn 2007 to autumn 2008.

This more radical approach to non-well-founded set theory may be found in the documents \cite{rbjt021,rbjt024,rbjt026,rbjt027}.
This now represent my most substantial piece of research in the foundations of mathematics, but has been suspended pro-tem.
The four documents represent a series of four steps in evolving the ideas, primarily simplifications intended to make reasoning about them tractable.
For the technical content you can ignore the first three and go straight to the last, all four are I believe logically independent.
However, there are probably better informal accounts of what I am trying to do in the earlier document(s), I must move some of them across to the later document.

The culmination was actually an impasse (unsolved problem) on a sufficient condition for extensionality in the interpretations of set theory which are obtained by the method.
I had an intuitively plausible criterion and a plan for the proof, I spent considerable time developing the proof, and ended up with a gap which I could not close.
I have no definite opinion about whether the conjecture I sought to prove is true, I have been unable to settle the matter either way (though I am still inclined to think it true, I have neither found how to fill in the gap in the proof, nor found a counterargument).

I also have a document on category theory \cite{rbjt017}  which may as well be mentioned here, though its motivation is not philosophical, except insofar as it connects (which at present it does not) with my lucubrations on categorical foundation systems.
There is now a properly foundational exercise in formal category theory in \cite{rbjt018}, based on the work on NFU in \cite{rbjt019}.
Its not much good, not only does it not get very far, but I believe I was trying to work out if co-induction would help.
I don't think it does, but I never actually properly understood it.
In fact the only bit of category theory related foundational work of mine which is worth looking at, if only for its entertainment value) is elsewhere written in XML (\href{http://rbjones.com/rbjpub/pp/gst/ctf.html}{Category Theoretic Foundation Systems}).
I have also started some work on Universal Algebra which was done to support the development of Lattice theory for a new version of X-Logic, and am beginning to try Category theory as based on this theory (though it is not strictly an algebra in the intended sense).
This version of category theory is intended to be used in exploring Goguen's work on institutions and further developments along those lines for X-Logic.
Most of the algebraic and categorical material is abstract but is not ontological (in the sense I intended for this paragraph).

There is also a foray into Conrad's surreal ontology in ``Surreal Geometric Analysis'' \cite{rbjt022}.
This was started when for a short time I thought it might be worth using surreal numbers for the formalisation of the theory of relativity because I thought it might make the handling of singularities nicer.
Since I didn't get very far, the interest such as it is in the material present is that there is an attempt at an axiomatisation of the surreal numbers independently of set theory.
The idea was to construct this in set theory, but the end result would be to make a set-free axiomatisation of surreals into a proper axiomatic foundation for mathematics (at least technically).

\paragraph{X-Logic}

This is represented at present by one document of formal models \cite{rbjt016}.

\subsection{Supporting Theories and Tools}

In all this formal work material progress depends upon developments in various enabling technologies not themselves of direct philosophical interest.
Like everything else in sight this work is all experimental and incomplete.
In these matters, if a problem can be avoided it should be, so one way of improving my treatment of a problem here is to find a way to approach the target applications which does not depend upon the proposed technology.
The most obvious candidate here is some of all of the material on inductive definitions.

The supporting theories and tools are, for concrete ontology:

\begin{enumerate}
\item differential geometry \cite{rbjt003}
[this material is obsolescent, being displaced by an approach based on geometric algebra, under development by Rob Arthan]
\end{enumerate}

And for abstract ontology:
\begin{enumerate}
\item inductive and co-inductive definitions \cite{rbjt007,rbjt008}
\item well-founded relations \cite{rbjt009}
\item set theory \cite{rbjt023}
\end{enumerate}

And more generally:
\begin{itemize}
\item Miscellaneous theory supplements and tactics \cite{rbjt006,rbjt010}
\item Inference by chaining and supporting materials \cite{rbjt010,rbjt011,rbjt012}
\item Another collection of Miscellanea which depend upon set theory \cite{rbjt025}
\end{itemize}

\subsection{ProofPower}

The documents in this series all make use of \Product.
This determines the language in which formal content is expressed (which is {\Product-HOL}).

The there are several (incomplete) documents about {\Product} \cite{rbjt013,rbjt014,rbjt015}, all produced in the course of co-authoring with Rob Arthan an article for the BCS-FACS newsletter.
I also have something in mind on HOL and its use in semantics for which a document has been created, but I have not yet come to a definite idea about how this should be done \cite{rbjt038}.

\include{t000abs}

\label{Bibliography}
\addcontentsline{toc}{section}{Bibliography}

{\def\section*#1{}
\raggedright
\bibliographystyle{rbjfmu}
\bibliography{rbj,fmu}
} %\raggedright

\appendix

%\section{Theory Listings}

%{
%\let\Section\subsection
%\def\subsection#1{}
%\def\section#1{\Section{#1}}
%\include{doc_theories}

%}  %\let


{\twocolumn[\section*{Index}\label{Index}]
\addcontentsline{toc}{section}{Index}
{\small\printindex}}

\end{document}
