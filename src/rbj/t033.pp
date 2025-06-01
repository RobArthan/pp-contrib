=IGN
$Id: t033.doc,v 1.3 2011/02/12 09:14:19 rbj Exp $
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\usepackage{A4}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}

\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{The Proposition}
\makeindex
\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

\author{Roger Bishop Jones}
\date{\ }

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
A place to play formally with the concept of proposition.
This actually started as a formal look at some of Harvey Friedman's ideas, particularly his concept calculus but also BRT theory, and I think somehow I got the idea that the relevance of this to me was something to do with propositions.
Anyway, it hasn't really got anywhere.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2009/11/22

Last Change $ $Date: 2011/02/12 09:14:19 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t033.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t033.pdf}

$ $Id: t033.doc,v 1.3 2011/02/12 09:14:19 rbj Exp $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize

\end{centering}

\thispagestyle{empty}
\end{titlepage}
\newpage
\addtocounter{page}{1}
%\section{DOCUMENT CONTROL}
%\subsection{Contents list}
{\parskip=0pt\tableofcontents}
%\newpage
%\subsection{Document cross references}

%{\raggedright
%\bibliographystyle{fmu}
%\bibliography{rbj,fmu}
%} %\raggedright

\newpage
\section{INTRODUCTION}

This document started as an exploration of Friedman's Concept Calculus.
What I was really intending was a critique which would serve as a vehicle for my own ideas.

Then I decided that probably would not get very far and decided to set it in a context which reflected the relevance of the idea of a concept calculus in my ideas.

\subsection{Some Ideas About Propositions}

For some time I have had a pluralistic conception of the proposition.
A proposition has been, in my scheme of things, the meaning of a sentence in some language.

My knowledge of the history of the idea of proposition is almost nil, (I must look into this!).
So in terms of known historical context there is not very much, and it is really just the very recent history of formal semantics which provides the context and origins of this conception of the proposition.

As to semantics, I begin with the idea of truth functional semantics, since I am preocupied with formalisation (and mechanisation), and a truth functional semantics is what you need to make the notion of sound derivation definite.
The most simplistic notion of proposition which comes out of this is just the extensional truth conditions, the set of models of the sentence.
This isn't very satisfactory, and the most obvious way it fails is in identifying the meaning of all logical truths (which in this conception includes all of mathematics).
But you have to have a reason for a richer notion of proposition, and I didn't have one until quite recently (or I didn't recognise the proposition as an answer to the problems which I cared about).


\newpage

\section{FRIEDMAN}

\subsection{Boolean Relation Theory}

I'm just going to set out from the beginning of \cite{friedmanharvey2007a} formalising in HOL.
I shalln't be literal about it though.
I don't expect to get through Chapter 1.

First we have a new theory.

=SML
open_theory "misc2";
force_new_theory "BRT";
set_merge_pcs ["misc21", "'savedthm_cs_∃_proof"];
=TEX

\subsection{BRT Syntax}

Not sure whether it will be necessary to formalise the syntax so I will leave it until I need it.

\subsection{Semantics}

The treatment of multivariate functions seems cumbersome to me, so I will make some changes which I hope will simplify the formalisation.
First note that Harvey says that the n-tuples and m-tuples must be distinct for distinct n and m, so forming tuples by iteration of the ordered pair construction won't do.
He doesn't actually say how to do it.

I will model a tuple by a function whose domain is an ordinal.
The length of the tuple is then recoverable and I do not need to use an ordered pair for the multivariate functions.
However, to avoid the ordered pair I will have to treat a multivariate function over 1-tuples as a function whose domain is ordered pairs of which the first element is zero (i.e. functions whose domain is the ordinal 1).
It remains to be seen whether that causes problems.

A multivariate function is therefore defined as any function over tuples of a consistent arity.

ⓈHOLCONST
│ MF: GS SET
├──────
│ MF = {f:GS | ∀x y⦁ x ∈⋎g f ∧ y ∈⋎g f ⇒ dom x = dom y ∧ ordinal (dom x)}
■

The arity of a multivariate function is obtained as follows:

ⓈHOLCONST
│ arity: GS → GS
├──────
│ ∀ mf⦁ arity mf = dom (⋃⋎g (dom mf))
■

Friedman has a syntax for the image of a multivariate function over the relevant power of some set.
In fact he just overloaded function application, which we can't do.
I will use the symbol $⌜∘⌝$ and perhaps arrange for it to be printed as a blank.

=SML
declare_infix (300, "∘");
=TEX

The required result is obtained by taking the range of the restriction of f to the relevant exponential of A.

ⓈHOLCONST
│ $⦏∘⦎: GS → GS → GS
├──────
│ ∀ f A⦁ f ∘ A = ran (((arity f) →⋎g A) ◁ f)
■

A lot of the notation Harvey is talking about is not far removed from what we get for free.

=SML
declare_infix (300, "∈⋎g⋎L");
declare_infix (300, "⊆∈⋎g");
=TEX

ⓈHOLCONST
│ $⦏∈⋎g⋎L⦎: GS LIST → GS → BOOL
├──────
│ ∀le s⦁ le ∈⋎g⋎L s ⇔ ∀⋎L (Map (λe⦁ e ∈⋎g s) le)
■

=SML
declare_alias ("∈⋎L", ⌜$∈⋎g⋎L⌝);
=TEX

ⓈHOLCONST
│ ⦏list_⊆⋎g⦎: GS LIST → BOOL
├──────
│	(list_⊆⋎g [] ⇔ T)
│ ∧ (∀h t⦁ list_⊆⋎g (Cons h t) ⇔ (if t = [] then T else h ⊆⋎g Head t)
│					∧ list_⊆⋎g t)
■

=SML
declare_alias ("list_⊆", ⌜list_⊆⋎g⌝);
=TEX

ⓈHOLCONST
│ $⦏⊆∈⋎g⦎: GS LIST → GS → BOOL
├──────
│ ∀ls s⦁ ls ⊆∈⋎g s ⇔ list_⊆ ls ∧ ls ∈⋎L s
■

=SML
declare_alias ("⊆∈", ⌜$⊆∈⋎g⌝);
=TEX

\subsection{Concept Calculus}

See \cite{friedmanharvey2009b}.

=SML
open_theory "misc2";
force_new_theory "CC";
set_merge_pcs ["hol1", "'savedthm_cs_∃_proof"];
=TEX

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\appendix

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{BRT.th}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{CC.th}
}  %\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
