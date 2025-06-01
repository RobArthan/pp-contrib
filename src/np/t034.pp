=IGN
$Id: t034.doc,v 1.1 2009/12/16 21:55:38 rbj Exp $
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

\title{A Self-Defining Semantics for First Order Set Theory}
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
Discussion of ``a semantics'' for first order set theory which is definable in the set theory construed by this semantics.
Most of the literature in this area is related to the Liar paradox, which is of interest here only insofar as it has been supposed that the Liar paradox renders impossible this kind of construction (though the situation is now known to be rather complex).
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2009/11/19

Last Change $ $Date: 2023/01/23 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t034.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t034.pdf}

$ $Id: t034.doc,v $ $

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

What I aim to discuss in this document is an approach to defining a semantics for the language of first order set theory from within that theory as construed by that semantics.
By ``a semantics'' I mean here simply a truth predicate, which, since we are in set theory, and the collection in question is countable, this is just a set.

The set we will define will be the set of true sentences in first order set theory.
The false sentences will be those whose negation is true.
It is not to be expected that if a sentence is not in this collection then its negation will be, some sentences will be left in limbo, with effectively no truth value.

The set theory for which we supply a semantics is a well-founded set theory, and by the methods used here could have been rendered as a theory like ZFC with large cardinal axioms.
However, global properties of the universe of discourse are not important to us here, and matters are simpler if we settle for less in that department.

In what ways does this semantics differ from the {\it normal} semantics for first order set theory?
The answer to this is, not at all in any aspect which is normally addressed, but that this does not usually include a definite truth valuation at the sentence level, which is all that is novel in this approach.
 
Semantics is not greatly discussed by mathematical logicians (among whom set theorists are usually counted).
Model theory is, and this provides the purely logical part of the semantics of `first order languages'.
This gives the truth conditions for the formulae of first order set theory and hence for sentences (closed formulae), relative to some given `interpretation' of the language (viz. membership structure).
However, it is not usual to nominate any particular interpretation, and so the semantics of set theory is left open at the level of judgemenmts.

There is an informal account of the intended interpretation of first order set theory, which is known as the cumulative heirarchy, however this involves a transfinite construction which cannot (on pain of contradiction) ever be completed.
One needs only to take this just so far to get a model of ZFC, so the fact that it can never be completed is not necessarily a matter for great concern.
However, we will worry about it a bit here.

The cumulative heirarchy was a good intuitive guide to the meaning of first order set theory only during the first half of the twentieth century.
Since then, technical developments have pushed the culture of set theorists away from such vague informalities, and towards a more formalisitic attitude towards set theory.
Powerful techniques were devised for proving independence results, and many logicians now regard a problem in set theory not as the determination of whether some first order conjecture is true, but rather as determining whether it is derivable from, refutable by or independent of the axioms of ZFC.


\newpage
\section{POSTSCRIPT}

On returning to this fragment which I never progresssed any further, I am concerned to give a concise characterisation of what I then intended, which is tricky!

First of all let me say that the foundational project of identifying a language suitable to act as ultimate foundation for the definition of abstract semantics inevitably runs into a problem of infinite regress.
A relevant split in the options for addressing this is as follows:

The first is to devise a system which is self-defining.
There are obvious disadvantages in this, since such a reflexive definition may be ambiguous in important ways, as was shown a very lomg time ago for the LISP programming language.
Nevertheless, such a self-definition would be a good starting point which when supplemented by other kinds of explanation, especially in areas of ambiguity, might prove valuable.

The second is to accept the usual (shall I say Tarkian) view that a heirarchy of languages is necessary and that any language of this sort can only be given a semantics by a language which is strictly stronger.
This is not so bad as it sounds, if the stronger language is essentially the same except that its semantics is bolstered by some stronger principles of infinity.

For the most convincing foundational effort, one might consider doing both of these things.

If one is interested in this foundational project, then clearly, whether the first is a genuine option is significant, and it was the purpose of this false start to give an example to show that the first possibility could not be summarrily dismissed (even if not a credible semantics in my mind).

The notion of semantics I had in mind was simply to give the truth conditions, and since these languages do not make empirical claims the sentences take the same truth value in every possible world, and hence is suffices to identify the set of sentences which are true.
The simeplest imaginable semantics which has this character is to take an axiomatic set theory and identify truth with provability.
The set of true sentences will then be effectievly enumerable, and such sets are definable in any reasonable set theory, and hence any reasonable axiomatic set theory has a minimalistic semantics obtained by identifying truth and provability which is definable im that language interpreted according to that semantics.

In discussion of this idea it was rejected because it does not comply with some of the conditions stipulated by Tarski in his paper on defining truth \cite{tarski31,tarski56} (I think it was comdition T).
However, in relation to the foundational project I touched upon above, I don't see that the objection is important.

The example I spoke of above is not a real contender for a semantics for set theory taking set theory as a universal foundation for abstract semantics, since it is far too weak, but it served to eliminate, pro-tem, arguments against seeking reflxive semantics.
I was then more interested than I am now in non-well founded set theories and I antifipated that a strong non-well founded system might have similar lack of conformance to Tarski's principles (since he basically didn't address languages in which some sentences might not have truth values).
Though I still find the restraint to well foundedness irksome and restrictive, I believe that it is acceptable in the foundational role, if not ideal in more practical application.
For this reason, when I comes to addressing the foundations of abstract semantics, I now no longer consider anything other than well-founded set theories.

For those wondering why I do not consider constructive type theories or homotopy type theory, this is not the place for any explanation I might give.

=SML
open_theory "misc2";
force_new_theory "semfos";
set_merge_pcs ["misc21", "'savedthm_cs_∃_proof"];
=TEX



{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj2,fmu}
} %\raggedright

\appendix

\ignore{
{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{semfos.th}
}  %\let
}%ignore

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
