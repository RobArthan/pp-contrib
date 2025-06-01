=IGN
$Id: t054.doc $
=TEX
\documentclass[11pt,a4paper]{article}
%\usepackage{latexsym}
%\usepackage{ProofPower}
\usepackage{rbj}
\ftlinepenalty=9999
\usepackage{A4}

\usepackage{fontspec}
\setmainfont[]{ProofPowerSerif}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}
\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{Formal Synthetic Epistemology}
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
Some formal modelling intended to aid precision to sharpen the presentation of ideas on how to contruct an episteme, which activity I describe as \emph{synthetic epistemology}.
The most abstract stages in the design of cognitive systems are essentially epistemological, one must have some theory of knowledge in order to design and construct things that know.
Consideration of these matters in the context of cognitive systems as they might be, rather than in that rather special cognitive system which we call homo sapiens, may therefore be an interesting and useful way of progressing the theory of knowledge.

A second aspect of the work is the status it gives to logical truth as a basis for all other kinds of propositional or declarative knowledge.
This is an aspect which is substantially informed by very recent advances in logic and its application.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2020/01/20

Last Change $ $Date: 2020/01/20 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t054.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t054.pdf}

$ $Id: t054.doc 2016/08 $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize

\end{centering}

\thispagestyle{empty}
\end{titlepage}
\newpage
\addtocounter{page}{1}
{\parskip=0pt\tableofcontents}

\newpage

\section{INTRODUCTION}

The ancient Greeks invented mathematics as a theoretical discipline.
As a theoretical discipline, mathematics is concerned with defining and reasoning about the abstract structures which are the subject matter of mathematics, and which underpin practical applications of mathematics.
This yields theorems, which are obtained by logical deduction from the basic premises and definitions which characterise the mathematical structures.

Because of the clarity with which the objects of mathematics can be defined, this process proved to be highly productive and reliable, and very early in the development of mathematics standards of rigour were achieved and documented which would not be exceeded for the next two thousand years.

This was in stark contrast with the other domains in which the Greek philosophers sought knowledge through reason.
The divide between what can be accomplished by reason in the artificially precise domains of abstract mathematics, and in in reasoning about the concrete world around us or about the values and morals which motivate and moderate behaviour has been recognised ever since.

Mathematics in modern times began to see advances such as Cartesian geometry, and became the foundation for the blossoming of science and engineering with the invention of the differential and integral calculus by Newton and Leibniz.
The practical utility of these new methods lead to an explosion in the mathematics which paid no more heed to rigour than was needed for the application, despite the calculus being founded on novel mathematial concepts such as infinitesimals which were wreathed in obscurity.

By the beginning of the nineteenth century rumours of discontent were being heard from some mathematicians about the apparent lack of rigour in the establishment of mathematical theorems, and a number of mathematicians began to pay attention to the foundations with a view to rebuilding on a more solid base.

The first stages in this may be broadly charactersied as concerned with conceptual clarificiation, which included showing how these theories could be formulated without resort to infinitesimals, and the clarification of the notion of 'function', important to these new mathematical domains.

During the second half of the century this foundational thrust turned to the clarification of the nature of logical deduction.
It was Aristotle who had first sought to clarify these matters, but Aristotelian logic, though reigning supreme ever since, was not adequate for the kimd of reasoning undertaken in mathematics, which had been progressed by less formal, but largely reliable, deductive methods ever since.

\section{THE DATA LAYER}

=SML
open_theory "hol";
force_new_theory "t054";
set_pc "hol";
=TEX

\ignore{
=SML

=TEX
}%ignore

\appendix

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{t054.th}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{t054.th}
}%\let

%{\raggedright
%\bibliographystyle{fmu}
%\bibliography{rbj,fmu}
%} %\raggedright

%{\let\Section\section
%\newcounter{ThyNum}
%\def\section#1{\Section{#1}
%\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
%\include{ordcard0.th}
%\def\section#1{\Section{#1}
%\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
%\include{ordcard.th}
%}%\let

%\twocolumn[\section{INDEX}\label{index}]
%{\small\printindex}

\end{document}
