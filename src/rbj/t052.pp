=IGN
$Id: t052.doc,v 1.6 2016/07/29 $
=TEX
\documentclass[11pt,a4paper]{article}
%\usepackage{latexsym}
%\usepackage{ProofPower}
\usepackage{rbj}
\ftlinepenalty=9999
\usepackage{A4}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}
\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{The Logical Syntax of Language}
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
Some notes on one of Carnap's greatest works.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2013/01/20

Last Change $ $Date: 2014/08/17 16:07:53 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t052.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t052.pdf}

$ $Id: t052.doc 2016/07/29 $ $

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

At first this document is just notes and other ways of helping me digest the content of LSL.
The reason for my wanting to do this (in greater than the very superficial way I already have) is because of my finally beginning to take seriously the counterattack against Quine, which I am at present trying to get moving.

\section{SYNTAX IN SML}

I have sometimes found that a good way to clarify my understanding of a formal system is to render the syntax of the system, not in a formal specification language, but just in the functional programming language ``Standard Meta-Language'' (henceforth SML).

In LSL Carnap describes two formal languages (or families of formal languages) which he calls ``Langauge I'' and ``Language II''.

\subsection{Language I}

Two classes of symbol are defined to keep the complexity down, the sentential operators and the quantifiers.

=SML
datatype Sop = Disj | Conj | Imp | Equiv;

datatype Quant = All | Exists;
=TEX

Which helps keep down the number of clauses in the following mutually recursive definitions of the abstravt syntax of terms and sentences (which are not requierd to be closed).

=SML
datatype LITerm =
	 V of string			(* numeric variables *)
|	 N of int			(* numerals *)
|	 Suc of LITerm			(* successor *)
|	 F of string * LITerm list 	(* functor applications *)
|	 K of string * LITerm * LISent 	(* bounded least *)

and
	LISent =
	P of string * LITerm list	(* predicate applications *)
|	Neg of LISent 	     		(* negation *)
|	Csen of Sop * LISent * LISent	(* compound sentence *)
|	Equ of LITerm * LITerm		(* equation *)
|	Qsen of Quant * string * LISent	(* universal *)
;
=TEX

=SML
val nu = N 0;
=TEX


Over this sytax we can now define some functions (following Carnap, but pretty standard practice still).





\appendix

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

%{\let\Section\section
%\newcounter{ThyNum}
%\def\section#1{\Section{#1}
%\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
%\include{ordcard0.th}
%\def\section#1{\Section{#1}
%\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
%\include{ordcard.th}
%}%\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
