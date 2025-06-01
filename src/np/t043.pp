=IGN
$Id: t043.doc,v 1.2 2013/01/03 17:12:44 rbj Exp $
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
\usepackage{ProofPower}
\ftlinepenalty=9999
\usepackage{A4}

%\def\ExpName{\mbox{{\sf exp}
%\def\Exp#1{\ExpName(#1)}

\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{More Miscellanea}
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
This theory is for miscellanea which depend upon well-founded set theory with urelements (GSU).
It also has misc1 as a parent.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created: 2010/11/13

Last Change $ $Date: 2013/01/03 17:12:44 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t043.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t043.pdf}

$ $Id: t043.doc,v 1.2 2013/01/03 17:12:44 rbj Exp $ $

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

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\newpage

\section{INTRODUCTION}

This document contains material which was in \cite{rbjt025} but which depends upon GSU \cite{rbjt042} and therefore caused all theories dependent on \cite{rbjt025} to be rebuilt every time GSU was changed.
It is moved here to reduce the rebuilding which takes place as a theory of transfinite sequences is added to GSU.


=SML
open_theory "misc1";
force_new_theory "⦏misc3⦎";
new_parent "GSU";
force_new_pc "⦏'misc3⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'misc3";
set_merge_pcs ["misc11", "'GSU", "'misc3"];
=TEX

\section{SET THEORY}

\subsection{Mapping Functions over Sets}

The following function makes recursive definition of functions over sets of type GS just a little more compact.

ⓈHOLCONST
│ ⦏FunImage⋎u⦎ : ('a GSU → 'b) → 'a GSU → ('b SET)
├───────────
│ ∀f s⦁ FunImage⋎u f s = {x | ∃y⦁ y ∈⋎u s ∧ x = f y}
■

=GFT
⦏funimage⋎u_fc_lemma⦎ =
	⊢ ∀ f s x⦁ x ∈⋎u s ⇒ f x ∈ FunImage⋎u f s
=TEX

\ignore{
=SML
set_flag("subgoal_package_quiet", true);


set_goal([], ⌜∀f s x⦁ x ∈⋎u s ⇒ f x ∈ FunImage⋎u f s⌝);
a (∀_tac THEN rewrite_tac [get_spec ⌜FunImage⋎u⌝] THEN REPEAT strip_tac);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[]);
val funimage⋎u_fc_lemma = save_pop_thm "funimage⋎u_fc_lemma";

set_merge_pcs ["misc11", "'misc3"];
=TEX
}%ignore


=SML
add_pc_thms "'misc3" [];
commit_pc "'misc3";

force_new_pc "⦏misc3⦎";
merge_pcs ["misc1", "'GSU", "'misc3"] "misc3";
commit_pc "misc3";
force_new_pc "⦏misc31⦎";
merge_pcs ["misc11", "'GSU", "'misc3"] "misc31";
commit_pc "misc31";

set_flag("subgoal_package_quiet", false);
=TEX




{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{misc3.th}
}  %\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
