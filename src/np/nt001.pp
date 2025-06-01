% $Id: np001.tex $ﬁ
% bibref{rbjnp001} pdfname{np001}
\documentclass[10pt,titlepage]{article}
\usepackage{makeidx}
\newcommand{\ignore}[1]{}
\usepackage{graphicx}
\usepackage[unicode]{hyperref}
\pagestyle{plain}
\usepackage[paperwidth=5.25in,paperheight=8in,hmargin={0.75in,0.5in},vmargin={0.5in,0.5in},includehead,includefoot]{geometry}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{pdftitle={Advancing Deductive Automation}}
\hypersetup{colorlinks=true, urlcolor=red, citecolor=blue, filecolor=blue, linkcolor=blue}
%\usepackage{html}
\usepackage{paralist}
\usepackage{relsize}
\usepackage{verbatim}
\usepackage{enumerate}
\usepackage{longtable}
\usepackage{url}
\newcommand{\hreg}[2]{\href{#1}{#2}\footnote{\url{#1}}}
\makeindex

\title{\LARGE\bf Advancing Deductive Automation}
\author{Roger~Bishop~Jones}
\date{\small 2025/05/27}


\begin{document}

%\begin{abstract}
% Some thoughts about directions for deductive technology.
%\end{abstract}
                               
\begin{titlepage}
\maketitle

%\vfill

%\begin{centering}

%{\footnotesize
%copyright\ Roger~Bishop~Jones;
%}%footnotesize

%\end{centering}

\end{titlepage}

\ \

\ignore{
\begin{centering}
{}
\end{centering}
}%ignore

\setcounter{tocdepth}{2}
{\parskip-0pt\tableofcontents}

\           

\section{Introduction}

My main interest is in progressing the most advanced and speculative ideas, albeit in perhaps modest ways.
There are quite a number of ideas that I am interested in progressing, and I have presened a first sketch of these ideas in three tiers according to how radical the departure is from existing technology.

THe start point for this exercise is ProofPower support for Cambridge HOL.
I won't go into the merit of that baseline, except to say that the logical system has the characteristics which seem to me most germinal for the roles which I envisage, and the implementation in ProofPower is one with which I am familiar, and which is well documented including a suite of formal specifications in HOL itself.

The three tiers correspond to different levels of disruption of the baseline technology.
They are all considered as contributing to the tier three aspiration.
The highest tier is things which are probably only realisable by starting again from scratch, which is to say, that they involve a complete reconception of the logical kernel.
The first tier includes ideas which can be delivered as non-disruption progressions to the existing system, through the usual combinations of new theories supported by additional superstructure.
The middle tier is for ideas which can be at least explored by various degrees of disruptive re-adaptation of the existing system, possibly retaining the logical kernal but exploring more or less radical recoceptions of the overlying systems.

None of this pretends to be exhaustive, I am concerned only with ideas which might contribute to the strategic objectives which I am pursuing, and the major bets I am placing on how to best progress them.

\begin{itemize}
  \item

    Ideas simple enough to implement in the existing ProofPower system, demanding no reconception of the aims and methods of the systems.
    
  \item

    Ideas Which would significantly advance the existing system possibly into new domains, mainly by adding new technology, particularly greater automation through the adoption of AI.

  \item

    Ideas which represent major reconceptions of the purpose, methods and scope of application of HOL and its support.
   
    
\end{itemize}

The following materials with sketch first the strategic objectives, and some of the ideas which I think might make realisaton of those objectives possible.
Then the main ideas will be sketched, and then some degree of fleshing out of the ideas.

\section{Some Philosophy, Some Strategy)

  Here we go right over to the most radical ideas for the next generation of proof technology, before returning to the components which might best contribute to their realisation.

  \subsection{Epistemology}

  Proof is the best way we know of conclusively establishing truth, and we might say, providing the most reliable ways to conclusively establish truths.
  The philosophical underpinning of this work comes in the epistemological thesis that a certain class of logical systems provide systematic underpinnings for the representation and qualified demonstration of all declarative truths.
  Among these the system which is known as Cambridge HOL, an elaboration of Alonzo Church's Simple Theory of Types devised by Mike Gordon for use in the formal verification of digital hardware, is particularly suitable by virtue of simplicity and power of the logical system and the universality of the underlying abstract syntax for the representation of propositions expressed in any finitary declarative language.

  The central contention is twofold, that all declarative propositions can be thought of as speaking of their subject matter in terms of some abstract model which has been shown to correspond to a suitable of degree of precision to some structure or phenomenon.
  From this perspective, all such declarative propositions about real world phenomena can be factorised into a demonstrable claim about the model, and an empirically supported correspondence between the model and the world.

  

\section{First Sketches}

\subsection{Simple Ideas}

I have only one idea to mention here as yet.
This serves two purposes.
Firstly it strengthens the system in terms of its semantic expressiveness and logical strength, as well as providing a simpler route to support for inductive datatypes.
It is to replace the axiom of infinity with a polymorphic strong infinity, which would give a type of inaccessibly greater cardinality than any monotype.





%\listoffigures

\pagebreak

\phantomsection
\addcontentsline{toc}{section}{Bibliography}
\bibliographystyle{rbjfmu}
\bibliography{rbj}

%\addcontentsline{toc}{section}{Index}\label{index}
%{\twocolumn[]
%{\small\printindex}}

%\vfill

\tiny{
Started 2025/05/27
}%tiny

\end{document}

% LocalWords:
