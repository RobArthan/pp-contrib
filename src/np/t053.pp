=IGN
$Id: t053.doc $
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
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

\title{Simple Predicate Calculus Proof Methods for HOL and Z}
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
Notes on some simple and instructive methods of proof for predicate calculus theorems in {\Product} HOL and Z.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2013/01/20

Last Change $ $Date: 2014/08/17 16:07:53 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t053.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t053.pdf}

$ $Id: t053.doc 2016/08 $ $

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

A tool such as {\Product} for constructing formal logical proofs is a good way to get an understanding of logic and set theory for discrete mathematics. 
However, formal proofs, by comparison with ordinary mathematical proofs, are very detailed, long, complicated and constructing these manually is onerous.
This is one of the reasons why the construction of formal proofs, with the exception only of those for teaching logic in textbooks, is normally conducted using software which takes on lot of the detailed work and ensures that the proof is correct.

In ordinary journal or text book mathematics proofs, the level of proofs is very much higher than that which would be necessary for fully formal proofs, and mathematicians do not need to know the details of any formal deductive system to undertake such proofs.
Primitive inference rules are simply not something that one needs to know about to do mathematics.

Constructing formal proofs using sophisticated software is very different, but it shares the same characteristic.
It is not necessary to know the primitive inference rules, and when constructinbg proofs in this way, the user will not often use primitive rules, and may not be aware of which of the rules he uses are primitive.

Normally also, a primitive inference system provides for what Euclid would have called {\it synthetic} proofs (and we call {\it forward} proofs), in which the proof proceeds from the axioms of the system, using the rules, to the desired theorem.
In practice, it is usually easier to undertake a proof by what the Greeks would have called an {\it analytic} proof, in which we start with the conjecture to be proven, and work our way back to the axioms, at each stage reducing the problem to simpler subproblems from which the desired results can be derived.
This is now often called {\it backward} or goal oriented proof, and may be undertaken using software called a goal package.
The advantage of this is that is is easier for the human being to see how to construct a proof in this way, and it is also easier for the machine to assist in that process, because it knows at every stage what it is that the user of the sotware is trying to prove.
Consequently, in a goal directed proof supported by software, the user has to type much less than he would in a forward proof; his task is easier and takes less time.

An LCF style proof tool such as \Product{} has a rich collection of facilities for constructing such proofs, and it may be difficult for him to know what he needs to learn to become effective in constructing proofs.

\section{An illustrative forward proof}

=SML
val L1 = asm_rule ⌜p(x,y):BOOL⌝;
(* val L1 = p (x, y) ⊢ p (x, y): THM *)
val L2 = ⌜∃x:'a⦁p(x,y)⌝;
(* val L2 = ⌜∃ x⦁ p (x, y)⌝: TERM *)
val L3 = ∃_intro L2 L1;
(* val L3 = p (x, y) ⊢ ∃ x⦁ p (x, y): THM *)
val L4 = ⌜∃y:'b⦁∃x:'a⦁p(x,y)⌝;
(* val L4 = ⌜∃ y x⦁ p (x, y)⌝: TERM *)
val L5 = ∃_intro L4 L3;
(* val L5 = p (x, y) ⊢ ∃ y x⦁ p (x, y): THM *)
val L6 = asm_rule ⌜∃y:'b⦁p(x,y)⌝;
(* val L6 = ∃ y⦁ p (x, y) ⊢ ∃ y⦁ p (x, y): THM *)
val L7 = ∃_elim ⌜y:'b⌝ L6 L5;
(* val L7 = ∃ y⦁ p (x, y) ⊢ ∃ y x⦁ p (x, y): THM *)
val L8 = asm_rule ⌜∃x:'a⦁ ∃y:'b⦁p(x,y)⌝;
(* val L8 = ∃ x y⦁ p (x, y) ⊢ ∃ x y⦁ p (x, y): THM *)
val L9 = ∃_elim ⌜x:'a⌝ L8 L7;
(* val L9 = ∃ x y⦁ p (x, y) ⊢ ∃ y x⦁ p (x, y): THM *)
val L10 = ⇒_intro ⌜∃x:'a⦁ ∃y:'b⦁p(x,y)⌝ L9;
(* val L10 = ⊢ (∃ x y⦁ p (x, y)) ⇒ (∃ y x⦁ p (x, y)): THM *)
=TEX

=GFT ProofPower Output
val L1 = ⌜p (x, y)⌝ ⊢ ⌜p (x, y)⌝: THM
val L2 = ⌜∃ x⦁ p (x, y)⌝: TERM
val L3 = p (x, y) ⊢ ∃ x⦁ p (x, y): THM
val L4 = ⌜∃ y x⦁ p (x, y)⌝: TERM
val L5 = p (x, y) ⊢ ∃ y x⦁ p (x, y): THM
val L6 = ∃ y⦁ p (x, y) ⊢ ∃ y⦁ p (x, y): THM
val L7 = ∃ y⦁ p (x, y) ⊢ ∃ y x⦁ p (x, y): THM
val L8 = ∃ x y⦁ p (x, y) ⊢ ∃ x y⦁ p (x, y): THM
val L9 = ∃ x y⦁ p (x, y) ⊢ ∃ y x⦁ p (x, y): THM
val L10 = ⊢ ⌜∃ x y⦁ p (x, y)⌝ ⇒ ⌜∃ y x⦁ p (x, y)⌝: THM
=TEX

\section{Predicate calculus proofs in HOL}

\subsection{The Two-tactic Method for HOL}

This method, which is sufficient to prove any theorem in the pure predicate calculus in HOL, has the merit that it provides a systematic approach to these proofs which makes use of just two tactics.

Propositional reasoning is undertaken automatically by the tactics involved, and so the details of this are not explicit, to expose this so that the user can grasp how it works the following three-tactic method is better.

Those operations with quantifiers which can be done without intelligence are also undertaken automatically, which in this method consists only of the elimination of existential quamtifiers whenever an existential clause is added into the assumptions, a process sometimes called "skolemisation".

First we get ourselves into a suitable context:

=SML
open_theory "hol";
new_theory "t053h";
set_pc "hol";
=TEX
and set our goal:
=SML
set_goal([], ⌜(∃ x y⦁ p (x, y)) ⇒ (∃ y x⦁ p (x, y))⌝);
=GFT ProofPower Output
Now 1 goal on the main goal stack

(* *** Goal "" *** *)

(* ?⊢ *)⌜(∃ x y⦁ p (x, y)) ⇒ (∃ y x⦁ p (x, y))⌝
=TEX
The method involves ``indirect'' proof, also called proof by contradiction.
To start such a proof one assumes the negation of the desired theorem and then tries to prove a contradiction, in this case the conjecture "false".
This kind of proof is set up using the tactic {\it $contr\_tac$}, which not only assumes the negation of the desired theorem, but systematicall simplifies that negation as is shown by its action here:
=SML
a (contr_tac);
=GFT ProofPower Output
Tactic produced 1 subgoal:

(* *** Goal "" *** *)

(*  2 *)⌜p (x, y)⌝
(*  1 *)⌜∀ y⦁ ¬ (∃ x⦁ p (x, y))⌝

(* ?⊢ *)⌜F⌝
=TEX
the simplification above arises in the following way:
\begin{itemize}
\item the negated implication is transformed into a conjunction, one conjunct being am existential and the other the negation of an existential.
\item the existential is skolemised before being added as an assumption.
\item the negated existential is transformed into a universal of a negation and added as an assumption.
\end{itemize}
=TEX
in the general pattern the proof then proceeds by instantiating universal assumptions until a contradiction appears in the assumptions.
In this case two instantiations are required:
=SML
a (spec_nth_asm_tac 1 ⌜y⌝);
=GFT ProofPower Output
Tactic produced 1 subgoal:

(* *** Goal "" *** *)

(*  3 *)⌜p (x, y)⌝
(*  2 *)⌜∀ y⦁ ¬ (∃ x⦁ p (x, y))⌝
(*  1 *)⌜∀ x⦁ ¬ p (x, y)⌝
=SML
a (spec_nth_asm_tac 1 ⌜x⌝);
=GFT ProofPower Output
Tactic produced 0 subgoals:
Current and main goal achieved
=TEX

This is an effective method for proving theorems in the predicate calculus, but does not facilitate an understanding of the steps which are being undertaken automatically by the tactics invoked.
Its exclusive use of proof by contradiction may also be thought of as less conducive to understanding than more direct proof methods.
These difficulties can be rememdied by replaeing the use of $contr\_tac$ with $strip\_tac$ and adding to instantiation of assumptions, the offering of witnesses for existential goals, which can be illustrated on the same example as follows.

First we set up our goal again:
=SML
set_goal([], ⌜(∃ x y⦁ p (x, y)) ⇒ (∃ y x⦁ p (x, y))⌝);
=GFT ProofPower Output
Now 1 goal on the main goal stack

(* *** Goal "" *** *)

(* ?⊢ *)⌜(∃ x y⦁ p (x, y)) ⇒ (∃ y x⦁ p (x, y))⌝
=TEX
This time, we strip the conclusion by repeated application of $strip\_tac$.
=SML
a (REPEAT strip_tac);
=GFT ProofPower Output
Tactic produced 1 subgoal:

(* *** Goal "" *** *)

(*  1 *)⌜p (x, y)⌝

(* ?⊢ *)⌜∃ y x⦁ p (x, y)⌝
=TEX
And then we offer witnesses for the nested existentials in our goal:
=SML
a (∃_tac ⌜y⌝);
=GFT ProofPower Output
(* *** Goal "" *** *)

(*  1 *)⌜p (x, y)⌝

(* ?⊢ *)⌜∃ x⦁ p (x, y)⌝
=SML
a (∃_tac ⌜x⌝);
=GFT ProofPower Output
(* *** Goal "" *** *)

(*  1 *)⌜p (x, y)⌝

(* ?⊢ *)⌜p (x, y)⌝
=TEX
and finally strip again ($strip\_tac$ sees that the conclusion is in the assumptions and completes the proof).
=SML
a strip_tac;
=GFT ProofPower output
Tactic produced 0 subgoals:
Current and main goal achieved
=TEX
and now we can retrieve the theorem from the goal package:
=SML
save_pop_thm "ex2_thm1";
=GFT ProofPower Output
Now 0 goals on the main goal stack
val it = ⊢ (∃ x y⦁ p (x, y)) ⇒ (∃ y x⦁ p (x, y)): THM
=TEX
The method we now have is open to greater transparency if the student wants to see what is going on behind the scenes.
When the proof is expanded in that we get the following sequence:

=SML
set_goal([], ⌜(∃ x y⦁ p (x, y)) ⇒ (∃ y x⦁ p (x, y))⌝);
=GFT ProofPower Output
(* ?⊢ *)⌜(∃ x y⦁ p (x, y)) ⇒ (∃ y x⦁ p (x, y))⌝
=SML
a strip_tac;
=GFT ProofPower Output
(*  1 *)⌜p (x, y)⌝

(* ?⊢ *)⌜∃ y x⦁ p (x, y)⌝
=SML

\section{Predicate Calculus in Z}

Predicate calculus proofs in Z are more complex than in HOL because quantification in Z are always bounded by some set, the predicate calculus involves some elementary set theory.
Though it may not be immediately obvious, quantificiation is always over {\it bindings} which are a kind of labelled structure, so these too are involved in the Z predicate calculus.

\subsection{The two-tactic method}

The two tactic method still works, as is shown by this Z version of the first two-tactic example:

=SML
open_theory "z_library";
new_theory "t053z";
set_pc "z_predicates";

set_goal([], ⓩ(∃ x:a; y:b⦁ p (x, y)) ⇒ (∃ y:b; x:a⦁ p (x, y))⌝);
=GFT ProofPower Output
Now 1 goal on the main goal stack

(* *** Goal "" *** *)

(* ?⊢ *)ⓩ(∃ x : a; y : b ⦁ p (x, y)) ⇒ (∃ y : b; x : a ⦁ p (x, y))⌝
=SML
a (contr_tac);
=GFT ProofPower Output
:) a (contr_tac);
Tactic produced 1 subgoal:

(* *** Goal "" *** *)

(*  4 *)ⓩx ∈ a⌝
(*  3 *)ⓩy ∈ b⌝
(*  2 *)ⓩp (x, y)⌝
(*  1 *)ⓩ∀ y : b; x : a ⦁ ¬ p (x, y)⌝

(* ?⊢ *)ⓩfalse⌝
=SML
a (z_spec_nth_asm_tac 1 ⓩ(y ≜ y, x ≜ x)⌝);
=GFT ProofPower Output
Tactic produced 0 subgoals:
Current and main goal achieved
=TEX

\section{The two-tactic method for Z}

=SML
new_theory "ex2z";

set_goal([], ⓩ(∃ x:a; y:b⦁ p (x, y)) ⇒ (∃ y:b; x:a⦁ p (x, y))⌝);
a (contr_tac);
a (z_spec_nth_asm_tac 1 ⓩ(y ≜ y, x ≜ x)⌝);

set_goal([], ⓩ(∃ x:a; y:b⦁ p (x, y)) ⇒ (∃ y:b; x:a⦁ p (x, y))⌝);
a (REPEAT strip_tac);
a (z_∃_tac ⓩ(y ≜ y, x ≜ x)⌝);
a (REPEAT strip_tac);
=TEX

\appendix

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
