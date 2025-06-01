=TEX
\def\rbjidtADIdoc{$$Id: t038.doc,v 1.5 2011/05/16 21:40:17 rbj Exp $$}

The following presentation of Higher Order Logic is undertaken using the interactive proof assistant {\Product}.
The first part of the presentation (Sections \ref{ST}-\ref{STT}) closely follows Church's paper \cite{church40}, and the remainder accounts for the subsequent developments which are relevant to an understanding of documents produced using {\Product}.

Church's formulation of the simple theory of types is distinguished by its simplicity, which is made possible by basing the theory upon the typed lambda calculus.
This makes it possible to define as higher order constants all but a very few of thee logical connectives.

Because of its great simplicity there is no better place to start than with Church's system.
Once this is described the modest adjustments and extensions which help to make STT into a practical language for developing mathematics with a proof tool are readily understood.

It is not always easy for those who have spent a lifetime working with these ideas to understand which parts will prove hard to grasp for people coming to this with a different background.
I have assumed some familiarity with modern symbolic logic, and an acquaintance with the idea of programming languages.
Beyond that I suspect that the idea of higher order functions, which is pervasive, will be the largest stumbling block for any readers whc are not previously acquainted with it. and so I have made an attempt to make that clear.

I hesitate to say that I anticipate a wide audience for this material, but whatever my expectations on that score, it is written to accompany my work on the application of formal methods using {\Product} to problems in philosophy and elsewhere.
It is therefore written with the aim of making it possible for some philosophers to read and understand that kind of formal material, without daring to hope that any other philosopher might adopt the methods.

\subsection{Abstract and Concrete Syntax}

When Church wrote his paper \emph{Abstract} syntax had not been invented.
I first came across this idea when I came to `denotation semantics', an approach to the semantics of programming languages concocted by a computer scientics (Strachey) and a set theorist (Scott) collaborating at Oxford.
It is beneficial when working in the design of complex programming languages, simplifying the task by separating out the details and difficulties of the concrete presentation of the language from the underlying abstract structure both of syntax and of semantics.

In presenting Higher Order Logic here, the emphasis is on the underlying abstract structures.
Where examples are given, of necessity they must be presented using some concrete syntax, and this will be the concrete syntax adopted in {\Product-HOL}.

\section{Simple Types}\label{ST}

Simple types, as presented by Church in his paper presenting \emph{A Formulation of The Simple Theory of Types}\cite{church40}, consist of the set of types obtainable from two primitive types, that of individuals ($ι$) and that of propositions ($∘$) by repeated application of the function type construction.
The function type is written by Church as juxtaposition of the two types from which it is formed codomain first, the whole enclosed in brackets.
Thus $(∘ι)$ is a type of propositional functions, functions whose domain is the individuals and whose codomain is the propositions.
These may be thought of as first-order predicates.

We will work henceforth with the type system as is appears in {\Product-HOL}.
The differences in the type systems insofar as they bear upon the present section are, firstly that the type of individuals is called \emph{IND} rather than $ι$ and secondly that the instead of a type of \emph{propositions} {\Product} has a type of \emph{truth values}, \emph{BOOL}.%
\footnote{In Church the axiom of excluded middle is left optional, so that the logic need not be `classical'.
In {\Product-HOL} the axiom of exluded middle is stated as the assertion that there are just two truth values, $T$ and $F$.}
For illustrative purposes we work as if the primitive types were the natural numbers, $ℕ$ and the truth values \emph{BOOL}.

Types will normally be shown in ``Quine corners'' thus: ⓣℕ⌝ is the type of natural numbers and ⓣBOOL⌝ the type of truth values.
We work with a ``meta-language'' which is a functional programming language, and which allows us to manipulate syntax using a computer, and provides facilities for constructing and checking formal proofs.
The text will be interspersed with short scripts which should be understood as being submitted to an interactive proof tool in sequence.

For example:
=SML
val one = 1;
=TEX

gives the name $one$ to the number 1.
We may also sometimes show the response of the tool to such an input.
Thus, to the input:

=SML
one+one;
=TEX

the system will now respond:

=GFT ProofPower output
val it = 2 : int
=TEX

showing that {\Product} has evaluated the expression \emph{one + one} and concluded that its value is the integer 2.

Standard ML (SML) is itself closely related to the typed lambda calculus which is our subject matter, so we have similar type systems and facilities for functional abstraction both in our metalanguage and in our object language.
In order to talk about the object language type system in our metalanguage we have in SML a type \emph{TYPE} which has a structure corresponding to that of the types of the object language.
When an expression is entered in the type quote brackets $ⓣ$ and $⌝$ it is construed as an object of type TYPE representing a type of the object language, and can then be manipulated as such.

The exchange:

=SML
ⓣℕ⌝;
=TEX

=GFT ProofPower output
val it = ⓣℕ⌝ : TYPE
=TEX

shows that {\Product} has recognised the type we entered as a type.

Function types may be written in the object language using the infix function type constructor $→$, or may be computed using the metalanguage function $mk\_→\_type$.
Thus a truth-valued function may have type:

=SML
ⓣℕ → BOOL⌝;
=TEX

which may also be obtained by the following computation:

=SML
mk_→_type (ⓣℕ⌝, ⓣBOOL⌝);
=TEX

=GFT ProofPower Output
val it = ⓣℕ → BOOL⌝ : TYPE
=TEX

Thus the heirarchy of types is the set of types which are obtainable from $ⓣℕ⌝$ and $ⓣBOOL⌝$ by use of the metalanguage function $mk\_→\_type$ or the object language infix type constructor $→$.

\section{The Simply Typed Lambda Calculus}\label{TSTLC}

The simple types are introduced to serve as a type system for a typed $lambda-calculus$.

The lambda-calculus is the simplest imaginable notation for functional abstraction and application.

Functional abstraction is the process of obtaining a function from some expression containing variable symbols.

A function is a mapping from argument values to result values.
When a function is to be defined using an expression, such as $⌜x + x * x⌝$ the idea is that the value of the function for some argument is obtained by substituting the value of the argument for the variable in the expression and the resulting expression is then evaluated to give the value of the function for that argument.
However, we want to be able to do this with expressions which contain more than one variable, and we then need to be able to stipulate which variable is to be used for the argument value.

Typically this might be done as follows:

=GFT
f(x) = x + x*x
=TEX

\section{Church's Simple Theory of Types}\label{STT}

=SML
infix →;
datatype Type = ∘ | i⋎ | op → of Type * Type;
=IGN
∘ → i⋎;
=TEX

=SML
fun	print_Type ∘ = "∘"
|	print_Type i⋎ = "i"
|	print_Type (f → a) = concat [if f = ∘ orelse f = i⋎ then print_Type f else concat ["(", print_Type f, ")"], "→", print_Type a]
;
=TEX
=IGN
print_Type (∘ → i⋎);

=TEX

=IGN
fun def_const consts (h::t) = find consts (fn c => fst(dest_const c) = h)
		handle _ => def_const consts t; 

fun def_consts consts (h::t) = (((h, get_spec (def_const consts h))
			:: (def_consts consts t)) handle _ => def_consts consts t)
|   def_consts consts [] = [];

fun get_specs thy = def_consts (get_consts thy) (map fst (get_defns thy));

get_specs "ℝ";
get_consts "ℕ";
get_defns "ℕ";
map fst (get_defns "one");
=TEX

=SML
infix ⋏⁀;
fun a ⋏⁀ 0 = a |
    a ⋏⁀ n =	let val a' = a  ⋏⁀ (n - 1)
		in (a' → a') → (a' → a')
		end;

infix ⋎a;
datatype Term =	V of string * Type
		| C of string * Type
		| op ⋎a of Term * Term
		| λ of string * Type * Term;
=TEX
=SML
fun	atomic_Term (V (s, t)) = true
|	atomic_Term (C (s, t)) = true
|	atomic_Term x = false;

fun print_Term (V (s, t)) = concat["(", s, ":", print_Type t, ")"]
|	print_Term (C (s, t)) = concat["(", s, "::", print_Type t, ")"]
|	print_Term (f ⋎a a) = concat[
		print_Term f,
		if atomic_Term a then print_Term a else concat["(", print_Term a, ")"]]
|	print_Term (λ (s, ty, tm)) = concat ["λ", s, ":", print_Type ty, print_Term tm];
=TEX

=SML
infix 8 ⋎a;
=IGN
datatype Term = op ⋎v of string * Type
	| op ⋎c of string * Type
	| op ⋎a of Term * Term	
	| λ of string * Type * Term;
=SML
exception Ill_typed_term of string;

fun typ_of (V(s, t)) = t
|   typ_of (C(s, t)) = t
|   typ_of (λ (s,ty,te)) = ty → (typ_of te)
|   typ_of (f ⋎a a) = let val (tfd → tfc) = typ_of f
		     and ta = typ_of a
	 	     in	if tfd = ta
			then tfc
			else raise Ill_typed_term (translate_for_output ((concat[
				"function:", print_Term f, " :", print_Type (tfd → tfc), " ",
				"argument:", print_Term a, " :", print_Type (ta)])))
		     end;

typ_of ((C ("a", i⋎ → ∘)) ⋎a (V ("a", i⋎)));
=TEX

=SML
fun ~ A = C("N", (∘ → ∘)) ⋎a A;
infix ∨;
fun A ∨ B = C("A", ∘ → ∘ → ∘) ⋎a A ⋎a B;
infix ∧;
fun A ∧ B = ~(~ A ∨ ~ B);
infix ⊃;
fun A ⊃ B = (~ A ∨ B);
infix ≡;
fun A ≡ B = (A ⊃ B) ∧ (B ⊃ A);
fun ∀ A = C("Π", ((typ_of A) → ∘)) ⋎a A;
fun ∃ A = ~ (∀ (~ A));
fun ι A = let val ta = typ_of A
	in C("ι", ta → ∘) ⋎a A
	end;
infix Q;
fun A Q B =
	let	val ft = (typ_of A) → ∘;
		val f = V("f", ft)
	in ∀ (λ("f", ft, f ⋎a A ⊃ f ⋎a B))
	end;
infix ≠;
fun A ≠ B = ~ (A Q B);
fun I⋎t a = λ("x", a, V ("x", a));
fun I A = (I⋎t (typ_of A)) ⋎a A;
fun K⋎t a1 a2 = λ("x", a1, λ("y", a2, V ("x", a1)));
fun K A B = K⋎t (typ_of A) (typ_of B) ⋎a A ⋎a B;
fun Z⋎t a = λ("f", a → a, I⋎t a);
fun Nat⋎t a n = λ("f", a → a, λ("x", a, fun_pow n (fn t => V("f", a → a) ⋎a t) (V("x", a))));
fun Suc⋎t a = 
	let val f = V("f", a → a);
	    val n = V("n", a ⋏⁀ 1);
	    val x = V("x", a)
	in λ("n", a ⋏⁀ 1, λ("f", a → a, λ("x", a, (f ⋎a ((n ⋎a f) ⋎a x)))))
	end; 
fun Suc A = (Suc⋎t (typ_of A)) ⋎a A;
fun N⋎t a = λ("n", a ⋏⁀ 1,
	∀ (λ("f", ((a ⋏⁀ 1) → ∘),
	  (V ("f", (a ⋏⁀ 1) → ∘) ⋎a (Z⋎t a))
	  ⊃ (∀	(λ("x", a ⋏⁀ 1,
		  (V("f", (a ⋏⁀ 1) → ∘) ⋎a (V("x", a ⋏⁀ 1)))
		  ⊃ (V("f", (a ⋏⁀ 1) → ∘) ⋎a Suc(V("x", a ⋏⁀ 1)))
		) )
	  ⊃ (V("f", (a ⋏⁀ 1) → ∘) ⋎a (V("n", a ⋏⁀ 1))
	    )
	))));
=IGN
typ_of (Suc(V ("x", (i⋎ ⋏⁀ 1))));
typ_of ((N⋎t i⋎));
"\173";
print_Type (i⋎ ⋏⁀ 2);
print_Term (Suc(V ("x", (i⋎ ⋏⁀ 1))));
typ_of(V ("x", (i⋎ ⋏⁀ 1)));
=TEX


\section{HOL}\label{HOL}

\subsection{Origins}

Formal Higher Order Logics originate in Russell's Theory of Types \cite{russell08} which is a so-called \emph{ramified} type theory, the ramifications in which are obviated by the adoption of an axiom of reducibility.
That the effect could be obtained more economically by omitting both the ramifications and the axiom of reducibility was quickly noted, and the resulting Simple Theory of Types was first codified in detail by Rudolf Carnap in his \emph{Abriss Der Logistik}\cite{carnap29}.

Alonzo Church, for the purpose of answering the `enscheidungsproblem' distilled the essence of functional abstraction into the lambda-calculus, and subsequently investigated whether this calculus could be made the basis for a logical systems strong enough for mathematics.
An attempt using a type-free lambda-calculus having foundered, Church put forward an elegant and economic formulation of the Simple Theory of Types \cite{church40} based on a simply-typed lambda-calculus.
Later, Robin Milner (a computer scientist), for purposes connected with program verification using a logic for computable functions devised by Dana Scott (a set theorist), devised a polymorphic version of the simply typed lambda calculus (i.e. one in which type variables were permitted), and lead the development of LCF, an interactive proof assistant in which formal proofs in LCF could be constructed and checked using a functional programming language also benefitting from a polymorphic type system.

The version of Higher Order Logic which is used in this document was then devised by Mike Gordon for the formal verification of digital hardware.
It consists of Church's formulation of the Simple Theory of Types made polymorphic, augmented by principles of convervative extension and implemented following the LCF paradigm as a proof assistant.
The present document was prepared using a subsequently developed proof assistant for that same logical system, again following the patterm set by LCF.

\subsection{The HOL Language}

For a fully detailed account of the {\ProductHOL} language see the {\Product} Description Manual\cite{ds/fmu/ied/usr005}.
Tutorial material may be found in \cite{ds/fmu/ied/usr022,ds/fmu/ied/usr013}.
The following is a very simplified and condensed account of the language which might possibly be sufficient for readers of this document.

\subsubsection{Types}

The types are defined inductively as follows.

A type may be any of the following:

\begin{itemize}
\item a type-variable
\item a type construction consisting of a type constructor applied to a (possibly empty) finite sequence of types
\end{itemize}

\subsubsection{Terms}

Typed lambda terms consist of terms of the lambda-calculus annotated by types in the above type system.

The terms are defined inductively as follows.

A term may be any of the following:

\begin{enumerate}
\item a variable consisting of a name and a type
\item a constant also consisting of a name and a type
\item an application consisting of two terms, a function on the left and an argument on the right
\item an abstraction consisting of a variable (name and type) and a body (a term). 
\end{enumerate}

Terms must be well-typed, and if well-typed will have a most general polymorphic simple type.
The following rules must be observed.

In an application the function must have a type of the form $ⓣα → β⌝$ and the argument must have type $ⓣα⌝$.
The application will then have type $ⓣβ⌝$

The type of an abstraction is formed from the type of the variable and the type of the body, and is the type of functions from the first to the second.
It is written as a lambda abstraction.

If $b$ has type $ⓣβ⌝$ then the lambda abstraction $⌜λx:α⦁ b⌝$ will have type $ⓣα→β⌝$.

In the concrete syntax of terms the presentation of applications is controlled by the use of fixity declarations which indicate whether the application of a variable or constant of a give name should be written prefix (with the function on the left of the argument), postfix (with the function on the right), or infix (with the function bewteen two arguments) and also permits a precedence to be assigned which controls how the parser inserts omitted brackets.
Functions take only one argument which need not be enclosed in brackets, however, that argument might be a pair (or a pair of pairs) formed by the infix operator 
=INLINEFT
⌜$,⌝
=TEX
, in which case it would normally be enclosed in brackets.
As in this example, the lexical status of a function may be suspended by preceding it with a dollar sign, and this is necessary if the function is to be used as an argument to some other function.

Type variables begin with a backquote $\verb!`!$.
Variable and constant names may include special symbols.


\subsubsection{Formulae and Sequents}

A formula is a term of type ⓣBOOL⌝.

The logical system is a Hilbert style sequent calculus.
A sequent is a list of formulae (the assumptions) together with a single formula (the conclusion).
A sequent which has not been proven is called a goal or a conjecture.
Sequents which have been proven have a special ML type THM.
Objects of this type can only be computed by computations which parallel the structure of the logical system with the effect that all objects of type THM are indeed theorems of the logic derivable in an appropriate context.
The relevant kind of context is call a theory, and determines what definitions and/or non-logical axioms are in scope.
Theories are organised into a heirarchy, each theory except "min" having at least one parent and inheriting all definitions and axioms from its ancestors.
Proven theorems may be saved in a theory, in which case they will be listed with the theory.

\subsubsection{Primitive Type Constructors and Constants}

The primitive type constructors and constants are introduced in \href{http://www.rbjones.com/rbjpub/pp/min.html}{theory min}.

There are three primitive type constructors.
Two 0-ary constructors (type constants), a type of individuals $ⓣIND⌝$ and a type of truth values $ⓣBOOL⌝$, and a 2-ary constructor $→$ (function space) normally written infix (
=INLINEFT
ⓣBOOL → BOOL⌝
=TEX
is the type of unary functions over type $ⓣBOOL⌝$).

There are just three primitive constants:

\begin{centering}
\hfil
\begin{tabular}{l l l}
$⇒$&$:BOOL→BOOL→BOOL$ & material implication\\
$=$&$:'a→'a→BOOL$ & equality\\
$ε$&$:('a→BOOL)→'a$ & the choice function\\
\end{tabular}
\hfil
\end{centering}

\subsubsection{Primitive Definitions}

Certain definitions are required before the axioms of HOL can be stated.
These define the logical connectives and quantifiers and the concepts of injection and surjection which are needed in the axiom of infinity and in defining new types.

\begin{centering}
\hfil
\begin{tabular}{l l}
T &	$:BOOL$\\
$∀$ &	$:('a→BOOL)→BOOL$\\
$∃$ &	$:('a→BOOL)→BOOL$\\
F &	$:BOOL$\\
$¬$ &	$:BOOL→BOOL$\\
$∧$ &	$:BOOL→BOOL→BOOL$\\
$∨$ &	$:BOOL→BOOL→BOOL$\\
OneOne & $:('a→'b)→BOOL$\\
Onto &	$:('a→'b)→BOOL$\\
TypeDefn & $:('b→BOOL)→('a→'b)→BOOL$\\
\end{tabular}
\hfil
\end{centering}

These definitions may be found in \href{http://www.rbjones.com/rbjpub/pp/log.html}{theory log}.

\subsubsection{Fixity and Sugar}

In order to make HOL terms more readable, certain special syntactic forms are accepted by the parser which are closer to normal mathenatical notation than would otherwise be acceptable.
Full details of the accepted concrete syntax are shown in the {\Product} Description Manual \cite{ds/fmu/ied/usr005}

\hfil
\begin{tabular}{l l p{3in}}
& {\bf Sugared} & {\bf Unsweetened} \\
binders &
=INLINEFT
∀x⦁ x+x
=TEX
&
=INLINEFT
$∀ (λx⦁ x+x)
=TEX
\\
paired abstractions &
=INLINEFT
λ(x, y)⦁ x
=TEX
&
=INLINEFT
Uncurry (λx y⦁ x)
=TEX
\\
let clauses &
=INLINEFT
let a = 4 in a * a
=TEX
&
=INLINEFT
Let (λa⦁ a * a) 4
=TEX
\\
if clauses &
=INLINEFT
if a = 4 then 0 else a * a
=TEX
&
=INLINEFT
Cond (a = 4) 0 (a * a)
=TEX
\\
set displays &
=INLINEFT
{1;2;3}
=TEX
&
=INLINEFT
Insert 1 (Insert 2 (Insert 3 {}))
=TEX
\\
set comprehension &
=INLINEFT
{x | x ≤ 34}
=TEX
&
=INLINEFT
SetComp (λx⦁ x ≤ 34)
=TEX
\\
list displays &
=INLINEFT
[1;2;3]
=TEX
&
=INLINEFT
Cons 1 (Cons 2 (Cons 3 []))
=TEX
\\
\end{tabular}
\hfil

\subsection{The HOL Deductive System}

\subsubsection{Axioms}

There are five axioms.


\hfil
\begin{tabular}{l l}
$bool\_cases\_axiom$ & asserts that T and F are the only values of type BOOL.\\
$⇒\_antisym\_axiom$ & asserts that implication is antisymmetric.\\
$η\_axiom$ & makes functions extensional.\\
$ε\_axiom$ & is the axiom of choice.\\
$infinity\_axiom$ & is the axiom of infinity.\\
\end{tabular}
\hfil

These axioms may be found in \href{http://www.rbjones.com/rbjpub/pp/init.html}{theory init}.

\subsubsection{Rules of Inference}

There are six primitive rules of inference in Church's STT:

\begin{itemize}
\item[I] Alpha conversion.
\item[II] Beta contraction.
\item[III] Beta expansion.
\item[IV] Substitution for free variables
\item[V] Modus Ponens
\item[VI] Universal Generalisation
\end{itemize}

Our system also needs a rule permitting the instantiation of type variables.

\subsubsection{Definitions and Other Extensions}

There are three kinds of extension which are possible.
Axioms, definitions and conservative extensions.

An axiom is an assertion of a sequent without proof.
These are always stored as such in the current theory when they are asserted so that the axioms used in deriving theorems can be determined.
HOL is a powerful logical system sufficient for the development of a large part of mathematics using only definitions or conservative extensions over the primitive logical axioms.
It is therefore rarely necessary to adopt new axioms, and it is the norm to proceed by definitions and conservative extensions.




\section{ProofPower}

\section{Conclusions}
