=TEX
\def\rbjidtADJdoc{$$Id: t044.doc,v 1.2 2011/02/01 21:32:02 rbj Exp $$}

\subsection{Directions and Motivations}

This discussion will be largely by comparison with my own previous efforts and Rob Arthan's work in wrk080 and wrk081.

My own previous is more about abstraction than algebra.
Rob's is definitely algebraic.
Many of the problems we address and the ways in which they are addressed derive from the peculiarities of working formally or of working in a polymorphic type theory rather than (say) in a first order set theory.

\subsection{Overall Strategy}

Here is a preliminary statement of what I have in mind.

The desire is to do abstract mathematics in a way which is in itself reasonably efficient and intelligible, and which can conveniently be applied.
We may think in the first instance of abstract algebra, but the scope is intended to be broader than theories which are strictly algebraic.
An easy one to think of is group theory.

Putting aside for a moment the special considerations which arise when working formally, there are two ways of developing group theory.
One's first thought might be that such algebraic theories start with a set of axioms which define the kind of algebra at stake, and group theory is the first order theory determined by these axioms.
One could do this in HOL just by starting a new theory, putting in the group axioms and then reasoning in that theory.
However, this would be nothing like what group theorists do.
Also, even if it was similar to what they do, it would not be formally applicable.
If we subsequently define elsewhere a structure which complies with the axioms of a group, we would not be able to instantiate the theorems we had proven in group theory to the structure we had defined.
This latter problem is well known at least to computer scientists who develop interactive proof systems, and various approaches to solving it have been implemented.
These are not our present concern here for I am here working in the context of a fixed tool which has very limited features to address this kind of problem, and I am intersted in how to make the most of what we have.

To expand on my allegation that this is not what group theorists do, it seems to me that in developing group theory a group theory, though using the first order axioms, is not really reasoning in the first order theory of groups.
He is primarily reasoning in first order set theory about the structures which satisfy the group axioms.
This is the context in which one can talk about morphisms, it can't be done in the first order theory of groups.
You could interpret group theory as the metatheory of groups, but I don't think there is much syntax in there, so its not really meta-`theory', its not the theory as a syntactic structure which is the object of study, it is the structures which satisfy the theory, i.e. the models of the theory, so its a kind of model theory.
This possibly explains why Cohn's book on Universal Algebra is in significant part about model theory.
Model theory generalises on Universal Algebra, which is of course a generalisation of particular abstract algebras.

So what I am after here is a way of developing the theory of certain kinds of structures which are characterised by sets of axioms.
I don't think the notion of algebra is completely definite, but one way of construing an algebra is through the notion of variety, and this is a constraint on the kinds of theory which characterise the structures which fall under the algebra.
A variety is something like a first order equational theory, a set of equations between expressions in the language of the algebra in question.

Why do we care about this particular constraint on the theory?
Well, one reason for caring is that this constraint guarantees that the theory is consistent, though it doesn't prevent there being non non-trivial models.
This in turn is of some importance in rather grubby ways in the context of formal reasoning with a tool with out much by way of special features for doing abstract algebra, because, by using a special method which Rob Arthan has adopted in \cite{LEMMA/HOL/WRK080,LEMMA/HOL/WRK081}, it is possibly to undertake general reasoning applicable to all members of a variety without an explicit condition in each theorem asserting that the structures under consideration are members of the variety.
There are doubtless other benefits from working specifically in the context of algebraic varieties, but my interest at present is with this one feature, and its generalisation beyond the specific context of algebraic varieties.
I think the reason this works is simply that it guarantees consistency, and that a similar method may work with any kind of theory for which a sufficiently general consistency proof is available.

So the general scheme I have in mind is to devise a way of doing this kind of applicable model theory which is more general and flexible than my last attempt (which was in \cite{rbjt039}) and which allows the kind of treatment of algebraic theories shown in \cite{LEMMA/HOL/WRK080,LEMMA/HOL/WRK081} in as broad a context as possible (hopefully not specific to algebraic varieties).

\begin{itemize}
\item Two layers, one like model theory, the second closer to algebra.
\item Both layers generalised.
\end{itemize}

\subsection{More Specific Notes}

This is a temporary holding place for some more detailed ideas on how this document might differ from its predecessors \cite{rbjt039,LEMMA1/HOL/WRK080,LEMMA1/HOL/WRK081}.

\subsubsection{Points Specific to \cite{rbjt039}}

The present kind of structure in this document has information which belongs to signature, so that one can speak, for example, of a homomorphism between two structures without mentioning the signature.
Nevertheless signatures are present and needed, and the relationship between the two is not clean because of the presence of signature information in the structure.
We want inheritance to work nicely and I now feel that it will work better if there is a cleaner separation between structure and signature.

At this point I am thinking along the lines of a relational structure in which the relations are represented as a string indexed family of maps from lists of values in the carrier to BOOL.

Next, thinking about the methods used by Rob to represent algebraic varieties, I am speculating about generalising something like that to consistent theories.
To this is added the following consideration.
In the case of algebraic varieties on gets a polymorphic theory (polymorphic in the type of the carrier) and we know because of the restriction on the institution (equations between terms) we know that there will always be a trivial solution (with one element) and hence a solution at every type (since all types are non-empty) and so you get a fully polymorphic theory which can be developed without using conditionals.
So this approach is limited to theories which say nothing about the cardinality of the carrier.

So I have this further idea, that if instead of using an arbitrary type as carrier, we use a 

\subsubsection{Points Specific to \cite{LEMMA1/HOL/WRK080,LEMMA1/HOL/WRK081}}

The construction of a new type seems to me in the wrong place.
The type is specifically algebraic and therefore closes down the scope of the work.
The idea is to do as much as possible in the more general model theoretic context and to narrow down for something like an algebraic method (also generalised) as late as possible.

For maximal generality in the model theoretic context a relational theory could be adopted, if we have a fixed conception of structure.
However I am also considering the possibility of a generalised notion of structure and signature.

I don't see the need of a distinguished element.

The arguments in favour of numeric indexes seem weak to me, so I shall go with strings.

\section{Preliminaries}

=SML
open_theory "equiv";
force_new_theory "unalgII";
new_parent "GSU";
force_new_pc ⦏"'unalgII"⦎;
merge_pcs ["'prove_∃_⇒_conv", "'savedthm_cs_∃_proof"] "'unalgII";
set_merge_pcs ["rbjmisc", "'unalgII"];
=TEX

I explore the possibility of doing something like universal algebra using a polymorphic higher order set theory with urelements.
A generalisation of universal algebra is sought in which minimal constraints are imposed to allow the construction of a universal object as a product.
Because of the generality sought the term algebra will not be used, and the flavour will initially be more model theoretic than algebraic (I imagine, though I have limited knowledge of either of these).

So, rather than algebras we talk of structures, and rather than equational varieties we have theories.
One of the aims is to see whether it is convenient to work with universal structures as a way of developing theories.
The supposed benefit is that results need not be conditional (of the form `if A is a group then ....').

The benefit of working in a higher order set theory relative to working in a polymorphic higher order logic without the set theory is expected to be a much more liberal notion of theory to which the work is applicable.

We work with structures, and use values of type $ⓣ'a GSU⌝$ for them.
These may best be thought of in the first instance as dependent pairs, though possibly the approach will work with other kinds of structure.
The first thought for a signature might then be a dependent product `type', represented by a function from values on the left of the pairs to types for the right hand side.
We might then allow that the left hand side be an assignment of sets to type variables (an indexed set of carriers for the operators of the theory), and the right hand side be an indexed set of operators the type of which is given by applying the function determining the dependent type to the value on the left.
However to obtain the universal structures we need to be able to form products of structures which are themselves structures.
This is easier to work out in the context of a more specific idea about what structures and signatures are, so I will do this for higher-order relational structures, and then possibly relax the requirements.

So a higher-order relational structure will be an indexed set of type parameters, and an indexed set of higher-order relations.
A higher order relation is a relation whose domain is some type constructed using the type parameters.
The relation will then be a subset of that type.

A signature will consist of the following:
\begin{enumerate}
\item A set of type variable names.
\item A set of relation names.
\item A function from assignments of sets to type variables to assignments of domains to relation names.
\end{enumerate}

Think of this as a kind of syntactic object to which a value is assigned as follows:


\ignore{
=SML
commit_pc "'unalgII";

force_new_pc "⦏unalgII⦎";
merge_pcs ["rbjmisc", "'unalgII"] "unalgII";
commit_pc "unalgII";

force_new_pc "⦏unalgII1⦎";
merge_pcs ["rbjmisc1", "'unalgII"] "unalgII1";
commit_pc "unalgII1";
=TEX
}%ignore


\section{Conclusions}
