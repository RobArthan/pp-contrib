=TEX
\ignore{
=VDUMP t046i.tex
Last Change $ $Date: 2011/05/16 21:40:17 $ $

$ $Id: t046.doc,v 1.8 2011/05/16 21:40:17 rbj Exp $ $
=TEX
}%ignore

Three logical systems are explored in combination in this document.
They are:

\begin{itemize}
\item The logic of pluralities.
\item Set theory.
\item Modal operators.
\end{itemize}

At this stage the document is little more than a partial formalisation of materials from Linnebo's paper.

\section{Methods}

The following formal analysis is conducted in a single logical system, a Higher Order Logic based on Church's formulation of the Simple Theory of Types\cite{church40}.
The formal treatment is prepared with the assistance of an interactive theorem proving tool.
This tool assists by syntax checking and type-checking specifications, by confirming that these specifications are conservative over the initial logical system, by facilitating the construction of detailed formal proofs and mechanically checking their correctness.
The tool also prepares listings of the resulting theories, which may be found in appendices \ref{t046a} and \ref{t046b} and facilitates the preparation of documents including the formal materials.

There is some additional complexity in undertaking strictly formal work in this manner, which is not entirely eliminated by the use of software support.
Feasibility depends on careful choice of methods (and problems) to keep complexity within bounds.
In the kind of exploratory investigation at hand, one simplification is to avoid reasoning about syntax.
This may be done by constructing interpretations of the target systems and reasoning about these interpretations in HOL.
In the resulting theorems the syntax of HOL (which is in some degree extendable) is used to express claims which correspond to the rules, axioms and theorems of the logical system or systems under investigation.
When proven they give good grounds for belief in the soundness of the logic under consideration, even though we have avoided formal treatment of its syntax.

This approach to reasoning in some logic of interest using a tool supporting a different logical system, is sometimes called \emph{shallow embedding} (by contrast with \emph{deep embedding} in which both syntax and semantics and the relationship between them are formally treated, supporting full formalisation of the metatheory).
An extended discussion of these methods is not within our present scope, but I will try to include a certain amount of further explanation as the document proceeds in the hope of making the technical detail as intelligible as practicable.

\subsection{Dependencies}

For a complete understanding of the details of the formal materials in this document it would strictly be necessary to refer to the definition of the language in which the specifications are written (\ProductHOL) and to the listings of the various theories in the context of which these theories have been developed.
I hope that the material will be intelligible to a reasonable degree without studying all this material, many readers will already be familiar with Church's formulation of the Simple Theory of Types \cite{church40} and will be familiar with the meanings of the usual logical connectives in that context.

\pagebreak

For the full detail the following documents may be consulted.

\begin{enumerate}
\item Church's formulation of STT: \cite{church40}.
\item The {\ProductHOL} language: informal description \cite{ds/fmu/ied/usr005}
\item The {\ProductHOL} language: formal specification \cite{ds/fmu/ied/spc001}
\item {\ProductHOL} theory listings: \cite{lemma1/hol/usr029} or \href{http://rbjones.com/rbjpub/pp/pptheories.html}{in HTML at RBJones.com}%
\footnote{http://rbjones.com/rbjpub/pp/pptheories.html}.
\item Other theories at RBJones.com: rbjmisc \cite{rbjt006}, t045 \cite{rbjt045}.
\item Complete documentation for {\Product} can be obtained from \href{http://www.lemma-one.com/ProofPower/doc/doc.html}{the {\Product} web pages}%
\footnote{http://www.lemma-one.com/ProofPower/doc/doc.html}.
\end{enumerate}

\section{Plural Quantification}

Since quantification in HOL is \emph{typed}, and the quantifiers therefore range over the elements of any chosen type, to interpret plural quantification we need a type of plurals, or better, a \emph{type-constructor}, which, given any type, will construct the type of plurals of values of its argument type. 

We therefore introduce in HOL just such a type constructor, and the polymorphic relationship `\emph{is one of}' ($⤕$) between arbitrary values and plurals.

=SML
open_theory "rbjmisc";
force_new_theory "⦏t046a⦎";
=TEX

\ignore{
=SML
force_new_pc ⦏"'t046a"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'t046a";
set_merge_pcs ["rbjmisc", "'t046a"];
set_flag ("pp_use_alias", true);
=TEX
}%ignore

\subsection{A Plurals Type-Constructor}

In order to be able to quantify over plurals, we introduce a new type constructor.

This can be done axiomatically, or conservatively (using definitions rather than arbitrary axioms).
A conservative extension is normally preferred, but this requires a full understanding of the requirements since once the type has been defined no further modifications can be made.
In this case we adopt a kind of compromise.

We explore the logic of plurals without settling the question of which non-empty extensions of any particular type do form plurals.
This will be achieved by introducing a loosely defined constant to determine this question, and then proving hypothetical results in the theory of plurals dependent on hypotheses about the properties of this constant, i.e. dependent upon various assumptions about which extensions are plurals.

I introduce a 1-ary type constructor for plurals.
It is not clear to me from Linnebo's paper whether this is the correct way to model his intentions.
Sometimes Linnebo talks as if plurals can be formed from absolutely everything, but if plurals exist, if we can quantify over plurals, then absolutely everything would include the plurals, and I see no sign in Linnebo that he intends this.
Instead we have a new type $S$ which may include both urelements and sets, and a type-constructor $'a\ PL$ which is the type of plurals of values of type $'a$.
It is not impossible that the plurals are also elements of $S$, but the type system prevents us from asking the question.

We do have quite a variety of kinds of set already available, but here we must start from scratch again.
It is clear that Linnebo is thinking in terms of a well-founded set theory with urelements.

The type constructors are introduced thus:

=SML
new_type("⦏PL⦎", 1);
new_type("⦏S⦎", 0);
=TEX

We then introduce some primitive constants for these types, without giving definitions.

=SML
new_const("⦏⋳⦎", ⓣ'a → ('a) PL → BOOL⌝);
declare_infix(240, "⋳");
new_const("⦏∈⋎s⦎", ⓣ S → S → BOOL⌝);
declare_infix(230, "∈⋎s");
declare_alias("∈", ⌜$∈⋎s⌝);
=TEX

We are now in a position to define various notions which Linnebo uses.

ⓈHOLCONST
│ ⦏FORM⦎: S PL × S → BOOL
├──────
│ ∀xx y⦁ FORM(xx, y) ⇔ ∀u⦁ u ⋳ xx ⇔ u ∈⋎s y
■

ⓈHOLCONST
│ ⦏COLLAPSE⦎: BOOL
├──────
│ COLLAPSE ⇔ ∀xx:S PL⦁ ∃y:S⦁ FORM(xx, y)
■

The principle of plural comprehension is that the extension of any formula is a plurality.
Linnebo does elsewhere require that pluralities be non-empty, but he does not incorporate this requirement into his principle of plural comprehension.
The following definition differs from Linnebo's, as our proceeding does generally, in being formulated in HOL rather than in some first order language.
So here we have a single principle which quantifies over properties, where Linnebo has a first order axiom scheme.

Note also that here {\it P\_Comp} is not an axiom.
It is the name of a boolean constant, which we will use as a hypothesis (on the left of sequents) in some of the theorems which we prove later. 

ⓈHOLCONST
│ ⦏P_Comp⦎: BOOL
├──────
│ P_Comp ⇔ ∀φ⦁ ∃xx:S PL⦁ ∀u:S⦁ u ⋳ xx ⇔ φ u
■

Linnebo then derives a contradiction, corresponding to which we have the theorem:

=GFT
⦏COLLAPSE_contradiction_thm⦎ =
	COLLAPSE, P_Comp ⊢ F
=TEX

Proofs will not be shown, they are all straightforward.

\ignore{
=SML
val FORM_def = get_spec ⌜FORM⌝;
val COLLAPSE_def = get_spec ⌜COLLAPSE⌝;
val P_Comp_def = get_spec ⌜P_Comp⌝;

set_goal([⌜COLLAPSE⌝, ⌜P_Comp⌝], ⌜F⌝);
a (REPEAT (POP_ASM_T ante_tac));
a (rewrite_tac [COLLAPSE_def, P_Comp_def, FORM_def]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 1 ⌜λv⦁ ¬ v ∈⋎s v⌝);
a (∃_tac ⌜xx⌝ THEN asm_rewrite_tac[]);
a (REPEAT strip_tac);
a (∃_tac ⌜y⌝ THEN contr_tac);
val COLLAPSE_contradiction_thm = save_pop_thm "COLLAPSE_contradiction_thm";
=TEX
}%ignore

Linnebo observes that this is normally taken as a refutation of COLLAPSE, but proposes to resolve the contradiction by some other means.

To do this he needs to scrutinise carefully all the assumptions which participate in the derivation of the contradiction.
Doing the proof formall⬜y gives us a strong basis for considering this matter, for it is clearer what the logical context of the proof is.

This has involved some assumptions about the types of pluralities and sets which are not explicit in Linnebo (who is not working in a context in which these questions arise).
We have also formulated a second order principle of plural abstraction, whereas Linnebo's is an axiom scheme.

Apart from considering \emph{P\_Comp} as a suspect, Linnebo considers that he has assumed that one can quantify over absolutely everything, and questions this assumption.
This is implicit in our formalisation if we interpret S as \emph{absolutely everything}, though it is not apparent that the proof depends on this.

Linnebo approaches a distinction between COLLAPSE and full comprehension by referring to the concept used in comprehension as \emph{intensional}, by contrast with the extensional nature of the plurality used to determine a set in COLLAPSE.
This doesn't work very well here, because COLLAPSE is formulated using an extensional notion of concept (a propositional function in an extensional higher order logic), and still suffices to derive the contradiction.
The point Linnebo is driving at is that comprehension does not give a properly iterative process of building the universe of sets, because a set introduced at some point in an imagined iterative process has one extension before we add it, but once added it (and other new sets) become candidates for membership in that same set, so the extension may therefore change.
He seems here to be wanting to treat the pluralities as rigid designators of extensions, even if they are defined by plural comprehension, so that the question of whether a set introduced by COLLAPSE is a member of itself does not arise.
However, this perspective is not a legitimate interpretation of the theory as we have formulated it here.
If we want our universe to be the result of some iterative process, we need a new approach to the formal modelling.

\ignore{
=SML
add_pc_thms "'t046a" [];
set_merge_pcs ["rbjmisc", "'t046a"];
=TEX
}%ignore


\ignore{
=SML
commit_pc "'t046a";

force_new_pc "⦏t046a⦎";
merge_pcs ["rbjmisc", "'t046a"] "t046a";
commit_pc "t046a";

force_new_pc "⦏t046a1⦎";
merge_pcs ["rbjmisc1", "'t046a"] "t046a1";
commit_pc "t046a1";
=TEX
}%ignore


\section{Modalised Set Theory}

\subsection{Alternatives to COLLAPSE}

Linnebo devotes a section of his paper to a critique of alternatives to COLLAPSE.
I pass over this to concentrate on his positive proposals.

\subsection{Restoring Consistency}


=SML
open_theory "t046a";
force_new_theory "⦏t046b⦎";
new_parent "t045";
=TEX

\ignore{
=SML
force_new_pc ⦏"'t046b"⦎;
merge_pcs ["'savedthm_cs_∃_proof"] "'t046b";
set_merge_pcs ["t045", "'t046b"];
set_flag ("pp_use_alias", true);
=TEX
}%ignore


We now come to Linnebo's proposals for obtaining a consistent system incorporating COLLAPSE.

This is based upon an idea by Yablo that determinacy of the pool of candidates is a pre-requisite for the determinacy of a set determined by some condition $φ$ (this is good in the present context because it replaces the idea that the problem is with \emph{intensionality} of the condition, which doesn't work well in our present context).

This translates into the requirement that the condition determines a set only if it is applied at a specific stage in an iterative process of forming the universe of sets, and the resulting set appears at the next stage.
The extension of the set will then correspond to those elements prior to the determination of the set which satisfy the condition.
Not every element of the complete universe (not \emph{absolutely everything}) is a candidate, and in particular the set itself is not a candidate for membership.
We may say parenthetically, that what Linnebo has done here is something like adopting separation instead of comprehension.
Note however, that Linnebo does not embrace the idea that the heirarchy of sets ever can be completed (and nor do I).
In the present context, interpretations of our theory will assign some set to the type $S$, which will (when we consider further constraints below) correspond to some stage in the formation at which this interminable process is arbitrarily brought to a halt.
The results we obtain relate not to the completion, nor to any particular stage short of completion, but to some unspecified stage short of completion, and hence to all unspecified stages (subject to some constraints) short of completion.

Linnebo proposes to spell out the idea using modal vocabulary to talk about stages.
This is rather different to and more subtle than the initial result of our formalisation as relating to arbitrary stages, and so I now examine how such a modal notation can be used.

In this modal notion, a \emph{possible world} is a stage in the formation of the ``universe'' $S$.
Let us ignore the fact that $S$ itself cannot be the whole, for the present, and imagine that it is.
Such a stage will be a subset of the type S, and thefore will in our logical system be a value of type $S\ SET$.
The collection of possible worlds will then be a set of such sets.
We will call them \emph{Stages}.

We introduce this as a loosely defined constant.
The only constraint we apply to it is to ensure that this is a non-empty directed set (though it may be necessary to beef this up later).

\ignore{
=SML
set_goal([], ⌜∃Stages:(S SET) SET⦁ (∃x⦁ x ∈ Stages) ∧ ∀x y⦁ x ∈ Stages ∧ y ∈ Stages ⇒ ∃z⦁ z ∈ Stages ∧ x ⊆ z ∧ y ⊆ z⌝);
a (∃_tac ⌜{x:S SET | T}⌝ THEN REPEAT strip_tac);
a (∃_tac ⌜ThisStage:S SET⌝ THEN rewrite_tac[]);
a (∃_tac ⌜x ∪ y⌝ THEN PC_T1 "hol1" prove_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Stages⦎: (S SET) SET
├──────
│	(∃x⦁ x ∈ Stages)
│  ∧	∀x y⦁ x ∈ Stages ∧ y ∈ Stages ⇒ ∃z⦁ z ∈ Stages ∧ x ⊆ z ∧ y ⊆ z
■

We note here the elementary consequence of directedness that every member of a stage is reachable from any stage.

=GFT
⦏Stages_fc_thm⦎ =
	⊢ ∀ x y⦁ x ∈ Stages ∧ y ∈ Stages ⇒ ∃z⦁ z ∈ Stages ∧ x ⊆ z ∧ y ⊆ z

⦏set_reachability_thm⦎ = 
	⊢ ∀ s1 s2 x⦁ s1 ∈ Stages ∧ s2 ∈ Stages ∧ x ∈ s2
		⇒ (∃ s3⦁ s3 ∈ Stages ∧ x ∈ s3 ∧ s1 ⊆ s3)
=TEX

\ignore{
=SML
val Stages_def = get_spec ⌜Stages⌝;

set_goal([], ⌜∀x y⦁ x ∈ Stages ∧ y ∈ Stages ⇒ ∃z⦁ z ∈ Stages ∧ x ⊆ z ∧ y ⊆ z⌝);
a (rewrite_tac [Stages_def]);
val Stages_fc_thm = save_pop_thm "Stages_fc_thm";

set_goal([], ⌜∀(s1:S SET) (s2:S SET) x⦁ s1 ∈ Stages ∧ s2 ∈ Stages ∧ x ∈ s2 ⇒ ∃s3:S SET⦁ s3 ∈ Stages ∧ x ∈ s3 ∧ s1 ⊆ s3⌝);
a (REPEAT strip_tac);
a (all_fc_tac [Stages_fc_thm]);
a (∃_tac ⌜z'⌝ THEN asm_rewrite_tac[]);
a (PC_T1 "hol1" asm_prove_tac[]); 
val set_reachability_thm = save_pop_thm "set_reachability_thm";
=TEX
}%ignore


We could then define the relevant notion of accessibility between these stages, but since this is set inclusion (or its converse) which is already defined we will use that directly (A is accessible from B if A is a stage subsequent to B and hence $⌜B\ ⊆\ A⌝$).

The expression of modal claims in our logic requires a recasting of all the logical vocabulary.
The definitions extant in HOL treat propositions as values of type $ⓣBOOL⌝$, but in the modal logic they will have to be considered as values of type $ⓣS\ SET\ →\ BOOL⌝$, i.e. a BOOLean valued function over the relevant possibilities, which in this case are stages in the iterative cumulation of sets.

From here on in the names used for constants will usually be subscripted with `m' to distinguish them from previous versions, but will be aliased back to the non-subscripted name so that the subscript may be omitted if no ambiguity arises (usually the type-checker can resolve any ambiguity).
In the case of the universal and existential quantifiers we need different definitions according to whether we are quantifying over sets or plurals, and in these cases the subscripts `s' and `p' will be used as appropriate.

=SML
declare_type_abbrev("PROP⋎m", [], ⓣS SET → BOOL⌝);
=TEX

The modal operators are defined as follows:

ⓈHOLCONST
│ ⦏◇⋎m⦎ : PROP⋎m → PROP⋎m
├──────
│ ∀s⦁ ◇⋎m s = λw⦁ ∀v⦁ v ∈ Stages ∧ w ⊆ v ⇒ s v
■

ⓈHOLCONST
│ ⦏⬜⋎m⦎ : PROP⋎m → PROP⋎m
├──────
│ ∀s⦁⬜⋎m s = ¬ ◇⋎m (¬ s)
■

So that we need not use the subscript $⋎m$ unless ambiguity might otherwise arise, we introduce the un-subscripted modal operators as aliases:

=SML
declare_alias("◇", ⌜◇⋎m⌝);
declare_alias("⬜", ⌜⬜⋎m⌝);
=IGN
declare_prefix(5, "⬜");
declare_prefix(5, "⬜⋎m");
declare_prefix(5, "◇");
declare_prefix(5, "◇⋎m");
=TEX

Since modal propositions are not of type $ⓣBOOL⌝$ we need a way of asserting them, for which we use the symbol $⊨$, which should be read as asserting `truth'.
Though `truth' simpliciter in a modal logic should perhaps be construed as truth in ``this world'', and since worlds are stages we use the name \emph{ThisStage} and introduce this as a new constant.
Linnebo says nothing about this, so nor do we, so we know nothing from this loose `definition' about \emph{ThisStage} other than that it is a \emph{Stage} (and we do already know that there is one, so the definition is conservative).

\ignore{
=SML
set_goal([], ⌜∃ThisStage⦁ ThisStage ∈ Stages⌝);
a (strip_asm_tac (get_spec ⌜Stages⌝));
a (∃_tac ⌜x⌝ THEN strip_tac);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore


ⓈHOLCONST
│ $⦏ThisStage⦎ : S SET
├──────
│ ThisStage ∈ Stages
■

ⓈHOLCONST
│ $⦏⊨⋎m⦎ : PROP⋎m → BOOL
├──────
│ ∀p⦁ ⊨⋎m p ⇔ p ThisStage
■

=SML
declare_alias("⊨", ⌜⊨⋎m⌝);
declare_prefix(5, "⊨⋎m");
=TEX

=GFT
⦏⬜◇⋎m_thm⦎ =	⊢ ∀ s p⦁ (◇⋎m p s ⇔ (∀ s2⦁ s ⊆ s2 ⇒ p s2))
		∧ (⬜⋎m p s ⇔ (∃ s2⦁ s ⊆ s2 ∧ p s2))
=TEX

\ignore{
=SML
val ThisStage_def = get_spec ⌜ThisStage⌝;
val ◇⋎m_def = get_spec ⌜$◇⋎m⌝;
val ⬜⋎m_def = get_spec ⌜$⬜⋎m⌝;

set_goal([], ⌜∀(s:S SET) p⦁ ((◇⋎m p) s ⇔ ∀s2⦁ s2 ∈ Stages ∧ s ⊆ s2 ⇒  p s2)
		∧	((⬜⋎m p) s ⇔ ∃s2⦁ s2 ∈ Stages ∧ s ⊆ s2 ∧  p s2)⌝);
a (rewrite_tac [⬜⋎m_def, ◇⋎m_def, l_defs]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜v⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜s2⌝ THEN asm_rewrite_tac[]);
val ⬜◇⋎m_thm = save_pop_thm "⬜◇⋎m_thm";

add_pc_thms "'t046b" [⬜◇⋎m_thm];
add_rw_thms [get_spec ⌜ThisStage⌝] "'t046b";
add_sc_thms [get_spec ⌜ThisStage⌝] "'t046b";
set_merge_pcs ["t045", "'t046b"];
=TEX
}%ignore

We can now \emph{prove} as theorems the propositions which would normally be taken as axioms for this kind of modal logic.

=GFT
⦏distrib⋎m_thm⦎ =	⊢ ⊨ ◇ (A ⇒ B) ⇒ ◇ A ⇒ ◇ B
⦏D⋎m_thm⦎ =		⊢ ⊨ ◇ A ⇒ ⬜ A
⦏M⋎m_thm⦎ =		⊢ ⊨ ◇ A ⇒ A
⦏A4⋎m_thm⦎ =		⊢ ⊨ ◇ A ⇒ ◇ (◇ A)
⦏◇M⋎m_thm⦎ =		⊢ ⊨ ◇ (◇ A ⇒ A)
⦏C4⋎m_thm⦎ =		⊢ ⊨ ◇ (◇ A) ⇒ ◇ A
⦏C⋎m_thm⦎ =		⊢ ⊨ ⬜ (◇ A) ⇒ ◇ (⬜ A)
=TEX

=IGN
⦏B⋎m_thm⦎ =		⊢ ⊨ A ⇒ ◇ (⬜ A)
⦏A5⋎m_thm⦎ =		⊢ ⊨ ⬜ A ⇒ ◇ (⬜ A)
=TEX

\ignore{
=SML
set_goal([], ⌜⊨⋎m ◇(A ⇒ B) ⇒ ◇ A ⇒ ◇ B⌝);
a (rewrite_tac [get_spec ⌜$⊨⋎m⌝] THEN REPEAT strip_tac THEN REPEAT (all_asm_fc_tac[]));
val distrib⋎m_thm = save_pop_thm "distrib⋎m_thm";

set_goal([], ⌜⊨⋎m (◇ A) ⇒ ⬜ A⌝);
a (rewrite_tac [get_spec ⌜$⊨⋎m⌝] THEN prove_tac[]);
a (∃_tac ⌜ThisStage⌝);
a (spec_nth_asm_tac 1 ⌜ThisStage⌝ THEN REPEAT strip_tac);
a (asm_prove_tac[]);
val D⋎m_thm = save_pop_thm "D⋎m_thm";

set_goal([], ⌜⊨⋎m (◇ A) ⇒ A⌝);
a (rewrite_tac [get_spec ⌜$⊨⋎m⌝] THEN prove_tac[]);
a (spec_nth_asm_tac 1 ⌜ThisStage⌝ THEN REPEAT strip_tac);
a (asm_prove_tac[]);
val M⋎m_thm = save_pop_thm "M⋎m_thm";

set_goal([], ⌜⊨⋎m (◇ A) ⇒ (◇ (◇ A))⌝);
a (rewrite_tac [get_spec ⌜$⊨⋎m⌝] THEN prove_tac[]);
a (lemma_tac ⌜ThisStage ⊆ s2'⌝ THEN1 all_asm_fc_tac [⊆_trans_thm]);
a (all_asm_fc_tac[]);
val A4⋎m_thm = save_pop_thm "A4⋎m_thm";

=IGN
set_goal([], ⌜⊨ (⬜ A) ⇒ (◇ (⬜ A))⌝);
a (rewrite_tac [get_spec ⌜$⊨⌝] THEN prove_tac[]);
val A5_thm = save_pop_thm "A5_thm";
=SML

set_goal([], ⌜⊨⋎m ◇((◇ A) ⇒ A)⌝);
a (rewrite_tac [get_spec ⌜$⊨⋎m⌝] THEN prove_tac[]);
a (spec_nth_asm_tac 1 ⌜s2⌝);
val ◇M⋎m_thm = save_pop_thm "◇M⋎m_thm";

set_goal([], ⌜⊨⋎m (◇ (◇ A)) ⇒ (◇ A)⌝);
a (rewrite_tac [get_spec ⌜$⊨⋎m⌝] THEN prove_tac[]);
a (asm_fc_tac[]);
a (spec_nth_asm_tac 1 ⌜s2⌝);
val C4⋎m_thm = save_pop_thm "C4⋎m_thm";

set_goal([], ⌜⊨⋎m (⬜ (◇ A)) ⇒ (◇ (⬜ A))⌝);
a (rewrite_tac [get_spec ⌜$⊨⋎m⌝] THEN prove_tac[]);
a (all_fc_tac [Stages_fc_thm]);
a (∃_tac ⌜z'⌝ THEN asm_fc_tac [] THEN REPEAT strip_tac);
val C⋎m_thm = save_pop_thm "C⋎m_thm";
=TEX
}%ignore

The quantifiers, or at least those over sets, are now expected to be modally sensitive.
They quantify over a particular stage in the formation of the cumulative hierarchy.

ⓈHOLCONST
│ ⦏∀⋎s⦎:(S → PROP⋎m) → PROP⋎m
├──────
│  ∀f⦁ ∀⋎s f = λs⦁ ∀x⦁ x ∈ s ⇒ f x s
■

=SML
declare_alias ("∀", ⌜∀⋎s⌝);
declare_binder "∀⋎s";
=TEX

ⓈHOLCONST
│ ⦏∃⋎s⦎:(S → PROP⋎m) → PROP⋎m
├──────
│  ∀f:S → PROP⋎m⦁ ∃⋎s f = λs:S SET⦁ ∃x:S⦁ x ∈ s ∧ f x s
■

=SML
declare_alias ("∃", ⌜∃⋎s⌝);
declare_binder "∃⋎s";
=TEX

Declaring these as binders has the effect that when applied to a lambda-expression the lambda is to be omitted, giving the usual syntax for quantifiers.
Sometimes, as in the following theorems, we want to use the quantifier without binding a variable, in which case its status as a binder can be suspended for a particular occurrence by prefixing the quantifier with a dollar sign.

=GFT
⦏∃⋎s_thm⦎ = ⊢ ∀ f s⦁ $∃ f s ⇔ (∃ x⦁ x ∈ s ∧ f x s)
⦏∀⋎s_thm⦎ = ⊢ ∀ f s⦁ $∀ f s ⇔ (∀ x⦁ x ∈ s ⇒ f x s)
=TEX

\ignore{
=SML
val ∀⋎s_def = get_spec ⌜$∀⋎s⌝;
set_goal([], ⌜∀f s⦁ $∀⋎s f s = ∀x⦁ x ∈ s ⇒ f x s⌝);
a (REPEAT ∀_tac THEN rewrite_tac [∀⋎s_def]);
val ∀⋎s_thm = save_pop_thm "∀⋎s_thm";

val ∃⋎s_def = get_spec ⌜$∃⋎s⌝;
set_goal([], ⌜∀f s⦁ $∃⋎s f s = ∃x⦁ x ∈ s ∧ f x s⌝);
a (REPEAT ∀_tac THEN rewrite_tac [∃⋎s_def]);
val ∃⋎s_thm = save_pop_thm "∃⋎s_thm";

add_pc_thms "'t046b" [∀⋎s_thm, ∃⋎s_thm];
set_merge_pcs ["t045", "'t046b"];
=TEX
}%ignore

We need new quantifiers to quantify over pluralities in a modal context.
I have made plural quantification also sensitive to the stage, but in this case the constraint is not membership of the stage but extensional inclusion in it.

ⓈHOLCONST
│ ⦏∀⋎p⦎:(S PL → PROP⋎m) → PROP⋎m
├──────
│  ∀f⦁ ∀⋎p f = λs⦁ ∀xx⦁ (∀z⦁ z ⋳ xx ⇒ z ∈ s) ⇒ f xx s
■

=SML
declare_alias ("∀", ⌜∀⋎p⌝);
declare_binder "∀⋎p";
=TEX

ⓈHOLCONST
│ ⦏∃⋎p⦎:(S PL → PROP⋎m) → PROP⋎m
├──────
│  ∀f⦁ ∃⋎p f = λs⦁ ∃xx:S PL⦁ (∀z⦁ z ⋳ xx ⇒ z ∈ s) ∧ f xx s
■

=SML
declare_alias ("∃", ⌜∃⋎p⌝);
declare_binder "∃⋎p";
=TEX

=GFT
⦏∃⋎p_thm⦎ = ⊢ ∀ f s⦁ $∃⋎p f s ⇔ (∃ xx⦁ (∀z⦁ z ⋳ xx ⇒ z ∈ s) ∧ f xx s)
⦏∀⋎p_thm⦎ = ⊢ ∀ f s⦁ $∀⋎p f s ⇔ (∀ xx⦁ (∀z⦁ z ⋳ xx ⇒ z ∈ s) ⇒ f xx s)
=TEX

\ignore{
=SML
val ∀⋎p_def = get_spec ⌜$∀⋎p⌝;
set_goal([], ⌜∀f s⦁ $∀⋎p f s = ∀xx⦁ (∀z⦁ z ⋳ xx ⇒ z ∈ s) ⇒ f xx s⌝);
a (REPEAT ∀_tac THEN rewrite_tac [∀⋎p_def]);
val ∀⋎p_thm = save_pop_thm "∀⋎p_thm";

val ∃⋎p_def = get_spec ⌜$∃⋎p⌝;
set_goal([], ⌜∀f s⦁ $∃⋎p f s = ∃xx⦁ (∀z⦁ z ⋳ xx ⇒ z ∈ s) ∧ f xx s⌝);
a (REPEAT ∀_tac THEN rewrite_tac [∃⋎p_def]);
val ∃⋎p_thm = save_pop_thm "∃⋎p_thm";

add_pc_thms "'t046b" [∀⋎p_thm, ∃⋎p_thm];
set_merge_pcs ["t045", "'t046b"];
=TEX
}%ignore

We are now able to demonstrate the `converse Barcan' formula.
The Barcan formula itself fails, because it infers from possible existence to actual existence which would only be possible if no stage actually added any extra sets.

=IGN
⦏BF⋎m_thm⦎ =	⊢ ⊨⋎m ⬜ (∃ x⦁ A x) ⇒ (∃⋎s x⦁ ⬜ A x)
=GFT
⦏CBF⋎m_thm⦎ =	⊢ ⊨⋎m (∃ x⦁ ⬜ A x) ⇒ ⬜ (∃⋎s x⦁ A x)
=TEX

\ignore{
=IGN
stop;
set_goal([], ⌜⊨⋎m (⬜ ((∃ x⦁ A x))) ⇒ ((∃ x⦁ (⬜ (A x))))⌝);
a (rewrite_tac [get_spec ⌜$⊨⋎m⌝] THEN prove_tac[]);
val BF⋎m_thm = save_pop_thm "BF⋎m_thm";

=SML
set_goal([], ⌜⊨⋎m ((∃ x:S⦁ (⬜ (A x)))) ⇒ (⬜ ((∃ x:S⦁ A x)))⌝);
a (rewrite_tac [get_spec ⌜$⊨⋎m⌝] THEN prove_tac[]);
a (∃_tac ⌜s2⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜x⌝ THEN PC_T1 "hol1" asm_prove_tac[]);
val CBF⋎m_thm = save_pop_thm "CBF⋎m_thm";
=TEX
}%ignore

The notion of plurality has not really changed as we moved to a modal set theory, but our notion of proposition has changed and so we need to replicate the definitions of the plural operations to deliver the right kinds of proposition.

We didn't actually have a `definition' of plural membership, just a constant about which we made assumptions as needed.
Here we lift that constant to deliver a modal proposition which does the same thing at every stage.
This reflects the rigidity of the values we quantify over, both sets an plurals.

We need a similar constant at a different type.

=SML
declare_infix(240, "⋲");
=TEX

ⓈHOLCONST
│ $⦏⋲⦎: 'a → ('a) PL → PROP⋎m
├──────
│ ∀x yy s⦁ (x ⋲ yy) s ⇔ x ⋳ yy
■

=SML
declare_alias("⋳", ⌜$⋲⌝);
=TEX

On my first pass I defined the modal set membership taking into account of the stage parameter so that it is false if the value of the variable does not exist.
Later, seeing Linnebo's appendix in which he affirms the necessity of true membership claims this was thrown into doubt.
It turns out that the definition of membership in which membership is false if the set does not appear in the current stage is compatible with the necessity of true membership statements but not with the necessity of false ones, which Linnebo requires, so I have revised the definition accordingly.

=SML
declare_infix(240, "∈⋎m");
=TEX

ⓈHOLCONST
│ $⦏∈⋎m⦎: S → S → PROP⋎m
├──────
│ ∀x y s⦁ (x ∈⋎m y) s ⇔ x ∈⋎s y
■

=SML
declare_alias("∈", ⌜$∈⋎m⌝);
=TEX

We now restate the two contradictory principles using modal language (i.e. using quantifiers suitable for use in modal contexts, but not modal operators).

ⓈHOLCONST
│ ⦏FORM⋎m⦎: S PL × S → PROP⋎m
├──────
│ ∀xx y⦁ FORM⋎m(xx, y) = ∀ u⦁ u ⋲ xx ⇔ u ∈⋎m y
■

=GFT
⦏FORM⋎m_thm⦎ = ⊢ ∀ xx y s⦁ FORM⋎m (xx, y) s ⇔ (∀ x⦁ x ∈ s ⇒ ((x ⋳ xx) s ⇔ (x ∈ y) s))
=TEX

\ignore{
=SML
val FORM⋎m_def = get_spec ⌜$FORM⋎m⌝;

set_goal([], ⌜∀xx y s⦁ FORM⋎m(xx, y) s ⇔ ∀x⦁ x ∈ s ⇒ ((x ⋳ xx) s ⇔ (x ∈ y) s)⌝);
a (rewrite_tac[FORM⋎m_def]);
val FORM⋎m_thm = pop_thm ();

(* add_pc_thms "'t046b" [get_spec ⌜$⋲⌝, get_spec ⌜$∈⋎m⌝, FORM⋎m_thm]; *)
add_pc_thms "'t046b" [get_spec ⌜$⋲⌝, get_spec ⌜$∈⋎m⌝, FORM⋎m_thm];
set_merge_pcs ["t045", "'t046b"];
=TEX
}%ignore


ⓈHOLCONST
│ ⦏COLLAPSE⋎m⦎: BOOL
├──────
│ COLLAPSE⋎m ⇔ ⊨⋎m ∀⋎p xx:S PL⦁ ∃ y:S⦁ FORM⋎m(xx, y)
■


We can now state the principle of plural comprehension:

ⓈHOLCONST
│ ⦏P_Comp⋎m⦎: BOOL
├──────
│ P_Comp⋎m ⇔ ∀φ⦁ ⊨⋎m ∃⋎p xx:S PL⦁ ∀ u:S⦁ u ⋲ xx ⇔ φ u
■

Since there are no modal operators, these principles speak only of the stage which is in context globally, of which we know nothing, except what the principles tell is (if they are assumed).

These two principles, under this new interpretation, remain contradictory:

=GFT
⦏COLLAPSE_contradiction_thm2⦎ =
	COLLAPSE⋎m, P_Comp⋎m ⊢ F
=TEX

It is accidental in the previous version of this that the domain of sets is a type and hence cannot be empty.
In this version the domain of sets is a class (or may best be thought of as a class, it has type ⓣS\ SET⌝ in which S is the type of sets for present purposes, and SET is similar to the higher type in second order logic).
We can therefore establish its non-emptyness here only by using the two principles at hand, and it is fortuitous that the principle of plural comprehension does not insist that plurals are non-empty.
If it did the two principles as formalised above would not be contradicatory.

\ignore{
=SML
val ⊨⋎m_def = get_spec ⌜$⊨⋎m⌝;
val COLLAPSE⋎m_def = get_spec ⌜COLLAPSE⋎m⌝;
val P_Comp⋎m_def = get_spec ⌜P_Comp⋎m⌝;

set_goal([⌜COLLAPSE⋎m⌝, ⌜P_Comp⋎m⌝], ⌜F⌝);
a (REPEAT (POP_ASM_T ante_tac) THEN pure_rewrite_tac [⊨⋎m_def, COLLAPSE⋎m_def, P_Comp⋎m_def]
	THEN contr_tac);
a (SPEC_NTH_ASM_T 2 ⌜λx:S⦁ λs:S SET⦁F⌝ (strip_asm_tac o (rewrite_rule[])));
a (SPEC_NTH_ASM_T 4 ⌜λx:S⦁ ¬ x ∈⋎m x⌝ (strip_asm_tac o (rewrite_rule[])));
a (SPEC_NTH_ASM_T 5 ⌜xx'⌝ (strip_asm_tac o (rewrite_rule[])));
(* *** Goal "1" *** *)
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 5 ⌜x⌝);
a (spec_nth_asm_tac 2 ⌜x⌝);
(* *** Goal "2.1" *** *)
a (spec_nth_asm_tac 6 ⌜x⌝);
(* *** Goal "2.2" *** *)
a (spec_nth_asm_tac 6 ⌜x⌝);
val COLLAPSE_contradiction_thm2 = save_pop_thm "COLLAPSE_contradiction_thm2";
=TEX
}%ignore

We now define the two properly modalised versions of plural comprehension and collapse (as given by Linnebo).

ⓈHOLCONST
│ ⦏COLLAPSE⋏⬜⦎: BOOL
├──────
│ COLLAPSE⋏⬜ ⇔ ⊨⋎m ◇∀⋎p xx⦁ ⬜∃⋎s y⦁ FORM⋎m(xx, y)
■

ⓈHOLCONST
│ ⦏P_Comp⋏⬜⦎: BOOL
├──────
│ P_Comp⋏⬜ ⇔ ∀φ⦁ ⊨⋎m ⬜∃ xx⦁ ◇∀⋎s u⦁ u ⋲ xx ⇔ φ u
■

Once again the, a contradiction is derivable from these two principles.

=GFT
⦏COLLAPSE_contradiction_thm3⦎ = COLLAPSE⋏⬜, P_Comp⋏⬜ ⊢ F
=TEX

\ignore{
=SML
val COLLAPSE⋏⬜_def = get_spec ⌜COLLAPSE⋏⬜⌝;
val P_Comp⋏⬜_def = get_spec ⌜P_Comp⋏⬜⌝;

set_goal([⌜COLLAPSE⋏⬜⌝, ⌜P_Comp⋏⬜⌝], ⌜F⌝);
a (REPEAT (POP_ASM_T ante_tac) THEN pure_rewrite_tac [⊨⋎m_def, COLLAPSE⋏⬜_def, P_Comp⋏⬜_def]
	THEN contr_tac);
a (SPEC_NTH_ASM_T 2 ⌜λx:S⦁ ¬ x ∈⋎m x⌝ (strip_asm_tac o (rewrite_rule[])));
a (ALL_ASM_FC_T (MAP_EVERY (strip_asm_tac o (rewrite_rule[])))[]);
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 7 ⌜s2'⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 7 ⌜s2'⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
val COLLAPSE_contradiction_thm3 = save_pop_thm "COLLAPSE_contradiction_thm3";
=TEX
}%ignore

Strangely, though taking this contradiction as establishing the need to weaken plural comprehension, he does not offer a weakened version which is compatible with \emph{COLLAPSE}.

One obvious `solution' is simply to restrict plural comprehension to some stage in the formation of sets, thus in effect downgrading it to separation.

ⓈHOLCONST
│ ⦏P_Comp⋎w⋏⬜⦎: BOOL
├──────
│ P_Comp⋎w⋏⬜ ⇔ ∀φ⦁ ⊨⋎m ⬜∃ xx⦁ ∀⋎s u⦁ u ⋲ xx ⇔ φ u
■

I don't have the means in the present context to establish the consistency of this weakened comprehension with \emph{COLLAPSE} thought that does seem intuitively plausible.

\section{Logical Properties of the Modalised Quantifiers}

This section addresses the material under the above heading in Linnebo's Appendix.
Some of this material has already emerged as a result of our method of introducing the modal vocabulary, but the main theses of this appendix are metatheoretic and explicitly syntactic in character.
Since we do not have here a formalisation of the syntax of the system, these theses cannot be formalised.
We could formalise the syntax in order to be able to state them, but the cost of doing so would probably not justify the return.
Instead we prove a variety of purely semantic claims which are closely related to the results given by Linnebo.

I believe that Linnebo's prohibition of instantiation of plural quantifiers with constants is unnecessary in our treatment.
He seems by this means to wish to prohibit instantiation of plural quantifiers with concepts such as \emph{ordinal}, since it is not necessarily the case that the entire extension of a concept will correspond to a plural, once P-Comp has been weakened as necessary for it to be compatible with COLLAPSE.

In our treatment, the HOL type system supplies the necessary constraint.
We could instantiate with plural constants, if we had any (and we could have some).
But we cannot instantiate with a concept, because concepts do not have the same \emph{type} as plurals.

The next matter considered by Linnebo is the correspondence of his system with the modal logic S4.2, which we have already shown and arises from the definition we have give for the \emph{Stage}s, which are our ``possible worlds''.

Then we come to the necessity of equality and membership assertions and their negations, three of which Linnebo asserts as axioms.

First we must define equality, inequality and non-membership suitable for use in these modal contexts, i.e. which deliver a modal proposition rather than a BOOL value.

=SML
declare_infix(240, "=⋎m");
declare_infix(240, "≠⋎m");
declare_infix(240, "∉⋎m");
=TEX

ⓈHOLCONST
│ $⦏=⋎m⦎: S → S → PROP⋎m
├──────
│ ∀x y s⦁ (x =⋎m y) s ⇔ x = y
■

ⓈHOLCONST
│ $⦏≠⋎m⦎: S → S → PROP⋎m
├──────
│ ∀x y⦁ x ≠⋎m y = ¬ x =⋎m y
■

ⓈHOLCONST
│ $∉⋎m: S → S → PROP⋎m
├──────
│ ∀x y⦁ x ∉⋎m y = ¬ x ∈⋎m y
■

The four required results (of which the last three are asserted by Linnebo as axioms) may then be proven, resulting in the following theorems:

=GFT
⦏eq∈⋎m_◇_thm⦎ = 	⊢ ⊨ x =⋎m y ⇒ ◇ (x =⋎m y)
⦏≠∈⋎m_◇_thm⦎ = 	⊢ ⊨ x ≠⋎m y ⇒ ◇ (x ≠⋎m y)
⦏∈⋎m_◇_thm⦎ =		⊢ ⊨ x ∈⋎m y ⇒ ◇ (x ∈⋎m y)
∉⋎m_◇_thm =		⊢ ⊨ x ∉⋎m y ⇒ ◇ (x ∉⋎m y)
=TEX

\ignore{
=SML
val eq⋎m_def = get_spec ⌜$=⋎m⌝;
val ≠⋎m_def = get_spec ⌜$≠⋎m⌝;
val ∈⋎m_def = get_spec ⌜$∈⋎m⌝;
val ∉⋎m_def = get_spec ⌜$∉⋎m⌝;

set_goal([], ⌜⊨⋎m x =⋎m y ⇒ ◇ (x =⋎m y)⌝);
a (rewrite_tac[⊨⋎m_def, eq⋎m_def] THEN REPEAT strip_tac THEN asm_rewrite_tac[]);
val eq∈⋎m_◇_thm = save_pop_thm "eq⋎m_◇_thm";

set_goal([], ⌜⊨⋎m x ≠⋎m y ⇒ ◇ (x ≠⋎m y)⌝);
a (rewrite_tac[⊨⋎m_def, ≠⋎m_def, eq⋎m_def] THEN REPEAT strip_tac);
val ≠⋎m_◇_thm = save_pop_thm "≠⋎m_◇_thm";

set_goal([], ⌜⊨⋎m x ∈⋎m y ⇒ ◇ (x ∈⋎m y)⌝);
a (rewrite_tac[⊨⋎m_def, ∈⋎m_def, sets_ext_clauses] THEN REPEAT strip_tac);
val ∈⋎m_◇_thm = save_pop_thm "∈⋎m_◇_thm";

set_goal([], ⌜⊨⋎m x ∉⋎m y ⇒ ◇ (x ∉⋎m y)⌝);
a (rewrite_tac[⊨⋎m_def, ∉⋎m_def, ∈⋎m_def] THEN REPEAT strip_tac);
val ∉⋎m_◇_thm = save_pop_thm "∉⋎m_◇_thm";

set_goal([], ⌜⊨⋎m⬜ (x =⋎m y) ⇒ ◇ (x =⋎m y)⌝);
a (rewrite_tac[⊨⋎m_def, eq⋎m_def] THEN REPEAT strip_tac);
val ⬜◇∉⋎m_◇_thm = save_pop_thm "⬜◇∉⋎m_◇_thm";
=TEX
}%ignore

Now we consider Linnebo's \emph{Lemma1}.
This is needed by Linnebo to prove his \emph{Theorem 1}, instead of which we will attempt to demonstrate a corresponding purely semantic claim, so we will not need \emph{Lemnma 1} as it is given by Linnebo.
However, by way of checking that our definitions are consistent with Linnebo's system the following results, corresponding to steps in Linnebo's proof, have been proven.

=GFT
⦏⬜◇eq⋎m_thm⦎ =
	⊢ ⊨⬜ (x =⋎m y) ⇒ ◇ (x =⋎m y)

⦏⬜◇∈⋎m_thm⦎ =
	⊢ ⊨⬜ (x ∈ y) ⇒ ◇ (x ∈ y)

⦏⬜◇¬_thm⦎ = ⊨⬜ φ ⇒ ◇ φ
	⊢ ⊨⬜ (¬ φ) ⇒ ◇ (¬ φ)

⦏⬜◇∧_thm⦎ = ⊨⬜ φ ⇒ ◇ φ, ⊨⬜ ψ ⇒ ◇ ψ
	⊢ ⊨⬜ (φ ∧ ψ) ⇒ ◇ (φ ∧ ψ)

⦏⬜◇⬜∃⋎p_thm⦎ = ∀ xx⦁ ⊨⬜ (ψ xx) ⇒ ◇ (ψ xx)
	⊢ ⊨⬜ (∃ xx⦁ ψ xx) ⇒ ◇ (⬜ (∃ xx⦁ ψ xx))
=TEX

\ignore{
=SML
set_goal([], ⌜⊨⋎m⬜ (x =⋎m y) ⇒ ◇ (x =⋎m y)⌝);
a (rewrite_tac[⊨⋎m_def, eq⋎m_def] THEN REPEAT strip_tac);
val ⬜◇eq⋎m_thm = save_pop_thm "⬜◇eq⋎m_thm";

set_goal([], ⌜⊨⋎m⬜ (x ∈⋎m y) ⇒ ◇ (x ∈⋎m y)⌝);
a (rewrite_tac[⊨⋎m_def, ∈⋎m_def] THEN REPEAT strip_tac);
val ⬜◇∈⋎m_thm = save_pop_thm "⬜◇∈⋎m_thm";

set_goal([⌜⊨⋎m⬜ φ ⇒ ◇ φ⌝], ⌜⊨⋎m⬜ (¬ φ) ⇒ ◇ (¬ φ)⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac[⊨⋎m_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 6 ⌜s2'⌝);
(* *** Goal "2" *** *)
a (asm_fc_tac[]);
val ⬜◇¬_thm = save_pop_thm "⬜◇¬_thm";

set_goal([⌜⊨⋎m⬜ φ ⇒ ◇ φ⌝, ⌜⊨⋎m⬜ ψ ⇒ ◇ ψ⌝], ⌜⊨⋎m⬜ (φ ∧ ψ) ⇒ ◇ (φ ∧ ψ)⌝);
a (REPEAT (POP_ASM_T ante_tac) THEN rewrite_tac[⊨⋎m_def] THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
val ⬜◇∧_thm = save_pop_thm "⬜◇∧_thm";

set_goal([⌜∀xx:S PL⦁ ⊨⋎m⬜ (ψ xx) ⇒ ◇ (ψ xx)⌝], ⌜⊨⋎m⬜(∃⋎p xx⦁ (ψ xx)) ⇒ ◇(⬜∃⋎p xx⦁ (ψ xx))⌝);
a (REPEAT (POP_ASM_T ante_tac) THEN rewrite_tac[⊨⋎m_def, ◇⋎m_def,⬜⋎m_def] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 7 ⌜xx⌝);
(* *** Goal "1" *** *)
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (all_asm_fc_tac[Stages_fc_thm]);
a (∃_tac ⌜z'⌝ THEN asm_rewrite_tac[]);
a (∃_tac ⌜xx⌝);
a (lemma_tac ⌜ThisStage ⊆ z'⌝ THEN PC_T1 "hol1" asm_prove_tac[]);
val ⬜◇⬜∃⋎p_thm = save_pop_thm "⬜◇⬜∃⋎p_thm";
=TEX
}%ignore

Linnebo's \emph{Theorem 1} is to the effect that the modalised quantifiers are equivalent to the normal non modal quantification over sets.
Since this means that they quantify over all the sets in all the stages this can be stated directly rather than as a result about provability of translations.

The following theorem comes close to that result:

=GFT
⦏⬜∃⋎p_lemma1⦎ = ⊢ ∀ φ⦁ (⊨⬜ (∃ x⦁ φ x))
		⇔ (∃ s x⦁ s ∈ Stages ∧ ThisStage ⊆ s ∧ x ∈ s ∧ φ x s)
=TEX

It falls short by requiring that $φ\ x$ be true at some stage which is reachable from \emph{ThisStage}.
This would not be an issue if we required that all stages are reachable from \emph{ThisStage}, which is what one might reasonably expect.

This theorem is of greater scope than Linnebo's \emph{Theorem 1}, since we have no constraint on what $φ$ may be, whereas \emph{Theorem 1} is concerned only with the modal translations of formulae of non-modal first order set theory.
Since for that set of propositions \emph{Lemma 1} shows that they are necessary if true, and hence there will always be a stage which is reachable from \emph{ThisStage} at which $∃ x⦁ φ x$ if there is any stage at which it holds.

So our formally obtained results come very close to Linnebo's \emph{Theorem 1} if not quite as close as we might like.
To get a more exact semantic correspondent to Linnebo's \emph{Theorem 1} it would be necessary to define the set of modal propositions which are the meanings of the set of formulae obtainable by modalisation of sentences of first order set theory.

\ignore{
=SML
set_goal([], ⌜∀φ⦁ (⊨⋎m⬜ (∃⋎s x⦁ φ x)) ⇔ ∃(s:S SET) (x:S)⦁ s ∈ Stages ∧ ThisStage ⊆ s ∧ x ∈ s ∧ φ x s⌝);
a (rewrite_tac[⊨⋎m_def, ◇⋎m_def,⬜⋎m_def] THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜s2⌝ THEN ∃_tac ⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a (∃_tac ⌜s⌝ THEN REPEAT strip_tac);
a (∃_tac ⌜x⌝ THEN REPEAT strip_tac);
val ⬜∃⋎p_lemma1 = save_pop_thm "⬜∃⋎p_lemma1";

=IGN
set_goal([], ⌜∀φ⦁ (⊨⋎m⬜ (∃⋎s x⦁ φ x))⌝);
a (rewrite_tac[⊨⋎m_def, ◇⋎m_def,⬜⋎m_def] THEN REPEAT strip_tac
	THEN asm_fc_tac[]);

set_goal([], ⌜∀φ⦁ (⊨⋎m⬜ (∃⋎s x⦁ φ x)) ⇔ ∃s x⦁ s ∈ Stages ∧ x ∈ s ∧ φ x s⌝);
a (rewrite_tac[⊨⋎m_def, ◇⋎m_def,⬜⋎m_def] THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜s2⌝ THEN ∃_tac ⌜x⌝ THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a (strip_asm_tac ThisStage_def);
a (all_fc_tac [set_reachability_thm]);
a (∃_tac ⌜s3⌝ THEN REPEAT strip_tac);
a (all_fc_tac []);
a (∃_tac ⌜x⌝ THEN REPEAT strip_tac);
val ⬜∃⋎p_lemma1 = save_pop_thm "⬜∃⋎p_lemma1";

set_goal([], ⌜∀φ⦁ (⊨⋎m⬜ (∃⋎p x⦁ φ x)) ⇔ ∃(s:S SET) (x:S)⦁ s ∈ Stages ∧ ThisStage ⊆ s ∧ φ x s⌝);
a (rewrite_tac[⊨⋎m_def, ◇⋎m_def,⬜⋎m_def] THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
a (∃_tac ⌜s2⌝ THEN ∃_tac ⌜x⌝ THEN REPEAT strip_tac);
a (∃_tac ⌜s⌝ THEN REPEAT strip_tac);
a (∃_tac ⌜x⌝ THEN REPEAT strip_tac);
val ⬜∃⋎p_lemma1 = save_pop_thm "⬜∃⋎p_lemma1";

set_goal([], ⌜∀φ⦁ (⬜ (∃⋎p x⦁ φ x)) = λs⦁ ∃x⦁ x ∈ ⋃ Stages ∧ φ x s⌝);
a (rewrite_tac[⊨⋎m_def, ◇⋎m_def,⬜⋎m_def, ext_thm] THEN REPEAT strip_tac
	THEN asm_fc_tac[]);

=TEX
}%ignore


\ignore{
=SML
add_pc_thms "'t046b" [];
set_merge_pcs ["rbjmisc", "'t046b"];
=TEX
}%ignore


\ignore{
=SML
commit_pc "'t046b";

force_new_pc "⦏t046b⦎";
merge_pcs ["rbjmisc", "'t046b"] "t046b";
commit_pc "t046b";

force_new_pc "⦏t046b1⦎";
merge_pcs ["rbjmisc1", "'t046b"] "t046b1";
commit_pc "t046b1";
=TEX


=SML
set_flag ("subgoal_package_quiet", false);
set_flag ("pp_use_alias", true);
=TEX
}%ignore


