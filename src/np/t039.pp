=TEX
\def\rbjidtADJdoc{$$Id: t039.doc,v 1.12 2011/03/03 22:01:11 rbj Exp $$}

\section{Equivalence Relations}

=SML
open_theory "rbjmisc";
force_new_theory "equiv";
force_new_pc ⦏"'equiv"⦎;
merge_pcs ["'prove_∃_⇒_conv", "'savedthm_cs_∃_proof"] "'equiv";
set_merge_pcs ["rbjmisc", "'equiv"];
=TEX

=SML
declare_infix(230, "≡");
declare_infix(230, "≡⋎l");
declare_infix(230, "≡⋎r");
=TEX

It will be convenient to name an uncurried version of \emph{QuotientSet}:

ⓈHOLCONST
│ ⦏EquivClasses⦎ : ('a SET × ('a → 'a → BOOL)) → ('a SET SET)
├──────
│ EquivClasses = Uncurry QuotientSet
■

=GFT
⦏EquivClasses_thm⦎ =
   ⊢ EquivClasses (X, $≡) = {A|∃ x⦁ x ∈ X ∧ A = EquivClass (X, $≡) x}

⦏EquivClasses_thm1⦎ =
   ⊢ ∀ r⦁ EquivClasses r = {A|∃ x⦁ x ∈ Fst r ∧ A = EquivClass r x}
=TEX
\ignore{
=SML
push_pc "hol";

val EquivClasses_def = get_spec ⌜EquivClasses⌝;

set_goal([], ⌜∀(X, $≡)⦁ EquivClasses (X, $≡) = {A|∃ x⦁ x ∈ X ∧ A = EquivClass (X, $≡) x}⌝);
a (REPEAT strip_tac THEN rewrite_tac [quotient_set_def, EquivClasses_def]);
val EquivClasses_thm = save_pop_thm "EquivClasses_thm";

set_goal([], ⌜∀r⦁ EquivClasses r = {A|∃ x⦁ x ∈ Fst r ∧ A = EquivClass r x}⌝);
a (REPEAT ∀_tac THEN split_pair_rewrite_tac [⌜r⌝] [EquivClasses_thm]);
a (rewrite_tac[]);
val EquivClasses_thm1 = save_pop_thm "EquivClasses_thm1";
=TEX
}%ignore

=GFT
⦏EquivClasses_sub_thm⦎ =
   ⊢ ∀ (D, $≡)⦁ Equiv (D, $≡) ⇒ (∀ l⦁ l ∈ EquivClasses (D, $≡) ⇒ l ⊆ D)

⦏EquivClasses_sub_thm1⦎ =
   ⊢ ∀ r⦁ Equiv r ⇒ (∀ l⦁ l ∈ EquivClasses r ⇒ l ⊆ Fst r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀(D, $≡)⦁ Equiv(D, $≡) ⇒ ∀l⦁ l ∈ EquivClasses (D, $≡) ⇒ l ⊆ D⌝);
a (PC_T "hol1" (rewrite_tac [EquivClasses_thm, get_spec ⌜EquivClass⌝] THEN REPEAT strip_tac));
a (all_asm_fc_tac[]);
val EquivClasses_sub_thm = save_pop_thm "EquivClasses_sub_thm";

set_goal([], ⌜∀r⦁ Equiv r ⇒ ∀l⦁ l ∈ EquivClasses r ⇒ l ⊆ Fst r⌝);
a (REPEAT ∀_tac THEN split_pair_rewrite_tac [⌜r⌝][]);
a (REPEAT strip_tac THEN all_asm_fc_tac [EquivClasses_sub_thm]);
a (asm_rewrite_tac[]);
val EquivClasses_sub_thm1 = save_pop_thm "EquivClasses_sub_thm1";
=TEX
}%ignore

\subsection{Products of Equivalence Relations}\label{PER}

I am providing an alternative way of lifting operators from some type to equivalence classes over the type.
The treatment of dyadic operators, which in {\Product} have to be curried if they are to be used infix, is done by uncurrying and then lifting as if a monadic function over the cartesian product.

This will lift to the product equivalence classes so we need a treatment of products of equivalence relations.

=GFT
⦏Equiv_RelProd_thm⦎ =
   ⊢ ∀ (L, $≡⋎l) (R, $≡⋎r)⦁
	Equiv (L, $≡⋎l) ∧ Equiv (R, $≡⋎r) ⇒ Equiv ((L, $≡⋎l) RelProd (R, $≡⋎r))
=TEX

\ignore{
=SML
push_pc "hol1";

set_goal([], ⌜∀(L, $≡⋎l) (R, $≡⋎r)⦁ Equiv(L, $≡⋎l) ∧ Equiv(R, $≡⋎r) ⇒ Equiv ((L, $≡⋎l) RelProd (R, $≡⋎r))⌝);
a (REPEAT strip_tac THEN fc_tac [equiv_def]);
a (split_pair_rewrite_tac [⌜(L, $≡⋎l) RelProd (R, $≡⋎r)⌝] [equiv_def]);
a (rewrite_tac[] THEN REPEAT strip_tac);
a (all_fc_tac [Refl_RelProd_thm]);
a (all_fc_tac [Sym_RelProd_thm]);
a (all_fc_tac [Trans_RelProd_thm]);
val Equiv_RelProd_thm = save_pop_thm "Equiv_RelProd_thm";

pop_pc();
=TEX
}%ignore

\ignore{
=IGN
add_pc_thms "'rbjmisc" (map get_spec [] @ []);
set_merge_pcs ["basic_hol", "'sets_alg", "'ℝ", "'rbjmisc"];
=TEX
}%ignore

=GFT
⦏EquivClass_RelProd_thm⦎ =
   ⊢ ∀ (L, $≡⋎l) (R, $≡⋎r)⦁ Equiv (L, $≡⋎l) ∧ Equiv (R, $≡⋎r)
         ⇒ (∀ xl xr yl yr⦁ xl ∈ L ∧ xr ∈ R ∧ yl ∈ L ∧ yr ∈ R
             ⇒ ((xl, xr) ∈ EquivClass ((L, $≡⋎l) RelProd (R, $≡⋎r)) (yl, yr)
               ⇔ xl ∈ EquivClass (L, $≡⋎l) yl
                 ∧ xr ∈ EquivClass (R, $≡⋎r) yr))
=TEX
=GFT
⦏EquivClass_RelProd_thm1⦎ =
   ⊢ ∀ (L, $≡⋎l) (R, $≡⋎r)⦁ Equiv (L, $≡⋎l) ∧ Equiv (R, $≡⋎r)
         ⇒ (∀ l r⦁ l ∈ L ∧ r ∈ R
             ⇒ EquivClass ((L, $≡⋎l) RelProd (R, $≡⋎r)) (l, r)
                = (EquivClass (L, $≡⋎l) l × EquivClass (R, $≡⋎r) r))
=TEX

\ignore{
=SML
set_goal([], ⌜∀(L, $≡⋎l) (R, $≡⋎r)⦁ Equiv(L, $≡⋎l) ∧ Equiv(R, $≡⋎r) ⇒ ∀xl xr yl yr⦁ yl ∈ L ∧ yr ∈ R ⇒ ((xl, xr) ∈ EquivClass ((L, $≡⋎l) RelProd (R, $≡⋎r)) (yl, yr)
	⇔ xl ∈ EquivClass (L, $≡⋎l) yl ∧ xr ∈ EquivClass (R, $≡⋎r) yr)⌝);
a (REPEAT ∀_tac THEN strip_tac THEN rewrite_tac [RelProd_def, get_spec ⌜EquivClass⌝] THEN REPEAT strip_tac
	THEN asm_rewrite_tac [rel_∈_in_clauses]);
val EquivClass_RelProd_thm = save_pop_thm "EquivClass_RelProd_thm";

set_goal([], ⌜∀(L, $≡⋎l) (R, $≡⋎r)⦁ Equiv(L, $≡⋎l) ∧ Equiv(R, $≡⋎r)
	⇒ ∀l r⦁ l ∈ L ∧ r ∈ R ⇒ EquivClass ((L, $≡⋎l) RelProd (R, $≡⋎r)) (l, r) = ((EquivClass (L, $≡⋎l) l) × (EquivClass (R, $≡⋎r) r))⌝);
a (REPEAT strip_tac
	THEN rewrite_tac [sets_ext_clauses]
	THEN strip_tac
	THEN split_pair_rewrite_tac [⌜x⌝] [rel_∈_in_clauses]
	THEN REPEAT strip_tac
	THEN_TRY all_fc_tac [EquivClass_RelProd_thm]);
a (all_ufc_⇔_rewrite_tac [EquivClass_RelProd_thm] THEN contr_tac);
val EquivClass_RelProd_thm1 = save_pop_thm "EquivClass_RelProd_thm1";
=TEX
}%ignore

=GFT
⦏EquivClasses_RelProd_thm⦎ =
   ⊢ ∀ (L, $≡⋎l) (R, $≡⋎r)⦁ Equiv (L, $≡⋎l) ∧ Equiv (R, $≡⋎r) ⇒ (∀ l r⦁
		(l × r) ∈ EquivClasses ((L, $≡⋎l) RelProd (R, $≡⋎r))
		⇔ l ∈ EquivClasses (L, $≡⋎l) ∧ r ∈ EquivClasses (R, $≡⋎r))
=TEX
=GFT
⦏EquivClasses_RelProd_thm1⦎ =
   ⊢ ∀ (L, $≡⋎l) (R, $≡⋎r)⦁ Equiv (L, $≡⋎l) ∧ Equiv (R, $≡⋎r) ⇒ (∀ x⦁
		x ∈ EquivClasses ((L, $≡⋎l) RelProd (R, $≡⋎r))
             ⇔ (∃ l r⦁ x = (l × r)
                 ∧ l ∈ EquivClasses (L, $≡⋎l)
                 ∧ r ∈ EquivClasses (R, $≡⋎r)))
=TEX
=GFT
⦏EquivClasses_RelProd_thm2⦎ =
   ⊢ ∀ (L, $≡⋎l) (R, $≡⋎r)⦁ Equiv (L, $≡⋎l) ∧ Equiv (R, $≡⋎r)
         ⇒ EquivClasses ((L, $≡⋎l) RelProd (R, $≡⋎r))
           = EquivClasses (L, $≡⋎l) ×⋎D EquivClasses (R, $≡⋎r)
=TEX

\ignore{
=SML
set_goal([], ⌜∀(L, $≡⋎l) (R, $≡⋎r)⦁ Equiv(L, $≡⋎l) ∧ Equiv(R, $≡⋎r) ⇒ ∀l r⦁ (l × r) ∈ EquivClasses ((L, $≡⋎l) RelProd (R, $≡⋎r))
	         ⇔ l ∈ EquivClasses (L, $≡⋎l) ∧ r ∈ EquivClasses (R, $≡⋎r)⌝);
a (split_pair_rewrite_tac [⌜(L, $≡⋎l) RelProd (R, $≡⋎r)⌝][EquivClasses_thm] THEN REPEAT_N 9 strip_tac);
a (rewrite_tac [∈_in_clauses]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac [RelProd_projections_thm]);
a (split_pair_rewrite_tac [⌜x⌝][rel_∈_in_clauses] THEN strip_tac);
a (∃_tac ⌜Fst x⌝ THEN asm_rewrite_tac[]);
a (all_fc_tac [equiv_class_∈_thm]);
a (DROP_NTH_ASM_T 5 ante_tac);
a (split_pair_rewrite_tac [⌜x⌝][]);
a (ALL_UFC_T rewrite_tac [EquivClass_RelProd_thm1]);
a (STRIP_T (asm_tac o eq_sym_rule) THEN all_fc_tac [cp_eq_thm1]);
a (asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac [RelProd_projections_thm]);
a (split_pair_rewrite_tac [⌜x⌝][rel_∈_in_clauses] THEN strip_tac);
a (∃_tac ⌜Snd x⌝ THEN asm_rewrite_tac[]);
a (all_fc_tac [equiv_class_∈_thm]);
a (DROP_NTH_ASM_T 5 ante_tac);
a (split_pair_rewrite_tac [⌜x⌝][]);
a (ALL_UFC_T rewrite_tac [EquivClass_RelProd_thm1]);
a (STRIP_T (asm_tac o eq_sym_rule) THEN all_fc_tac [cp_eq_thm1]);
a (asm_rewrite_tac[]);
(* *** Goal "3" *** *)
a (∃_tac ⌜(x,x')⌝ THEN asm_rewrite_tac[RelProd_projections_thm, rel_∈_in_clauses]);
a (ALL_FC_T rewrite_tac [EquivClass_RelProd_thm1]);
val EquivClasses_RelProd_thm = save_pop_thm "EquivClasses_RelProd_thm";

set_goal([], ⌜∀(L, $≡⋎l) (R, $≡⋎r)⦁ Equiv(L, $≡⋎l) ∧ Equiv(R, $≡⋎r) ⇒ ∀x⦁ x ∈ EquivClasses ((L, $≡⋎l) RelProd (R, $≡⋎r))
	         ⇔ ∃l r⦁ x = (l × r) ∧ l ∈ EquivClasses (L, $≡⋎l) ∧ r ∈ EquivClasses (R, $≡⋎r)⌝);
a (split_pair_rewrite_tac [⌜(L, $≡⋎l) RelProd (R, $≡⋎r)⌝][EquivClasses_thm] THEN REPEAT_N 9 strip_tac);
a (rewrite_tac [∈_in_clauses]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (DROP_NTH_ASM_T 2 ante_tac THEN rewrite_tac [RelProd_projections_thm]);
a (split_pair_rewrite_tac [⌜x'⌝][rel_∈_in_clauses] THEN strip_tac);
a (∃_tac ⌜EquivClass (L, $≡⋎l) (Fst x')⌝ THEN ∃_tac ⌜EquivClass (R, $≡⋎r) (Snd x')⌝ THEN asm_rewrite_tac[]);
a (all_fc_tac [equiv_class_∈_thm]);
a (DROP_NTH_ASM_T 5 ante_tac);
a (split_pair_rewrite_tac [⌜x'⌝][]);
a (ALL_UFC_T rewrite_tac [EquivClass_RelProd_thm1]);
a (STRIP_T (asm_tac o eq_sym_rule) THEN all_fc_tac [cp_eq_thm1]);
a (REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (∃_tac ⌜Fst x'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜Snd x'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜x', x''⌝ THEN asm_rewrite_tac[RelProd_projections_thm]);
a (rewrite_tac [rel_∈_in_clauses] THEN REPEAT strip_tac);
a (ALL_UFC_T rewrite_tac [EquivClass_RelProd_thm1]);
val EquivClasses_RelProd_thm1 = save_pop_thm "EquivClasses_RelProd_thm1";

set_goal([], ⌜∀(L, $≡⋎l) (R, $≡⋎r)⦁ Equiv(L, $≡⋎l) ∧ Equiv(R, $≡⋎r) ⇒ EquivClasses ((L, $≡⋎l) RelProd (R, $≡⋎r))
	         = (EquivClasses (L, $≡⋎l) ×⋎D EquivClasses (R, $≡⋎r))⌝);
a (REPEAT strip_tac THEN rewrite_tac [sets_ext_clauses, ×⋎D_ext_thm]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [EquivClasses_RelProd_thm1]);
a (∃_tac ⌜l⌝ THEN ∃_tac ⌜r⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_ufc_⇔_rewrite_tac [EquivClasses_RelProd_thm1]);
a (∃_tac ⌜leq⌝ THEN ∃_tac ⌜req⌝ THEN asm_rewrite_tac[sets_ext_clauses]);
val EquivClasses_RelProd_thm2 = save_pop_thm "EquivClasses_RelProd_thm2";
=TEX
}%ignore

=GFT
=TEX

\ignore{
=IGN
val QuotientClasses_RelProd_thm2 = rewrite_rule [EquivClasses_def, RelProd_projections_thm] EquivClasses_RelProd_thm2;

set_goal([])

=SML
pop_pc();
=TEX
}%ignore

\subsection{Powers of Equivalence Relations}

=GFT
⦏RelPower_Equiv_thm⦎ =
   ⊢ ∀ (D, $≡) is⦁ Equiv (D, $≡) ⇒ Equiv (RelPower (D, $≡) is)
=TEX

\ignore{
=SML
set_goal([], ⌜∀(D, $≡) is⦁ Equiv(D, $≡) ⇒ Equiv(RelPower (D, $≡) is)⌝);
a (REPEAT ∀_tac THEN split_pair_rewrite_tac [⌜RelPower (D, $≡) is⌝] [equiv_def] THEN strip_tac);
a (rewrite_tac [pair_clauses]);
a (all_fc_tac [RelPower_Trans_thm, RelPower_Sym_thm, RelPower_Refl_thm]
	THEN asm_rewrite_tac[]);
val RelPower_Equiv_thm = save_pop_thm "RelPower_Equiv_thm";

=IGN
set_goal([], ⌜∀(D, $≡) is⦁ Equiv(D, $≡) ⇒ ∀f⦁ (∀i⦁ i ∈ is ⇒ f i ∈ D) 
	⇒ EquivClass (RelPower (D, $≡) is) f = {g | ∀i⦁ i ∈ is ⇒ g i ∈ (EquivClass (D, $≡) (f i))}⌝);
a (REPEAT ∀_tac THEN rewrite_tac [RelPower_def]);
=TEX
}%ignore

\subsection{Lifting Operators Over Quotients}

The conditions for a function to be liftable from a structure to a quotient of that structure are now expressed.
This will be possible of the function ``respects'' the equivalence relations which determine the relevant quotient types.

The definition give here differs from {\it Respects} in theory {\it equiv\_rel} in expressing conditions for lifting both on the domain and the codomain relative to possibly distinct equivalence relation, and therefore requires that if two elements of the domain are equivalent under one relationship then the results of the function on these two elements will be equivalent under the other relationship.

=SML
declare_infix(200, "Respects1");
declare_infix(230, "≡⋎d");
declare_infix(230, "≡⋎c");
declare_infix(230, "≡⋎e");
declare_infix(230, "≡⋎f");
=TEX

ⓈHOLCONST
│ $⦏Respects1⦎ : ('a → 'b) → (('a SET × ('a → 'a → BOOL)) × ('b SET × ('b → 'b → BOOL))) → BOOL
├──────
│ ∀ f $≡⋎c $≡⋎d C D⦁ (f Respects1 ((D, $≡⋎d), (C, $≡⋎c)))
	⇔ ∀x y⦁x ∈ D ∧ y ∈ D ∧ x ≡⋎d y ⇒ f x ∈ C ∧ f y ∈ C ∧ f x ≡⋎c f y
■

=GFT
⦏Respects1_Respects_thm⦎ =
   ⊢ ∀ f $≡⋎d C D⦁ f Respects1 ((D, $≡⋎d), Universe, $=) ⇔ (f Respects $≡⋎d) D 

⦏Respects1_Refines_thm⦎ =
   ⊢ ∀ f $≡⋎d ≡⋎c $≡⋎e ≡⋎f D C⦁
	f Respects1 ((D, $≡⋎d), C, $≡⋎c)
           ∧ ($≡⋎e Refines $≡⋎d) D
           ∧ ($≡⋎c Refines $≡⋎f) C
         ⇒ f Respects1 ((D, $≡⋎e), C, $≡⋎f)
=TEX
=GFT
⦏eq_Refines_thm⦎ =
   ⊢ ∀ $≡⋎d D⦁ Equiv (D, $≡⋎d) ⇒ ($= Refines $≡⋎d) D

⦏constant_img_thm1⦎ =
   ⊢ ∀ f A a c⦁ a ∈ A ∧ (∀ x⦁ x ∈ A ⇒ f x = c)
	⇒ (ε y⦁ ∃ x⦁ x ∈ A ∧ y = f x) = c
=TEX

\ignore{
=SML
set_goal([], ⌜∀ f $≡⋎d D⦁ (f Respects1 ((D, $≡⋎d), (Universe, $=))) ⇔ (f Respects $≡⋎d) D⌝);
a (REPEAT ∀_tac THEN rewrite_tac (map get_spec [⌜$Respects1⌝, ⌜$Respects⌝]) THEN REPEAT strip_tac
	THEN all_asm_ufc_tac[]);
val Respects1_Respects_thm = save_pop_thm "Respects1_Respects_thm";

set_goal([], ⌜∀ f $≡⋎d $≡⋎c $≡⋎e $≡⋎f D C⦁ (f Respects1 ((D, $≡⋎d), (C, $≡⋎c))) ∧ ($≡⋎e Refines $≡⋎d) D ∧ ($≡⋎c Refines $≡⋎f) C
	⇒ (f Respects1 ((D, $≡⋎e), (C, $≡⋎f)))⌝);
a (REPEAT ∀_tac THEN rewrite_tac (map get_spec [⌜$Respects1⌝, ⌜$Refines⌝]) THEN REPEAT strip_tac
	THEN all_asm_ufc_tac[] THEN REPEAT (all_asm_ufc_tac[]));
val Respects1_Refines_thm = save_pop_thm "Respects1_Refines_thm";

set_goal([], ⌜∀ $≡⋎d D⦁ Equiv (D, $≡⋎d) ⇒ ($= Refines $≡⋎d) D⌝);
a (REPEAT ∀_tac THEN rewrite_tac (map get_spec [⌜$Refines⌝, ⌜$Equiv⌝, ⌜$Refl⌝])
	THEN REPEAT strip_tac
	THEN REPEAT (all_asm_ufc_tac[])
	THEN asm_rewrite_tac[]);
val eq_Refines_thm = save_pop_thm "eq_Refines_thm";

set_goal([], ⌜
	∀f A a c⦁
		a ∈ A ∧ (∀x⦁x ∈ A ⇒ f x = c)
	⇒	(εy⦁ ∃x⦁ x ∈ A ∧ y = f x) = c
⌝);
a(REPEAT strip_tac);
a(ε_tac ⌜ε y⦁ ∃ x⦁ x ∈ A ∧ y = f x⌝);
(* *** Goal "1" *** *)
a(∃_tac⌜c⌝ THEN ∃_tac⌜a⌝ THEN REPEAT strip_tac);
a (asm_fc_tac[] THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (LEMMA_T ⌜c = f x⌝ asm_rewrite_thm_tac);
a (ASM_FC_T rewrite_tac []);
val ⦏constant_img_thm1⦎ = save_pop_thm "constant_img_thm1";
=TEX
}%ignore

The following operator lifts a function over a pair of equivalence relations respected by the function.
This definition allows that they domain and codomains are of different type, and will provide the basis for lifting monadic and dyadic operators in a single sorted theory.

=SML
declare_infix(200, "LiftOver");
=TEX

ⓈHOLCONST
│ $⦏LiftOver⦎ : ('a → 'b)
│	→ (('a SET × ('a → 'a → BOOL)) × ('b SET × ('b → 'b → BOOL)))
│	→ ('a SET → 'b SET)
├──────
│ ∀ f (D, $≡⋎d) (C, $≡⋎c)⦁ (f LiftOver ((D, $≡⋎d), (C, $≡⋎c)))
│	= λx⦁ εy⦁ ∃z⦁ z ∈ x ∧ y = EquivClass (C, $≡⋎c) (f z)
■

=GFT
⦏LiftOver_thm⦎ =
   ⊢ ∀ f (D, $≡⋎d) (C, $≡⋎c) de ce⦁
	     Equiv (D, $≡⋎d)
           ∧ Equiv (C, $≡⋎c)
           ∧ f Respects1 ((D, $≡⋎d), C, $≡⋎c)
           ∧ de ∈ D / $≡⋎d
           ∧ ce ∈ C / $≡⋎c
         ⇒ ((f LiftOver ((D, $≡⋎d), C, $≡⋎c)) de = ce
           ⇔ (∃ d c⦁ d ∈ D
               ∧ EquivClass (D, $≡⋎d) d = de
               ∧ EquivClass (C, $≡⋎c) c = ce
               ∧ c = f d))
=TEX

\ignore{
=SML
val Respects1_def= get_spec ⌜$Respects1⌝;
val LiftOver_def= get_spec ⌜$LiftOver⌝;

set_goal([], ⌜
	∀f (D, $≡⋎d) (C, $≡⋎c) de ce⦁
		Equiv(D, $≡⋎d) ∧ Equiv(C, $≡⋎c)
	∧	(f Respects1 ((D, $≡⋎d), (C, $≡⋎c)))
	∧	de ∈ (D / $≡⋎d) ∧ ce ∈ (C / $≡⋎c)
	⇒	((f LiftOver ((D, $≡⋎d), (C, $≡⋎c))) de = ce
		⇔ ∃d c⦁ d ∈ D ∧ EquivClass (D, $≡⋎d) d = de ∧ EquivClass (C, $≡⋎c) c = ce
			∧ c = f d)
⌝);
a(rewrite_tac[Respects1_def, LiftOver_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [list_∀_elim [⌜D⌝,⌜$≡⋎d⌝] quotient_map_onto_thm]);
a (∃_tac ⌜x⌝ THEN ∃_tac ⌜f x⌝ THEN_TRY asm_rewrite_tac[]);
a (SYM_ASMS_T rewrite_tac);
a (ε_tac ⌜(ε y⦁ ∃ z⦁ z ∈ de ∧ y = EquivClass (C, $≡⋎c) (f z))⌝);
(* *** Goal "1.1" *** *)
a (lemma_tac ⌜x ∈ de⌝ THEN1 (all_fc_tac [equiv_class_∈_thm] THEN asm_rewrite_tac[]));
a (∃_tac ⌜EquivClass (C, $≡⋎c) (f x)⌝ THEN ∃_tac  ⌜x⌝ THEN_TRY asm_rewrite_tac[]);
(* *** Goal "1.2" *** *)
a (asm_rewrite_tac[]);
a (lemma_tac ⌜z ∈ D⌝ THEN1 all_fc_tac [all_∀_intro quotient_∈_thm]);
a (lemma_tac ⌜x ≡⋎d z⌝);
(* *** Goal "1.2.1" *** *)
a (DROP_NTH_ASM_T 3 ante_tac THEN asm_rewrite_tac[get_spec ⌜EquivClass⌝]);
(* *** Goal "1.2.2" *** *)
a (all_asm_fc_tac[]);
a (all_ufc_⇔_tac[equiv_class_eq_thm]);
(* *** Goal "2" *** *)
a (ε_tac ⌜(ε y⦁ ∃ z⦁ z ∈ de ∧ y = EquivClass (C, $≡⋎c) (f z))⌝);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜EquivClass (C, $≡⋎c) (f d)⌝ THEN ∃_tac  ⌜d⌝ THEN_TRY asm_rewrite_tac[]);
a (SYM_ASMS_T rewrite_tac);
a (all_fc_tac[equiv_class_∈_thm]);
(* *** Goal "2.2" *** *)
a (asm_rewrite_tac[]);
a (lemma_tac ⌜z ∈ D⌝ THEN1 all_fc_tac [all_∀_intro quotient_∈_thm]);
a (lemma_tac ⌜d ≡⋎d z⌝);
(* *** Goal "2.2.1" *** *)
a (DROP_NTH_ASM_T 3 ante_tac THEN SYM_ASMS_T rewrite_tac);
a (rewrite_tac[get_spec ⌜EquivClass⌝]);
a (REPEAT strip_tac);
(* *** Goal "2.2.2" *** *)
a (all_asm_fc_tac[]);
a (LEMMA_T ⌜ce = EquivClass (C, $≡⋎c) (f d)⌝ rewrite_thm_tac THEN1 SYM_ASMS_T rewrite_tac);
a (ALL_UFC_⇔_T (rewrite_tac) [equiv_class_eq_thm]);
a (all_fc_tac [equiv_def]);
a (all_fc_tac [sym_def]);
val LiftOver_thm = save_pop_thm "LiftOver_thm";
=TEX
}%ignore

\subsubsection{Lifting Monadic Operators}

=SML
declare_infix(200, "MonOpRespects");
=TEX

ⓈHOLCONST
│ $⦏MonOpRespects⦎ : ('a → 'a) → ('a SET × ('a → 'a → BOOL)) → BOOL
├──────
│ ∀ f e⦁ f MonOpRespects e ⇔ f Respects1 (e, e)
■

=GFT
⦏MonOpRespects_thm⦎ =
   ⊢ ∀ f C $≡⦁ f MonOpRespects (C, $≡) ⇔ ∀x y⦁x ∈ C ∧ y ∈ C ∧ x ≡ y ⇒ f x ∈ C ∧ f y ∈ C ∧ f x ≡ f y
=TEX

\ignore{
=SML
set_goal([], ⌜∀ f C $≡⦁ f MonOpRespects (C, $≡) ⇔ ∀x y⦁x ∈ C ∧ y ∈ C ∧ x ≡ y ⇒ f x ∈ C ∧ f y ∈ C ∧ f x ≡ f y⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$MonOpRespects⌝, get_spec ⌜$Respects1⌝]);
val MonOpRespects_thm = save_pop_thm "MonOpRespects_thm";
=TEX
}%ignore

The following operator lifts a monadic operator over an equivalence relations respected by the operator.

=SML
declare_infix(210, "MonOpLift");
=TEX

ⓈHOLCONST
│ $⦏MonOpLift⦎ : ('a → 'a)
│	→ ('a SET × ('a → 'a → BOOL))
│	→ ('a SET → 'a SET)
├──────
│ ∀ f (D, $≡⋎d)⦁ f MonOpLift (D, $≡⋎d) = f LiftOver ((D, $≡⋎d), (D, $≡⋎d))
■
=GFT
⦏MonOpLift_thm⦎ =
   ⊢ ∀ f (D, $≡⋎d) de ce
     ⦁ Equiv (D, $≡⋎d)
           ∧ f Respects1 ((D, $≡⋎d), D, $≡⋎d)
           ∧ de ∈ D / $≡⋎d
           ∧ ce ∈ D / $≡⋎d
         ⇒ ((f MonOpLift (D, $≡⋎d)) de = ce
           ⇔ (∃ d c⦁ d ∈ D
               ∧ EquivClass (D, $≡⋎d) d = de
               ∧ EquivClass (D, $≡⋎d) c = ce
               ∧ c = f d))
=TEX

\ignore{
=SML
val MonOpRespects_def= get_spec ⌜$MonOpRespects⌝;
val MonOpLift_def= get_spec ⌜$MonOpLift⌝;

push_pc "hol";

set_goal([], ⌜
	∀f (D, $≡⋎d) de ce⦁
		Equiv(D, $≡⋎d)
	∧	(f MonOpRespects (D, $≡⋎d))
	∧	de ∈ (D / $≡⋎d) ∧ ce ∈ (D / $≡⋎d)
	⇒	((f MonOpLift (D, $≡⋎d)) de = ce
		⇔ ∃d c⦁ d ∈ D ∧ EquivClass (D, $≡⋎d) d = de ∧ EquivClass (D, $≡⋎d) c = ce
			∧ c = f d)
⌝);
a(rewrite_tac[MonOpLift_def, MonOpRespects_def] THEN REPEAT_N 7 strip_tac);
a (ALL_UFC_⇔_T (rewrite_tac) [LiftOver_thm]);
val MonOpLift_thm = save_pop_thm "MonOpLift_thm";
=TEX
}%ignore

\subsubsection{Lifting Dyadic Operators}

=SML
declare_infix(200, "DyOpRespects");
=TEX

ⓈHOLCONST
│ $⦏DyOpRespects⦎ : ('a → 'a → 'a) → ('a SET × ('a → 'a → BOOL)) → BOOL
├──────
│ ∀ f e⦁ f DyOpRespects e ⇔ (Uncurry f) Respects1 (e RelProd e, e)
■

=GFT
⦏DyOpRespects_thm⦎ =
   ⊢ ∀ f C $≡⦁ f DyOpRespects (C, $≡)
         ⇔ (∀ x1 y1 x2 y2⦁ x1 ∈ C ∧ y1 ∈ C ∧ x2 ∈ C ∧ y2 ∈ C ∧ x1 ≡ x2 ∧ y1 ≡ y2
             ⇒ f x1 y1 ∈ C ∧ f x2 y2 ∈ C ∧ f x1 y1 ≡ f x2 y2)
=TEX

\ignore{
=SML
set_goal([], ⌜∀ f C $≡⦁ f DyOpRespects (C, $≡) ⇔ ∀x1 y1 x2 y2⦁ x1 ∈ C ∧ y1 ∈ C ∧ x2 ∈ C ∧ y2 ∈ C ∧ x1 ≡ x2 ∧ y1 ≡ y2 ⇒ f x1 y1 ∈ C ∧ f x2 y2 ∈ C ∧ f x1 y1 ≡ f x2 y2⌝);
a (REPEAT ∀_tac THEN rewrite_tac [get_spec ⌜$DyOpRespects⌝, get_spec ⌜$Respects1⌝, get_spec ⌜Uncurry⌝, get_spec ⌜$RelProd⌝]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (lemma_tac ⌜(x1,y1) ∈ (C × C) ∧ (x2,y2) ∈ (C × C)⌝ THEN1 asm_rewrite_tac[get_spec ⌜$×⌝]);
a (LIST_SPEC_NTH_ASM_T 9 [⌜x1,y1⌝, ⌜x2,y2⌝] (strip_asm_tac o (rewrite_rule[])));
(* *** Goal "2" *** *)
a (lemma_tac ⌜(x1,y1) ∈ (C × C) ∧ (x2,y2) ∈ (C × C)⌝ THEN1 asm_rewrite_tac[get_spec ⌜$×⌝]);
a (LIST_SPEC_NTH_ASM_T 9 [⌜x1,y1⌝, ⌜x2,y2⌝] (strip_asm_tac o (rewrite_rule[])));
(* *** Goal "3" *** *)
a (lemma_tac ⌜(x1,y1) ∈ (C × C) ∧ (x2,y2) ∈ (C × C)⌝ THEN1 asm_rewrite_tac[get_spec ⌜$×⌝]);
a (LIST_SPEC_NTH_ASM_T 9 [⌜x1,y1⌝, ⌜x2,y2⌝] (strip_asm_tac o (rewrite_rule[])));
(* *** Goal "4" *** *)
a (all_asm_ufc_tac[]);
(* *** Goal "5" *** *)
a (all_asm_ufc_tac[]);
(* *** Goal "6" *** *)
a (all_asm_ufc_tac[]);
val DyOpRespects_thm = save_pop_thm "DyOpRespects_thm";
=TEX
}%ignore

The following operator lifts a dyadic operator over an equivalence relations respected by the operator.

=SML
declare_infix(210, "DyOpLift");
=TEX

ⓈHOLCONST
│ $⦏DyOpLift⦎ : ('a → 'a → 'a)
│	→ ('a SET × ('a → 'a → BOOL))
│	→ ('a SET → 'a SET → 'a SET)
├──────
│ ∀ f (D, $≡⋎d)⦁ f DyOpLift (D, $≡⋎d)
│	= λx y⦁((Uncurry f) LiftOver ((D, $≡⋎d) RelProd (D, $≡⋎d), (D, $≡⋎d))) (x × y)
■

=GFT
⦏DyOpLift_thm⦎ =
   ⊢ ∀ f (D, $≡⋎d) l r c
     ⦁ Equiv (D, $≡⋎d)
           ∧ f DyOpRespects (D, $≡⋎d)
           ∧ l ∈ D / $≡⋎d
           ∧ r ∈ D / $≡⋎d
           ∧ c ∈ D / $≡⋎d
         ⇒ ((f DyOpLift (D, $≡⋎d)) l r = c
           ⇔ (∃ le re ce
           ⦁ le ∈ D
               ∧ re ∈ D
               ∧ EquivClass (D, $≡⋎d) le = l
               ∧ EquivClass (D, $≡⋎d) re = r
               ∧ EquivClass (D, $≡⋎d) ce = c
               ∧ ce = f le re))
=TEX

\ignore{
=SML

push_pc "hol";

val DyOpRespects_def= get_spec ⌜$DyOpRespects⌝;
val DyOpLift_def= get_spec ⌜$DyOpLift⌝;

set_goal([], ⌜
	∀f (D, $≡⋎d) l r c⦁
		Equiv(D, $≡⋎d)
	∧	(f DyOpRespects (D, $≡⋎d))
	∧	l ∈ (D / $≡⋎d) ∧ r ∈ (D / $≡⋎d) ∧ c ∈ (D / $≡⋎d)
	⇒	((f DyOpLift (D, $≡⋎d)) l r = c
		⇔ ∃le re ce⦁ le ∈ D ∧ re ∈ D ∧ EquivClass (D, $≡⋎d) le = l ∧ EquivClass (D, $≡⋎d) re = r ∧ EquivClass (D, $≡⋎d) ce = c
			∧ ce = f le re)
⌝);
a (rewrite_tac[DyOpLift_def, DyOpRespects_def] THEN REPEAT_N 8 strip_tac);
a (all_fc_tac [Equiv_RelProd_thm]);
a (lemma_tac ⌜∃(D2, eD2)⦁ (D, $≡⋎d) RelProd (D, $≡⋎d) = (D2, eD2)⌝ THEN1 (∃_tac ⌜(D, $≡⋎d) RelProd (D, $≡⋎d)⌝ THEN rewrite_tac[]));
a (DROP_NTH_ASM_T 6 ante_tac THEN asm_rewrite_tac[] THEN strip_tac);
a (DROP_NTH_ASM_T 3 ante_tac THEN asm_rewrite_tac[] THEN strip_tac);
a (GET_NTH_ASM_T 3 (strip_asm_tac o (rewrite_rule [pair_clauses, RelProd_projections_thm]) o (eq_sym_rule)));
a (lemma_tac ⌜(l × r) ∈  EquivClasses (D2, eD2)⌝);
(* *** Goal "1" *** *)
a (SYM_ASMS_T rewrite_tac);
a (all_ufc_⇔_rewrite_tac [EquivClasses_RelProd_thm]);
a (asm_rewrite_tac [EquivClasses_def]);
(* *** Goal "2" *** *)
a (POP_ASM_T (strip_asm_tac o (rewrite_rule [EquivClasses_def])));
a (all_fc_tac [quotient_map_onto_thm]);
a (ALL_UFC_⇔_T (rewrite_tac) [LiftOver_thm]);
a (REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜Fst d⌝ THEN ∃_tac ⌜Snd d⌝ THEN ∃_tac ⌜c'⌝ THEN asm_rewrite_tac[]);
a (DROP_ASM_T ⌜d ∈ D2⌝ ante_tac THEN asm_rewrite_tac[]);
a (split_pair_rewrite_tac [⌜d⌝][rel_∈_in_clauses]);
a (strip_tac THEN asm_rewrite_tac[]);
a (SYM_ASMS_T rewrite_tac);
a (DROP_NTH_ASM_T 5 ante_tac);
a (split_pair_rewrite_tac [⌜d⌝] [eq_sym_rule (asm_rule  ⌜(D, $≡⋎d) RelProd (D, $≡⋎d) = (D2, eD2)⌝)]);
a (ALL_FC_T rewrite_tac [EquivClass_RelProd_thm1]);
a (all_fc_tac [equiv_class_∈_thm]);
a (strip_tac);
a (all_ufc_⇔_tac [cp_eq_thm1]);
a (contr_tac);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜le,re⌝ THEN ∃_tac ⌜ce⌝ THEN rewrite_tac[]);
a (rewrite_tac [asm_rule ⌜D2 = (D × D)⌝, rel_∈_in_clauses]);
a (REPEAT strip_tac);
a (SYM_ASMS_T rewrite_tac);
a (ALL_FC_T rewrite_tac [EquivClass_RelProd_thm1]);
val DyOpLift_thm = save_pop_thm "DyOpLift_thm";
=TEX
}%ignore

\subsubsection{Lifting Generic Operators}

For Universal Algebra we will represent all operators whatever their arity using a single type.
The domain of the operators is a collection of values indexed by an initial segment of the natural numbers.
The operator is represented by a pair of which the first element is the number of arguments and the second is a function which accepts a map from natural numbers into the domain of the algebra and returns a value in the domain.

The values of the argument function for natural numbers equal or greater than its arity is to be ignored, as are values for argument sets which are not confined to the domain of the algebra.
When lifting, the domain of the equivalence relation is assumed to be that of the algebra.

=SML
declare_type_abbrev("UOP", ["'a"], ⓣℕ × ((ℕ → 'a) → 'a)⌝);
=TEX


The following function effects the lifting of an operator.

ⓈHOLCONST
│ ⦏UniOpLift⦎ :  (('b)SET × ('b → 'b → BOOL)) → 'b UOP → 'b SET UOP
├──────
│ ∀ a op r⦁ UniOpLift r (a, op) = (a, λf⦁ (op LiftOver (RelPower r {x:ℕ | x < a}, r))
│							{g | ∀i⦁ i < a ⇒ g i ∈ f i})
■



\subsection{Equivalence Closure}

We are concerned here with obtaining an equivalence relation by taking the closure of some other relationship.

The presentation is slicker if we define inclusion for the kinds of relationship we are working with here.
Since there is some junk in the representation of these relations its not immediately obvious which is the best way to define inclusion.

ⓈHOLCONST
│ ⦏RelIncl⦎ : (('b)SET × ('b → 'b → BOOL)) → (('b)SET × ('b → 'b → BOOL)) → BOOL
├───────────
│ ∀A r1 B r2 ⦁ RelIncl (A, r1) (B, r2) ⇔ ∀x y⦁ x ∈ A ∧ y ∈ A ∧ r1 x y ⇒ x ∈ B ∧ y ∈ B ∧ r2 x y
■

=SML
declare_alias ("⊆", ⌜RelIncl⌝);
=TEX

The obvious way to do this is to take the intersection of the equivalence relationships which contain the given relationship, and for this purpose we need to prove that such an intersection will be an equivalence relation.

=GFT
⦏Equiv_Equiv_closure_thm⦎ =
   ⊢ ∀ A r
     ⦁ Equiv
         (A,
             (λ x y
               ⦁ ∀ $≡⋎d
                 ⦁ Equiv (A, $≡⋎d) ∧ (∀ v w⦁ r v w ⇒ v ≡⋎d w) ⇒ x ≡⋎d y))
=TEX

\ignore{
=SML
val RelIncl_def = get_spec ⌜RelIncl⌝;
=IGN
set_goal ([], ⌜∀(A:'d SET) (r:'d → 'd → BOOL)⦁ Equiv (A, λx y:'d⦁ ∀$≡⋎d⦁ Equiv(A, $≡⋎d) ∧ (∀v w:'d⦁ r v w ⇒ v ≡⋎d w) ⇒ x ≡⋎d y)⌝);
a (REPEAT strip_tac THEN rewrite_tac [equiv_def, refl_def, sym_def, trans_def] THEN REPEAT strip_tac
	THEN REPEAT (all_asm_ufc_tac[]));
val Equiv_Equiv_closure_thm = save_pop_thm "Equiv_Equiv_closure_thm";
=SML
set_goal ([], ⌜∀(A:'d SET) (r:'d → 'd → BOOL)⦁ Equiv (A, λx y:'d⦁ ∀$≡⋎d⦁ Equiv(A, $≡⋎d) ∧ ((A, r) ⊆ (A, $≡⋎d)) ⇒ x ≡⋎d y)⌝);
a (REPEAT strip_tac THEN rewrite_tac [equiv_def, refl_def, sym_def, trans_def, RelIncl_def] THEN REPEAT strip_tac
	THEN REPEAT (all_asm_ufc_tac[]));
val Equiv_Equiv_closure_thm = save_pop_thm "Equiv_Equiv_closure_thm";
=TEX
}%ignore

We therefore define the equivalence closure of a relation thus:

ⓈHOLCONST
│ ⦏EquivClosure⦎ : (('b)SET × ('b → 'b → BOOL)) → (('b)SET × ('b → 'b → BOOL))
├───────────
│ ∀A r⦁  EquivClosure (A, r) = (A, λx y⦁ ∀$≡⋎d⦁ Equiv(A, $≡⋎d) ∧ (A, r) ⊆ (A, $≡⋎d) ⇒ x ≡⋎d y)
■

The following are then immediate:

=GFT
⦏Equiv_EquivClosure_thm⦎ = ⊢ ∀ A r⦁ Equiv (EquivClosure (A, r))
⦏EquivClosure_MinEquiv_thm⦎ =
   ⊢ ∀ A r $≡⋎d⦁ Equiv (A, $≡⋎d) ∧ (A, r) ⊆ (A, $≡⋎d)
	⇒ EquivClosure (A, r) ⊆ (A, $≡⋎d)
⦏Fst_EquivClosure_thm⦎ = ⊢ ∀ eq⦁ Fst (EquivClosure eq) = Fst eq
=TEX

\ignore{
=SML
val EquivClosure_def = get_spec ⌜EquivClosure⌝;

set_goal([], ⌜∀A r⦁ Equiv(EquivClosure (A, r))⌝);
a (rewrite_tac [EquivClosure_def, Equiv_Equiv_closure_thm]);
val Equiv_EquivClosure_thm = save_pop_thm "Equiv_EquivClosure_thm";

set_goal([], ⌜∀A r $≡⋎d⦁ Equiv(A, $≡⋎d) ∧ (A, r) ⊆ (A, $≡⋎d) ⇒ EquivClosure (A, r) ⊆ (A, $≡⋎d)⌝);
a (rewrite_tac [EquivClosure_def, Equiv_Equiv_closure_thm, RelIncl_def]
	THEN REPEAT strip_tac THEN REPEAT (all_asm_ufc_tac[]));
val EquivClosure_MinEquiv_thm = save_pop_thm "EquivClosure_MinEquiv_thm";

set_goal([], ⌜∀eq⦁ Fst (EquivClosure eq) = Fst eq⌝);
a (strip_tac THEN split_pair_rewrite_tac [⌜eq⌝] [EquivClosure_def]);
a (rewrite_tac[]);
val Fst_EquivClosure_thm = save_pop_thm "Fst_EquivClosure_thm";
=TEX
}%ignore

\section{Universal Algebra}

=SML
open_theory "equiv";
force_new_theory "unalg";
force_new_pc ⦏"'unalg"⦎;
merge_pcs ["'prove_∃_⇒_conv", "'savedthm_cs_∃_proof"] "'unalg";
set_merge_pcs ["rbjmisc", "'unalg"];
=TEX

To make the operators fairly general within the constrainst imposed by the HOL type system we will have operators as functions over indexed sets of values.

The following labelled product is used as a general notion of ``structure'' independent of signature.
Of course any particular algebra will have a definite signature.

A signature is a string indexed set of arities, where an arity is a natural number.

=SML
declare_type_abbrev ("SIG", [], ⓣ(STRING, ℕ) IX⌝);
=TEX

The operators over the algebra are represented by functions from indexed sets of operands to a single result value.
In this case we pack the arguments into a total function and ignore the values which do not correspond to the signature.
The signature (i.e. the arity of each operator) is explicit in this structure, otherwise the range of significance of the operators would not be known.

ⓈHOLLABPROD ⦏STRUCT⦎───────────────
│	⦏SCar⦎		: 'a SET;
│	⦏SOps⦎		: (STRING, 'a UOP)IX
■─────────────────────────────

ⓈHOLCONST
│ ⦏Arity⋎u⦎ : ('a) STRUCT → STRING → ℕ
├───────────
│ ∀A n⦁ Arity⋎u A n = Fst (ValueOf (SOps A n)) 
■

=GFT
⦏Arity⋎u_lemma⦎ =
	⊢ ∀ d l n⦁ Arity⋎u (MkSTRUCT d (IxPack l)) n = Fst (ValueOf (IxPack l n))
=TEX

\ignore{
=SML
val SOps_def = get_spec ⌜SOps⌝;
val Arity⋎u_def = get_spec ⌜Arity⋎u⌝;

set_goal([], ⌜∀d l n⦁ Arity⋎u(MkSTRUCT d (IxPack l)) n = Fst (ValueOf (IxPack l n))⌝);
a (rewrite_tac [Arity⋎u_def, SOps_def]);
val Arity⋎u_lemma = save_pop_thm "Arity⋎u_lemma";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Oper⦎ : ('a) STRUCT → STRING → ((ℕ → 'a) → 'a)
├───────────
│ ∀A n⦁ Oper A n = Snd (ValueOf (SOps A n)) 
■

=GFT
⦏Oper_lemma⦎ =
	⊢ ∀ d l n⦁ Oper (MkSTRUCT d (IxPack l)) n = Snd (ValueOf (IxPack l n))
=TEX

\ignore{
=SML
val Oper_def = get_spec ⌜Oper⌝;

set_goal([], ⌜∀d l n⦁ Oper(MkSTRUCT d (IxPack l)) n = Snd (ValueOf (IxPack l n))⌝);
a (rewrite_tac [Oper_def, SOps_def]);
val Oper_lemma = save_pop_thm "Oper_lemma";
=TEX
}%ignore

\ignore{
=SML
add_pc_thms "'unalg" (map get_spec [] @ [Arity⋎u_lemma, Oper_lemma]);
set_merge_pcs ["rbjmisc", "'unalg"];
=TEX
}%ignore


The following function extracts the signature from a structure.

ⓈHOLCONST
│ ⦏Sig⦎ : ('a) STRUCT → SIG
├───────────
│ ∀s⦁ Sig s = IxCompIx (SOps s) (λx⦁ Value (Fst x)) 
■

=GFT
⦏IxDom_Sig_thm⦎ =
	⊢ ∀ S⦁ IxDom (Sig S) = IxDom (SOps S)

⦏∈_IxDom_Sig_thm⦎ =
	⊢ ∀ S x⦁ x ∈ IxDom (Sig S) ⇔ x ∈ IxDom (SOps S)
=TEX

\ignore{
=SML
val SOps_def = get_spec ⌜SOps⌝;
val IxCompIx_def = get_spec ⌜$IxCompIx⌝;
val Sig_def = get_spec ⌜Sig⌝;

set_goal ([], ⌜∀S⦁ IxDom (Sig S) = IxDom (SOps S)⌝);
a (strip_tac THEN rewrite_tac[Sig_def, IxCompIx_def, IxDom_def, sets_ext_clauses]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
val IxDom_Sig_thm = save_pop_thm "IxDom_Sig_thm";

set_goal ([], ⌜∀S x⦁ x ∈ IxDom (Sig S) ⇔ x ∈ IxDom (SOps S)⌝);
a (strip_tac THEN rewrite_tac[Sig_def, IxCompIx_def, IxDom_def, sets_ext_clauses]
	THEN REPEAT strip_tac THEN_TRY asm_rewrite_tac[]);
a (swap_nth_asm_concl_tac 1 THEN asm_rewrite_tac[]);
val ∈_IxDom_Sig_thm = save_pop_thm "∈_IxDom_Sig_thm";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Arity⋎i⦎ : SIG → STRING → ℕ
├───────────
│ ∀A n⦁ Arity⋎i A n = ValueOf (A n) 
■

=GFT
⦏sig_arity_lemma⦎ =
	⊢ ∀ A n⦁ n ∈ IxDom (Sig A) ⇒ Arity⋎i (Sig A) n = Arity⋎u A n
=TEX

\ignore{
=SML
val Arity⋎i_def = get_spec ⌜Arity⋎i⌝;

set_goal([], ⌜∀A n⦁ n ∈ IxDom (Sig A) ⇒ Arity⋎i (Sig A) n = Arity⋎u A n⌝);
a (REPEAT ∀_tac THEN rewrite_tac[Arity⋎i_def, Arity⋎u_def, Sig_def, IxCompIx_def, IxDom_def]
	THEN cond_cases_tac ⌜SOps A n = Undefined⌝);
val sig_arity_lemma = save_pop_thm "sig_arity_lemma";
=TEX
}%ignore


\emph{IxInc} (aliased as $⊑$) is inclusion of indexed sets, and suffices for signature inclusion.

=GFT
⦏IxDom_Sig_SOps_thm⦎ =
	⊢ ∀ A⦁ IxDom (Sig A) = IxDom (SOps A)

⦏SigInc_IxDom_⊆_thm⦎ =
	⊢ ∀ A B⦁ Sig A ⊑ Sig B ⇒ IxDom (Sig A) ⊆ IxDom (Sig B)

⦏SigInc_IxDom_Sops_⊆_thm⦎ =
	⊢ ∀ A B⦁ Sig A ⊑ Sig B ⇒ IxDom (SOps A) ⊆ IxDom (SOps B)

⦏SigInc_Arity⋎i_thm⦎ =
	⊢ ∀ A B n⦁ Sig A ⊑ Sig B ∧ n ∈ IxDom (Sig A)
         ⇒ Arity⋎i (Sig A) n = Arity⋎i (Sig B) n

⦏SigInc_Arity⋎u_thm⦎ =
	⊢ ∀ A B n⦁ Sig A ⊑ Sig B ∧ n ∈ IxDom (Sig A)
	⇒ Arity⋎u A n = Arity⋎u B n
=TEX

\ignore{
=SML
set_goal([], ⌜∀A⦁ IxDom (Sig A) = IxDom (SOps A)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[Sig_def, IxDom_def, sets_ext_clauses, IxCompIx_def] THEN strip_tac);
a (cond_cases_tac ⌜SOps A x = Undefined⌝);
val IxDom_Sig_SOps_thm = save_pop_thm "IxDom_Sig_SOps_thm";

set_goal([], ⌜∀A B⦁ Sig A ⊑ Sig B ⇒ IxDom (Sig A) ⊆ IxDom (Sig B)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[IxInc_def, IxDom_def]);
a (PC_T "hol1" (REPEAT strip_tac) THEN asm_fc_tac[] THEN asm_rewrite_tac[]);
val SigInc_IxDom_⊆_thm = save_pop_thm "SigInc_IxDom_⊆_thm";

set_goal([], ⌜∀A B⦁ Sig A ⊑ Sig B ⇒ IxDom (SOps A) ⊆ IxDom (SOps B)⌝);
a (REPEAT strip_tac THEN fc_tac[SigInc_IxDom_⊆_thm]);
a (asm_rewrite_tac [map_eq_sym_rule IxDom_Sig_SOps_thm]);
val SigInc_IxDom_Sops_⊆_thm = save_pop_thm "SigInc_IxDom_Sops_⊆_thm";

set_goal([], ⌜∀A B n⦁ Sig A ⊑ Sig B ∧ n ∈ IxDom (Sig A) ⇒ Arity⋎i (Sig A) n = Arity⋎i (Sig B) n⌝);
a (REPEAT strip_tac THEN rewrite_tac[Arity⋎i_def]);
a (all_fc_tac [⊑_IxVal_thm]);
a (POP_ASM_T ante_tac THEN rewrite_tac [IxVal_def] THEN STRIP_T rewrite_thm_tac);
val SigInc_Arity⋎i_thm = save_pop_thm "SigInc_Arity⋎i_thm";

set_goal([], ⌜∀A B n⦁ Sig A ⊑ Sig B ∧ n ∈ IxDom (Sig A) ⇒ Arity⋎u A n = Arity⋎u B n⌝);
a (REPEAT strip_tac THEN all_asm_fc_tac [SigInc_Arity⋎i_thm]);
a (all_asm_fc_tac [sig_arity_lemma, IxDom_⊑_thm]);
a (all_asm_fc_tac [sig_arity_lemma]);
a (SYM_ASMS_T rewrite_tac);
val SigInc_Arity⋎u_thm = save_pop_thm "SigInc_Arity⋎u_thm";
=TEX
}%ignore

This is possibly too crude, it might be better to ignore the irrelevant behaviour of the operators (i.e. values off sig or out of domain).

ⓈHOLCONST
│ ⦏StructInc⦎ : ('a) STRUCT → ('a) STRUCT → BOOL
├───────────
│ ∀s t⦁ StructInc s t ⇔ SCar s = SCar t ∧ IxInc (SOps s) (SOps t) 
■

=SML
declare_alias("⊑", ⌜StructInc⌝);
=TEX

There is a general requirement on structures that the operators are closed on the domain of the structure.

ⓈHOLCONST
│ ⦏ClosedOp⦎ : 'a SET → (ℕ × ((ℕ → 'a) → 'a)) → BOOL
├───────────
│ ∀s p⦁ ClosedOp s p = ∀f⦁ (∀i⦁ i < Fst p ⇒ f i ∈ s) ⇒ Snd p f ∈ s
■

ⓈHOLCONST
│ ⦏ClosedStruct⦎ : ('a) STRUCT → BOOL
├───────────
│ ∀s⦁ ClosedStruct s ⇔ ∀p⦁ p ∈ IxRan (SOps s) ⇒ ClosedOp (SCar s) p
■

\subsection{Packing Functions}

The form of the operators is not ideal for talking about the structures, so we define some functions which will make more convenient forms readily obtainable.

There are two things we need to be able to do.
The first is to convert 0-ary 1-ary and 2-ary operations in their usual convenient representation to the representation in which the arguments are collected into an indexed set.
The second is to collect the operators into a name-indexed set (this is done by \emph{IxPack} \cite{rbjt006}).

ⓈHOLCONST
│ ⦏pack0op⦎ : 'a → (ℕ × ((ℕ → 'a) → 'a))
├───────────
│ ∀c⦁ pack0op c = (0, λis⦁ c)
■

ⓈHOLCONST
│ ⦏unpack0op⦎ : ((ℕ → 'a) → 'a) → 'a
├───────────
│ ∀f⦁ unpack0op f = f (εx⦁T)
■


=GFT
⦏unpack0op_lemma⦎ = ⊢ ∀ c⦁ unpack0op (Snd (pack0op c)) = c
=TEX

\ignore{
=SML
val pack0op_def = get_spec ⌜pack0op⌝;
val unpack0op_def = get_spec ⌜unpack0op⌝;

set_goal([], ⌜∀c⦁ unpack0op (Snd(pack0op c)) = c⌝);
a (rewrite_tac [pack0op_def, unpack0op_def]);
val unpack0op_lemma = pop_thm();
=TEX
}%ignore

ⓈHOLCONST
│ ⦏pack1op⦎ : ('a → 'a) → (ℕ × ((ℕ → 'a) → 'a))
├───────────
│ ∀f⦁ pack1op f = (1, λis⦁ f (is 0))
■

ⓈHOLCONST
│ ⦏unpack1op⦎ : ((ℕ → 'a) → 'a) → ('a → 'a)
├───────────
│ ∀f⦁ unpack1op f = λx⦁ f (λy⦁ x)
■

=GFT
⦏unpack1op_lemma⦎ = ⊢ ∀ f⦁ unpack1op (Snd (pack1op f)) = f
=TEX

\ignore{
=SML
val pack1op_def = get_spec ⌜pack1op⌝;
val unpack1op_def = get_spec ⌜unpack1op⌝;

set_goal([], ⌜∀f⦁ unpack1op (Snd(pack1op f)) = f⌝);
a (rewrite_tac [pack1op_def, unpack1op_def, ext_thm]);
val unpack1op_lemma = pop_thm();
=TEX
}%ignore

ⓈHOLCONST
│ ⦏pack2op⦎ : ('a → 'a → 'a) → (ℕ × ((ℕ → 'a) → 'a))
├───────────
│ ∀f⦁ pack2op f = (2, λis⦁ f (is 0) (is 1))
■

ⓈHOLCONST
│ ⦏unpack2op⦎ : ((ℕ → 'a) → 'a) → ('a → 'a → 'a)
├───────────
│ ∀f⦁ unpack2op f = λx y⦁ f (λz⦁ if z = 0 then x else y)
■

=GFT
⦏unpack2op_lemma⦎ = ⊢ ∀ f⦁ unpack2op (Snd (pack2op f)) = f
=TEX

\ignore{
=SML
val pack2op_def = get_spec ⌜pack2op⌝;
val unpack2op_def = get_spec ⌜unpack2op⌝;

set_goal([], ⌜∀f⦁ unpack2op (Snd(pack2op f)) = f⌝);
a (rewrite_tac [pack2op_def, unpack2op_def, ext_thm]);
val unpack2op_lemma = pop_thm();
=TEX
}%ignore

It is intended that specific algebras are introduced by defining a constructor which takes a domain and a number of operators of various arities and packs them into an object of type \emph{STRUCT}.

Such a definitions has the general form:

=GFT
	∀ D o⋎1 o⋎2... o⋎n⦁ MkAlg D o⋎1 o⋎2... o⋎n
         	= MkSTRUCT D (IxPack [("o⋎1", pack?op o⋎1); ("o⋎2", pack?op o⋎2);
					... ; ("o⋎n", pack?op o⋎n)])
=TEX
It will be convenient to unpack such structures using pattern matching on the kinds of expression which are used to construct them, but in order for the consistency such definitions to be automatically proven it is necessary to supply a theorem for each particular algebra in use of the general form:
=GFT
	∀cf⦁ ∃f⦁ ∀D o⋎1 o⋎2... o⋎n⦁ f(MkAlg D o⋎1 o⋎2... o⋎n) = cf D o⋎1 o⋎2... o⋎n
=TEX
The witness for proving the existential can be presented in the form:
=GFT
	λs⦁ cf (SCar s) (unpack?op (Oper s o⋎1name)) (unpack?op (Oper s o⋎2name))
					... (unpack?op (Oper s o⋎nname))
=TEX
in which the `?' signs and the operator names are discovered from the definition of the constructor \emph{MkAlg}. 

Because the operators have different types according to their arity this cannot be expressed as a general theorem, but it is possible to automate the construction an proof of the required theorem given the definition of the particular \emph{MkAlg} constructor, assuming that this packs up its arguments into a structure in a standard way.

We next undertake the required automation.
=SML
local
   fun oprev f =
	let val (n, t) = dest_const f
	    val (_, [ot1, ot2]) = dest_ctype t
	    val (_, [_, ot3]) = dest_ctype ot2
	    val nt = list_mk_→_type [ot3, ot1]
	    val nop = mk_const (implode((explode "un")@(explode n)), nt)
        in nop
	end

   fun opmap (l, r) =
	let val cname = dest_string l
	    val (pakfun, oper) = dest_app r
	    val rtype = type_of r
	    val (_, [_, ot]) = dest_ctype rtype
	    val (ft, [_, tv]) = dest_ctype ot
	    val opex = list_mk_app (mk_const ("Oper", inst_type [(tv, ⓣ'a⌝)] ⓣ'a STRUCT → STRING → ((ℕ → 'a) → 'a)⌝),
			[mk_var("s", inst_type [(tv, ⓣ'a⌝)] ⓣ'a STRUCT⌝), l])
	    val res = list_mk_app (oprev pakfun, [opex])
	in res
	end

in fun make_alg_∃_thm tm =
	let val spec = get_spec tm;
	    val (vars, body) = strip_binder "∀" (concl spec);
	    val (_, [mkalge, mkstructe]) = strip_app body;
	    val (mkalg, (d1 :: ops)) = strip_app mkalge;
	    val (mkalgname, mkalgtype) = dest_const mkalg;
	    val (mkstructetype :: revalgtype) = rev (strip_→_type mkalgtype);
	    val (_, [d, packe]) = strip_app mkstructe;
	    val (_, [packlist]) = strip_app packe;
	    val oplist = dest_list packlist;
	    val newoplist = (map (opmap o dest_pair) oplist);
	    val codtype = mk_vartype (string_variant (term_tyvars mkalge) "'b");
	    val vars = mk_var("s", mkstructetype);
	    val varf = mk_var("f", mk_→_type (mkstructetype, codtype));
	    val varcf = mk_var("cf", list_mk_→_type (rev(codtype::revalgtype)));
	    val cfe = list_mk_app (varcf, d1::ops);
	    val fe = mk_app (varf, mkalge);
	    val eq1 = mk_eq (fe, cfe);
	    val innerall = list_mk_∀ (d1::ops, eq1);
	    val exists = mk_∃ (varf, innerall);
	    val conjec = mk_∀ (varcf, exists);
	    val scars = mk_app (mk_const("SCar", mk_→_type (mkstructetype, type_of d1)) , vars);
	    val witness = mk_λ (vars, list_mk_app (varcf, (scars::newoplist)));
	    val pat_thm = tac_proof(([], conjec),
			REPEAT ∀_tac THEN ∃_tac witness THEN rewrite_tac [spec, SOps_def]);
	    in pat_thm
	end;
end;

=IGN
set_goal([], conjec);
a (REPEAT ∀_tac);
a (∃_tac witness THEN rewrite_tac [get_spec ⌜MkLat⌝, SOps_def]);
val spec = get_spec ⌜MkLat⌝;
make_alg_∃_thm ⌜MkLat⌝;
=TEX

=GFT
⦏fst_packop_lemma⦎ =
	⊢ (∀ k⦁ Fst (pack0op k) = 0)
	∧ (∀ k⦁ Fst (pack1op k) = 1)
	∧ (∀ k⦁ Fst (pack2op k) = 2)

⦏UniOpLift_pack0op_lemma⦎ =
	⊢ ∀ C r op⦁ UniOpLift (C, r) (pack0op op) = pack0op (EquivClass (C, r) op)

⦏UniOpLift_pack1op_lemma⦎ =
	⊢ ∀ C r op⦁ UniOpLift (C, r) (pack1op op) = pack1op (op MonOpLift (C, r))

⦏UniOpLift_pack2op_lemma⦎ =
	⊢ ∀ C r op⦁ UniOpLift (C, r) (pack2op op) = pack2op (op DyOpLift (C, r))
=TEX

\ignore{

=SML
val UniOpLift_def = get_spec ⌜UniOpLift⌝;

set_goal([], ⌜(∀k⦁ Fst (pack0op k) = 0)
		∧ (∀k⦁ Fst (pack1op k) = 1)
		∧ (∀k⦁ Fst (pack2op k) = 2)⌝);
a (rewrite_tac[pack0op_def, pack1op_def, pack2op_def]);
val fst_packop_lemma = save_pop_thm "fst_packop_lemma";

set_goal([], ⌜∀C r op⦁ UniOpLift (C, r) (pack0op op) = pack0op (EquivClass (C, r) op)⌝);
a (rewrite_tac [UniOpLift_def, pack0op_def]);
a (REPEAT ∀_tac THEN rewrite_tac [ext_thm]);
a (rewrite_tac [LiftOver_def, RelPower_def, RelProd_def]);
a (ε_tac ⌜ε y⦁ y = EquivClass (C, r) op⌝);
a (∃_tac ⌜EquivClass (C, r) op⌝ THEN rewrite_tac[]);
val UniOpLift_pack0op_lemma = save_pop_thm "UniOpLift_pack0op_lemma";

set_goal([], ⌜∀C r op⦁ UniOpLift (C, r) (pack1op op) = pack1op (op MonOpLift (C, r))⌝);
a (rewrite_tac [UniOpLift_def, pack1op_def, MonOpLift_def]);
a (REPEAT ∀_tac THEN rewrite_tac [ext_thm] THEN strip_tac);
a (rewrite_tac [LiftOver_def, RelPower_def, RelProd_def]);
a (LEMMA_T ⌜(λ y⦁ ∃ z⦁ (∀ i⦁ i < 1 ⇒ z i ∈ x i) ∧ y = EquivClass (C, r) (op (z 0))) = (λ y⦁ ∃ z⦁ z ∈ x 0 ∧ y = EquivClass (C, r) (op z))⌝
	rewrite_thm_tac);
a (rewrite_tac [ext_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜z 0⌝ THEN asm_rewrite_tac[rel_∈_in_clauses]);
a (LEMMA_T ⌜0 < 1⌝ asm_tac THEN1 PC_T1 "lin_arith" prove_tac[]);
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜λy⦁ z⌝);
a (asm_rewrite_tac[] THEN REPEAT strip_tac);
a (fc_tac [pc_rule1 "lin_arith" prove_rule[] ⌜i < 1 ⇒ i=0⌝]
	THEN all_var_elim_asm_tac);
val UniOpLift_pack1op_lemma = save_pop_thm "UniOpLift_pack1op_lemma";

set_goal([], ⌜∀C r op⦁ UniOpLift (C, r) (pack2op op) = pack2op (op DyOpLift (C, r))⌝);
a (rewrite_tac [UniOpLift_def, pack2op_def, DyOpLift_def]);
a (REPEAT ∀_tac THEN rewrite_tac [ext_thm] THEN strip_tac);
a (rewrite_tac [LiftOver_def, RelPower_def, RelProd_def]);
a (LEMMA_T ⌜	(λy⦁ ∃ z⦁ (∀ i⦁ i < 2 ⇒ z i ∈ x i) ∧ y = EquivClass (C, r) (op (z 0) (z 1))) =
		(λy⦁ ∃ z⦁ z ∈ (x 0 × x 1) ∧ y = EquivClass (C, r) (op (Fst z) (Snd z)))⌝
	rewrite_thm_tac);
a (rewrite_tac [ext_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜(z 0, z 1)⌝ THEN asm_rewrite_tac[rel_∈_in_clauses]);
a (lemma_tac ⌜0 < 2 ∧ 1 < 2⌝ THEN1 PC_T1 "lin_arith" prove_tac[]);
a (asm_fc_tac[]);
a (contr_tac);
(* *** Goal "2" *** *)
a (∃_tac ⌜λy⦁ if y = 0 then Fst z else Snd z⌝);
a (asm_rewrite_tac[] THEN REPEAT strip_tac);
a (DROP_NTH_ASM_T 3 ante_tac THEN split_pair_rewrite_tac [⌜z⌝][rel_∈_in_clauses]
	THEN (cond_cases_tac ⌜i = 0⌝) THEN contr_tac);
a (fc_tac [pc_rule1 "lin_arith" prove_rule[] ⌜i < 2 ∧ ¬ i = 0 ⇒ i=1 ∨ i=2⌝]
	THEN all_var_elim_asm_tac);
val UniOpLift_pack2op_lemma = save_pop_thm "UniOpLift_pack2op_lemma";

add_pc_thms "'unalg" [unpack0op_lemma, unpack1op_lemma, unpack2op_lemma, fst_packop_lemma, UniOpLift_pack0op_lemma, UniOpLift_pack1op_lemma, UniOpLift_pack2op_lemma];
set_merge_pcs ["rbjmisc", "'unalg"];
=TEX
}%ignore

We need to know that lifting commutes with packing, which is shown by the following theorems.

=GFT
=TEX

\ignore{
=IGN
set_goal([], ⌜UniOpLift (pack0op c) = ⌝);

=TEX
}%ignore


\subsection{Homomorphisms}

Now we can define the notion of homomorphism.

First we define the requirement on the homomorphism to map the domain of the source into the domain of the target.

ⓈHOLCONST
│ ⦏FunClosed⦎ : ('b)STRUCT  × ('b → 'c) × ('c) STRUCT → BOOL
├──────
│ ∀ A f B⦁ FunClosed (A, f, B) ⇔ ∀ x⦁ x ∈ SCar A ⇒ f x ∈ SCar B
■

=GFT
⦏FunClosed_trans_thm⦎ = ⊢ ∀ A f B g C⦁
	FunClosed (A, f, B) ∧ FunClosed (B, g, C) ⇒ FunClosed (A, g o f, C)

⦏FunClosed_FunImage_thm⦎ =
	⊢ ∀ A f B⦁ FunClosed (A, f, B) ⇔ FunImage f (SCar A) ⊆ SCar B
=TEX

\ignore{
=SML
val FunClosed_def = get_spec ⌜FunClosed⌝;

set_goal([], ⌜∀ A f B g C⦁ FunClosed (A, f, B) ∧ FunClosed (B, g, C) ⇒ FunClosed (A, g o f, C)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [FunClosed_def] THEN REPEAT strip_tac THEN REPEAT (all_asm_ufc_tac[]));
val FunClosed_trans_thm = save_pop_thm "FunClosed_trans_thm";

set_goal([], ⌜∀ A f B⦁ FunClosed (A, f, B) ⇔ FunImage f (SCar A) ⊆ (SCar B)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [FunClosed_def, FunImage_def, sets_ext_clauses] THEN REPEAT strip_tac THEN REPEAT (all_asm_ufc_tac[]));
(* *** Goal "1" *** *)
a (SYM_ASMS_T rewrite_tac);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜f x⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
val FunClosed_FunImage_thm = save_pop_thm "FunClosed_FunImage_thm";
=TEX
}%ignore

Then the requirement that the function respects an operator is expressed:

ⓈHOLCONST
│ ⦏OpRespect⦎ : ('b SET × ('b → 'c) × ℕ) → ((ℕ → 'b) → 'b) → ((ℕ → 'c) → 'c) → BOOL
├──────
│ ∀ D f n op1 op2⦁ OpRespect (D, f, n) op1 op2 ⇔
│	∀g⦁ FunImage g {i | i < n} ⊆ D ⇒ f (op1 g) = op2 (λx⦁ f (g x))
■

=GFT
⦏OpRespect_pack0op_lemma⦎ =
   ⊢ ∀ D f d c⦁ OpRespect (D, f, 0) (Snd (pack0op d)) (Snd (pack0op c)) ⇔ f d = c

⦏OpRespect_pack1op_lemma⦎ =
	⊢ ∀ D f d c⦁ OpRespect (D, f, 1) (Snd (pack1op d)) (Snd (pack1op c))
         ⇔ (∀ x⦁ x ∈ D ⇒ f (d x) = c (f x))

⦏OpRespect_pack2op_lemma⦎ =
	⊢ ∀ D f $*⋎d $*⋎c⦁ OpRespect (D, f, 2) (Snd (pack2op $*⋎d)) (Snd (pack2op $*⋎c))
         ⇔ (∀ x y⦁ x ∈ D ∧ y ∈ D ⇒ f (x *⋎d y) = f x *⋎c f y)
=TEX

=SML
declare_infix (200, "*⋎d");
declare_infix (200, "*⋎c");
=TEX

\ignore{
=SML
val OpRespect_def = get_spec ⌜OpRespect⌝;

set_goal([], ⌜∀D f d c⦁ OpRespect (D, f, 0) (Snd (pack0op d)) (Snd (pack0op c)) ⇔ f d = c⌝);
a (REPEAT ∀_tac);
a (rewrite_tac [OpRespect_def, pack0op_def, sets_ext_clauses, ∈_in_clauses, FunImage_def]);
val OpRespect_pack0op_lemma = save_pop_thm "OpRespect_pack0op_lemma";

set_goal([], ⌜∀D f d c⦁ OpRespect (D, f, 1) (Snd (pack1op d)) (Snd (pack1op c))
	⇔ ∀x⦁ x ∈ D ⇒ f (d x) = c (f x)⌝);
a (REPEAT ∀_tac);
a (rewrite_tac [OpRespect_def, pack1op_def, sets_ext_clauses, ∈_in_clauses, FunImage_def]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 2 ⌜λn:ℕ⦁x⌝);
(* *** Goal "1.1" *** *)
a (DROP_ASM_T ⌜a < 1⌝ (strip_asm_tac o less_cases_rule) THEN all_var_elim_asm_tac);
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule[])) THEN all_var_elim_asm_tac);
(* *** Goal "1.2" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 1 ⌜g 0⌝);
(* *** Goal "2.1" *** *)
a (spec_nth_asm_tac 1 ⌜0⌝);
(* *** Goal "2.2" *** *)
a (all_asm_fc_tac[]);
val OpRespect_pack1op_lemma = save_pop_thm "OpRespect_pack1op_lemma";

set_goal([], ⌜∀D f $*⋎d $*⋎c⦁ OpRespect (D, f, 2) (Snd (pack2op $*⋎d)) (Snd (pack2op $*⋎c))
	⇔ ∀x y⦁ x ∈ D ∧ y ∈ D ⇒ f (x *⋎d y) = (f x) *⋎c (f y)⌝);
a (REPEAT ∀_tac);
a (rewrite_tac [OpRespect_def, pack2op_def, sets_ext_clauses, ∈_in_clauses, FunImage_def]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (spec_nth_asm_tac 3 ⌜λn⦁ if n=0 then x else y⌝);
(* *** Goal "1.1" *** *)
a (DROP_ASM_T ⌜a < 2⌝ (strip_asm_tac o less_cases_rule) THEN all_var_elim_asm_tac);
(* *** Goal "1.1.1" *** *)
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule[])) THEN all_var_elim_asm_tac);
(* *** Goal "1.1.2" *** *)
a (DROP_NTH_ASM_T 2 (strip_asm_tac o (rewrite_rule[])) THEN all_var_elim_asm_tac);
(* *** Goal "1.2" *** *)
a (POP_ASM_T ante_tac THEN rewrite_tac[]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 1 ⌜g 0⌝);
(* *** Goal "2.1" *** *)
a (spec_nth_asm_tac 1 ⌜0⌝);
a (POP_ASM_T ante_tac THEN PC_T1 "lin_arith" rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (spec_nth_asm_tac 2 ⌜g 1⌝);
(* *** Goal "2.2.1" *** *)
a (spec_nth_asm_tac 1 ⌜1⌝);
a (POP_ASM_T ante_tac THEN PC_T1 "lin_arith" rewrite_tac[]);
(* *** Goal "2.2.2" *** *)
a (all_asm_fc_tac[]);
val OpRespect_pack2op_lemma = save_pop_thm "OpRespect_pack2op_lemma";

add_pc_thms "'unalg" [OpRespect_pack0op_lemma, OpRespect_pack1op_lemma, OpRespect_pack2op_lemma];
set_merge_pcs ["rbjmisc", "'unalg"];
=TEX
}%ignore


ⓈHOLCONST
│ ⦏HomOp⦎ : ('b)STRUCT × ('b → 'c) × ('c) STRUCT → STRING → BOOL
├──────
│ ∀ A s B f⦁ HomOp (A, f, B) s ⇔
│	OpRespect (SCar A, f, Arity⋎u A s) (Oper A s) (Oper B s)
■

and the requirement that the function respects all the operators in the signature of the domain.

ⓈHOLCONST
│ ⦏HomOps⦎ : ('b)STRUCT  × ('b → 'c) × ('c) STRUCT → BOOL
├──────
│ ∀ A B f⦁ HomOps (A, f, B) ⇔ ∀s⦁ s ∈ IxDom (SOps A) ⇒ HomOp (A, f, B) s
■

=GFT
⦏HomOps_o_thm⦎ =
	⊢ ∀ A f B g C⦁ HomOps (A, f, B)
		∧ Sig A ⊑ Sig B ∧ FunClosed (A, f, B)
		∧ HomOps (B, g, C)
	⇒ HomOps (A, g o f, C)
=TEX

\ignore{
=SML
val HomOp_def = get_spec ⌜HomOp⌝;
val HomOps_def = get_spec ⌜HomOps⌝;

set_goal([], ⌜∀ A f B g C⦁ HomOps (A, f, B) ∧ Sig A ⊑ Sig B ∧ FunClosed (A, f, B) ∧ HomOps (B, g, C) ⇒ HomOps (A, g o f, C)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [OpRespect_def, HomOp_def, HomOps_def] THEN REPEAT strip_tac);
a (all_fc_tac [FunClosed_trans_thm] THEN REPEAT strip_tac);
a (ALL_ASM_FC_T rewrite_tac []);
a (rule_nth_asm_tac 2 (rewrite_rule[map_eq_sym_rule IxDom_Sig_thm]));
a (all_asm_fc_tac [IxDom_⊑_thm]);
a (rule_nth_asm_tac 1 (rewrite_rule[IxDom_Sig_thm]));
a (lemma_tac ⌜FunImage (f o g') {i|i < Arity⋎u B s} ⊆ SCar B⌝);
(* *** Goal "1" *** *)
a (ALL_FC_T (MAP_EVERY (rewrite_thm_tac o eq_sym_rule)) [SigInc_Arity⋎u_thm]);
a (rewrite_tac [FunImage_o_thm]);
a (all_fc_tac [FunImage_mono_thm]);
a (all_fc_tac [FunClosed_FunImage_thm]);
a (all_ufc_tac [⊆_trans_thm]);
(* *** Goal "2" *** *)
a (ALL_ASM_FC_T (rewrite_tac o (map(rewrite_rule[
			prove_rule [get_spec ⌜$o:(('a→'c)→(('b→'a)→('b→'c)))⌝, ext_thm] ⌜(f o g') = (λ x⦁ f (g' x))⌝
			]))) []);
val HomOps_o_thm = save_pop_thm "HomOps_o_thm";
=TEX
}%ignore

ⓈHOLCONST
│ ⦏AlgHom⦎ : ('b)STRUCT  × ('b → 'c) × ('c) STRUCT → BOOL
├──────
│ ∀ A f B⦁ AlgHom (A, f, B) ⇔
│	Sig A ⊑ Sig B ∧ FunClosed (A, f, B) ∧ HomOps (A, f, B)
■

=GFT
⦏AlgHom_o_thm⦎ =
	⊢ ∀ A f B g C⦁ AlgHom (A, f, B) ∧ AlgHom (B, g, C) ⇒ AlgHom (A, g o f, C)
=TEX

\ignore{
=SML
val AlgHom_def = get_spec ⌜AlgHom⌝;

set_goal([], ⌜∀ A f B g C⦁ AlgHom (A, f, B) ∧ AlgHom (B, g, C) ⇒ AlgHom (A, g o f, C)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [AlgHom_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [IxInc_trans_thm]);
(* *** Goal "2" *** *)
a (all_fc_tac [FunClosed_trans_thm]);
(* *** Goal "3" *** *)
a (all_fc_tac [HomOps_o_thm]);
val AlgHom_o_thm = save_pop_thm "AlgHom_o_thm";

=IGN
set_goal([], ⌜∀ A f B g C⦁ HomOps (MkSTRUCT D (IxPack [("a", pack0op c);("b", pack0op d)]), f, B)⌝);
a (rewrite_tac [HomOps_def, HomOp_def, SOps_def]);
a (REPEAT strip_tac THEN asm_rewrite_tac []);
	THEN asm_rewrite_tac[Oper_def, SOps_def, Arity⋎u_def]);
=TEX
}%ignore

\subsection{Quotients}

Given an equivalence relation which is respected by the operators in an algebra, a quotient algebra can be obtained whose objects are equivalence classes and whose operators are the operators of the original algebra lifted to operate on the equivalence classes.

The quotient operation can then be defined as follows:

ⓈHOLCONST
│ ⦏QuotientAlg⦎ : ('b)STRUCT  → ('b → 'b → BOOL) → ('b SET) STRUCT
├──────
│ ∀ A r⦁ QuotientAlg A r = MkSTRUCT (QuotientSet (SCar A) r) (IxComp (SOps A) (UniOpLift (SCar A, r)))
■

With the usual alias:

=SML
declare_alias ("/", ⌜QuotientAlg⌝);
=TEX

If an equivalence relation respects the operators in an algebra, then the quotient group will be an homomorphic image of the original algebra.
We now seek to simplify the necessary conditions on the equivalence relation.

=GFT
⦏QuotientAlg_Sig_lemma⦎ =
	⊢ ∀ A r⦁ Sig A ⊑ Sig (QuotientAlg A r)

⦏AlgHom_EquivClass_HomOps_lemma⦎ =
	⊢ AlgHom (A, EquivClass (SCar A, r), QuotientAlg A r)
		⇔ HomOps (A, EquivClass (SCar A, r), QuotientAlg A r)
=TEX

\ignore{
=SML
val QuotientAlg_def = get_spec ⌜QuotientAlg⌝;

set_goal([], ⌜∀A r⦁ Sig A ⊑ Sig (QuotientAlg A r)⌝);
a (rewrite_tac [QuotientAlg_def, IxComp_def]);
a (split_pair_rewrite_tac [⌜ValueOf (SOps A x)⌝] [UniOpLift_def]);
a (rewrite_tac [Sig_def, SOps_def, IxCompIx_def, IxInc_def, UniOpLift_def]);
a (REPEAT ∀_tac);
a (cond_cases_tac ⌜SOps A x = Undefined⌝);
val QuotientAlg_Sig_lemma = save_pop_thm "QuotientAlg_Sig_lemma";

set_goal([], ⌜∀A r⦁ FunClosed (A, EquivClass (SCar A, r), QuotientAlg A r)⌝);
a (rewrite_tac [QuotientAlg_def, FunClosed_def, SOps_def, get_spec ⌜QuotientSet⌝]);
a (REPEAT strip_tac);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[get_spec ⌜EquivClass⌝]);
val FunClosed_EquivClass_lemma = save_pop_thm "FunClosed_EquivClass_lemma";

set_goal([], ⌜∀A r⦁ AlgHom (A, EquivClass (SCar A, r), QuotientAlg A r) ⇔ HomOps (A, EquivClass (SCar A, r), QuotientAlg A r)⌝);
a (rewrite_tac [AlgHom_def, QuotientAlg_Sig_lemma, FunClosed_EquivClass_lemma]);
val AlgHom_EquivClass_HomOps_lemma = save_pop_thm "AlgHom_EquivClass_HomOps_lemma";
=TEX
}%ignore


\subsection{Algebraic Equations}

Algebraic equations in an algebra are preserved under homomorphism.

To prove this general claim we must first define the concept of an algebraic equation, which will be done inductively.
We need to be able to talk about the same algebraic equation over two distinct algebras so the notion will be parameterised by an algebra.

We will represent an expression over an algebra by a function from a valuation of variables to a value.
We generate the expressions for a specific ``signature''.
The signature is just a triple giving the number of 0-ary, 1-ary and 2-ary operations in the algebra.

=SML
declare_type_abbrev("EXPR", ["'a"], ⓣ('a) STRUCT → ((ℕ → 'a) → 'a)⌝);
=TEX

There is no syntax in this account of polynomials, so the list is a list of the values of the variables.

An equation is a pair of polynomials.

To define the set of polynomials we first define the ways in which new polynomials can be constucted from a set already to hand.
This is by the use of any of the operations in the algebra, and the operation involved is functional composition.

ⓈHOLCONST
│ ⦏VExpr⦎ : ℕ → 'a EXPR
├──────
│ ∀n⦁ VExpr n = λa va⦁ va n
■

ⓈHOLCONST
│ ⦏VExprs⦎ : ℕ → 'a EXPR SET
├──────
│ ∀n⦁ VExprs n = {p | ∃m⦁ m < n ∧ p = VExpr m}
■

ⓈHOLCONST
│ ⦏CExprs⦎ : SIG → 'a EXPR SET → 'a EXPR SET
├──────
│ ∀sig es⦁ CExprs sig es = {e | ∃name arity am⦁
│		name ∈ IxDom sig ∧ sig name = Value arity
│	∧	(∀i⦁ i < arity ⇒ am i ∈ es)
│	∧	e = λstruct va⦁  (Snd (ValueOf (SOps struct name))) (λi⦁ am i struct va)}
■

Now we define closure under the above operators.

ⓈHOLCONST
│ ⦏ExprClosed⦎ : SIG → 'a EXPR SET → BOOL
├──────
│ ∀s es⦁ ExprClosed s es ⇔ CExprs s es ⊆ es
■

ⓈHOLCONST
│ ⦏Exprs⦎ : SIG → ℕ → 'a EXPR SET
├──────
│ ∀s n⦁ Exprs s n = ⋂{ps | ExprClosed s ps ∧ VExprs n ⊆ ps}
■


\ignore{
=SML
commit_pc "'unalg";

force_new_pc "⦏unalg⦎";
merge_pcs ["rbjmisc", "'unalg"] "unalg";
commit_pc "unalg";

force_new_pc "⦏unalg1⦎";
merge_pcs ["rbjmisc1", "'unalg"] "unalg1";
commit_pc "unalg1";
=TEX
}%ignore


\section{Lattices (I)}

The beginnings of a theory of lattices.
This version was done before the work on Univesal Algebra, and will be discarded if the later version conformant with that theory is found satisfactory.

=SML
open_theory "unalg";
force_new_theory "lattice";
force_new_pc ⦏"'lattice"⦎;
merge_pcs ["'prove_∃_⇒_conv", "'savedthm_cs_∃_proof"] "'lattice";
set_merge_pcs ["unalg", "'lattice"];
=TEX

=SML
set_merge_pcs ["hol", "'rbjmisc"] ;
=TEX

\subsection{Signature and Defining Property}

We will represent a lattice as a triple comprising a carrier set and two-argument join and meet functions.

ⓈHOLLABPROD ⦏LAT⦎───────────────
│	⦏Car⋎L⦎			: 'a SET;
│	⦏Join⋎L⦎			: 'a → 'a → 'a;
│	⦏Meet⋎L⦎		: 'a → 'a → 'a
■─────────────────────────────

We will use L and M as variables for lattices and the following infixity declarations will be useful as names for the corresponding operations.

=SML
declare_infix (235, "∨⋎L");
declare_infix (235, "∨⋎M");
declare_infix (240, "∧⋎L");
declare_infix (240, "∧⋎M");
=TEX

ⓈHOLCONST
│ ⦏IsLattice⦎ : 'a LAT → BOOL
├──────
│ ∀ L⦁	IsLattice L ⇔ ∀ C $∨⋎L $∧⋎L⦁ MkLAT C $∨⋎L $∧⋎L = L ⇒ 
│       (∀x y⦁ x ∈ C ∧ y ∈ C ⇒
		x ∨⋎L y ∈ C ∧ x ∧⋎L y ∈ C
	∧	x ∨⋎L y = y ∨⋎L x ∧ x ∧⋎L y = y ∧⋎L x
	∧	x ∧⋎L (x ∨⋎L y) = x ∧ x ∨⋎L (x ∧⋎L y) = x
        ∧ (∀z⦁ z ∈ C
		⇒	(x ∨⋎L y) ∨⋎L z = x ∨⋎L (y ∨⋎L z)
		∧	(x ∧⋎L y) ∧⋎L z = x ∧⋎L (y ∧⋎L z)))
■

\subsection{Elementary Theorems}

=GFT
⦏∧⋎L_idempot_thm⦎ =
   ⊢ ∀ L
     ⦁ IsLattice L ⇒ (∀ C $∨⋎L $∧⋎L⦁ MkLAT C $∨⋎L $∧⋎L = L
        ⇒ (∀ x⦁ x ∈ C ⇒ x ∧⋎L x = x))

⦏∧⋎L_idempot_thm⦎ =
   ⊢ ∀ L⦁ IsLattice L ⇒ (∀ C $∨⋎L $∧⋎L⦁ MkLAT C $∨⋎L $∧⋎L = L
	⇒ (∀ x⦁ x ∈ C ⇒ x ∨⋎L x = x))
=TEX

\ignore{
=SML
val lattice_def = get_spec ⌜IsLattice⌝;

set_goal([], ⌜∀L⦁ IsLattice L ⇒ ∀ C $∨⋎L $∧⋎L⦁ MkLAT C $∨⋎L $∧⋎L = L ⇒
	∀x⦁ x ∈ C ⇒ x ∧⋎L x = x⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜x ∧⋎L x ∈ C⌝ THEN1 all_ufc_tac [lattice_def]);
a (lemma_tac ⌜x ∧⋎L (x ∨⋎L x ∧⋎L x) = x⌝ THEN1 all_ufc_tac [lattice_def]);
a (lemma_tac ⌜x ∨⋎L x ∧⋎L x = x⌝ THEN1 all_ufc_tac [lattice_def]);
a (DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[]);
val ∧⋎L_idempot_thm = save_pop_thm "∧⋎L_idempot_thm";

set_goal([], ⌜∀L⦁ IsLattice L ⇒ ∀ C $∨⋎L $∧⋎L⦁ MkLAT C $∨⋎L $∧⋎L = L ⇒
	∀x⦁ x ∈ C ⇒ x ∨⋎L x = x⌝);
a (REPEAT_N 8 strip_tac);
a (lemma_tac ⌜x ∨⋎L x ∈ C⌝ THEN1 all_ufc_tac [lattice_def]);
a (lemma_tac ⌜x ∨⋎L (x ∧⋎L (x ∨⋎L x)) = x⌝ THEN1 all_ufc_tac [lattice_def]);
a (lemma_tac ⌜x ∧⋎L (x ∨⋎L x) = x⌝ THEN1 all_ufc_tac [lattice_def]);
a (DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[]);
val ∨⋎L_idempot_thm = save_pop_thm "∨⋎L_idempot_thm";

=TEX
}%ignore

\subsection{Quotient Lattices}

The quotient of a lattice with respect to some equivalence relation over its elements is defined as follows:

ⓈHOLCONST
│ ⦏QuotientLattice⦎ : 'a LAT → ('a → 'a → BOOL) → 'a SET LAT
├──────
│ ∀ L $≡⋎d⦁ QuotientLattice L $≡⋎d =
│	let D = (Car⋎L L, $≡⋎d)
│	in let $∨⋎L = (Join⋎L L) DyOpLift D and $∧⋎L = (Meet⋎L L) DyOpLift D
│	   in MkLAT (EquivClasses D) $∨⋎L $∧⋎L
■

=SML
declare_alias ("/", ⌜QuotientLattice⌝);
=TEX

-GFT
=TEX

\ignore{
=IGN
val QuotientLattice_def = get_spec ⌜QuotientLattice⌝;

set_goal([], ⌜∀L $≡⋎d⦁ IsLattice L ∧ Equiv (Car⋎L L, $≡⋎d) ⇒ IsLattice (L / $≡⋎d)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [lattice_def, QuotientLattice_def, let_def] THEN REPEAT strip_tac);
=TEX
}%ignore

\subsection{Lattice Orders}


=SML
declare_infix (210, "≤⋎L");
declare_infix (210, "≤⋎M");
=TEX

The ordering on the lattice is derived from the operations as follows,

ⓈHOLCONST
│ ⦏LeLat⦎ : 'a LAT → 'a → 'a → BOOL
├──────
│ ∀ L:'a LAT⦁ LeLat L = λx y⦁  ∀$∨⋎L⦁ $∨⋎L = Join⋎L L ⇒ x ∨⋎L y = y
■

=GFT
=TEX

\ignore{
=IGN
set_goal([],⌜∀L⦁ IsLattice L ⇒ PartialOrder (Car⋎L L, LeLat L)⌝);
a ((rewrite_tac (map get_spec [⌜PartialOrder⌝, ⌜Trans⌝, ⌜Antisym⌝, ⌜LeLat⌝])));
a ((REPEAT strip_tac));
a (asm_fc_tac[]);
a (MAP_EVERY (fn x => ∃_tac x THEN strip_tac) [⌜C⌝, ⌜$∨⋎L⌝, ⌜$∧⋎L⌝]);
a (asm_rewrite_tac[]);

=TEX
}%ignore

\section{Lattices (II)}

The beginnings of another theory of lattices.
This version was done using Universal Algebra, the previous version will be discarded if this version conformant with the approach to universal algebra is found satisfactory.

=SML
open_theory "unalg";
force_new_theory "latt2";
force_new_pc ⦏"'latt2"⦎;
merge_pcs ["'prove_∃_⇒_conv", "'savedthm_cs_∃_proof"] "'latt2";
set_merge_pcs ["unalg", "'latt2"];
=TEX

\subsection{Signature and Defining Property}

We will use the general structure type \emph{STRUCT} to represent lattice structures.

ⓈHOLCONST
│ ⦏LatSig⦎ : SIG
├──────
│ LatSig = IxPack [("∨⋎L" , 2); ("∨⋎L" , 2)]
■

We will use L and M as variables for lattices and the following infixity declarations will be useful as names for the corresponding operations.

=SML
declare_infix (235, "∨⋎L");
declare_infix (235, "∨⋎M");
declare_infix (240, "∧⋎L");
declare_infix (240, "∧⋎M");
=TEX

ⓈHOLCONST
│ ⦏MkLat⦎ : 'a SET → ('a → 'a → 'a) → ('a → 'a → 'a) → ('a) STRUCT
├──────
│ ∀ C $∨⋎L $∧⋎L⦁ MkLat C $∨⋎L $∧⋎L = MkSTRUCT C (IxPack [("∨⋎L" , pack2op $∨⋎L); ("∧⋎L" , pack2op $∧⋎L)])
■

ⓈHOLCONST
│ ⦏IsLat⦎ : ('a) STRUCT → BOOL
├──────
│ ∀ L⦁	IsLat L ⇔ ∀ C $∨⋎L $∧⋎L⦁ StructInc (MkLat C $∨⋎L $∧⋎L) L ⇒ 
│       (∀x y⦁ x ∈ C ∧ y ∈ C ⇒
		x ∨⋎L y ∈ C ∧ x ∧⋎L y ∈ C
	∧	x ∨⋎L y = y ∨⋎L x ∧ x ∧⋎L y = y ∧⋎L x
	∧	x ∧⋎L (x ∨⋎L y) = x ∧ x ∨⋎L (x ∧⋎L y) = x
        ∧ (∀z⦁ z ∈ C
		⇒	(x ∨⋎L y) ∨⋎L z = x ∨⋎L (y ∨⋎L z)
		∧	(x ∧⋎L y) ∧⋎L z = x ∧⋎L (y ∧⋎L z)))
■

\subsection{Pattern Matching}

We now add the the existence proof context the theorem necessary to allow function definitions which pattern-match on patterns formed by \emph{MkLat}.
The proof of the theorem is now automatic, from the specification of \emph{MkLat}.

=SML
val MkLat_∃_lemma = make_alg_∃_thm ⌜MkLat⌝;
=TEX

=GFT
⦏MkLat_∃_lemma⦎ =
	⊢ ∀ cf⦁ ∃ f⦁ ∀ C $∨⋎L $∧⋎L⦁ f (MkLat C $∨⋎L $∧⋎L) = cf C $∨⋎L $∧⋎L
=TEX

\ignore{
=SML
val MkLat_def = get_spec ⌜MkLat⌝;
val IsLat_def = get_spec ⌜IsLat⌝;
val LatSig_def = get_spec ⌜LatSig⌝;
=TEX
}%ignore

This gets plugged into proof context {\it 'latt2} for use in consistency proofs.

=SML
add_∃_cd_thms [MkLat_∃_lemma] "'latt2";
set_merge_pcs ["unalg", "'latt2"];
=TEX

\subsection{Lattice Ordering}

Well try out the pattern matching definition by defining the ordering on a lattice.

ⓈHOLCONST
│ ⦏LeLat⦎ : 'a STRUCT → 'a → 'a → BOOL
├──────
│ ∀C $∨⋎L $∧⋎L⦁ LeLat (MkLat C $∨⋎L $∧⋎L) = λx y⦁ x ∨⋎L y = y
■

\subsection{Elementary Theorems}

=GFT
⦏∧⋎L_idempot_thm⦎ =
   ⊢ ∀ L⦁ IsLat L ⇒ (∀ C $∨⋎L $∧⋎L⦁ MkLat C $∨⋎L $∧⋎L ⊑ L
	⇒ (∀ x⦁ x ∈ C ⇒ x ∧⋎L x = x))

⦏∨⋎L_idempot_thm⦎ =
   ⊢ ∀ L⦁ IsLat L ⇒ (∀ C $∨⋎L $∧⋎L⦁ MkLat C $∨⋎L $∧⋎L ⊑ L
	⇒ (∀ x⦁ x ∈ C ⇒ x ∨⋎L x = x))
=TEX

\ignore{
=SML
set_goal([], ⌜∀L⦁ IsLat L ⇒ ∀ C $∨⋎L $∧⋎L⦁ StructInc (MkLat C $∨⋎L $∧⋎L) L ⇒
	∀x⦁ x ∈ C ⇒ x ∧⋎L x = x⌝);
a (REPEAT strip_tac);
a (lemma_tac ⌜x ∧⋎L x ∈ C⌝ THEN1 all_ufc_tac [IsLat_def]);
a (lemma_tac ⌜x ∧⋎L (x ∨⋎L x ∧⋎L x) = x⌝ THEN1 all_ufc_tac [IsLat_def]);
a (lemma_tac ⌜x ∨⋎L x ∧⋎L x = x⌝ THEN1 all_ufc_tac [IsLat_def]);
a (DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[]);
val ∧⋎L_idempot_thm1 = save_pop_thm "∧⋎L_idempot_thm1";

set_goal([], ⌜∀L⦁ IsLat L ⇒ ∀ C $∨⋎L $∧⋎L⦁ StructInc (MkLat C $∨⋎L $∧⋎L) L ⇒
	∀x⦁ x ∈ C ⇒ x ∨⋎L x = x⌝);
a (REPEAT_N 8 strip_tac);
a (lemma_tac ⌜x ∨⋎L x ∈ C⌝ THEN1 all_ufc_tac [IsLat_def]);
a (lemma_tac ⌜x ∨⋎L (x ∧⋎L (x ∨⋎L x)) = x⌝ THEN1 all_ufc_tac [IsLat_def]);
a (lemma_tac ⌜x ∧⋎L (x ∨⋎L x) = x⌝ THEN1 all_ufc_tac [IsLat_def]);
a (DROP_NTH_ASM_T 2 ante_tac THEN asm_rewrite_tac[]);
val ∨⋎L_idempot_thm1 = save_pop_thm "∨⋎L_idempot_thm1";
=TEX
}%ignore

\subsection{Homomorphisms}

I am hoping that results from Univeral Algebra will not prove difficult to instantiate to Lattice theory.

Let us define a Lattice homomorphism as a homomorphism whose source is a lattice.

ⓈHOLCONST
│ ⦏LatHom⦎ : (('a) STRUCT × ('a → 'b) × 'b STRUCT) → BOOL
├──────
│ ∀ A f B⦁ LatHom (A, f, B) ⇔ AlgHom (A, f, B) ∧ Sig A = LatSig
■

=GFT
⦏LatHom_o_thm⦎ =
	⊢ ∀ A f B g C⦁ LatHom (A, f, B) ∧ AlgHom (B, g, C) ⇒ LatHom (A, g o f, C)

⦏Latt_HomOps_lemma⦎ =
	⊢ ∀ C $∨⋎L $∧⋎L f D $∨⋎M $∧⋎M⦁ HomOps (MkLat C $∨⋎L $∧⋎L, f, MkLat D $∨⋎M $∧⋎M)
         ⇔ (∀ x y⦁ x ∈ C ∧ y ∈ C ⇒ f (x ∧⋎L y) = f x ∧⋎M f y)
           ∧ (∀ x y⦁ x ∈ C ∧ y ∈ C ⇒ f (x ∨⋎L y) = f x ∨⋎M f y)
=TEX

\ignore{
=SML
val LatHom_def = get_spec ⌜LatHom⌝;

set_goal([], ⌜∀A f B g C⦁ LatHom (A,f,B) ∧ AlgHom (B,g,C) ⇒ LatHom (A, g o f, C)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [LatHom_def] THEN REPEAT strip_tac THEN all_fc_tac [AlgHom_o_thm]);
val LatHom_o_thm = save_pop_thm "LatHom_o_thm";

set_goal([], ⌜∀ C $∨⋎L $∧⋎L f D $∨⋎M $∧⋎M⦁ HomOps (MkLat C $∨⋎L $∧⋎L, f, MkLat D $∨⋎M $∧⋎M) ⇔
		(∀ x y⦁ x ∈ C ∧ y ∈ C ⇒ f (x ∧⋎L y) = f x ∧⋎M f y)
	∧	(∀ x y⦁ x ∈ C ∧ y ∈ C ⇒ f (x ∨⋎L y) = f x ∨⋎M f y)
⌝);
a (REPEAT ∀_tac THEN rewrite_tac [HomOps_def, MkLat_def, SOps_def]);
a (REPEAT ∈_disp_⇒_tac);
a (rewrite_tac[HomOp_def, SOps_def]);
a (REPEAT strip_tac THEN all_asm_fc_tac[]);
val Latt_HomOps_lemma = save_pop_thm "Latt_HomOps_lemma";
=TEX
}%ignore

\subsection{Quotient Lattices}

A quotient lattice requires no special definition, it is simply a \emph{QuotientAlg} of a lattice.
However, as in the case of the homomorphism, it is convenient to have the conditions expressed explicitly in terms of the lattice operations.

=GFT
=TEX

\ignore{
=IGN
set_goal([], ⌜∀C $∨⋎L $∧⋎L r⦁ AlgHom (MkLat C $∨⋎L $∧⋎L, EquivClass (C, r), QuotientAlg (MkLat C $∨⋎L $∧⋎L) r)⌝);
a (REPEAT ∀_tac);
a (LEMMA_T ⌜(C, r) = (SCar(MkLat C $∨⋎L $∧⋎L), r)⌝ rewrite_thm_tac THEN1 rewrite_tac[MkLat_def, SOps_def]);
a (rewrite_tac [AlgHom_EquivClass_HomOps_lemma, SOps_def, QuotientAlg_def, MkLat_def, IxComp_IxPack_thm]);
a (rewrite_tac [map_def, rewrite_rule [MkLat_def] Latt_HomOps_lemma]);


=TEX
}%ignore


\ignore{
=SML
commit_pc "'latt2";

force_new_pc "⦏latt2⦎";
merge_pcs ["unalg", "'latt2"] "latt2";
commit_pc "latt2";

force_new_pc "⦏latt21⦎";
merge_pcs ["unalg1", "'latt2"] "latt21";
commit_pc "latt21";
=TEX
}%ignore

\section{Conclusions}
