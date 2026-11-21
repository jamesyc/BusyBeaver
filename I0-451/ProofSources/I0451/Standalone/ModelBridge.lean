module
public import I0451.Standalone.SetModel
public import I0451.Logic.NameParameters
public import I0451.Logic.ZFModel

/-! The standalone membership models are exactly the models of
Foundation's ZF. The equivalence covers all instances of separation
and replacement, with arbitrary finite parameters. -/
@[expose] public section
namespace I0451.Standalone

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.Logic (NamedFormula)
open I0451.Logic.NamedFormula

variable {V : Type} [SetStructure V]

private theorem eval_eq (p : NamedFormula) (s : Nat → V) :
    eval (fun x y : V => x ∈ y) s p ↔ p.eval s := by
  induction p generalizing s with
  | truth | falsity | mem | equal => rfl
  | imp a b ha hb => exact (ha s).imp (hb s)
  | all a b ih =>
    simp only [eval, NamedFormula.eval]
    exact forall_congr' fun x => ih (assign s a x)

private theorem separation_def (p : NamedFormula) (s : Nat → V) (label : Nat) :
    ℒₛₑₜ-predicate (fun x => eval (fun u v : V => u ∈ v) (assign s label x) p) := by
  let terms (i : Nat) : SetTheorySemiterm V 1 :=
    if i = label then #0 else &(s i)
  refine ⟨p.toSet terms, fun env => ?_⟩
  have values : (fun i => (terms i).val env id) = assign s label (env 0) := by
    funext i
    by_cases eq : i = label <;> simp [terms,assign,eq]
  rw [toSet_eval, values]
  exact (eval_eq p _).symm

private theorem replacement_def (p : NamedFormula) (s : Nat → V) (a b : Nat) :
    ℒₛₑₜ-relation (fun x y => eval (fun u v : V => u ∈ v) (assign (assign s a x) b y) p) := by
  let terms (i : Nat) : SetTheorySemiterm V 2 :=
    if i = b then #1 else if i = a then #0 else &(s i)
  refine ⟨p.toSet terms, fun env => ?_⟩
  have values : (fun i => (terms i).val env id) = assign (assign s a (env 0)) b (env 1) := by
    funext i
    by_cases eqB : i = b
    · simp only [terms, assign, eqB, ite_true, Semiterm.val_bvar]
    · by_cases eqA : i = a
      · subst i
        simp [terms,assign,eqB]
      · simp [terms,assign,eqB,eqA]
  rw [toSet_eval, values]
  exact (eval_eq p _).symm

theorem model_of_zf [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    Model (fun x y : V => x ∈ y) := by
  constructor
  · exact ⟨∅, by simp⟩
  · exact fun _ _ => mem_ext_iff.mpr
  · exact fun a b => ⟨{a,b}, by simp⟩
  · exact fun a => ⟨⋃ˢ a, fun _ => mem_sUnion_iff⟩
  · exact fun a => ⟨℘ a, fun _ => mem_power_iff⟩
  · refine ⟨ω, ?_, ?_⟩
    · intro z noMember
      have eq : z = (∅ : V) := mem_ext_iff.mpr fun x => iff_of_false (noMember x) (by simp)
      exact eq.symm ▸ empty_mem_ω
    · intro a aIn b spec
      have eq : b = succ a := mem_ext_iff.mpr fun x => (spec x).trans mem_succ_iff.symm
      exact eq.symm ▸ ω_succ_closed aIn
  · exact I0451.Logic.ZFModel.foundation
  · intro p s label A
    exact separation_exists A _ (separation_def p s label)
  · intro p s a b R total A
    exact replacement_rel_exists A R (by simpa only [ExistsUnique] using total) (replacement_def p s a b)

private theorem separation_of_model [Nonempty V] (M : Model (fun x y : V => x ∈ y))
    (P : V → Prop) (defP : ℒₛₑₜ-predicate P) (A : V) :
    ∃ B : V, ∀ y : V, y ∈ B ↔ y ∈ A ∧ P y := by
  have bin : ℒₛₑₜ-relation (fun x (_ : V) => P x) := by definability
  obtain ⟨f,s,_,_,reads⟩ := name_definable_relation (fun x (_ : V) => P x) bin A
  have picture (x : V) : eval (fun u v : V => u ∈ v) (assign s 1 x) f ↔ P x := by
    have h := reads x (s 2)
    have same : assign (assign s 1 x) 2 (s 2) = assign s 1 x := by
      funext i
      by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;> simp_all [assign]
    rw [← same]
    exact (eval_eq f _).trans h
  simpa only [picture] using M.separation f s 1 A

private theorem replacement_of_model [Nonempty V] (M : Model (fun x y : V => x ∈ y))
    (R : V → V → Prop) (defR : ℒₛₑₜ-relation R) (total : ∀ x, ∃! y, R x y) (A : V) :
    ∃ B : V, ∀ y : V, y ∈ B ↔ ∃ x ∈ A, R x y := by
  obtain ⟨f,s,_,_,reads⟩ := name_definable_relation R defR A
  have same (x y : V) : eval (fun u v : V => u ∈ v) (assign (assign s 1 x) 2 y) f ↔ R x y :=
    (eval_eq f _).trans (reads x y)
  simpa only [same] using M.replacement f s 1 2 (by simpa only [same, ExistsUnique] using total) A

theorem zf_of_model [Nonempty V] (M : Model (fun x y : V => x ∈ y)) : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  constructor
  rintro σ ((base | sep) | repl)
  · cases base with
    | equality _ h => exact Theory.models V (𝗘𝗤 ℒₛₑₜ) h
    | empty_set => simpa [models_iff,isEmpty,Rew.q_subst,Matrix.comp_vecCons',Function.comp_def] using M.empty
    | extensionality =>
      simp [models_iff]
      intro x y
      exact ⟨fun eq z => eq ▸ Iff.rfl, M.extensionality x y⟩
    | pairing => simpa [models_iff] using M.pairing
    | union => simpa [models_iff] using M.union
    | power_set =>
      simp [models_iff]
      intro a
      obtain ⟨z, meaning⟩ := M.power a
      exact ⟨z, fun q => (meaning q).trans Iff.rfl⟩
    | infinity =>
      simpa [models_iff,isEmpty,isSucc,Rew.q_subst,Matrix.comp_vecCons',Function.comp_def] using M.infinity
    | foundation =>
      simp [models_iff,isNonempty,Rew.q_subst,Matrix.comp_vecCons',Function.comp_def]
      intro a w wa
      obtain ⟨x, belongs, well⟩ := M.foundation a ⟨w,wa⟩
      exact ⟨x,belongs,fun y ya yx => well y yx ya⟩
  · cases sep with
    | separation φ =>
      simp [models_iff, Axiom.separationSchema, Semiformula.eval_univCl, Matrix.comp_vecCons', Function.comp_def]
      intro s A
      have defP : ℒₛₑₜ-predicate (fun x : V => φ.Eval (fun _ => x) s) := by
        refine ⟨(Rew.rewriteMap s) ▹ φ, fun v => ?_⟩
        rw [Semiformula.eval_rewriteMap, Matrix.fun_eq_vec_one v]
        simp [Matrix.vec_single_eq_const]
      exact separation_of_model M _ defP A
  · cases repl with
    | replacement φ =>
      simp [models_iff, Axiom.replacementSchema, Semiformula.eval_univCl, Matrix.comp_vecCons', Function.comp_def]
      intro s total A
      have defR : ℒₛₑₜ-relation (fun x y : V => φ.Eval (x :> fun _ : Fin 1 => y) s) := by
        refine ⟨(Rew.rewriteMap s) ▹ φ, fun v => ?_⟩
        rw [Semiformula.eval_rewriteMap, Matrix.fun_eq_vec_two v]
        simp [Matrix.vec_single_eq_const]
      exact replacement_of_model M _ defR total A

/-- Close the named translation of a membership sentence. The
additional quantifiers merely bind external variable labels. -/
def ofFoundationSentence (φ : SetTheorySentence) : NamedFormula :=
  let source := fromSet (Rewriting.emb φ : SetTheoryProposition) Fin.elim0 0
  source.closeOver source.labels

theorem ofFoundationSentence_closed (φ : SetTheorySentence) :
    (ofFoundationSentence φ).freeLabels = [] := by
  exact List.eq_nil_iff_forall_not_mem.mpr (closed_names _)

theorem ofFoundationSentence_eval [Nonempty V] (φ : SetTheorySentence) (s : Nat → V) :
    eval (fun x y : V => x ∈ y) s (ofFoundationSentence φ) ↔ V↓[ℒₛₑₜ] ⊧ φ := by
  let source := fromSet (Rewriting.emb φ : SetTheoryProposition) Fin.elim0 0
  have evaluates (env : Nat → V) : source.eval env ↔ V↓[ℒₛₑₜ] ⊧ φ := by
    unfold source
    have h := fromSet_eval (Rewriting.emb φ : SetTheoryProposition) Fin.elim0 0
      (fun i => i.elim0) env
    simpa [Semiformula.eval_emb, models_iff, Semiformula.Realize, Matrix.empty_eq] using h
  rw [eval_eq]
  change (source.closeOver source.labels).eval s ↔ _
  rw [eval_closeOver, show (∀ t : Nat → V, (∀ i ∉ source.labels, s i = t i) → source.eval t) ↔
      (∀ t : Nat → V, (∀ i ∉ source.labels, s i = t i) → V↓[ℒₛₑₜ] ⊧ φ) by
    simp only [evaluates]]
  exact ⟨fun h => h s (fun _ _ => rfl), fun h _ _ => h⟩

theorem choice_iff [Nonempty V] :
    Choice (fun x y : V => x ∈ y) ↔ V↓[ℒₛₑₜ] ⊧ Axiom.choice := by
  simp [Choice, Axiom.choice, models_iff, isNonempty, ExistsUnique,
    Rew.q_subst, Matrix.comp_vecCons', Function.comp_def, and_imp, and_assoc]
  constructor
  · intro selects F nonempty disjoint
    exact selects F nonempty (fun A B aF bF x xA xB => disjoint A aF B bF x xA xB)
  · intro selects F nonempty disjoint
    exact selects F nonempty (fun A aF B bF x xA xB => disjoint A B aF bF x xA xB)

end I0451.Standalone
