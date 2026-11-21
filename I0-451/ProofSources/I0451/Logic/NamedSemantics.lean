module
public import I0451.Logic.CloseNamed

/-! The named and set-language interpretations of the native axioms.
A closed sentence ranges over every assignment of the original names. -/
@[expose] public section
namespace I0451.Logic.NamedFormula

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type} [Tarski.Structure ℒₛₑₜ V]

def eval (s : Nat → V) : NamedFormula → Prop
  | .truth => True
  | .falsity => False
  | .mem a b => Tarski.Structure.rel (L := ℒₛₑₜ) Language.Set.Rel.mem ![s a,s b]
  | .equal a b => Tarski.Structure.rel (L := ℒₛₑₜ) Language.Set.Rel.eq ![s a,s b]
  | .imp a b => eval s a → eval s b
  | .all a b => ∀ x, eval (assign s a x) b

theorem eval_depends {s t : Nat → V} (f : NamedFormula)
    (same : ∀ i ∈ f.freeLabels, s i = t i) : f.eval s ↔ f.eval t := by
  induction f generalizing s t with
  | truth | falsity => rfl
  | mem a b | equal a b =>
    simp only [eval]
    rw [same a (by simp [freeLabels]), same b (by simp [freeLabels])]
  | imp a b ha hb =>
    simp only [eval]
    exact (ha fun i h => same i (List.mem_append_left _ h)).imp
      (hb fun i h => same i (List.mem_append_right _ h))
  | all a f ih =>
    simp only [eval]
    refine forall_congr' fun x => ih ?_
    intro i used
    by_cases bound : i = a
    · simp [assign,bound]
    · simp [assign,bound,same i (freeLabels_all.mpr ⟨used,bound⟩)]

theorem toSet_eval {ξ : Type} {n : Nat} (terms : Nat → Semiterm ℒₛₑₜ ξ n)
    (bound : Fin n → V) (free : ξ → V) (f : NamedFormula) :
    (f.toSet terms).Eval bound free ↔ f.eval (fun i => (terms i).val bound free) := by
  induction f generalizing n with
  | truth | falsity => rfl
  | mem a b | equal a b =>
    simp [toSet, eval, Semiformula.eval_rel, Function.comp_def, Matrix.comp_vecCons', Matrix.vec_single_eq_const]
  | imp a b ha hb => simp [toSet, eval, ha, hb]
  | all x f ih =>
    simp only [toSet, eval, Semiformula.eval_all]
    apply forall_congr'
    intro y
    rw [ih, SetSyntax.bindTerms_values terms x bound free y]

theorem eval_closeOver (names : List Nat) (f : NamedFormula) (s : Nat → V) :
    (f.closeOver names).eval s ↔
      ∀ t : Nat → V, (∀ label, label ∉ names → s label = t label) → f.eval t := by
  induction names generalizing s with
  | nil =>
    simp [closeOver]
    exact ⟨fun proof t agrees => (f.eval_depends (fun x _ => agrees x)).mp proof,
      fun each => each s (fun _ => rfl)⟩
  | cons a rest ih =>
    simp only [closeOver, List.foldr_cons, eval]
    constructor
    · intro closed t agrees
      exact (ih (assign s a (t a))).mp (closed (t a)) t fun i notIn => by
        by_cases same : i = a
        · simp [assign,same]
        · simpa [assign,same] using
            (agrees i (fun contains => (List.mem_cons.mp contains).elim same notIn))
    · intro holds x
      apply (ih (assign s a x)).mpr
      intro t agrees
      apply holds t
      intro i outside
      have notA : i ≠ a := fun eq => outside (List.mem_cons.mpr (.inl eq))
      have notRest : i ∉ rest := fun mem => outside (List.mem_cons.mpr (.inr mem))
      simpa [assign,notA] using agrees i notRest

theorem closedSentence_models [Nonempty V] (f : NamedFormula) :
    V↓[ℒₛₑₜ] ⊧ f.closedSentence ↔ ∀ s : Nat → V, f.eval s := by
  let any : Nat → V := fun _ => Classical.arbitrary V
  have cl : V↓[ℒₛₑₜ] ⊧ f.closedSentence ↔
      ((f.closeOver f.labels).toSet (fun i => (Semiterm.fvar i : SyntacticTerm ℒₛₑₜ))).Eval ![] any := by
    exact (Semiformula.eval_toEmpty (f := any) f.closedFormula_noFree).symm
  rw [cl, toSet_eval]
  have universal := eval_closeOver f.labels f any
  constructor
  · intro proof s
    let t (i : Nat) := if i ∈ f.labels then s i else any i
    have model := universal.mp proof t (fun i missing => by simp [t,missing])
    exact (f.eval_depends (fun i hi => by simp [t,freeLabel_is_label hi])).mp model
  · intro all
    exact universal.mpr (fun s _ => all s)

theorem fromNative_eval {W : Type} [SetStructure W] (f : I0451.Logic.Formula) (s : Nat → W) (irreflexive : ∀ x : W, x ∉ x) :
    (fromNative f).eval s ↔ f.eval (fun x y : W => x ∈ y) s := by
  induction f generalizing s with
  | truth => rfl
  | mem a b =>
    cases a <;> cases b <;> simp [fromNative, eval, I0451.Logic.Formula.eval, irreflexive] <;> rfl
  | equal a b => rfl
  | imp a b ha hb => simp [fromNative, eval, I0451.Logic.Formula.eval, ha, hb]
  | all a b ih => simp [fromNative, eval, I0451.Logic.Formula.eval, ih]

end I0451.Logic.NamedFormula
