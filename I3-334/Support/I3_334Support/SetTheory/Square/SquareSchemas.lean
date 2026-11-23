module
public import I3_334Support.SetTheory.Square.SquareChoice
public import I3_334Support.Logic.Soundness
@[expose] public section

namespace PalomarI3380.Logic

theorem bound_rename (p : Formula) {n m : Nat} {σ : Nat → Nat}
    (h : Bound p n) (map : ∀ i, i < n → σ i < m) : Bound (rename σ p) m := by
  induction p generalizing n m σ with
  | bot => trivial
  | mem i j | eq i j => exact ⟨map i h.1, map j h.2⟩
  | and p q ihp ihq | or p q ihp ihq | imp p q ihp ihq => exact ⟨ihp h.1 map, ihq h.2 map⟩
  | all p ih | ex p ih =>
    apply ih h
    intro i hi
    cases i with
    | zero => simp [lift]
    | succ i => exact Nat.succ_lt_succ (map i (by omega))

theorem eval_allPrefix {Point : Type} {E : Point → Point → Prop}
    {p : Formula} (h : ∀ s, eval E p s) (n : Nat) (s : Nat → Point) :
    eval E (allPrefix n p) s := by
  induction n generalizing s with
  | zero => exact h s
  | succ n ih => exact fun x => ih (pushValue s x)

/-- Semantic formulation of the two schemas at an arbitrary assignment
of their finite parameter list. -/
theorem eval_separation {Point : Type} {E : Point → Point → Prop} (p : Formula) (s : Nat → Point) :
    eval E (separationFormula (rename sepIndex p)) s ↔
    ∀ a, ∃ b, ∀ x, E x b ↔ E x a ∧ eval E p (pushValue s x) := by
  have renameAt (a b x : Point) :
      (pushValue (pushValue (pushValue s a) b) x) ∘ sepIndex = pushValue s x := by
    funext i
    cases i <;> rfl
  simp only [separationFormula, sourceIff, eval, NDSemantics.eval_rename, renameAt, pushValue, iff_def]

theorem eval_replacement {Point : Type} {E : Point → Point → Prop} (p : Formula) (s : Nat → Point) :
    eval E (replacementFormula (rename repAIndex p) (rename repBIndex p) (rename repCIndex p)) s ↔
    (let R := fun x y => eval E p (pushValue (pushValue s y) x)
     (∀ x y z, R x y → R x z → y = z) → ∀ a, ∃ b, ∀ y, E y b ↔ ∃ x, E x a ∧ R x y) := by
  have renameA (x y z : Point) :
      (pushValue (pushValue (pushValue s x) y) z) ∘ repAIndex = pushValue (pushValue s y) x := by
    funext i
    cases i with
    | zero => rfl
    | succ i => cases i <;> rfl
  have renameB (x y z : Point) :
      (pushValue (pushValue (pushValue s x) y) z) ∘ repBIndex = pushValue (pushValue s z) x := by
    funext i
    cases i with
    | zero => rfl
    | succ i => cases i <;> rfl
  have renameC (a b y x : Point) :
      (pushValue (pushValue (pushValue (pushValue s a) b) y) x) ∘ repCIndex =
        pushValue (pushValue s y) x := by
    funext i
    cases i with
    | zero => rfl
    | succ i => cases i <;> rfl
  simp only [replacementFormula, functionalityFormula, sourceIff, eval, NDSemantics.eval_rename,
    renameA, renameB, renameC, pushValue, iff_def]

end PalomarI3380.Logic

namespace PalomarI3380.SquareRepresentation

open Logic Manifest

variable {A Point : Type} {M : Algebra A} {S : SquareRepresentation M Point}

private theorem parameter_assignment (s : Nat → Point) (n : Nat) (x y : Point) :
    ∀ i, i < n + 2 →
      parameterEnv (List.ofFn fun i : Fin n => s i) x y i = pushValue (pushValue s y) x i := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i =>
      have inside : i < n := by omega
      change ((List.ofFn fun i : Fin n => s i)[i]?).getD x = s i
      rw [List.getElem?_eq_getElem (by simpa using inside), List.getElem_ofFn]
      rfl

theorem separation_schema (P : QuasiProjections S) (hM : M.Models preceding)
    (names : ∀ x, S.Named x) (p : Formula) (n : Nat) (bound : Bound p (n + 1)) (env : Nat → Point) :
    eval (S.rel (M.constant .E)) (separationSchema n p) env := by
  apply eval_allPrefix
  intro environment
  apply (eval_separation p environment).mpr
  intro input
  let σ : Nat → Nat := fun i => if i = 0 then 0 else i + 1
  let E := S.rel (M.constant .E)
  let params := List.ofFn fun i : Fin n => environment i
  let formula := RelationFormula.liftMembership (M.constant .E) (rename σ p)
  have renameBound : Bound (rename σ p) (n + 2) := bound_rename p bound fun i hi => by
    unfold σ
    split <;> omega
  have formulaBound : formula.Bound (params.length + 2) := by
    simpa only [formula, params, List.length_ofFn, RelationFormula.liftMembership_bound] using renameBound
  obtain ⟨output, result⟩ := S.separation P hM names params formula formulaBound input input
  refine ⟨output, fun x => (result x).trans (and_congr_right fun _ => ?_)⟩
  rw [RelationFormula.liftMembership_eval]
  have param := parameter_assignment environment n x input
  have h₁ := eval_congr_bound (E := E) (rename σ p) renameBound param
  have h₂ := NDSemantics.eval_rename E p σ (pushValue (pushValue environment input) x)
  have compose : pushValue (pushValue environment input) x ∘ σ = pushValue environment x := by
    funext i
    cases i <;> rfl
  rw [compose] at h₂
  exact h₁.trans h₂

theorem replacement_schema (P : QuasiProjections S) (hM : M.Models preceding)
    (names : ∀ x, S.Named x) (p : Formula) (n : Nat) (bound : Bound p (n + 2)) (env : Nat → Point) :
    eval (S.rel (M.constant .E)) (replacementSchema n p) env := by
  apply eval_allPrefix
  intro environment
  apply (eval_replacement p environment).mpr
  dsimp only
  intro unique input
  let params := List.ofFn fun i : Fin n => environment i
  let formula := RelationFormula.liftMembership (M.constant .E) p
  have formulaBound : formula.Bound (params.length + 2) := by
    simpa only [formula, params, List.length_ofFn, RelationFormula.liftMembership_bound] using bound
  have description (x y : Point) :
      RelationFormula.eval S formula (parameterEnv params x y) ↔
        eval (S.rel (M.constant .E)) p (pushValue (pushValue environment y) x) := by
    rw [RelationFormula.liftMembership_eval]
    exact eval_congr_bound p bound (parameter_assignment environment n x y)
  obtain ⟨output, result⟩ := definable_image P hM names params formula formulaBound
    (fun x y z hy hz => unique x y z ((description x y).mp hy) ((description x z).mp hz)) input
  exact ⟨output, fun y => (result y).trans (exists_congr fun x => and_congr_right fun _ => description x y)⟩

end PalomarI3380.SquareRepresentation
