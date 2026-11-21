module
public import I3_380.Calibration.FilterReading
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder

theorem eval_vector_conj {L : Language} {A : Type} [Tarski.Structure L A]
    {k n : Nat} (p : Fin k → Semisentence L n) (env : Fin n → A) :
    (Matrix.conj p).Evalb env ↔ ∀ i, (p i).Evalb env := by
  induction k with
  | zero => simp
  | succ k ih =>
    change ((p 0).Evalb env ∧ (Matrix.conj (Matrix.vecTail p)).Evalb env) ↔ _
    simp [ih,Fin.forall_fin_succ,Matrix.vecTail]

def representativeTerms {n : Nat} (j : Nat) : ClosedSemiterm FilterLanguage n :=
  if valid : j < n then .bvar ⟨j,valid⟩ else Rew.castLE (Nat.zero_le n) unitOp.term

def namedArguments (n : Nat) : Semisentence FilterLanguage n :=
  Matrix.conj fun i : Fin n => namedPointOp.operator ![.bvar i]

/-- Interpret a membership template on named point representatives.
The guard ensures that each argument has a well-defined point value. -/
def namedMembership (n : Nat) (φ : Logic.Formula) : Semisentence FilterLanguage n :=
  namedArguments n ⋏ interpretMembership φ representativeTerms

section Semantics

variable {A : Type} [Tarski.Structure FilterLanguage A] [Tarski.Structure.Eq FilterLanguage A]
variable (C : FilterModel A)

theorem named_argument_eval {n : Nat} (arg : Fin n) (env : Fin n → A) :
    (namedPointOp.operator ![.bvar arg]).Evalb env ↔
      ∃ r : C.Representative, r.val.val = env arg := by
  have point : namedPointOp.sentence.Evalb ![env arg] ↔
      ∃ r : C.Representative, r.val.val = env arg := C.representative_eval (env arg)
  simpa [Semiformula.Operator.operator,Semiformula.eval_substs,Semiterm.val,
    Function.comp_def,Matrix.constant_eq_singleton,Fin.forall_fin_one] using point

theorem namedMembership_eval {n : Nat} {φ : Logic.Formula} (bound : Logic.Bound φ n)
    (env : Fin n → A) (default : C.Representative) :
    (namedMembership n φ).Evalb env ↔
      ∃ v : Fin n → C.Representative, (∀ i, (v i).val.val = env i) ∧
        Logic.eval C.mem φ (fun i => if inside : i < n then C.asPoint (v ⟨i,inside⟩) else C.asPoint default) := by
  let extend := fun (v : Fin n → C.Representative) (i : Nat) =>
    if inside : i < n then v ⟨i,inside⟩ else default
  have readings (v : Fin n → C.Representative) (same : ∀ i, (v i).val.val = env i) :
      (interpretMembership φ representativeTerms).Evalb env ↔
        Logic.eval C.mem φ (fun i => if inside : i < n then C.asPoint (v ⟨i,inside⟩) else C.asPoint default) := by
    have values : ∀ i, i < n → (representativeTerms i).valb env = (extend v i).val.val := by
      intro i inside
      simp [representativeTerms,extend,inside,Semiterm.valb,Semiterm.val,same]
    have h := interpretMembership_eval C φ bound representativeTerms env (extend v) values
    exact h.trans (Iff.of_eq (congrArg (Logic.eval C.mem φ) (funext fun i => by
      by_cases inside : i < n <;> simp [extend,inside])))
  change ((namedArguments n).Evalb env ∧ (interpretMembership φ representativeTerms).Evalb env) ↔ _
  constructor
  · rintro ⟨guard,truth⟩
    have reps : ∀ i, ∃ x : C.Representative, x.val.val = env i := by
      intro i
      exact (named_argument_eval C i env).mp ((eval_vector_conj _ _).mp guard i)
    let v := fun i => Classical.choose (reps i)
    have same : ∀ i, (v i).val.val = env i := fun i => Classical.choose_spec (reps i)
    exact ⟨v,same,(readings v same).mp truth⟩
  · rintro ⟨v,same,truth⟩
    refine ⟨(eval_vector_conj _ _).mpr ?_,(readings v same).mpr truth⟩
    intro i
    exact (named_argument_eval C i env).mpr ⟨v i,same i⟩

def pointLevels {n : Nat} (points : Fin n → C.Representative) (default : C.Representative) :
    Nat → C.Domain := fun i =>
  if inside : i < n then C.asPoint (points ⟨n-(i+1),by omega⟩) else C.asPoint default

theorem namedSetFormula_eval {n : Nat} (p : Logic.SetFormula) (bound : Logic.Bound (p n) n)
    (env : Fin n → A) (default : C.Representative) :
    (namedMembership n (p n)).Evalb env ↔
      ∃ v : Fin n → C.Representative, (∀ i, (v i).val.val = env i) ∧
        Logic.SetFormula.holds C.mem p n (pointLevels C v default) (C.asPoint default) := by
  rw [namedMembership_eval C bound env default]
  apply exists_congr
  intro v
  apply and_congr_right
  intro _
  apply Logic.eval_congr_bound _ bound
  intro i hi
  have reversed : n-(i+1) < n := by omega
  have restore : n-(n-(i+1)+1) = i := by omega
  simp [Logic.SetFormula.assignment,pointLevels,hi,reversed,restore]

end Semantics
end PalomarI3380.Calibration
