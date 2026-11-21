module
public import I0451.Logic.SetLanguageCodes
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.CraigTrick

/-! Craig padding of a fixed arithmetic enumeration predicate.
Foundation's prenex theorem turns the predicate into an explicit
bounded witness, which remains valid in every model of IΣ₁. -/
@[expose] public section
namespace I0451.Logic.UniformCraig

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

noncomputable def witness (enumerates : 𝚺ᴬ₁.Semisentence 1) : 𝚺ᴬ₀.Semisentence 2 :=
  .mkSigma (ISigma1.exists_matrix_provable enumerates.sigma_prop).choose.val

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma witness_spec (enumerates : 𝚺ᴬ₁.Semisentence 1) (code : V) :
    enumerates.val.Evalb ![code] ↔ ∃ stamp : V, (witness enumerates).val.Evalb ![stamp,code] :=
  (models_iff_of_provable_iff
    (ISigma1.exists_matrix_provable enumerates.sigma_prop).choose_spec V ![code]).trans
    Semiformula.eval_ex

variable (L : Language) [L.Encodable] [L.LORDefinable]

/-- Internally, a witness is part of each admitted axiom's padding. -/
def Axiom (enumerates : 𝚺ᴬ₁.Semisentence 1) (out : V) : Prop :=
  ∃ code < out, ∃ stamp < out,
    out = code ^⋏ qqVerums stamp ∧ IsFormula L code ∧ shift L code = code ∧ shift L out = out ∧
      (witness enumerates).val.Evalb ![stamp,code]

noncomputable def axiomDef (enumerates : 𝚺ᴬ₁.Semisentence 1) : 𝚫ᴬ₁.Semisentence 1 :=
  .mkDelta
    (.mkSigma “out. ∃ code < out, ∃ stamp < out, ∃ verums,
      !qqVerumsGraph verums stamp ∧ !qqAndDef out code verums ∧
      !(isSemiformula L).sigma 0 code ∧ !(shiftGraph L) code code ∧ !(shiftGraph L) out out ∧
      !(witness enumerates) stamp code”)
    (.mkPi “out. ∃ code < out, ∃ stamp < out,
      (∀ verums, !qqVerumsGraph verums stamp → !qqAndDef out code verums) ∧
      !(isSemiformula L).pi 0 code ∧ (∀ shifted, !(shiftGraph L) shifted code → shifted = code) ∧
      (∀ shifted, !(shiftGraph L) shifted out → shifted = out) ∧ !(witness enumerates) stamp code”)

theorem axiomDef_defines (enumerates : 𝚺ᴬ₁.Semisentence 1) :
    𝚫ᴬ₁-Predicate[V] Axiom L enumerates via axiomDef L enumerates := by
  refine .mk ⟨?_, ?_⟩ <;> intro v
  · simp [axiomDef, Axiom, eq_comm]
  · simp [axiomDef, Axiom, eq_comm]

def theory (enumerates : 𝚺ᴬ₁.Semisentence 1) : Theory L :=
  { σ | Axiom L enumerates (⌜σ⌝ : Nat) }

lemma fixed_proposition_is_sentence {n : Nat} {φ : Semiproposition L n}
    (fixes : shift L (⌜φ⌝ : Nat) = ⌜φ⌝) :
    ∃ σ : Semisentence L n, φ = Rewriting.emb σ := by
  have fixed : Rewriting.shift φ = φ := (Semiformula.quote_inj_iff (V := Nat)).mp (by
    rw [Semiformula.quote_shift]; exact fixes)
  have closed := Semiformula.freeVariables_eq_empty_of_shift_eq fixed
  exact ⟨φ.toEmpty closed, (Semiformula.emb_toEmpty φ closed).symm⟩

noncomputable instance theory_delta (enumerates : 𝚺ᴬ₁.Semisentence 1) : (theory L enumerates).Δ₁ where
  ch := axiomDef L enumerates
  mem_iff φ := by
    refine ((axiomDef_defines L enumerates (V := Nat)).iff (v := ![⌜φ⌝])).trans ?_
    change Axiom L enumerates (⌜φ⌝ : Nat) ↔ _
    constructor
    · intro ax
      obtain ⟨_, _, _, _, _, _, _, fixed, _⟩ := id ax
      obtain ⟨σ,rfl⟩ := fixed_proposition_is_sentence L fixed
      exact ⟨σ, ax, rfl⟩
    · rintro ⟨σ, admitted, rfl⟩
      exact admitted
  isDelta1 := Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
    fun W _ _ => (axiomDef_defines L enumerates (V := W)).proper

theorem mem_iff (enumerates : 𝚺ᴬ₁.Semisentence 1) (p : V) :
    p ∈ (theory L enumerates).Δ₁Class ↔ Axiom L enumerates p :=
  (axiomDef_defines L enumerates (V := V)).iff (v := ![p])

lemma shift_verums : ∀ stamp : V, shift L (qqVerums stamp) = qqVerums stamp := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  · simp
  · rename_i n ih
    rw [qqVerums_succ, shift_and (by simp) (IsSemiformula.qqVerums (n := 0) n).isUFormula,
      shift_verum, ih]

theorem padded {enumerates : 𝚺ᴬ₁.Semisentence 1} {p stamp : V} (well : IsFormula L p)
    (closed : shift L p = p) (proves : (witness enumerates).val.Evalb ![stamp,p]) :
    Axiom L enumerates (p ^⋏ qqVerums stamp) := by
  have wf := (IsSemiformula.qqVerums (n := (0 : V)) stamp).isUFormula (L := L)
  refine ⟨p, lt_K!_left _ _, stamp, lt_of_le_of_lt (le_qqVerums _) (lt_K!_right _ _),
    rfl, well, closed, ?_, proves⟩
  simp [well.isUFormula, wf, closed, shift_verums L stamp]

theorem padded_axiom {enumerates : 𝚺ᴬ₁.Semisentence 1} {p : V} (well : IsFormula L p)
    (closed : shift L p = p) (admitted : enumerates.val.Evalb ![p]) :
    ∃ stamp, (p ^⋏ qqVerums stamp) ∈ (theory L enumerates).Δ₁Class (V := V) := by
  obtain ⟨stamp,wit⟩ := (witness_spec enumerates p).mp admitted
  exact ⟨stamp, (mem_iff L enumerates _).mpr (padded L well closed wit)⟩

end I0451.Logic.UniformCraig
