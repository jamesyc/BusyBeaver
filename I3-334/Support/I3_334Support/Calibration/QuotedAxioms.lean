module
public import I3_334Support.Calibration.RelationalTheory
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem characteristic_transport {L : Language} [L.Encodable] [L.LORDefinable]
    {T U : Theory L} (spec : T.Δ₁) (h : T=U) :
    (spec.ofEq h).ch.val=spec.ch.val := by subst U; rfl

theorem finiteTheory_quoted {L : Language} [L.Encodable] [L.LORDefinable]
    (s : List (Sentence L)) (p : M) :
    (Theory.Δ₁.ofList s).ch.val.Evalb ![p] ↔ ∃ φ ∈ s, p=(⌜φ⌝ : M) := by
  induction s with
  | nil =>
    change (⊥ : Semisentence ℒₒᵣ 1).Evalb ![p] ↔ _
    simp
  | cons a s ih =>
    rw [Theory.Δ₁.ofList,characteristic_transport]
    change ((Theory.Δ₁.singleton a).ch ⋎ (Theory.Δ₁.ofList s).ch).val.Evalb ![p] ↔ _
    rw [Bounding.HierarchySymbol.Semiformula.val_or,LogicalConnective.HomClass.map_or]
    have here : (Theory.Δ₁.singleton a).ch.val.Evalb ![p] ↔ p=(⌜a⌝ : M) := by
      change (“x. x = ↑(Encodable.encode a)” : Semisentence ℒₒᵣ 1).Evalb ![p] ↔ _
      simp [FFL.FirstOrder.Sentence.quote_eq_encode,numeral_eq_natCast]
    rw [here,ih]
    simp only [List.mem_cons,exists_eq_or_imp,LogicalConnective.Prop.or_eq]

theorem graphTheory_quoted (p : M) :
    p ∈ graphTheory.Δ₁Class ↔ ∃ φ ∈ graphTheory, p=(⌜φ⌝ : M) := by
  let list := graphTheory_finite.toFinset.toList
  have definition : graphTheory.Δ₁ch.val = (Theory.Δ₁.ofList list).ch.val :=
    characteristic_transport (Theory.Δ₁.ofList list) (by ext; simp [list])
  change graphTheory.Δ₁ch.val.Evalb ![p] ↔ _
  rw [definition,finiteTheory_quoted]
  simp [list]

end PalomarI3380.Calibration
