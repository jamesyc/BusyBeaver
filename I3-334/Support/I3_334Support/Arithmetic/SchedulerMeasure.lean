module
public import I3_334Support.Arithmetic.FiniteTraces
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def schedulerBudget (target index pending : M) : M :=
  (target-index)*(target+1)+pending

theorem schedulerBudget_tail (target index : M) {p q : M} (smaller : q < p) :
    schedulerBudget target index q < schedulerBudget target index p := by
  unfold schedulerBudget
  exact add_lt_add_right smaller _

theorem schedulerBudget_next (target index p : M) (before : index < target) (bound : p ≤ target) :
    schedulerBudget target (index+1) p < schedulerBudget target index 0 := by
  unfold schedulerBudget
  have needed : index+1 ≤ target := succ_le_iff_lt.mpr before
  have remainder : target-(index+1)+1=target-index := by
    apply add_right_cancel (b := index)
    calc
      target-(index+1)+1+index = target-(index+1)+(index+1) := by ac_rfl
      _ = target := tsub_add_cancel_of_le needed
      _ = target-index+index := (tsub_add_cancel_of_le (le_of_lt before)).symm
  rw [← remainder,add_mul,one_mul,add_zero]
  exact add_lt_add_right (lt_of_le_of_lt bound (lt_add_one _)) _

theorem schedulerBudget_definable (target : M) : 𝚺ᴬ₁-Function₂ (schedulerBudget target) := by
  unfold schedulerBudget
  definability

theorem definableAllCons {n k : Nat} {P : (Fin (n+1) → M) → Prop}
    (h : 𝚷ᴬ_[k+1].Definable P) : 𝚷ᴬ_[k+1].Definable (fun v => ∀ x, P (x :> v)) := by
  exact Bounding.HierarchySymbol.Definable.all (P := fun v x => P (x :> v)) (h.of_iff fun _ => by simp)

end PalomarI3380.Compiler.Source
