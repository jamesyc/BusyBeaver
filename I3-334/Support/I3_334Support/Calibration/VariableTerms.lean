module
public import I3_334Support.Calibration.RelationalLanguage
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Basic
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_term_cases {n t : M} :
    IsSemiterm GraphLanguage n t ↔ (∃ i < n, t = ^#i) ∨ ∃ i, t = ^&i := by
  rw [IsSemiterm.case_iff]
  simp

end PalomarI3380.Calibration
