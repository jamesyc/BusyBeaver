module
public import I3_334Support.Arithmetic.OmegaMultiplication
public import Foundation.FirstOrder.Arithmetic.Schemata
@[expose] public section

namespace PalomarI3380.Logic.Expanded.OmegaDomain

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type} {E G : V → V → Prop}
variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

local notation "W" => D.Points

theorem models_peanoMinus : (W)↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := by
  apply models_theory_iff.mpr
  intro σ h
  cases h
  · exact models_theory_iff.mp (inferInstance : (W)↓[ℒₒᵣ] ⊧* 𝗘𝗤 ℒₒᵣ) _ (by assumption)
  all_goals simp only [models_iff]
  case addZero => exact D.plus_zero
  case addAssoc => exact D.plus_assoc
  case addComm => exact D.plus_comm
  case addEqOfLt =>
    have h (a b : W) (lt : a < b) : ∃ c : W, c < b+1 ∧ a+c=b := by
      obtain ⟨c,below,eq⟩ := D.difference a b lt
      exact ⟨c,by rw [D.plus_one]; exact (D.lt_successor _ _).mpr below,eq⟩
    simpa [Semiformula.eval_bexsLTSucc] using h
  case zeroLe => simpa [Semiformula.Operator.LE.def_of_Eq_of_LT,or_comm] using D.zero_le
  case zeroLtOne => exact D.lt_succ_self 0
  case oneLeOfZeroLt =>
    simpa [Semiformula.Operator.LE.def_of_Eq_of_LT,or_comm] using (fun a : W => D.one_le_of_positive (a := a))
  case addLtAdd => simpa using (fun (a b c : W) (h : a < b) => D.plus_lt_plus h c)
  case mulZero => exact D.times_zero
  case mulOne => exact D.times_one
  case mulAssoc => exact D.times_assoc
  case mulComm => exact D.times_comm
  case mulLtMul =>
    simpa using (fun (a b c : W) (h : a < b ∧ 0 < c) => D.times_lt_times h.1 h.2)
  case distr => exact D.times_plus
  case ltIrrefl => exact D.lt_irrefl
  case ltTrans => simpa using (fun (a b c : W) (h : a < b ∧ b < c) => D.lt_trans h.1 h.2)
  case ltTri => exact D.lt_trichotomy

theorem models_peano : (W)↓[ℒₒᵣ] ⊧* 𝗣𝗔 := by
  apply models_theory_iff.mpr
  intro p h
  rcases h with base | ⟨φ,_,rfl⟩
  · exact models_theory_iff.mp D.models_peanoMinus p base
  · suffices ∀ params : Nat → W, φ.Eval ![0] params →
          (∀ x : W, φ.Eval ![x] params → φ.Eval ![x+1] params) →
          ∀ x : W, φ.Eval ![x] params by
      simpa [Semiformula.eval_univCl,succInd,models_iff,Matrix.constant_eq_singleton,
        Semiformula.eval_substs] using this
    intro params first step
    have next (x : W) (hx : φ.Eval (fun _ => x) params) :
        φ.Eval (fun _ => D.successor x) params := by
      simpa [D.plus_one,Matrix.constant_eq_singleton] using
        step x (by simpa [Matrix.constant_eq_singleton] using hx)
    simpa [Matrix.constant_eq_singleton] using
      D.induction φ params (by simpa [Matrix.constant_eq_singleton] using first) next

end PalomarI3380.Logic.Expanded.OmegaDomain
