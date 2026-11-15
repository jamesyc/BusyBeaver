module
public import ProofTranslation
public import LiteralDiagonalBridge
public import RankHullFiniteParameters
@[expose] public section
namespace ZFR
open C209Soundness

theorem parameterizedSeparationContext_in_zfr (n : Nat) (phi : Formula) (hb : Bound phi (n+1)) :
 ∀ p, p ∈ parameterizedSeparationContext n phi → sourceZfrAxiom (encodeFormula p) := by
 intro p hp
 simp only [parameterizedSeparationContext,List.mem_cons,List.not_mem_nil,or_false] at hp
 rcases hp with rfl | rfl | rfl
 · exact coreContext_in_zfr _ (by simp [coreContext])
 · exact coreContext_in_zfr _ (by simp [coreContext])
 · exact separationSchema_in_zfr n phi hb

/-- Complete syntactic repeated-label pointed-gate proof, using a concrete
finite context of literal ZFR fixed axioms plus one recognized Separation
instance. No gate/model/hull assumption. -/
theorem source_diagonal_gate (a x : Nat) (hax : a ≠ x) :
 SourceTheorem (translateCode id (pointedGateCode a x x)) := by
 let phi := translate (bindName x id) (decodeNat a)
 let Δ := parameterizedSeparationContext (parameterBound phi) phi
 have hΔ : ∀ p, p ∈ Δ → sourceZfrAxiom (encodeFormula p) :=
   parameterizedSeparationContext_in_zfr _ phi ((parameterBound_valid phi).mono (by omega))
 have ht : ND (.seq Δ (.ex (diagonalPointedBody x phi))) :=
   (all_formula_diagonal_certificate phi x).2.2
 refine ⟨coreContext ++ Δ,?_,nd_positive_to_literal_diagonal a x hax
   (fun p hp => List.mem_append_left Δ hp)
   (ND.wk (fun p hp => List.mem_append_right coreContext hp) ht)⟩
 intro p hp
 rcases List.mem_append.mp hp with hc | hd
 · exact coreContext_in_zfr p hc
 · exact hΔ p hd

/-- The remaining gate obligation is now ONLY the distinct-label case. -/
def DistinctGateTranslationObligation : Prop := ∀ a d h,
 a ≠ d → a ≠ h → d ≠ h → SourceTheorem (translateCode id (pointedGateCode a d h))

theorem gate_obligation_of_distinct (hd : DistinctGateTranslationObligation) :
 GateTranslationObligation := by
 intro a d h had hah
 by_cases hdh : d = h
 · subst h; exact source_diagonal_gate a d had
 · exact hd a d h had hah hdh

theorem reverse_calibration_pending_distinct_gate (hd : DistinctGateTranslationObligation)
 (h : ExactProvable 1) : ZfrProvable 0 :=
 reverse_calibration_pending_gate (gate_obligation_of_distinct hd) h

end ZFR
