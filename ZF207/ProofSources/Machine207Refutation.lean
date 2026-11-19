module
public import SourceFetchBinding
public import SearchEquivalence
@[expose] public section
namespace C207Search
open C207Soundness M207.Source M207.SourceSimulation

private theorem exact_initial :
 project initialState = Primitive.SourceScheduler.boundary 2 0 zeroStore := by
 apply congrArg (ScalarState.mk 25)
 funext r
 have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
  exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
 rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- Literal published209-state transition table, blank tape, halts exactly
when the exact numeric C207 source proof calculus refutes. This theorem does
not identify C207 refutation with ZF inconsistency or assert ZF independence. -/
theorem literal207_halts_iff_C207_refutation :
 M6.Zip.Halts M207.literal (M6.Zip.zc 0 [] []) ↔ ExactProvable 1 := by
 have hm := blank_halts_iff_nine_register_cfg
 rw [exact_initial] at hm
 exact hm.trans ((Primitive.SourceScheduler.literal_source_scheduler_iff 2 zeroStore).trans
  retained_scheduler_iff_refutation)
end C207Search
