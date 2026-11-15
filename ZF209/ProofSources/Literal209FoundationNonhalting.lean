module
public import NumericZFConsistency
public import ExactMachineZfrReverse
@[expose] public section
namespace ZF209
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
/-- The ORIGINAL literal209 table, not the redesigned Rosser whole engine.
Only ordinary consistency of actual pinned Foundation ZF is assumed.
This is a semantic nonhalting theorem, NOT ZF unprovability of nonhalting. -/
theorem literal209_nonhalting_of_foundation_consistent
 [FFL.Entailment.Consistent (𝗭𝗙 : SetTheory)] :
 ¬ M6.Zip.Halts M209.literal (M6.Zip.zc 0 [] []) := by
 intro h
 exact ZFR.NumericDecode.no_numeric_refutation (literal209_halts_to_zfr_refutation h)
end ZF209
