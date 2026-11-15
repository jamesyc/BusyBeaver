module
public import SourceNumericCompleteness
public import SourceZFConsistency
@[expose] public section
namespace ZFR.NumericDecode
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
/-- Consistency of actual pinned Foundation ZF forbids the exact NUMERIC
source-refutation predicate used by the literal209 calibration. -/
theorem no_numeric_refutation [FFL.Entailment.Consistent (𝗭𝗙 : SetTheory)] :
 ¬ ZfrProvable 0 := by
 intro h
 have ht : RosserDirect.ZFDriver.SourceCertificate Formula.bot := numeric_to_source h
 exact ZFR.NDSemantics.source_zf_consistent ht
end ZFR.NumericDecode
