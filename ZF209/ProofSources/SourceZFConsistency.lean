module
public import SourceFoundationConsistency
public import SourceOmegaSemantics
public import SourceSchemaSemantics
@[expose] public section
namespace ZFR.NDSemantics
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
/-- Pure source-theory calibration, with no Rosser engine or self-binding import. -/
theorem all_source_zf_axioms_valid (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
 AxiomsTrue (fun x y : V => x ∈ y) := by
 intro p hp s
 rcases hp with hf | hs | hr
 · exact source_fixed_valid hf s
 · exact numeric_separation_valid p hs s
 · exact numeric_replacement_valid p hr s

theorem source_zf_consistent [FFL.Entailment.Consistent (𝗭𝗙 : SetTheory)] :
 ¬ RosserDirect.ZFDriver.SourceCertificate Formula.bot :=
 source_consistent_of_foundation_consistent all_source_zf_axioms_valid
end ZFR.NDSemantics
