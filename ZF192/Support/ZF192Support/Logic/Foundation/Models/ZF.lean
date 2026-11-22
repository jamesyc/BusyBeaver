module
public import ZF192Support.Logic.Foundation.Models.Consistency
public import ZF192Support.Logic.Foundation.Models.Infinity
public import ZF192Support.Logic.Foundation.Models.Schemas
@[expose] public section
namespace ZFR.NDSemantics
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
/-- Pure source-theory calibration, with no Rosser engine or self-binding import. -/
theorem all_source_zf_axioms_valid (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
 AxiomsTrue (fun x y : V => x ∈ y) := by
 intro p hp s
 rcases hp with hf | ⟨n, b, _, rfl⟩ | ⟨n, b, _, rfl⟩
 · exact source_fixed_valid hf s
 · exact separation_schema_valid b n s
 · exact replacement_schema_valid b n s

theorem source_zf_consistent [FFL.Entailment.Consistent (𝗭𝗙 : SetTheory)] :
 ¬ ZFR.SourceTheorem Formula.bot :=
 source_consistent_of_foundation_consistent all_source_zf_axioms_valid
end ZFR.NDSemantics
