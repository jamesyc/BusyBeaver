module
public import I0451.Logic.BerkeleyCardinal
public import I0451.Logic.CompressedTheory
public import I0451.Logic.TruthDefinability

/-! The literal EXTRA sentence and the Berkeley cardinal axiom are
interderivable over ZF. -/
@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

theorem berkeley_yields_compressed (existsBerkeley : ∃ δ : V, BerkeleyCardinal δ) :
    SetSentences.BerkeleyFormula E := by
  obtain ⟨δ, initial, uncountable, mapExists⟩ := existsBerkeley
  apply berkeleyFormula_iff_generated.mpr
  refine ⟨δ, fun d transitive hasδ => ?_⟩
  have zeroIn : (0 : V) ∈ δ := initial.1.toIsTransitive.transitive ω uncountable _ zero_mem_ω
  obtain ⟨j, κ, _, below, elementary, critical⟩ :=
    mapExists d ⟨transitive⟩ hasδ 0 zeroIn
  exact ⟨j, ⟨κ, below, critical.2.1⟩, elementary.generatedComparison⟩

theorem compressed_iff_berkeley_models :
    V↓[ℒₛₑₜ] ⊧ compressedSetAxiom ↔ V↓[ℒₛₑₜ] ⊧ berkeleySetAxiom := by
  rw [compressed_models_iff (fun x : V => mem_irrefl x), berkeleySetAxiom_models]
  exact ⟨compressed_yields_berkeley, berkeley_yields_compressed⟩

end I0451.Logic.SetAssignments

namespace I0451.Logic

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.Logic.SetAssignments

def berkeleyTheory : SetTheory := 𝗭𝗙 ∪ {berkeleySetAxiom}

instance : 𝗭𝗙 ⪯ berkeleyTheory :=
  Entailment.WeakerThan.ofSubset fun _ h => Or.inl h

instance : 𝗘𝗤 ℒₛₑₜ ⪯ berkeleyTheory :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₛₑₜ ⪯ 𝗭𝗙) inferInstance

attribute [local irreducible] compressedSetAxiom berkeleySetAxiom

set_option maxHeartbeats 1600000 in
theorem compressed_provable_in_berkeley : berkeleyTheory ⊢ compressedSetAxiom := by
  apply SetTheory.complete.{0}
  intro M _ _ _
  let : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := models_of_subtheory (U := berkeleyTheory) inferInstance
  exact compressed_iff_berkeley_models.mpr (Theory.models M berkeleyTheory (.inr rfl))

set_option maxHeartbeats 1600000 in
theorem berkeley_provable_in_compressed : compressedTheory ⊢ berkeleySetAxiom := by
  apply SetTheory.complete.{0}
  intro M _ _ _
  let : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := models_of_subtheory (U := compressedTheory) inferInstance
  exact compressed_iff_berkeley_models.mp (Theory.models M compressedTheory (.inr rfl))

theorem literal_nonhalting_of_berkeley_consistency (consistent : Entailment.Consistent berkeleyTheory) :
    ¬ Halts literal (blank 0) := by
  have weaker : compressedTheory ⪯ berkeleyTheory :=
    Entailment.WeakerThan.ofAxm! fun {p} h => by
      rcases h with zf | same
      · exact Entailment.by_axm (show p ∈ berkeleyTheory from Or.inl zf)
      · have equal : p = compressedSetAxiom := same
        subst p
        exact compressed_provable_in_berkeley
  exact literal_nonhalting_of_compressed_consistency (consistent.of_le weaker)

end I0451.Logic
