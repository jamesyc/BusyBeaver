module
public import ZF192Support.Logic.Source.Models
public import Foundation.FirstOrder.SetTheory.BST.BST
@[expose] public section
namespace ZFR.NDSemantics
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* BasicSetTheory]
local notation "E" => (fun x y : V => x ∈ y)
theorem fixed_ext_valid (s : Nat → V) : eval E fixedExt s := by
 simp only [fixedExt,eval,pushValue]
 intro x y hxy hyx
 exact mem_ext_iff.mpr (fun z => ⟨hxy z,hyx z⟩)
theorem fixed_empty_valid (s : Nat → V) : eval E fixedEmpty s := by
 simp only [fixedEmpty,eval,pushValue]
 exact ⟨∅,fun x => not_mem_empty⟩
theorem fixed_pair_valid (s : Nat → V) : eval E fixedPair s := by
 simp only [fixedPair,eval,pushValue]
 intro x y
 obtain ⟨z,hz⟩ := pairing_exists x y
 exact ⟨z,fun w => ⟨(hz w).mp,(hz w).mpr⟩⟩
theorem fixed_union_valid (s : Nat → V) : eval E fixedUnion s := by
 simp only [fixedUnion,eval,pushValue]
 intro x
 obtain ⟨y,hy⟩ := union_exists x
 exact ⟨y,fun z => ⟨(hy z).mp,(hy z).mpr⟩⟩
theorem fixed_power_valid (s : Nat → V) : eval E fixedPower s := by
 simp only [fixedPower,eval,pushValue]
 intro x
 obtain ⟨y,hy⟩ := power_exists x
 exact ⟨y,fun z => ⟨(hy z).mp,(hy z).mpr⟩⟩
theorem fixed_foundation_valid (s : Nat → V) : eval E fixedFoundation s := by
 simp only [fixedFoundation,eval,pushValue]
 have hf : ∀ x : V, IsNonempty x → ∃ y, y ∈ x ∧ ∀ z, z ∈ x → z ∈ y → False := by
  simpa [models_iff, BasicSetTheory.foundation] using Theory.models V BasicSetTheory BasicSetTheory.foundation
 intro x hx
 obtain ⟨y,hy,hmin⟩ := hf x ⟨hx⟩
 exact ⟨y,hy,fun z hzy hzx => hmin z hzx hzy⟩
end ZFR.NDSemantics
