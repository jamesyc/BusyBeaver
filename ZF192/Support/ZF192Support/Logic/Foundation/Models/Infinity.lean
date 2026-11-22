module
public import ZF192Support.Logic.Foundation.Models.Fixed
public import Foundation.FirstOrder.SetTheory.Z.Z
@[expose] public section
namespace ZFR.NDSemantics
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭]
def SourceInductive (I : V) : Prop :=
 (∃ e : V, (∀ z, z ∈ e → False) ∧ e ∈ I) ∧
 (∀ x : V, x ∈ I → ∃ y : V, (∀ z, (z ∈ y → z ∈ x ∨ z=x) ∧ ((z ∈ x ∨ z=x) → z ∈ y)) ∧ y ∈ I)
theorem source_inductive_iff (I : V) : SourceInductive I ↔ IsInductive I := by
 constructor
 · rintro ⟨⟨e,he,heI⟩,hs⟩
   have heq : e = (∅ : V) := mem_ext_iff.mpr (fun z => ⟨fun hz => False.elim (he z hz),fun hz => False.elim (not_mem_empty hz)⟩)
   refine ⟨heq ▸ heI,?_⟩
   intro x hx
   obtain ⟨y,hy,hyI⟩ := hs x hx
   have hyeq : y = succ x := mem_ext_iff.mpr (fun z => by
    rw [mem_succ_iff]
    exact ⟨fun hz => ((hy z).1 hz).symm,fun hz => (hy z).2 hz.symm⟩)
   exact hyeq ▸ hyI
 · intro hI
   refine ⟨⟨∅,fun z => not_mem_empty,hI.1⟩,?_⟩
   intro x hx
   refine ⟨succ x,?_,hI.2 x hx⟩
   intro z
   exact ⟨fun hz => (mem_succ_iff.mp hz).symm,fun hz => mem_succ_iff.mpr hz.symm⟩
/-- The source axiom names the LEAST inductive set. Zermelo separation and
infinity supply it; no equation with the weaker raw infinity axiom is assumed. -/
theorem fixed_omega_valid (s : Nat → V) : eval (fun x y : V => x ∈ y) fixedOmega s := by
 change ∃ I : V, SourceInductive I ∧ ∀ J : V, SourceInductive J → ∀ x : V, x ∈ I → x ∈ J
 refine ⟨ω,(source_inductive_iff _).mpr ω_isInductive,?_⟩
 intro J hJ
 exact ((source_inductive_iff J).mp hJ).ω_subset
theorem source_fixed_valid {p : Formula} (hp : SourceFixedAxiom p)
 (s : Nat → V) : eval (fun x y : V => x ∈ y) p s := by
 rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · exact fixed_refl_valid _ s
 · exact fixed_sym_valid _ s
 · exact fixed_trans_valid _ s
 · exact fixed_eqElem_valid _ s
 · exact fixed_ext_valid s
 · exact fixed_empty_valid s
 · exact fixed_pair_valid s
 · exact fixed_union_valid s
 · exact fixed_power_valid s
 · exact fixed_omega_valid s
 · exact fixed_foundation_valid s
end ZFR.NDSemantics
