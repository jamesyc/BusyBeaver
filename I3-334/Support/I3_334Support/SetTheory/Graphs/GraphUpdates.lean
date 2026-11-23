module
public import I3_334Support.SetTheory.Recursion.RecursionUnion
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

noncomputable def succDomain (a i : V) : V := N.union₂ a (N.singleton i)

theorem mem_succDomain (a i x : V) : N.mem x (N.succDomain a i) ↔ N.mem x a ∨ x = i := by
  rw [succDomain,N.mem_union₂,N.mem_singleton]

theorem succDomain_self (a : V) : N.succDomain a a = N.succ a := rfl

/-- Adjoin a value to a function at an unused argument. -/
noncomputable def adjoinValue (f x y : V) : V :=
  N.union₂ f (N.singleton (N.orderedPair x y))

theorem at_adjoinValue (f i v x y : V) :
    Internal.At N.mem (N.adjoinValue f i v) x y ↔
      Internal.At N.mem f x y ∨ x = i ∧ y = v := by
  rw [N.at_pair,N.at_pair,adjoinValue,N.mem_union₂,N.mem_singleton]
  exact or_congr Iff.rfl ⟨N.orderedPair_inj,fun ⟨rfl,rfl⟩ => rfl⟩

theorem at_unique {f a i x y : V} (function : Internal.FunctionOn N.mem f a)
    (left : Internal.At N.mem f i x) (right : Internal.At N.mem f i y) : x = y := by
  have hi := SetRecursion.at_domain function left
  obtain ⟨_,_,unique⟩ := function.1 i hi
  exact (unique x left).trans (unique y right).symm

theorem function_adjoinValue {f a i v : V} (function : Internal.FunctionOn N.mem f a)
    (fresh : ¬N.mem i a) : Internal.FunctionOn N.mem (N.adjoinValue f i v) (N.succDomain a i) := by
  refine ⟨fun x hx => ?_,fun p hp => ?_⟩
  · rcases (N.mem_succDomain _ _ _).mp hx with old | same
    · obtain ⟨y,hit,one⟩ := function.1 x old
      refine ⟨y,(N.at_adjoinValue ..).mpr (Or.inl hit),fun z h => ?_⟩
      rcases (N.at_adjoinValue ..).mp h with previous | ⟨rfl,_⟩
      · exact one z previous
      · exact (fresh old).elim
    · subst x
      refine ⟨v,(N.at_adjoinValue ..).mpr (Or.inr ⟨rfl,rfl⟩),fun z h => ?_⟩
      rcases (N.at_adjoinValue ..).mp h with previous | ⟨_,eq⟩
      · exact (fresh (SetRecursion.at_domain function previous)).elim
      · exact eq
  · rcases (N.mem_union₂ ..).mp hp with old | added
    · obtain ⟨x,y,hx,pair⟩ := function.2 p old
      exact ⟨x,y,(N.mem_succDomain ..).mpr (Or.inl hx),pair⟩
    · have same := (N.mem_singleton ..).mp added
      exact ⟨i,v,(N.mem_succDomain ..).mpr (Or.inr rfl),same.symm ▸ N.orderedPair_intro i v⟩

end PalomarI3380.SquareRepresentation.SetContext
