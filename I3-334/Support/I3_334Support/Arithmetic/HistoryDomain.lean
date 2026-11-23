module
public import I3_334Support.Arithmetic.ConfigurationFormula
public import I3_334Support.Arithmetic.InternalMoves
@[expose] public section

namespace PalomarI3380.Logic.Expanded.OmegaDomain

open SquareRepresentation ArithmeticMachine
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type} {E G : V → V → Prop}
variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

local notation "K" => (L.context inhabited)
local notation "W" => D.Points
local instance : (W)↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano

theorem member_of_time_domain (n : W) (i : V) (hi : E i ((K).succ n.val)) : E i D.omega := by
  rcases ((K).mem_succ _ _).mp hi with lt | same
  · exact ((K).omega_ordinal D.specification).transitive n.val n.property i lt
  · exact same.symm ▸ n.property

theorem successor_in_domain {n : W} {i : V} (hi : E i D.omega) :
    E ((K).succ i) ((K).succ n.val) ↔ E i n.val := by
  let idx : W := ⟨i,hi⟩
  constructor
  · intro inside
    rcases ((K).mem_succ _ _).mp inside with lower | eq
    · exact D.lt_trans (D.lt_succ_self idx) (show D.successor idx < n from lower)
    · exact eq ▸ ((K).mem_succ i i).mpr (Or.inr rfl)
  · intro earlier
    have bound : D.successor idx ≤ n := by
      rw [← D.plus_one]
      exact succ_le_iff_lt.mpr earlier
    rcases eq_or_lt_of_le bound with eq | less
    · exact ((K).mem_succ _ _).mpr (Or.inr (congrArg Subtype.val eq))
    · exact ((K).mem_succ _ _).mpr (Or.inl less)

end PalomarI3380.Logic.Expanded.OmegaDomain
