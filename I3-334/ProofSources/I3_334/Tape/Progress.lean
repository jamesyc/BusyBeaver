module
public import I3_334Support.Engine.Arithmetic.Tape
@[expose] public section

namespace PalomarI3334.Stock

open PalomarI3380 PalomarI3380.ArithmeticMachine
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A positive number of literal transitions in the ambient arithmetic. -/
def Progress (m : Machine) (first last : M) : Prop :=
  ∃ time : M, 0 < time ∧ clock m.workingStates m.packedRows time first = last

theorem Progress.reach {m : Machine} {a b : M} (walk : Progress m a b) : Reaches m a b := by
  obtain ⟨n, _, eq⟩ := walk
  exact ⟨n, eq⟩

theorem progress_of_ne {m : Machine} {a b : M} (walk : Reaches m a b) (different : a ≠ b) :
    Progress m a b := by
  obtain ⟨n, eq⟩ := walk
  by_cases zero : n = 0
  · subst n
    simp only [clock_zero] at eq
    exact (different eq).elim
  · exact ⟨n, lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm zero), eq⟩

theorem Progress.trans {m : Machine} {a b c : M} (first : Progress m a b) (rest : Reaches m b c) :
    Progress m a c := by
  obtain ⟨n, positive, toMiddle⟩ := first
  obtain ⟨k, toEnd⟩ := rest
  exact ⟨n+k, lt_of_lt_of_le positive (le_add_of_nonneg_right (Arithmetic.zero_le _)),
    by rw [clock_add, toMiddle, toEnd]⟩

end PalomarI3334.Stock
