module
public import I3_334Support.Machine
@[expose] public section

namespace PalomarI3380

theorem step_none_iff (m : Machine) (c : Configuration) :
    step m c = none ↔ m.workingStates ≤ c.state := by
  by_cases h : m.workingStates ≤ c.state
  · simp [step,h]
  · simp only [step,h,↓reduceIte]
    split <;> simp

theorem step_from_row (m : Machine) (q l r : Nat) (h : q < m.workingStates) :
    let row := m.row q (Nat.mod r 2)
    let next := Nat.div row 4
    let bit := Nat.mod (Nat.div row 2) 2
    step m ⟨q,l,r⟩ =
      some (if Nat.mod row 2 = 1 then ⟨next,2*l+bit,Nat.div r 2⟩
        else ⟨next,Nat.div l 2,4*Nat.div r 2+2*bit+Nat.mod l 2⟩) := by
  have work := Nat.not_le_of_lt h
  unfold step
  rw [if_neg work]
  let row := m.row q (Nat.mod r 2)
  change (if Nat.mod row 2 = 1 then some _ else some _) = some (if Nat.mod row 2 = 1 then _ else _)
  by_cases direction : Nat.mod row 2 = 1 <;> simp only [direction,↓reduceIte] <;> rfl

end PalomarI3380
