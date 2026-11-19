module
public import PrimitivePairCore
@[expose] public section
set_option linter.unusedSimpArgs false
namespace C207Search.Primitive.TimesFour
open M207.Source
abbrev Store := PairCore.Store
abbrev registers := PairCore.registers
abbrev configAt := PairCore.configAt
def expected (base : Nat) : Nat → Instruction
 | 0 => .dec 5 (base+6) (base+1)
 | 1 => .inc 2 (base+2)
 | 2 => .inc 2 (base+3)
 | 3 => .inc 2 (base+4)
 | 4 => .inc 2 (base+5)
 | _ => .jump base
def Bound (base : Nat) := ∀ j : Fin 6, program (base+j.val) = some (expected base j.val)
variable {base : Nat} (hbound : Bound base)
include hbound
theorem step_0 (t w x y : Nat) (f : Registers) :
    step (configAt base 0 ⟨t,w,x,y,f⟩) = if y = 0 then configAt base 6 ⟨t,w,x,y,f⟩ else configAt base 1 ⟨t,w,x,y-1,f⟩ := by
  have hx : program (base+0) = some (expected base 0) := hbound ⟨0,by decide⟩
  unfold step scalarNext configAt PairCore.configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, PairCore.registers, PairCore.configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, PairCore.registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_1 (t w x y : Nat) (f : Registers) :
    step (configAt base 1 ⟨t,w,x,y,f⟩) = configAt base 2 ⟨t+1,w,x,y,f⟩ := by
  have hx : program (base+1) = some (expected base 1) := hbound ⟨1,by decide⟩
  unfold step scalarNext configAt PairCore.configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, PairCore.registers, PairCore.configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, PairCore.registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_2 (t w x y : Nat) (f : Registers) :
    step (configAt base 2 ⟨t,w,x,y,f⟩) = configAt base 3 ⟨t+1,w,x,y,f⟩ := by
  have hx : program (base+2) = some (expected base 2) := hbound ⟨2,by decide⟩
  unfold step scalarNext configAt PairCore.configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, PairCore.registers, PairCore.configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, PairCore.registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_3 (t w x y : Nat) (f : Registers) :
    step (configAt base 3 ⟨t,w,x,y,f⟩) = configAt base 4 ⟨t+1,w,x,y,f⟩ := by
  have hx : program (base+3) = some (expected base 3) := hbound ⟨3,by decide⟩
  unfold step scalarNext configAt PairCore.configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, PairCore.registers, PairCore.configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, PairCore.registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_4 (t w x y : Nat) (f : Registers) :
    step (configAt base 4 ⟨t,w,x,y,f⟩) = configAt base 5 ⟨t+1,w,x,y,f⟩ := by
  have hx : program (base+4) = some (expected base 4) := hbound ⟨4,by decide⟩
  unfold step scalarNext configAt PairCore.configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, PairCore.registers, PairCore.configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, PairCore.registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_5 (t w x y : Nat) (f : Registers) :
    step (configAt base 5 ⟨t,w,x,y,f⟩) = configAt base 0 ⟨t,w,x,y,f⟩ := by
  have hx : program (base+5) = some (expected base 5) := hbound ⟨5,by decide⟩
  unfold step scalarNext configAt PairCore.configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, PairCore.registers, PairCore.configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, PairCore.registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem times4 (t w x y : Nat) (f : Registers) :
    Steps (6*y+1) (configAt base 0 ⟨t,w,x,y,f⟩)
      (configAt base 6 ⟨t+4*y,w,x,0,f⟩) := by
  induction y generalizing t with
  | zero =>
    apply Steps.cons
    rw [step_0 hbound]
    simp only [↓reduceIte,Nat.mul_zero,Nat.add_zero]
    exact Steps.refl _
  | succ y ih =>
    have he : 6*(y+1)+1 = (6*y+1)+1+1+1+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_0 hbound]
    simp only [Nat.add_sub_cancel,Nat.succ_ne_zero,↓reduceIte]
    apply Steps.cons
    rw [step_1 hbound]
    apply Steps.cons
    rw [step_2 hbound]
    apply Steps.cons
    rw [step_3 hbound]
    apply Steps.cons
    rw [step_4 hbound]
    apply Steps.cons
    rw [step_5 hbound]
    have ht : t+4*(y+1) = (t+1+1+1+1)+4*y := by omega
    rw [ht]
    exact ih (t+1+1+1+1)

end C207Search.Primitive.TimesFour
