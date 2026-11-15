module
public import PrimitiveStep
@[expose] public section
set_option linter.unusedSimpArgs false
namespace C209Search.Primitive.AXGateCompare
open M209.Source
structure Store where
  t : Nat
  h : Nat
  x : Nat
  frame : Registers
def registers (s : Store) : Registers := fun r =>
  if r = 2 then s.t else if r = 7 then s.h else if r = 8 then s.x else s.frame r
def configAt (base pc : Nat) (s : Store) : Configuration := ⟨base+pc,registers s⟩
def expected (base : Nat) : Nat → Instruction
  | 0 => .dec 7 (base+4) (base+1)
  | 1 => .dec 8 (base+3) (base+2)
  | 2 => .jump (base+0)
  | 3 => .jump (base+5)
  | 4 => .dec 8 (base+10) (base+5)
  | 5 => .dec 7 (base+7) (base+6)
  | 6 => .jump (base+5)
  | 7 => .dec 8 (base+9) (base+8)
  | 8 => .jump (base+5)
  | 9 => .jump (base+12)
  | 10 => .dec 2 (base+12) (base+11)
  | 11 => .jump (base+10)
  | _ => .halt
def Bound (base : Nat) : Prop :=
  ∀ j : Fin 12, program (base+j.val) = some (expected base j.val)
variable {base : Nat} (hbound : Bound base)

include hbound
theorem step_0 (t h x : Nat) (f : Registers) :
    step (configAt base 0 ⟨t,h,x,f⟩) = if h = 0 then configAt base 4 ⟨t,h,x,f⟩ else configAt base 1 ⟨t,h-1,x,f⟩ := by
  have hx : program (base+0) = some (expected base 0) := hbound ⟨0,by decide⟩
  unfold step scalarNext configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_1 (t h x : Nat) (f : Registers) :
    step (configAt base 1 ⟨t,h,x,f⟩) = if x = 0 then configAt base 3 ⟨t,h,x,f⟩ else configAt base 2 ⟨t,h,x-1,f⟩ := by
  have hx : program (base+1) = some (expected base 1) := hbound ⟨1,by decide⟩
  unfold step scalarNext configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_2 (t h x : Nat) (f : Registers) :
    step (configAt base 2 ⟨t,h,x,f⟩) = configAt base 0 ⟨t,h,x,f⟩ := by
  have hx : program (base+2) = some (expected base 2) := hbound ⟨2,by decide⟩
  unfold step scalarNext configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_3 (t h x : Nat) (f : Registers) :
    step (configAt base 3 ⟨t,h,x,f⟩) = configAt base 5 ⟨t,h,x,f⟩ := by
  have hx : program (base+3) = some (expected base 3) := hbound ⟨3,by decide⟩
  unfold step scalarNext configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_4 (t h x : Nat) (f : Registers) :
    step (configAt base 4 ⟨t,h,x,f⟩) = if x = 0 then configAt base 10 ⟨t,h,x,f⟩ else configAt base 5 ⟨t,h,x-1,f⟩ := by
  have hx : program (base+4) = some (expected base 4) := hbound ⟨4,by decide⟩
  unfold step scalarNext configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_5 (t h x : Nat) (f : Registers) :
    step (configAt base 5 ⟨t,h,x,f⟩) = if h = 0 then configAt base 7 ⟨t,h,x,f⟩ else configAt base 6 ⟨t,h-1,x,f⟩ := by
  have hx : program (base+5) = some (expected base 5) := hbound ⟨5,by decide⟩
  unfold step scalarNext configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_6 (t h x : Nat) (f : Registers) :
    step (configAt base 6 ⟨t,h,x,f⟩) = configAt base 5 ⟨t,h,x,f⟩ := by
  have hx : program (base+6) = some (expected base 6) := hbound ⟨6,by decide⟩
  unfold step scalarNext configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_7 (t h x : Nat) (f : Registers) :
    step (configAt base 7 ⟨t,h,x,f⟩) = if x = 0 then configAt base 9 ⟨t,h,x,f⟩ else configAt base 8 ⟨t,h,x-1,f⟩ := by
  have hx : program (base+7) = some (expected base 7) := hbound ⟨7,by decide⟩
  unfold step scalarNext configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_8 (t h x : Nat) (f : Registers) :
    step (configAt base 8 ⟨t,h,x,f⟩) = configAt base 5 ⟨t,h,x,f⟩ := by
  have hx : program (base+8) = some (expected base 8) := hbound ⟨8,by decide⟩
  unfold step scalarNext configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_9 (t h x : Nat) (f : Registers) :
    step (configAt base 9 ⟨t,h,x,f⟩) = configAt base 12 ⟨t,h,x,f⟩ := by
  have hx : program (base+9) = some (expected base 9) := hbound ⟨9,by decide⟩
  unfold step scalarNext configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_10 (t h x : Nat) (f : Registers) :
    step (configAt base 10 ⟨t,h,x,f⟩) = if t = 0 then configAt base 12 ⟨t,h,x,f⟩ else configAt base 11 ⟨t-1,h,x,f⟩ := by
  have hx : program (base+10) = some (expected base 10) := hbound ⟨10,by decide⟩
  unfold step scalarNext configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_11 (t h x : Nat) (f : Registers) :
    step (configAt base 11 ⟨t,h,x,f⟩) = configAt base 10 ⟨t,h,x,f⟩ := by
  have hx : program (base+11) = some (expected base 11) := hbound ⟨11,by decide⟩
  unfold step scalarNext configAt
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem clear_h (t h x : Nat) (f : Registers) :
    Steps (2*h+1) (configAt base 5 ⟨t,h,x,f⟩)
      (configAt base 7 ⟨t,0,x,f⟩) := by
  induction h with
  | zero =>
    apply Steps.cons
    rw [step_5 hbound]
    exact Steps.refl _
  | succ h ih =>
    have he : 2*(h+1)+1 = (2*h+1)+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_5 hbound]
    simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step_6 hbound]
    exact ih

theorem clear_x (t x : Nat) (f : Registers) :
    Steps (3*x+2) (configAt base 7 ⟨t,0,x,f⟩)
      (configAt base 12 ⟨t,0,0,f⟩) := by
  induction x with
  | zero =>
    apply Steps.cons
    rw [step_7 hbound]
    simp only [↓reduceIte]
    apply Steps.cons
    rw [step_9 hbound]
    exact Steps.refl _
  | succ x ih =>
    have he : 3*(x+1)+2 = (3*x+2)+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_7 hbound]
    simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step_8 hbound]
    apply Steps.cons
    rw [step_5 hbound]
    exact ih

theorem cleanup (t h x : Nat) (f : Registers) :
    Steps ((2*h+1)+(3*x+2)) (configAt base 5 ⟨t,h,x,f⟩)
      (configAt base 12 ⟨t,0,0,f⟩) :=
  steps_trans (clear_h hbound t h x f) (clear_x hbound t x f)

theorem clear_t (t h x : Nat) (f : Registers) :
    Steps (2*t+1) (configAt base 10 ⟨t,h,x,f⟩)
      (configAt base 12 ⟨0,h,x,f⟩) := by
  induction t with
  | zero =>
    apply Steps.cons
    rw [step_10 hbound]
    exact Steps.refl _
  | succ t ih =>
    have he : 2*(t+1)+1 = (2*t+1)+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_10 hbound]
    simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step_11 hbound]
    exact ih

/-- Equality destroys T; inequality preserves T. H and X are cleared in both cases. -/
theorem compare (t h x : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps n (configAt base 0 ⟨t,h,x,f⟩)
      (configAt base 12 ⟨if h=x then 0 else t,0,0,f⟩) := by
  induction h generalizing x with
  | zero =>
    cases x with
    | zero =>
      refine ⟨(2*t+1)+2,by omega,?_⟩
      apply Steps.cons
      rw [step_0 hbound]
      simp only [↓reduceIte]
      apply Steps.cons
      rw [step_4 hbound]
      exact clear_t hbound t 0 0 f
    | succ x =>
      refine ⟨((2*0+1)+(3*x+2))+2,by omega,?_⟩
      apply Steps.cons
      rw [step_0 hbound]
      simp only [↓reduceIte,Nat.zero_ne_add_one]
      apply Steps.cons
      rw [step_4 hbound]
      simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
      exact cleanup hbound t 0 x f
  | succ h ih =>
    cases x with
    | zero =>
      refine ⟨((2*h+1)+(3*0+2))+3,by omega,?_⟩
      apply Steps.cons
      rw [step_0 hbound]
      simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
      apply Steps.cons
      rw [step_1 hbound]
      simp only [↓reduceIte]
      apply Steps.cons
      rw [step_3 hbound]
      exact cleanup hbound t h 0 f
    | succ x =>
      obtain ⟨n,hn,hh⟩ := ih x
      refine ⟨n+3,by omega,?_⟩
      apply Steps.cons
      rw [step_0 hbound]
      simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel,Nat.add_right_cancel_iff]
      apply Steps.cons
      rw [step_1 hbound]
      simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
      apply Steps.cons
      rw [step_2 hbound]
      exact hh

end C209Search.Primitive.AXGateCompare
