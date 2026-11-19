module
public import PrimitiveGuardEndpoint
@[expose] public section
set_option linter.unusedSimpArgs false
namespace C207Search.Primitive.SStage
open M207.Source
structure Store where
 t : Nat
 h : Nat
 x : Nat
 frame : Registers

def registers (s : Store) : Registers := fun r =>
 if r=2 then s.t else if r=7 then s.h else if r=8 then s.x else s.frame r

def configAt (pc : Nat) (s : Store) : Configuration := ⟨pc,registers s⟩
private theorem row4329 : program 4329 = some (.dec 2 4332 4330) := by decide +kernel
private theorem step4329 (t h x : Nat) (f : Registers) : step (configAt 4329 ⟨t,h,x,f⟩) = if t=0 then configAt 4332 ⟨t,h,x,f⟩ else configAt 4330 ⟨t - 1,h,x,f⟩ := by
  unfold step scalarNext configAt
  rw [row4329]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4330 : program 4330 = some (.inc 8 4331) := by decide +kernel
private theorem step4330 (t h x : Nat) (f : Registers) : step (configAt 4330 ⟨t,h,x,f⟩) = configAt 4331 ⟨t,h,x + 1,f⟩ := by
  unfold step scalarNext configAt
  rw [row4330]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4331 : program 4331 = some (.jump 4329) := by decide +kernel
private theorem step4331 (t h x : Nat) (f : Registers) : step (configAt 4331 ⟨t,h,x,f⟩) = configAt 4329 ⟨t,h,x,f⟩ := by
  unfold step scalarNext configAt
  rw [row4331]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4332 : program 4332 = some (.dec 7 4336 4333) := by decide +kernel
private theorem step4332 (t h x : Nat) (f : Registers) : step (configAt 4332 ⟨t,h,x,f⟩) = if h=0 then configAt 4336 ⟨t,h,x,f⟩ else configAt 4333 ⟨t,h - 1,x,f⟩ := by
  unfold step scalarNext configAt
  rw [row4332]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4333 : program 4333 = some (.inc 2 4334) := by decide +kernel
private theorem step4333 (t h x : Nat) (f : Registers) : step (configAt 4333 ⟨t,h,x,f⟩) = configAt 4334 ⟨t + 1,h,x,f⟩ := by
  unfold step scalarNext configAt
  rw [row4333]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4334 : program 4334 = some (.inc 8 4335) := by decide +kernel
private theorem step4334 (t h x : Nat) (f : Registers) : step (configAt 4334 ⟨t,h,x,f⟩) = configAt 4335 ⟨t,h,x + 1,f⟩ := by
  unfold step scalarNext configAt
  rw [row4334]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4335 : program 4335 = some (.jump 4332) := by decide +kernel
private theorem step4335 (t h x : Nat) (f : Registers) : step (configAt 4335 ⟨t,h,x,f⟩) = configAt 4332 ⟨t,h,x,f⟩ := by
  unfold step scalarNext configAt
  rw [row4335]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4336 : program 4336 = some (.dec 8 4339 4337) := by decide +kernel
private theorem step4336 (t h x : Nat) (f : Registers) : step (configAt 4336 ⟨t,h,x,f⟩) = if x=0 then configAt 4339 ⟨t,h,x,f⟩ else configAt 4337 ⟨t,h,x - 1,f⟩ := by
  unfold step scalarNext configAt
  rw [row4336]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4337 : program 4337 = some (.inc 7 4338) := by decide +kernel
private theorem step4337 (t h x : Nat) (f : Registers) : step (configAt 4337 ⟨t,h,x,f⟩) = configAt 4338 ⟨t,h + 1,x,f⟩ := by
  unfold step scalarNext configAt
  rw [row4337]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4338 : program 4338 = some (.jump 4336) := by decide +kernel
private theorem step4338 (t h x : Nat) (f : Registers) : step (configAt 4338 ⟨t,h,x,f⟩) = configAt 4336 ⟨t,h,x,f⟩ := by
  unfold step scalarNext configAt
  rw [row4338]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4339 : program 4339 = some (.inc 8 4340) := by decide +kernel
private theorem step4339 (t h x : Nat) (f : Registers) : step (configAt 4339 ⟨t,h,x,f⟩) = configAt 4340 ⟨t,h,x + 1,f⟩ := by
  unfold step scalarNext configAt
  rw [row4339]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4340 : program 4340 = some (.jump 0) := by decide +kernel
private theorem step4340 (t h x : Nat) (f : Registers) : step (configAt 4340 ⟨t,h,x,f⟩) = configAt 0 ⟨t,h,x,f⟩ := by
  unfold step scalarNext configAt
  rw [row4340]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

theorem drain_t (t h x : Nat) (f : Registers) :
 Steps (3*t+1) (configAt 4329 ⟨t,h,x,f⟩) (configAt 4332 ⟨0,h,x+t,f⟩) := by
 induction t generalizing x with
 | zero =>
   apply Steps.cons; rw [step4329]; simp; exact Steps.refl _
 | succ t ih =>
   have he : 3*(t+1)+1=(3*t+1)+1+1+1 := by omega
   rw [he]
   apply Steps.cons; rw [step4329]; simp
   apply Steps.cons; rw [step4330]
   apply Steps.cons; rw [step4331]
   simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (x+1)

theorem drain_h (h t x : Nat) (f : Registers) :
 Steps (4*h+1) (configAt 4332 ⟨t,h,x,f⟩) (configAt 4336 ⟨t+h,0,x+h,f⟩) := by
 induction h generalizing t x with
 | zero =>
   apply Steps.cons; rw [step4332]; simp; exact Steps.refl _
 | succ h ih =>
   have he : 4*(h+1)+1=(4*h+1)+1+1+1+1 := by omega
   rw [he]
   apply Steps.cons; rw [step4332]; simp
   apply Steps.cons; rw [step4333]
   apply Steps.cons; rw [step4334]
   apply Steps.cons; rw [step4335]
   simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (t+1) (x+1)

theorem drain_x (x t h : Nat) (f : Registers) :
 Steps (3*x+1) (configAt 4336 ⟨t,h,x,f⟩) (configAt 4339 ⟨t,h+x,0,f⟩) := by
 induction x generalizing h with
 | zero =>
   apply Steps.cons; rw [step4336]; simp; exact Steps.refl _
 | succ x ih =>
   have he : 3*(x+1)+1=(3*x+1)+1+1+1 := by omega
   rw [he]
   apply Steps.cons; rw [step4336]; simp
   apply Steps.cons; rw [step4337]
   apply Steps.cons; rw [step4338]
   simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (h+1)

theorem total (t h : Nat) (f : Registers) :
 Steps ((3*t+1)+(4*h+1)+(3*(t+h)+1)+2)
 (configAt 4329 ⟨t,h,0,f⟩) (configAt 0 ⟨h,t+h,1,f⟩) := by
 have h1 := drain_t t h 0 f
 have h2 := drain_h h 0 t f
 have h3 := drain_x (t+h) h 0 f
 simp only [Nat.zero_add] at h1 h2 h3
 apply steps_trans (steps_trans (steps_trans h1 h2) h3)
 apply Steps.cons; rw [step4339]
 apply Steps.cons; rw [step4340]; exact Steps.refl _
end C207Search.Primitive.SStage
