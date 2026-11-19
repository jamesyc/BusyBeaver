module
public import PrimitiveStep
@[expose] public section
set_option linter.unusedSimpArgs false
namespace C207Search.Primitive.MPGuard
open M207.Source
def registers (t h x : Nat) (f : Registers) : Registers := fun r =>
  if r = 2 then t else if r = 7 then h else if r = 8 then x else f r

def config (pc t h x : Nat) (f : Registers) : Configuration :=
  ⟨pc,registers t h x f⟩
private theorem row4289 : program 4289 = some (.dec 2 4292 4290) := by decide +kernel
theorem step4289 (t h x : Nat) (f : Registers) :
    step (config 4289 t h x f) = if t = 0 then config 4292 t h x f else config 4290 (t-1) h x f := by
  unfold step scalarNext config
  rw [row4289]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4290 : program 4290 = some (.inc 8 4291) := by decide +kernel
theorem step4290 (t h x : Nat) (f : Registers) :
    step (config 4290 t h x f) = config 4291 t h (x+1) f := by
  unfold step scalarNext config
  rw [row4290]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4291 : program 4291 = some (.jump 4289) := by decide +kernel
theorem step4291 (t h x : Nat) (f : Registers) :
    step (config 4291 t h x f) = config 4289 t h x f := by
  unfold step scalarNext config
  rw [row4291]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4292 : program 4292 = some (.dec 7 4296 4293) := by decide +kernel
theorem step4292 (t h x : Nat) (f : Registers) :
    step (config 4292 t h x f) = if h = 0 then config 4296 t h x f else config 4293 t (h-1) x f := by
  unfold step scalarNext config
  rw [row4292]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4293 : program 4293 = some (.dec 8 4295 4294) := by decide +kernel
theorem step4293 (t h x : Nat) (f : Registers) :
    step (config 4293 t h x f) = if x = 0 then config 4295 t h x f else config 4294 t h (x-1) f := by
  unfold step scalarNext config
  rw [row4293]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4294 : program 4294 = some (.jump 4292) := by decide +kernel
theorem step4294 (t h x : Nat) (f : Registers) :
    step (config 4294 t h x f) = config 4292 t h x f := by
  unfold step scalarNext config
  rw [row4294]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4295 : program 4295 = some (.jump 4297) := by decide +kernel
theorem step4295 (t h x : Nat) (f : Registers) :
    step (config 4295 t h x f) = config 4297 t h x f := by
  unfold step scalarNext config
  rw [row4295]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4296 : program 4296 = some (.dec 8 4302 4297) := by decide +kernel
theorem step4296 (t h x : Nat) (f : Registers) :
    step (config 4296 t h x f) = if x = 0 then config 4302 t h x f else config 4297 t h (x-1) f := by
  unfold step scalarNext config
  rw [row4296]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4297 : program 4297 = some (.dec 7 4299 4298) := by decide +kernel
theorem step4297 (t h x : Nat) (f : Registers) :
    step (config 4297 t h x f) = if h = 0 then config 4299 t h x f else config 4298 t (h-1) x f := by
  unfold step scalarNext config
  rw [row4297]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4298 : program 4298 = some (.jump 4297) := by decide +kernel
theorem step4298 (t h x : Nat) (f : Registers) :
    step (config 4298 t h x f) = config 4297 t h x f := by
  unfold step scalarNext config
  rw [row4298]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4299 : program 4299 = some (.dec 8 4301 4300) := by decide +kernel
theorem step4299 (t h x : Nat) (f : Registers) :
    step (config 4299 t h x f) = if x = 0 then config 4301 t h x f else config 4300 t h (x-1) f := by
  unfold step scalarNext config
  rw [row4299]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4300 : program 4300 = some (.jump 4297) := by decide +kernel
theorem step4300 (t h x : Nat) (f : Registers) :
    step (config 4300 t h x f) = config 4297 t h x f := by
  unfold step scalarNext config
  rw [row4300]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4301 : program 4301 = some (.jump 4328) := by decide +kernel
theorem step4301 (t h x : Nat) (f : Registers) :
    step (config 4301 t h x f) = config 4328 t h x f := by
  unfold step scalarNext config
  rw [row4301]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem drain_t (t h x : Nat) (f : Registers) :
    Steps (3*t+1) (config 4289 t h x f)
      (config 4292 0 h (x+t) f) := by
  induction t generalizing x with
  | zero =>
    apply Steps.cons
    rw [step4289]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ t ih =>
    have hn : 3*(t+1)+1 = (3*t+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step4289]
    simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step4290]
    apply Steps.cons
    rw [step4291]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (x+1)

theorem drain_h (t h x : Nat) (f : Registers) :
    Steps (2*h+1) (config 4297 t h x f) (config 4299 t 0 x f) := by
  induction h with
  | zero =>
    apply Steps.cons
    rw [step4297]
    simp only [↓reduceIte]
    exact Steps.refl _
  | succ h ih =>
    have hn : 2*(h+1)+1 = (2*h+1)+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step4297]
    simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step4298]
    exact ih

theorem drain_x (t x : Nat) (f : Registers) :
    Steps (3*x+2) (config 4299 t 0 x f) (config 4328 t 0 0 f) := by
  induction x with
  | zero =>
    apply Steps.cons
    rw [step4299]
    simp only [↓reduceIte]
    apply Steps.cons
    rw [step4301]
    exact Steps.refl _
  | succ x ih =>
    have hn : 3*(x+1)+2 = (3*x+2)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step4299]
    simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step4300]
    apply Steps.cons
    rw [step4297]
    simp only [↓reduceIte]
    exact ih

theorem cleanup (t h x : Nat) (f : Registers) :
    Steps (2*h+3*x+3) (config 4297 t h x f) (config 4328 t 0 0 f) := by
  have hn : 2*h+3*x+3 = (2*h+1)+(3*x+2) := by omega
  rw [hn]
  exact steps_trans (drain_h t h x f) (drain_x t x f)

theorem compare (t h x : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps n (config 4292 t h x f)
      (config (if h = x then 4302 else 4328) t 0 0 f) := by
  induction h generalizing x with
  | zero =>
    cases x with
    | zero =>
      refine ⟨2,by omega,?_⟩
      apply Steps.cons
      rw [step4292]
      simp only [↓reduceIte]
      apply Steps.cons
      rw [step4296]
      simp only [↓reduceIte]
      exact Steps.refl _
    | succ x =>
      refine ⟨(3*x+3)+1+1,by omega,?_⟩
      apply Steps.cons
      rw [step4292]
      simp only [↓reduceIte,Nat.zero_ne_add_one]
      apply Steps.cons
      rw [step4296]
      simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
      simpa only [Nat.mul_zero,Nat.zero_add] using cleanup t 0 x f
  | succ h ih =>
    cases x with
    | zero =>
      refine ⟨(2*h+3)+1+1+1,by omega,?_⟩
      apply Steps.cons
      rw [step4292]
      simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
      apply Steps.cons
      rw [step4293]
      simp only [↓reduceIte]
      apply Steps.cons
      rw [step4295]
      simpa only [Nat.mul_zero,Nat.add_zero] using cleanup t h 0 f
    | succ x =>
      obtain ⟨n,hn,hs⟩ := ih x
      refine ⟨n+1+1+1,by omega,?_⟩
      apply Steps.cons
      rw [step4292]
      simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel,Nat.add_right_cancel_iff]
      apply Steps.cons
      rw [step4293]
      simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
      apply Steps.cons
      rw [step4294]
      exact hs

/-- The actual MP equality guard clears T,H,X on both paths, retaining the
entire unrelated frame; equality alone reaches the success push at4302. -/
theorem guard (t h : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps n (config 4289 t h 0 f)
      (config (if t = h then 4302 else 4328) 0 0 0 f) := by
  obtain ⟨n,hn,hs⟩ := compare 0 h t f
  have a := drain_t t h 0 f
  simp only [Nat.zero_add] at a
  refine ⟨3*t+1+n,by omega,?_⟩
  simpa only [eq_comm] using steps_trans a hs


end C207Search.Primitive.MPGuard
