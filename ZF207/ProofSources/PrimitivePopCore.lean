module
public import PrimitiveStep
@[expose] public section
namespace C207Search.Primitive.PopCore
open M207.Source
structure Store where
  w : Nat
  h : Nat
  x : Nat
  y : Nat
  frame : Registers

def registers (s : Store) : Registers := fun r =>
  if r = 0 then s.w else if r = 7 then s.h else if r = 8 then s.x else if r = 5 then s.y
  else s.frame r

def configAt (offset n : Nat) (s : Store) : Configuration := ⟨offset+n, registers s⟩



@[simp] theorem read_w (s : Store) : registers s 0 = s.w := by simp [registers]
@[simp] theorem read_h (s : Store) : registers s 7 = s.h := by simp [registers]
@[simp] theorem read_x (s : Store) : registers s 8 = s.x := by simp [registers]
@[simp] theorem read_y (s : Store) : registers s 5 = s.y := by simp [registers]
def expected (offset : Nat) : Nat → Instruction
 | 0 => .dec 0 (offset+8) (offset+1)
 | 1 => .inc 5 (offset+2)
 | 2 => .dec 8 (offset+4) (offset+3)
 | 3 => .jump (offset+7)
 | 4 => .dec 5 (offset+7) (offset+5)
 | 5 => .inc 8 (offset+6)
 | 6 => .jump (offset+4)
 | 7 => .jump (offset+0)
 | 8 => .dec 5 (offset+11) (offset+9)
 | 9 => .inc 0 (offset+10)
 | 10 => .jump (offset+8)
 | _ => .halt
def Bound (offset : Nat) := ∀ j : Fin 11, program (offset+j.val) = some (expected offset j.val)
variable {offset : Nat} (hb : Bound offset)
include hb
private theorem step_4262 (w h x y : Nat) (f : Registers) :
    step (configAt offset 0 ⟨w, h, x, y, f⟩) = if w = 0 then configAt offset 8 ⟨w, h, x, y, f⟩ else configAt offset 1 ⟨w - 1, h, x, y, f⟩  := by
  have hx : program (offset+0) = some (expected offset 0) := hb ⟨0,by decide⟩
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

private theorem step_4263 (w h x y : Nat) (f : Registers) :
    step (configAt offset 1 ⟨w, h, x, y, f⟩) = configAt offset 2 ⟨w, h, x, y + 1, f⟩  := by
  have hx : program (offset+1) = some (expected offset 1) := hb ⟨1,by decide⟩
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

private theorem step_4264 (w h x y : Nat) (f : Registers) :
    step (configAt offset 2 ⟨w, h, x, y, f⟩) = if x = 0 then configAt offset 4 ⟨w, h, x, y, f⟩ else configAt offset 3 ⟨w, h, x - 1, y, f⟩  := by
  have hx : program (offset+2) = some (expected offset 2) := hb ⟨2,by decide⟩
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

private theorem step_4265 (w h x y : Nat) (f : Registers) :
    step (configAt offset 3 ⟨w, h, x, y, f⟩) = configAt offset 7 ⟨w, h, x, y, f⟩  := by
  have hx : program (offset+3) = some (expected offset 3) := hb ⟨3,by decide⟩
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

private theorem step_4266 (w h x y : Nat) (f : Registers) :
    step (configAt offset 4 ⟨w, h, x, y, f⟩) = if y = 0 then configAt offset 7 ⟨w, h, x, y, f⟩ else configAt offset 5 ⟨w, h, x, y - 1, f⟩  := by
  have hx : program (offset+4) = some (expected offset 4) := hb ⟨4,by decide⟩
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

private theorem step_4267 (w h x y : Nat) (f : Registers) :
    step (configAt offset 5 ⟨w, h, x, y, f⟩) = configAt offset 6 ⟨w, h, x + 1, y, f⟩  := by
  have hx : program (offset+5) = some (expected offset 5) := hb ⟨5,by decide⟩
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

private theorem step_4268 (w h x y : Nat) (f : Registers) :
    step (configAt offset 6 ⟨w, h, x, y, f⟩) = configAt offset 4 ⟨w, h, x, y, f⟩  := by
  have hx : program (offset+6) = some (expected offset 6) := hb ⟨6,by decide⟩
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

private theorem step_4269 (w h x y : Nat) (f : Registers) :
    step (configAt offset 7 ⟨w, h, x, y, f⟩) = configAt offset 0 ⟨w, h, x, y, f⟩  := by
  have hx : program (offset+7) = some (expected offset 7) := hb ⟨7,by decide⟩
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

private theorem step_4270 (w h x y : Nat) (f : Registers) :
    step (configAt offset 8 ⟨w, h, x, y, f⟩) = if y = 0 then configAt offset 11 ⟨w, h, x, y, f⟩ else configAt offset 9 ⟨w, h, x, y - 1, f⟩  := by
  have hx : program (offset+8) = some (expected offset 8) := hb ⟨8,by decide⟩
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

private theorem step_4271 (w h x y : Nat) (f : Registers) :
    step (configAt offset 9 ⟨w, h, x, y, f⟩) = configAt offset 10 ⟨w + 1, h, x, y, f⟩  := by
  have hx : program (offset+9) = some (expected offset 9) := hb ⟨9,by decide⟩
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

private theorem step_4272 (w h x y : Nat) (f : Registers) :
    step (configAt offset 10 ⟨w, h, x, y, f⟩) = configAt offset 8 ⟨w, h, x, y, f⟩  := by
  have hx : program (offset+10) = some (expected offset 10) := hb ⟨10,by decide⟩
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

theorem move_y_x (y w h x : Nat) (f : Registers) :
    Steps (3*y+1) (configAt offset 4 ⟨w, h, x, y, f⟩) (configAt offset 7 ⟨w, h, x + y, 0, f⟩) := by
  induction y generalizing x with
  | zero =>
    apply Steps.cons
    rw [step_4266 hb]
    try simp
    exact Steps.refl _
  | succ y ih =>
    have hn : 3*(y+1)+1 = (3*y+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step_4266 hb]
    try simp
    apply Steps.cons
    rw [step_4267 hb]
    try simp
    apply Steps.cons
    rw [step_4268 hb]
    try simp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (x+1)

theorem restore_y_w (y w h x : Nat) (f : Registers) :
    Steps (3*y+1) (configAt offset 8 ⟨w, h, x, y, f⟩) (configAt offset 11 ⟨w + y, h, x, 0, f⟩) := by
  induction y generalizing w with
  | zero =>
    apply Steps.cons
    rw [step_4270 hb]
    try simp
    exact Steps.refl _
  | succ y ih =>
    have hn : 3*(y+1)+1 = (3*y+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step_4270 hb]
    try simp
    apply Steps.cons
    rw [step_4271 hb]
    try simp
    apply Steps.cons
    rw [step_4272 hb]
    try simp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (w+1)

def roundCost (p : Nat × Nat) : Nat := if p.1 = 0 then 3*p.2+8 else 5

private theorem round_positive (a b w h : Nat) (f : Registers) :
    Steps 5
      (configAt offset 0 ⟨w+1,h,a+1,b,f⟩) (configAt offset 0 ⟨w,h,a,b+1,f⟩) := by
  apply Steps.cons
  rw [step_4262 hb]
  try simp
  apply Steps.cons
  rw [step_4263 hb]
  try simp
  apply Steps.cons
  rw [step_4264 hb]
  try simp
  apply Steps.cons
  rw [step_4265 hb]
  try simp
  apply Steps.cons
  rw [step_4269 hb]
  try simp
  exact Steps.refl _

private theorem round_zero (b w h : Nat) (f : Registers) :
    Steps (3*b+8)
      (configAt offset 0 ⟨w+1,h,0,b,f⟩) (configAt offset 0 ⟨w,h,b+1,0,f⟩) := by
  have entrySegment : Steps 3
      (configAt offset 0 ⟨w+1,h,0,b,f⟩) (configAt offset 4 ⟨w,h,0,b+1,f⟩) := by
    apply Steps.cons
    rw [step_4262 hb]
    try simp
    apply Steps.cons
    rw [step_4263 hb]
    try simp
    apply Steps.cons
    rw [step_4264 hb]
    try simp
    exact Steps.refl _
  have middle := move_y_x hb (b+1) w h 0 f
  simp only [Nat.zero_add] at middle
  have suffix : Steps 1
      (configAt offset 7 ⟨w,h,b+1,0,f⟩) (configAt offset 0 ⟨w,h,b+1,0,f⟩) := by
    apply Steps.cons
    rw [step_4269 hb]
    exact Steps.refl _
  have q := steps_trans entrySegment (steps_trans middle suffix)
  have hn : 3*b+8 = 3+(3*(b+1)+1)+1 := by omega
  rw [hn]
  simpa [Nat.add_assoc] using q

theorem round (p : Nat × Nat) (w h : Nat) (f : Registers) :
    Steps (roundCost p)
      (configAt offset 0 ⟨w+1,h,p.1,p.2,f⟩)
      (configAt offset 0 ⟨w,h,(M6.Source.Cantor.advance p).1,(M6.Source.Cantor.advance p).2,f⟩) := by
  rcases p with ⟨a,b⟩
  cases a with
  | zero => simpa [roundCost, M6.Source.Cantor.advance] using round_zero hb b w h f
  | succ a => simpa [roundCost, M6.Source.Cantor.advance] using round_positive hb a b w h f

def loopCost : Nat → Nat × Nat → Nat
  | 0, _ => 1
  | n+1, p => roundCost p + loopCost n (M6.Source.Cantor.advance p)

/-- All-natural outer loop, measured by its decreasing W register. -/
theorem loop (n : Nat) (p : Nat × Nat) (h : Nat) (f : Registers) :
    Steps (loopCost n p)
      (configAt offset 0 ⟨n,h,p.1,p.2,f⟩)
      (configAt offset 8 ⟨0,h,(M6.Source.Cantor.decode (n+M6.Source.Cantor.pair p.1 p.2)).1,
        (M6.Source.Cantor.decode (n+M6.Source.Cantor.pair p.1 p.2)).2,f⟩) := by
  induction n generalizing p with
  | zero =>
    simp only [loopCost, Nat.zero_add, M6.Source.Cantor.decode_pair]
    apply Steps.cons
    rw [step_4262 hb]
    try simp
    exact Steps.refl _
  | succ n ih =>
    have q := steps_trans (round hb p n h f) (ih (M6.Source.Cantor.advance p))
    have hn : n + M6.Source.Cantor.pair (M6.Source.Cantor.advance p).1 (M6.Source.Cantor.advance p).2 =
        n+1+M6.Source.Cantor.pair p.1 p.2 := by rw [M6.Source.Cantor.pair_advance]; omega
    simpa only [loopCost, hn] using q


theorem decode_prefix (n h : Nat) (f : Registers) :
 Steps (loopCost n (0,0)+(3*(M6.Source.Cantor.decode n).2+1))
 (configAt offset 0 ⟨n,h,0,0,f⟩)
 (configAt offset 11 ⟨(M6.Source.Cantor.decode n).2,h,(M6.Source.Cantor.decode n).1,0,f⟩) := by
 have a := loop hb n (0,0) h f
 have b := restore_y_w hb (M6.Source.Cantor.decode n).2 0 h (M6.Source.Cantor.decode n).1 f
 simp only [M6.Source.Cantor.pair,M6.Source.Cantor.triangle,Nat.add_zero] at a
 simp only [Nat.zero_add] at b
 exact steps_trans a b
omit hb in
theorem mp_bound : Bound 4262 := by unfold Bound; decide +kernel
end C207Search.Primitive.PopCore
