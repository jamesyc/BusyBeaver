module
public import PrimitiveStep
@[expose] public section
namespace C207Search.Primitive.AXReadH
open M207.Source
structure Store where
  w : Nat
  h : Nat
  x : Nat
  y : Nat
  frame : Registers

def registers (s : Store) : Registers := fun r =>
  if r = 1 then s.w else if r = 7 then s.h else if r = 8 then s.x else if r = 5 then s.y
  else s.frame r

def configAt (n : Nat) (s : Store) : Configuration := ⟨n, registers s⟩

def exitAt (s : Store) : Configuration := ⟨145, registers s⟩

@[simp] theorem read_w (s : Store) : registers s 1 = s.w := by simp [registers]
@[simp] theorem read_h (s : Store) : registers s 7 = s.h := by simp [registers]
@[simp] theorem read_x (s : Store) : registers s 8 = s.x := by simp [registers]
@[simp] theorem read_y (s : Store) : registers s 5 = s.y := by simp [registers]
private theorem row34 : program 131 = some (.dec 1 139 132) := by decide +kernel
private theorem step_131 (w h x y : Nat) (f : Registers) :
    step (configAt 131 ⟨w, h, x, y, f⟩) = if w = 0 then configAt 139 ⟨w, h, x, y, f⟩ else configAt 132 ⟨w - 1, h, x, y, f⟩  := by
  unfold step scalarNext configAt
  rw [row34]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

private theorem row35 : program 132 = some (.inc 5 133) := by decide +kernel
private theorem step_132 (w h x y : Nat) (f : Registers) :
    step (configAt 132 ⟨w, h, x, y, f⟩) = configAt 133 ⟨w, h, x, y + 1, f⟩  := by
  unfold step scalarNext configAt
  rw [row35]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

private theorem row36 : program 133 = some (.dec 8 135 134) := by decide +kernel
private theorem step_133 (w h x y : Nat) (f : Registers) :
    step (configAt 133 ⟨w, h, x, y, f⟩) = if x = 0 then configAt 135 ⟨w, h, x, y, f⟩ else configAt 134 ⟨w, h, x - 1, y, f⟩  := by
  unfold step scalarNext configAt
  rw [row36]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

private theorem row37 : program 134 = some (.jump 138) := by decide +kernel
private theorem step_134 (w h x y : Nat) (f : Registers) :
    step (configAt 134 ⟨w, h, x, y, f⟩) = configAt 138 ⟨w, h, x, y, f⟩  := by
  unfold step scalarNext configAt
  rw [row37]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

private theorem row38 : program 135 = some (.dec 5 138 136) := by decide +kernel
private theorem step_135 (w h x y : Nat) (f : Registers) :
    step (configAt 135 ⟨w, h, x, y, f⟩) = if y = 0 then configAt 138 ⟨w, h, x, y, f⟩ else configAt 136 ⟨w, h, x, y - 1, f⟩  := by
  unfold step scalarNext configAt
  rw [row38]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

private theorem row39 : program 136 = some (.inc 8 137) := by decide +kernel
private theorem step_136 (w h x y : Nat) (f : Registers) :
    step (configAt 136 ⟨w, h, x, y, f⟩) = configAt 137 ⟨w, h, x + 1, y, f⟩  := by
  unfold step scalarNext configAt
  rw [row39]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

private theorem row40 : program 137 = some (.jump 135) := by decide +kernel
private theorem step_137 (w h x y : Nat) (f : Registers) :
    step (configAt 137 ⟨w, h, x, y, f⟩) = configAt 135 ⟨w, h, x, y, f⟩  := by
  unfold step scalarNext configAt
  rw [row40]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

private theorem row41 : program 138 = some (.jump 131) := by decide +kernel
private theorem step_138 (w h x y : Nat) (f : Registers) :
    step (configAt 138 ⟨w, h, x, y, f⟩) = configAt 131 ⟨w, h, x, y, f⟩  := by
  unfold step scalarNext configAt
  rw [row41]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

private theorem row42 : program 139 = some (.dec 5 142 140) := by decide +kernel
private theorem step_139 (w h x y : Nat) (f : Registers) :
    step (configAt 139 ⟨w, h, x, y, f⟩) = if y = 0 then configAt 142 ⟨w, h, x, y, f⟩ else configAt 140 ⟨w, h, x, y - 1, f⟩  := by
  unfold step scalarNext configAt
  rw [row42]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

private theorem row43 : program 140 = some (.inc 1 141) := by decide +kernel
private theorem step_140 (w h x y : Nat) (f : Registers) :
    step (configAt 140 ⟨w, h, x, y, f⟩) = configAt 141 ⟨w + 1, h, x, y, f⟩  := by
  unfold step scalarNext configAt
  rw [row43]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

private theorem row44 : program 141 = some (.jump 139) := by decide +kernel
private theorem step_141 (w h x y : Nat) (f : Registers) :
    step (configAt 141 ⟨w, h, x, y, f⟩) = configAt 139 ⟨w, h, x, y, f⟩  := by
  unfold step scalarNext configAt
  rw [row44]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

private theorem row45 : program 142 = some (.dec 8 145 143) := by decide +kernel
private theorem step_142 (w h x y : Nat) (f : Registers) :
    step (configAt 142 ⟨w, h, x, y, f⟩) = if x = 0 then exitAt ⟨w, h, x, y, f⟩ else configAt 143 ⟨w, h, x - 1, y, f⟩  := by
  unfold step scalarNext configAt
  rw [row45]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

private theorem row46 : program 143 = some (.inc 7 144) := by decide +kernel
private theorem step_143 (w h x y : Nat) (f : Registers) :
    step (configAt 143 ⟨w, h, x, y, f⟩) = configAt 144 ⟨w, h + 1, x, y, f⟩  := by
  unfold step scalarNext configAt
  rw [row46]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

private theorem row47 : program 144 = some (.jump 142) := by decide +kernel
private theorem step_144 (w h x y : Nat) (f : Registers) :
    step (configAt 144 ⟨w, h, x, y, f⟩) = configAt 142 ⟨w, h, x, y, f⟩  := by
  unfold step scalarNext configAt
  rw [row47]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

theorem move_y_x (y w h x : Nat) (f : Registers) :
    Steps (3*y+1) (configAt 135 ⟨w, h, x, y, f⟩) (configAt 138 ⟨w, h, x + y, 0, f⟩) := by
  induction y generalizing x with
  | zero =>
    apply Steps.cons
    rw [step_135]
    try simp
    exact Steps.refl _
  | succ y ih =>
    have hn : 3*(y+1)+1 = (3*y+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step_135]
    try simp
    apply Steps.cons
    rw [step_136]
    try simp
    apply Steps.cons
    rw [step_137]
    try simp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (x+1)

theorem restore_y_w (y w h x : Nat) (f : Registers) :
    Steps (3*y+1) (configAt 139 ⟨w, h, x, y, f⟩) (configAt 142 ⟨w + y, h, x, 0, f⟩) := by
  induction y generalizing w with
  | zero =>
    apply Steps.cons
    rw [step_139]
    try simp
    exact Steps.refl _
  | succ y ih =>
    have hn : 3*(y+1)+1 = (3*y+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step_139]
    try simp
    apply Steps.cons
    rw [step_140]
    try simp
    apply Steps.cons
    rw [step_141]
    try simp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (w+1)

theorem restore_x_h (x w h y : Nat) (f : Registers) :
    Steps (3*x+1) (configAt 142 ⟨w, h, x, y, f⟩) (exitAt ⟨w, h + x, 0, y, f⟩) := by
  induction x generalizing h with
  | zero =>
    apply Steps.cons
    rw [step_142]
    try simp
    exact Steps.refl _
  | succ x ih =>
    have hn : 3*(x+1)+1 = (3*x+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step_142]
    try simp
    apply Steps.cons
    rw [step_143]
    try simp
    apply Steps.cons
    rw [step_144]
    try simp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (h+1)

/-- Cost of one outer diagonal-enumeration round. -/
def roundCost (p : Nat × Nat) : Nat := if p.1 = 0 then 3*p.2+8 else 5

private theorem round_positive (a b w h : Nat) (f : Registers) :
    Steps 5
      (configAt 131 ⟨w+1,h,a+1,b,f⟩) (configAt 131 ⟨w,h,a,b+1,f⟩) := by
  apply Steps.cons
  rw [step_131]
  try simp
  apply Steps.cons
  rw [step_132]
  try simp
  apply Steps.cons
  rw [step_133]
  try simp
  apply Steps.cons
  rw [step_134]
  try simp
  apply Steps.cons
  rw [step_138]
  try simp
  exact Steps.refl _

private theorem round_zero (b w h : Nat) (f : Registers) :
    Steps (3*b+8)
      (configAt 131 ⟨w+1,h,0,b,f⟩) (configAt 131 ⟨w,h,b+1,0,f⟩) := by
  have entrySegment : Steps 3
      (configAt 131 ⟨w+1,h,0,b,f⟩) (configAt 135 ⟨w,h,0,b+1,f⟩) := by
    apply Steps.cons
    rw [step_131]
    try simp
    apply Steps.cons
    rw [step_132]
    try simp
    apply Steps.cons
    rw [step_133]
    try simp
    exact Steps.refl _
  have middle := move_y_x (b+1) w h 0 f
  simp only [Nat.zero_add] at middle
  have suffix : Steps 1
      (configAt 138 ⟨w,h,b+1,0,f⟩) (configAt 131 ⟨w,h,b+1,0,f⟩) := by
    apply Steps.cons
    rw [step_138]
    exact Steps.refl _
  have q := steps_trans entrySegment (steps_trans middle suffix)
  have hn : 3*b+8 = 3+(3*(b+1)+1)+1 := by omega
  rw [hn]
  simpa [Nat.add_assoc] using q

theorem round (p : Nat × Nat) (w h : Nat) (f : Registers) :
    Steps (roundCost p)
      (configAt 131 ⟨w+1,h,p.1,p.2,f⟩)
      (configAt 131 ⟨w,h,(M6.Source.Cantor.advance p).1,(M6.Source.Cantor.advance p).2,f⟩) := by
  rcases p with ⟨a,b⟩
  cases a with
  | zero => simpa [roundCost, M6.Source.Cantor.advance] using round_zero b w h f
  | succ a => simpa [roundCost, M6.Source.Cantor.advance] using round_positive a b w h f

def loopCost : Nat → Nat × Nat → Nat
  | 0, _ => 1
  | n+1, p => roundCost p + loopCost n (M6.Source.Cantor.advance p)

/-- All-natural outer loop, measured by its decreasing W register. -/
theorem loop (n : Nat) (p : Nat × Nat) (h : Nat) (f : Registers) :
    Steps (loopCost n p)
      (configAt 131 ⟨n,h,p.1,p.2,f⟩)
      (configAt 139 ⟨0,h,(M6.Source.Cantor.decode (n+M6.Source.Cantor.pair p.1 p.2)).1,
        (M6.Source.Cantor.decode (n+M6.Source.Cantor.pair p.1 p.2)).2,f⟩) := by
  induction n generalizing p with
  | zero =>
    simp only [loopCost, Nat.zero_add, M6.Source.Cantor.decode_pair]
    apply Steps.cons
    rw [step_131]
    try simp
    exact Steps.refl _
  | succ n ih =>
    have q := steps_trans (round p n h f) (ih (M6.Source.Cantor.advance p))
    have hn : n + M6.Source.Cantor.pair (M6.Source.Cantor.advance p).1 (M6.Source.Cantor.advance p).2 =
        n+1+M6.Source.Cantor.pair p.1 p.2 := by rw [M6.Source.Cantor.pair_advance]; omega
    simpa only [loopCost, hn] using q

/-- Exact literal stack unpairing. All unmentioned registers remain arbitrary. -/
theorem unpair (n : Nat) (f : Registers) :
    Steps
      (loopCost n (0,0) + (3*(M6.Source.Cantor.decode n).2+1) + (3*(M6.Source.Cantor.decode n).1+1))
      (configAt 131 ⟨n,0,0,0,f⟩)
      (exitAt ⟨(M6.Source.Cantor.decode n).2,(M6.Source.Cantor.decode n).1,0,0,f⟩) := by
  have body := loop n (0,0) 0 f
  have yclean := restore_y_w (M6.Source.Cantor.decode n).2 0 0 (M6.Source.Cantor.decode n).1 f
  have xclean := restore_x_h (M6.Source.Cantor.decode n).1 (M6.Source.Cantor.decode n).2 0 0 f
  simp only [M6.Source.Cantor.pair, M6.Source.Cantor.triangle, Nat.add_zero] at body
  simp only [Nat.zero_add] at yclean xclean
  exact steps_trans (steps_trans body yclean) xclean



theorem unpair_add (n h : Nat) (f : Registers) :
    Steps
      (loopCost n (0,0) + (3*(M6.Source.Cantor.decode n).2+1) + (3*(M6.Source.Cantor.decode n).1+1))
      (configAt 131 ⟨n,h,0,0,f⟩)
      (exitAt ⟨(M6.Source.Cantor.decode n).2,h+(M6.Source.Cantor.decode n).1,0,0,f⟩) := by
  have body := loop n (0,0) h f
  have yclean := restore_y_w (M6.Source.Cantor.decode n).2 0 h (M6.Source.Cantor.decode n).1 f
  have xclean := restore_x_h (M6.Source.Cantor.decode n).1 (M6.Source.Cantor.decode n).2 h 0 f
  simp only [M6.Source.Cantor.pair, M6.Source.Cantor.triangle, Nat.add_zero] at body
  simp only [Nat.zero_add] at yclean
  exact steps_trans (steps_trans body yclean) xclean

end C207Search.Primitive.AXReadH
