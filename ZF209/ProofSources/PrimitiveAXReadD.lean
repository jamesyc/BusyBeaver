module
public import PrimitiveStep
@[expose] public section
namespace C209Search.Primitive.AXReadD
open M209.Source
structure Store where
  w : Nat
  h : Nat
  x : Nat
  y : Nat
  frame : Registers

def registers (s : Store) : Registers := fun r =>
  if r = 1 then s.w else if r = 3 then s.h else if r = 8 then s.x else if r = 5 then s.y
  else s.frame r

def configAt (n : Nat) (s : Store) : Configuration := ⟨n, registers s⟩

def exitAt (s : Store) : Configuration := ⟨238, registers s⟩

@[simp] theorem read_w (s : Store) : registers s 1 = s.w := by simp [registers]
@[simp] theorem read_h (s : Store) : registers s 3 = s.h := by simp [registers]
@[simp] theorem read_x (s : Store) : registers s 8 = s.x := by simp [registers]
@[simp] theorem read_y (s : Store) : registers s 5 = s.y := by simp [registers]
private theorem row34 : program 224 = some (.dec 1 232 225) := by decide +kernel
private theorem step_224 (w h x y : Nat) (f : Registers) :
    step (configAt 224 ⟨w, h, x, y, f⟩) = if w = 0 then configAt 232 ⟨w, h, x, y, f⟩ else configAt 225 ⟨w - 1, h, x, y, f⟩  := by
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

private theorem row35 : program 225 = some (.inc 5 226) := by decide +kernel
private theorem step_225 (w h x y : Nat) (f : Registers) :
    step (configAt 225 ⟨w, h, x, y, f⟩) = configAt 226 ⟨w, h, x, y + 1, f⟩  := by
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

private theorem row36 : program 226 = some (.dec 8 228 227) := by decide +kernel
private theorem step_226 (w h x y : Nat) (f : Registers) :
    step (configAt 226 ⟨w, h, x, y, f⟩) = if x = 0 then configAt 228 ⟨w, h, x, y, f⟩ else configAt 227 ⟨w, h, x - 1, y, f⟩  := by
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

private theorem row37 : program 227 = some (.jump 231) := by decide +kernel
private theorem step_227 (w h x y : Nat) (f : Registers) :
    step (configAt 227 ⟨w, h, x, y, f⟩) = configAt 231 ⟨w, h, x, y, f⟩  := by
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

private theorem row38 : program 228 = some (.dec 5 231 229) := by decide +kernel
private theorem step_228 (w h x y : Nat) (f : Registers) :
    step (configAt 228 ⟨w, h, x, y, f⟩) = if y = 0 then configAt 231 ⟨w, h, x, y, f⟩ else configAt 229 ⟨w, h, x, y - 1, f⟩  := by
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

private theorem row39 : program 229 = some (.inc 8 230) := by decide +kernel
private theorem step_229 (w h x y : Nat) (f : Registers) :
    step (configAt 229 ⟨w, h, x, y, f⟩) = configAt 230 ⟨w, h, x + 1, y, f⟩  := by
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

private theorem row40 : program 230 = some (.jump 228) := by decide +kernel
private theorem step_230 (w h x y : Nat) (f : Registers) :
    step (configAt 230 ⟨w, h, x, y, f⟩) = configAt 228 ⟨w, h, x, y, f⟩  := by
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

private theorem row41 : program 231 = some (.jump 224) := by decide +kernel
private theorem step_231 (w h x y : Nat) (f : Registers) :
    step (configAt 231 ⟨w, h, x, y, f⟩) = configAt 224 ⟨w, h, x, y, f⟩  := by
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

private theorem row42 : program 232 = some (.dec 5 235 233) := by decide +kernel
private theorem step_232 (w h x y : Nat) (f : Registers) :
    step (configAt 232 ⟨w, h, x, y, f⟩) = if y = 0 then configAt 235 ⟨w, h, x, y, f⟩ else configAt 233 ⟨w, h, x, y - 1, f⟩  := by
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

private theorem row43 : program 233 = some (.inc 1 234) := by decide +kernel
private theorem step_233 (w h x y : Nat) (f : Registers) :
    step (configAt 233 ⟨w, h, x, y, f⟩) = configAt 234 ⟨w + 1, h, x, y, f⟩  := by
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

private theorem row44 : program 234 = some (.jump 232) := by decide +kernel
private theorem step_234 (w h x y : Nat) (f : Registers) :
    step (configAt 234 ⟨w, h, x, y, f⟩) = configAt 232 ⟨w, h, x, y, f⟩  := by
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

private theorem row45 : program 235 = some (.dec 8 238 236) := by decide +kernel
private theorem step_235 (w h x y : Nat) (f : Registers) :
    step (configAt 235 ⟨w, h, x, y, f⟩) = if x = 0 then exitAt ⟨w, h, x, y, f⟩ else configAt 236 ⟨w, h, x - 1, y, f⟩  := by
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

private theorem row46 : program 236 = some (.inc 3 237) := by decide +kernel
private theorem step_236 (w h x y : Nat) (f : Registers) :
    step (configAt 236 ⟨w, h, x, y, f⟩) = configAt 237 ⟨w, h + 1, x, y, f⟩  := by
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

private theorem row47 : program 237 = some (.jump 235) := by decide +kernel
private theorem step_237 (w h x y : Nat) (f : Registers) :
    step (configAt 237 ⟨w, h, x, y, f⟩) = configAt 235 ⟨w, h, x, y, f⟩  := by
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
    Steps (3*y+1) (configAt 228 ⟨w, h, x, y, f⟩) (configAt 231 ⟨w, h, x + y, 0, f⟩) := by
  induction y generalizing x with
  | zero =>
    apply Steps.cons
    rw [step_228]
    try simp
    exact Steps.refl _
  | succ y ih =>
    have hn : 3*(y+1)+1 = (3*y+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step_228]
    try simp
    apply Steps.cons
    rw [step_229]
    try simp
    apply Steps.cons
    rw [step_230]
    try simp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (x+1)

theorem restore_y_w (y w h x : Nat) (f : Registers) :
    Steps (3*y+1) (configAt 232 ⟨w, h, x, y, f⟩) (configAt 235 ⟨w + y, h, x, 0, f⟩) := by
  induction y generalizing w with
  | zero =>
    apply Steps.cons
    rw [step_232]
    try simp
    exact Steps.refl _
  | succ y ih =>
    have hn : 3*(y+1)+1 = (3*y+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step_232]
    try simp
    apply Steps.cons
    rw [step_233]
    try simp
    apply Steps.cons
    rw [step_234]
    try simp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (w+1)

theorem restore_x_h (x w h y : Nat) (f : Registers) :
    Steps (3*x+1) (configAt 235 ⟨w, h, x, y, f⟩) (exitAt ⟨w, h + x, 0, y, f⟩) := by
  induction x generalizing h with
  | zero =>
    apply Steps.cons
    rw [step_235]
    try simp
    exact Steps.refl _
  | succ x ih =>
    have hn : 3*(x+1)+1 = (3*x+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step_235]
    try simp
    apply Steps.cons
    rw [step_236]
    try simp
    apply Steps.cons
    rw [step_237]
    try simp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (h+1)

/-- Cost of one outer diagonal-enumeration round. -/
def roundCost (p : Nat × Nat) : Nat := if p.1 = 0 then 3*p.2+8 else 5

private theorem round_positive (a b w h : Nat) (f : Registers) :
    Steps 5
      (configAt 224 ⟨w+1,h,a+1,b,f⟩) (configAt 224 ⟨w,h,a,b+1,f⟩) := by
  apply Steps.cons
  rw [step_224]
  try simp
  apply Steps.cons
  rw [step_225]
  try simp
  apply Steps.cons
  rw [step_226]
  try simp
  apply Steps.cons
  rw [step_227]
  try simp
  apply Steps.cons
  rw [step_231]
  try simp
  exact Steps.refl _

private theorem round_zero (b w h : Nat) (f : Registers) :
    Steps (3*b+8)
      (configAt 224 ⟨w+1,h,0,b,f⟩) (configAt 224 ⟨w,h,b+1,0,f⟩) := by
  have entrySegment : Steps 3
      (configAt 224 ⟨w+1,h,0,b,f⟩) (configAt 228 ⟨w,h,0,b+1,f⟩) := by
    apply Steps.cons
    rw [step_224]
    try simp
    apply Steps.cons
    rw [step_225]
    try simp
    apply Steps.cons
    rw [step_226]
    try simp
    exact Steps.refl _
  have middle := move_y_x (b+1) w h 0 f
  simp only [Nat.zero_add] at middle
  have suffix : Steps 1
      (configAt 231 ⟨w,h,b+1,0,f⟩) (configAt 224 ⟨w,h,b+1,0,f⟩) := by
    apply Steps.cons
    rw [step_231]
    exact Steps.refl _
  have q := steps_trans entrySegment (steps_trans middle suffix)
  have hn : 3*b+8 = 3+(3*(b+1)+1)+1 := by omega
  rw [hn]
  simpa [Nat.add_assoc] using q

theorem round (p : Nat × Nat) (w h : Nat) (f : Registers) :
    Steps (roundCost p)
      (configAt 224 ⟨w+1,h,p.1,p.2,f⟩)
      (configAt 224 ⟨w,h,(M6.Source.Cantor.advance p).1,(M6.Source.Cantor.advance p).2,f⟩) := by
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
      (configAt 224 ⟨n,h,p.1,p.2,f⟩)
      (configAt 232 ⟨0,h,(M6.Source.Cantor.decode (n+M6.Source.Cantor.pair p.1 p.2)).1,
        (M6.Source.Cantor.decode (n+M6.Source.Cantor.pair p.1 p.2)).2,f⟩) := by
  induction n generalizing p with
  | zero =>
    simp only [loopCost, Nat.zero_add, M6.Source.Cantor.decode_pair]
    apply Steps.cons
    rw [step_224]
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
      (configAt 224 ⟨n,0,0,0,f⟩)
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
      (configAt 224 ⟨n,h,0,0,f⟩)
      (exitAt ⟨(M6.Source.Cantor.decode n).2,h+(M6.Source.Cantor.decode n).1,0,0,f⟩) := by
  have body := loop n (0,0) h f
  have yclean := restore_y_w (M6.Source.Cantor.decode n).2 0 h (M6.Source.Cantor.decode n).1 f
  have xclean := restore_x_h (M6.Source.Cantor.decode n).1 (M6.Source.Cantor.decode n).2 h 0 f
  simp only [M6.Source.Cantor.pair, M6.Source.Cantor.triangle, Nat.add_zero] at body
  simp only [Nat.zero_add] at yclean
  exact steps_trans (steps_trans body yclean) xclean

end C209Search.Primitive.AXReadD
