module
public import PrimitiveResidual
@[expose] public section
set_option linter.unusedSimpArgs false
namespace C207Search.Primitive.FetchPrefix
open M207.Source
structure Store where
  n : Nat
  l : Nat
  x : Nat
  frame : Registers

def registers (s : Store) : Registers := fun r =>
  if r = 6 then s.n else if r = 1 then s.l else if r = 8 then s.x else s.frame r

def configAt (k : Nat) (s : Store) : Configuration := ⟨k,registers s⟩
private theorem row25 : program 25 = some (.dec 1 27 26) := by decide +kernel
private theorem step_25 (n l x : Nat) (f : Registers) :
    step (configAt 25 ⟨n,l,x,f⟩) = if l = 0 then configAt 27 ⟨n,l,x,f⟩ else configAt 26 ⟨n,l-1,x,f⟩ := by
  unfold step scalarNext configAt
  rw [row25]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row26 : program 26 = some (.jump 34) := by decide +kernel
private theorem step_26 (n l x : Nat) (f : Registers) :
    step (configAt 26 ⟨n,l,x,f⟩) = configAt 34 ⟨n,l,x,f⟩ := by
  unfold step scalarNext configAt
  rw [row26]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row27 : program 27 = some (.dec 6 31 28) := by decide +kernel
private theorem step_27 (n l x : Nat) (f : Registers) :
    step (configAt 27 ⟨n,l,x,f⟩) = if n = 0 then configAt 31 ⟨n,l,x,f⟩ else configAt 28 ⟨n-1,l,x,f⟩ := by
  unfold step scalarNext configAt
  rw [row27]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row28 : program 28 = some (.inc 1 29) := by decide +kernel
private theorem step_28 (n l x : Nat) (f : Registers) :
    step (configAt 28 ⟨n,l,x,f⟩) = configAt 29 ⟨n,l+1,x,f⟩ := by
  unfold step scalarNext configAt
  rw [row28]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row29 : program 29 = some (.inc 8 30) := by decide +kernel
private theorem step_29 (n l x : Nat) (f : Registers) :
    step (configAt 29 ⟨n,l,x,f⟩) = configAt 30 ⟨n,l,x+1,f⟩ := by
  unfold step scalarNext configAt
  rw [row29]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row30 : program 30 = some (.jump 27) := by decide +kernel
private theorem step_30 (n l x : Nat) (f : Registers) :
    step (configAt 30 ⟨n,l,x,f⟩) = configAt 27 ⟨n,l,x,f⟩ := by
  unfold step scalarNext configAt
  rw [row30]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row31 : program 31 = some (.inc 6 32) := by decide +kernel
private theorem step_31 (n l x : Nat) (f : Registers) :
    step (configAt 31 ⟨n,l,x,f⟩) = configAt 32 ⟨n+1,l,x,f⟩ := by
  unfold step scalarNext configAt
  rw [row31]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row32 : program 32 = some (.dec 8 34 33) := by decide +kernel
private theorem step_32 (n l x : Nat) (f : Registers) :
    step (configAt 32 ⟨n,l,x,f⟩) = if x = 0 then configAt 34 ⟨n,l,x,f⟩ else configAt 33 ⟨n,l,x-1,f⟩ := by
  unfold step scalarNext configAt
  rw [row32]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row33 : program 33 = some (.jump 31) := by decide +kernel
private theorem step_33 (n l x : Nat) (f : Registers) :
    step (configAt 33 ⟨n,l,x,f⟩) = configAt 31 ⟨n,l,x,f⟩ := by
  unfold step scalarNext configAt
  rw [row33]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem drain_n (n l x : Nat) (f : Registers) :
    Steps (4*n+1) (configAt 27 ⟨n,l,x,f⟩)
      (configAt 31 ⟨0,l+n,x+n,f⟩) := by
  induction n generalizing l x with
  | zero =>
    apply Steps.cons
    rw [step_27]
    simp only [↓reduceIte, Nat.add_zero]
    exact Steps.refl _
  | succ n ih =>
    have he : 4*(n+1)+1 = (4*n+1)+1+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_27]
    simp only [Nat.add_eq_zero_iff, Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte]
    apply Steps.cons
    rw [step_28]
    apply Steps.cons
    rw [step_29]
    apply Steps.cons
    rw [step_30]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (l+1) (x+1)

theorem restore_x (x n l : Nat) (f : Registers) :
    Steps (3*x+2) (configAt 31 ⟨n,l,x,f⟩)
      (configAt 34 ⟨n+x+1,l,0,f⟩) := by
  induction x generalizing n with
  | zero =>
    apply Steps.cons
    rw [step_31]
    apply Steps.cons
    rw [step_32]
    simp only [↓reduceIte, Nat.add_zero]
    exact Steps.refl _
  | succ x ih =>
    have he : 3*(x+1)+2 = (3*x+2)+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_31]
    apply Steps.cons
    rw [step_32]
    simp only [Nat.add_eq_zero_iff, Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte]
    apply Steps.cons
    rw [step_33]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n+1)

theorem positive (n l : Nat) (f : Registers) :
    Steps 2 (configAt 25 ⟨n,l+1,0,f⟩) (configAt 34 ⟨n,l,0,f⟩) := by
  apply Steps.cons
  rw [step_25]
  simp only [Nat.add_eq_zero_iff, Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte]
  apply Steps.cons
  rw [step_26]
  exact Steps.refl _

theorem fresh (n : Nat) (f : Registers) :
    Steps (7*n+4) (configAt 25 ⟨n,0,0,f⟩) (configAt 34 ⟨n+1,n,0,f⟩) := by
  have hd := drain_n n 0 0 f
  simp only [Nat.zero_add] at hd
  have h := steps_trans hd (restore_x n 0 n f)
  simp only [Nat.zero_add] at h
  have he : 7*n+4 = ((4*n+1)+(3*n+2))+1 := by omega
  rw [he]
  apply Steps.cons
  rw [step_25]
  simp only [↓reduceIte]
  exact h


end C207Search.Primitive.FetchPrefix
