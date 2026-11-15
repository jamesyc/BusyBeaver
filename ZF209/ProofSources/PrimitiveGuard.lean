module
public import PrimitiveUnpairEndpoint
@[expose] public section
namespace C209Search.Primitive.Unpair
open M209.Source
private theorem grow0 : program 0 = some (.dec 7 4 1) := by decide +kernel
private theorem gstep0 (w h x y : Nat) (f : Registers) : step (configAt 0 ⟨w,h,x,y,f⟩) = if h = 0 then configAt 4 ⟨w,h,x,y,f⟩ else configAt 1 ⟨w,h - 1,x,y,f⟩ := by
  unfold step scalarNext configAt
  rw [grow0]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem grow1 : program 1 = some (.dec 8 3 2) := by decide +kernel
private theorem gstep1 (w h x y : Nat) (f : Registers) : step (configAt 1 ⟨w,h,x,y,f⟩) = if x = 0 then configAt 3 ⟨w,h,x,y,f⟩ else configAt 2 ⟨w,h,x - 1,y,f⟩ := by
  unfold step scalarNext configAt
  rw [grow1]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem grow2 : program 2 = some (.jump 0) := by decide +kernel
private theorem gstep2 (w h x y : Nat) (f : Registers) : step (configAt 2 ⟨w,h,x,y,f⟩) = configAt 0 ⟨w,h,x,y,f⟩ := by
  unfold step scalarNext configAt
  rw [grow2]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem grow3 : program 3 = some (.jump 5) := by decide +kernel
private theorem gstep3 (w h x y : Nat) (f : Registers) : step (configAt 3 ⟨w,h,x,y,f⟩) = configAt 5 ⟨w,h,x,y,f⟩ := by
  unfold step scalarNext configAt
  rw [grow3]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem grow4 : program 4 = some (.dec 8 10 5) := by decide +kernel
private theorem gstep4 (w h x y : Nat) (f : Registers) : step (configAt 4 ⟨w,h,x,y,f⟩) = if x = 0 then configAt 10 ⟨w,h,x,y,f⟩ else configAt 5 ⟨w,h,x - 1,y,f⟩ := by
  unfold step scalarNext configAt
  rw [grow4]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem grow5 : program 5 = some (.dec 7 7 6) := by decide +kernel
private theorem gstep5 (w h x y : Nat) (f : Registers) : step (configAt 5 ⟨w,h,x,y,f⟩) = if h = 0 then configAt 7 ⟨w,h,x,y,f⟩ else configAt 6 ⟨w,h - 1,x,y,f⟩ := by
  unfold step scalarNext configAt
  rw [grow5]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem grow6 : program 6 = some (.jump 5) := by decide +kernel
private theorem gstep6 (w h x y : Nat) (f : Registers) : step (configAt 6 ⟨w,h,x,y,f⟩) = configAt 5 ⟨w,h,x,y,f⟩ := by
  unfold step scalarNext configAt
  rw [grow6]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem grow7 : program 7 = some (.dec 8 9 8) := by decide +kernel
private theorem gstep7 (w h x y : Nat) (f : Registers) : step (configAt 7 ⟨w,h,x,y,f⟩) = if x = 0 then configAt 9 ⟨w,h,x,y,f⟩ else configAt 8 ⟨w,h,x - 1,y,f⟩ := by
  unfold step scalarNext configAt
  rw [grow7]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem grow8 : program 8 = some (.jump 5) := by decide +kernel
private theorem gstep8 (w h x y : Nat) (f : Registers) : step (configAt 8 ⟨w,h,x,y,f⟩) = configAt 5 ⟨w,h,x,y,f⟩ := by
  unfold step scalarNext configAt
  rw [grow8]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem grow9 : program 9 = some (.jump 11) := by decide +kernel
private theorem gstep9 (w h x y : Nat) (f : Registers) : step (configAt 9 ⟨w,h,x,y,f⟩) = configAt 11 ⟨w,h,x,y,f⟩ := by
  unfold step scalarNext configAt
  rw [grow9]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, exitAt, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

theorem clear_x (x w y : Nat) (f : Registers) :
 ∃n, Steps n (configAt 7 ⟨w,0,x,y,f⟩) (configAt 11 ⟨w,0,0,y,f⟩) := by
 induction x with
 | zero =>
   refine ⟨2, Steps.cons ?_⟩
   rw [gstep7]; simp
   apply Steps.cons; rw [gstep9]; exact Steps.refl _
 | succ x ih =>
   obtain ⟨n,hn⟩ := ih
   refine ⟨n+1+1+1, Steps.cons ?_⟩
   rw [gstep7]; simp
   apply Steps.cons; rw [gstep8]
   apply Steps.cons; rw [gstep5]; simp
   exact hn

theorem clear_hx (h x w y : Nat) (f : Registers) :
 ∃n, Steps n (configAt 5 ⟨w,h,x,y,f⟩) (configAt 11 ⟨w,0,0,y,f⟩) := by
 induction h with
 | zero =>
   obtain ⟨n,hn⟩ := clear_x x w y f
   refine ⟨n+1, Steps.cons ?_⟩
   rw [gstep5]; simp; exact hn
 | succ h ih =>
   obtain ⟨n,hn⟩ := ih
   refine ⟨n+1+1, Steps.cons ?_⟩
   rw [gstep5]; simp
   apply Steps.cons; rw [gstep6]; exact hn

theorem guard_equal (h w y : Nat) (f : Registers) :
 ∃n, Steps n (configAt 0 ⟨w,h,h,y,f⟩) (configAt 10 ⟨w,0,0,y,f⟩) := by
 induction h with
 | zero =>
   refine ⟨2, Steps.cons ?_⟩
   rw [gstep0]; simp
   apply Steps.cons; rw [gstep4]; simp; exact Steps.refl _
 | succ h ih =>
   obtain ⟨n,hn⟩ := ih
   refine ⟨n+1+1+1, Steps.cons ?_⟩
   rw [gstep0]; simp
   apply Steps.cons; rw [gstep1]; simp
   apply Steps.cons; rw [gstep2]; exact hn

theorem guard_unequal (h x w y : Nat) (f : Registers) (hne : h ≠ x) :
 ∃n, Steps n (configAt 0 ⟨w,h,x,y,f⟩) (configAt 11 ⟨w,0,0,y,f⟩) := by
 induction h generalizing x with
 | zero =>
   cases x with
   | zero => exact False.elim (hne rfl)
   | succ x =>
     obtain ⟨n,hn⟩ := clear_hx 0 x w y f
     refine ⟨n+1+1, Steps.cons ?_⟩
     rw [gstep0]; simp
     apply Steps.cons; rw [gstep4]; simp; exact hn
 | succ h ih =>
   cases x with
   | zero =>
     obtain ⟨n,hn⟩ := clear_hx h 0 w y f
     refine ⟨n+1+1+1, Steps.cons ?_⟩
     rw [gstep0]; simp
     apply Steps.cons; rw [gstep1]; simp
     apply Steps.cons; rw [gstep3]; exact hn
   | succ x =>
     obtain ⟨n,hn⟩ := ih x (by omega)
     refine ⟨n+1+1+1, Steps.cons ?_⟩
     rw [gstep0]; simp
     apply Steps.cons; rw [gstep1]; simp
     apply Steps.cons; rw [gstep2]; exact hn
end C209Search.Primitive.Unpair
