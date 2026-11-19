module
public import PrimitiveStep
@[expose] public section
set_option linter.unusedSimpArgs false
namespace C207Search.Primitive.PairCore
open M207.Source
structure Store where
 t : Nat
 w : Nat
 x : Nat
 y : Nat
 frame : Registers

def registers (s : Store) : Registers := fun r =>
 if r=2 then s.t else if r=0 then s.w else if r=8 then s.x else if r=5 then s.y else s.frame r

def configAt (offset pc : Nat) (s : Store) : Configuration := ⟨offset+pc,registers s⟩
def expected (offset : Nat) : Nat → Instruction
 | 0 => .dec 2 (offset+4) (offset+1)
 | 1 => .inc 5 (offset+2)
 | 2 => .inc 8 (offset+3)
 | 3 => .jump (offset+0)
 | 4 => .dec 8 (offset+10) (offset+5)
 | 5 => .inc 5 (offset+6)
 | 6 => .dec 8 (offset+9) (offset+7)
 | 7 => .inc 2 (offset+8)
 | 8 => .jump (offset+6)
 | 9 => .jump (offset+0)
 | _ => .halt

def Bound (offset : Nat) : Prop := ∀ j : Fin 10,
 program (offset+j.val) = some (expected offset j.val)
variable {offset : Nat} (hbound : Bound offset)
include hbound
theorem step_0 (t w x y : Nat) (f : Registers) : step (configAt offset 0 ⟨t,w,x,y,f⟩) = if t=0 then configAt offset 4 ⟨t,w,x,y,f⟩ else configAt offset 1 ⟨t - 1,w,x,y,f⟩ := by
  have hb : program (offset+0) = some (.dec 2 (offset+4) (offset+1)) := by simpa [expected] using hbound ⟨0,by decide⟩
  unfold step scalarNext configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_1 (t w x y : Nat) (f : Registers) : step (configAt offset 1 ⟨t,w,x,y,f⟩) = configAt offset 2 ⟨t,w,x,y + 1,f⟩ := by
  have hb : program (offset+1) = some (.inc 5 (offset+2)) := by simpa [expected] using hbound ⟨1,by decide⟩
  unfold step scalarNext configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_2 (t w x y : Nat) (f : Registers) : step (configAt offset 2 ⟨t,w,x,y,f⟩) = configAt offset 3 ⟨t,w,x + 1,y,f⟩ := by
  have hb : program (offset+2) = some (.inc 8 (offset+3)) := by simpa [expected] using hbound ⟨2,by decide⟩
  unfold step scalarNext configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_3 (t w x y : Nat) (f : Registers) : step (configAt offset 3 ⟨t,w,x,y,f⟩) = configAt offset 0 ⟨t,w,x,y,f⟩ := by
  have hb : program (offset+3) = some (.jump (offset+0)) := by simpa [expected] using hbound ⟨3,by decide⟩
  unfold step scalarNext configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_4 (t w x y : Nat) (f : Registers) : step (configAt offset 4 ⟨t,w,x,y,f⟩) = if x=0 then configAt offset 10 ⟨t,w,x,y,f⟩ else configAt offset 5 ⟨t,w,x - 1,y,f⟩ := by
  have hb : program (offset+4) = some (.dec 8 (offset+10) (offset+5)) := by simpa [expected] using hbound ⟨4,by decide⟩
  unfold step scalarNext configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_5 (t w x y : Nat) (f : Registers) : step (configAt offset 5 ⟨t,w,x,y,f⟩) = configAt offset 6 ⟨t,w,x,y + 1,f⟩ := by
  have hb : program (offset+5) = some (.inc 5 (offset+6)) := by simpa [expected] using hbound ⟨5,by decide⟩
  unfold step scalarNext configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_6 (t w x y : Nat) (f : Registers) : step (configAt offset 6 ⟨t,w,x,y,f⟩) = if x=0 then configAt offset 9 ⟨t,w,x,y,f⟩ else configAt offset 7 ⟨t,w,x - 1,y,f⟩ := by
  have hb : program (offset+6) = some (.dec 8 (offset+9) (offset+7)) := by simpa [expected] using hbound ⟨6,by decide⟩
  unfold step scalarNext configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_7 (t w x y : Nat) (f : Registers) : step (configAt offset 7 ⟨t,w,x,y,f⟩) = configAt offset 8 ⟨t + 1,w,x,y,f⟩ := by
  have hb : program (offset+7) = some (.inc 2 (offset+8)) := by simpa [expected] using hbound ⟨7,by decide⟩
  unfold step scalarNext configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_8 (t w x y : Nat) (f : Registers) : step (configAt offset 8 ⟨t,w,x,y,f⟩) = configAt offset 6 ⟨t,w,x,y,f⟩ := by
  have hb : program (offset+8) = some (.jump (offset+6)) := by simpa [expected] using hbound ⟨8,by decide⟩
  unfold step scalarNext configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_9 (t w x y : Nat) (f : Registers) : step (configAt offset 9 ⟨t,w,x,y,f⟩) = configAt offset 0 ⟨t,w,x,y,f⟩ := by
  have hb : program (offset+9) = some (.jump (offset+0)) := by simpa [expected] using hbound ⟨9,by decide⟩
  unfold step scalarNext configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem Steps.append (h : C207Search.Primitive.Steps n a b)
 (k : C207Search.Primitive.Steps m b c) : C207Search.Primitive.Steps (n+m) a c := steps_trans h k
theorem drain_t_xy (t w x y : Nat) (f : Registers) :
    Steps (4*t+1) (configAt offset 0 ⟨t,w,x,y,f⟩)
      (configAt offset 4 ⟨0,w,x+t,y+t,f⟩) := by
  induction t generalizing x y with
  | zero =>
    apply Steps.cons
    rw [step_0 hbound]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ t ih =>
    have he : 4*(t+1)+1 = (4*t+1)+1+1+1+1 := by omega
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
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (x+1) (y+1)

theorem drain_x (t w x y : Nat) (f : Registers) :
    Steps (3*x+1) (configAt offset 6 ⟨t,w,x,y,f⟩)
      (configAt offset 9 ⟨t+x,w,0,y,f⟩) := by
  induction x generalizing t with
  | zero =>
    apply Steps.cons
    rw [step_6 hbound]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ x ih =>
    have he : 3*(x+1)+1 = (3*x+1)+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_6 hbound]
    simp only [Nat.add_sub_cancel,Nat.succ_ne_zero,↓reduceIte]
    apply Steps.cons
    rw [step_7 hbound]
    apply Steps.cons
    rw [step_8 hbound]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (t+1)

/-- The diagonal walk terminates by decreasing X, accumulating its triangular
number. Its inner transfer loops preserve the complete unrelated register frame. -/
theorem pair_loop (s w y : Nat) (f : Registers) :
    ∃ n, Steps n (configAt offset 4 ⟨0,w,s,y,f⟩)
      (configAt offset 10 ⟨0,w,0,y+M6.Source.Cantor.triangle s,f⟩) := by
  induction s generalizing y with
  | zero =>
    refine ⟨1,?_⟩
    apply Steps.cons
    rw [step_4 hbound]
    simp only [↓reduceIte,M6.Source.Cantor.triangle,Nat.add_zero]
    exact Steps.refl _
  | succ s ih =>
    obtain ⟨n,hn⟩ := ih (y+1+s)
    have a : Steps 2 (configAt offset 4 ⟨0,w,s+1,y,f⟩)
        (configAt offset 6 ⟨0,w,s,y+1,f⟩) := by
      apply Steps.cons
      rw [step_4 hbound]
      simp only [Nat.add_sub_cancel,Nat.succ_ne_zero,↓reduceIte]
      apply Steps.cons
      rw [step_5 hbound]
      exact Steps.refl _
    have b : Steps (3*s+1) (configAt offset 6 ⟨0,w,s,y+1,f⟩)
        (configAt offset 9 ⟨s,w,0,y+1,f⟩) := by
      simpa only [Nat.zero_add] using drain_x hbound 0 w s (y+1) f
    have c : Steps 1 (configAt offset 9 ⟨s,w,0,y+1,f⟩)
        (configAt offset 0 ⟨s,w,0,y+1,f⟩) := by
      apply Steps.cons
      rw [step_9 hbound]
      exact Steps.refl _
    have d : Steps (4*s+1) (configAt offset 0 ⟨s,w,0,y+1,f⟩)
        (configAt offset 4 ⟨0,w,s,y+1+s,f⟩) := by
      simpa only [Nat.zero_add] using drain_t_xy hbound s w 0 (y+1) f
    refine ⟨2+(3*s+1)+1+(4*s+1)+n,?_⟩
    simpa only [M6.Source.Cantor.triangle,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      steps_trans (steps_trans (steps_trans (steps_trans a b) c) d) hn

/-- Ten-row arithmetic core, without assuming surrounding push instructions. -/
theorem pair (t w x : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps n (configAt offset 0 ⟨t,w,x,0,f⟩)
      (configAt offset 10 ⟨0,w,0,M6.Source.Cantor.pair x t,f⟩) := by
  have a : Steps (4*t+1) (configAt offset 0 ⟨t,w,x,0,f⟩)
      (configAt offset 4 ⟨0,w,x+t,t,f⟩) := by
    simpa only [Nat.zero_add] using drain_t_xy hbound t w x 0 f
  obtain ⟨n,hn⟩ := pair_loop hbound (x+t) w t f
  refine ⟨4*t+1+n,by omega,?_⟩
  simpa only [M6.Source.Cantor.pair,Nat.add_comm] using steps_trans a hn

end C207Search.Primitive.PairCore
