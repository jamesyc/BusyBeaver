module
public import PrimitiveAXGateCompare
@[expose] public section
set_option linter.unusedSimpArgs false
namespace C209Search.Primitive.AXGate
open M209.Source
structure Store where
  t : Nat
  a : Nat
  d : Nat
  h : Nat
  x : Nat
  y : Nat
  frame : Registers
def registers (s : Store) : Registers := fun r =>
  if r = 2 then s.t else if r = 4 then s.a else if r = 3 then s.d else if r = 7 then s.h else if r = 8 then s.x else if r = 5 then s.y else s.frame r
def configAt (pc : Nat) (s : Store) : Configuration := ⟨pc,registers s⟩
private theorem row4187 : program 4187 = some (.dec 4 4191 4188) := by decide +kernel
theorem step_4187 (s : Store) : step (configAt 4187 s) = if s.a=0 then configAt 4191 s else configAt 4188 {s with a := s.a-1} := by
  unfold step scalarNext configAt
  rw [row4187]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4188 : program 4188 = some (.inc 5 4189) := by decide +kernel
theorem step_4188 (s : Store) : step (configAt 4188 s) = configAt 4189 {s with y := s.y+1} := by
  unfold step scalarNext configAt
  rw [row4188]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4189 : program 4189 = some (.inc 8 4190) := by decide +kernel
theorem step_4189 (s : Store) : step (configAt 4189 s) = configAt 4190 {s with x := s.x+1} := by
  unfold step scalarNext configAt
  rw [row4189]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4190 : program 4190 = some (.jump 4187) := by decide +kernel
theorem step_4190 (s : Store) : step (configAt 4190 s) = configAt 4187 s := by
  unfold step scalarNext configAt
  rw [row4190]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4203 : program 4203 = some (.dec 5 4206 4204) := by decide +kernel
theorem step_4203 (s : Store) : step (configAt 4203 s) = if s.y=0 then configAt 4206 s else configAt 4204 {s with y := s.y-1} := by
  unfold step scalarNext configAt
  rw [row4203]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4204 : program 4204 = some (.inc 8 4205) := by decide +kernel
theorem step_4204 (s : Store) : step (configAt 4204 s) = configAt 4205 {s with x := s.x+1} := by
  unfold step scalarNext configAt
  rw [row4204]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4205 : program 4205 = some (.jump 4203) := by decide +kernel
theorem step_4205 (s : Store) : step (configAt 4205 s) = configAt 4203 s := by
  unfold step scalarNext configAt
  rw [row4205]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4206 : program 4206 = some (.dec 3 4209 4207) := by decide +kernel
theorem step_4206 (s : Store) : step (configAt 4206 s) = if s.d=0 then configAt 4209 s else configAt 4207 {s with d := s.d-1} := by
  unfold step scalarNext configAt
  rw [row4206]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4207 : program 4207 = some (.inc 7 4208) := by decide +kernel
theorem step_4207 (s : Store) : step (configAt 4207 s) = configAt 4208 {s with h := s.h+1} := by
  unfold step scalarNext configAt
  rw [row4207]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4208 : program 4208 = some (.jump 4206) := by decide +kernel
theorem step_4208 (s : Store) : step (configAt 4208 s) = configAt 4206 s := by
  unfold step scalarNext configAt
  rw [row4208]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem row4221 : program 4221 = some (.jump 4328) := by decide +kernel
theorem step_4221 (s : Store) : step (configAt 4221 s) = configAt 4328 s := by
  unfold step scalarNext configAt
  rw [row4221]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem bound4191 : AXGateCompare.Bound 4191 := by unfold AXGateCompare.Bound; decide +kernel
private theorem bound4209 : AXGateCompare.Bound 4209 := by unfold AXGateCompare.Bound; decide +kernel
theorem copy_a (t a d h x y : Nat) (f : Registers) :
    Steps (4*a+1) (configAt 4187 ⟨t,a,d,h,x,y,f⟩)
      (configAt 4191 ⟨t,0,d,h,x+a,y+a,f⟩) := by
  induction a generalizing x y with
  | zero =>
    apply Steps.cons
    rw [step_4187]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ a ih =>
    have he : 4*(a+1)+1 = (4*a+1)+1+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_4187]
    simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step_4188]
    apply Steps.cons
    rw [step_4189]
    apply Steps.cons
    rw [step_4190]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (x+1) (y+1)

theorem y_to_x (t a d h x y : Nat) (f : Registers) :
    Steps (3*y+1) (configAt 4203 ⟨t,a,d,h,x,y,f⟩)
      (configAt 4206 ⟨t,a,d,h,x+y,0,f⟩) := by
  induction y generalizing x with
  | zero =>
    apply Steps.cons
    rw [step_4203]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ y ih =>
    have he : 3*(y+1)+1 = (3*y+1)+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_4203]
    simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step_4204]
    apply Steps.cons
    rw [step_4205]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (x+1)

theorem d_to_h (t a d h x y : Nat) (f : Registers) :
    Steps (3*d+1) (configAt 4206 ⟨t,a,d,h,x,y,f⟩)
      (configAt 4209 ⟨t,a,0,h+d,x,y,f⟩) := by
  induction d generalizing h with
  | zero =>
    apply Steps.cons
    rw [step_4206]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ d ih =>
    have he : 3*(d+1)+1 = (3*d+1)+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_4206]
    simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step_4207]
    apply Steps.cons
    rw [step_4208]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (h+1)

private theorem compare_registers (t a d h x y t' h' x' : Nat) (f : Registers) :
    AXGateCompare.registers ⟨t',h',x',registers ⟨t,a,d,h,x,y,f⟩⟩ =
      registers ⟨t',a,d,h',x',y,f⟩ := by
  funext r
  by_cases h1 : r = 2 <;> by_cases h3 : r = 4 <;> by_cases h4 : r = 3 <;>
    by_cases h5 : r = 7 <;> by_cases h6 : r = 8 <;> by_cases h7 : r = 5 <;>
    simp_all [registers,AXGateCompare.registers]

theorem comparison {base : Nat} (hb : AXGateCompare.Bound base)
    (t a d h x y : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps n (configAt base ⟨t,a,d,h,x,y,f⟩)
      (configAt (base+12) ⟨if h=x then 0 else t,a,d,0,0,y,f⟩) := by
  obtain ⟨n,hn,hs⟩ := AXGateCompare.compare hb t h x (registers ⟨t,a,d,h,x,y,f⟩)
  refine ⟨n,hn,?_⟩
  simpa only [AXGateCompare.configAt,compare_registers,configAt,Nat.add_zero] using hs

/-- The actual final AX gate clears all five work registers. It preserves the
formula stack W and every unrelated register, and sets T to zero when either
comparison matches the original A; otherwise it preserves T. -/
theorem gate (t a d h : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps n (configAt 4187 ⟨t,a,d,h,0,0,f⟩)
      (configAt 4328 ⟨if d=a ∨ h=a then 0 else t,0,0,0,0,0,f⟩) := by
  have first : Steps (4*a+1) (configAt 4187 ⟨t,a,d,h,0,0,f⟩)
      (configAt 4191 ⟨t,0,d,h,a,a,f⟩) := by
    simpa only [Nat.zero_add] using copy_a t a d h 0 0 f
  obtain ⟨n,hn,second⟩ := comparison bound4191 t 0 d h a a f
  have third := y_to_x (if h=a then 0 else t) 0 d 0 0 a f
  have fourth := d_to_h (if h=a then 0 else t) 0 d 0 a 0 f
  obtain ⟨m,hm,fifth⟩ := comparison bound4209 (if h=a then 0 else t) 0 0 d a 0 f
  have sixth : Steps 1
      (configAt 4221 ⟨if d=a then 0 else if h=a then 0 else t,0,0,0,0,0,f⟩)
      (configAt 4328 ⟨if d=a then 0 else if h=a then 0 else t,0,0,0,0,0,f⟩) := by
    apply Steps.cons
    rw [step_4221]
    exact Steps.refl _
  have third' := third
  have fourth' := fourth
  simp only [Nat.zero_add] at third' fourth'
  have all := steps_trans (steps_trans (steps_trans (steps_trans (steps_trans first second) third') fourth') fifth) sixth
  refine ⟨(4*a+1)+n+(3*a+1)+(3*d+1)+m+1,by omega,?_⟩
  by_cases hd : d=a <;> by_cases hh : h=a <;> simpa only [hd,hh,↓reduceIte,or_self,or_false,false_or] using all

private theorem return_row : program 4328 = some (.jump 25) := by decide +kernel
theorem return_to_fetch (s : Store) : Steps 1 (configAt 4328 s) (configAt 25 s) := by
 apply Steps.cons
 have hs : step (configAt 4328 s) = configAt 25 s := by
  unfold step scalarNext configAt
  rw [return_row]
  rfl
 rw [hs]
 exact Steps.refl _

theorem gate_fetch (t a d h : Nat) (f : Registers) :
 ∃ n, 0<n ∧ Steps n (configAt 4187 ⟨t,a,d,h,0,0,f⟩)
 (configAt 25 ⟨if a≠d ∧ a≠h then t else 0,0,0,0,0,0,f⟩) := by
 obtain ⟨n,hn,hs⟩ := gate t a d h f
 have ht := steps_trans hs (return_to_fetch _)
 refine ⟨n+1,by omega,?_⟩
 by_cases hd : a=d <;> by_cases hh : a=h <;> simp_all [eq_comm]

end C209Search.Primitive.AXGate
