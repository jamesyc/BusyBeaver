module
public import PrimitiveStep
@[expose] public section
set_option linter.unusedSimpArgs false
namespace C207Search.Primitive.MPCopy
open M207.Source

def expected (base : Nat) : Nat → Instruction
 | 0 => .dec 3 (base+4) (base+1)
 | 1 => .inc 2 (base+2)
 | 2 => .inc 8 (base+3)
 | 3 => .jump base
 | 4 => .dec 8 (base+7) (base+5)
 | 5 => .inc 3 (base+6)
 | _ => .jump (base+4)
def Bound (base : Nat) := ∀ j : Fin 7, program (base+j.val) = some (expected base j.val)
def registers (v t x : Nat) (f : Registers) : Registers := fun r =>
 if r=3 then v else if r=2 then t else if r=8 then x else f r
def config (base pc v t x : Nat) (f : Registers) : Configuration := ⟨base+pc,registers v t x f⟩
variable {base : Nat} (hb : Bound base)
include hb
private theorem step0 (v t x : Nat) (f : Registers) :
    step (config base 0 v t x f) =
      if v = 0 then config base 4 v t x f else config base 1 (v-1) t x f := by
  have hx : program (base+0) = some (expected base 0) := hb ⟨0,by decide⟩
  unfold step scalarNext config
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem step1 (v t x : Nat) (f : Registers) :
    step (config base 1 v t x f) = config base 2 v (t+1) x f := by
  have hx : program (base+1) = some (expected base 1) := hb ⟨1,by decide⟩
  unfold step scalarNext config
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem step2 (v t x : Nat) (f : Registers) :
    step (config base 2 v t x f) = config base 3 v t (x+1) f := by
  have hx : program (base+2) = some (expected base 2) := hb ⟨2,by decide⟩
  unfold step scalarNext config
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem step3 (v t x : Nat) (f : Registers) :
    step (config base 3 v t x f) = config base 0 v t x f := by
  have hx : program (base+3) = some (expected base 3) := hb ⟨3,by decide⟩
  unfold step scalarNext config
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem step4 (v t x : Nat) (f : Registers) :
    step (config base 4 v t x f) =
      if x = 0 then config base 7 v t x f else config base 5 v t (x-1) f := by
  have hx : program (base+4) = some (expected base 4) := hb ⟨4,by decide⟩
  unfold step scalarNext config
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem step5 (v t x : Nat) (f : Registers) :
    step (config base 5 v t x f) = config base 6 (v+1) t x f := by
  have hx : program (base+5) = some (expected base 5) := hb ⟨5,by decide⟩
  unfold step scalarNext config
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
private theorem step6 (v t x : Nat) (f : Registers) :
    step (config base 6 v t x f) = config base 4 v t x f := by
  have hx : program (base+6) = some (expected base 6) := hb ⟨6,by decide⟩
  unfold step scalarNext config
  rw [hx]
  simp only [expected]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, config, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem drain_source (v t x : Nat) (f : Registers) :
    Steps (4*v+1) (config base 0 v t x f)
      (config base 4 0 (t+v) (x+v) f) := by
  induction v generalizing t x with
  | zero =>
    apply Steps.cons
    rw [step0 hb]
    simp only [Nat.add_zero,↓reduceIte]
    exact Steps.refl _
  | succ v ih =>
    have hh := ih (t+1) (x+1)
    have hn : 4*(v+1)+1 = (4*v+1)+1+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step0 hb]
    simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step1 hb]
    apply Steps.cons
    rw [step2 hb]
    apply Steps.cons
    rw [step3 hb]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem restore_source (v t x : Nat) (f : Registers) :
    Steps (3*x+1) (config base 4 v t x f)
      (config base 7 (v+x) t 0 f) := by
  induction x generalizing v with
  | zero =>
    apply Steps.cons
    rw [step4 hb]
    simp only [Nat.add_zero,↓reduceIte]
    exact Steps.refl _
  | succ x ih =>
    have hn : 3*(x+1)+1 = (3*x+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step4 hb]
    simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step5 hb]
    apply Steps.cons
    rw [step6 hb]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (v+1)

/-- A proved seven-row source macro: add a preserved parameter into T,
restoring X to zero and preserving every unrelated register. -/
theorem copy (v t : Nat) (f : Registers) :
    Steps (7*v+2) (config base 0 v t 0 f)
      (config base 7 v (t+v) 0 f) := by
  have a := drain_source hb v t 0 f
  have b := restore_source hb 0 (t+v) v f
  simp only [Nat.zero_add] at a b
  have hn : 7*v+2 = (4*v+1)+(3*v+1) := by omega
  rw [hn]
  exact steps_trans a b


omit hb in
theorem first_bound : Bound 4255 := by unfold Bound; decide +kernel
omit hb in
theorem last_bound : Bound 4321 := by unfold Bound; decide +kernel
omit hb in
theorem first_copy (d t : Nat) (f : Registers) : Steps (7*d+2) (config 4255 0 d t 0 f) (config 4255 7 d (t+d) 0 f) := copy first_bound d t f
omit hb in
theorem last_copy (d t : Nat) (f : Registers) : Steps (7*d+2) (config 4321 0 d t 0 f) (config 4321 7 d (t+d) 0 f) := copy last_bound d t f
end C207Search.Primitive.MPCopy
