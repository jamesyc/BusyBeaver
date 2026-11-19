module
public import PrimitivePairCore
@[expose] public section
set_option linter.unusedSimpArgs false
namespace C207Search.Primitive.Push
open M207.Source
abbrev Store := PairCore.Store
abbrev registers := PairCore.registers
abbrev configAt := PairCore.configAt

def expected (offset : Nat) : Nat → Instruction
 | 0 => .dec 2 (offset+3) (offset+1)
 | 1 => .inc 8 (offset+2)
 | 2 => .jump (offset+0)
 | 3 => .dec 0 (offset+6) (offset+4)
 | 4 => .inc 2 (offset+5)
 | 5 => .jump (offset+3)
 | 6 => .dec 2 (offset+10) (offset+7)
 | 7 => .inc 5 (offset+8)
 | 8 => .inc 8 (offset+9)
 | 9 => .jump (offset+6)
 | 10 => .dec 8 (offset+16) (offset+11)
 | 11 => .inc 5 (offset+12)
 | 12 => .dec 8 (offset+15) (offset+13)
 | 13 => .inc 2 (offset+14)
 | 14 => .jump (offset+12)
 | 15 => .jump (offset+6)
 | 16 => .dec 5 (offset+19) (offset+17)
 | 17 => .inc 0 (offset+18)
 | 18 => .jump (offset+16)
 | _ => .halt

def Bound (offset : Nat) : Prop := ∀ j : Fin 19,
 program (offset+j.val) = some (expected offset j.val)
variable {offset : Nat} (hbound : Bound offset)
include hbound

theorem pair_bound : PairCore.Bound (offset+6) := by
 intro j
 have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by
  exact (by decide +kernel : ∀ j : Fin 10, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9) j
 rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · simpa [expected,PairCore.expected,Nat.add_assoc,(show ((0 : Fin 10) : Nat) = 0 from rfl)] using hbound ⟨6,by decide⟩
 · simpa [expected,PairCore.expected,Nat.add_assoc,(show ((1 : Fin 10) : Nat) = 1 from rfl)] using hbound ⟨7,by decide⟩
 · simpa [expected,PairCore.expected,Nat.add_assoc,(show ((2 : Fin 10) : Nat) = 2 from rfl)] using hbound ⟨8,by decide⟩
 · simpa [expected,PairCore.expected,Nat.add_assoc,(show ((3 : Fin 10) : Nat) = 3 from rfl)] using hbound ⟨9,by decide⟩
 · simpa [expected,PairCore.expected,Nat.add_assoc,(show ((4 : Fin 10) : Nat) = 4 from rfl)] using hbound ⟨10,by decide⟩
 · simpa [expected,PairCore.expected,Nat.add_assoc,(show ((5 : Fin 10) : Nat) = 5 from rfl)] using hbound ⟨11,by decide⟩
 · simpa [expected,PairCore.expected,Nat.add_assoc,(show ((6 : Fin 10) : Nat) = 6 from rfl)] using hbound ⟨12,by decide⟩
 · simpa [expected,PairCore.expected,Nat.add_assoc,(show ((7 : Fin 10) : Nat) = 7 from rfl)] using hbound ⟨13,by decide⟩
 · simpa [expected,PairCore.expected,Nat.add_assoc,(show ((8 : Fin 10) : Nat) = 8 from rfl)] using hbound ⟨14,by decide⟩
 · simpa [expected,PairCore.expected,Nat.add_assoc,(show ((9 : Fin 10) : Nat) = 9 from rfl)] using hbound ⟨15,by decide⟩
theorem step_0 (t w x y : Nat) (f : Registers) : step (configAt offset 0 ⟨t,w,x,y,f⟩) = if t=0 then configAt offset 3 ⟨t,w,x,y,f⟩ else configAt offset 1 ⟨t - 1,w,x,y,f⟩ := by
  have hb : program (offset+0) = some (.dec 2 (offset+3) (offset+1)) := by simpa [expected] using hbound ⟨0,by decide⟩
  unfold step scalarNext configAt PairCore.configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, PairCore.registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, PairCore.registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_1 (t w x y : Nat) (f : Registers) : step (configAt offset 1 ⟨t,w,x,y,f⟩) = configAt offset 2 ⟨t,w,x + 1,y,f⟩ := by
  have hb : program (offset+1) = some (.inc 8 (offset+2)) := by simpa [expected] using hbound ⟨1,by decide⟩
  unfold step scalarNext configAt PairCore.configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, PairCore.registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, PairCore.registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_2 (t w x y : Nat) (f : Registers) : step (configAt offset 2 ⟨t,w,x,y,f⟩) = configAt offset 0 ⟨t,w,x,y,f⟩ := by
  have hb : program (offset+2) = some (.jump (offset+0)) := by simpa [expected] using hbound ⟨2,by decide⟩
  unfold step scalarNext configAt PairCore.configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, PairCore.registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, PairCore.registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_3 (t w x y : Nat) (f : Registers) : step (configAt offset 3 ⟨t,w,x,y,f⟩) = if w=0 then configAt offset 6 ⟨t,w,x,y,f⟩ else configAt offset 4 ⟨t,w - 1,x,y,f⟩ := by
  have hb : program (offset+3) = some (.dec 0 (offset+6) (offset+4)) := by simpa [expected] using hbound ⟨3,by decide⟩
  unfold step scalarNext configAt PairCore.configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, PairCore.registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, PairCore.registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_4 (t w x y : Nat) (f : Registers) : step (configAt offset 4 ⟨t,w,x,y,f⟩) = configAt offset 5 ⟨t + 1,w,x,y,f⟩ := by
  have hb : program (offset+4) = some (.inc 2 (offset+5)) := by simpa [expected] using hbound ⟨4,by decide⟩
  unfold step scalarNext configAt PairCore.configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, PairCore.registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, PairCore.registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_5 (t w x y : Nat) (f : Registers) : step (configAt offset 5 ⟨t,w,x,y,f⟩) = configAt offset 3 ⟨t,w,x,y,f⟩ := by
  have hb : program (offset+5) = some (.jump (offset+3)) := by simpa [expected] using hbound ⟨5,by decide⟩
  unfold step scalarNext configAt PairCore.configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, PairCore.registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, PairCore.registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_16 (t w x y : Nat) (f : Registers) : step (configAt offset 16 ⟨t,w,x,y,f⟩) = if y=0 then configAt offset 19 ⟨t,w,x,y,f⟩ else configAt offset 17 ⟨t,w,x,y - 1,f⟩ := by
  have hb : program (offset+16) = some (.dec 5 (offset+19) (offset+17)) := by simpa [expected] using hbound ⟨16,by decide⟩
  unfold step scalarNext configAt PairCore.configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, PairCore.registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, PairCore.registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_17 (t w x y : Nat) (f : Registers) : step (configAt offset 17 ⟨t,w,x,y,f⟩) = configAt offset 18 ⟨t,w + 1,x,y,f⟩ := by
  have hb : program (offset+17) = some (.inc 0 (offset+18)) := by simpa [expected] using hbound ⟨17,by decide⟩
  unfold step scalarNext configAt PairCore.configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, PairCore.registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, PairCore.registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]
theorem step_18 (t w x y : Nat) (f : Registers) : step (configAt offset 18 ⟨t,w,x,y,f⟩) = configAt offset 16 ⟨t,w,x,y,f⟩ := by
  have hb : program (offset+18) = some (.jump (offset+16)) := by simpa [expected] using hbound ⟨18,by decide⟩
  unfold step scalarNext configAt PairCore.configAt
  rw [hb]
  simp only [Option.bind_some, scalarExecute]
  try split
  all_goals
    simp_all [registerIndex, registers, PairCore.registers, configAt, Option.getD]
  all_goals
    funext r
    have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by
      exact (by decide +kernel : ∀ r : Fin 9, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8) r
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [registers, PairCore.registers, Fin.val_ofNat, (show ((0 : Fin 9) : Nat) = 0 from rfl), (show ((1 : Fin 9) : Nat) = 1 from rfl), (show ((2 : Fin 9) : Nat) = 2 from rfl), (show ((3 : Fin 9) : Nat) = 3 from rfl), (show ((4 : Fin 9) : Nat) = 4 from rfl), (show ((5 : Fin 9) : Nat) = 5 from rfl), (show ((6 : Fin 9) : Nat) = 6 from rfl), (show ((7 : Fin 9) : Nat) = 7 from rfl), (show ((8 : Fin 9) : Nat) = 8 from rfl)]

theorem drain_t (t w x y : Nat) (f : Registers) :
 Steps (3*t+1) (configAt offset 0 ⟨t,w,x,y,f⟩) (configAt offset 3 ⟨0,w,x+t,y,f⟩) := by
 induction t generalizing x with
 | zero =>
   apply Steps.cons; rw [step_0 hbound]; simp; exact Steps.refl _
 | succ t ih =>
   have he : 3*(t+1)+1=(3*t+1)+1+1+1 := by omega
   rw [he]
   apply Steps.cons; rw [step_0 hbound]; simp
   apply Steps.cons; rw [step_1 hbound]
   apply Steps.cons; rw [step_2 hbound]
   simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (x+1)

theorem drain_w (w t x y : Nat) (f : Registers) :
 Steps (3*w+1) (configAt offset 3 ⟨t,w,x,y,f⟩) (configAt offset 6 ⟨t+w,0,x,y,f⟩) := by
 induction w generalizing t with
 | zero =>
   apply Steps.cons; rw [step_3 hbound]; simp; exact Steps.refl _
 | succ w ih =>
   have he : 3*(w+1)+1=(3*w+1)+1+1+1 := by omega
   rw [he]
   apply Steps.cons; rw [step_3 hbound]; simp
   apply Steps.cons; rw [step_4 hbound]
   apply Steps.cons; rw [step_5 hbound]
   simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (t+1)

theorem drain_y (y t w x : Nat) (f : Registers) :
 Steps (3*y+1) (configAt offset 16 ⟨t,w,x,y,f⟩) (configAt offset 19 ⟨t,w+y,x,0,f⟩) := by
 induction y generalizing w with
 | zero =>
   apply Steps.cons; rw [step_16 hbound]; simp; exact Steps.refl _
 | succ y ih =>
   have he : 3*(y+1)+1=(3*y+1)+1+1+1 := by omega
   rw [he]
   apply Steps.cons; rw [step_16 hbound]; simp
   apply Steps.cons; rw [step_17 hbound]
   apply Steps.cons; rw [step_18 hbound]
   simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (w+1)

theorem push (t w : Nat) (f : Registers) :
 ∃n, 0<n ∧ Steps n (configAt offset 0 ⟨t,w,0,0,f⟩)
  (configAt offset 19 ⟨0,M6.Source.Cantor.pair t w,0,0,f⟩) := by
 have a := drain_t hbound t w 0 0 f
 have b := drain_w hbound w 0 t 0 f
 obtain ⟨n,hn,c⟩ := PairCore.pair (pair_bound hbound) w 0 t f
 have d := drain_y hbound (M6.Source.Cantor.pair t w) 0 0 0 f
 simp only [Nat.zero_add] at a b d
 have c' : Steps n (configAt offset 6 ⟨w,0,t,0,f⟩)
   (configAt offset 16 ⟨0,0,0,M6.Source.Cantor.pair t w,f⟩) := by
  simpa [configAt,PairCore.configAt,Nat.add_assoc] using c
 exact ⟨_,by omega,steps_trans (steps_trans (steps_trans a b) c') d⟩
end C207Search.Primitive.Push
