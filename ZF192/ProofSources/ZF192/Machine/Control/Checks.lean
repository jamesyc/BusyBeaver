module
public import ZF192Support.Machine.RegisterProgram.Projection
public import ZF192.Machine.Control.Data
public import ZF192.Machine.Decoder.Paths
public import ZF192Support.Machine.RegisterProgram.Instructions

@[expose] public section
namespace M192.Control
open RegisterMachine.Source (Instruction instructionBound registerIndex)

abbrev Program := Nat → Option Instruction

/-- A finite string of unconditional jumps. Registers are untouched. -/
inductive JumpPath (code : Program) : Nat → Nat → Prop
  | refl (pc : Nat) : JumpPath code pc pc
  | step {pc mid dst : Nat} (row : code pc = some (.jump mid))
      (tail : JumpPath code mid dst) : JumpPath code pc dst

def skip (code : Program) : Nat → Nat → Option Nat
  | 0, _ => none
  | n+1, pc =>
    match code pc with
    | none => none
    | some (.jump next) => skip code n next
    | some _ => some pc

def isJump : Instruction → Bool
  | .jump _ => true
  | _ => false

theorem skip_sound {code : Program} {fuel pc dst : Nat} (h : skip code fuel pc = some dst) :
    JumpPath code pc dst ∧ ∃ op, code dst = some op ∧ isJump op = false := by
  induction fuel generalizing pc with
  | zero => simp [skip] at h
  | succ n ih =>
    cases row : code pc with
    | none => simp [skip, row] at h
    | some op =>
      cases op with
      | jump mid =>
        have hs : skip code n mid = some dst := by simpa [skip, row] using h
        exact ⟨.step row (ih hs).1, (ih hs).2⟩
      | inc r p =>
        have hd : pc = dst := by simpa [skip, row] using h
        subst dst
        exact ⟨.refl _, _, row, rfl⟩
      | dec r z p =>
        have hd : pc = dst := by simpa [skip, row] using h
        subst dst
        exact ⟨.refl _, _, row, rfl⟩
      | halt =>
        have hd : pc = dst := by simpa [skip, row] using h
        subst dst
        exact ⟨.refl _, _, row, rfl⟩

def compilerSlot (i : Fin 9) : Fin 9 := ([6, 2, 0, 4, 3, 7, 8, 5, 1] : List (Fin 9)).getD i.val 0
def machineSlot (i : Fin 9) : Fin 9 := ([2, 8, 1, 4, 3, 7, 0, 5, 6] : List (Fin 9)).getD i.val 0

theorem compilerSlot_machineSlot (i : Fin 9) : compilerSlot (machineSlot i) = i := by
  have h : ∀ j : Fin 9, compilerSlot (machineSlot j) = j := by decide +kernel
  exact h i

theorem machineSlot_compilerSlot (i : Fin 9) : machineSlot (compilerSlot i) = i := by
  have h : ∀ j : Fin 9, machineSlot (compilerSlot j) = j := by decide +kernel
  exact h i

universe u

def permute {α : Type u} (r : Fin 9 → α) : Fin 9 → α := r ∘ compilerSlot

def mapRegister (r : Nat) : Nat := (machineSlot (registerIndex r)).val

def compilerProgram : Program := RegisterMachine.Source.program
def machineProgram : Program := M192.Paths.program
def machineSkip (pc : Nat) : Option Nat := skip machineProgram 4 pc
def compilerSkip (pc : Nat) : Option Nat := skip compilerProgram 4 pc

/-- A test stated against the actual decoded row. Only unconditional jumps
are omitted by the alignment. -/
def MatchesAt (pc : Nat) (other : Option Instruction) : Instruction → Prop
  | .jump next => align pc = align next
  | .inc r next =>
    match other with
    | some (.inc r' next') => r' = mapRegister r ∧ machineSkip next' = some (align next)
    | _ => False
  | .dec r z p =>
    match other with
    | some (.dec r' z' p') =>
      r' = mapRegister r ∧ machineSkip z' = some (align z) ∧ machineSkip p' = some (align p)
    | _ => False
  | .halt => other = some .halt

instance (pc : Nat) (other : Option Instruction) (op : Instruction) : Decidable (MatchesAt pc other op) := by
  cases op <;> cases other with
  | none => unfold MatchesAt; infer_instance
  | some row => cases row <;> unfold MatchesAt <;> infer_instance

abbrev Matches (pc : Nat) : Instruction → Prop := MatchesAt pc (machineProgram (align pc))

def check (pc : Nat) : Bool :=
  (compilerSkip pc).isSome && decide (align pc < M192.Paths.siteCount) &&
  match compilerProgram pc with
  | none => false
  | some op => decide (instructionBound 4341 op ∧ Matches pc op)

theorem checked {pc : Nat} (h : check pc = true) :
    (∃ dst, compilerSkip pc = some dst) ∧ align pc < M192.Paths.siteCount ∧
    ∃ op, compilerProgram pc = some op ∧ instructionBound 4341 op ∧ Matches pc op := by
  unfold check at h
  cases ho : compilerProgram pc with
  | none => simp [ho] at h
  | some op =>
    simp only [ho, Bool.and_eq_true, Option.isSome_iff_exists, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, op, rfl, h.2.1, h.2.2⟩

end M192.Control
