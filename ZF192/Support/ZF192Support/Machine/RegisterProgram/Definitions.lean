module
public import ZF192Support.Machine.RegisterProgram.Simulation
@[expose] public section
namespace RegisterMachine.Source

def incr : Nat → List Nat → List Nat
  | _, [] => []
  | 0, v :: vs => (v + 1) :: vs
  | r + 1, v :: vs => v :: incr r vs

def decr : Nat → List Nat → List Nat
  | _, [] => []
  | 0, v :: vs => (v - 1) :: vs
  | r + 1, v :: vs => v :: decr r vs

inductive Instruction where
  | inc (reg next : Nat)
  | dec (reg zero positive : Nat)
  | jump (next : Nat)
  | halt
  deriving DecidableEq, Repr

/-- Source state with a gap counter and a register file that may include auxiliary
entries. The scalar projection keeps the program counter and the nine registers. -/
structure State where
  pc : Nat
  gap : Nat
  file : List Nat
  deriving DecidableEq, Repr

def execute : Instruction → State → Option State
  | .inc r k, s => some ⟨k,s.gap,incr r s.file ++ [1]⟩
  | .dec r z p, s =>
    if s.file.getD r 0 = 0 then some ⟨z,s.gap,s.file⟩
    else some ⟨p,s.gap+1,decr r s.file⟩
  | .jump k, s => some ⟨k,s.gap,s.file⟩
  | .halt, _ => none

def next (program : Nat → Option Instruction) (s : State) : Option State :=
  ((program s.pc)).bind fun code => execute code s

def Valid (count : Nat) (s : State) : Prop := s.pc < count ∧ 10 ≤ s.file.length

def instructionBound (count : Nat) : Instruction → Prop
  | .inc r k => r < 9 ∧ k < count
  | .dec r z p => r < 9 ∧ z < count ∧ p < count
  | .jump k => k < count
  | .halt => True

instance (count : Nat) (code : Instruction) : Decidable (instructionBound count code) := by
  cases code <;> unfold instructionBound <;> infer_instance

@[simp] theorem incr_length (r : Nat) (vs : List Nat) : (incr r vs).length = vs.length := by
  induction r generalizing vs with
  | zero => cases vs <;> rfl
  | succ r ih => cases vs <;> simp [incr,ih]

@[simp] theorem decr_length (r : Nat) (vs : List Nat) : (decr r vs).length = vs.length := by
  induction r generalizing vs with
  | zero => cases vs <;> rfl
  | succ r ih => cases vs <;> simp [decr,ih]

theorem execute_preserves {count : Nat} {code : Instruction} {s t : State}
    (bound : instructionBound count code) (valid : Valid count s)
    (step : execute code s = some t) : Valid count t := by
  obtain ⟨hp,hf⟩ := valid
  cases code with
  | inc r k =>
    simp only [execute,Option.some.injEq] at step
    subst t
    exact ⟨bound.2, by simp; omega⟩
  | dec r z p =>
    simp only [execute] at step
    split at step
    · cases step; exact ⟨bound.2.1,hf⟩
    · cases step; exact ⟨bound.2.2,by simpa using hf⟩
  | jump k => cases step; exact ⟨bound,hf⟩
  | halt => cases step
end RegisterMachine.Source
