module
public import M207.FrameSoundness
public import M207.Permutation
public import M207.SourceSimulation
@[expose] public section
namespace M207.Source
open M6.Zip M6.Runtime

inductive Instruction where
  | inc (reg next : Nat)
  | dec (reg zero positive : Nat)
  | jump (next : Nat)
  | halt
  deriving DecidableEq, Repr

/-- Includes the full physical register file and gap; spare entries are retained. -/
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

def rootFrame (path : List Bool) (extra : Nat := 0) (effect : Eff := .none) : SConf :=
  (inverse 74,false,[.bit true],path.map Seg.bit ++
    [.run false 1 (48+extra-path.length),.bit true,.box (.plain effect)])

def frame (paths : Nat → List Bool) (s : State) : Conf :=
  mapConf forward (conc s.gap s.file (rootFrame (paths s.pc)))

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
end M207.Source
