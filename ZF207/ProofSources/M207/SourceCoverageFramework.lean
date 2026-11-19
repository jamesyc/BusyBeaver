module
public import M207.SourceContracts
@[expose] public section
namespace M207.Source
open M6.Zip

def CoverageAt (program : Nat → Option Instruction) (paths : Nat → List Bool) (count i : Nat) : Prop :=
  ∃ code, (program i) = some code ∧ instructionBound count code ∧
    ImplementsCode paths (paths i) code

private theorem execute_pc (code : Instruction) (s : State) :
    execute code ⟨0,s.gap,s.file⟩ = execute code s := by
  cases code <;> rfl

theorem coverage_implements {program : Nat → Option Instruction} {paths : Nat → List Bool}
    {count : Nat} (coverage : ∀ i, i < count → CoverageAt program paths count i) :
    SourceSimulation.Implements literal (next program) (Valid count) (frame paths) where
  preserve s t hs hnext := by
    obtain ⟨code,hget,hbound,himpl⟩ := coverage s.pc hs.1
    simp only [next,hget,Option.bind_some] at hnext
    exact execute_preserves hbound hs hnext
  terminal s hs hnext := by
    obtain ⟨code,hget,hbound,himpl⟩ := coverage s.pc hs.1
    simp only [next,hget,Option.bind_some] at hnext
    have h := himpl s.gap s.file hs.2
    rw [execute_pc, hnext] at h
    exact h
  progress s t hs hnext := by
    obtain ⟨code,hget,hbound,himpl⟩ := coverage s.pc hs.1
    simp only [next,hget,Option.bind_some] at hnext
    have h := himpl s.gap s.file hs.2
    rw [execute_pc, hnext] at h
    exact h
end M207.Source
