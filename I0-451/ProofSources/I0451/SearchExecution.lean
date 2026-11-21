module
public import I0451.ProgramExecution
public import I0451.CandidateLoading
public import I0451.Logic.Derivability

/-! A complete command either halts or reaches the next root at a
strictly later interpreter step. Determinism then transfers both
directions of halting between the literal run and the scheduler. -/
@[expose] public section
namespace I0451.Runtime

open I0451.Logic

def searchRegisters (s : SearchState ProofStore) : Registers := fun j =>
  match j.val with
  | 0 => s.nextCandidate
  | 1 => s.store.top
  | 2 => s.store.stack
  | 4 => s.store.operand
  | 5 => s.store.cache
  | 8 => s.queued
  | _ => 0

def boundarySearch : SearchState ProofStore := ⟨3, 0, ⟨0, 0, 1, 0⟩⟩

theorem boundarySearch_represents : RepresentsFrame commandBoundary 0 (searchRegisters boundarySearch) := by
  exact ⟨commandBoundary_permanent, by decide +kernel, by decide +kernel⟩

def CommandsImplemented (exec : CommandEval ProofStore) : Prop :=
  ∀ s : SearchState ProofStore,
    match s.step exec with
    | none => ∃ after, Executes mainEdge (searchRegisters s) .halt after
    | some next => Executes mainEdge (searchRegisters s) .normal (searchRegisters next)

private theorem macro_run_before_halt {a b c : RegisterFrame} {n m : Nat}
    (run : runMacros n a = some b) (reached : runMacros m a = some c)
    (halt : macroStep c = .halt) : n ≤ m := by
  apply Nat.le_of_not_gt
  intro longer
  obtain ⟨k, eq⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt longer)
  have steps : n = m + (k + 1) := by omega
  rw [steps, runMacros_add, reached] at run
  simp [runMacros, halt] at run

private theorem macro_extend {a b : RegisterFrame} {n : Nat}
    (advance : runMacros n a = some b) (halt : MacroHalts b) : MacroHalts a := by
  obtain ⟨m, last, reached, ended⟩ := halt
  exact ⟨n + m, last, runMacros_join advance reached rfl, ended⟩

private theorem scheduler_advances {exec : CommandEval ProofStore} {s t : SearchState ProofStore}
    (commands : CommandsImplemented exec) (step : s.step exec = some t)
    {f : RegisterFrame} (view : RepresentsFrame f 0 (searchRegisters s)) :
    ∃ n next, 0 < n ∧ runMacros n f = some next ∧
      RepresentsFrame next 0 (searchRegisters t) := by
  have block := commands s
  rw [step] at block
  obtain ⟨n, next, address, positive, advances, atAddress, read⟩ :=
    (block.implements_main view).advances (by decide)
  have same : address = 0 := Option.some.inj atAddress.symm
  exact ⟨n, next, positive, advances, same ▸ read⟩

theorem macro_halts_iff_search {exec : CommandEval ProofStore} (commands : CommandsImplemented exec)
    {f : RegisterFrame} {s : SearchState ProofStore} (view : RepresentsFrame f 0 (searchRegisters s)) :
    MacroHalts f ↔ SearchHalts exec s := by
  constructor
  · rintro ⟨n, last, trace, stop⟩
    induction n using Nat.strongRecOn generalizing f s with
    | ind n ih =>
      cases step : s.step exec with
      | none => exact ⟨1, by simp [SearchState.run, step]⟩
      | some t =>
        obtain ⟨m, next, positive, advances, viewNext⟩ := scheduler_advances commands step view
        have enough := macro_run_before_halt advances trace stop
        obtain ⟨remaining, len⟩ := Nat.exists_eq_add_of_le enough
        rw [len, runMacros_add, advances] at trace
        obtain ⟨ticks, ran⟩ := ih remaining (by omega) viewNext (by simpa using trace)
        exact ⟨ticks + 1, by simp [SearchState.run, step, ran]⟩
  · rintro ⟨ticks, halted⟩
    induction ticks generalizing f s with
    | zero => simp [SearchState.run] at halted
    | succ ticks ih =>
      cases step : s.step exec with
      | none =>
        have block := commands s
        rw [step] at block
        obtain ⟨last, stopped⟩ := block
        exact (stopped.implements_main view).halts rfl
      | some t =>
        obtain ⟨n, next, _, advances, viewNext⟩ := scheduler_advances commands step view
        exact macro_extend advances (ih viewNext (by simpa [SearchState.run, step] using halted))

theorem blank_halts_iff_search {exec : CommandEval ProofStore} (commands : CommandsImplemented exec) :
    Halts literal (blank 0) ↔ SearchHalts exec boundarySearch :=
  blank_halts_iff_boundary.trans (macro_halts_iff_search commands boundarySearch_represents)

end I0451.Runtime
