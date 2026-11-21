module
public import I3_380.Engine.Interpreter
@[expose] public section

namespace PalomarI3380.Engine

open scoped PalomarI3380.Engine

/-- Start of the reference interpreter, with twelve zeroed logical
registers and the loader's auxiliary register prefix. -/
def initialState : RegisterState :=
  ⟨[], 18, List.replicate 132 0 ++ [1] ++ List.replicate 68 0⟩

theorem initial_configuration : initialState.config = loaderExit := by
  decide +kernel

def nextRegister (s : RegisterState) : Option RegisterState :=
  match execute s with
  | .next t => some t
  | _ => none

def advanceRegisters : Nat → RegisterState → Option RegisterState
  | 0, s => some s
  | n + 1, s => (nextRegister s).bind (advanceRegisters n)

theorem advance_realizes {n : Nat} {s t : RegisterState}
    (h : advanceRegisters n s = some t) (hClean : Clean s.path)
    (hLen : 13 ≤ s.registers.length) :
    s.config ⟶* t.config ∧ Clean t.path ∧ t.registers.length = s.registers.length := by
  induction n generalizing s with
  | zero =>
    change some s = some t at h
    cases h
    exact ⟨Reach.refl _, hClean, rfl⟩
  | succ n ih =>
    cases hOut : execute s with
    | invalid => simp [advanceRegisters, nextRegister, hOut] at h
    | halt => simp [advanceRegisters, nextRegister, hOut] at h
    | next u =>
      have hTail : advanceRegisters n u = some t := by
        simpa only [advanceRegisters, nextRegister, hOut, Option.bind_some] using h
      have first := execute_realizes s hClean hLen
      rw [hOut] at first
      obtain ⟨reach, clean, counts, _⟩ := first
      obtain ⟨rest, clean', counts'⟩ := ih hTail clean (counts.symm ▸ hLen)
      exact ⟨reach.reach.trans rest, clean', counts'.trans counts⟩

private theorem advanceRegisters_add (n m : Nat) (s : RegisterState) :
    advanceRegisters (n + m) s = (advanceRegisters n s).bind (advanceRegisters m) := by
  induction n generalizing s with
  | zero => simp only [Nat.zero_add, advanceRegisters, Option.bind_some]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [advanceRegisters]
    cases step : nextRegister s with
    | none => rfl
    | some t => exact ih t

def bootstrapRegisters (tail : List Nat) : List Nat :=
  List.replicate 132 0 ++ [1] ++ List.replicate 56 0 ++ tail

private def bootstrap32 : RegisterState :=
  ⟨List.replicate 7 true ++ [false, false, true], 27,
    bootstrapRegisters [0,0,0,0,0,0,0,4,0,0,0,1]⟩

private def bootstrap64 : RegisterState :=
  ⟨List.replicate 12 true ++
    [false, true, true, false, false, false, true, true, false, false, true, false, true, true],
    31, bootstrapRegisters [2,1,0,1,0,0,0,1,0,0,0,1]⟩

/-- State reached after the 93 checked register cycles. -/
def preparedStart : RegisterState :=
  ⟨List.replicate 12 true ++ [false, true, true, false, false, true, false, false, true, false, true, true],
    50, bootstrapRegisters [0,0,0,1,0,0,0,0,0,0,0,1]⟩

section BootstrapReplay

set_option maxRecDepth 16384
set_option maxHeartbeats 7000000

private theorem bootstrap_first : advanceRegisters 32 initialState = some bootstrap32 := by
  decide +kernel

private theorem bootstrap_second : advanceRegisters 32 bootstrap32 = some bootstrap64 := by
  decide +kernel

private theorem bootstrap_last : advanceRegisters 29 bootstrap64 = some preparedStart := by
  decide +kernel

end BootstrapReplay

theorem bootstrap_exact :
    advanceRegisters 93 initialState = some preparedStart ∧ preparedStart.span = 74 := by
  refine ⟨?_, by decide +kernel⟩
  change advanceRegisters (32 + (32 + 29)) initialState = some preparedStart
  rw [advanceRegisters_add, bootstrap_first, Option.bind_some,
    advanceRegisters_add, bootstrap_second, Option.bind_some]
  exact bootstrap_last

/-- The 93 cycles give a permanent span of 74 cells before the leading separator. -/
theorem checked_bootstrap :
    (advanceRegisters 93 initialState).any (fun s => s.span == 74) = true := by
  simp [bootstrap_exact.1, bootstrap_exact.2]

private theorem initial_register_count : 13 ≤ initialState.registers.length := by
  simp only [initialState, List.length_append, List.length_replicate, List.length_singleton]
  decide

theorem boot_ready :
    initialState.config ⟶* preparedStart.config ∧ preparedStart.Prepared := by
  obtain ⟨hRun, hSpan⟩ := bootstrap_exact
  obtain ⟨reach, clean, counts⟩ := advance_realizes
    (n := 93) (s := initialState) (t := preparedStart) hRun clean_nil initial_register_count
  exact ⟨reach, clean, counts.symm ▸ initial_register_count, Nat.le_of_eq hSpan.symm⟩

theorem unbounded_simulation :
    RunSimulation nextRegister referenceMachine (fun s c => s.Prepared ∧ c = s.config) := by
  constructor
  · intro s c hFrame hStop
    obtain ⟨ready, rfl⟩ := hFrame
    have hSound := execute_realizes s ready.1 ready.2.1
    cases hOut : execute s with
    | invalid => exact (execute_safe s ready hOut).elim
    | halt => rwa [hOut] at hSound
    | next t => simp [nextRegister, hOut] at hStop
  · intro s t c hFrame hNext
    obtain ⟨ready, rfl⟩ := hFrame
    have hSound := execute_realizes s ready.1 ready.2.1
    cases hOut : execute s with
    | invalid => simp [nextRegister, hOut] at hNext
    | halt => simp [nextRegister, hOut] at hNext
    | next u =>
      simp only [nextRegister, hOut, Option.some.injEq] at hNext
      subst u
      rw [hOut] at hSound
      obtain ⟨⟨n, positive, reach⟩, clean, regs, span⟩ := hSound
      exact ⟨n, t.config, positive, reach, ⟨clean, regs.symm ▸ ready.2.1,
        Nat.le_trans ready.2.2 span⟩, rfl⟩

/-- The literal machine's halting is equivalent to termination of its
unbounded register interpreter after the finite loader. -/
theorem literal_halts_iff_register :
    HaltsFrom machine blank ↔ Terminates nextRegister preparedStart := by
  obtain ⟨⟨n, hRun⟩, ready⟩ := boot_ready
  have hFirst : HaltsFrom referenceMachine blank ↔ HaltsFrom referenceMachine loaderExit :=
    halts_after_run (m := referenceMachine) (n := 39753) (c := blank) (d := loaderExit)
      reference_startup
  have hSecond : HaltsFrom referenceMachine loaderExit ↔ HaltsFrom referenceMachine preparedStart.config := by
    rw [← initial_configuration]
    exact halts_after_run hRun
  exact literal_halts_iff_reference.trans
    (hFirst.trans (hSecond.trans (unbounded_simulation.halts_iff ⟨ready, rfl⟩)))

theorem advance_terminates {n : Nat} {s t : RegisterState}
    (h : advanceRegisters n s = some t) :
    Terminates nextRegister s ↔ Terminates nextRegister t := by
  induction n generalizing s with
  | zero =>
    change some s = some t at h
    cases h
    exact Iff.rfl
  | succ n ih =>
    cases next : nextRegister s with
    | none => simp [advanceRegisters, next] at h
    | some u =>
      have rest : advanceRegisters n u = some t := by
        simpa only [advanceRegisters, next, Option.bind_some] using h
      refine Iff.trans ?_ (ih rest)
      constructor
      · intro terminates
        cases terminates with
        | stop e => simp [next] at e
        | advance e hNext =>
          rw [next] at e
          cases e
          exact hNext
      · exact .advance next

theorem literal_halts_iff_register_initial :
    HaltsFrom machine blank ↔ Terminates nextRegister initialState :=
  literal_halts_iff_register.trans
    (advance_terminates (n := 93) (s := initialState) (t := preparedStart) bootstrap_exact.1).symm

end PalomarI3380.Engine
