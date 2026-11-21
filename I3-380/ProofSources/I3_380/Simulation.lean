module
public import I3_380.Machine
@[expose] public section

namespace PalomarI3380

/-- A terminal configuration reached after finitely many literal steps. -/
def HaltsFrom (m : Machine) (c : Configuration) : Prop :=
  ∃ n terminal, run m n c = some terminal ∧ step m terminal = none

inductive Terminates {State : Type} (next : State → Option State) : State → Prop where
  | stop : next s = none → Terminates next s
  | advance : next s = some t → Terminates next t → Terminates next s

theorem Terminates.map_iff {X Y : Type} {small : X → Option X} {large : Y → Option Y}
    (project : X → Y) (valid : X → Prop)
    (same : ∀ x, valid x → (small x).map project = large (project x))
    (preserved : ∀ {x x'}, valid x → small x = some x' → valid x')
    {x : X} (hx : valid x) :
    Terminates small x ↔ Terminates large (project x) := by
  constructor
  · intro h
    induction h with
    | stop stopped =>
      have eq := same _ hx
      rw [stopped] at eq
      exact .stop eq.symm
    | advance next _ ih =>
      have eq := same _ hx
      rw [next, Option.map_some] at eq
      exact .advance eq.symm (ih (preserved hx next))
  · intro h
    generalize eq : project x = y at h
    induction h generalizing x with
    | stop stopped =>
      have equation := same _ hx
      rw [eq, stopped] at equation
      cases next : small x with
      | none => exact .stop next
      | some x' => simp [next] at equation
    | advance next _ ih =>
      have equation := same _ hx
      rw [eq, next] at equation
      cases source : small x with
      | none => simp [source] at equation
      | some x' =>
        exact .advance source (ih (preserved hx source) (by simpa [source] using equation))

theorem halts_iff_terminates (m : Machine) (c : Configuration) :
    HaltsFrom m c ↔ Terminates (step m) c := by
  constructor
  · rintro ⟨n, terminal, h, done⟩
    induction n generalizing c with
    | zero =>
      change some c = some terminal at h
      cases h
      exact .stop done
    | succ n ih =>
      rw [run] at h
      cases next : step m c with
      | none => simp [next] at h
      | some d => exact .advance next (ih d (by simpa only [next] using h))
  · intro h
    induction h with
    | stop h => exact ⟨0, _, rfl, h⟩
    | advance h₁ _ ih =>
      obtain ⟨n, d, h₂, h₃⟩ := ih
      refine ⟨n + 1, d, ?_, h₃⟩
      rw [run, h₁]
      exact h₂

theorem halts_after_run {m : Machine} {n : Nat} {c d : Configuration}
    (h : run m n c = some d) : HaltsFrom m c ↔ HaltsFrom m d := by
  induction n generalizing c with
  | zero =>
    change some c = some d at h
    cases h
    exact Iff.rfl
  | succ n ih =>
    rw [run] at h
    cases hs : step m c with
    | none => simp [hs] at h
    | some next =>
      have hTail : run m n next = some d := by simpa only [hs] using h
      refine Iff.trans ?_ (ih hTail)
      rw [halts_iff_terminates, halts_iff_terminates]
      constructor
      · intro terminates
        cases terminates with
        | stop e => rw [hs] at e; contradiction
        | advance e hNext =>
          rw [hs] at e
          cases e
          exact hNext
      · exact .advance hs

/-- Contracts for a register-step interpreter. The frame relation admits
different physical encodings of the same source state, including different
padding or tape outside the active frame. -/
structure RunSimulation {State : Type} (next : State → Option State) (m : Machine)
    (frame : State → Configuration → Prop) : Prop where
  halt : ∀ {s c}, frame s c → next s = none → HaltsFrom m c
  advance : ∀ {s t c}, frame s c → next s = some t →
    ∃ n d, 0 < n ∧ run m n c = some d ∧ frame t d

namespace RunSimulation

variable {State : Type} {next : State → Option State} {m : Machine}
variable {frame : State → Configuration → Prop}

theorem halts_of_terminates (sim : RunSimulation next m frame)
    {s : State} {c : Configuration} (h : Terminates next s) (hf : frame s c) :
    HaltsFrom m c := by
  induction h generalizing c with
  | stop hs => exact sim.halt hf hs
  | advance hs _ ih =>
      obtain ⟨n, d, _, hRun, hFrame⟩ := sim.advance hf hs
      obtain ⟨k, terminal, hTail, hHalt⟩ := ih hFrame
      exact ⟨n + k, terminal, join_run hRun hTail, hHalt⟩

theorem runs_at_least (sim : RunSimulation next m frame) (fuel : Nat)
    {s : State} {c : Configuration} (hf : frame s c) (h : ¬ Terminates next s) :
    ∃ n d, fuel ≤ n ∧ run m n c = some d := by
  induction fuel generalizing s c with
  | zero => exact ⟨0, c, Nat.le_refl 0, rfl⟩
  | succ fuel ih =>
      cases hs : next s with
      | none => exact (h (.stop hs)).elim
      | some t =>
          obtain ⟨n, d, hn, hRun, hFrame⟩ := sim.advance hf hs
          obtain ⟨k, tail, hk, hTail⟩ := ih hFrame (fun ht => h (.advance hs ht))
          exact ⟨n + k, tail, by omega, join_run hRun hTail⟩

/-- The positive duration of each simulated step rules out a halt during
an infinite source run. -/
theorem halts_iff (sim : RunSimulation next m frame) {s : State} {c : Configuration}
    (hf : frame s c) : HaltsFrom m c ↔ Terminates next s := by
  classical
  constructor
  · rintro ⟨n, terminal, hRun, hStop⟩
    apply Classical.byContradiction
    intro hSource
    obtain ⟨elapsed, d, hElapsed, hLongRun⟩ := sim.runs_at_least (n + 1) hf hSource
    have hSteps : elapsed = n + (elapsed - (n + 1) + 1) := by omega
    rw [hSteps, run_add, hRun] at hLongRun
    change run m (elapsed - (n + 1) + 1) terminal = some d at hLongRun
    rw [run, hStop] at hLongRun
    contradiction
  · exact fun h => sim.halts_of_terminates h hf

end RunSimulation
end PalomarI3380
