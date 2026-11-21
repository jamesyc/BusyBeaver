module
public import I3_380.Engine.Bootstrap
public import I3_380.Engine.LogicalStep
@[expose] public section

namespace PalomarI3380.Engine

def RegisterState.logical (s : RegisterState) : LogicalState :=
  ⟨s.path, s.registers⟩

theorem logical_projection (s : RegisterState) (safe : execute s ≠ .invalid) :
    (nextRegister s).map RegisterState.logical = logicalNext s.logical := by
  obtain ⟨d, hd⟩ := decode_root (s.path ++ zeros 59)
    (by simp only [List.length_append, List.length_replicate]; omega)
  cases hActual : follow 59 Port.root [] (s.path ++ zeros s.gap) with
  | none => exact (safe (by simp only [execute, hActual])).elim
  | some e =>
    have same := logical_same_arm s.path s.registers s.gap 59 hActual hd
    simp only [logicalNext, RegisterState.logical, hd, Option.bind_some]
    rw [← same]
    cases hOp : e.command with
    | halt => simp [nextRegister, execute, hActual, executeDecoded, logicalDecoded, hOp]
    | «break» skip => simp [nextRegister, execute, hActual, executeDecoded, logicalDecoded, hOp,
        RegisterState.logical]
    | «continue» skip =>
      cases skip <;> simp [nextRegister, execute, hActual, executeDecoded, logicalDecoded, hOp,
        RegisterState.logical]
    | register dec r =>
      have hGap : r.val + 3 ≤ e.rest.length := by
        by_cases hGap : r.val + 3 ≤ e.rest.length
        · exact hGap
        · exact (safe (by simp only [execute, hActual, executeDecoded, hOp, hGap, ↓reduceIte])).elim
      simp [nextRegister, execute, hActual, executeDecoded, logicalDecoded, hOp, hGap,
        RegisterState.logical]

private theorem next_safe {s t : RegisterState} (h : nextRegister s = some t) :
    execute s ≠ .invalid := by
  intro bad
  simp [nextRegister, bad] at h

private theorem prepared_next {s t : RegisterState} (h : nextRegister s = some t)
    (ready : s.Prepared) : t.Prepared := by
  have evidence := execute_realizes s ready.1 ready.2.1
  cases hOut : execute s with
  | invalid => simp [nextRegister, hOut] at h
  | halt => simp [nextRegister, hOut] at h
  | next u =>
    simp only [nextRegister, hOut, Option.some.injEq] at h
    subst u
    rw [hOut] at evidence
    exact ⟨evidence.2.1, evidence.2.2.1.symm ▸ ready.2.1, Nat.le_trans ready.2.2 evidence.2.2.2⟩

theorem logical_termination {s : RegisterState} (ready : s.Prepared) :
    Terminates nextRegister s ↔ Terminates logicalNext s.logical := by
  constructor
  · intro h
    induction h with
    | stop e =>
      have h := logical_projection _ (execute_safe _ ready)
      rw [e] at h
      exact .stop h.symm
    | advance e _ ih =>
      have h := logical_projection _ (next_safe e)
      rw [e, Option.map_some] at h
      exact .advance h.symm (ih (prepared_next e ready))
  · intro h
    generalize heq : s.logical = c at h
    induction h generalizing s with
    | stop e =>
      have h := logical_projection s (execute_safe s ready)
      rw [heq, e] at h
      cases next : nextRegister s with
      | none => exact .stop next
      | some t => simp [next] at h
    | advance e _ ih =>
      have h := logical_projection s (execute_safe s ready)
      rw [heq, e] at h
      cases next : nextRegister s with
      | none => simp [next] at h
      | some t =>
        exact .advance next (ih (prepared_next next ready) (by simpa [next] using h))

theorem logical_after_bootstrap {n : Nat} {s t : RegisterState}
    (h : advanceRegisters n s = some t) :
    Terminates logicalNext s.logical ↔ Terminates logicalNext t.logical := by
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
      have logical : logicalNext s.logical = some u.logical := by
        have eq := logical_projection s (next_safe next)
        simpa only [next, Option.map_some] using eq.symm
      refine Iff.trans ?_ (ih rest)
      constructor
      · intro reaches
        cases reaches with
        | stop e => simp [logical] at e
        | advance e h' =>
          rw [logical] at e
          cases e
          exact h'
      · exact .advance logical

theorem literal_halts_iff_logical :
    HaltsFrom machine blank ↔ Terminates logicalNext initialState.logical :=
  literal_halts_iff_register.trans
    ((logical_termination boot_ready.2).trans
      (logical_after_bootstrap (n := 93) (s := initialState) (t := preparedStart) bootstrap_exact.1).symm)

end PalomarI3380.Engine
