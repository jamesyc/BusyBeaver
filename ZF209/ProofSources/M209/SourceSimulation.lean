module
public import M6.Zip
@[expose] public section
namespace M209.SourceSimulation
open M6.Zip

/-- Finite termination of a deterministic source transition function. -/
inductive Terminates {S : Type} (next : S → Option S) : S → Prop where
  | done {s} : next s = none → Terminates next s
  | more {s t} : next s = some t → Terminates next t → Terminates next s

/-- Strict macro-step progress excludes finite physical halting. Adapted from
jamesyc/BusyBeaver M6/PositiveInvariant.lean; no machine-specific assumptions. -/
theorem not_halts_of_positive_invariant (M : TMN) (Inv : Conf → Prop)
    (progress : ∀ c, Inv c → ∃ d, Reach1 M c d ∧ Inv d)
    (initial : Conf) (hi : Inv initial) : ¬ Halts M initial := by
  rintro ⟨terminal, ⟨n, hrun⟩, hstop⟩
  have impossible : ∀ n c, Inv c → run M n c = some terminal → False := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro c hc hr
        obtain ⟨d, ⟨k, hmove⟩, hd⟩ := progress c hc
        by_cases hkn : k < n
        · have hle : k + 1 ≤ n := by omega
          obtain ⟨remaining, heq⟩ := Nat.exists_eq_add_of_le hle
          have htail : run M remaining d = some terminal := by
            rw [heq, run_add, hmove] at hr
            exact hr
          exact ih remaining (by omega) d hd htail
        · have hle : n ≤ k := by omega
          obtain ⟨remaining, heq⟩ := Nat.exists_eq_add_of_le hle
          have hlong : run M (n + (remaining + 1)) c = some d := by
            simpa only [heq, Nat.add_assoc] using hmove
          rw [run_add, hr] at hlong
          simp only [run, hstop] at hlong
          cases hlong
  exact impossible n initial hi hrun

/-- The complete interface needed to compose all finite source contracts.
`valid` must include program-index and whole-file invariants. `frame` represents
the entire physical configuration, not a projection to logical registers. -/
structure Implements {S : Type} (M : TMN) (next : S → Option S)
    (valid : S → Prop) (frame : S → Conf) : Prop where
  preserve : ∀ s t, valid s → next s = some t → valid t
  terminal : ∀ s, valid s → next s = none → Halts M (frame s)
  progress : ∀ s t, valid s → next s = some t → Reach1 M (frame s) (frame t)

theorem source_to_machine {S : Type} {M : TMN} {next : S → Option S}
    {valid : S → Prop} {frame : S → Conf}
    (correct : Implements M next valid frame) {s : S}
    (hs : valid s) (h : Terminates next s) : Halts M (frame s) := by
  induction h with
  | done h => exact correct.terminal _ hs h
  | more h _ ih =>
    exact (ih (correct.preserve _ _ hs h)).of_reach (correct.progress _ _ hs h).reach

theorem machine_to_source {S : Type} {M : TMN} {next : S → Option S}
    {valid : S → Prop} {frame : S → Conf}
    (correct : Implements M next valid frame) {s : S}
    (hs : valid s) (h : Halts M (frame s)) : Terminates next s := by
  classical
  apply Classical.byContradiction
  intro hn
  let Inv : Conf → Prop := fun c => ∃ t, valid t ∧ ¬ Terminates next t ∧ c = frame t
  apply not_halts_of_positive_invariant M Inv ?_ (frame s) ⟨s,hs,hn,rfl⟩ h
  intro c hc
  obtain ⟨t,ht,hn,rfl⟩ := hc
  cases he : next t with
  | none => exact False.elim (hn (.done he))
  | some u =>
    exact ⟨frame u, correct.progress t u ht he, u,
      correct.preserve t u ht he, fun hu => hn (.more he hu), rfl⟩

theorem halts_iff_source {S : Type} {M : TMN} {next : S → Option S}
    {valid : S → Prop} {frame : S → Conf}
    (correct : Implements M next valid frame) {s : S} (hs : valid s) :
    Halts M (frame s) ↔ Terminates next s :=
  ⟨machine_to_source correct hs, source_to_machine correct hs⟩
/-- Determinism carries any alleged halt past a finite checked startup prefix. -/
theorem halt_after_reach {M : TMN} {a b : Conf}
    (hr : Reach M a b) (hh : Halts M a) : Halts M b := by
  obtain ⟨n,hn⟩ := hr
  obtain ⟨z,⟨k,hk⟩,hz⟩ := hh
  by_cases hnk : n ≤ k
  · refine ⟨z,⟨k-n,?_⟩,hz⟩
    have he : k = n + (k-n) := by omega
    rw [he,run_add,hn] at hk
    exact hk
  · have he : n = k + (n-k) := by omega
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n-k ≠ 0)
    rw [he,run_add,hk,hm] at hn
    simp [M6.Zip.run,hz] at hn

end M209.SourceSimulation
