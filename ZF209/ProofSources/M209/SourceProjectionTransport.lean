module
public import M209.SourceSimulation
@[expose] public section
namespace M209.SourceSimulation

theorem termination_projection {S T : Type} (source : S → Option S) (target : T → Option T)
    (project : S → T) (valid : S → Prop)
    (preserve : ∀ s t, valid s → source s = some t → valid t)
    (commute : ∀ s, valid s → target (project s) = (source s).map project)
    (s : S) (hs : valid s) : Terminates source s ↔ Terminates target (project s) := by
  constructor
  · intro h
    induction h with
    | done hn =>
      apply Terminates.done
      rw [commute _ hs,hn]
      rfl
    | more hn _ ih =>
      apply Terminates.more (t := project _)
      · rw [commute _ hs,hn]
        rfl
      · exact ih (preserve _ _ hs hn)
  · intro h
    have aux : ∀ t, Terminates target t → ∀ u, valid u → project u = t → Terminates source u := by
      intro t ht
      induction ht with
      | @done t hnone =>
        intro u hu heq
        cases hnext : source u with
        | none => exact .done hnext
        | some v =>
          have hc := commute u hu
          rw [heq,hnone,hnext] at hc
          cases hc
      | @more t v hstep _ ih =>
        intro u hu heq
        cases hnext : source u with
        | none =>
          have hc := commute u hu
          rw [heq,hstep,hnext] at hc
          cases hc
        | some w =>
          apply Terminates.more hnext
          apply ih w (preserve u w hu hnext)
          have hc := commute u hu
          rw [heq,hstep,hnext] at hc
          exact (Option.some.inj hc).symm
    exact aux (project s) h s hs rfl
end M209.SourceSimulation
