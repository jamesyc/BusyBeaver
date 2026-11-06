import PA215PA.Startup

namespace PA215.PA.NatTape

theorem halts_step_iff {s t : Configuration} (hs : step s = some t) :
    Halts s ↔ Halts t := by
  constructor
  · rintro ⟨n,u,hr,hu⟩
    cases n with
    | zero =>
      have he : s = u := Option.some.inj hr
      have hn : step s = none := by simp [step,he,hu,halt]
      rw [hn] at hs
      contradiction
    | succ n =>
      exact ⟨n,u,by simpa [run,hs] using hr,hu⟩
  · rintro ⟨n,u,hr,hu⟩
    exact ⟨n+1,u,by simp [run,hs,hr],hu⟩

theorem halts_run_iff {n : Nat} {s t : Configuration}
    (h : run n s = some t) : Halts s ↔ Halts t := by
  induction n generalizing s with
  | zero =>
    have he : s = t := Option.some.inj h
    rw [he]
  | succ n ih =>
    cases hs : step s with
    | none => simp [run,hs] at h
    | some u =>
      have hu : run n u = some t := by simpa [run,hs] using h
      exact (halts_step_iff hs).trans (ih hu)

end PA215.PA.NatTape

namespace PA215.PA.Startup

theorem blank_halts_iff_final : NatTape.Halts NatTape.blank ↔ NatTape.Halts c064 :=
  NatTape.halts_run_iff blank_run_63228

#print axioms blank_halts_iff_final
end PA215.PA.Startup
