module
public import I0451.PermanentFrame

/-! Unbounded instruction-level execution of the literal machine.
The proved interpreter and the physical machine have the same halting
predicate from the verified startup frame. -/
@[expose] public section
namespace I0451.Runtime

theorem ready_permanent : Permanent readyFrame := by
  let address := pack readyFrame.word 0
  have checked : (Decoder.decode 94 root true false address).map (·.rest) = some 0 := by
    decide +kernel
  cases parsed : Decoder.decode 94 root true false address with
  | none => simp [parsed] at checked
  | some d =>
    have noStray : d.rest = 0 := by simpa [parsed] using checked
    refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
    refine ⟨d.word, Decoder.decoded_address parsed, ?_⟩
    have same := (Decoder.decode_sound parsed).1
    rw [noStray] at same
    exact same.symm

/-- A finite computation of the abstract instruction interpreter ending
in the halt instruction. -/
def MacroHalts (f : RegisterFrame) : Prop :=
  ∃ n g, runMacros n f = some g ∧ macroStep g = .halt

private theorem macroHalts_of_physical {f : RegisterFrame} (good : Permanent f)
    (halted : Halts literal f.tape) : MacroHalts f := by
  obtain ⟨fuel, endTape, runToEnd, endStep⟩ := halted
  induction fuel using Nat.strongRecOn generalizing f with
  | ind fuel ih =>
    have preserves := macroStep_preserves good
    have sound := macroStep_sound f
    cases stepEq : macroStep f with
    | invalid => simp [stepEq, Preserves] at preserves
    | halt => exact ⟨0, f, rfl, stepEq⟩
    | next g =>
      rw [stepEq] at preserves sound
      obtain ⟨n, pos, predecessor⟩ := sound
      have enough := run_len_le_terminal predecessor runToEnd endStep
      obtain ⟨remaining, length⟩ := Nat.exists_eq_add_of_le enough
      rw [length, run_add, predecessor] at runToEnd
      obtain ⟨macros, last, runAbstract, haltAbstract⟩ :=
        ih remaining (by omega) preserves runToEnd
      exact ⟨macros + 1, last, by simpa only [runMacros, stepEq] using runAbstract, haltAbstract⟩

private theorem physical_of_macroHalts {f : RegisterFrame} (halted : MacroHalts f) :
    Halts literal f.tape := by
  obtain ⟨n, g, visits, stops⟩ := halted
  obtain ⟨m, reach⟩ := runMacros_sound visits
  have halt := macroStep_sound g
  rw [stops] at halt
  exact (halts_iff_of_run reach).2 halt

theorem halts_iff_macro {f : RegisterFrame} (good : Permanent f) :
    Halts literal f.tape ↔ MacroHalts f :=
  ⟨macroHalts_of_physical good, physical_of_macroHalts⟩

/-- Direct equivalence for the exact 451-state table. -/
theorem blank_halts_iff_interpreter :
    Halts literal (blank 0) ↔ MacroHalts readyFrame := by
  obtain ⟨n, reach⟩ := blank_reaches_ready_frame
  exact (halts_iff_of_run reach).trans (halts_iff_macro ready_permanent)

end I0451.Runtime
