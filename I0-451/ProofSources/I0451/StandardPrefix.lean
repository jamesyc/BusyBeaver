module
public import I0451.ArithmeticTrace
public import I0451.Boundary

/-! A standard finite tape prefix yields the same clock value in every
model of the arithmetic base. This covers the literal boot without
replaying individual tape cells inside the object theory. -/
@[expose] public section
namespace I0451.Arithmetization

theorem totalRun_of_run {table : Table} {n : Nat} {a b : Config}
    (ran : run table n a = some b) : totalRun table n a = b := by
  induction n generalizing a with
  | zero => exact Option.some.inj ran
  | succ n ih =>
    cases stepEq : step table a with
    | none => simp [run, stepEq] at ran
    | some c =>
      simp only [totalRun, totalStep, stepEq, Option.getD_some]
      exact ih (by simpa [run, stepEq] using ran)

section Models

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- All standard configurations along the blank-tape computation
also occur in the arithmetic model at the corresponding numeral. -/
theorem atTime_of_standard_run {table : Nat} {m : Nat} {c : Config}
    (ran : run table m (blank 0) = some c) :
    atTime table (m : V) = (encodeConfig c : V) := by
  have physical : atTime table m = encodeConfig c := by
    rw [atTime_nat, totalRun_of_run ran]
  let φ := (machineBlueprint table).resultDef
  have concrete : φ.val.Evalb (![encodeConfig c, m] : Fin 2 → Nat) :=
    (blankTime_defined table (V := Nat)).iff (v := ![encodeConfig c, m]) |>.mpr physical.symm
  have lifted := bold_sigma_one_completeness' (M := V) φ.sigma_prop concrete
  have typed : φ.val.Evalb (![↑(encodeConfig c), ↑m] : Fin 2 → V) := by
    simpa [numeral_eq_natCast, Function.comp_def, Matrix.comp_vecCons', Matrix.vec_single_eq_const] using lifted
  exact ((blankTime_defined table (V := V)).iff (v := ![↑(encodeConfig c), ↑m]) |>.mp typed).symm

theorem literal_boot_arithmetic :
    atTime literal (39753 : V) = (encodeConfig bootFrame : V) := by
  exact atTime_of_standard_run literal_boot

/-- The command scheduler starts from the same literal configuration
in the standard run and in every model of the arithmetic base. -/
theorem command_boundary_arithmetic :
    ∃ n : Nat, atTime literal (n : V) = (encodeConfig Runtime.commandBoundary.tape : V) := by
  obtain ⟨n, reached⟩ :=
    Runtime.blank_reaches_ready_frame.trans (Runtime.runMacros_sound Runtime.reaches_boundary)
  exact ⟨n, atTime_of_standard_run reached⟩

/-- The same internal halting sentence can be checked from the command
boundary, with its concrete initial register contents. -/
theorem literal_halts_from_boundary :
    (haltsDef literal).val.Evalb (![] : Fin 0 → V) ↔
      ∃ n : V, Terminal literal (trace literal n (encodeConfig Runtime.commandBoundary.tape : V)) := by
  obtain ⟨m, reached⟩ := command_boundary_arithmetic (V := V)
  rw [halts_after_prefix literal (m : V), trace_from_blank, reached]

end Models

end I0451.Arithmetization
