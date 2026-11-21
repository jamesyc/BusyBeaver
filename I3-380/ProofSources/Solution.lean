module
public import I3_380.Arithmetic.HaltingSoundness
public import I3_380.EquationalConsistency
public import I3_380.Search.Compiler.SearchCompleteness
public import I3_380.Calibration.InternalConsistency
@[expose] public section

namespace PalomarI3380

/-- Local statement comparison for the exact machine table and its loader. -/
theorem loaderReplay :
    machine.workingStates = 380 ∧ literal.size = 760 ∧
    (literal.toList.zipIdx.all fun (row, i) => machine.row (i / 2) (i % 2) == row) = true ∧
    run machine 39753 blank = some loaderExit :=
  ⟨literal_shape.1, literal_shape.2.1, packed_rows_exact, literal_startup⟩

theorem consistency_of_literal_nonhalting (h : ¬HaltsFrom machine blank) : Logic.ZFCI3Consistent :=
  consistency_of_equational_underivability (fun proof =>
    h (Compiler.Source.exact_machine_halts_iff_derives.mpr proof))

/-- External consistency calibration for the exact released machine. -/
theorem literal_nonhalting_iff_consistency :
    (¬HaltsFrom machine blank) ↔ Logic.ZFCI3Consistent :=
  ⟨consistency_of_literal_nonhalting, fun h halt =>
    equational_underivability_of_consistency h (Compiler.Source.exact_machine_halts_iff_derives.mp halt)⟩

theorem literal_halting_unprovable (soundness : Logic.ArithmeticSigma1Sound) :
    ¬Logic.ZFCI3Provable Logic.haltingSentence :=
  Logic.halting_unprovable_of_nonhalting soundness
    (literal_nonhalting_iff_consistency.mpr soundness.consistent)

theorem literal_nonhalting_unprovable (consistency : Logic.ZFCI3Consistent) :
    ¬Logic.ZFCI3Provable (Logic.Neg Logic.haltingSentence) :=
  Calibration.calibration.nonhalting_unprovable consistency

/-- The external consistency calibration and both independence directions
for the literal 380-state machine. -/
theorem exactClaim : Logic.ExactClaim :=
  ⟨Logic.haltingSentence,Logic.haltingSentence_represents,
    fun h => ⟨literal_nonhalting_iff_consistency.mpr h,literal_nonhalting_unprovable h⟩,
    fun h => ⟨literal_halting_unprovable h,literal_nonhalting_unprovable h.consistent⟩⟩

end PalomarI3380
