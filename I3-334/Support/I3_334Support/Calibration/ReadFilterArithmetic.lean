module
public import I3_334Support.Calibration.ArithmeticTemplateSemantics
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open Logic (SetFormula)
open Logic.Expanded (ClassAxioms OmegaDomain)
open ArithmeticInterpretation (Reads)

variable {A : Type} [Tarski.Structure FilterLanguage A] [Tarski.Structure.Eq FilterLanguage A]
variable (C : FilterModel A)
variable {laws : ClassAxioms C.mem (fun _ _ => False)} {inhabited : Nonempty C.Domain}
variable (D : OmegaDomain laws inhabited)

/-- In the graph structure, the arithmetic templates read the model's
named natural numbers through a surjection defined on the whole algebra. -/
theorem reads_filter_arithmetic (marker : A) (default : C.Representative) :
    letI := graphStructure (A := A)
    Reads filterInterpretation marker (readValue C D) := by
  letI := graphStructure (A := A)
  refine ⟨readValue_surjective C D,fun _ => trivial,?_,?_,?_,?_,?_,?_⟩
  · intro x y
    have scope : SetFormula.Scoped 2 (SetFormula.eq 1 0) := SetFormula.scope_eq (by decide) (by decide)
    change (markedTemplate 2 (SetFormula.eq 1 0)).Evalb (marker :> ![x,y]) ↔
      readValue C D x = readValue C D y
    rw [markedTemplate_eval C D _ scope _ marker default,SetFormula.holds_eq C.mem 2 1 0 _ _ (by decide) (by decide)]
    simp only [naturalLevels,show 1 < 2 by decide,show 0 < 2 by decide,↓reduceDIte]
    exact Subtype.ext_iff.symm
  · intro x y
    have scope : SetFormula.Scoped 2 (SetFormula.mem 1 0) := SetFormula.scope_mem (by decide) (by decide)
    change (markedTemplate 2 (SetFormula.mem 1 0)).Evalb (marker :> ![x,y]) ↔
      readValue C D x < readValue C D y
    rw [markedTemplate_eval C D _ scope _ marker default,SetFormula.holds_mem C.mem 2 1 0 _ _ (by decide) (by decide)]
    simp [naturalLevels] <;> rfl
  · intro x
    have scope : SetFormula.Scoped 1 (SetFormula.numeral 0 0) := SetFormula.scope_numeral _ (by decide)
    change (markedTemplate 1 (SetFormula.numeral 0 0)).Evalb (marker :> ![x]) ↔ readValue C D x = 0
    rw [markedTemplate_eval C D _ scope _ marker default,SetFormula.holds_numeral _ (by decide)]
    change Logic.Internal.Numeral (laws.context inhabited).mem 0 _ ↔ _
    rw [(laws.context inhabited).numeral_def]
    simp only [naturalLevels,show 0 < 1 by decide,↓reduceDIte]
    change (readValue C D x).val = (0 : D.Points).val ↔ _
    exact Subtype.ext_iff.symm
  · intro x
    have scope : SetFormula.Scoped 1 (SetFormula.numeral 1 0) := SetFormula.scope_numeral _ (by decide)
    change (markedTemplate 1 (SetFormula.numeral 1 0)).Evalb (marker :> ![x]) ↔ readValue C D x = 1
    rw [markedTemplate_eval C D _ scope _ marker default,SetFormula.holds_numeral _ (by decide)]
    change Logic.Internal.Numeral (laws.context inhabited).mem 1 _ ↔ _
    rw [(laws.context inhabited).numeral_def]
    simp only [naturalLevels,show 0 < 1 by decide,↓reduceDIte]
    change (readValue C D x).val = (1 : D.Points).val ↔ _
    exact Subtype.ext_iff.symm
  · intro a b out
    have scope : SetFormula.Scoped 3 (SetFormula.addition 2 1 0) :=
      SetFormula.scope_addition (by decide) (by decide) (by decide)
    change (markedTemplate 3 (SetFormula.addition 2 1 0)).Evalb (marker :> ![a,b,out]) ↔
      readValue C D a + readValue C D b = readValue C D out
    rw [markedTemplate_eval C D _ scope _ marker default,SetFormula.holds_addition (by decide) (by decide) (by decide)]
    simp only [naturalLevels,show 0 < 3 by decide,show 1 < 3 by decide,show 2 < 3 by decide,↓reduceDIte]
    exact (D.add_result _ _ _).trans (eq_comm.trans Subtype.ext_iff.symm)
  · intro a b out
    have scope : SetFormula.Scoped 3 (SetFormula.multiplication 2 1 0) :=
      SetFormula.scope_multiplication (by decide) (by decide) (by decide)
    change (markedTemplate 3 (SetFormula.multiplication 2 1 0)).Evalb (marker :> ![a,b,out]) ↔
      readValue C D a * readValue C D b = readValue C D out
    rw [markedTemplate_eval C D _ scope _ marker default,
      SetFormula.holds_multiplication (by decide) (by decide) (by decide)]
    simp only [naturalLevels,show 0 < 3 by decide,show 1 < 3 by decide,show 2 < 3 by decide,↓reduceDIte]
    exact (D.mul_result _ _ _).trans (eq_comm.trans Subtype.ext_iff.symm)

end PalomarI3380.Calibration
