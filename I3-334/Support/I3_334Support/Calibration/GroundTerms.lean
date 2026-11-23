module
public import I3_334Support.Calibration.TermWords
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Coding
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ArithmeticMachine.SourceWords

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Codes with no dangling bound variables. Free-variable leaves are
read as D by termTokens. This supplies a total algebra of ground words. -/
abbrev GroundTerm (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :=
  Bootstrapping.Term M FilterLanguage

theorem arguments_wellFormed {n : Nat} (args : Fin n → GroundTerm M) :
    IsSemitermVec FilterLanguage (n : M) 0 (matrixToVec fun i => (args i).val) :=
  SemitermVec.isSemitermVec args

noncomputable def application {n : Nat} (symbol : FunctionSymbol n) (args : Fin n → GroundTerm M) :
    GroundTerm M :=
  Bootstrapping.Semiterm.func (L := FilterLanguage) symbol args

noncomputable def groundAlgebra : Algebra (GroundTerm M) where
  constant c := application (.constant c) ![]
  neg x := application .complement ![x]
  converse x := application .converse ![x]
  choice x := application .choose ![x]
  localRel x := application .localRelation ![x]
  nand x y := application .nand ![x,y]
  product x y := application .product ![x,y]
  node x y z := application .node ![x,y,z]

theorem argumentTokens {n : Nat} (args : Fin n → GroundTerm M) :
    termConstruction.resultVec FilterLanguage ![] (n : M) (matrixToVec fun i => (args i).val) =
      matrixToVec (fun i => termTokens (args i).val) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    let rest := fun i : Fin n => args i.succ
    have good := (arguments_wellFormed rest).isUTerm
    have first := (args 0).isUTerm
    change termConstruction.resultVec FilterLanguage ![] ((n : M)+1)
        ((args 0).val ∷ matrixToVec fun i => (rest i).val) = _
    rw [termConstruction.resultVec_cons _ _ good first,ih rest]
    rfl

theorem application_tokens {n : Nat} (symbol : FunctionSymbol n) (args : Fin n → GroundTerm M) :
    termTokens (application symbol args).val =
      ⟪(n : M),(⌜(show FilterLanguage.Func n from symbol)⌝ : M)⟫ ∷
        flattenTokens (matrixToVec fun i => termTokens (args i).val) := by
  have valid : FilterLanguage.IsFunc (n : M) (⌜(show FilterLanguage.Func n from symbol)⌝ : M) :=
    codeIn_func_quote (L := FilterLanguage) symbol
  change termConstruction.result FilterLanguage ![]
      (^func (n : M) (⌜(show FilterLanguage.Func n from symbol)⌝ : M) (matrixToVec fun i => (args i).val)) = _
  rw [termConstruction.result_func' (param := ![]) valid (arguments_wellFormed args).isUTerm]
  change _ ∷ flattenTokens (termConstruction.resultVec FilterLanguage ![] (n : M)
    (matrixToVec fun i => (args i).val)) = _
  rw [argumentTokens]

theorem termWord_nonempty (t : GroundTerm M) : 0 < termWord t.val := by
  have untyped := t.isUTerm
  unfold termWord
  apply emitVector_nonempty
  rcases IsUTerm.case_iff.mp untyped with bound | free | applied
  · obtain ⟨i,hi⟩ := bound
    rw [hi,termTokens,termConstruction.result_bvar]
    simp [termConstruction]
  · obtain ⟨i,hi⟩ := free
    rw [hi,termTokens,termConstruction.result_fvar]
    simp [termConstruction]
  · obtain ⟨k,f,args,ok,argsOk,same⟩ := applied
    rw [same,termTokens,termConstruction.result_func' (param := ![]) ok argsOk]
    simp [termConstruction]

end PalomarI3380.Calibration.TermWords
