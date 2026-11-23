module
public import I3_334Support.Calibration.GroundContexts
import Mathlib.Tactic.FinCases
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {n : Nat}
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def template (term : PalomarI3380.Term (Fin n)) : ClosedSemiterm FilterLanguage n :=
  embedTerm .bvar term

noncomputable def instantiate (term : PalomarI3380.Term (Fin n)) (args : M) : M :=
  termSubst FilterLanguage args ⌜template term⌝

noncomputable def instantiateDef (term : PalomarI3380.Term (Fin n)) : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “out args. !(termSubstGraph FilterLanguage) out args ↑(⌜template term⌝ : Nat)”

theorem instantiate_defined (term : PalomarI3380.Term (Fin n)) :
    𝚺ᴬ₁-Function₁ (instantiate (M := M) term) via instantiateDef term := .mk <| by
  intro v
  simp [instantiateDef,instantiate,termSubst.defined.iff,numeral_eq_natCast,FFL.FirstOrder.Semiterm.empty_quote_eq_encode]

private theorem substitute_application {k : Nat} (symbol : FunctionSymbol k)
    (terms : Fin k → ClosedSemiterm FilterLanguage n) (args : Fin n → GroundTerm M) :
    (⌜(FFL.FirstOrder.Semiterm.func (L := FilterLanguage) symbol terms :
      ClosedSemiterm FilterLanguage n)⌝ : Bootstrapping.Semiterm M FilterLanguage n).subst args =
      application symbol (fun i => (⌜terms i⌝ : Bootstrapping.Semiterm M FilterLanguage n).subst args) :=
  Bootstrapping.Semiterm.substs_func (L := FilterLanguage) symbol args (fun i => ⌜terms i⌝)

theorem substitute_eq_eval (term : PalomarI3380.Term (Fin n)) (args : Fin n → GroundTerm M) :
    (⌜template term⌝ : Bootstrapping.Semiterm M FilterLanguage n).subst args =
      groundAlgebra.eval args term := by
  induction term <;>
    simp_all [template,embedTerm,Algebra.eval,groundAlgebra,substitute_application,
      Function.comp_def,Matrix.comp_vecCons',
      Matrix.empty_eq,Matrix.constant_eq_singleton]
  all_goals
    congr 1
    funext i
    fin_cases i <;> simp_all

theorem instantiate_eval (term : PalomarI3380.Term (Fin n)) (args : Fin n → GroundTerm M) :
    instantiate term (matrixToVec fun i => (args i).val) = (groundAlgebra.eval args term).val := by
  exact congrArg Bootstrapping.Semiterm.val (substitute_eq_eval term args)

end PalomarI3380.Calibration.TermWords
