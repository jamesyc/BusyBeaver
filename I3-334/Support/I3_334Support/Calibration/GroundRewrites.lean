module
public import I3_334Support.Calibration.GroundSubstitution
public import I3_334Support.Arithmetic.FiniteTraces
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ArithmeticMachine.SourceWords

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An instance of a basis equation in a common token
context. The two sides may be used in either orientation. -/
def EquationStep (row : Equation) (x y : M) : Prop :=
  ∃ args : M, IsSemitermVec FilterLanguage 3 0 args ∧
    ∃ ctx : Context M,
      let s := ctx.fill (termTokens (instantiate row.1 args))
      let t := ctx.fill (termTokens (instantiate row.2 args))
      (x = s ∧ y = t) ∨ (x = t ∧ y = s)

def RewriteStep (x y : M) : Prop :=
  ∃ row ∈ Manifest.final, EquationStep row x y

noncomputable def filledDef : 𝚺ᴬ₁.Semisentence 4 :=
  .mkSigma “out before body after. ∃ suffix,
    !appendBlueprint.resultDef suffix body after ∧ !appendBlueprint.resultDef out before suffix”

theorem filledDef_eval (out before body after : M) :
    filledDef.val.Evalb ![out,before,body,after] ↔ out = (Context.mk before after).fill body := by
  simp [filledDef,appendVector_eval,Context.fill]

noncomputable def instanceDef (term : PalomarI3380.Term (Fin 3)) : 𝚺ᴬ₁.Semisentence 4 :=
  .mkSigma “out args before after. ∃ code tokens,
    !(instantiateDef term) code args ∧ !termTokensDef tokens code ∧ !filledDef out before tokens after”

theorem instanceDef_eval (term : PalomarI3380.Term (Fin 3)) (out args before after : M) :
    (instanceDef term).val.Evalb ![out,args,before,after] ↔
      out = (Context.mk before after).fill (termTokens (instantiate term args)) := by
  simp [instanceDef,(instantiate_defined (M := M) term).iff,(termTokens_defined (M := M)).iff,filledDef_eval]

noncomputable def equationStepDef (row : Equation) : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “x y. ∃ args before after a b,
    !((isSemitermVec FilterLanguage).sigma) 3 0 args ∧
    !(instanceDef row.1) a args before after ∧ !(instanceDef row.2) b args before after ∧
    ((x = a ∧ y = b) ∨ (x = b ∧ y = a))”

theorem equationStepDef_eval (row : Equation) (x y : M) :
    (equationStepDef row).val.Evalb ![x,y] ↔ EquationStep row x y := by
  have valid (args : M) :
      (isSemitermVec FilterLanguage).sigma.val.Evalb ![3,0,args] ↔ IsSemitermVec FilterLanguage 3 0 args := by
    rw [Bounding.HierarchySymbol.Semiformula.val_sigma]
    exact (IsSemitermVec.defined (V := M) (L := FilterLanguage)).iff (v := ![3,0,args])
  simp [equationStepDef,valid,instanceDef_eval,EquationStep,Semiformula.eval_substs]
  constructor
  · rintro ⟨args,valid,before,after,eq⟩
    exact ⟨args,valid,⟨before,after⟩,eq⟩
  · rintro ⟨args,valid,⟨before,after⟩,eq⟩
    exact ⟨args,valid,before,after,eq⟩

noncomputable def stepsDef : List Equation → 𝚺ᴬ₁.Semisentence 2
  | [] => .mkSigma “x y. ⊥”
  | e :: rest => .mkSigma “x y. !(equationStepDef e) x y ∨ !(stepsDef rest) x y”

theorem stepsDef_eval (rows : List Equation) (x y : M) :
    (stepsDef rows).val.Evalb ![x,y] ↔ ∃ e ∈ rows, EquationStep e x y := by
  induction rows with
  | nil => simp [stepsDef]
  | cons e rest ih => simp [stepsDef, equationStepDef_eval, ih]

theorem rewriteStep_eval (x y : M) :
    (stepsDef Manifest.final).val.Evalb ![x,y] ↔ RewriteStep x y :=
  stepsDef_eval _ _ _

instance rewriteStep_definable : 𝚺ᴬ₁-Relation (RewriteStep (M := M)) :=
  (show 𝚺ᴬ₁-Relation (RewriteStep (M := M)) via stepsDef Manifest.final
    from .mk fun v => by rw [Matrix.fun_eq_vec_two v]; simpa only [Matrix.cons_val_zero,Matrix.cons_val_one]
      using rewriteStep_eval (v 0) (v 1)).to_definable

end PalomarI3380.Calibration.TermWords
