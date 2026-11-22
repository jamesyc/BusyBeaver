module
public import ZF192Support.Execution.Commands.Program.ResidualTail
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def residualIterationBlueprint : PR.Blueprint 1 where
 zero := .mkSigma “z n. z=n”
 succ := .mkSigma “u z i n. !residualTailGraph u z”
noncomputable def residualIterationConstruction : PR.Construction M residualIterationBlueprint where
 zero := fun v => v 0
 succ := fun _ _ z => residualTail z
 zero_defined := .mk (by intro v; simp [residualIterationBlueprint])
 succ_defined := .mk (by intro v; simp [residualIterationBlueprint,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,residualTail_defined.iff])
noncomputable def residualIter (k n : M) : M := residualIterationConstruction.result ![n] k
def residualIterGraph : 𝚺ᴬ₁.Semisentence 3 := residualIterationBlueprint.resultDef
lemma residualIterGraph_defined : 𝚺ᴬ₁.DefinedFunction₂ (residualIter (M:=M)) residualIterGraph := .mk (by
 intro v
 rw [Matrix.fun_eq_vec_three v]
 exact residualIterationConstruction.result_defined_iff _)
lemma residualIter_zero (n : M) : residualIter 0 n=n := residualIterationConstruction.result_zero ![n]
lemma residualIter_succ (k n : M) : residualIter (k+1) n=residualTail (residualIter k n) :=
 residualIterationConstruction.result_succ ![n] k
instance residualIter_definable : 𝚺ᴬ₁-Function₂ (residualIter (M:=M)) := residualIterGraph_defined.to_definable
lemma residualIter_at_zero (k : M) : residualIter k (0:M)=0 := by
 induction k using ISigma1.sigma1_succ_induction
 · definability
 case zero => exact residualIter_zero 0
 case succ k ih => rw [residualIter_succ,ih,residualTail_zero]
lemma residualIter_commute (k n : M) : residualIter k (residualTail n)=residualIter (k+1) n := by
 induction k using ISigma1.sigma1_succ_induction
 · definability
 case zero => rw [residualIter_zero,residualIter_succ,residualIter_zero]
 case succ k ih => rw [residualIter_succ,ih,residualIter_succ (k+1)]
lemma residualIter_stops (k n : M) (hn:n≤k) : residualIter k n=0 := by
 have hh : ∀k : M, ∀n≤k, residualIter k n=0 := by
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
   intro n hn
   have hz:n=0 := le_antisymm hn (by simp)
   rw [hz,residualIter_zero]
  case succ k ih =>
   intro n hn
   by_cases hz:n=0
   · rw [hz,residualIter_at_zero]
   · rw [←residualIter_commute]
     apply ih
     have hlt := residualTail_lt n (pos_iff_ne_zero.mpr hz)
     exact lt_succ_iff_le.mp (lt_of_lt_of_le hlt hn)
 exact hh k n hn
end ZF192Support.ModelCommands
