module
public import ModelCommandReverseStep
public import ModelResidualIteration
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def programReverseBlueprint : PR.Blueprint 2 where
 zero := .mkSigma “z n b. z=b”
 succ := .mkSigma “u z i n b. ∃g, !residualIterGraph g i n ∧ !reverseCommandStepGraph u g z”
noncomputable def programReverseConstruction : PR.Construction M programReverseBlueprint where
 zero := fun v => v 1
 succ := fun v i z => reverseCommandStep (residualIter i (v 0)) z
 zero_defined := .mk (by intro v; simp [programReverseBlueprint])
 succ_defined := .mk (by
  intro v
  simp [programReverseBlueprint,Semiformula.eval_rew,Function.comp_def,
   Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,residualIterGraph_defined.iff,reverseCommandStep_defined.iff])
noncomputable def programReverseSteps (k n b:M) : M := programReverseConstruction.result ![n,b] k
def programReverseStepsGraph : 𝚺ᴬ₁.Semisentence 4 := programReverseBlueprint.resultDef
lemma programReverseSteps_defined : 𝚺ᴬ₁.DefinedFunction₃ (programReverseSteps (M:=M)) programReverseStepsGraph := .mk (by
 intro v
 have hv:v=![v 0,v 1,v 2,v 3] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  refine Fin.cases rfl (fun j=>?_) j
  refine Fin.cases rfl (fun j=>?_) j
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]; exact programReverseConstruction.result_defined_iff _)
instance programReverseSteps_definable : 𝚺ᴬ₁-Function₃ (programReverseSteps (M:=M)) := programReverseSteps_defined.to_definable
lemma programReverseSteps_zero (n b:M) : programReverseSteps 0 n b=b := programReverseConstruction.result_zero ![n,b]
lemma programReverseSteps_succ (k n b:M) : programReverseSteps (k+1) n b=
 reverseCommandStep (residualIter k n) (programReverseSteps k n b) := programReverseConstruction.result_succ ![n,b] k
noncomputable def programReverseOnto (n b:M) : M := programReverseSteps n n b
lemma programReverseSteps_cons (k:M) (c:Command M) (n b:M) :
 programReverseSteps (k+1) (commandCode c n+1) b=programReverseSteps k n (commandCode c b+1) := by
 induction k using ISigma1.sigma1_succ_induction
 · definability
 case zero => simp only [programReverseSteps_succ,residualIter_zero,programReverseSteps_zero,reverseCommandStep_cons]
 case succ k ih =>
  rw [programReverseSteps_succ (k+1),←residualIter_commute,residualTail_code,ih,programReverseSteps_succ k]
lemma programReverseSteps_stable_add (n b j:M) : programReverseSteps (n+j) n b=programReverseSteps n n b := by
 induction j using ISigma1.sigma1_succ_induction
 · definability
 case zero => simp
 case succ j ih =>
  rw [←add_assoc,programReverseSteps_succ,residualIter_stops _ n (by simp),reverseCommandStep_zero,ih]
lemma programReverseSteps_stable {k n:M} (b:M) (h:n≤k) : programReverseSteps k n b=programReverseSteps n n b := by
 obtain ⟨j,hj⟩ := exists_add_of_le h
 rw [hj,programReverseSteps_stable_add]
lemma programReverseOnto_zero (b:M) : programReverseOnto 0 b=b := programReverseSteps_zero 0 b
lemma programReverseOnto_cons (c:Command M) (n b:M) :
 programReverseOnto (commandCode c n+1) b=programReverseOnto n (commandCode c b+1) := by
 have hn:n≤commandCode c n := commandCode_tail_le c n
 change programReverseSteps (commandCode c n+1) (commandCode c n+1) b=programReverseSteps n n (commandCode c b+1)
 rw [programReverseSteps_cons,programReverseSteps_stable _ hn]
attribute [irreducible] programReverseStepsGraph
end ZF207.ModelCommands
