module
public import ModelGeneralHistory
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.ModelOperationalConcat
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def reverseBlueprint : PR.Blueprint 2 where
 zero := .mkSigma “z n b. z=b”
 succ := .mkSigma “u z i n b. ∃ g, !tailIterationGraph g i n ∧
   ((g=0 ∧ u=z) ∨ (g≠0 ∧ ∃ a, !listHeadGraph a g ∧ !listConsGraph u a z))”

noncomputable def reverseConstruction : PR.Construction M reverseBlueprint where
 zero := fun v => v 1
 succ := fun v i z => if modelTailIter i (v 0)=0 then z
   else modelListCons (modelListHead (modelTailIter i (v 0))) z
 zero_defined := .mk (by intro v; simp [reverseBlueprint])
 succ_defined := .mk (by
  intro v
  by_cases h:modelTailIter (v 2) (v 3)=0
  all_goals simp [reverseBlueprint,Semiformula.eval_rew,Function.comp_def,
   Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,
   tailIterationGraph_defined.iff,ruleHead_defined.iff,ruleCons_defined.iff,h])

noncomputable def reverseSteps (k n b:M) : M := reverseConstruction.result ![n,b] k

def reverseStepsGraph : 𝚺ᴬ₁.Semisentence 4 := reverseBlueprint.resultDef
lemma reverseSteps_defined : 𝚺ᴬ₁.DefinedFunction₃ (reverseSteps (M:=M)) reverseStepsGraph := .mk (by
 intro v
 have hv:v=![v 0,v 1,v 2,v 3] := by
  funext i
  refine Fin.cases rfl (fun j=>?_) i
  refine Fin.cases rfl (fun j=>?_) j
  refine Fin.cases rfl (fun j=>?_) j
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]
 exact reverseConstruction.result_defined_iff _)
instance reverseSteps_definable : 𝚺ᴬ₁-Function₃ (reverseSteps (M:=M)) := reverseSteps_defined.to_definable
lemma reverseSteps_zero (n b:M) : reverseSteps 0 n b=b := reverseConstruction.result_zero ![n,b]
lemma reverseSteps_succ (k n b:M) : reverseSteps (k+1) n b=
 if modelTailIter k n=0 then reverseSteps k n b
 else modelListCons (modelListHead (modelTailIter k n)) (reverseSteps k n b) :=
 reverseConstruction.result_succ ![n,b] k

noncomputable def reverseOnto (n b:M) : M := reverseSteps n n b
instance cons_definable : 𝚺ᴬ₁-Function₂ (modelListCons (M:=M)) := ruleCons_defined.to_definable
instance head_definable : 𝚺ᴬ₁-Function₁ (modelListHead (M:=M)) := ruleHead_defined.to_definable
lemma cons_ne_zero (a b:M) : modelListCons a b≠0 := by
 exact ne_of_gt (by dsimp [modelListCons]; simp)
lemma reverseSteps_cons (k a n b:M) :
 reverseSteps (k+1) (modelListCons a n) b=reverseSteps k n (modelListCons a b) := by
 induction k using ISigma1.sigma1_succ_induction
 · definability
 case zero => simp only [reverseSteps_succ,modelTailIter_zero,
   if_neg (cons_ne_zero a n),modelListHead_cons,reverseSteps_zero]
 case succ k ih =>
  rw [reverseSteps_succ (k+1),←modelTailIter_commute,modelListTail_cons,ih,
    reverseSteps_succ k]
lemma reverseSteps_stable_add (n b j:M) : reverseSteps (n+j) n b=reverseSteps n n b := by
 induction j using ISigma1.sigma1_succ_induction
 · definability
 case zero => simp
 case succ j ih =>
  rw [←add_assoc,reverseSteps_succ,if_pos (modelTailIter_stops _ n (by simp)),ih]
lemma reverseSteps_stable {k n:M} (b:M) (h:n≤k) : reverseSteps k n b=reverseSteps n n b := by
 obtain ⟨j,hj⟩ := exists_add_of_le h
 rw [hj,reverseSteps_stable_add]
lemma reverseOnto_zero (b:M) : reverseOnto 0 b=b := reverseSteps_zero 0 b
lemma reverseOnto_cons (a n b:M) :
 reverseOnto (modelListCons a n) b=reverseOnto n (modelListCons a b) := by
 have hp:0<modelListCons a n := pos_iff_ne_zero.mpr (cons_ne_zero a n)
 obtain ⟨k,hk⟩ := eq_succ_of_pos hp
 have hn:n<modelListCons a n := by
  simpa only [modelListTail_cons] using modelListTail_lt (modelListCons a n) hp
 have hnk:n≤k := lt_succ_iff_le.mp (hk ▸ hn)
 change reverseSteps (modelListCons a n) (modelListCons a n) b=reverseSteps n n (modelListCons a b)
 nth_rw 1 [hk]
 rw [reverseSteps_cons,reverseSteps_stable _ hnk]
attribute [irreducible] reverseStepsGraph
end ZF209.ModelOperationalConcat
