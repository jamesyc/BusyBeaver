module
public import ModelListAlgebra
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelOperationalConcat
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def mapBlueprint (φ:𝚺ᴬ₁.Semisentence 3) : PR.Blueprint 3 where
 zero := .mkSigma “z n b t. z=b”
 succ := .mkSigma “u z i n b t. ∃g, !tailIterationGraph g i n ∧
 ((g=0 ∧ u=z) ∨ (g≠0 ∧ ∃a, ∃fa, !listHeadGraph a g ∧ !φ fa a t ∧ !listConsGraph u fa z))”
noncomputable def mapConstruction (φ:𝚺ᴬ₁.Semisentence 3) (f:M→M→M)
 (hf:𝚺ᴬ₁.DefinedFunction₂ f φ) : PR.Construction M (mapBlueprint φ) where
 zero := fun v=>v 1
 succ := fun v i z=>if modelTailIter i (v 0)=0 then z else
  modelListCons (f (modelListHead (modelTailIter i (v 0))) (v 2)) z
 zero_defined := .mk (by intro v; simp [mapBlueprint])
 succ_defined := .mk (by
  intro v
  by_cases h:modelTailIter (v 2) (v 3)=0
  all_goals simp [mapBlueprint,Semiformula.eval_rew,Function.comp_def,
   Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,
   tailIterationGraph_defined.iff,ruleHead_defined.iff,ruleCons_defined.iff,hf.iff,h])
noncomputable def mapSteps (φ:𝚺ᴬ₁.Semisentence 3) (f:M→M→M)
 (hf:𝚺ᴬ₁.DefinedFunction₂ f φ) (k n b t:M) : M :=
 (mapConstruction φ f hf).result ![n,b,t] k
def mapStepsGraph (φ:𝚺ᴬ₁.Semisentence 3) : 𝚺ᴬ₁.Semisentence 5 := (mapBlueprint φ).resultDef
variable (φ:𝚺ᴬ₁.Semisentence 3) (f:M→M→M) (hf:𝚺ᴬ₁.DefinedFunction₂ f φ)
lemma mapSteps_defined : 𝚺ᴬ₁.DefinedFunction₄ (mapSteps φ f hf) (mapStepsGraph φ) := .mk (by
 intro v
 have hv:v=![v 0,v 1,v 2,v 3,v 4] := by
  funext i
  refine Fin.cases rfl (fun j=>?_) i
  refine Fin.cases rfl (fun j=>?_) j
  refine Fin.cases rfl (fun j=>?_) j
  refine Fin.cases rfl (fun j=>?_) j
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]
 exact (mapConstruction φ f hf).result_defined_iff _)
instance mapSteps_definable : 𝚺ᴬ₁-Function₄ (mapSteps φ f hf) := (mapSteps_defined φ f hf).to_definable
lemma mapSteps_zero (n b t:M) : mapSteps φ f hf 0 n b t=b := (mapConstruction φ f hf).result_zero _
lemma mapSteps_succ (k n b t:M) : mapSteps φ f hf (k+1) n b t=
 if modelTailIter k n=0 then mapSteps φ f hf k n b t else
 modelListCons (f (modelListHead (modelTailIter k n)) t) (mapSteps φ f hf k n b t) :=
 (mapConstruction φ f hf).result_succ _ k
lemma mapSteps_cons (k a n b t:M) :
 mapSteps φ f hf (k+1) (modelListCons a n) b t=mapSteps φ f hf k n (modelListCons (f a t) b) t := by
 haveI : 𝚺ᴬ₁-Function₂ f := hf.to_definable
 induction k using ISigma1.sigma1_succ_induction
 · definability
 case zero => simp only [mapSteps_succ,modelTailIter_zero,
   if_neg (cons_ne_zero a n),modelListHead_cons,mapSteps_zero]
 case succ k ih =>
  rw [mapSteps_succ φ f hf (k+1),←modelTailIter_commute,modelListTail_cons,ih,mapSteps_succ]
lemma mapSteps_stable_add (n b t j:M) : mapSteps φ f hf (n+j) n b t=mapSteps φ f hf n n b t := by
 induction j using ISigma1.sigma1_succ_induction
 · definability
 case zero => simp
 case succ j ih =>
  rw [←add_assoc,mapSteps_succ,if_pos (modelTailIter_stops _ n (by simp)),ih]
lemma mapSteps_stable {k n:M} (b t:M) (h:n≤k) : mapSteps φ f hf k n b t=mapSteps φ f hf n n b t := by
 obtain ⟨j,hj⟩ := exists_add_of_le h
 rw [hj,mapSteps_stable_add]
noncomputable def mapReverse (n b t:M) : M := mapSteps φ f hf n n b t
instance mapReverse_definable : 𝚺ᴬ₁-Function₃ (mapReverse φ f hf) := by
 unfold mapReverse
 definability
lemma mapReverse_zero (b t:M) : mapReverse φ f hf 0 b t=b := mapSteps_zero φ f hf 0 b t
lemma mapReverse_cons (a n b t:M) :
 mapReverse φ f hf (modelListCons a n) b t=mapReverse φ f hf n (modelListCons (f a t) b) t := by
 have hp:0<modelListCons a n := pos_iff_ne_zero.mpr (cons_ne_zero a n)
 obtain ⟨k,hk⟩ := eq_succ_of_pos hp
 have hn:n<modelListCons a n := by
  simpa only [modelListTail_cons] using modelListTail_lt (modelListCons a n) hp
 have hnk:n≤k := lt_succ_iff_le.mp (hk ▸ hn)
 change mapSteps φ f hf (modelListCons a n) (modelListCons a n) b t=mapSteps φ f hf n n (modelListCons (f a t) b) t
 nth_rw 1 [hk]
 rw [mapSteps_cons,mapSteps_stable φ f hf _ _ hnk]
attribute [irreducible] mapStepsGraph
end ZF207.ModelOperationalConcat
