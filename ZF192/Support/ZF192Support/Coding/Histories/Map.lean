module
public import ZF192Support.Coding.Lists.MapGraph
public import ZF192Support.Coding.Histories.Splice
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelOperationalConcat
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def mapPreservesFormula (φ ψ:ArithmeticSemiformula Nat 1) (mg:𝚺ᴬ₁.Semisentence 3) :
 ArithmeticSemiformula Nat 1 := “n. ∀m, !mg m n &2 → (!φ n → !ψ m)”
lemma mapPreservesFormula_eval (φ ψ:ArithmeticSemiformula Nat 1) (γ:𝚺ᴬ₁.Semisentence 3)
 (f:M→M→M) (hf:𝚺ᴬ₁.DefinedFunction₂ f γ) (ρ:Nat→M) (F G:M→Prop)
 (hF:∀n,φ.Eval ![n] ρ ↔ F n) (hG:∀n,ψ.Eval ![n] ρ ↔ G n) (n:M) :
 (mapPreservesFormula φ ψ (mapGraph γ)).Eval ![n] ρ ↔ (F n→G (map γ f hf n (ρ 2))) := by
 simp [mapPreservesFormula,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,Matrix.constant_eq_singleton,hF,hG,(map_defined γ f hf).iff]
/-- Transport every internally coded rooted history through an actual Sigma1-coded
map. Both history predicates have explicit first-order definitions; no bound on
history length is assumed. The map retains a model-valued parameter. -/
lemma history_map (φ ψ:ArithmeticSemiformula Nat 1) (γ:𝚺ᴬ₁.Semisentence 3)
 (f:M→M→M) (hf:𝚺ᴬ₁.DefinedFunction₂ f γ) (ρ:Nat→M) (F G:M→Prop)
 (hF:∀n,φ.Eval ![n] ρ ↔ F n) (hG:∀n,ψ.Eval ![n] ρ ↔ G n)
 (R S:M→M→Prop) (t:M) (ht:ρ 2=t) (zero:¬F 0)
 (single:∀a,F (modelListCons a 0)→G (modelListCons (f a t) 0))
 (fcons:∀a b,b≠0→(F (modelListCons a b) ↔ F b ∧ R (modelListHead b) a))
 (gcons:∀a b,b≠0→(G (modelListCons a b) ↔ G b ∧ S (modelListHead b) a))
 (step:∀a b,R a b→S (f a t) (f b t)) :
 ∀n,F n→G (map γ f hf n t) := by
 apply model_list_induction (mapPreservesFormula φ ψ (mapGraph γ)) ρ
  (fun n=>F n→G (map γ f hf n t))
  (by intro n; simpa only [ht] using mapPreservesFormula_eval φ ψ γ f hf ρ F G hF hG n)
 · intro h; exact False.elim (zero h)
 · intro a b ih hab
   rw [map_cons]
   by_cases hb:b=0
   · subst b; rw [map_zero]; exact single a hab
   · have parts: F b ∧ R (modelListHead b) a := (fcons a b hb).mp hab
     apply (gcons _ _ (map_ne_zero γ f hf t hb)).mpr
     refine ⟨ih parts.1,?_⟩
     rw [map_head γ f hf t hb]
     exact step _ _ parts.2
end ZF192Support.ModelOperationalConcat
