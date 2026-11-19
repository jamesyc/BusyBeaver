module
public import ModelListInduction
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelOperationalConcat
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def spliceFormula (φ ψ:ArithmeticSemiformula Nat 1)
 (app:𝚺ᴬ₁.Semisentence 3) : ArithmeticSemiformula Nat 1 :=
 “n. ∀ s, ∀ b, ∀ one, ∀ u, ∀ v,
 !listConsGraph one s 0 → !app u n one → !app v n b →
 (!φ u → !ψ b → b≠0 → !listHeadGraph s b → !ψ v)”
def SpliceProperty (F G:M→Prop) (n:M) : Prop := ∀s b,
 F (append n (modelListCons s 0)) → G b → b≠0 → modelListHead b=s → G (append n b)
lemma spliceFormula_eval (φ ψ:ArithmeticSemiformula Nat 1) (ρ:Nat→M) (F G:M→Prop)
 (hF:∀n,φ.Eval ![n] ρ ↔ F n) (hG:∀n,ψ.Eval ![n] ρ ↔ G n) (n:M) :
 (spliceFormula φ ψ appendGraph).Eval ![n] ρ ↔ SpliceProperty F G n := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [spliceFormula,SpliceProperty,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,hv,hF,hG,ruleCons_defined.iff,
 append_defined.iff,ruleHead_defined.iff,eq_comm]
 constructor
 · intro h s b; exact h s b _ _ _ rfl rfl rfl
 · intro h s b one u v hone hu hv
   subst one; subst u; subst v
   exact h s b
/-- Genuine model-sized substitution of a rooted history for a matching singleton.
Only the two history predicates need first-order definitions. The edge relation is
shared on nonempty tails; zero-tail roots can differ. -/
lemma history_splice (φ ψ:ArithmeticSemiformula Nat 1) (ρ:Nat→M) (F G:M→Prop)
 (hF:∀n,φ.Eval ![n] ρ ↔ F n) (hG:∀n,ψ.Eval ![n] ρ ↔ G n)
 (R:M→M→Prop)
 (fcons:∀a t,t≠0→(F (modelListCons a t) ↔ F t ∧ R (modelListHead t) a))
 (gcons:∀a t,t≠0→(G (modelListCons a t) ↔ G t ∧ R (modelListHead t) a)) :
 ∀n,SpliceProperty F G n := by
 apply model_list_induction (spliceFormula φ ψ appendGraph) ρ (SpliceProperty F G)
  (spliceFormula_eval φ ψ ρ F G hF hG)
 · intro s b _ hb _ _
   simpa only [append_zero] using hb
 · intro a t ih s b hf hb hb0 hhead
   rw [append_cons] at hf ⊢
   have ht0:=append_ne_zero_right t (cons_ne_zero s 0)
   have parts: F (append t (modelListCons s 0)) ∧
     R (modelListHead (append t (modelListCons s 0))) a := (fcons a _ ht0).mp hf
   apply (gcons a _ (append_ne_zero_right t hb0)).mpr
   refine ⟨ih s b parts.1 hb hb0 hhead,?_⟩
   have hh:modelListHead b=modelListHead (modelListCons s 0) := by
    simpa only [modelListHead_cons] using hhead
   rw [append_head_eq t b (modelListCons s 0) hh]
   exact parts.2
end ZF207.ModelOperationalConcat
