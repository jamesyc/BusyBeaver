module
public import ZF192Support.Coding.Lists.Append
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelOperationalConcat
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def reverseOntoGraph : 𝚺ᴬ₁.Semisentence 3 :=
 reverseStepsGraph.rew (Rew.bind (L:=ℒₒᵣ) ![#0,#1,#1,#2] Empty.elim)
lemma reverseOnto_defined : 𝚺ᴬ₁.DefinedFunction₂ (reverseOnto (M:=M)) reverseOntoGraph := .mk (by
 intro v
 simp [reverseOntoGraph,reverseOnto,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,reverseSteps_defined.iff])

def appendGraphOf (φ : 𝚺ᴬ₁.Semisentence 3) : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z n b. ∃ r, !φ r n 0 ∧ !φ z r b”
def appendGraph : 𝚺ᴬ₁.Semisentence 3 := appendGraphOf reverseOntoGraph
lemma appendGraphOf_eval (φ : 𝚺ᴬ₁.Semisentence 3) (f:M→M→M)
 (hf:𝚺ᴬ₁.DefinedFunction₂ f φ) (v:Fin 3→M) :
 (appendGraphOf φ).val.Evalb v ↔ v 0=f (f (v 1) 0) (v 2) := by
 simp [appendGraphOf,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,hf.iff]
lemma append_defined : 𝚺ᴬ₁.DefinedFunction₂ (append (M:=M)) appendGraph := .mk (by
 intro v
 exact appendGraphOf_eval _ _ reverseOnto_defined v)
end ZF192Support.ModelOperationalConcat
