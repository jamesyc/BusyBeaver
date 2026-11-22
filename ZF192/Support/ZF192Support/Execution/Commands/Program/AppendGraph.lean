module
public import ZF192Support.Execution.Commands.Program.Append
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def programReverseOntoGraph : 𝚺ᴬ₁.Semisentence 3 :=
 programReverseStepsGraph.rew (Rew.bind (L:=ℒₒᵣ) ![#0,#1,#1,#2] Empty.elim)
lemma programReverseOnto_defined : 𝚺ᴬ₁.DefinedFunction₂ (programReverseOnto (M:=M)) programReverseOntoGraph := .mk (by
 intro v
 simp [programReverseOntoGraph,programReverseOnto,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,programReverseSteps_defined.iff])

def programAppendGraphOf (φ : 𝚺ᴬ₁.Semisentence 3) : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z n b. ∃ r, !φ r n 0 ∧ !φ z r b”
def programAppendGraph : 𝚺ᴬ₁.Semisentence 3 := programAppendGraphOf programReverseOntoGraph
lemma programAppendGraphOf_eval (φ : 𝚺ᴬ₁.Semisentence 3) (f:M→M→M)
 (hf:𝚺ᴬ₁.DefinedFunction₂ f φ) (v:Fin 3→M) :
 (programAppendGraphOf φ).val.Evalb v ↔ v 0=f (f (v 1) 0) (v 2) := by
 simp [programAppendGraphOf,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,hf.iff]
lemma programAppend_defined : 𝚺ᴬ₁.DefinedFunction₂ (programAppend (M:=M)) programAppendGraph := .mk (by
 intro v
 exact programAppendGraphOf_eval _ _ programReverseOnto_defined v)
end ZF192Support.ModelCommands
