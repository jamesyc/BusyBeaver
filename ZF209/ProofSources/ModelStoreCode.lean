module
public import ModelMPFormula
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def storeCode (s:Store M) : M := modelCantor s.t (modelCantor s.w (modelCantor s.d s.h))
noncomputable def storeDecode (n:M) : Store M :=
 ⟨modelUnpairLeft n,modelUnpairLeft (modelUnpairRight n),
 modelUnpairLeft (modelUnpairRight (modelUnpairRight n)),
 modelUnpairRight (modelUnpairRight (modelUnpairRight n))⟩
lemma storeDecode_code (s:Store M) : storeDecode (storeCode s)=s := by
 cases s
 simp [storeDecode,storeCode,modelUnpairLeft_pair,modelUnpairRight_pair]
lemma storeCode_injective : Function.Injective (storeCode (M:=M)) := by
 intro a b h
 have hh:=congrArg storeDecode h
 simpa only [storeDecode_code] using hh
/-- Output code followed by the four store fields. -/
def storeGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
 “z t w d h. ∃q, ∃r, !exactCantorGraph q d h ∧ !exactCantorGraph r w q ∧ !exactCantorGraph z t r”
lemma storeGraph_eval (z t w d h:M) : storeGraph.val.Evalb ![z,t,w,d,h] ↔ z=storeCode ⟨t,w,d,h⟩ := by
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b :=
  graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 simp [storeGraph,storeCode,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
 Matrix.comp_vecCons',Matrix.empty_eq,hc]
end ZF209.ModelCommands
