module
public import ModelCAxiomCompilation
public import ModelProgramRebaseRun
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.ModelCommands
open ZFR.ArithmeticRepresentation ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem modelGen_compilable (i a:M) (h:compilable a) : compilable (t322 i a) := by
 obtain ⟨word,hw⟩ := h
 let tail:=macroPointer (modelGEN i) (0:M)
 refine ⟨programAppend word tail,?_⟩
 intro t w
 obtain ⟨hist,hr,ho⟩ := hw t w
 obtain ⟨hb,hend⟩ := rebase_run_result word tail ⟨t,w,0,0⟩ ⟨a,w,0,0⟩ hist hr ho
 rcases hend with hh|he
 · exact ⟨_,hb,Or.inl hh⟩
 · obtain ⟨out,hrun,hout⟩ := macro_history (modelGEN i) 0 ⟨a,w,0,0⟩ _ _ hb he
   exact ⟨out,hrun,Or.inr (by simpa only [modelGEN_total,cleanCfg] using hout)⟩
end ZF209.ModelCommands
