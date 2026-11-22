module
public import ZF192Support.Execution.Commands.Compiler.Axiom
public import ZF192Support.Execution.Commands.Program.RebaseRun
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZF192Support.Internal (imp mem eqc all)
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem modelGen_compilable (i a:M) (h:compilable a) : compilable (all i a) := by
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
end ZF192Support.ModelCommands
