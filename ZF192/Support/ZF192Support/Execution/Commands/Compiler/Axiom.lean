module
public import ZF192Support.Execution.Commands.Program.MacroHistory
public import ZF192Support.Execution.Commands.Compiler.GateRhoSupply
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZF192Support.Internal (imp mem eqc all)
open ZF192Support.Halting (cAxiom cRule)
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem totalMacro_compilable (cs:List (Command M)) (n:M)
 (ht:∀t w:M,modelCommandsEval cs ⟨t,w,0,0⟩=some ⟨n,w,0,0⟩) : compilable n := by
 refine ⟨macroPointer cs 0,?_⟩
 intro t w
 let initial := cleanCfg (macroPointer cs 0) t w
 obtain ⟨out,hr,he⟩ := macro_history cs 0 ⟨t,w,0,0⟩ initial (modelListCons initial 0)
   (runHistory_singleton initial) (modelListHead_cons _ _)
 refine ⟨out,hr,Or.inr ?_⟩
 simpa only [ht t w,cleanCfg] using he
/-- Every exact C axiom, including nonstandard parameters, has a concrete
coded finite macro and an internally coded execution history. -/
theorem modelCAxiom_compilable (n:M) (h:cAxiom n) : compilable n := by
 obtain ⟨a,d,b,u,hn⟩ := h
 rcases hn with h0|h1|h2|h3|h4|h5|h6|hr|hg
 · subst n; exact totalMacro_compilable modelDISCARD 0 modelDISCARD_total
 · subst n; exact totalMacro_compilable (modelSupplyHead 1 a d b) _ (modelSupplyHead_total 0 a d b)
 · subst n; exact totalMacro_compilable (modelSupplyHead 2 a d b) _ (modelSupplyHead_total 1 a d b)
 · subst n; exact totalMacro_compilable (modelSupplyHead 3 a d b) _ (modelSupplyHead_total 2 a d b)
 · subst n; exact totalMacro_compilable (modelSupplyHead 4 a d b) _ (modelSupplyHead_total 3 a d b)
 · subst n; exact totalMacro_compilable (modelSupplyHead 5 a d b) _ (modelSupplyHead_total 4 a d b)
 · subst n; exact totalMacro_compilable (modelSupplyHead 6 a d b) _ (modelSupplyHead_total 5 a d b)
 · obtain ⟨hu,rfl⟩ := hr
   obtain ⟨offset, rfl⟩ := le_iff_exists_add.mp hu
   exact totalMacro_compilable (modelSupplyRho a offset b u) _ (modelSupplyRho_total a offset b u)
 · obtain ⟨had,hah,rfl⟩ := hg
   exact totalMacro_compilable (modelSupplyGate a d b) _ (fun t w=>modelSupplyGate_total a d b t w had hah)
end ZF192Support.ModelCommands
