module
public import ModelCGenCompilation
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelCommands
open ZFR.ArithmeticRepresentation ZF207.MM0ModelReplay ModelOperationalConcat
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma push_eval (t w d h:M) : modelCommandsEval modelPUSH ⟨t,w,d,h⟩=
 some ⟨0,modelCantor t w,0,0⟩ := modelPUSH_total t w d h
lemma push_mptail_eval (a b w:M) :
 modelCommandsEval (modelPUSH++modelMPtail b) ⟨a,modelCantor (t299 a b) w,0,0⟩=none ∨
 modelCommandsEval (modelPUSH++modelMPtail b) ⟨a,modelCantor (t299 a b) w,0,0⟩=some ⟨b,w,0,0⟩ := by
 simpa only [modelCommandsEval_append,push_eval,Option.bind_some] using modelMPtail_result a b w
theorem modelMP_compilable (a b:M) (ha:compilable a) (hi:compilable (t299 a b)) : compilable b := by
 obtain ⟨aword,haw⟩ := ha
 obtain ⟨iword,hiw⟩ := hi
 let finish:=macroPointer (modelPUSH++modelMPtail b) (0:M)
 let operand:=programAppend aword finish
 let afterImp:=macroPointer modelPUSH operand
 refine ⟨programAppend iword afterImp,?_⟩
 intro t w
 obtain ⟨ihist,hir,hio⟩ := hiw t w
 obtain ⟨hreb,hend⟩ := rebase_run_result iword afterImp ⟨t,w,0,0⟩ ⟨t299 a b,w,0,0⟩ ihist hir hio
 rcases hend with hhalt|hiend
 · exact ⟨_,hreb,Or.inl hhalt⟩
 · obtain ⟨phist,hpr,hpo⟩ := macro_history modelPUSH operand ⟨t299 a b,w,0,0⟩ _ _ hreb hiend
   have hphead:modelListHead phist=commandCfgCode operand ⟨0,modelCantor (t299 a b) w,0,0⟩ := by
    simpa only [push_eval] using hpo
   obtain ⟨ahist,har,hao⟩ := haw 0 (modelCantor (t299 a b) w)
   obtain ⟨hareb,haend⟩ := rebase_run_result aword finish ⟨0,modelCantor (t299 a b) w,0,0⟩
     ⟨a,modelCantor (t299 a b) w,0,0⟩ ahist har hao
   obtain ⟨joined,hjr,hjh⟩ := command_history_concat _ _ _ phist hareb hpr hphead
   rcases haend with hh|he
   · exact ⟨joined,hjr,Or.inl (by rw [hjh];exact hh)⟩
   · have hjhead:modelListHead joined=commandCfgCode finish ⟨a,modelCantor (t299 a b) w,0,0⟩ := hjh.trans he
     obtain ⟨out,hrun,hout⟩ := macro_history (modelPUSH++modelMPtail b) 0
       ⟨a,modelCantor (t299 a b) w,0,0⟩ _ _ hjr hjhead
     refine ⟨out,hrun,?_⟩
     rcases push_mptail_eval a b w with hf|hf
     · exact Or.inl (by simpa only [hf] using hout)
     · exact Or.inr (by simpa only [hf,cleanCfg] using hout)
end ZF207.ModelCommands
