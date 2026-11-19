module
public import ModelCCompilerInvariant
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def macroPointer : List (Command M) → M → M
 | [],tail => tail
 | c::cs,tail => commandCode c (macroPointer cs tail)+1
lemma command_failure_halt (c:Command M) (tail:M) (s:Store M)
 (h:modelCommandEval c s=none) : haltAt (commandCfgCode (commandCode c tail+1) s) := by
 cases c with
 | shift =>
   have hs : s.t+s.h=1 := by
    by_contra hn
    simp [modelCommandEval,hn] at h
   exact ⟨tail,s,rfl,hs⟩
 | mp x => simp only [modelCommandEval] at h; split at h <;> contradiction
 | ax a x y => simp [modelCommandEval] at h
/-- Actual internal history for a fixed finite macro, with arbitrary model
parameters and residual continuation. This is not a nonstandard-word compiler. -/
theorem macro_history (cs:List (Command M)) (tail:M) (s:Store M)
 (initial hist:M) (hr:runHistory initial hist)
 (hh:modelListHead hist=commandCfgCode (macroPointer cs tail) s) :
 ∃out:M,runHistory initial out ∧
 match modelCommandsEval cs s with
 | none => haltAt (modelListHead out)
 | some s' => modelListHead out=commandCfgCode tail s' := by
 induction cs generalizing s hist with
 | nil => exact ⟨hist,hr,hh⟩
 | cons c cs ih =>
   cases he:modelCommandEval c s with
   | none =>
     refine ⟨hist,hr,?_⟩
     simp only [modelCommandsEval,he,Option.bind_none]
     rw [hh]
     exact command_failure_halt c (macroPointer cs tail) s he
   | some s' =>
     have hs : codedCommandStep (modelListHead hist) (commandCfgCode (macroPointer cs tail) s') := by
      rw [hh]; exact codedCommandStep_of_eval c (macroPointer cs tail) s s' he
     have hnew := runHistory_extend hr hs
     have hhead : modelListHead (modelListCons (commandCfgCode (macroPointer cs tail) s') hist)=
       commandCfgCode (macroPointer cs tail) s' := modelListHead_cons _ _
     obtain ⟨out,ho,hend⟩ := ih s' _ hnew hhead
     exact ⟨out,ho,by simpa only [modelCommandsEval,he,Option.bind_some] using hend⟩
end ZF207.ModelCommands
