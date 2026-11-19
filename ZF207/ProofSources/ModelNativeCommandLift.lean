module
public import ModelNativeShiftCommand
public import ModelCommandTotality
public import ModelCommandHistoryDecompose
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeCommands
open ZF207.NativeSource ZF207.ModelCommands ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def liftState (n code:M) : State M :=
 commandState 25 n (modelUnpairLeft code) 0 (storeDecode (modelUnpairRight code))
lemma liftState_cfg (n pc:M) (s:Store M) :
 liftState n (commandCfgCode pc s)=commandState 25 n pc 0 s := by
 simp only [liftState,commandCfgCode,modelUnpairLeft_pair,modelUnpairRight_pair,storeDecode_code]
lemma cfg_decode (code:M) : commandCfgCode (modelUnpairLeft code) (storeDecode (modelUnpairRight code))=code := by
 simp only [commandCfgCode,storeCode,storeDecode,modelUnpair_reconstruct]
noncomputable def liftStateGraph : ArithmeticSemiformula Nat 3 :=
 “z n code. ∃pc, ∃t, ∃w, ∃d, ∃h,
 !cfgFormula code pc t w d h ∧ !stateGraph z 25 w pc t d 0 0 n h 0”
lemma liftStateGraph_eval (ρ:Nat→M) (z n code:M) :
 liftStateGraph.Eval ![z,n,code] ρ ↔ z=stateCode (liftState n code) := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [liftStateGraph,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,
 cfgFormula_eval,stateGraph_eval,numeral_eq_natCast]
 constructor
 · rintro ⟨pc,t,w,d,h,rfl,hz⟩
   simpa only [liftState_cfg,commandState] using hz
 · intro hz
   let s:=storeDecode (modelUnpairRight code)
   refine ⟨modelUnpairLeft code,s.t,s.w,s.d,s.h,?_,?_⟩
   · exact (cfg_decode code).symm
   · exact hz
/-- Explicit remaining native-body contract. SHIFT is already verified; MP/AX
must be supplied by their actual literal-program body proofs. -/
def successBodyContract : Prop := ∀(c:Command M) (n tail:M) (s out:Store M),
 modelCommandEval c s=some out → nativeReaches (bodyEntry c n tail s) (commandState 25 n tail 0 out)
lemma codedStep_native (hc:successBodyContract (M:=M)) (n:M) {before after:M}
 (hs:codedCommandStep before after) : nativeReaches (liftState n before) (liftState n after) := by
 obtain ⟨c,tail,s,out,rfl,rfl,he⟩:=hs
 rw [liftState_cfg,liftState_cfg]
 exact nativeReaches_trans (fetch_coded_command c n tail s) (hc c n tail s out he)
end ZF207.NativeCommands
