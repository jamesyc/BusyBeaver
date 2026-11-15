module
public import ModelNativeRun
public import ModelFormulaCertificates
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.AXFieldDSource
open ZF209.NativeSource ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano M209.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def restoreXState (ρ:Nat→M) (pc y x:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,ρ 1,ρ 2,x,ρ 4,ρ 5,ρ 6,ρ 7,y]⟩
def restoreXTerminates (ρ:Nat→M) (y:M) : Prop := ∀x initial hist:M,
 nativeRunHistory initial hist → modelListHead hist=stateCode (restoreXState ρ 235 y x) →
 ∃out:M,nativeRunHistory initial out ∧ modelListHead out=stateCode (restoreXState ρ 238 0 (x+y))
noncomputable def restoreXFormula : ArithmeticSemiformula Nat 1 :=
 “y. ∀x, ∀initial, ∀hist, ∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧
 !stateGraph head 235 &0 &1 &2 x &4 &5 &6 &7 y) →
 ∃out, ∃last, !nativeRunFormula initial out ∧ !listHeadGraph last out ∧
 !stateGraph last 238 &0 &1 &2 (x+y) &4 &5 &6 &7 0”
lemma restoreXFormula_eval (ρ:Nat→M) (y:M) : restoreXFormula.Eval ![y] ρ ↔ restoreXTerminates ρ y := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [restoreXFormula,restoreXTerminates,restoreXState,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,nativeRunFormula_eval,ruleHead_defined.iff,stateGraph_eval,numeral_eq_natCast]
noncomputable def restoreX_certificate (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>restoreXTerminates ρ (v 0)) := by
 refine ⟨restoreXFormula,?_⟩
 intro v
 have hv:v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv]; exact (restoreXFormula_eval ρ (v 0)).symm
private lemma extend_from {initial hist:M} (s t:State M) (hr:nativeRunHistory initial hist)
 (hh:modelListHead hist=stateCode s) (hs:programStep s t) :
 nativeRunHistory initial (modelListCons (stateCode t) hist) := by
 apply nativeRunHistory_extend hr
 rw [hh]; exact ⟨s,t,rfl,rfl,hs⟩
private lemma step_zero (ρ:Nat→M) (x:M) : programStep (restoreXState ρ 235 0 x) (restoreXState ρ 238 0 x) := by
 refine ⟨235,by decide,by simp [restoreXState],.dec 8 238 236,by decide,?_⟩
 simp [NativeSource.execute,restoreXState,registerIndex]
private lemma step_dec (ρ:Nat→M) (y x:M) : programStep (restoreXState ρ 235 (y+1) x) (restoreXState ρ 236 y x) := by
 refine ⟨235,by decide,by simp [restoreXState],.dec 8 238 236,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (restoreXState ρ 235 (y+1) x).registers (registerIndex 8)≠0 from by change y+1≠0; simp)]
 change some ⟨(236:M),fun j=>if j.val=8 then modelPredecessor ((restoreXState ρ 235 (y+1) x).registers j) else (restoreXState ρ 235 (y+1) x).registers j⟩=some (restoreXState ρ 236 y x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [restoreXState,modelPredecessor_succ]
private lemma step_inc (ρ:Nat→M) (y x:M) : programStep (restoreXState ρ 236 y x) (restoreXState ρ 237 y (x+1)) := by
 refine ⟨236,by decide,by simp [restoreXState],.inc 3 237,by decide,?_⟩
 simp only [NativeSource.execute,restoreXState]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp
private lemma step_jump (ρ:Nat→M) (y x:M) : programStep (restoreXState ρ 237 y x) (restoreXState ρ 235 y x) := by
 refine ⟨237,by decide,by simp [restoreXState],.jump 235,by decide,?_⟩
 simp [NativeSource.execute,restoreXState]
theorem restoreX_terminates (ρ:Nat→M) : ∀y:M,restoreXTerminates ρ y := by
 apply (restoreX_certificate ρ).induction
 · intro x initial hist hr hh
   refine ⟨modelListCons (stateCode (restoreXState ρ 238 0 x)) hist,extend_from _ _ hr hh (step_zero ρ x),?_⟩
   simp [modelListHead_cons]
 · intro y ih x initial hist hr hh
   have h1:=extend_from _ _ hr hh (step_dec ρ y x)
   have h2:=extend_from _ _ h1 (modelListHead_cons _ _) (step_inc ρ y x)
   have h3:=extend_from _ _ h2 (modelListHead_cons _ _) (step_jump ρ y (x+1))
   obtain ⟨out,ho,he⟩:=ih (x+1) initial _ h3 (modelListHead_cons _ _)
   refine ⟨out,ho,?_⟩
   simpa [add_assoc,add_comm,add_left_comm] using he
end ZF209.AXFieldDSource
