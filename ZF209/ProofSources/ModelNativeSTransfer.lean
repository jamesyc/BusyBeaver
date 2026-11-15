module
public import ModelNativeRun
public import ModelFormulaCertificates
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeSTransfer
open ZF209.NativeSource ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano M209.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def transferState (ρ:Nat→M) (pc y x:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,ρ 1,y,ρ 3,ρ 4,ρ 5,ρ 6,ρ 7,x]⟩
def transferTerminates (ρ:Nat→M) (y:M) : Prop := ∀x initial hist:M,
 nativeRunHistory initial hist → modelListHead hist=stateCode (transferState ρ 4329 y x) →
 ∃out:M,nativeRunHistory initial out ∧ modelListHead out=stateCode (transferState ρ 4332 0 (x+y))
noncomputable def transferFormula : ArithmeticSemiformula Nat 1 :=
 “y. ∀x, ∀initial, ∀hist, ∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧
 !stateGraph head 4329 &0 &1 y &3 &4 &5 &6 &7 x) →
 ∃out, ∃last, !nativeRunFormula initial out ∧ !listHeadGraph last out ∧
 !stateGraph last 4332 &0 &1 0 &3 &4 &5 &6 &7 (x+y)”
lemma transferFormula_eval (ρ:Nat→M) (y:M) : transferFormula.Eval ![y] ρ ↔ transferTerminates ρ y := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [transferFormula,transferTerminates,transferState,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,nativeRunFormula_eval,ruleHead_defined.iff,stateGraph_eval,numeral_eq_natCast]
noncomputable def transfer_certificate (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>transferTerminates ρ (v 0)) := by
 refine ⟨transferFormula,?_⟩
 intro v
 have hv:v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv]; exact (transferFormula_eval ρ (v 0)).symm
private lemma extend_from {initial hist:M} (s t:State M) (hr:nativeRunHistory initial hist)
 (hh:modelListHead hist=stateCode s) (hs:programStep s t) :
 nativeRunHistory initial (modelListCons (stateCode t) hist) := by
 apply nativeRunHistory_extend hr
 rw [hh]; exact ⟨s,t,rfl,rfl,hs⟩
private lemma step_zero (ρ:Nat→M) (x:M) : programStep (transferState ρ 4329 0 x) (transferState ρ 4332 0 x) := by
 refine ⟨4329,by decide,by simp [transferState],.dec 2 4332 4330,by decide,?_⟩
 simp [NativeSource.execute,transferState,registerIndex]
private lemma step_dec (ρ:Nat→M) (y x:M) : programStep (transferState ρ 4329 (y+1) x) (transferState ρ 4330 y x) := by
 refine ⟨4329,by decide,by simp [transferState],.dec 2 4332 4330,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (transferState ρ 4329 (y+1) x).registers (registerIndex 2)≠0 from by change y+1≠0; simp)]
 change some ⟨(4330:M),fun j=>if j.val=2 then modelPredecessor ((transferState ρ 4329 (y+1) x).registers j) else (transferState ρ 4329 (y+1) x).registers j⟩=some (transferState ρ 4330 y x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [transferState,modelPredecessor_succ]
private lemma step_inc (ρ:Nat→M) (y x:M) : programStep (transferState ρ 4330 y x) (transferState ρ 4331 y (x+1)) := by
 refine ⟨4330,by decide,by simp [transferState],.inc 8 4331,by decide,?_⟩
 simp only [NativeSource.execute,transferState]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp
private lemma step_jump (ρ:Nat→M) (y x:M) : programStep (transferState ρ 4331 y x) (transferState ρ 4329 y x) := by
 refine ⟨4331,by decide,by simp [transferState],.jump 4329,by decide,?_⟩
 simp [NativeSource.execute,transferState]
theorem transfer_terminates (ρ:Nat→M) : ∀y:M,transferTerminates ρ y := by
 apply (transfer_certificate ρ).induction
 · intro x initial hist hr hh
   refine ⟨modelListCons (stateCode (transferState ρ 4332 0 x)) hist,extend_from _ _ hr hh (step_zero ρ x),?_⟩
   simp [modelListHead_cons]
 · intro y ih x initial hist hr hh
   have h1:=extend_from _ _ hr hh (step_dec ρ y x)
   have h2:=extend_from _ _ h1 (modelListHead_cons _ _) (step_inc ρ y x)
   have h3:=extend_from _ _ h2 (modelListHead_cons _ _) (step_jump ρ y (x+1))
   obtain ⟨out,ho,he⟩:=ih (x+1) initial _ h3 (modelListHead_cons _ _)
   refine ⟨out,ho,?_⟩
   simpa [add_assoc,add_comm,add_left_comm] using he
end ZF209.NativeSTransfer
