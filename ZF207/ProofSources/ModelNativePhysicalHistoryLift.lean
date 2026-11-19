module
public import ModelNativeRun
public import ModelPhysicalHistory
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativePhysicalLift
open ZFR.ArithmeticRepresentation ZF207.NativeSource ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Relation is on coded native/physical states. Its physical witness can carry
changing gap/spare values, not a fixed hidden resource invariant. -/
def StepContract (R:M→M→Prop) : Prop := ∀a b p:M,codedStep a b→R a p→
 ∀root hist:M,BinaryTape.runHistory root hist→modelListHead hist=p→
 ∃out q:M,BinaryTape.runHistory root out ∧ modelListHead out=q ∧ R b q
def Simulation (R:M→M→Prop) (initial code:M) : Prop := nativeRunHistory initial code→
 ∀root hist p:M,BinaryTape.runHistory root hist→modelListHead hist=p→R initial p→
 ∃out q:M,BinaryTape.runHistory root out ∧ modelListHead out=q ∧ R (modelListHead code) q
noncomputable def simulationFormula (relation:ArithmeticSemisentence 2) : ArithmeticSemiformula Nat 1 :=
 “code. !nativeRunFormula &0 code → ∀root, ∀hist, ∀p,
 (!BinaryTape.physicalRunFormula root hist ∧ !listHeadGraph p hist ∧ !relation &0 p) →
 ∃out, ∃q, ∃last, !BinaryTape.physicalRunFormula root out ∧ !listHeadGraph q out ∧
 !listHeadGraph last code ∧ !relation last q”
lemma simulationFormula_eval (relation:ArithmeticSemisentence 2) (R:M→M→Prop)
 (hr:∀a b,relation.Evalb ![a,b]↔R a b) (ρ:Nat→M) (code:M) :
 (simulationFormula relation).Eval ![code] ρ ↔ Simulation R (ρ 0) code := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [simulationFormula,Simulation,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,nativeRunFormula_eval,
 BinaryTape.physicalRunFormula_eval,ruleHead_defined.iff,hr,eq_comm]
noncomputable def simulation_certificate (relation:ArithmeticSemisentence 2) (R:M→M→Prop)
 (hr:∀a b,relation.Evalb ![a,b]↔R a b) (initial:M) :
 FormulaCertificate (fun _=>initial) 1 (fun v=>Simulation R initial (v 0)) := by
 refine ⟨simulationFormula relation,?_⟩
 intro v
 have hv:v=![v 0]:=by funext i; have hi:i=0:=Subsingleton.elim _ _;subst i;rfl
 rw [hv];exact (simulationFormula_eval relation R hr (fun _=>initial) (v 0)).symm
/-- Genuine PA induction over internal native histories. Both definability and
one-native-step simulation are explicit, and must be instantiated before use. -/
theorem native_history_lift (relation:ArithmeticSemisentence 2) (R:M→M→Prop)
 (hr:∀a b,relation.Evalb ![a,b]↔R a b) (hs:StepContract R) (initial:M) :
 ∀code:M,Simulation R initial code := by
 apply (simulation_certificate relation R hr initial).orderInduction
 intro code ih
 change Simulation R initial code
 intro hn root hist p hhist hhead hrel
 have hp:0<code:=pos_iff_ne_zero.mpr hn.1
 have ht:=modelListTail_lt code hp
 have he:code=modelListCons (modelListHead code) (modelListTail code):=(modelList_reconstruct code hp).symm
 have edge:=hn.2
 rw [he,modelTrace_cons] at edge
 by_cases hz:modelListTail code=0
 · have ha:modelListHead code=initial:=by simpa [nativeRunEdge,hz] using edge.2
   exact ⟨hist,p,hhist,hhead,ha.symm ▸ hrel⟩
 · have prev:nativeRunHistory initial (modelListTail code):=⟨hz,edge.1⟩
   have step:codedStep (modelListHead (modelListTail code)) (modelListHead code):=by
    simpa [nativeRunEdge,hz] using edge.2
   obtain ⟨mid,q,hm,hq,hrq⟩:=ih _ ht prev root hist p hhist hhead hrel
   exact hs _ _ q step hrq root mid hm hq
end ZF207.NativePhysicalLift
