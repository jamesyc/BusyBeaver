module
public import ZF192Support.Execution.Registers.ProgramGraph
public import ZF192Support.Coding.Histories.General
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeSource
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def stateCode (s:State M) : M := modelCantor s.pc (modelCantor (s.registers 0) (modelCantor (s.registers 1) (modelCantor (s.registers 2) (modelCantor (s.registers 3) (modelCantor (s.registers 4) (modelCantor (s.registers 5) (modelCantor (s.registers 6) (modelCantor (s.registers 7) (s.registers 8)))))))))
lemma stateCode_injective {s t:State M} (he:stateCode s=stateCode t) : s=t := by
 unfold stateCode at he
 rcases modelCantor_injective he with ⟨hp,he⟩
 rcases modelCantor_injective he with ⟨h0,he⟩
 rcases modelCantor_injective he with ⟨h1,he⟩
 rcases modelCantor_injective he with ⟨h2,he⟩
 rcases modelCantor_injective he with ⟨h3,he⟩
 rcases modelCantor_injective he with ⟨h4,he⟩
 rcases modelCantor_injective he with ⟨h5,he⟩
 rcases modelCantor_injective he with ⟨h6,he⟩
 rcases modelCantor_injective he with ⟨h7,h8⟩
 have hr:s.registers=t.registers:=by
  funext j;rcases j with ⟨j,hj⟩
  have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8:=by omega
  rcases hh with hh|hh|hh|hh|hh|hh|hh|hh|hh <;> subst j <;> assumption
 cases s;cases t;cases hp;cases hr;rfl
def stateGraph : ArithmeticSemisentence 11 :=
 “code pc r0 r1 r2 r3 r4 r5 r6 r7 r8. ∃q0, ∃q1, ∃q2, ∃q3, ∃q4, ∃q5, ∃q6, ∃q7, !exactCantorGraph q0 r7 r8 ∧ !exactCantorGraph q1 r6 q0 ∧ !exactCantorGraph q2 r5 q1 ∧ !exactCantorGraph q3 r4 q2 ∧ !exactCantorGraph q4 r3 q3 ∧ !exactCantorGraph q5 r2 q4 ∧ !exactCantorGraph q6 r1 q5 ∧ !exactCantorGraph q7 r0 q6 ∧ !exactCantorGraph code pc q7”
lemma stateGraph_eval (code pc r0 r1 r2 r3 r4 r5 r6 r7 r8:M) : stateGraph.Evalb ![code,pc,r0,r1,r2,r3,r4,r5,r6,r7,r8] ↔ code=stateCode ⟨pc,![r0,r1,r2,r3,r4,r5,r6,r7,r8]⟩ := by
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b := graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 simp [stateGraph,stateCode,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,hc]
def codedStep (a b:M) : Prop := ∃s t:State M, a=stateCode s ∧ b=stateCode t ∧ programStep s t
noncomputable def nativeStepFormula : ArithmeticSemiformula Nat 2 :=
 “before after. ∃op, ∃ip, ∃a0, ∃a1, ∃a2, ∃a3, ∃a4, ∃a5, ∃a6, ∃a7, ∃a8, ∃b0, ∃b1, ∃b2, ∃b3, ∃b4, ∃b5, ∃b6, ∃b7, ∃b8, 
 !stateGraph before ip a0 a1 a2 a3 a4 a5 a6 a7 a8 ∧ !stateGraph after op b0 b1 b2 b3 b4 b5 b6 b7 b8 ∧
 !nativeProgramGraph op ip a0 a1 a2 a3 a4 a5 a6 a7 a8 b0 b1 b2 b3 b4 b5 b6 b7 b8”
lemma nativeGraph_vector (op ip a0 a1 a2 a3 a4 a5 a6 a7 a8 b0 b1 b2 b3 b4 b5 b6 b7 b8:M) : nativeProgramGraph.Evalb ![op,ip,a0,a1,a2,a3,a4,a5,a6,a7,a8,b0,b1,b2,b3,b4,b5,b6,b7,b8] ↔ programStep ⟨ip,![a0,a1,a2,a3,a4,a5,a6,a7,a8]⟩ ⟨op,![b0,b1,b2,b3,b4,b5,b6,b7,b8]⟩ := by
 rw [nativeProgramGraph_eval]
 have ho : (fun j=>![op,ip,a0,a1,a2,a3,a4,a5,a6,a7,a8,b0,b1,b2,b3,b4,b5,b6,b7,b8] (oldIndex j))=![a0,a1,a2,a3,a4,a5,a6,a7,a8] := by funext j; rcases j with ⟨j,hj⟩; have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := (by omega); rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> rfl
 have hn : (fun j=>![op,ip,a0,a1,a2,a3,a4,a5,a6,a7,a8,b0,b1,b2,b3,b4,b5,b6,b7,b8] (newIndex j))=![b0,b1,b2,b3,b4,b5,b6,b7,b8] := by funext j; rcases j with ⟨j,hj⟩; have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := (by omega); rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> rfl
 simp only [ho,hn,Matrix.cons_val_zero,Matrix.cons_val_one]
lemma nativeStepFormula_eval (ρ:Nat→M) (a b:M) : nativeStepFormula.Eval ![a,b] ρ ↔ codedStep a b := by
 simp [Matrix.constant_eq_singleton,nativeStepFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,stateGraph_eval,nativeGraph_vector]
 constructor
 · rintro ⟨op,ip,a0,a1,a2,a3,a4,a5,a6,a7,a8,ha,b0,b1,b2,b3,b4,b5,b6,b7,b8,hb,hr⟩
   exact ⟨⟨ip,![a0,a1,a2,a3,a4,a5,a6,a7,a8]⟩,⟨op,![b0,b1,b2,b3,b4,b5,b6,b7,b8]⟩,ha,hb,hr⟩
 · rintro ⟨s,t,ha,hb,hr⟩
   have hs:s.registers=![s.registers 0,s.registers 1,s.registers 2,s.registers 3,s.registers 4,s.registers 5,s.registers 6,s.registers 7,s.registers 8] := by funext j; rcases j with ⟨j,hj⟩; have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := (by omega); rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> rfl
   have ht:t.registers=![t.registers 0,t.registers 1,t.registers 2,t.registers 3,t.registers 4,t.registers 5,t.registers 6,t.registers 7,t.registers 8] := by funext j; rcases j with ⟨j,hj⟩; have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := (by omega); rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> rfl
   refine ⟨t.pc,s.pc,s.registers 0,s.registers 1,s.registers 2,s.registers 3,s.registers 4,s.registers 5,s.registers 6,s.registers 7,s.registers 8,?_,t.registers 0,t.registers 1,t.registers 2,t.registers 3,t.registers 4,t.registers 5,t.registers 6,t.registers 7,t.registers 8,?_,?_⟩
   · simpa only [←hs] using ha
   · simpa only [←ht] using hb
   · simpa only [←hs,←ht] using hr
end ZF192Support.NativeSource
