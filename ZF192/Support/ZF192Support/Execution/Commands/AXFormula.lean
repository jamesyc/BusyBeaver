module
public import ZF192Support.Execution.Commands.Program.PushFormula
public import ZF192Support.Calculus.Internal.TraceRules
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZF192Support.Halting ZFR.ArithmeticRepresentation
open ZF192Support.Internal (allDef)
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Graph of the AX command, in the same arithmetic codes as the compiler. -/
def axGraph : 𝚺ᴬ₁.Semisentence 11 := .mkSigma
  “a x y t w d h u v dd hh. ∃d1, ∃h1, d1=d+x ∧ h1=h+y ∧ dd=0 ∧ hh=0 ∧
    ((a≠d1 ∧ a≠h1 ∧ !bundleDef u h1 d1 a) ∨ ((a=d1 ∨ a=h1) ∧ u=0)) ∧
    ∃q1, ∃q2, ∃q3, ∃q4, ∃q5, ∃q6, ∃q7, ∃q8,
    !head6Def q1 d1 a h1 ∧ !head5Def q2 d1 h1 ∧ !head4Def q3 h1 d1 a ∧
    !head3Def q4 h1 d1 a ∧ !head2Def q5 d1 a h1 ∧ !head1Def q6 d1 h1 ∧
    !rho8Def q7 d1 a h1 d ∧ !allDef q8 d h ∧
    ∃s0, ∃s1, ∃s2, ∃s3, ∃s4, ∃s5, ∃s6, ∃s7,
    !exactCantorGraph s0 t w ∧ !exactCantorGraph s1 q8 s0 ∧
    !exactCantorGraph s2 q7 s1 ∧ !exactCantorGraph s3 q6 s2 ∧
    !exactCantorGraph s4 q5 s3 ∧ !exactCantorGraph s5 q4 s4 ∧
    !exactCantorGraph s6 q3 s5 ∧ !exactCantorGraph s7 q2 s6 ∧ !exactCantorGraph v q1 s7”

def fixedAXFormula : ArithmeticSemiformula Nat 11 :=
  Rew.rewriteMap (Empty.elim : Empty → Nat) ▹ axGraph.val

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma fixedAXFormula_eval (ρ : Nat → M) (a x y t w d h u v dd hh : M) :
    fixedAXFormula.Eval ![a,x,y,t,w,d,h,u,v,dd,hh] ρ ↔
    modelCommandEval (.ax a x y) ⟨t,w,d,h⟩ = some ⟨u,v,dd,hh⟩ := by
 have pair (z a b : M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z = modelCantor a b :=
   graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 rw [fixedAXFormula, Semiformula.eval_rewriteMap]
 change axGraph.val.Evalb ![a,x,y,t,w,d,h,u,v,dd,hh] ↔ _
 simp [axGraph, head6Def_iff, head5Def_iff, head4Def_iff, head3Def_iff,
   head2Def_iff, head1Def_iff, bundleDef_iff, pair, exists_eq_left]
 simp [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton, rho8Def_iff]
 by_cases hg:a≠d+x ∧ a≠h+y
 · simp [modelCommandEval,gate,heads,implicationHeads,CKernel.Generic.Codes.axImplicationHeads,axHead6,axHead5,axHead4,axHead3,axHead2,axHead1,axRho8,axGate,hg,eq_comm,and_assoc,and_comm,and_left_comm]
 · have hn : a=d+x ∨ a=h+y := by tauto
   rcases hn with hn|hn <;> simp [modelCommandEval,gate,heads,implicationHeads,CKernel.Generic.Codes.axImplicationHeads,axHead6,axHead5,axHead4,axHead3,axHead2,axHead1,axRho8,hg,hn,eq_comm,and_assoc,and_comm,and_left_comm]
end ZF192Support.ModelCommands
