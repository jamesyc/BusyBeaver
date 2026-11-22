module
public import ZF192Support.Execution.Commands.History
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Replace exactly the parsed command's continuation, without changing its fields. -/
noncomputable def retargetCommand (n tail:M) : M :=
 let a:=modelUnpairLeft n
 let b:=modelUnpairRight n
 if a=0 then modelCantor 0 tail
 else if a=1 then modelCantor 1 (modelCantor (modelUnpairLeft b) tail)
 else modelCantor a (modelCantor (modelUnpairLeft b)
  (modelCantor (modelUnpairLeft (modelUnpairRight b)) tail))
lemma retargetCommand_code (c:Command M) (old tail:M) :
 retargetCommand (commandCode c old) tail=commandCode c tail := by
 cases c with
 | shift => simp [retargetCommand,commandCode,modelUnpairLeft_pair,modelUnpairRight_pair]
 | mp x => simp [retargetCommand,commandCode,modelUnpairLeft_pair,modelUnpairRight_pair]
 | ax a x y =>
   have h0 : a+2≠(0:M) := ne_of_gt (lt_of_lt_of_le (by norm_num : (0:M)<2) (le_add_self))
   have h1 : a+2≠(1:M) := ne_of_gt (lt_of_lt_of_le (by norm_num : (1:M)<2) (le_add_self))
   simp [retargetCommand,commandCode,modelUnpairLeft_pair,modelUnpairRight_pair,h0,h1]
def retargetGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z n tail. ∃a, ∃b, !unpairLeftGraph a n ∧ !unpairRightGraph b n ∧
 ((a=0 ∧ !exactCantorGraph z 0 tail) ∨
 (a=1 ∧ ∃x, ∃q, !unpairLeftGraph x b ∧ !exactCantorGraph q x tail ∧ !exactCantorGraph z 1 q) ∨
 (a≠0 ∧ a≠1 ∧ ∃y, ∃r, ∃x, ∃q, ∃s,
 !unpairLeftGraph y b ∧ !unpairRightGraph r b ∧ !unpairLeftGraph x r ∧
 !exactCantorGraph q x tail ∧ !exactCantorGraph s y q ∧ !exactCantorGraph z a s))”
lemma retargetGraph_eval (z n tail:M) : retargetGraph.val.Evalb ![z,n,tail] ↔ z=retargetCommand n tail := by
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b :=
  graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 have hl (z n:M) : unpairLeftGraph.val.Evalb ![z,n] ↔ z=modelUnpairLeft n :=
  graphValue_spec unpairLeftGraph unpairLeftGraph_total z ![n]
 have hr (z n:M) : unpairRightGraph.val.Evalb ![z,n] ↔ z=modelUnpairRight n :=
  graphValue_spec unpairRightGraph unpairRightGraph_total z ![n]
 simp [retargetGraph,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton,
 Empty.eq_elim,hc,hl,hr]
 by_cases h0:modelUnpairLeft n=0
 · simp [retargetCommand,h0]
 · by_cases h1:modelUnpairLeft n=1
   · simp [retargetCommand,h0,h1]
   · simp [retargetCommand,h0,h1]
lemma retarget_defined : 𝚺ᴬ₁.DefinedFunction₂ (retargetCommand (M:=M)) retargetGraph := .mk (by
 intro v
 rw [Matrix.fun_eq_vec_three v]
 exact retargetGraph_eval _ _ _)
instance retarget_definable : 𝚺ᴬ₁-Function₂ (retargetCommand (M:=M)) := retarget_defined.to_definable
end ZF192Support.ModelCommands
