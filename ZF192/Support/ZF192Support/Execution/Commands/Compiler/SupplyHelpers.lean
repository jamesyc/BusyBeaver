module
public import ZF192Support.Execution.Commands.Compiler.Macros
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZF192Support.Internal (imp mem eqc all)
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma modelImp_eq_zero_iff (a b:M) : imp a b=0 ↔ a=0 ∧ b=0 := by
 rw [modelImp_value]
 constructor
 · intro hz
   have he:4*modelCantor a b=4*0 := by simpa using hz
   exact modelCantor_injective ((mul_left_cancel₀ (by norm_num : (4:M)≠0) he).trans modelCantor_zero.symm)
 · rintro ⟨rfl,rfl⟩; simp [modelCantor_zero]
lemma modelAll_ne_zero (i a:M) : all i a≠0 := by
 rw [modelAll_value]
 have hh:(0:M)<4*modelCantor a i+2 := by simp
 exact ne_of_gt hh
noncomputable def modelDISCARD : List (Command M) := [.mp 1]++([.ax 1 0 0]++List.replicate 9 .shift)++[.mp 0]
lemma modelDISCARD_total (t w:M) : modelCommandsEval modelDISCARD ⟨t,w,0,0⟩=some ⟨0,w,0,0⟩ := by
 have hmp:modelCommandsEval [.mp 1] ⟨t,w,0,0⟩=some ⟨0,w,1,0⟩ := by
  simp [modelCommandsEval,modelCommandEval,modelImp_eq_zero_iff]
 rw [modelDISCARD,modelCommandsEval_append,modelCommandsEval_append,hmp]
 simp only [Option.bind_some]
 rw [modelAX_shift9]
 simp only [Option.bind_some,modelCommandsEval,modelCommandEval,add_zero]
 simp [modelImp_eq_zero_iff,modelAll_ne_zero]
def modelPOP : List (Command M) := [.ax 0 0 0]++List.replicate 10 .shift
lemma modelPOP_pair (t x w d h:M) : modelCommandsEval modelPOP ⟨t,modelCantor x w,d,h⟩=some ⟨t,w,0,x⟩ := by
 rw [modelPOP,modelAX_shift10,modelUnpairLeft_pair,modelUnpairRight_pair]
def modelPOPs : Nat → List (Command M)
 | 0=>[]
 | n+1=>modelPOP++modelPOPs n
/-- External finite stack of values; used only for bounded supply macros. -/
lemma modelPOPs_clear (xs:List M) (t w d h:M) :
 modelCommandsEval (modelPOPs (xs.length+1)) ⟨t,(xs++[0]).foldr modelCantor w,d,h⟩=some ⟨t,w,0,0⟩ := by
 induction xs generalizing d h with
 | nil => simp only [List.length_nil,Nat.zero_add,List.nil_append,List.foldr_cons,List.foldr_nil,
   modelPOPs,modelCommandsEval_append,modelPOP_pair,Option.bind_some,modelCommandsEval]
 | cons x xs ih =>
   simp only [List.length_cons,List.cons_append,List.foldr_cons,modelPOPs,modelCommandsEval_append,modelPOP_pair,Option.bind_some]
   simpa only [modelPOPs,modelCommandsEval_append] using ih 0 x
end ZF192Support.ModelCommands
