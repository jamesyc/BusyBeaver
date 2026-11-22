module
public import ZF192Support.Execution.Commands.Program.Push
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZF192Support.Internal (imp mem eqc all)
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma all_add_ne_one (i a b:M) : all i a+b≠1 := by
 rw [modelAll_value]
 intro he
 have hb : (2:M)≤4*modelCantor a i+2+b := by
  have h1 : (2:M)≤4*modelCantor a i+2 := by simp
  exact le_trans h1 (by simp)
 rw [he] at hb
 have hlt:(1:M)<2 := by simp
 exact (not_le_of_gt hlt) hb
lemma add_all_ne_one (i a b:M) : b+all i a≠1 := by rw [add_comm]; exact all_add_ne_one _ _ _
lemma modelAX_shift9 (a x y t w d h:M) :
 modelCommandsEval ([.ax a x y]++List.replicate 9 .shift) ⟨t,w,d,h⟩ = some ⟨all d h,w,0,t⟩ := by
 have he : ([.ax a x y]++List.replicate 9 (.shift:Command M))=
  ([.ax a x y]++List.replicate 8 .shift)++[.shift] := by rfl
 rw [he,modelCommandsEval_append,modelAX_shift8]
 simp only [Option.bind_some,modelCommandsEval,modelCommandEval,add_all_ne_one,ite_false,
  modelUnpairLeft_pair,modelUnpairRight_pair]
lemma modelAX_shift10 (a x y t w d h:M) :
 modelCommandsEval ([.ax a x y]++List.replicate 10 .shift) ⟨t,w,d,h⟩ =
 some ⟨t,modelUnpairRight w,0,modelUnpairLeft w⟩ := by
 have he : ([.ax a x y]++List.replicate 10 (.shift:Command M))=
  ([.ax a x y]++List.replicate 9 .shift)++[.shift] := by rfl
 rw [he,modelCommandsEval_append,modelAX_shift9]
 simp only [Option.bind_some,modelCommandsEval,modelCommandEval,all_add_ne_one,ite_false]
def modelMPtail (b:M) : List (Command M) := [.shift,.shift,.mp b]++([.ax b 0 0]++List.replicate 10 .shift)
lemma modelMPtail_result (a b w:M) :
 modelCommandsEval (modelMPtail b) ⟨0,modelCantor a (modelCantor (imp a b) w),0,0⟩=none ∨
 modelCommandsEval (modelMPtail b) ⟨0,modelCantor a (modelCantor (imp a b) w),0,0⟩=some ⟨b,w,0,0⟩ := by
 have hp:modelCommandsEval [.shift,.shift,.mp b] ⟨0,modelCantor a (modelCantor (imp a b) w),0,0⟩=
  if a=1 then none else some ⟨b,modelCantor 0 w,b,0⟩ := by
  by_cases ha:a=1 <;> simp [modelCommandsEval,modelCommandEval,modelUnpairLeft_pair,modelUnpairRight_pair,ha]
 by_cases ha:a=1
 · left; rw [modelMPtail,modelCommandsEval_append,hp,if_pos ha]; rfl
 · right; rw [modelMPtail,modelCommandsEval_append,hp,if_neg ha]
   simp only [Option.bind_some,modelAX_shift10,modelUnpairLeft_pair,modelUnpairRight_pair]
noncomputable def modelJ (i:M) : List (Command M) := if i=0 then [] else [.mp i]
lemma modelJ_total (i w:M) : modelCommandsEval (modelJ i) ⟨0,w,0,0⟩=some ⟨0,w,i,0⟩ := by
 by_cases hi:i=0
 · simp [modelJ,hi,modelCommandsEval]
 · have he:imp (0:M) i≠0 := by
    rw [modelImp_value]
    intro hz
    have heq:4*modelCantor (0:M) i=4*0 := by simpa using hz
    have hp:modelCantor (0:M) i=modelCantor 0 0 := (mul_left_cancel₀ (by norm_num : (4:M)≠0) heq).trans modelCantor_zero.symm
    exact hi (modelCantor_injective hp).2
   simp [modelJ,hi,modelCommandsEval,modelCommandEval,he]
def modelPUSH : List (Command M) := ([.ax 0 0 0]++List.replicate 8 .shift)++[.mp 0]
noncomputable def modelGEN (i:M) : List (Command M) := modelPUSH++(modelJ i++([.shift]++([.ax i 0 0]++List.replicate 9 .shift)))
lemma modelGEN_total (i a w:M) : modelCommandsEval (modelGEN i) ⟨a,w,0,0⟩=some ⟨all i a,w,0,0⟩ := by
 rw [modelGEN,modelCommandsEval_append,modelPUSH,modelPUSH_total]
 simp only [Option.bind_some]
 rw [modelCommandsEval_append,modelJ_total]
 simp only [Option.bind_some]
 rw [modelCommandsEval_append]
 simp only [modelCommandsEval,modelCommandEval,add_zero,zero_ne_one,ite_false,modelUnpairLeft_pair,modelUnpairRight_pair,Option.bind_some]
 exact modelAX_shift9 i 0 0 0 w i a
end ZF192Support.ModelCommands
