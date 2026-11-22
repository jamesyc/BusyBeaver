module
public import ZF192Support.Execution.Commands.Program.ResidualTail
public import ZF192Support.Machine.RegisterProgram.Projection
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeSource
open ZFR.ArithmeticRepresentation RegisterMachine.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
structure State (M:Type*) where
 pc:M
 registers:Fin 9→M
noncomputable def execute (i:Instruction) (s:State M) : Option (State M) :=
 match i with
 | .inc r k => some ⟨(k: M),fun j=>if j.val=r then s.registers j+1 else s.registers j⟩
 | .dec r z p => if s.registers (registerIndex r)=0 then some ⟨(z:M),s.registers⟩
   else some ⟨(p:M),fun j=>if j.val=r then modelPredecessor (s.registers j) else s.registers j⟩
 | .jump k => some ⟨(k:M),s.registers⟩
 | .halt => none
/-- Exact standard-model binding, retaining all nine scalar registers. -/
lemma execute_nat (i:Instruction) (s:ScalarState) :
 execute i (⟨s.pc,s.registers⟩:State Nat)=(scalarExecute i s).map (fun o=>⟨o.pc,o.registers⟩) := by
 cases i <;> simp [execute,scalarExecute,modelPredecessor_nat] <;> split <;> rfl
end ZF192Support.NativeSource
