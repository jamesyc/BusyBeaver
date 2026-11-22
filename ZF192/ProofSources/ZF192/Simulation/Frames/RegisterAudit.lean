module
public import ZF192.Simulation.Frames.Contracts
public import ZF192Support.Execution.Registers.Source
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.BinaryTape
open ZFR.ArithmeticRepresentation RegisterMachine.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma audit_increment_registers (regs:Fin 9→M) (r:Nat) (hr:r<9) :
 incrementRegisters regs ⟨r,hr⟩=(fun j=>if j.val=r then regs j+1 else regs j) := by
 funext j
 simp only [incrementRegisters,Fin.ext_iff]
lemma audit_decrement_registers (regs:Fin 9→M) (r:Nat) (hr:r<9) :
 decrementRegisters regs ⟨r,hr⟩=(fun j=>if j.val=r then modelPredecessor (regs j) else regs j) := by
 funext j
 simp only [decrementRegisters,Fin.ext_iff]
lemma audit_register_index (r:Nat) (hr:r<9) : registerIndex r=⟨r,hr⟩ := by
 simp [registerIndex,hr]
end ZF192.BinaryTape
