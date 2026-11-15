module
public import ModelRuntimeOracle
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open M6.Runtime
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma model_box_head (vs:List M) (spares:M) (x:BoxSt) (hlen:vs.length=9) :
 ∃t,modelBox vs spares x 0=2*t := by
 cases vs with
 | nil => simp at hlen
 | cons v vs =>
  cases x with
  | plain eff =>
   cases eff with
   | none => exact ⟨_,rfl⟩
   | inc r => cases r <;> exact ⟨_,rfl⟩
   | dec r => cases r <;> exact ⟨_,rfl⟩
  | mark r =>
   cases r with
   | zero =>
    refine ⟨2*bitRun v 1 (vs.foldr registerBlock (spareRun spares 0)),?_⟩
    change 4*_=2*(2*_)
    rw [←mul_assoc]; norm_num
   | succ r => exact ⟨_,rfl⟩
end ZF209.BinaryTape
