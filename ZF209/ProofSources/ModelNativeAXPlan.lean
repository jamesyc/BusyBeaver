module
public import ModelNativeAXSymbolicEval
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeAXSymbolic
open ZF209.NativeSource
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
inductive Certificate : Nat→List Op→Nat→Prop
 | nil (pc) : Certificate pc [] pc
 | cons : Realizes (M:=M) op start mid→Certificate mid ops stop→Certificate start (op::ops) stop
lemma certificate_sound (hc:Certificate (M:=M) start ops stop) (he:run ops s=some s')
 (n:M)(v:Fin 6→M)(tail bottom:M) :
 nativeReaches (NativeAX.config start n (materialize v tail bottom s))
 (NativeAX.config stop n (materialize v tail bottom s')) := by
 induction hc generalizing s s' with
 | nil pc=>
  simp only [run,Option.some.injEq] at he
  subst s'
  intro initial hist hh hl
  exact ⟨hist,hh,hl⟩
 | @cons op start mid ops stop hop hc ih=>
  cases hx:exec op s with
  | none=>simp [run,hx] at he
  | some m=>
   simp only [run,hx,Option.bind_some] at he
   exact nativeReaches_trans (hop s m hx n v tail bottom) (ih he)
end ZF209.NativeAXSymbolic
