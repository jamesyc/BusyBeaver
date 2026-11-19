module
public import AXRealization
public import PrimitivePushBindings
public import PrimitivePairBindings
public import PrimitiveCopyBindings
public import PrimitiveConsBindings
@[expose] public section
namespace C207Search.AXMacro
open C207Search.Primitive

inductive Certificate : Nat → List Op → Nat → Prop
 | nil (pc) : Certificate pc [] pc
 | cons : Realizes op start mid → Certificate mid ops stop → Certificate start (op::ops) stop

theorem certificate_sound (hc : Certificate start ops stop)
 (he : run ops s = some s') (bottom : Nat) (f : Registers) :
 ∃n,(ops≠[]→0<n) ∧ Steps n (configAt start s bottom f) (configAt stop s' bottom f) := by
 induction hc generalizing s s' with
 | nil pc =>
   simp only [run,Option.some.injEq] at he
   subst s'
   exact ⟨0,by simp,Steps.refl _⟩
 | @cons op start mid ops stop hop htail ih =>
   cases hx : exec op s with
   | none => simp [run,hx] at he
   | some m =>
     simp only [run,hx,Option.bind_some] at he
     obtain ⟨k,hk,hfirst⟩ := hop s m hx bottom f
     obtain ⟨n,_,hrest⟩ := ih he
     exact ⟨k+n,by omega,steps_trans hfirst hrest⟩
end C207Search.AXMacro
