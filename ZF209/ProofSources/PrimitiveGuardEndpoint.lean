module
public import PrimitiveGuard
@[expose] public section
namespace C209Search.Primitive.Unpair
open M209.Source M209.SourceSimulation

private theorem row10 : program 10 = some .halt := by decide +kernel

theorem steps_terminate (h : Steps n s t) (ht : scalarNext program t = none) :
 Terminates (scalarNext program) s := by
 induction h with
 | refl => exact .done ht
 | @cons n s t h ih =>
   cases hs : scalarNext program s with
   | none => exact .done hs
   | some mid =>
     apply Terminates.more hs
     have he : step s = mid := by simp [step,hs]
     rw [he] at ih
     exact ih ht

theorem equal_guard_halts (h w y : Nat) (f : Registers) :
 Terminates (scalarNext program) (configAt 0 ⟨w,h,h,y,f⟩) := by
 obtain ⟨n,hn⟩ := guard_equal h w y f
 apply steps_terminate hn
 unfold scalarNext configAt
 rw [row10]
 rfl

end C209Search.Primitive.Unpair
