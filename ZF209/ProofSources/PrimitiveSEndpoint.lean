module
public import PrimitiveSStage
@[expose] public section
namespace C209Search.Primitive.SCommand
open M209.Source M209.SourceSimulation

def frame (w : Nat) (f : Registers) : Registers := write (write f 0 w) 5 0
def start (t h w : Nat) (f : Registers) : Configuration :=
 SStage.configAt 4329 ⟨t,h,0,frame w f⟩
def output (h w : Nat) (f : Registers) : Configuration :=
 Unpair.exitAt ⟨(M6.Source.Cantor.decode w).2,(M6.Source.Cantor.decode w).1,0,0,
  write (frame w f) 2 h⟩

private theorem bridge (t h w : Nat) (f : Registers) :
 SStage.configAt 0 ⟨h,t+h,1,frame w f⟩ =
 Unpair.configAt 0 ⟨w,t+h,1,0,write (frame w f) 2 h⟩ := by
 apply congrArg (ScalarState.mk 0)
 funext r
 by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h5 : r=5 <;>
 by_cases h7 : r=7 <;> by_cases h8 : r=8 <;>
 simp_all [SStage.registers,Unpair.registers,frame,write]

private theorem prefix_terminates (h : Steps n s t) (ht : Terminates (scalarNext program) t) :
 Terminates (scalarNext program) s := by
 induction h with
 | refl => exact ht
 | @cons n s t h ih =>
   cases hs : scalarNext program s with
   | none => exact .done hs
   | some mid =>
     apply Terminates.more hs
     have he : step s=mid := by simp [step,hs]
     rw [he] at ih
     exact ih ht

/-- Literal S command, including staging and the shared guard. -/
theorem halts_of_sum_one (t h w : Nat) (f : Registers) (hs : t+h=1) :
 Terminates (scalarNext program) (start t h w f) := by
 have hp := SStage.total t h (frame w f)
 rw [bridge,hs] at hp
 exact prefix_terminates hp (Unpair.equal_guard_halts 1 w 0 (write (frame w f) 2 h))

/-- Literal S command returns T:=old H, pops W into H, clears scratch X/Y,
and preserves N,L,A,D and unrelated registers whenever T+H is not one. -/
theorem run_of_sum_ne_one (t h w : Nat) (f : Registers) (hs : t+h≠1) :
 ∃n, runSource n (start t h w f) = some (output h w f) := by
 have hp := SStage.total t h (frame w f)
 rw [bridge] at hp
 obtain ⟨k,hk⟩ := Unpair.guard_unequal (t+h) 1 w 0 (write (frame w f) 2 h) hs
 have hd := Unpair.unpair w (write (frame w f) 2 h)
 exact ⟨_,steps_real _ _ _ (steps_trans (steps_trans hp hk) hd) (Unpair.exit_not_terminal _)⟩
end C209Search.Primitive.SCommand
