module
public import I3_380.Search.Arithmetic.ScanConsumption
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine.SourceCantor (decodeLeft decodeRight)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem coded_keep_field {kept discarded source : Register}
    (fields : kept ≠ discarded) (keepSource : kept ≠ source) (dropSource : discarded ≠ source)
    (s : Store M) (clearKeep : s kept = 0) (clearDrop : s discarded = 0) (a b : M) :
    (Program.seq (clear discarded) (move kept source)).Runs .normal
      (((s.set source 0).set kept a).set discarded b).code (s.set source a).code := by
  let unpacked := ((s.set source 0).set kept a).set discarded b
  let filtered := unpacked.set discarded 0
  have clearField := coded_clear discarded unpacked
  have moveField := coded_move keepSource filtered
  have sourceEmpty : filtered source = 0 := by
    simp [filtered,unpacked,Store.set,Ne.symm keepSource,Ne.symm dropSource]
  have keep : filtered kept = a := by simp [filtered,unpacked,Store.set,fields]
  rw [sourceEmpty,keep,zero_add] at moveField
  have final : (filtered.set kept 0).set source a = s.set source a := by
    funext r
    by_cases atSource : r = source <;> by_cases atKept : r = kept <;> by_cases atDiscarded : r = discarded <;>
      simp_all [filtered,unpacked,Store.set,Ne.symm fields,Ne.symm keepSource,Ne.symm dropSource]
  rw [final] at moveField
  exact Program.Runs.rightExit clearField moveField rfl

theorem coded_dropField (s : Store M) (scratch : ContextScratch s) :
    dropField.Runs .normal s.code (s.set tmp (decodeRight (s tmp))).code := by
  let a := decodeLeft (s tmp)
  let b := decodeRight (s tmp)
  have first := coded_unpair (a := «exp») (b := u) (input := tmp)
    (by decide) (by decide) (by decide) s scratch.1 scratch.2.2
  have last := coded_keep_field (kept := u) (discarded := «exp») (source := tmp)
    (by decide) (by decide) (by decide) s scratch.2.2 scratch.1 b a
  have swap : ((s.set tmp 0).set u b).set «exp» a =
      ((s.set tmp 0).set «exp» a).set u b :=
    Store.set_comm _ (by decide) _ _
  rw [swap] at last
  exact Program.Runs.rightExit first last rfl

theorem coded_grabField (s : Store M) (scratch : ContextScratch s) :
    grabField.Runs .normal s.code (s.set tmp (decodeLeft (s tmp))).code := by
  have first := coded_unpair (a := «exp») (b := u) (input := tmp)
    (by decide) (by decide) (by decide) s scratch.1 scratch.2.2
  have last := coded_keep_field (kept := «exp») (discarded := u) (source := tmp)
    (by decide) (by decide) (by decide) s scratch.1 scratch.2.2
    (decodeLeft (s tmp)) (decodeRight (s tmp))
  exact Program.Runs.rightExit first last rfl

end PalomarI3380.Compiler.Source
