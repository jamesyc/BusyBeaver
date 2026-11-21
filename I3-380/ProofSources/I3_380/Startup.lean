module
public import I3_380.Machine
public import I3_380.Literal
@[expose] public section

namespace PalomarI3380

def machine : Machine := ⟨380, packedLiteral⟩

/-- Check the packed lookup at every row of the source transition array. -/
theorem packed_rows_exact :
    (literal.toList.zipIdx.all fun (row, i) => machine.row (i / 2) (i % 2) == row) = true := by
  decide +kernel

theorem literal_shape :
    machine.workingStates = 380 ∧ literal.size = 760 ∧
    (literal.toList.all fun row => row / 4 ≤ 380) = true ∧
    ((literal.toList.zipIdx.filter fun (row, _) => row / 4 == 380).map Prod.snd) = [521] := by
  decide +kernel

/-- The seven pre-decoder states. A successful run can reach the first
decoder configuration as its endpoint. -/
def bootMachine : Machine := ⟨7, packedLiteral⟩

/-- Full tape, relative to the head, at the end of the parity loader. -/
def loaderExit : Configuration :=
  ⟨7, 1, 0x15555555555555555555555555555555555aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000⟩

section LoaderReplay

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

-- Three tape snapshots bound the kernel's memory during the loader replay.
private def c10000 : Configuration :=
  ⟨4, 0x24444464444445222222222222291111111111, 0x5555555555555555554⟩

private def c20000 : Configuration :=
  ⟨1, 0x91111191111c8889911111111111111111111111111111111111, 0xaaaaaaaaaaaaaaaaaaab⟩

private def c30000 : Configuration :=
  ⟨1, 0x91111323222222222222222222222222, 0x1555555555555555555555555555555555555555555555555555⟩

private theorem firstBlock : run bootMachine 10000 blank = some c10000 := by decide +kernel
private theorem secondBlock : run bootMachine 10000 c10000 = some c20000 := by decide +kernel
private theorem thirdBlock : run bootMachine 10000 c20000 = some c30000 := by decide +kernel
private theorem lastBlock : run bootMachine 9753 c30000 = some loaderExit := by decide +kernel

theorem boot_startup : run bootMachine 39753 blank = some loaderExit := by
  have replay := join_run (join_run (join_run firstBlock secondBlock) thirdBlock) lastBlock
  rw [show 10000 + 10000 + 10000 + 9753 = 39753 by decide] at replay
  exact replay

end LoaderReplay

theorem literal_startup : run machine 39753 blank = some loaderExit :=
  run_extend (small := bootMachine) (large := machine) (n := 39753) (c := blank) (d := loaderExit)
    (by decide) (fun _ _ _ _ => rfl) boot_startup

end PalomarI3380
