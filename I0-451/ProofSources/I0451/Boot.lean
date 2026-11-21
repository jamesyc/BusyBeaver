module
public import I0451.Tables
public import I0451.Simulation

@[expose] public section
namespace I0451

/-- The exact table has 902 rows, two for each working state 0 through 450.
Label 451 has no outgoing row and the table contains exactly one edge into it. -/
def literalShape : Prop :=
  literal < 2048 ^ 902 ∧
  (List.range 902).all (fun i => let code := digit literal i
      code != 0 && (code - 1) / 4 ≤ 451) = true ∧
  ((List.range 902).filter (fun i => (digit literal i - 1) / 4 == 451)).length = 1

theorem literal_shape : literalShape := by
  unfold literalShape
  decide +kernel

/-- The five-state initialization with the handoff row omitted. Its
small width keeps kernel startup evaluation focused on the boot rows. -/
private def bootTable : Table := 0x28020000440980e00e02c04808

private def agreeOnBootRows (full : Table) : Bool :=
  (List.range 10).all fun i => digit bootTable i == 0 || digit full i == digit bootTable i

private theorem bootWidth : bootTable < 2048 ^ 10 := by decide +kernel

private theorem extendsBoot {full : Table} (checked : agreeOnBootRows full = true)
    (q : Nat) (b : Bool) (present : row bootTable q b ≠ 0) :
    row full q b = row bootTable q b := by
  let i := 2 * q + b.toNat
  change digit full i = digit bootTable i
  change digit bootTable i ≠ 0 at present
  have within : i < 10 := by
    by_cases h : i < 10
    · exact h
    · have power : 2048 ^ 10 ≤ 2048 ^ i :=
        Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt h)
      have zero := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le bootWidth power)
      exact (present (by simp only [digit, zero, Nat.zero_mod])).elim
  have agrees := List.all_eq_true.mp checked i (List.mem_range.mpr within)
  simp only [Bool.or_eq_true, beq_iff_eq] at agrees
  exact agrees.resolve_left present

private theorem literal_extends_boot : agreeOnBootRows literal = true := by decide +kernel

private def at8000 : Config :=
  ⟨0, 0x24444442222222c8888888888, 0x15555555555555555555555aaaab⟩
private def at16000 : Config :=
  ⟨1, 0x911111911116444444, 0x55555555555555555555555555555555555555555555556aa⟩
private def at24000 : Config :=
  ⟨2, 0x911113222229164444444444444444444444444444444444444444444, 0x155555555555555555554⟩
private def at32000 : Config :=
  ⟨1, 0x244444c8, 0xaaaaaaaaaad555555555555555555555555555555555555555555555555555555555555555555555554⟩
private def handoff : Config :=
  ⟨3, 0x48888,
    0x55555555555555555555555555555555556aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab⟩

/-- The tape at the first decoder entry, with the head on the first
instruction-pointer bit. -/
def bootFrame : Config :=
  ⟨root, 1,
    0x15555555555555555555555555555555555aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000⟩

section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem boot1 : run bootTable 8000 (blank 0) = some at8000 := by decide +kernel
private theorem boot2 : run bootTable 8000 at8000 = some at16000 := by decide +kernel
private theorem boot3 : run bootTable 8000 at16000 = some at24000 := by decide +kernel
private theorem boot4 : run bootTable 8000 at24000 = some at32000 := by decide +kernel
private theorem boot5 : run bootTable 7733 at32000 = some handoff := by decide +kernel

private theorem bootShared : run bootTable 39733 (blank 0) = some handoff := by
  have first : run bootTable 16000 (blank 0) = some at16000 :=
    run_join (m := 8000) (n := 8000) boot1 boot2 rfl
  have second : run bootTable 16000 at16000 = some at32000 :=
    run_join (m := 8000) (n := 8000) boot3 boot4 rfl
  have both : run bootTable 32000 (blank 0) = some at32000 :=
    run_join (m := 16000) (n := 16000) first second rfl
  exact run_join (m := 32000) (n := 7733) both boot5 rfl

private theorem literal_finish : run literal 20 handoff = some bootFrame := by decide +kernel
end

theorem literal_boot : run literal 39753 (blank 0) = some bootFrame :=
  run_join (m := 39733) (n := 20)
    (run_of_agreeing_rows (extendsBoot literal_extends_boot) bootShared) literal_finish rfl

end I0451
