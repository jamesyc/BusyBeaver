module
public import ZF192.Simulation.Frames.RegisterAudit
public import ZF192.Machine.Control.Coverage
public import ZF192.Machine.Decoder.Coverage

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.NativePhysicalLift
open ZFR.ArithmeticRepresentation ZF192.BinaryTape M192.Control M192.Paths
open RegisterMachine.Source (Instruction instructionBound registerIndex)

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Every live contextual row has its positive physical implementation. -/
theorem coverage_complete {pc : Nat} {op : Instruction}
    (bound : pc < siteCount) (row : machineProgram pc = some op) :
    instructionBound siteCount op ∧ FrameImplements (M := M) pc op := by
  have checked := M192.FiniteChecks.of_block M192.Sites.allChecked bound
  exact frameImplements_of_check pc op row (by simpa using checked)

theorem contextual_jumps {pc dst : Nat} (h : JumpPath machineProgram pc dst)
    (bound : pc < siteCount) (regs : Fin 9 → M) (n ρ : M) :
    dst < siteCount ∧ Reaches (nativeFrame pc regs n ρ) (nativeFrame dst regs n ρ) := by
  induction h with
  | refl pc => exact ⟨bound, .refl _⟩
  | step row tail ih =>
    obtain ⟨valid, run⟩ := coverage_complete (M := M) bound row
    obtain ⟨bd, rest⟩ := ih valid
    exact ⟨bd, (run n ρ regs).reaches.trans rest⟩

private theorem contextual_skip {pc dst : Nat} (h : machineSkip pc = some dst)
    (bound : pc < siteCount) (regs : Fin 9 → M) (n ρ : M) :
    Reaches (nativeFrame pc regs n ρ) (nativeFrame dst regs n ρ) :=
  (contextual_jumps (skip_sound h).1 bound regs n ρ).2

/-- Permuting the register file commutes with an update at the matched slot. -/
private theorem permute_update (f : M → M) (regs : Fin 9 → M)
    {r r' : Nat} (hr : r < 9) (hr' : r' < 9) (matched : r' = mapRegister r) :
    (fun j => if j = ⟨r', hr'⟩ then f (permute regs j) else permute regs j) =
      permute (fun j => if j.val = r then f (regs j) else regs j) := by
  have slot : (⟨r', hr'⟩ : Fin 9) = machineSlot ⟨r, hr⟩ := by
    apply Fin.ext
    simpa [mapRegister, audit_register_index r hr] using matched
  funext j
  have which : (j = ⟨r', hr'⟩) ↔ (compilerSlot j).val = r := by
    rw [slot]
    constructor
    · intro e
      rw [e, compilerSlot_machineSlot]
    · intro e
      have eq : compilerSlot j = (⟨r, hr⟩ : Fin 9) := Fin.ext e
      rw [← eq, machineSlot_compilerSlot]
  simp [permute, which]

private theorem aligned_increment (regs : Fin 9 → M) {r r' : Nat}
    (hr : r < 9) (hr' : r' < 9) (matched : r' = mapRegister r) :
    incrementRegisters (permute regs) ⟨r', hr'⟩ =
      permute (fun j => if j.val = r then regs j + 1 else regs j) := by
  exact permute_update (· + 1) regs hr hr' matched

private theorem aligned_decrement (regs : Fin 9 → M) {r r' : Nat}
    (hr : r < 9) (hr' : r' < 9) (matched : r' = mapRegister r) :
    decrementRegisters (permute regs) ⟨r', hr'⟩ =
      permute (fun j => if j.val = r then modelPredecessor (regs j) else regs j) := by
  exact permute_update modelPredecessor regs hr hr' matched

private theorem aligned_value (regs : Fin 9 → M) {r r' : Nat}
    (hr : r < 9) (hr' : r' < 9) (matched : r' = mapRegister r) :
    permute regs ⟨r', hr'⟩ = regs ⟨r, hr⟩ := by
  have slot : (⟨r', hr'⟩ : Fin 9) = machineSlot ⟨r, hr⟩ := by
    apply Fin.ext
    simpa [mapRegister, audit_register_index r hr] using matched
  simp [permute, slot, compilerSlot_machineSlot]

/-- Old unconditional jumps leave the aligned frame fixed. Arithmetic consumes
a genuine physical step before any contextual jump suffix. -/
def AlignedMove (code : Instruction) (a b : State M) : Prop :=
  if isJump code then b = a else Reaches1 a b

theorem AlignedMove.reaches {code : Instruction} {a b : State M}
    (move : AlignedMove code a b) : Reaches a b := by
  unfold AlignedMove at move
  split at move
  · exact Reaches.of_eq move.symm
  · exact move.reaches

theorem AlignedMove.positive {code : Instruction} {a b : State M}
    (move : AlignedMove code a b) (h : isJump code = false) : Reaches1 a b := by
  simpa [AlignedMove, h] using move

theorem execute_aligned {pc : Nat} {code : Instruction} (bound : pc < 4341)
    (row : compilerProgram pc = some code) (regs : Fin 9 → M) (n ρ : M)
    (t : ZF192Support.NativeSource.State M)
    (run : ZF192Support.NativeSource.execute code ⟨(pc : M), regs⟩ = some t) :
    ∃ k : Nat, k < 4341 ∧ t.pc = (k : M) ∧ ∃ n',
      AlignedMove code (nativeFrame (align pc) (permute regs) n ρ)
        (nativeFrame (align k) (permute t.registers) n' ρ) := by
  obtain ⟨_, live, op, originalRow, valid, matched⟩ := checked (checked_at pc bound)
  have same : op = code := Option.some.inj (originalRow.symm.trans row)
  subst op
  cases code with
  | jump k =>
    simp only [ZF192Support.NativeSource.execute, Option.some.injEq] at run
    subst t
    refine ⟨k, valid, rfl, n, ?_⟩
    change nativeFrame (align k) (permute regs) n ρ = nativeFrame (align pc) (permute regs) n ρ
    change align pc = align k at matched
    rw [matched]
  | inc r k =>
    cases row' : machineProgram (align pc) with
    | none => simp [Matches, MatchesAt, row'] at matched
    | some op =>
      change MatchesAt pc (machineProgram (align pc)) (.inc r k) at matched
      rw [row'] at matched
      cases op <;> simp [MatchesAt] at matched
      case inc r' k' =>
        obtain ⟨slot, endPC⟩ := matched
        obtain ⟨valid', realizes⟩ := coverage_complete (M := M) live row'
        obtain ⟨hr', realize⟩ := realizes
        obtain ⟨n', moves⟩ := realize n ρ (permute regs)
        simp only [ZF192Support.NativeSource.execute, Option.some.injEq] at run
        subst t
        refine ⟨k, valid.2, rfl, n', ?_⟩
        simp only [AlignedMove, isJump, Bool.false_eq_true, if_false]
        rw [aligned_increment regs valid.1 hr' slot] at moves
        exact moves.trans (contextual_skip endPC valid'.2 _ n' ρ)
  | dec r z k =>
    cases row' : machineProgram (align pc) with
    | none => simp [Matches, MatchesAt, row'] at matched
    | some op =>
      change MatchesAt pc (machineProgram (align pc)) (.dec r z k) at matched
      rw [row'] at matched
      cases op <;> simp [MatchesAt] at matched
      case dec r' z' k' =>
        obtain ⟨slot, endZero, endPos⟩ := matched
        obtain ⟨valid', realizes⟩ := coverage_complete (M := M) live row'
        obtain ⟨hr', realize⟩ := realizes
        have value := aligned_value regs valid.1 hr' slot
        have index := audit_register_index r valid.1
        by_cases zero : regs ⟨r, valid.1⟩ = 0
        · simp only [ZF192Support.NativeSource.execute, index, zero, if_true, Option.some.injEq] at run
          subst t
          have moves := (realize n ρ (permute regs)).1 (value.trans zero)
          exact ⟨z, valid.2.1, rfl, n, moves.trans (contextual_skip endZero valid'.2.1 _ n ρ)⟩
        · simp only [ZF192Support.NativeSource.execute, index, zero, if_false, Option.some.injEq] at run
          subst t
          obtain ⟨n', moves⟩ := (realize n ρ (permute regs)).2 (fun h => zero (value.symm.trans h))
          rw [aligned_decrement regs valid.1 hr' slot] at moves
          exact ⟨k, valid.2.2, rfl, n', moves.trans (contextual_skip endPos valid'.2.2 _ n' ρ)⟩
  | halt => simp [ZF192Support.NativeSource.execute] at run

theorem aligned_halt {pc : Nat} (bound : pc < 4341) (row : compilerProgram pc = some .halt)
    (regs : Fin 9 → M) (n ρ : M) :
    ∃ terminal, Reaches1 (nativeFrame (align pc) (permute regs) n ρ) terminal ∧
      ∀ next, ¬ codedStep (stateCode terminal) next := by
  obtain ⟨_, live, code, hcode, _, matched⟩ := checked (checked_at pc bound)
  have same : code = .halt := Option.some.inj (hcode.symm.trans row)
  subst code
  change machineProgram (align pc) = some .halt at matched
  exact (coverage_complete (M := M) live matched).2 n ρ (permute regs)

end ZF192.NativePhysicalLift
