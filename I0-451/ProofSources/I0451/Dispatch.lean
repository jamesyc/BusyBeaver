module
public import I0451.TapeRuns
public import I0451.Tables

/-! Returning to the decoder root in the literal machine. The dispatch
control counts consecutive zeros while going left. Eight zeros past the
left marker trigger the rightward scan back to that marker. -/

@[expose] public section
namespace I0451.Runtime

def dispatch (n : Nat) : Nat := dispatchStates[n]?.getD continueZero

def zeroRun (n : Nat) (read : Bool) : Nat := if read then 0 else n + 1

/-- The dispatcher never takes its bounce row while scanning this word. -/
def SafeDispatch : Nat → List Bool → Prop
  | _, [] => True
  | n, b :: bs => zeroRun n b ≤ 7 ∧ SafeDispatch (zeroRun n b) bs

theorem SafeDispatch.ones {word : List Bool} (safe : SafeDispatch 0 word) (n : Nat) :
    SafeDispatch 0 (List.replicate n true ++ word) := by
  induction n with
  | zero => exact safe
  | succ n ih =>
    rw [List.replicate_succ]
    exact ⟨by decide, ih⟩

def dispatchEnd : Nat → List Bool → Nat
  | n, [] => n
  | n, b :: bs => dispatchEnd (zeroRun n b) bs

namespace DispatchRows

theorem dispatch_zero : dispatch 0 = continueZero := by decide +kernel

theorem onesRow (n : Fin 8) :
    row literal (dispatch n.val) true = transition true false continueZero := by
  have checked : (List.range 8).all (fun k =>
      row literal (dispatch k) true == transition true false continueZero) = true := by
    decide +kernel
  exact beq_iff_eq.mp (List.all_eq_true.mp checked n.val (List.mem_range.mpr n.isLt))

theorem zerosRow (n : Fin 7) :
    row literal (dispatch n.val) false = transition false false (dispatch (n.val + 1)) := by
  have checked : (List.range 7).all (fun k =>
      row literal (dispatch k) false == transition false false (dispatch (k + 1))) = true := by
    decide +kernel
  exact beq_iff_eq.mp (List.all_eq_true.mp checked n.val (List.mem_range.mpr n.isLt))

theorem dispatchRow {n : Nat} {b : Bool} (start : n ≤ 7) (finish : zeroRun n b ≤ 7) :
    row literal (dispatch n) b = transition b false (dispatch (zeroRun n b)) := by
  cases b
  · exact zerosRow ⟨n, by simp [zeroRun] at finish; omega⟩
  · simpa [zeroRun, dispatch_zero] using onesRow ⟨n, by omega⟩

theorem safeEnd {n : Nat} {word : List Bool} (hn : n ≤ 7) (safe : SafeDispatch n word) :
    dispatchEnd n word ≤ 7 := by
  induction word generalizing n with
  | nil => exact hn
  | cons b bs ih => exact ih safe.1 safe.2

end DispatchRows

open DispatchRows

private theorem scanWord {n : Nat} {word : List Bool} (hn : n ≤ 7)
    (safe : SafeDispatch n word) (l r : Nat) :
    Reaches literal (fromLeft (dispatch n) (pack word l) r)
      (fromLeft (dispatch (dispatchEnd n word)) l (pack word.reverse r)) := by
  induction word generalizing n r with
  | nil => exact ⟨0, rfl⟩
  | cons b bs ih =>
    simp only [pack_cons, List.reverse_cons, pack_append, pack_nil, dispatchEnd]
    exact (Reaches.left' (dispatchRow hn safe.1) _ _).trans
      (ih safe.1 safe.2 (push b r))

namespace DispatchRows

theorem bounce_window :
    Window.run literal 16
      ⟨continueZero, List.replicate 7 false, [false, true]⟩ =
      some ⟨root, true :: List.replicate 8 false, []⟩ := by decide +kernel

end DispatchRows

private theorem zero_pack (n : Nat) : pack (List.replicate n false) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, push, ih]

private theorem bounce (r : Nat) :
    Reaches literal (fromLeft continueZero 0 (push true r)) ⟨root, 1, r⟩ := by
  refine ⟨16, ?_⟩
  have full := Window.run_extend bounce_window 0 r
  change run literal 16 ⟨continueZero, pack (List.replicate 7 false) 0,
      push false (push true r)⟩ = some ⟨root, push true (pack (List.replicate 8 false) 0), r⟩ at full
  rw [zero_pack 7, zero_pack 8] at full
  exact full

/-- Return from the reversed instruction prefix. The tape to the left
of the marker is blank, and the prefix does not trigger dispatch early. -/
theorem continue_zero {word : List Bool} (safe : SafeDispatch 0 word.reverse) (r : Nat) :
    Reaches literal (fromLeft continueZero (pack word.reverse 1) r)
      ⟨root, 1, pack word r⟩ := by
  have scan := scanWord (n := 0) (by decide) safe 1 r
  rw [dispatch_zero, List.reverse_reverse] at scan
  have count := safeEnd (n := 0) (by decide) safe
  have throughMarker : Reaches literal
      (fromLeft (dispatch (dispatchEnd 0 word.reverse)) 1 (pack word r))
      (fromLeft continueZero 0 (push true (pack word r))) :=
    Reaches.left' (onesRow ⟨_, by omega⟩) 0 (pack word r)
  exact scan.trans (throughMarker.trans (bounce _))

namespace DispatchRows

theorem breakOneBit : row literal breakZero true = transition false false breakZero := by decide +kernel
theorem breakZeroBit : row literal breakZero false = transition true false continueZero := by decide +kernel

end DispatchRows

/-- Increment an instruction address which has a zero before the trailing
ones. The trailing ones become zeros, and that zero becomes one. -/
theorem advance_address {word : List Bool} (safe : SafeDispatch 0 word.reverse)
    (ones r : Nat) :
    Reaches literal
      (fromLeft breakZero
        (pack (List.replicate ones true) (push false (pack word.reverse 1))) r)
      ⟨root, 1, pack (word ++ true :: List.replicate ones false) r⟩ := by
  have trailing := Reaches.scanLeft breakOneBit ones (push false (pack word.reverse 1)) r
  have carry := Reaches.left' breakZeroBit (pack word.reverse 1) (pack (List.replicate ones false) r)
  have back := continue_zero safe (push true (pack (List.replicate ones false) r))
  simpa only [pack_append, pack_cons] using trailing.trans (carry.trans back)

/-- On overflow the machine writes a new marker one cell farther left.
The old marker and the trailing ones become zero. -/
theorem advance_overflow (ones r : Nat) :
    Reaches literal (fromLeft breakZero (pack (List.replicate ones true) 1) r)
      ⟨root, 1, pack (List.replicate (ones + 1) false) r⟩ := by
  have trailing := Reaches.scanLeft breakOneBit ones 1 r
  have marker : Reaches literal
      (fromLeft breakZero 1 (pack (List.replicate ones false) r))
      (fromLeft breakZero 0 (pack (List.replicate (ones + 1) false) r)) := by
    have markerValue : push true 0 = 1 := rfl
    simpa only [List.replicate_succ, pack_cons, markerValue] using
      Reaches.left' breakOneBit 0 (pack (List.replicate ones false) r)
  have carry : Reaches literal
      (fromLeft breakZero 0 (pack (List.replicate (ones + 1) false) r))
      (fromLeft continueZero 0 (push true (pack (List.replicate (ones + 1) false) r))) :=
    Reaches.left' breakZeroBit 0 _
  exact trailing.trans (marker.trans (carry.trans (bounce _)))

theorem SafeDispatch.mono {m n : Nat} {word : List Bool}
    (safe : SafeDispatch n word) (le : m ≤ n) : SafeDispatch m word := by
  induction word generalizing m n with
  | nil => trivial
  | cons bit rest ih =>
    have count : zeroRun m bit ≤ zeroRun n bit := by
      cases bit <;> simp [zeroRun, le]
    exact ⟨Nat.le_trans count safe.1, ih safe.2 count⟩

theorem SafeDispatch.tail {n : Nat} {bit : Bool} {rest : List Bool}
    (safe : SafeDispatch n (bit :: rest)) : SafeDispatch 0 rest :=
  safe.2.mono (Nat.zero_le _)

/-- Increment a little-endian address by carrying from the end of the
instruction word. Overflow leaves one extra zero before the gap. -/
def carry : List Bool → List Bool
  | [] => [false]
  | false :: rest => true :: rest
  | true :: rest => false :: carry rest

/-- The physical increment of the instruction address. -/
theorem break_zero {reversed : List Bool} (safe : SafeDispatch 0 reversed) (r : Nat) :
    Reaches literal (fromLeft breakZero (pack reversed 1) r)
      ⟨root, 1, pack (carry reversed).reverse r⟩ := by
  induction reversed generalizing r with
  | nil => exact advance_overflow 0 r
  | cons bit rest ih =>
    cases bit
    · have ready := advance_address (word := rest.reverse) (by simpa using safe.tail) 0 r
      simpa [carry, List.reverse_cons, pack_append] using ready
    · simp only [carry, List.reverse_cons, pack_append, pack_cons, pack_nil]
      exact (Reaches.left' breakOneBit _ _).trans (ih safe.tail (push false r))

namespace DispatchRows

theorem breakSkipOne :
    row literal breakOne true = transition false false breakOne := by decide +kernel
theorem breakSkipZero :
    row literal breakOne false = transition false false breakZero := by decide +kernel
theorem continueSkipZero :
    row literal continueOne false = transition false false continueOne := by decide +kernel
theorem continueSkipOne :
    row literal continueOne true = transition false false continueZero := by decide +kernel

end DispatchRows

/-- Skip the nearest zero before carrying. The consumed cells remain in
the gap as zeros. -/
theorem break_one {reversed : List Bool} (safe : SafeDispatch 0 reversed) (ones r : Nat) :
    Reaches literal
      (fromLeft breakOne (pack (List.replicate ones true) (push false (pack reversed 1))) r)
      ⟨root, 1, pack (carry reversed).reverse (push false (pack (List.replicate ones false) r))⟩ :=
  (Reaches.scanLeft breakSkipOne ones _ _).trans
    ((Reaches.left' breakSkipZero _ _).trans (break_zero safe _))

/-- Skip the nearest one while erasing it; leave the earlier address intact. -/
theorem continue_one {reversed : List Bool} (safe : SafeDispatch 0 reversed) (zeros r : Nat) :
    Reaches literal
      (fromLeft continueOne (pack (List.replicate zeros false) (push true (pack reversed 1))) r)
      ⟨root, 1, pack reversed.reverse (push false (pack (List.replicate zeros false) r))⟩ := by
  have enter := Reaches.scanLeft continueSkipZero zeros (push true (pack reversed 1)) r
  have clear := Reaches.left' continueSkipOne (pack reversed 1) (pack (List.replicate zeros false) r)
  have back := continue_zero (word := reversed.reverse) (by simpa using safe)
    (push false (pack (List.replicate zeros false) r))
  rw [List.reverse_reverse] at back
  exact enter.trans (clear.trans back)

end I0451.Runtime
