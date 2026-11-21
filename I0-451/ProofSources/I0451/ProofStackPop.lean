module
public import I0451.CompareCounters

/-! NIP tests the cached contradiction code and, on a miss, pops the
next cached proof from the literal stack. -/
@[expose] public section
namespace I0451.Runtime

open M6.Source.Cantor

def nipCompare : Cursor := ⟨90, false, false⟩
def compareEntry : Cursor := ⟨106, false, false⟩
def compareGuard : Cursor := ⟨107, true, false⟩
def nipCondition : Cursor := ⟨156, false, true⟩
def nipHead : Cursor := ⟨138, false, true⟩
def nipRest : Cursor := ⟨148, true, false⟩
def popEntry : Cursor := ⟨118, true, true⟩

private theorem compare_cache (s : Registers) :
    Executes (.branch compareEntry) s .normal (compareResult scratchOne parameterTwo s) := by
  apply compare_loop (afterFirst := ⟨120, true, false⟩) (testSecond := ⟨132, false, true⟩)
    (mismatch := .branch ⟨133, true, true⟩)
  · decide
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro regs empty
    have move := move_one (entry := ⟨102, false, true⟩) (loop := ⟨116, true, false⟩)
      (source := scratchOne) (target := parameterTwo) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) regs
    let moved := transferOne scratchOne parameterTwo regs
    have inc := Executes.inc parameterTwo moved
    have done := executes_sequence (root := ⟨133, true, true⟩) (by decide +kernel) (by decide +kernel) move inc
    have count : moved parameterTwo = regs scratchOne := by
      simp [moved, transferOne, addAt, putRegister, parameterTwo, scratchOne,
        show regs 5 = 0 from empty]
    have same : putRegister moved parameterTwo (moved parameterTwo + 1) =
        putRegister (putRegister regs scratchOne 0) parameterTwo (regs scratchOne + 1) := by
      rw [count]
      funext j
      by_cases h : j = parameterTwo
      · simp [putRegister, h]
      · simp [moved, transferOne, putRegister, addAt, h]
    rw [same] at done
    exact done

private theorem test_cache (s : Registers) :
    Executes (.branch compareGuard) s
      (if s parameterTwo = 0 then .normal else .break 0) (putRegister s parameterTwo 0) := by
  apply clear_or_skip (cleanup := ⟨121, true, true⟩) (clear := .branch ⟨134, false, true⟩)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact clear_counter (by decide +kernel) (by decide +kernel)

theorem compare_cache_gate (s : Registers) :
    Executes (.branch nipCompare) s
      (if s scratchOne = s parameterTwo then .normal else .break 0)
      (clearPair scratchOne parameterTwo s) := by
  let mid := compareResult scratchOne parameterTwo s
  have compared := compare_cache s
  have tested := test_cache mid
  have count : mid parameterTwo = discrepancy (s scratchOne) (s parameterTwo) :=
    putRegister_at _ _ _
  rw [count] at tested
  have zero_iff : discrepancy (s scratchOne) (s parameterTwo) = 0 ↔
      s scratchOne = s parameterTwo := by unfold discrepancy; omega
  simp only [zero_iff] at tested
  have same : putRegister mid parameterTwo 0 = clearPair scratchOne parameterTwo s := by
    simp [mid, compareResult, clearPair, putRegister_overwrite]
  rw [same] at tested
  refine .rightExit (by decide +kernel) (by decide +kernel) compared tested ?_
  split <;> rfl

theorem literal_nip_halt (s : Registers) (firstZero : s scratchOne = 0) (code : s parameterTwo = 1) :
    ∃ finish, Executes (.branch nipCursor) s .halt finish := by
  let raised := putRegister s scratchOne (s scratchOne + 1)
  let cleared := clearPair scratchOne parameterTwo raised
  have same : raised scratchOne = raised parameterTwo := by
    simp [raised, putRegister, scratchOne, parameterTwo,
      show s 6 = 0 from firstZero, show s 5 = 1 from code]
  have ran := compare_cache_gate raised
  rw [ite_eq_left same] at ran
  have leaf : Executes (.branch nipCondition) raised .halt cleared :=
    .rightExit (by decide +kernel) (by decide +kernel) ran (.halt cleared) rfl
  have identity : Executes (.branch nipRest) raised .halt cleared :=
    .leftExit (by decide +kernel) leaf rfl
  have test : Executes (.branch nipHead) s .halt cleared :=
    .rightExit (by decide +kernel) (by decide +kernel) (.inc scratchOne s) identity rfl
  exact ⟨cleared, .leftExit (by decide +kernel) test rfl⟩

private theorem unpair_stack (s : Registers) :
    Executes (.branch ⟨128, false, true⟩) s .normal (unpairPost wffStack (s wffStack) s) :=
  unpair_graph (loop := ⟨44, true, false⟩) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) s

def nipResult (s : Registers) : Registers := readFrom wffStack parameterTwo (putRegister s parameterTwo 0)

/-- If the cache is not the contradiction, NIP pops exactly one proof. -/
theorem literal_nip (s : Registers) (firstZero : s scratchOne = 0) (secondZero : s scratchTwo = 0)
    (safe : s parameterTwo ≠ 1) : Executes (.branch nipCursor) s .normal (nipResult s) := by
  let raised := putRegister s scratchOne (s scratchOne + 1)
  let cleared := putRegister s parameterTwo 0
  have unequal : raised scratchOne ≠ raised parameterTwo := by
    simp [raised, putRegister, scratchOne, parameterTwo, show s 6 = 0 from firstZero,
      Ne.symm (show s 5 ≠ 1 from safe)]
  have test := compare_cache_gate raised
  rw [ite_eq_right unequal] at test
  have same : clearPair scratchOne parameterTwo raised = cleared := by
    have cancel : putRegister s scratchOne 0 = s := by rw [← firstZero, putRegister_read]
    simp [clearPair, raised, cleared, putRegister_overwrite, cancel]
  rw [same] at test
  have noHalt : Executes (.branch nipCondition) raised .normal cleared :=
    .leftExit (by decide +kernel) test rfl
  let split := unpairPost wffStack (cleared wffStack) cleared
  let stored := transferOne scratchTwo wffStack split
  have prepare := unpair_stack cleared
  have append := move_one (entry := ⟨129, true, true⟩) (loop := ⟨141, true, true⟩)
    (source := scratchTwo) (target := wffStack) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) split
  have pop := executes_sequence (root := popEntry) (by decide +kernel) (by decide +kernel) prepare append
  have read := executes_sequence (root := nipRest) (by decide +kernel) (by decide +kernel) noHalt pop
  have head := executes_sequence (root := nipHead) (by decide +kernel) (by decide +kernel)
    (.inc scratchOne s) read
  have final := move_one (entry := ⟨102, true, true⟩) (loop := ⟨116, true, true⟩)
    (source := scratchOne) (target := parameterTwo) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) stored
  have done := executes_sequence (root := nipCursor) (by decide +kernel) (by decide +kernel) head final
  have s₁ : cleared scratchOne = 0 := by
    rw [show cleared scratchOne = s scratchOne from putRegister_other _ (by decide) _]
    exact firstZero
  have s₂ : cleared scratchTwo = 0 := by
    rw [show cleared scratchTwo = s scratchTwo from putRegister_other _ (by decide) _]
    exact secondZero
  have result := read_transfer (source := wffStack) (target := parameterTwo)
    (by decide) (by decide) (by decide) (by decide) (by decide) cleared s₁ s₂
  simpa only [stored, split, result, nipResult] using done

end I0451.Runtime
