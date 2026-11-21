module
public import I0451.ProofStackPop
public import I0451.GraphSharing
public import I0451.Logic.Formula

/-! The literal MP command builds an implication, tests it against the
cached formula, and, on a match, restores the consequent. -/
@[expose] public section
namespace I0451.Runtime

open M6.Source.Cantor

def saveOperandEntry : Cursor := ⟨91, false, false⟩
def buildImpEntry : Cursor := ⟨105, true, false⟩

def saveOperand (s : Registers) : Registers :=
  putRegister (pushResult s) topWff (s parameterOne)

theorem literal_save_operand (s : Registers) (firstZero : s scratchOne = 0)
    (secondZero : s scratchTwo = 0) :
    Executes (.branch saveOperandEntry) s .normal (saveOperand s) := by
  let pushed := pushResult s
  let copied := putRegister (addAt (fun j => j == scratchOne || j == topWff)
    (pushed parameterOne) pushed) parameterOne 0
  have copy : Executes (.branch ⟨115, false, true⟩) pushed .normal copied := by
    apply while_add (block := ⟨127, true, false⟩) (body := .branch ⟨140, false, true⟩)
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide
    · intro r
      exact increment_two (by decide) (by decide +kernel) (by decide +kernel) r
  have restore := move_one (entry := ⟨33, true, true⟩) (loop := ⟨48, true, true⟩)
    (source := scratchOne) (target := parameterOne) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) copied
  have ran := executes_sequence (root := saveOperandEntry) (by decide +kernel) (by decide +kernel)
    (literal_stack_push s firstZero secondZero)
    (executes_sequence (root := ⟨109, true, false⟩) (by decide +kernel) (by decide +kernel) copy restore)
  have same : transferOne scratchOne parameterOne copied = saveOperand s := by
    funext j
    have fs : s 6 = 0 := firstZero
    by_cases ht : j = topWff
    · subst j
      simp [copied, pushed, transferOne, addAt, putRegister, saveOperand, pushResult,
        topWff, parameterOne, scratchOne, wffStack]
    · by_cases hp : j = parameterOne
      · subst j
        simp [copied, pushed, transferOne, addAt, putRegister, saveOperand, pushResult,
          topWff, parameterOne, scratchOne, wffStack, fs]
      · by_cases hs : j = scratchOne
        · subst j
          simp [transferOne, putRegister, saveOperand, pushResult, topWff,
            scratchOne, wffStack, fs]
        · simp [copied, transferOne, addAt, putRegister, saveOperand, ht, hp, hs, pushed]
  rw [same] at ran
  exact ran

def implicationResult (s : Registers) : Registers :=
  let proof := decode (s wffStack)
  putRegister (putRegister s wffStack proof.2) topWff (Logic.imp proof.1 (s topWff))

private theorem multiply_four (s : Registers) :
    Executes (.branch ⟨131, true, true⟩) s .normal
      (putRegister (addAt (· == topWff) (4 * s scratchTwo) s) scratchTwo 0) := by
  let bump := addAt (· == topWff) 4
  let finish := fun n regs => putRegister (addAt (· == topWff) (4 * n) regs) scratchTwo 0
  apply while_effect (block := ⟨144, true, true⟩) (body := .branch ⟨151, false, true⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bump finish
  · intro t
    let double := fun regs => putRegister regs topWff (regs topWff + 1)
    have first (regs : Registers) : Executes (.branch ⟨117, false, false⟩) regs .normal
        (double (double regs)) :=
      executes_sequence (by decide +kernel) (by decide +kernel) (.inc topWff regs) (.inc topWff _)
    have second := (first (double (double t))).share
      (target := .branch ⟨117, true, false⟩) (sameProgram_sound (fuel := 2) (by decide +kernel))
    have both := executes_sequence (root := ⟨151, false, true⟩) (by decide +kernel) (by decide +kernel)
      (first t) second
    have eq : double (double (double (double t))) = bump t := by
      funext j
      by_cases h : j = topWff <;> simp [double, bump, addAt, putRegister, h, Nat.add_assoc]
    simpa only [eq] using both
  · intro t
    simp [bump, addAt, topWff, scratchTwo]
  · intro t zero
    funext j
    by_cases h : j = scratchTwo <;> simp [finish, putRegister, addAt, h, zero]
  · intro n t _
    funext j
    by_cases hs : j = scratchTwo
    · simp [finish, hs]
    · by_cases ht : j = topWff
      · subst j
        simp [finish, bump, addAt, putRegister, topWff, scratchTwo, Nat.mul_succ]
        omega
      · simp [finish, bump, addAt, putRegister, ht, hs]

theorem literal_build_imp (s : Registers) (firstZero : s scratchOne = 0)
    (secondZero : s scratchTwo = 0) :
    Executes (.branch buildImpEntry) s .normal (implicationResult s) := by
  let unpacked := unpairPost wffStack (s wffStack) s
  let kept := transferOne scratchTwo wffStack unpacked
  let paired := pairedRegisters scratchOne topWff scratchTwo kept
  have unpack : Executes (.branch ⟨128, false, false⟩) s .normal unpacked :=
    unpair_graph (loop := ⟨44, true, false⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide) (by decide) s
  have keep := move_one (entry := ⟨129, true, false⟩) (loop := ⟨141, true, true⟩)
    (source := scratchTwo) (target := wffStack) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) unpacked
  have pairRun := (literal_stack_pair kept).share (target := .branch ⟨130, false, true⟩)
    (sameProgram_sound (fuel := 8) (by decide +kernel))
  have calcImp := executes_sequence (root := ⟨119, true, true⟩) (by decide +kernel) (by decide +kernel)
    pairRun (multiply_four paired)
  have ran := executes_sequence (root := buildImpEntry) (by decide +kernel) (by decide +kernel)
    (executes_sequence (root := ⟨118, false, true⟩) (by decide +kernel) (by decide +kernel) unpack keep)
    calcImp
  have eq : putRegister (addAt (· == topWff) (4 * paired scratchTwo) paired) scratchTwo 0 =
      implicationResult s := by
    have fs : s 6 = 0 := firstZero
    have ss : s 7 = 0 := secondZero
    funext j
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [paired, kept, unpacked, implicationResult, pairedRegisters, transferOne, unpairPost, addAt,
        putRegister, topWff, wffStack, scratchOne, scratchTwo, fs, ss, Logic.imp, show pair 0 0 = 0 from rfl]
  rw [eq] at ran
  exact ran

def mpResult (s : Registers) : Registers :=
  let cleared := putRegister (putRegister s topWff 0) parameterTwo 0
  if s parameterTwo = Logic.imp (s topWff) (s parameterOne) then saveOperand cleared
  else cleared

/-- A literal MP command always returns, preserving the operand and consuming
the cache even when the implication does not match. -/
theorem literal_mp (s : Registers) (firstZero : s scratchOne = 0) (secondZero : s scratchTwo = 0) :
    Executes (.branch mpCursor) s .normal (mpResult s) := by
  let pushed := saveOperand s
  let formed := implicationResult pushed
  let loaded := transferOne topWff scratchOne formed
  let cleared := putRegister (putRegister s topWff 0) parameterTwo 0
  have formedEq : formed = putRegister s topWff (Logic.imp (s topWff) (s parameterOne)) := by
    funext j
    by_cases ht : j = topWff
    · subst j
      simp [formed, pushed, saveOperand, implicationResult, pushResult, putRegister, topWff, wffStack, decode_pair]
    · by_cases hw : j = wffStack
      · subst j
        simp [formed, pushed, saveOperand, implicationResult, pushResult, putRegister, topWff, wffStack, decode_pair]
      · simp [formed, pushed, saveOperand, implicationResult, pushResult, putRegister, ht, hw]
  have fs : pushed scratchOne = 0 := by
    simpa [pushed, saveOperand, pushResult, putRegister, scratchOne, topWff, wffStack] using firstZero
  have ss : pushed scratchTwo = 0 := by
    simpa [pushed, saveOperand, pushResult, putRegister, scratchTwo, topWff, wffStack] using secondZero
  have build := executes_sequence (root := ⟨51, false, true⟩) (by decide +kernel) (by decide +kernel)
    (literal_save_operand s firstZero secondZero) (literal_build_imp pushed fs ss)
  have load := move_one (entry := ⟨69, false, true⟩) (loop := ⟨89, true, false⟩)
    (source := topWff) (target := scratchOne) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) formed
  have tested := (compare_cache_gate loaded).share (target := .branch ⟨90, false, true⟩)
    (sameProgram_sound (fuel := 8) (by decide +kernel))
  have count : loaded scratchOne = Logic.imp (s topWff) (s parameterOne) := by
    simp [loaded, formedEq, transferOne, addAt, putRegister, scratchOne, topWff,
      show s 6 = 0 from firstZero]
  have cached : loaded parameterTwo = s parameterTwo := by
    simp [loaded, formedEq, transferOne, addAt, putRegister, parameterTwo, scratchOne, topWff]
  have clearEq : clearPair scratchOne parameterTwo loaded = cleared := by
    funext j
    by_cases hs : j = scratchOne
    · subst j
      simp [cleared, clearPair, putRegister, scratchOne, topWff, parameterTwo,
        show s 6 = 0 from firstZero]
    · by_cases ht : j = topWff
      · subst j
        simp [cleared, loaded, clearPair, transferOne, putRegister, topWff, scratchOne, parameterTwo]
      · by_cases hp : j = parameterTwo
        · subst j
          simp [cleared, clearPair]
        · simp [cleared, loaded, formedEq, clearPair, transferOne, addAt, putRegister, ht, hs, hp]
  rw [count, cached, clearEq] at tested
  have handled : Executes (.branch ⟨70, true, true⟩) loaded .normal (mpResult s) := by
    by_cases eq : s parameterTwo = Logic.imp (s topWff) (s parameterOne)
    · rw [ite_eq_left eq.symm] at tested
      simp only [mpResult, ite_eq_left eq]
      have saved := literal_save_operand cleared
        (by simpa [cleared, putRegister, topWff, parameterTwo, scratchOne] using firstZero)
        (by simpa [cleared, putRegister, topWff, parameterTwo, scratchTwo] using secondZero)
      exact executes_sequence (by decide +kernel) (by decide +kernel) tested
        (saved.share (target := .branch ⟨91, true, true⟩) (sameProgram_sound (fuel := 8) (by decide +kernel)))
    · have wrong := Ne.symm eq
      rw [ite_eq_right wrong] at tested
      simpa only [mpResult, ite_eq_right eq] using
        (Executes.leftExit (cursor := ⟨70, true, true⟩) (by decide +kernel) tested
          (show (Signal.break 0).leftExit = some .normal from rfl))
  exact executes_sequence (by decide +kernel) (by decide +kernel) build
    (executes_sequence (root := ⟨52, true, true⟩) (by decide +kernel) (by decide +kernel) load handled)

end I0451.Runtime
