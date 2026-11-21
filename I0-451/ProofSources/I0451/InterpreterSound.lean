module
public import I0451.Interpreter

/-! The abstract instruction interpreter implements the literal machine.
The invalid case has no termination interpretation. -/

@[expose] public section
namespace I0451.Runtime

def Realizes (start : Config) : MacroResult → Prop
  | .invalid => True
  | .halt => Halts literal start
  | .next f => Advances literal start f.tape

theorem runRegister_sound {op : RegisterOp} {i : Nat} {word : List Bool}
    (bounded : i < 9) (path : Decoder.IssuePath root true false word (op.issue i))
    (safe : SafeDispatch 0 word.reverse) (gap : Nat) (regs : List Nat) :
    Realizes (frame word gap regs) (runRegister word gap regs op i) := by
  by_cases room : i + 4 ≤ gap
  · cases cutEq : cutRegister i regs with
    | none => simp [runRegister, room, cutEq, Realizes]
    | some cut =>
      rw [runRegister, ite_eq_left room, cutEq]
      obtain ⟨shape, index⟩ := cutRegister_sound cutEq
      obtain ⟨before, last, value, after⟩ := cut
      simp only at shape index
      let spare := gap - (i + 4)
      have gapEq : spare + (i + 1) + 3 = gap := by dsimp [spare]; omega
      cases op with
      | inc =>
        simp only [Realizes, makeFrame_tape, shape]
        cases before with
        | nil =>
          simpa only [List.singleton_append, List.nil_append, gapEq] using increment_register bounded path safe
            spare last value [] after index
        | cons b bs =>
          simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, gapEq]
            using increment_register bounded path safe spare b value (bs ++ [last]) after index
      | dec =>
        cases value with
        | zero =>
          cases cutAddressEq : cutAddress false word.reverse with
          | none => simp [Realizes]
          | some pair =>
            obtain ⟨n, rev⟩ := pair
            by_cases safeRest : SafeDispatch 0 rev
            · have split := cutAddress_sound cutAddressEq
              simp only [Bool.not_false] at split
              have actual := decrement_register_zero bounded path safe safeRest
                spare last n before after index split
              have grown : spare + (i + 1) + 4 + n + 1 = gap + n + 2 := by omega
              simpa only [cutAddressEq, ite_eq_left safeRest, Realizes, makeFrame_tape, shape, gapEq, grown]
                using actual
            · simp [safeRest, Realizes]
        | succ n =>
          simp only [Realizes, makeFrame_tape, shape]
          have grown : spare + (i + 1) + 4 = gap + 1 := by omega
          cases before with
          | nil =>
            simpa only [List.singleton_append, List.nil_append, gapEq, grown] using
              decrement_register_pos bounded path safe spare last n [] after index
          | cons b bs =>
            simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, gapEq, grown]
              using decrement_register_pos bounded path safe spare b n (bs ++ [last]) after index
  · simp [runRegister, room, Realizes]

private theorem gap_succ (n r : Nat) :
    push false (pack (List.replicate n false) r) =
      pack (List.replicate (n + 1) false) r := by
  rw [List.replicate_succ, pack_cons]

theorem runJump_sound (start : Config) (q : Nat) (rev : List Bool) (gap : Nat)
    (regs : List Nat)
    (reached : Advances literal start
      (fromLeft q (pack rev 1) (pack (List.replicate gap false) (pack (blocks regs) 0)))) :
    Realizes start (runJump q rev gap regs) := by
  by_cases toZero : q = continueZero
  · subst q
    by_cases safe : SafeDispatch 0 rev
    · have back := continue_zero (word := rev.reverse) (by simpa only [List.reverse_reverse] using safe)
        (pack (List.replicate gap false) (pack (blocks regs) 0))
      rw [List.reverse_reverse] at back
      simpa [runJump, safe, Realizes, frame] using reached.trans back
    · simp [runJump, safe, Realizes]
  · by_cases toOne : q = continueOne
    · subst q
      cases cut : cutAddress true rev with
      | none => simp [runJump, toZero, cut, Realizes]
      | some pair =>
        obtain ⟨n, rest⟩ := pair
        by_cases safe : SafeDispatch 0 rest
        · have split := cutAddress_sound cut
          simp only [Bool.not_true] at split
          rw [split, pack_append, pack_cons] at reached
          have back := continue_one safe n (pack (List.replicate gap false) (pack (blocks regs) 0))
          rw [pack_repeats, gap_succ, Nat.add_comm n gap] at back
          simpa [runJump, toZero, cut, safe, Realizes, frame] using reached.trans back
        · simp [runJump, toZero, cut, safe, Realizes]
    · by_cases toBreak : q = breakOne
      · subst q
        cases cut : cutAddress false rev with
        | none => simp [runJump, toZero, toOne, cut, Realizes]
        | some pair =>
          obtain ⟨n, rest⟩ := pair
          by_cases safe : SafeDispatch 0 rest
          · have split := cutAddress_sound cut
            simp only [Bool.not_false] at split
            rw [split, pack_append, pack_cons] at reached
            have back := break_one safe n (pack (List.replicate gap false) (pack (blocks regs) 0))
            rw [pack_repeats, gap_succ, Nat.add_comm n gap] at back
            simpa [runJump, toZero, toOne, cut, safe, Realizes, frame] using reached.trans back
          · simp [runJump, toZero, toOne, cut, safe, Realizes]
      · simp [runJump, toZero, toOne, toBreak, Realizes]

private theorem halt_label (left right : Nat) : step literal ⟨451, left, right⟩ = none := by
  have stop (b : Bool) : row literal 451 b = 0 := by cases b <;> decide +kernel
  rw [step, stop]

theorem macroStep_sound (f : RegisterFrame) : Realizes f.tape (macroStep f) := by
  cases parsed : Decoder.decode 94 root true false (pack f.word 0) with
  | none => simp [macroStep, parsed, Realizes]
  | some decoded =>
    by_cases fitted : f.word.length ≤ f.slot ∧ decoded.word.length ≤ f.slot ∧ decoded.rest = 0
    · let gap := f.slot - decoded.word.length
      have tapeEq : f.tape = frame decoded.word gap f.regs :=
        f.tape_decoded decoded parsed fitted.1 fitted.2.1 fitted.2.2
      let tail := pack (List.replicate gap false) (pack (blocks f.regs) 0)
      have path := (Decoder.decode_sound parsed).2.2
      obtain ⟨n, pos, _, trace⟩ := path.read 0 tail
      have marker : push true (push false 0) = 1 := rfl
      have reached : Advances literal f.tape (decoded.exit.place (pack decoded.word.reverse 1) tail) :=
        ⟨n, pos, by simpa only [tapeEq, frame, marker, tail] using trace⟩
      cases exitEq : decoded.exit with
      | issue q =>
        by_cases atHalt : q = 451
        · have interrupt : Halts literal f.tape := by
            subst q
            rw [exitEq] at reached
            exact reached.halts (halt_label _ _)
          simpa [macroStep, parsed, fitted, exitEq, atHalt, Realizes] using interrupt
        · by_cases safe : SafeDispatch 0 decoded.word.reverse
          · cases found : registerAddress q with
            | none => simp [macroStep, parsed, fitted, exitEq, atHalt, safe, found, Realizes]
            | some address =>
              obtain ⟨op, i⟩ := address
              obtain ⟨bounded, qEq⟩ := registerAddress_sound found
              have issued : Decoder.IssuePath root true false decoded.word (op.issue i) := by
                rw [exitEq, qEq] at path
                exact path
              have exactRun := runRegister_sound bounded issued safe gap f.regs
              rw [← tapeEq] at exactRun
              simpa only [macroStep, parsed, ite_eq_left fitted, exitEq, ite_eq_right atHalt,
                ite_eq_left safe, found] using exactRun
          · simp [macroStep, parsed, fitted, exitEq, atHalt, safe, Realizes]
      | erase q =>
        cases word : decoded.word.reverse with
        | nil => simp [macroStep, parsed, fitted, exitEq, word, Realizes]
        | cons b earlier =>
          cases b
          · simp [macroStep, parsed, fitted, exitEq, word, Realizes]
          · have atJump : Advances literal f.tape (fromLeft q (pack earlier 1)
                (pack (List.replicate (gap + 1) false) (pack (blocks f.regs) 0))) := by
              rw [exitEq, word] at reached
              simpa only [Decoder.Exit.place, pack_cons, pop_push, gap_succ, tail] using reached
            simpa only [macroStep, parsed, ite_eq_left fitted, exitEq, word] using
              runJump_sound _ q earlier (gap + 1) f.regs atJump
      | fused =>
        cases word : decoded.word.reverse with
        | nil => simp [macroStep, parsed, fitted, exitEq, word, Realizes]
        | cons a inner =>
          cases a
          · simp [macroStep, parsed, fitted, exitEq, word, Realizes]
          · cases inner with
            | nil => simp [macroStep, parsed, fitted, exitEq, word, Realizes]
            | cons b earlier =>
              cases b
              · simp [macroStep, parsed, fitted, exitEq, word, Realizes]
              · have atJump : Advances literal f.tape (fromLeft continueOne (pack earlier 1)
                    (pack (List.replicate (gap + 2) false) (pack (blocks f.regs) 0))) := by
                  rw [exitEq, word] at reached
                  simpa only [Decoder.Exit.place, pack_cons, pop_push, gap_succ, tail] using reached
                simpa only [macroStep, parsed, ite_eq_left fitted, exitEq, word] using
                  runJump_sound _ continueOne earlier (gap + 2) f.regs atJump
    · simp [macroStep, parsed, fitted, Realizes]

end I0451.Runtime
