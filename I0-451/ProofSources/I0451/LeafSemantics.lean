module
public import I0451.GraphDecoding
public import I0451.RegisterView

/-! Each abstract leaf has the effect of the decoded operation on a
permanent frame. This connects structured program executions to the
literal machine without introducing a second transition table. -/
@[expose] public section
namespace I0451.Runtime

inductive Emission : Instruction → Decoder.Exit → Prop where
  | ins (q : Nat) (i : Fin 9) (routes : registerAddress q = some (.inc, i.val)) (work : q ≠ 451) :
      Emission (.inc i) (.issue q)
  | dec (q : Nat) (i : Fin 9) (routes : registerAddress q = some (.dec, i.val)) (work : q ≠ 451) :
      Emission (.dec i) (.issue q)
  | jump : Emission (.break 0) (.erase breakOne)
  | restart1 : Emission (.restart 0) (.erase continueZero)
  | restart2 : Emission (.restart 1) (.erase continueOne)
  | restart3 : Emission (.restart 2) .fused
  | halt : Emission .halt (.issue 451)

theorem instruction_emission {op : Instruction} {exit : Decoder.Exit}
    (decoded : instruction exit = some op) : Emission op exit := by
  cases exit with
  | issue q =>
    by_cases halt : q = 451
    · subst q
      simp only [instruction, ↓reduceIte, Option.some.injEq] at decoded
      subst op
      exact .halt
    · cases routes : registerAddress q with
      | none => simp [instruction, halt, routes] at decoded
      | some r =>
        obtain ⟨operation, i⟩ := r
        have bounded := (registerAddress_sound routes).1
        cases operation
        · simp only [instruction, ite_eq_right halt, routes, dite_eq_left bounded,
            Option.some.injEq] at decoded
          subst op
          exact .ins q ⟨i, bounded⟩ routes halt
        · simp only [instruction, ite_eq_right halt, routes, dite_eq_left bounded,
            Option.some.injEq] at decoded
          subst op
          exact .dec q ⟨i, bounded⟩ routes halt
  | erase q =>
    by_cases isBreak : q = breakOne
    · subst q
      simp only [instruction, ↓reduceIte, Option.some.injEq] at decoded
      subst op
      exact .jump
    · by_cases toZero : q = continueZero
      · subst q
        simp only [instruction, ite_eq_right isBreak, ↓reduceIte, Option.some.injEq] at decoded
        subst op
        exact .restart1
      · by_cases toOne : q = continueOne
        · subst q
          simp only [instruction, ite_eq_right isBreak, ite_eq_right toZero, ↓reduceIte,
            Option.some.injEq] at decoded
          subst op
          exact .restart2
        · simp [instruction, isBreak, toZero, toOne] at decoded
  | fused =>
    simp only [instruction, Option.some.injEq] at decoded
    subst op
    exact .restart3

/-- The register and address represented by a permanent frame; extra
explicit zeros in an address do not affect its code. -/
structure RepresentsFrame (f : RegisterFrame) (address : Nat) (regs : Registers) : Prop where
  good : Permanent f
  address : pack f.word 0 = address
  values : f.regs = tapeRegisters regs

def LeafResult (result : MacroResult) (signal : Signal)
    (address : Option Nat) (regs : Registers) : Prop :=
  match signal with
  | .halt => result = .halt
  | _ => ∃ after, result = .next after ∧
      address = some (pack after.word 0) ∧ after.regs = tapeRegisters regs

theorem decoded_leaf_guard {f : RegisterFrame} {regs : Registers} {word : List Bool}
    (frame : RepresentsFrame f (pack word 0) regs) {out : Decoder.Exit}
    (parsed : Decoder.decode 94 root true false (pack word 0) = some ⟨word, 0, out⟩) :
    Decoder.decode 94 root true false (pack f.word 0) = some ⟨word, 0, out⟩ ∧
      (f.word.length ≤ f.slot ∧ word.length ≤ f.slot ∧ (0 : Nat) = 0) ∧
      13 ≤ f.slot - word.length := by
  have width := (Decoder.decode_sound parsed).2.1
  change word.length ≤ 94 at width
  have slot := frame.good.space
  exact ⟨frame.address ▸ parsed, ⟨frame.good.wordFits, by omega, rfl⟩, by omega⟩

private theorem run_register_leaf {f : RegisterFrame} {regs : Registers} {word : List Bool}
    (frame : RepresentsFrame f (pack word 0) regs) {q : Nat} {i : Fin 9} {op : RegisterOp}
    (parsed : Decoder.decode 94 root true false (pack word 0) = some ⟨word, 0, .issue q⟩)
    (routes : registerAddress q = some (op, i.val)) (work : q ≠ 451) :
    ∃ (cut : RegisterCut), cut.value = regs i ∧
      (∀ new, cut.before ++ cut.last :: new :: cut.after = tapeRegisters (putRegister regs i new)) ∧
      macroStep f =
        (match op with
        | .inc => .next (makeFrame (carry word.reverse).reverse (f.slot - word.length)
          (cut.before ++ cut.last :: (cut.value + 1) :: cut.after))
        | .dec => match cut.value with
          | value + 1 => .next (makeFrame (carry word.reverse).reverse
              (f.slot - word.length + 1) (cut.before ++ cut.last :: value :: cut.after))
          | 0 => match cutAddress false word.reverse with
            | none => .invalid
            | some (n, rest) =>
              if SafeDispatch 0 rest then .next (makeFrame (carry rest).reverse
                (f.slot - word.length + n + 2) f.regs)
              else .invalid) := by
  obtain ⟨parses, fit, space⟩ := decoded_leaf_guard frame parsed
  obtain ⟨safe, legal⟩ := Decoder.root_decoded_safe parsed
  have room : i.val + 4 ≤ f.slot - word.length := by have := i.isLt; omega
  have enough : i.val + 2 ≤ (tapeRegisters regs).length := by
    rw [tapeRegisters_length]
    have := i.isLt
    omega
  obtain ⟨cut, found⟩ := cutRegister_exists enough
  refine ⟨cut, cutRegister_value found, cutRegister_write found, ?_⟩
  have current : cutRegister i.val f.regs = some cut := by rw [frame.values]; exact found
  cases op <;> simp only [macroStep, parses, fit.1, fit.2.1, true_and, ite_true, ite_eq_right work,
    ite_eq_left safe, routes, runRegister, ite_eq_left room, current] <;> rfl

theorem leaf_inc {f : RegisterFrame} {regs : Registers} {word : List Bool} {i : Fin 9}
    (frame : RepresentsFrame f (pack word 0) regs) (path : AtEdge word (.instruction (.inc i))) :
    LeafResult (macroStep f) .normal (returnAddress .normal word.reverse)
      (putRegister regs i (regs i + 1)) := by
  obtain ⟨out, interpreted, parsed⟩ := path.decode
  generalize eq : Instruction.inc i = op at interpreted
  have emitted := instruction_emission interpreted
  cases emitted with
  | ins q j routes work =>
    cases eq
    obtain ⟨cut, old, writes, step⟩ := run_register_leaf frame parsed routes work
    refine ⟨_, step, rfl, ?_⟩
    rw [old]
    exact writes _
  | dec q j routes work => contradiction
  | jump => contradiction
  | restart1 => contradiction
  | restart2 => contradiction
  | restart3 => contradiction
  | halt => contradiction

theorem leaf_dec_pos {f : RegisterFrame} {regs : Registers} {word : List Bool} {i : Fin 9} {value : Nat}
    (frame : RepresentsFrame f (pack word 0) regs) (path : AtEdge word (.instruction (.dec i)))
    (positive : regs i = value + 1) :
    LeafResult (macroStep f) .normal (returnAddress .normal word.reverse)
      (putRegister regs i value) := by
  obtain ⟨out, interpreted, parsed⟩ := path.decode
  generalize eq : Instruction.dec i = op at interpreted
  have emitted := instruction_emission interpreted
  cases emitted with
  | dec q j routes work =>
    cases eq
    obtain ⟨cut, old, writes, step⟩ := run_register_leaf frame parsed routes work
    rw [old, positive] at step
    exact ⟨_, step, rfl, writes _⟩
  | ins q j routes work => contradiction
  | jump => contradiction
  | restart1 => contradiction
  | restart2 => contradiction
  | restart3 => contradiction
  | halt => contradiction

theorem AtEdge.emits {word : List Bool} {op : Instruction} (path : AtEdge word (.instruction op)) :
    ∃ out, Emission op out ∧
      Decoder.decode 94 root true false (pack word 0) = some ⟨word, 0, out⟩ := by
  obtain ⟨out, interpreted, read⟩ := path.decode
  exact ⟨out, instruction_emission interpreted, read⟩

private theorem legal_tail {a b : List Bool} {n : Nat} (safe : SafeDispatch n (a ++ b)) :
    SafeDispatch 0 b := by
  induction a generalizing n with
  | nil => exact safe.mono (Nat.zero_le _)
  | cons c cs ih => exact ih safe.2

theorem cut_safe {bit : Bool} {rev : List Bool} {n : Nat} {tail : List Bool}
    (safe : SafeDispatch 0 rev) (cut : cutAddress bit rev = some (n, tail)) :
    SafeDispatch 0 tail := by
  have split : rev = (List.replicate n (!bit) ++ [bit]) ++ tail := by
    simpa [List.append_assoc] using cutAddress_sound cut
  exact legal_tail (split ▸ safe)

theorem leaf_dec_zero {f : RegisterFrame} {regs : Registers} {word : List Bool} {i : Fin 9}
    (frame : RepresentsFrame f (pack word 0) regs) (path : AtEdge word (.instruction (.dec i)))
    (zero : regs i = 0) :
    LeafResult (macroStep f) (.break 0) (returnAddress (.break 0) word.reverse) regs := by
  obtain ⟨exit, emission, parsed⟩ := path.emits
  cases emission with
  | dec q j routes work =>
    obtain ⟨cut, old, _, step⟩ := run_register_leaf frame parsed routes work
    obtain ⟨safe, legal⟩ := Decoder.root_decoded_safe parsed
    have hasMarker := legal.2 (dec_issued routes)
    obtain ⟨n, rest, found⟩ := Decoder.cutAddress_exists hasMarker
    have safeRest : SafeDispatch 0 rest := cut_safe safe found
    rw [old, zero] at step
    simp only [found, ite_eq_left safeRest] at step
    refine ⟨_, step, ?_, frame.values⟩
    simp [returnAddress, skipDelimiters, found, makeFrame]

theorem leaf_halt {f : RegisterFrame} {regs : Registers} {word : List Bool}
    (frame : RepresentsFrame f (pack word 0) regs) (path : AtEdge word (.instruction .halt)) :
    LeafResult (macroStep f) .halt none regs := by
  obtain ⟨exit, emission, parsed⟩ := path.emits
  cases emission
  obtain ⟨actual, fit, _⟩ := decoded_leaf_guard frame parsed
  simp only [LeafResult, macroStep, actual, fit.1, fit.2.1, true_and, ite_true]

private theorem single_jump {f : RegisterFrame} {regs : Registers} {word : List Bool} {q : Nat}
    (frame : RepresentsFrame f (pack word 0) regs)
    (parsed : Decoder.decode 94 root true false (pack word 0) = some ⟨word, 0, .erase q⟩)
    {earlier : List Bool} (split : word.reverse = true :: earlier) :
    macroStep f = runJump q earlier (f.slot - word.length + 1) f.regs := by
  obtain ⟨actual, fit, _⟩ := decoded_leaf_guard frame parsed
  simp only [macroStep, actual, fit.1, fit.2.1, true_and, ite_true, split]

theorem leaf_break {f : RegisterFrame} {regs : Registers} {word : List Bool} {depth : Nat}
    (frame : RepresentsFrame f (pack word 0) regs)
    (path : AtEdge word (.instruction (.break depth))) :
    LeafResult (macroStep f) (.break depth) (returnAddress (.break depth) word.reverse) regs := by
  obtain ⟨exit, emission, parsed⟩ := path.emits
  cases emission
  obtain ⟨safe, legal⟩ := Decoder.root_decoded_safe parsed
  obtain ⟨_, earlier, split, zeroMarker, _⟩ := legal
  obtain ⟨n, rest, found⟩ := Decoder.cutAddress_exists (zeroMarker rfl)
  have safeEarlier : SafeDispatch 0 earlier := by
    change SafeDispatch 0 word.reverse at safe
    rw [split] at safe
    exact safe.tail
  have safeRest : SafeDispatch 0 rest := cut_safe safeEarlier found
  have zeroDiff : breakOne ≠ continueZero := by decide +kernel
  have oneDiff : breakOne ≠ continueOne := by decide +kernel
  have jump := single_jump frame parsed split
  simp only [runJump, ite_eq_right zeroDiff, ite_eq_right oneDiff, ↓reduceIte,
    found, ite_eq_left safeRest] at jump
  refine ⟨_, jump, ?_, frame.values⟩
  rw [returnAddress, split, skip_other 0 (by decide : true ≠ false)]
  simp [skipDelimiters, found, makeFrame]

private theorem after_restarts {f : RegisterFrame} {regs : Registers} {word earlier : List Bool}
    {erased gap : Nat} (frame : RepresentsFrame f (pack word 0) regs)
    (result : macroStep f = runJump continueOne earlier gap f.regs)
    (old : word.reverse = List.replicate erased true ++ earlier)
    (space : 0 < earlier.count true) (safe : SafeDispatch 0 earlier) :
    LeafResult (macroStep f) (.restart erased) (returnAddress (.restart erased) word.reverse) regs := by
  obtain ⟨n, rest, found⟩ := Decoder.cutAddress_exists space
  have safeRest : SafeDispatch 0 rest := cut_safe safe found
  have distinct : continueOne ≠ continueZero := by decide +kernel
  simp only [runJump, ite_eq_right distinct, ↓reduceIte, found, ite_eq_left safeRest] at result
  refine ⟨_, result, ?_, frame.values⟩
  have skip (m : Nat) :
      skipDelimiters (m + 1) true (List.replicate m true ++ earlier) =
        skipDelimiters 1 true earlier := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.replicate_succ, List.cons_append, skip_matching, ih]
  rw [returnAddress, old, skip]
  simp [skipDelimiters, found, makeFrame]

theorem leaf_restart {f : RegisterFrame} {regs : Registers} {word : List Bool} {depth : Nat}
    (frame : RepresentsFrame f (pack word 0) regs)
    (path : AtEdge word (.instruction (.restart depth))) :
    LeafResult (macroStep f) (.restart depth) (returnAddress (.restart depth) word.reverse) regs := by
  obtain ⟨exit, emission, parsed⟩ := path.emits
  cases emission with
  | restart1 =>
    obtain ⟨safe, legal⟩ := Decoder.root_decoded_safe parsed
    obtain ⟨_, earlier, split, _, _⟩ := legal
    change SafeDispatch 0 word.reverse at safe
    rw [split] at safe
    have step := single_jump frame parsed split
    have inner := safe.tail
    simp only [runJump, ↓reduceIte, ite_eq_left inner] at step
    refine ⟨_, step, ?_, frame.values⟩
    simp [returnAddress, split, skipDelimiters, cutAddress, makeFrame]
  | restart2 =>
    obtain ⟨safe, legal⟩ := Decoder.root_decoded_safe parsed
    obtain ⟨_, earlier, split, _, oneMarker⟩ := legal
    change SafeDispatch 0 word.reverse at safe
    rw [split] at safe
    exact after_restarts frame (single_jump frame parsed split) split (oneMarker rfl) safe.tail
  | restart3 =>
    obtain ⟨safe, legal⟩ := Decoder.root_decoded_safe parsed
    obtain ⟨earlier, split, oneMarker⟩ := legal
    change SafeDispatch 0 word.reverse at safe
    rw [split] at safe
    have step : macroStep f = runJump continueOne earlier (f.slot - word.length + 2) f.regs := by
      obtain ⟨actual, fit, _⟩ := decoded_leaf_guard frame parsed
      simp only [macroStep, actual, fit.1, fit.2.1, true_and, ite_true, split]
    exact after_restarts frame step split oneMarker safe.tail.tail

end I0451.Runtime
