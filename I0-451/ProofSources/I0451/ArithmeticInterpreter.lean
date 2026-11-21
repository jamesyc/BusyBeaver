module
public import I0451.ArithmeticFrame

/-! A single interpreter instruction implements the literal table on
model-valued register contents and at a model-valued tape offset. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open I0451.Runtime

structure ModelFrame (V : Type) where
  word : List Bool
  slot : V
  regs : List V

inductive ModelMacroResult (V : Type) where
  | invalid
  | halt
  | next (frame : ModelFrame V)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def makeModelFrame (word : List Bool) (gap : V) (regs : List V) : ModelFrame V :=
  ⟨word, (word.length : V) + gap, regs⟩

noncomputable def ModelFrame.tape (f : ModelFrame V) : V :=
  modelFrame f.word (f.slot - (f.word.length : V)) f.regs

@[simp] theorem makeModelFrame_tape (word : List Bool) (gap : V) (regs : List V) :
    (makeModelFrame word gap regs).tape = modelFrame word gap regs := by
  unfold ModelFrame.tape makeModelFrame
  rw [add_comm]
  simp only [add_tsub_cancel_right]

def ModelRealizes (start : V) : ModelMacroResult V → Prop
  | .invalid => True
  | .halt => ∃ n : V, Terminal literal (trace literal n start)
  | .next f => ModelReaches literal start f.tape

noncomputable def modelRunRegister (word : List Bool) (gap : V) (regs : List V)
    (op : RegisterOp) (i : Nat) : ModelMacroResult V := by
  classical
  exact
    if ((i + 1 : Nat) : V) + 1 + 1 + 1 ≤ gap then
      match cutRegister i regs with
      | none => .invalid
      | some cut =>
        let next := (carry word.reverse).reverse
        match op with
        | .inc => .next (makeModelFrame next gap
            (cut.before ++ cut.last :: (cut.value + 1) :: cut.after))
        | .dec =>
          if cut.value = 0 then
            match cutAddress false word.reverse with
            | none => .invalid
            | some (n, rest) =>
              if SafeDispatch 0 rest then
                .next (makeModelFrame (carry rest).reverse (gap + (n : V) + 1 + 1) regs)
              else .invalid
          else .next (makeModelFrame next (gap + 1)
            (cut.before ++ cut.last :: (cut.value - 1) :: cut.after))
    else .invalid

attribute [local irreducible] modelRepeat modelPush modelFromLeft modelConfig trace modelFrame

theorem model_runRegister_sound {op : RegisterOp} {i : Nat} {word : List Bool}
    (bounded : i < 9) (path : Decoder.IssuePath root true false word (op.issue i))
    (safe : SafeDispatch 0 word.reverse) (gap : V) (regs : List V) :
    ModelRealizes (modelFrame word gap regs) (modelRunRegister word gap regs op i) := by
  classical
  by_cases room : ((i + 1 : Nat) : V) + 1 + 1 + 1 ≤ gap
  · cases cutEq : cutRegister i regs with
    | none =>
      rw [modelRunRegister, ite_eq_left room, cutEq]
      exact True.intro
    | some cut =>
      rw [modelRunRegister, ite_eq_left room, cutEq]
      obtain ⟨shape, index⟩ := cutRegister_sound cutEq
      obtain ⟨before, last, value, after⟩ := cut
      simp only at shape index
      let spare := gap - (((i + 1 : Nat) : V) + 1 + 1 + 1)
      have gapEq : spare + ((i + 1 : Nat) : V) + 1 + 1 + 1 = gap := by
        have restored := sub_add_self_of_le room
        simpa only [spare, add_assoc] using restored
      cases op with
      | inc =>
        simp only [ModelRealizes, makeModelFrame_tape, shape]
        cases before with
        | nil =>
          simpa only [List.singleton_append, List.nil_append, gapEq] using
            model_increment_register bounded path safe spare last value [] after index
        | cons b bs =>
          simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, gapEq]
            using model_increment_register bounded path safe spare b value (bs ++ [last]) after index
      | dec =>
        by_cases empty : value = 0
        · subst value
          cases cutAddressEq : cutAddress false word.reverse with
          | none => simp [ModelRealizes]
          | some pair =>
            obtain ⟨n, rev⟩ := pair
            by_cases safeRest : SafeDispatch 0 rev
            · have split := cutAddress_sound cutAddressEq
              simp only [Bool.not_false] at split
              have actual := model_decrement_register_zero bounded path safe safeRest
                spare last n before after index split
              have grown : spare + ((i + 1 : Nat) : V) + 1 + 1 + 1 + 1 + (n : V) + 1 =
                  gap + (n : V) + 1 + 1 := by rw [gapEq]; ac_rfl
              rw [grown] at actual
              simpa only [ite_true, cutAddressEq, ite_eq_left safeRest, ModelRealizes,
                makeModelFrame_tape, shape, gapEq] using actual
            · simp [safeRest, ModelRealizes]
        · obtain ⟨n, rfl⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr empty)
          have minus : n + 1 - 1 = n := add_tsub_cancel_right n 1
          simp only [ite_eq_right empty, ModelRealizes, makeModelFrame_tape, shape, minus]
          cases before with
          | nil =>
            simpa only [List.singleton_append, List.nil_append, gapEq] using
              model_decrement_register_pos bounded path safe spare last n [] after index
          | cons b bs =>
            simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, gapEq]
              using model_decrement_register_pos bounded path safe spare b n (bs ++ [last]) after index
  · rw [modelRunRegister, ite_eq_right room]
    exact True.intro

noncomputable def modelRunJump (q : Nat) (rev : List Bool) (gap : V) (regs : List V) :
    ModelMacroResult V :=
  if q = continueZero then
    if SafeDispatch 0 rev then .next (makeModelFrame rev.reverse gap regs) else .invalid
  else if q = continueOne then
    match cutAddress true rev with
    | none => .invalid
    | some (n, rest) =>
      if SafeDispatch 0 rest then .next (makeModelFrame rest.reverse (gap + (n : V) + 1) regs)
      else .invalid
  else if q = breakOne then
    match cutAddress false rev with
    | none => .invalid
    | some (n, rest) =>
      if SafeDispatch 0 rest then .next (makeModelFrame (carry rest).reverse (gap + (n : V) + 1) regs)
      else .invalid
  else .invalid

theorem model_runJump_sound (start : V) (q : Nat) (rev : List Bool) (gap : V) (regs : List V)
    (reached : ModelReaches literal start
      (modelFromLeft q (modelPack rev 1) (modelRepeat false gap (modelBlocks regs 0)))) :
    ModelRealizes start (modelRunJump q rev gap regs) := by
  by_cases direct : q = continueZero
  · subst q
    by_cases safe : SafeDispatch 0 rev
    · have same := model_continue_zero (word := rev.reverse)
        (by simpa only [List.reverse_reverse] using safe) (modelRepeat false gap (modelBlocks regs 0))
      rw [List.reverse_reverse] at same
      simpa only [modelRunJump, ite_true, ite_eq_left safe, ModelRealizes, makeModelFrame_tape, modelFrame]
        using reached.trans same
    · simp [modelRunJump, safe, ModelRealizes]
  · by_cases toOne : q = continueOne
    · subst q
      cases cut : cutAddress true rev with
      | none => simp [modelRunJump, direct, cut, ModelRealizes]
      | some pair =>
        obtain ⟨n, rest⟩ := pair
        by_cases safe : SafeDispatch 0 rest
        · have split := cutAddress_sound cut
          simp only [Bool.not_true] at split
          rw [split, modelPack_append, modelPack_cons, ← modelRepeat_nat] at reached
          have back := model_continue_one safe (n : V) (modelRepeat false gap (modelBlocks regs 0))
          rw [← modelRepeat_add, ← modelRepeat_succ] at back
          simpa only [modelRunJump, ite_eq_right direct, ite_true, cut, ite_eq_left safe,
            ModelRealizes, makeModelFrame_tape, modelFrame] using reached.trans back
        · simp [modelRunJump, direct, cut, safe, ModelRealizes]
    · by_cases jump : q = breakOne
      · subst q
        cases cut : cutAddress false rev with
        | none => simp [modelRunJump, direct, toOne, cut, ModelRealizes]
        | some pair =>
          obtain ⟨n, rest⟩ := pair
          by_cases safe : SafeDispatch 0 rest
          · have split := cutAddress_sound cut
            simp only [Bool.not_false] at split
            rw [split, modelPack_append, modelPack_cons, ← modelRepeat_nat] at reached
            have back := model_break_one safe (n : V) (modelRepeat false gap (modelBlocks regs 0))
            rw [← modelRepeat_add, ← modelRepeat_succ] at back
            simpa only [modelRunJump, ite_eq_right direct, ite_eq_right toOne, ite_true, cut,
              ite_eq_left safe, ModelRealizes, makeModelFrame_tape, modelFrame] using reached.trans back
          · simp [modelRunJump, direct, toOne, cut, safe, ModelRealizes]
      · simp [modelRunJump, direct, toOne, jump, ModelRealizes]

/-- Decode the finite instruction address and execute its macro on the
register data in the arithmetic model. -/
noncomputable def modelMacroStep (f : ModelFrame V) : ModelMacroResult V := by
  classical
  exact
    match Decoder.decode 94 root true false (pack f.word 0) with
    | none => .invalid
    | some decoded =>
      if (f.word.length : V) ≤ f.slot ∧ (decoded.word.length : V) ≤ f.slot ∧ decoded.rest = 0 then
        let gap := f.slot - (decoded.word.length : V)
        match decoded.exit with
        | .issue q =>
          if q = 451 then .halt
          else if SafeDispatch 0 decoded.word.reverse then
            match registerAddress q with
            | none => .invalid
            | some (op, i) => modelRunRegister decoded.word gap f.regs op i
          else .invalid
        | .erase q =>
          match decoded.word.reverse with
          | true :: earlier => modelRunJump q earlier (gap + 1) f.regs
          | _ => .invalid
        | .fused =>
          match decoded.word.reverse with
          | true :: true :: earlier => modelRunJump continueOne earlier (gap + 1 + 1) f.regs
          | _ => .invalid
      else .invalid

theorem modelMacroStep_sound (f : ModelFrame V) :
    ModelRealizes f.tape (modelMacroStep f) := by
  classical
  cases parsed : Decoder.decode 94 root true false (pack f.word 0) with
  | none => simp [modelMacroStep, parsed, ModelRealizes]
  | some decoded =>
    by_cases fitted : (f.word.length : V) ≤ f.slot ∧
      (decoded.word.length : V) ≤ f.slot ∧ decoded.rest = 0
    · let gap := f.slot - (decoded.word.length : V)
      have layout : f.tape = modelFrame decoded.word gap f.regs :=
        modelFrame_decoded parsed fitted.1 fitted.2.1 fitted.2.2 f.regs
      let tail := modelRepeat false gap (modelBlocks f.regs 0)
      have path := (Decoder.decode_sound parsed).2.2
      have reached : ModelReaches literal f.tape
          (modelExit decoded.exit (modelPack decoded.word.reverse 1) tail) := by
        rw [layout, modelFrame]
        exact model_decoder_root path tail
      cases leaf : decoded.exit with
      | issue q =>
        by_cases stop : q = 451
        · subst q
          rw [leaf] at reached
          obtain ⟨n, arrived⟩ := reached
          have halts : ∃ t : V, Terminal literal (trace literal t f.tape) :=
            ⟨n, by rw [arrived]; exact terminal_halt_label _ _⟩
          simpa only [modelMacroStep, parsed, ite_eq_left fitted, leaf, ite_true, ModelRealizes]
            using halts
        · by_cases safe : SafeDispatch 0 decoded.word.reverse
          · cases reg : registerAddress q with
            | none =>
              simp only [modelMacroStep, parsed, ite_eq_left fitted, leaf, ite_eq_right stop, ite_eq_left safe,
                reg, ModelRealizes]
            | some addr =>
              obtain ⟨op, i⟩ := addr
              obtain ⟨valid, phys⟩ := registerAddress_sound reg
              have issued : Decoder.IssuePath root true false decoded.word (op.issue i) := by
                rw [leaf, phys] at path
                exact path
              have exact := model_runRegister_sound valid issued safe gap f.regs
              rw [← layout] at exact
              simpa only [modelMacroStep, parsed, ite_eq_left fitted, leaf, ite_eq_right stop,
                ite_eq_left safe, reg] using exact
          · simp only [modelMacroStep, parsed, ite_eq_left fitted, leaf, ite_eq_right stop, ite_eq_right safe,
              ModelRealizes]
      | erase q =>
        cases wordEq : decoded.word.reverse with
        | nil =>
          simp only [modelMacroStep, parsed, ite_eq_left fitted, leaf, wordEq, ModelRealizes]
        | cons b earlier =>
          cases b
          · simp only [modelMacroStep, parsed, ite_eq_left fitted, leaf, wordEq, ModelRealizes]
          · have jump : ModelReaches literal f.tape
                (modelFromLeft q (modelPack earlier 1) (modelRepeat false (gap + 1) (modelBlocks f.regs 0))) := by
              simpa only [leaf, wordEq, modelExit, modelPack_cons, modelDiv_push, tail, modelRepeat_succ]
                using reached
            simpa only [modelMacroStep, parsed, ite_eq_left fitted, leaf, wordEq] using
              model_runJump_sound _ q earlier (gap + 1) f.regs jump
      | fused =>
        cases wordEq : decoded.word.reverse with
        | nil =>
          simp only [modelMacroStep, parsed, ite_eq_left fitted, leaf, wordEq, ModelRealizes]
        | cons a suffix =>
          cases a with
          | false =>
            simp only [modelMacroStep, parsed, ite_eq_left fitted, leaf, wordEq, ModelRealizes]
          | true =>
            cases suffix with
            | nil =>
              simp only [modelMacroStep, parsed, ite_eq_left fitted, leaf, wordEq, ModelRealizes]
            | cons b earlier =>
              cases b with
              | false =>
                simp only [modelMacroStep, parsed, ite_eq_left fitted, leaf, wordEq, ModelRealizes]
              | true =>
                have jump : ModelReaches literal f.tape
                    (modelFromLeft continueOne (modelPack earlier 1)
                      (modelRepeat false (gap + 1 + 1) (modelBlocks f.regs 0))) := by
                  simpa only [leaf, wordEq, modelExit, modelPack_cons, modelDiv_push, tail, modelRepeat_succ]
                    using reached
                simpa only [modelMacroStep, parsed, ite_eq_left fitted, leaf, wordEq] using
                  model_runJump_sound _ continueOne earlier (gap + 1 + 1) f.regs jump
    · simp only [modelMacroStep, parsed, ite_eq_right fitted, ModelRealizes]

end I0451.Arithmetization
