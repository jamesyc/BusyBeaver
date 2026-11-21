module
public import I0451.ArithmeticModelRun
public import I0451.LeafSemantics

/-! The model-valued interpreter instructions have the same labels and
control effects as the finite register graph. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def modelRegisters (regs : Fin 9 → V) : List V :=
  tapeRegistersWith (fixedBlocks.map (fun n : Nat => (↑n : V))) regs

theorem modelRegisters_length (regs : Fin 9 → V) : (modelRegisters regs).length = 201 := by
  have fixed : fixedBlocks.length = 192 := by decide +kernel
  simp only [modelRegisters, tapeRegistersWith, List.length_append, List.length_map,
    List.length_reverse, List.length_ofFn, fixed]

/-- A model frame with a fixed address is definable whenever its gap
and nine live registers are given by definable functions. -/
theorem modelRegisterFrame_defined {arity : Nat} (word : List Bool) (gap : (Fin arity → V) → V)
    (regs : (Fin arity → V) → Fin 9 → V)
    (gapDefined : 𝚺ᴬ₁.DefinableFunction (V := V) gap)
    (regDefined : ∀ i, 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => regs v i)) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => modelFrame word (gap v) (modelRegisters (regs v))) := by
  let fixed := fixedBlocks.map (fun n : Nat => (fun _ : Fin arity → V => (↑n : V)))
  let live := (List.ofFn (fun i : Fin 9 => fun v : Fin arity → V => regs v i)).reverse
  have fields (f : (Fin arity → V) → V) (present : f ∈ fixed ++ live) :
      𝚺ᴬ₁.DefinableFunction (V := V) f := by
    rcases List.mem_append.mp present with inFixed | inLive
    · obtain ⟨n, _, rfl⟩ := List.mem_map.mp inFixed
      definability
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp inLive)
      exact regDefined i
  have frames := modelFrame_family_definable word gap (fixed ++ live) gapDefined fields
  simpa only [fixed, live, modelRegisters, tapeRegistersWith, List.map_append,
    List.map_map, List.map_reverse, List.map_ofFn, Function.comp_def] using frames

structure ModelRepresents (f : ModelFrame V) (address : Nat) (regs : Fin 9 → V) : Prop where
  good : ModelPermanent f
  address : pack f.word 0 = address
  registers : f.regs = modelRegisters regs

def ModelLeafResult (result : ModelMacroResult V) (signal : Signal)
    (address : Option Nat) (regs : Fin 9 → V) : Prop :=
  match signal with
  | .halt => result = .halt
  | _ => ∃ after, result = .next after ∧ address = some (pack after.word 0) ∧
      after.regs = modelRegisters regs

private theorem decoded_guard {f : ModelFrame V} {regs : Fin 9 → V} {word : List Bool}
    (view : ModelRepresents f (pack word 0) regs) {out : Decoder.Exit}
    (parsed : Decoder.decode 94 root true false (pack word 0) = some ⟨word, 0, out⟩) :
    Decoder.decode 94 root true false (pack f.word 0) = some ⟨word, 0, out⟩ ∧
      ((f.word.length : V) ≤ f.slot ∧ (word.length : V) ≤ f.slot ∧ (0 : Nat) = 0) ∧
      ∀ i : Fin 9, ((i.val + 1 : Nat) : V) + 1 + 1 + 1 ≤ f.slot - (word.length : V) := by
  have width : word.length ≤ 94 := (Decoder.decode_sound parsed).2.1
  have enough : (word.length : V) ≤ f.slot :=
    le_trans (Nat.cast_le.mpr (width.trans (by decide : (94 : Nat) ≤ 107))) view.good.space
  refine ⟨view.address ▸ parsed, ⟨view.good.wordFits, enough, rfl⟩, fun i => ?_⟩
  have fit : word.length + (i.val + 1) + 1 + 1 + 1 ≤ 107 := by have := i.isLt; omega
  have whole : (word.length : V) + (((i.val + 1 : Nat) : V) + 1 + 1 + 1) ≤ f.slot := by
    apply le_trans _ view.good.space
    simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, add_assoc] using
      (Nat.cast_le (α := V)).mpr fit
  have slot : f.slot = (word.length : V) + (f.slot - (word.length : V)) :=
    sub_spec_of_ge enough
  rw [slot] at whole
  exact le_of_add_le_add_left whole

private theorem register_leaf {f : ModelFrame V} {regs : Fin 9 → V} {word : List Bool}
    (view : ModelRepresents f (pack word 0) regs) {q : Nat} {i : Fin 9} {op : RegisterOp}
    (parsed : Decoder.decode 94 root true false (pack word 0) = some ⟨word, 0, .issue q⟩)
    (routes : registerAddress q = some (op, i.val)) (work : q ≠ 451) :
    ∃ (cut : RegisterCut V), cut.value = regs i ∧
      (∀ new, cut.before ++ cut.last :: new :: cut.after = modelRegisters (putRegister regs i new)) ∧
      modelMacroStep f =
        (match op with
        | .inc => .next (makeModelFrame (carry word.reverse).reverse (f.slot - (word.length : V))
          (cut.before ++ cut.last :: (cut.value + 1) :: cut.after))
        | .dec =>
          if cut.value = 0 then
            match cutAddress false word.reverse with
            | none => .invalid
            | some (n, rest) =>
              if SafeDispatch 0 rest then .next (makeModelFrame (carry rest).reverse
                (f.slot - (word.length : V) + (n : V) + 1 + 1) f.regs)
              else .invalid
          else .next (makeModelFrame (carry word.reverse).reverse (f.slot - (word.length : V) + 1)
            (cut.before ++ cut.last :: (cut.value - 1) :: cut.after))) := by
  classical
  obtain ⟨actual, fit, room⟩ := decoded_guard view parsed
  have safe := (Decoder.root_decoded_safe parsed).1
  have enough : i.val + 2 ≤ (modelRegisters regs).length := by
    rw [modelRegisters_length]
    have := i.isLt
    omega
  obtain ⟨cut, found⟩ := cutRegister_exists enough
  refine ⟨cut, cutRegister_value_with found, cutRegister_write_with found, ?_⟩
  have current : cutRegister i.val f.regs = some cut := by rw [view.registers]; exact found
  cases op <;> simp only [modelMacroStep, actual, fit.1, fit.2.1, true_and, ite_true, work, ite_eq_left safe,
    routes, modelRunRegister, ite_eq_left (room i), current, ite_false]
  by_cases zero : cut.value = 0
  · simp only [ite_eq_left zero]
    cases cutAddress false word.reverse with
    | none => rfl
    | some cut =>
      obtain ⟨n, rest⟩ := cut
      by_cases safeRest : SafeDispatch 0 rest <;> simp [safeRest]
  · simp only [ite_eq_right zero]

theorem model_leaf_inc {f : ModelFrame V} {regs : Fin 9 → V} {word : List Bool} {i : Fin 9}
    (view : ModelRepresents f (pack word 0) regs) (path : AtEdge word (.instruction (.inc i))) :
    ModelLeafResult (modelMacroStep f) .normal (returnAddress .normal word.reverse)
      (putRegister regs i (regs i + 1)) := by
  obtain ⟨out, emitted, parsed⟩ := path.emits
  cases emitted with
  | ins q j routes work =>
    obtain ⟨cut, old, writes, step⟩ := register_leaf view parsed routes work
    refine ⟨_, step, rfl, ?_⟩
    rw [old]
    exact writes _

theorem model_leaf_dec_pos {f : ModelFrame V} {regs : Fin 9 → V} {word : List Bool} {i : Fin 9} {value : V}
    (view : ModelRepresents f (pack word 0) regs) (path : AtEdge word (.instruction (.dec i)))
    (positive : regs i = value + 1) :
    ModelLeafResult (modelMacroStep f) .normal (returnAddress .normal word.reverse)
      (putRegister regs i value) := by
  obtain ⟨out, emitted, parsed⟩ := path.emits
  cases emitted with
  | dec q j routes work =>
    obtain ⟨cut, old, writes, step⟩ := register_leaf view parsed routes work
    rw [old, positive] at step
    have live : value + 1 ≠ 0 := by simp
    simp only [ite_eq_right live, add_tsub_cancel_right] at step
    exact ⟨_, step, rfl, writes _⟩

theorem model_leaf_dec_zero {f : ModelFrame V} {regs : Fin 9 → V} {word : List Bool} {i : Fin 9}
    (view : ModelRepresents f (pack word 0) regs) (path : AtEdge word (.instruction (.dec i)))
    (zero : regs i = 0) :
    ModelLeafResult (modelMacroStep f) (.break 0) (returnAddress (.break 0) word.reverse) regs := by
  obtain ⟨exit, emission, parsed⟩ := path.emits
  cases emission with
  | dec q j routes work =>
    obtain ⟨cut, old, _, step⟩ := register_leaf view parsed routes work
    obtain ⟨safe, legal⟩ := Decoder.root_decoded_safe parsed
    obtain ⟨n, rest, found⟩ := Decoder.cutAddress_exists (legal.2 (dec_issued routes))
    have safeRest : SafeDispatch 0 rest := cut_safe safe found
    rw [old, zero] at step
    simp only [ite_true, found, ite_eq_left safeRest] at step
    refine ⟨_, step, ?_, view.registers⟩
    simp [returnAddress, skipDelimiters, found, makeModelFrame]

theorem model_leaf_halt {f : ModelFrame V} {regs : Fin 9 → V} {word : List Bool}
    (view : ModelRepresents f (pack word 0) regs) (path : AtEdge word (.instruction .halt)) :
    ModelLeafResult (modelMacroStep f) .halt none regs := by
  obtain ⟨exit, emission, parsed⟩ := path.emits
  cases emission
  obtain ⟨actual, fit, _⟩ := decoded_guard view parsed
  simp only [ModelLeafResult, modelMacroStep, actual, fit.1, fit.2.1, true_and, ite_true, ite_true]

private theorem single_jump {f : ModelFrame V} {regs : Fin 9 → V} {word : List Bool} {q : Nat}
    (view : ModelRepresents f (pack word 0) regs)
    (parsed : Decoder.decode 94 root true false (pack word 0) = some ⟨word, 0, .erase q⟩)
    {earlier : List Bool} (split : word.reverse = true :: earlier) :
    modelMacroStep f = modelRunJump q earlier (f.slot - (word.length : V) + 1) f.regs := by
  obtain ⟨actual, fit, _⟩ := decoded_guard view parsed
  simp only [modelMacroStep, actual, fit.1, fit.2.1, true_and, ite_true, split]

theorem model_leaf_break {f : ModelFrame V} {regs : Fin 9 → V} {word : List Bool} {depth : Nat}
    (view : ModelRepresents f (pack word 0) regs)
    (path : AtEdge word (.instruction (.break depth))) :
    ModelLeafResult (modelMacroStep f) (.break depth) (returnAddress (.break depth) word.reverse) regs := by
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
  have jump := single_jump view parsed split
  simp only [modelRunJump, ite_eq_right zeroDiff, ite_eq_right oneDiff, ite_true,
    found, ite_eq_left safeRest] at jump
  refine ⟨_, jump, ?_, view.registers⟩
  rw [returnAddress, split, skip_other 0 (by decide : true ≠ false)]
  simp [skipDelimiters, found, makeModelFrame]

private theorem after_restarts {f : ModelFrame V} {regs : Fin 9 → V} {word earlier : List Bool}
    {erased : Nat} {gap : V} (view : ModelRepresents f (pack word 0) regs)
    (result : modelMacroStep f = modelRunJump continueOne earlier gap f.regs)
    (old : word.reverse = List.replicate erased true ++ earlier)
    (space : 0 < earlier.count true) (safe : SafeDispatch 0 earlier) :
    ModelLeafResult (modelMacroStep f) (.restart erased) (returnAddress (.restart erased) word.reverse) regs := by
  obtain ⟨n, rest, found⟩ := Decoder.cutAddress_exists space
  have safeRest : SafeDispatch 0 rest := cut_safe safe found
  have different : continueOne ≠ continueZero := by decide +kernel
  simp only [modelRunJump, ite_eq_right different, ite_true, found, ite_eq_left safeRest] at result
  refine ⟨_, result, ?_, view.registers⟩
  have skip (m : Nat) :
      skipDelimiters (m + 1) true (List.replicate m true ++ earlier) =
        skipDelimiters 1 true earlier := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.replicate_succ, List.cons_append, skip_matching, ih]
  rw [returnAddress, old, skip]
  simp [skipDelimiters, found, makeModelFrame]

theorem model_leaf_restart {f : ModelFrame V} {regs : Fin 9 → V} {word : List Bool} {depth : Nat}
    (view : ModelRepresents f (pack word 0) regs)
    (path : AtEdge word (.instruction (.restart depth))) :
    ModelLeafResult (modelMacroStep f) (.restart depth) (returnAddress (.restart depth) word.reverse) regs := by
  obtain ⟨exit, emission, parsed⟩ := path.emits
  cases emission with
  | restart1 =>
    obtain ⟨safe, legal⟩ := Decoder.root_decoded_safe parsed
    obtain ⟨_, earlier, split, _, _⟩ := legal
    change SafeDispatch 0 word.reverse at safe
    rw [split] at safe
    have step := single_jump view parsed split
    have inner := safe.tail
    simp only [modelRunJump, ite_true, ite_eq_left inner] at step
    refine ⟨_, step, ?_, view.registers⟩
    simp [returnAddress, split, skipDelimiters, cutAddress, makeModelFrame]
  | restart2 =>
    obtain ⟨safe, legal⟩ := Decoder.root_decoded_safe parsed
    obtain ⟨_, earlier, split, _, oneMarker⟩ := legal
    change SafeDispatch 0 word.reverse at safe
    rw [split] at safe
    exact after_restarts view (single_jump view parsed split) split (oneMarker rfl) safe.tail
  | restart3 =>
    obtain ⟨safe, legal⟩ := Decoder.root_decoded_safe parsed
    obtain ⟨earlier, split, oneMarker⟩ := legal
    change SafeDispatch 0 word.reverse at safe
    rw [split] at safe
    have step : modelMacroStep f = modelRunJump continueOne earlier (f.slot - (word.length : V) + 1 + 1) f.regs := by
      obtain ⟨actual, fit, _⟩ := decoded_guard view parsed
      simp only [modelMacroStep, actual, fit.1, fit.2.1, true_and, ite_true, split]
    exact after_restarts view step split oneMarker safe.tail.tail

end I0451.Arithmetization
