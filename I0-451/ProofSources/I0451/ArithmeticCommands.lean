module
public import I0451.ArithmeticAxioms
public import I0451.ArithmeticDispatchTree

/-! All five literal commands, including their exact reads and returns
to the common command boundary in any arithmetic model. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def CommandReady (s : Fin 9 → V) : Prop :=
  s axiomIndex = 0 ∧ s scratchOne = 0 ∧ s scratchTwo = 0

def boundaryRegisters (next top stack operand cache queue : V) : Fin 9 → V := fun i =>
  match i.val with
  | 0 => next
  | 1 => top
  | 2 => stack
  | 4 => operand
  | 5 => cache
  | 8 => queue
  | _ => 0

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem CommandReady.boundaryRegisters {s : Fin 9 → V} (ready : CommandReady s) :
    boundaryRegisters (s nextProof) (s topWff) (s wffStack) (s parameterOne)
      (s parameterTwo) (s proofList) = s := by
  funext j
  rcases index_cases j with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · rfl
  · rfl
  · rfl
  · exact ready.1.symm
  · rfl
  · rfl
  · exact ready.2.1.symm
  · exact ready.2.2.symm
  · rfl

noncomputable def modelPayload (s : Fin 9 → V) : V :=
  if s proofList = 0 then s nextProof else s proofList - 1

noncomputable def modelNextIndex (s : Fin 9 → V) : V :=
  if s proofList = 0 then s nextProof + 1 else s nextProof

noncomputable def modelCommandInput (s : Fin 9 → V) : Fin 9 → V :=
  let argument := cantorRight (modelPayload s)
  putRegister (putRegister (putRegister s nextProof (modelNextIndex s))
    proofList (cantorRight argument)) parameterOne (s parameterOne + cantorLeft argument)

theorem model_beforeDispatch_eq (s : Fin 9 → V) (clean : CommandReady s) :
    modelBeforeDispatch s =
      putRegister (modelCommandInput s) axiomIndex (cantorLeft (modelPayload s)) := by
  by_cases fresh : s proofList = 0
  all_goals
    funext j
    have zero : s 3 = 0 := clean.1
    rw [show s proofList = s 8 from rfl] at fresh
    rcases index_cases j with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [modelBeforeDispatch, modelRead, modelReadFrom, modelAfterLoad, modelCommandInput,
        modelPayload, modelNextIndex, putRegister, fresh, zero,
        nextProof, topWff, wffStack, axiomIndex, parameterOne, parameterTwo, scratchOne, scratchTwo, proofList]

theorem selector_cases (k : V) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ ∃ m, k = m + 4 := by
  by_cases zero : k = 0
  · exact .inl zero
  obtain ⟨a, rfl⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr zero)
  by_cases za : a = 0
  · exact .inr (.inl (by simp [za]))
  obtain ⟨b, rfl⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr za)
  by_cases zb : b = 0
  · exact .inr (.inr (.inl (by subst b; norm_num)))
  obtain ⟨c, rfl⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr zb)
  by_cases zc : c = 0
  · exact .inr (.inr (.inr (.inl (by subst c; norm_num))))
  obtain ⟨m, rfl⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr zc)
  exact .inr (.inr (.inr (.inr ⟨m, by
    simp only [Arithmetic.add_assoc]
    rw [show (1 : V) + (1 + (1 + 1)) = 4 by norm_num]⟩)))

private theorem select_cast (tree : DispatchTree) (k : Nat) :
    modelSelect tree (k : V) = ((tree.select k).1, ((tree.select k).2 : V)) := by
  induction tree generalizing k with
  | command entry => rfl
  | choose entry test next first rest ih =>
    cases k with
    | zero => simp [modelSelect, DispatchTree.select]
    | succ k =>
      simp [modelSelect, DispatchTree.select, Nat.cast_succ, add_tsub_cancel_right, ih]

private theorem select_axiom (m : V) :
    modelSelect commandDispatch (m + 4) = (axCursor, m) := by
  have four : m + 4 = (((m + 1) + 1) + 1) + 1 := by
    simp only [Arithmetic.add_assoc]
    rw [show (1 : V) + (1 + (1 + 1)) = 4 by norm_num]
  rw [four]
  simp [modelSelect, commandDispatch, add_tsub_cancel_right]

noncomputable def modelCommandResult (selector : V) (s : Fin 9 → V) : Option (Fin 9 → V) :=
  if selector = 0 then some (modelMPResult s)
  else if selector = 1 then some (modelDropResult s)
  else if selector = 2 then if s parameterTwo = 1 then none else some (modelNipResult s)
  else if selector = 3 then some (modelExtraResult s)
  else some (modelAxiomResult (putRegister s axiomIndex (selector - 4)))

theorem model_command_dispatch (selector : V) (s : Fin 9 → V) (ready : CommandReady s) :
    match modelCommandResult selector s with
    | some output => ModelEffect (.branch commandDispatch.entry) (putRegister s axiomIndex selector) .normal output
    | none => ∃ output, ModelEffect (.branch commandDispatch.entry) (putRegister s axiomIndex selector) .halt output := by
  classical
  have use {sig : Signal} (sigOK : CommandSignal sig) {out : Fin 9 → V}
      (ran : ModelEffect (.branch (modelSelect commandDispatch selector).1)
        (putRegister s axiomIndex (modelSelect commandDispatch selector).2) sig out) :
      ModelEffect (.branch commandDispatch.entry) (putRegister s axiomIndex selector) sig out := by
    apply model_dispatch commandDispatch_checked _ _ sigOK
    simpa only [putRegister_at, putRegister_overwrite] using ran
  have modeZero : putRegister s axiomIndex 0 = s := by rw [← ready.1, putRegister_read]
  rcases selector_cases selector with eq | eq | eq | eq | ⟨m, eq⟩
  · subst selector
    simp only [modelCommandResult, ite_true]
    apply use (.inl rfl)
    rw [show modelSelect commandDispatch (0 : V) = (mpCursor, 0) from
      by simpa only [commandDispatch_select, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using
        select_cast (V := V) commandDispatch 0, modeZero]
    exact model_mp s ready.2.1 ready.2.2
  · subst selector
    simp [modelCommandResult]
    apply use (.inl rfl)
    rw [show modelSelect commandDispatch (1 : V) = (dropCursor, 0) from
      by simpa only [commandDispatch_select, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using
        select_cast (V := V) commandDispatch 1, modeZero]
    exact model_drop s ready.2.1 ready.2.2
  · subst selector
    have sel : modelSelect commandDispatch (2 : V) = (nipCursor, 0) :=
      by simpa only [commandDispatch_select, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using
        select_cast (V := V) commandDispatch 2
    by_cases contradiction : s parameterTwo = 1
    · simp [modelCommandResult, contradiction]
      refine ⟨clearPair scratchOne parameterTwo (putRegister s scratchOne 1), use (.inr rfl) ?_⟩
      rw [sel, modeZero]
      exact model_nip_halt s ready.2.1 contradiction
    · simp [modelCommandResult, contradiction]
      apply use (.inl rfl)
      rw [sel, modeZero]
      exact model_nip s ready.2.1 ready.2.2 contradiction
  · subst selector
    simp [modelCommandResult]
    apply use (.inl rfl)
    rw [show modelSelect commandDispatch (3 : V) = (extraCursor, 0) from
      by simpa only [commandDispatch_select, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using
        select_cast (V := V) commandDispatch 3, modeZero]
    exact model_extra s ready.1 ready.2.1 ready.2.2
  · subst selector
    have ge : (4 : V) ≤ m + 4 := by simp
    have n0 : m + 4 ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) ge)
    have n1 : m + 4 ≠ 1 := ne_of_gt (lt_of_lt_of_le (by norm_num) ge)
    have n2 : m + 4 ≠ 2 := ne_of_gt (lt_of_lt_of_le ((Nat.cast_lt (α := V)).mpr (by decide : (2 : Nat) < 4)) ge)
    have n3 : m + 4 ≠ 3 := ne_of_gt (lt_of_lt_of_le ((Nat.cast_lt (α := V)).mpr (by decide : (3 : Nat) < 4)) ge)
    simp only [modelCommandResult, ite_eq_right n0, ite_eq_right n1, ite_eq_right n2,
      ite_eq_right n3, add_tsub_cancel_right]
    apply use (.inl rfl)
    rw [select_axiom]
    let r := putRegister s axiomIndex m
    have one : r scratchOne = 0 := (putRegister_other _ (by decide) _).trans ready.2.1
    have two : r scratchTwo = 0 := (putRegister_other _ (by decide) _).trans ready.2.2
    exact model_axiom r one two

noncomputable def modelCommandStep (s : Fin 9 → V) : Option (Fin 9 → V) :=
  modelCommandResult (cantorLeft (modelPayload s)) (modelCommandInput s)

theorem model_command_step (s : Fin 9 → V) (ready : CommandReady s) :
    match modelCommandStep s with
    | some output => ModelEffect mainEdge s .normal output
    | none => ∃ output, ModelEffect mainEdge s .halt output := by
  have clean : CommandReady (modelCommandInput s) := by
    refine ⟨?_, ?_, ?_⟩
    · exact ready.1
    · exact ready.2.1
    · exact ready.2.2
  have ran := model_command_dispatch (cantorLeft (modelPayload s)) (modelCommandInput s) clean
  unfold modelCommandStep
  split
  · rename_i out trace
    rw [trace] at ran
    apply model_main_exec ready.2.1 ready.2.2 (.inl rfl)
    rw [model_beforeDispatch_eq s ready]
    exact ran
  · rename_i trace
    rw [trace] at ran
    obtain ⟨output, result⟩ := ran
    refine ⟨output, model_main_exec ready.2.1 ready.2.2 (.inr rfl) ?_⟩
    rw [model_beforeDispatch_eq s ready]
    exact result

theorem cantorRight_le (n : V) : cantorRight n ≤ n := by
  rw [← cantor_encode_decode n]
  simp only [cantorRight_pair]
  rw [cantor_factor]
  simp

theorem model_command_result_shape {selector : V} {s out : Fin 9 → V}
    (ready : CommandReady s) (step : modelCommandResult selector s = some out) :
    CommandReady out ∧ out nextProof = s nextProof ∧ out proofList ≤ s proofList := by
  unfold modelCommandResult at step
  split at step
  · obtain rfl := (Option.some.inj step).symm
    unfold modelMPResult
    split <;> simpa [CommandReady, modelSaveOperand, modelPushResult, putRegister,
      nextProof, topWff, wffStack, axiomIndex, parameterOne, parameterTwo, scratchOne, scratchTwo, proofList]
      using ready
  · split at step
    · obtain rfl := (Option.some.inj step).symm
      simpa [CommandReady, modelDropResult, modelPushResult, putRegister, nextProof,
        topWff, wffStack, axiomIndex, parameterTwo, scratchOne, scratchTwo, proofList] using ready
    · split at step
      · split at step
        · contradiction
        · obtain rfl := (Option.some.inj step).symm
          simpa [CommandReady, modelNipResult, modelReadFrom, putRegister, nextProof, wffStack,
            axiomIndex, parameterTwo, scratchOne, scratchTwo, proofList] using ready
      · split at step
        · obtain rfl := (Option.some.inj step).symm
          simpa [CommandReady, modelExtraResult, putRegister, nextProof, topWff, wffStack,
            axiomIndex, parameterOne, parameterTwo, scratchOne, scratchTwo, proofList]
            using And.intro ready.2.1 ready.2.2
        · obtain rfl := (Option.some.inj step).symm
          have tail := le_trans (cantorRight_le (cantorRight (s proofList))) (cantorRight_le (s proofList))
          simpa [CommandReady, modelAxiomResult, putRegister, nextProof, topWff, wffStack,
            axiomIndex, parameterOne, parameterTwo, scratchOne, scratchTwo, proofList]
            using And.intro ready.2 tail

theorem model_command_step_shape {s out : Fin 9 → V} (ready : CommandReady s)
    (step : modelCommandStep s = some out) :
    CommandReady out ∧ out nextProof = modelNextIndex s ∧ out proofList ≤ modelPayload s := by
  let input := modelCommandInput s
  have initial : CommandReady input := ready
  have shape := model_command_result_shape initial step
  have next : input nextProof = modelNextIndex s := rfl
  have queue : input proofList = cantorRight (cantorRight (modelPayload s)) := rfl
  exact ⟨shape.1, shape.2.1.trans next, le_trans (shape.2.2.trans_eq queue)
    (le_trans (cantorRight_le _) (cantorRight_le _))⟩

end I0451.Arithmetization
