module
public import I0451.ArithmeticInput
public import I0451.DispatchCommands

/-! The literal program reads its command and operand and dispatches on
the model-valued selector. The fifth branch receives the unconsumed mode. -/

@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelSelect : DispatchTree → V → Cursor × V
  | .command entry, n => (entry, n)
  | .choose _ _ _ first rest, n =>
    if n = 0 then (first, 0) else modelSelect rest (n - 1)

theorem model_dispatch {tree : DispatchTree} (checked : tree.verified)
    (s finish : Fin 9 → V) {signal : Signal} (boundary : CommandSignal signal)
    (command : ModelEffect (.branch (modelSelect tree (s axiomIndex)).1)
      (putRegister s axiomIndex (modelSelect tree (s axiomIndex)).2) signal finish) :
    ModelEffect (.branch tree.entry) s signal finish := by
  induction tree generalizing s with
  | command entry =>
    simpa only [modelSelect, DispatchTree.entry, putRegister_read] using command
  | choose entry test recurse first rest ih =>
    obtain ⟨testEdge, firstEdge, selectEdge, recurseEdge, callEdge, skipEdge, inner⟩ := checked
    by_cases zero : s axiomIndex = 0
    · simp only [modelSelect, ite_eq_left zero] at command
      have initial : putRegister s axiomIndex 0 = s := by rw [← zero, putRegister_read]
      rw [initial] at command
      have skip : ModelEffect (.branch test) s .normal s :=
        .leftExit selectEdge (.dec_zero axiomIndex s zero) rfl
      have back : signal.rightExit = some signal := by
        rcases boundary with rfl | rfl <;> rfl
      exact .rightExit testEdge firstEdge skip command back
    · obtain ⟨n, positive⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr zero)
      have live : n + 1 ≠ 0 := by simp
      simp only [modelSelect, positive, ite_eq_right live, add_tsub_cancel_right] at command
      let reduced := putRegister s axiomIndex n
      have ready : reduced axiomIndex = n := putRegister_at _ _ _
      have ran : ModelEffect (.branch rest.entry) reduced signal finish := by
        apply ih inner reduced
        simpa only [ready, reduced, putRegister_overwrite] using command
      rcases boundary with rfl | rfl
      · have skipped : ModelEffect (.branch recurse) reduced (.break 0) finish :=
          .rightExit callEdge skipEdge ran (.breakLeaf 0 _) rfl
        have selected : ModelEffect (.branch test) s (.break 0) finish :=
          .rightExit selectEdge recurseEdge (.dec_pos axiomIndex s n positive) skipped rfl
        exact .leftExit testEdge selected rfl
      · have reached : ModelEffect (.branch recurse) reduced .halt finish :=
          .leftExit callEdge ran rfl
        have selected : ModelEffect (.branch test) s .halt finish :=
          .rightExit selectEdge recurseEdge (.dec_pos axiomIndex s n positive) reached rfl
        exact .leftExit testEdge selected rfl

noncomputable def modelBeforeDispatch (s : Fin 9 → V) : Fin 9 → V :=
  modelRead parameterOne (modelRead axiomIndex (modelAfterLoad s))

theorem model_main_exec {s finish : Fin 9 → V} {sig : Signal}
    (s1 : s scratchOne = 0) (s2 : s scratchTwo = 0) (boundary : CommandSignal sig)
    (run : ModelEffect (.branch commandDispatch.entry) (modelBeforeDispatch s) sig finish) :
    ModelEffect mainEdge s sig finish := by
  let queue := modelAfterLoad s
  let op := modelRead axiomIndex queue
  have loadPreserves (r : Fin 9) (pl : r ≠ proofList) (np : r ≠ nextProof) : queue r = s r := by
    unfold queue modelAfterLoad
    split <;> simp [putRegister, pl, np]
  have loadOne : queue scratchOne = 0 := (loadPreserves _ (by decide) (by decide)).trans s1
  have loadTwo : queue scratchTwo = 0 := (loadPreserves _ (by decide) (by decide)).trans s2
  have readPreserves (r : Fin 9) (pl : r ≠ proofList) (ax : r ≠ axiomIndex) : op r = queue r := by
    simp [op, modelRead, modelReadFrom, putRegister, pl, ax]
  have opOne : op scratchOne = 0 := (readPreserves _ (by decide) (by decide)).trans loadOne
  have opTwo : op scratchTwo = 0 := (readPreserves _ (by decide) (by decide)).trans loadTwo
  have back : sig.rightExit = some sig := by
    rcases boundary with rfl | rfl <;> rfl
  have withOperand := ModelEffect.rightExit (cursor := ⟨13,true,true⟩) (by decide +kernel)
    (by decide +kernel) (model_read_operand op opOne opTwo) run back
  have withSelector := ModelEffect.rightExit (cursor := ⟨9,true,true⟩) (by decide +kernel)
    (by decide +kernel) (model_read_selector queue loadOne loadTwo) withOperand back
  exact .rightExit main_load_branch (by decide +kernel) (model_candidate_loader s s1) withSelector back

end I0451.Arithmetization
