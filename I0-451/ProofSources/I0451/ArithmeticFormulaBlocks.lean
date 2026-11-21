module
public import I0451.ArithmeticSymbolic
public import I0451.Commands.AxiomExecution
public import I0451.Commands.FunctionValue

/-! Correctness of the closed operations used by AX and EXTRA in
arithmetic models. The assembler still reads the literal decoded graph. -/
@[expose] public section
namespace I0451.Runtime

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Arithmetization

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem model_push_one (s : Fin 9 → V) (applicable : Operation.pushOne.modelApplicable s) :
    ModelEffect (.branch ⟨104,false,false⟩) s .normal (Operation.pushOne.modelApply s) := by
  have pushed := model_stack_push s (applicable rfl).1 (applicable rfl).2
  have one := ModelEffect.inc topWff (modelPushResult s)
  simp only [modelPushResult, putRegister_other _ (show topWff ≠ wffStack by decide),
    putRegister_at, zero_add] at one
  exact ModelEffect.sequence (by decide +kernel) (by decide +kernel) pushed one

private theorem model_top_two (s : Fin 9 → V) :
    ModelEffect (.branch ⟨117,true,false⟩) s .normal (Operation.topIncrementTwo.modelApply s) := by
  let mid := putRegister s topWff (s topWff + 1)
  have one := ModelEffect.inc topWff s
  have two := ModelEffect.inc topWff mid
  have eq : putRegister mid topWff (mid topWff + 1) = Operation.topIncrementTwo.modelApply s := by
    simp only [mid, putRegister_at, putRegister_overwrite, Operation.modelApply, Arithmetic.add_assoc]
    rw [show (1 : V) + 1 = 2 by norm_num]
  rw [eq] at two
  exact ModelEffect.sequence (by decide +kernel) (by decide +kernel) one two

private theorem model_clear_on_match (s : Fin 9 → V) :
    ModelEffect (.branch ⟨447,true,false⟩) s .normal (Operation.clearOnMatch.modelApply s) := by
  let cleared := clearPair scratchOne parameterTwo s
  have compared := (model_compare_cache_gate s).share (target := .branch ⟨90,false,true⟩)
    (sameProgram_sound (fuel := 8) (by decide +kernel))
  by_cases same : s scratchOne = s parameterTwo
  · rw [ite_eq_left same] at compared
    simp only [Operation.modelApply, ite_eq_left same]
    have erased : ModelEffect (.branch ⟨449,true,true⟩) cleared .normal (putRegister cleared topWff 0) :=
      ModelEffect.clear_counter (by decide +kernel) (by decide +kernel) cleared
    exact ModelEffect.sequence (by decide +kernel) (by decide +kernel) compared erased
  · rw [ite_eq_right same] at compared
    simp only [Operation.modelApply, ite_eq_right same]
    exact .leftExit (by decide +kernel) compared rfl

private theorem model_makeClear (cursor : Cursor) (r : Fin 9)
    (dec : outgoing cursor false = some (.instruction (.dec r)))
    (back : outgoing cursor true = some (.instruction (.restart 0))) :
    ModelBlockCorrect (V := V) (makeClear cursor r dec back) :=
  fun s _ => ModelEffect.clear_counter dec back s

private theorem model_makeMove (entry loop : Cursor) (source target : Fin 9) (different : target ≠ source)
    (dec : outgoing entry false = some (.instruction (.dec source)))
    (body : outgoing entry true = some (.branch loop))
    (inc : outgoing loop false = some (.instruction (.inc target)))
    (back : outgoing loop true = some (.instruction (.restart 1))) :
    ModelBlockCorrect (V := V) (makeMove entry loop source target different dec body inc back) :=
  fun s _ => ModelEffect.move_one different dec body inc back s

private theorem model_makeCopy (entry loop body : Cursor) (source a b : Fin 9) (distinct : a ≠ b)
    (keep : (source == a || source == b) = false)
    (dec : outgoing entry false = some (.instruction (.dec source)))
    (bodyEdge : outgoing entry true = some (.branch loop))
    (incEdge : outgoing loop false = some (.branch body))
    (back : outgoing loop true = some (.instruction (.restart 1)))
    (first : outgoing body false = some (.instruction (.inc a)))
    (second : outgoing body true = some (.instruction (.inc b))) :
    ModelBlockCorrect (V := V) (makeCopy entry loop body source a b distinct keep dec bodyEdge incEdge back first second) :=
  fun s _ =>
    ModelEffect.while_add dec bodyEdge incEdge back _ keep (ModelEffect.increment_two distinct first second) s

theorem model_formulaBlocks {block : ClosedBlock} (found : block ∈ formulaBlocks) :
    ModelBlockCorrect (V := V) block := by
  simp only [formulaBlocks, List.mem_cons, List.not_mem_nil, or_false] at found
  rcases found with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun s h => model_stack_push s (h rfl).1 (h rfl).2
  · exact model_push_one
  · exact fun s _ => model_top_two s
  · exact fun s h => model_save_operand s (h rfl).1 (h rfl).2
  · exact fun s h => model_drop s (h rfl).1 (h rfl).2
  · exact fun s h => model_build_imp s (h rfl).1 (h rfl).2
  · intro s _
    exact model_unpair (loop := ⟨44,true,false⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide) (by decide) s
  all_goals first | exact model_makeClear _ _ _ _ | exact model_makeMove _ _ _ _ _ _ _ _ _ |
    exact model_makeCopy _ _ _ _ _ _ _ _ _ _ _ _ _ _ | exact fun s _ => model_clear_on_match s

theorem model_axiom_expression (s : Fin 9 → V) (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    ModelEffect (.branch axCursor) s .normal ((axiomPost (symbolicInput true)).modelEval s) := by
  have ran := model_checkFormulaBlock_sound (fun _ found => model_formulaBlocks found) axiomBlock_checked s
  rwa [modelEval_symbolicInput s oneZero twoZero] at ran

theorem model_function_value (s : Fin 9 → V) (clean : Operation.functionValue.modelApplicable s) :
    ModelEffect (.branch valueCursor) s .normal (Operation.functionValue.modelApply s) := by
  obtain ⟨one, two⟩ := clean rfl
  have ran := model_checkFormulaBlock_sound (fun _ found => model_formulaBlocks found) valueBlock_checked s
  rwa [Operation.modelEval_symbolic, modelEval_symbolicInput s one two] at ran

theorem model_extraBlocks {block : ClosedBlock} (found : block ∈ extraBlocks) :
    ModelBlockCorrect (V := V) block := by
  simp only [extraBlocks, List.mem_cons] at found
  rcases found with rfl | formula
  · exact model_function_value
  · exact model_formulaBlocks formula

end I0451.Runtime
