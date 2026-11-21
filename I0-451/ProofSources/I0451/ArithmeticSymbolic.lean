module
public import I0451.ArithmeticMP
public import I0451.Commands.Symbolic

/-! Interpret the existing symbolic certificates in arithmetic models.
The finite assembly check and symbolic plan are the same ones used for
standard register semantics. -/
@[expose] public section
namespace I0451.Runtime

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Arithmetization

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def CounterExpr.modelEval (s : Fin 9 → V) : CounterExpr → V
  | .input r => s r
  | .number n => (n : V)
  | .add a b => a.modelEval s + b.modelEval s
  | .pair a b => cantor (a.modelEval s) (b.modelEval s)
  | .first p => cantorLeft (p.modelEval s)
  | .second p => cantorRight (p.modelEval s)
  | .scaled a => 4 * a.modelEval s
  | .ifEqual a b yes no => if a.modelEval s = b.modelEval s then yes.modelEval s else no.modelEval s

@[simp] theorem CounterExpr.modelEval_plus (s : Fin 9 → V) (a b : CounterExpr) :
    (a.plus b).modelEval s = a.modelEval s + b.modelEval s := by
  unfold plus
  split <;> simp [modelEval, add_assoc]

@[simp] theorem CounterExpr.modelEval_pairWith (s : Fin 9 → V) (a b : CounterExpr) :
    (a.pairWith b).modelEval s = cantor (a.modelEval s) (b.modelEval s) := by
  unfold pairWith
  split <;> simp [modelEval]

@[simp] theorem CounterExpr.modelEval_left (s : Fin 9 → V) (p : CounterExpr) :
    p.left.modelEval s = cantorLeft (p.modelEval s) := by
  have zero : cantorLeft (0 : V) = 0 := by
    simpa only [cantor_zero] using cantorLeft_pair (0 : V) 0
  unfold left
  split <;> simp [modelEval, zero]

@[simp] theorem CounterExpr.modelEval_right (s : Fin 9 → V) (p : CounterExpr) :
    p.right.modelEval s = cantorRight (p.modelEval s) := by
  have zero : cantorRight (0 : V) = 0 := by
    simpa only [cantor_zero] using cantorRight_pair (0 : V) 0
  unfold right
  split <;> simp [modelEval, zero]

noncomputable def modelTag (n : Nat) (a b : V) : V := modelImp a b + (n : V)

@[simp] theorem CounterExpr.modelEval_tag (n : Nat) (a b : CounterExpr) (s : Fin 9 → V) :
    (CounterExpr.tag n a b).modelEval s = modelTag n (a.modelEval s) (b.modelEval s) := by
  simp [tag, modelEval, modelTag, modelImp]

theorem CounterExpr.modelEval_valueCode (s : Fin 9 → V) (a b c : CounterExpr) :
    (valueCode .number CounterExpr.tag a b c).modelEval s =
      valueCode (fun n => (n : V)) modelTag (a.modelEval s) (b.modelEval s) (c.modelEval s) := by
  simp only [valueCode, modelEval_tag, modelEval]

noncomputable def SymbolicRegisters.modelEval (s : SymbolicRegisters) (input : Fin 9 → V) : Fin 9 → V :=
  fun r => (s r).modelEval input

@[simp] theorem SymbolicRegisters.modelEval_set (s : SymbolicRegisters) (input : Fin 9 → V)
    (r : Fin 9) (v : CounterExpr) :
    (s.set r v).modelEval input = putRegister (s.modelEval input) r (v.modelEval input) := by
  funext j
  by_cases same : j = r <;> simp [modelEval, putRegister, same]

@[simp] theorem SymbolicRegisters.modelEval_push (s : SymbolicRegisters) (input : Fin 9 → V) :
    s.push.modelEval input = modelPushResult (s.modelEval input) := by
  simp [push, modelPushResult, modelEval, CounterExpr.modelEval]

def Operation.modelApplicable (op : Operation) (s : Fin 9 → V) : Prop :=
  op.needsScratch = true → s scratchOne = 0 ∧ s scratchTwo = 0

noncomputable def Operation.modelApply (op : Operation) (s : Fin 9 → V) : Fin 9 → V :=
  match op with
  | .inc r => putRegister s r (s r + 1)
  | .clear r => putRegister s r 0
  | .move source target => modelTransfer source target s
  | .copy source a b => putRegister (modelAddAt (fun j => j == a || j == b) (s source) s) source 0
  | .unpairQueue => writeUnpaired (putRegister s proofList 0)
      (cantor (s scratchOne) (s scratchTwo) + s proofList)
  | .push => modelPushResult s
  | .pushOne => putRegister (modelPushResult s) topWff 1
  | .topIncrementTwo => putRegister s topWff (s topWff + 2)
  | .saveOne => modelSaveOperand s
  | .saveTwo => modelDropResult s
  | .implication => modelImplicationResult s
  | .functionValue =>
    let result := valueCode (fun n => (n : V)) modelTag (s parameterOne) (s parameterTwo) (s axiomIndex)
    putRegister (putRegister (putRegister (putRegister (modelPushResult s) topWff result) parameterOne 0)
      parameterTwo 0) axiomIndex 0
  | .clearOnMatch =>
    let cleared := clearPair scratchOne parameterTwo s
    if s scratchOne = s parameterTwo then putRegister cleared topWff 0 else cleared

theorem Operation.modelEval_symbolic (op : Operation) (s : SymbolicRegisters) (input : Fin 9 → V) :
    (op.symbolic s).modelEval input = op.modelApply (s.modelEval input) := by
  cases op with
  | inc r | clear r | push | pushOne | topIncrementTwo | saveOne | saveTwo | implication =>
    simp [symbolic, modelApply, modelSaveOperand, modelDropResult, modelImplicationResult,
      modelImp, SymbolicRegisters.modelEval, CounterExpr.modelEval]
  | move source target =>
    funext j
    by_cases src : j = source
    · simp [symbolic, modelApply, modelTransfer, putRegister, src, CounterExpr.modelEval]
    · by_cases dst : j = target
      · subst j
        simp [symbolic, modelApply, modelTransfer, putRegister, modelAddAt, src, SymbolicRegisters.modelEval]
      · simp [symbolic, modelApply, modelTransfer, putRegister, modelAddAt, src, dst, SymbolicRegisters.modelEval]
  | copy source a b =>
    funext j
    by_cases zero : j = source
    · simp [symbolic, modelApply, SymbolicRegisters.modelEval, putRegister, zero, CounterExpr.modelEval]
    · simp [symbolic, modelApply, SymbolicRegisters.modelEval, putRegister, modelAddAt, zero]
      split <;> simp_all
  | unpairQueue =>
    simp [symbolic, modelApply, writeUnpaired, CounterExpr.modelEval, SymbolicRegisters.modelEval]
  | functionValue =>
    simp only [symbolic, modelApply, SymbolicRegisters.modelEval_set, SymbolicRegisters.modelEval_push,
      CounterExpr.modelEval_valueCode, CounterExpr.modelEval]
    rfl
  | clearOnMatch =>
    simp only [symbolic, modelApply, clearPair, SymbolicRegisters.modelEval_set, CounterExpr.modelEval]
    let regs := s.modelEval input
    let cleared := putRegister (putRegister regs scratchOne 0) parameterTwo 0
    change putRegister cleared topWff (if regs scratchOne = regs parameterTwo then 0 else regs topWff) =
      if regs scratchOne = regs parameterTwo then putRegister cleared topWff 0 else cleared
    split
    · rfl
    · have unchanged : cleared topWff = regs topWff := by
        rw [show cleared = putRegister (putRegister regs scratchOne 0) parameterTwo 0 from rfl,
          putRegister_other _ (show topWff ≠ parameterTwo by decide),
          putRegister_other _ (show topWff ≠ scratchOne by decide)]
      rw [← unchanged, putRegister_read]

theorem modelEval_symbolicInput (s : Fin 9 → V) (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    (symbolicInput true).modelEval s = s := by
  funext j
  by_cases first : j = scratchOne
  · simp [symbolicInput, SymbolicRegisters.modelEval, first, CounterExpr.modelEval, oneZero]
  · by_cases second : j = scratchTwo
    · simp [symbolicInput, SymbolicRegisters.modelEval, second, CounterExpr.modelEval, twoZero]
    · simp [symbolicInput, SymbolicRegisters.modelEval, first, second, CounterExpr.modelEval]

def ModelBlockCorrect (block : ClosedBlock) : Prop :=
  ∀ s : Fin 9 → V, block.op.modelApplicable s →
    ModelEffect (.branch block.cursor) s .normal (block.op.modelApply s)

private theorem model_run_one {op : Operation} {s t : SymbolicRegisters}
    (ran : symbolicRun [op] s = some t) (input : Fin 9 → V) :
    op.modelApplicable (s.modelEval input) ∧ op.modelApply (s.modelEval input) = t.modelEval input := by
  simp only [symbolicRun] at ran
  split at ran
  · contradiction
  · rename_i ready
    obtain rfl := Option.some.inj ran
    refine ⟨fun needs => ?_, (op.modelEval_symbolic s input).symm⟩
    have scratches : s scratchOne = .number 0 ∧ s scratchTwo = .number 0 := by
      simpa [needs, Bool.not_eq_true, Bool.and_eq_true, beq_iff_eq] using ready
    simp [SymbolicRegisters.modelEval, scratches.1, scratches.2, CounterExpr.modelEval]

private theorem symbolicRun_append (first rest : List Operation) (s : SymbolicRegisters) :
    symbolicRun (first ++ rest) s = (symbolicRun first s).bind (symbolicRun rest) := by
  induction first generalizing s with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.cons_append, symbolicRun]
    split
    · rfl
    · exact ih _

theorem AssemblyPlan.modelEffect {blocks : List ClosedBlock}
    (sound : ∀ b ∈ blocks, ModelBlockCorrect (V := V) b)
    {edge : Edge} {ops : List Operation} (plan : AssemblyPlan blocks edge ops) {s t : SymbolicRegisters}
    (ran : symbolicRun ops s = some t) (input : Fin 9 → V) :
    ModelEffect edge (s.modelEval input) .normal (t.modelEval input) := by
  induction plan generalizing s t with
  | increment r =>
    obtain ⟨_, eq⟩ := model_run_one ran input
    rw [← eq]
    exact ModelEffect.inc r _
  | closed block present same =>
    obtain ⟨ok, eq⟩ := model_run_one ran input
    rw [← eq]
    exact (sound block present _ ok).share same
  | sequence left right _ _ ihLeft ihRight =>
    rw [symbolicRun_append, Option.bind_eq_some_iff] at ran
    obtain ⟨middle, first, last⟩ := ran
    exact ModelEffect.sequence left right (ihLeft first) (ihRight last)

theorem model_assemble_sound {blocks : List ClosedBlock}
    (sound : ∀ b ∈ blocks, ModelBlockCorrect (V := V) b)
    {fuel : Nat} {edge : Edge} {ops : List Operation}
    (extracted : assembleWith blocks fuel edge = some ops) {s t : SymbolicRegisters}
    (ran : symbolicRun ops s = some t) (input : Fin 9 → V) :
    ModelEffect edge (s.modelEval input) .normal (t.modelEval input) :=
  (assemble_plan extracted).modelEffect sound ran input

theorem model_checkFormulaBlock_sound {blocks : List ClosedBlock}
    (sound : ∀ b ∈ blocks, ModelBlockCorrect (V := V) b)
    {fuel : Nat} {entry : Cursor} {initial expected : SymbolicRegisters}
    (checked : checkFormulaBlockWith blocks fuel entry initial expected = true) (input : Fin 9 → V) :
    ModelEffect (.branch entry) (initial.modelEval input) .normal (expected.modelEval input) := by
  unfold checkFormulaBlockWith at checked
  cases plan : assembleWith blocks fuel (.branch entry) with
  | none => simp [plan] at checked
  | some ops =>
    cases ran : symbolicRun ops initial with
    | none => simp [plan, ran] at checked
    | some result =>
      have each : ∀ j : Fin 9, result j = expected j := by
        intro j
        simp only [plan, ran, Option.bind_some, Option.any] at checked
        exact beq_iff_eq.mp (List.all_eq_true.mp checked j (List.mem_finRange j))
      rw [← SymbolicRegisters.ext each]
      exact model_assemble_sound sound plan ran input

end I0451.Runtime
