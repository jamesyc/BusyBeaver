module
public import I0451.Commands.Assembly

/-! Symbolic counter values keep formula codes small during certification.
Pairing and formula tags are interpreted only in the correctness theorem. -/
@[expose] public section
namespace I0451.Runtime

open M6.Source.Cantor

inductive CounterExpr where
  | input (source : Fin 9)
  | number (n : Nat)
  | add (left right : CounterExpr)
  | pair (left right : CounterExpr)
  | first (p : CounterExpr)
  | second (p : CounterExpr)
  | scaled (x : CounterExpr)
  | ifEqual (left right yes no : CounterExpr)
  deriving DecidableEq, Repr

def CounterExpr.eval (input : Registers) : CounterExpr → Nat
  | .input r => input r
  | .number n => n
  | .add a b => a.eval input + b.eval input
  | .pair a b => M6.Source.Cantor.pair (a.eval input) (b.eval input)
  | .first a => (decode (a.eval input)).1
  | .second a => (decode (a.eval input)).2
  | .scaled a => 4 * a.eval input
  | .ifEqual a b y n => if a.eval input = b.eval input then y.eval input else n.eval input

def CounterExpr.plus : CounterExpr → CounterExpr → CounterExpr
  | .number a, .number b => .number (a + b)
  | a, .number 0 => a
  | .number 0, b => b
  | .add a (.number n), .number (m + 1) => .add a (.number (n + (m + 1)))
  | a, b => .add a b

@[simp] theorem CounterExpr.eval_plus (s : Registers) (a b : CounterExpr) :
    (a.plus b).eval s = a.eval s + b.eval s := by
  unfold plus
  split <;> simp [eval, Nat.add_assoc]

def CounterExpr.pairWith : CounterExpr → CounterExpr → CounterExpr
  | .number 0, .number 0 => .number 0
  | a, b => .pair a b

@[simp] theorem CounterExpr.eval_pairWith (s : Registers) (a b : CounterExpr) :
    (a.pairWith b).eval s = M6.Source.Cantor.pair (a.eval s) (b.eval s) := by
  unfold pairWith
  split <;> rfl

def CounterExpr.tag (n : Nat) (a b : CounterExpr) : CounterExpr :=
  (CounterExpr.scaled (a.pairWith b)).plus (.number n)

@[simp] theorem CounterExpr.eval_tag (n : Nat) (a b : CounterExpr) (s : Registers) :
    (CounterExpr.tag n a b).eval s = numericTag n (a.eval s) (b.eval s) := by
  simp [CounterExpr.tag, CounterExpr.eval, numericTag]

theorem CounterExpr.eval_valueCode (s : Registers) (a b c : CounterExpr) :
    (valueCode .number CounterExpr.tag a b c).eval s =
      valueCode id numericTag (a.eval s) (b.eval s) (c.eval s) := by
  simp only [valueCode, CounterExpr.eval_tag, CounterExpr.eval, id_eq]

def CounterExpr.left : CounterExpr → CounterExpr
  | .pair a _ => a
  | .number 0 => .number 0
  | p => .first p

def CounterExpr.right : CounterExpr → CounterExpr
  | .pair _ b => b
  | .number 0 => .number 0
  | p => .second p

@[simp] theorem CounterExpr.eval_left (s : Registers) (p : CounterExpr) :
    p.left.eval s = (decode (p.eval s)).1 := by
  unfold left
  split
  · simp [eval, decode_pair]
  · rfl
  · rfl

@[simp] theorem CounterExpr.eval_right (s : Registers) (p : CounterExpr) :
    p.right.eval s = (decode (p.eval s)).2 := by
  unfold right
  split
  · simp [eval, decode_pair]
  · rfl
  · rfl

structure SymbolicRegisters where
  entries : Vector CounterExpr 9

instance : CoeFun SymbolicRegisters (fun _ => Fin 9 → CounterExpr) where
  coe s r := s.entries[r.val]

def SymbolicRegisters.ofFn (f : Fin 9 → CounterExpr) : SymbolicRegisters := ⟨Vector.ofFn f⟩

@[simp] theorem SymbolicRegisters.ofFn_at (f : Fin 9 → CounterExpr) (r : Fin 9) :
    ofFn f r = f r := by
  change (Vector.ofFn f)[r.val] = f r
  simp

theorem SymbolicRegisters.ext {a b : SymbolicRegisters} (h : ∀ r : Fin 9, a r = b r) : a = b := by
  cases a with
  | mk left =>
    cases b with
    | mk right =>
      congr 1
      exact Vector.ext fun i hi => h ⟨i, hi⟩

def SymbolicRegisters.set (s : SymbolicRegisters) (r : Fin 9) (value : CounterExpr) : SymbolicRegisters :=
  ⟨s.entries.set r.val value⟩

@[simp] theorem SymbolicRegisters.set_at (s : SymbolicRegisters) (r j : Fin 9) (value : CounterExpr) :
    s.set r value j = if j = r then value else s j := by
  change (s.entries.set r.val value)[j.val] = if j = r then value else s j
  by_cases same : j = r
  · subst j
    simp
  · have diff : r.val ≠ j.val := fun eq => same ((Fin.eq_of_val_eq eq).symm)
    simp [same, diff]

def SymbolicRegisters.eval (s : SymbolicRegisters) (input : Registers) : Registers :=
  fun j => (s j).eval input

@[simp] theorem SymbolicRegisters.eval_set (s : SymbolicRegisters) (input : Registers)
    (r : Fin 9) (v : CounterExpr) : (s.set r v).eval input = putRegister (s.eval input) r (v.eval input) := by
  funext j
  by_cases same : j = r <;> simp [eval, putRegister, same]

def SymbolicRegisters.push (s : SymbolicRegisters) : SymbolicRegisters :=
  (s.set topWff (.number 0)).set wffStack ((s topWff).pairWith (s wffStack))

@[simp] theorem SymbolicRegisters.eval_push (s : SymbolicRegisters) (input : Registers) :
    s.push.eval input = pushResult (s.eval input) := by
  simp [push, pushResult, eval, CounterExpr.eval]

def Operation.symbolic (op : Operation) (s : SymbolicRegisters) : SymbolicRegisters :=
  match op with
  | .inc r => s.set r ((s r).plus (.number 1))
  | .clear r => s.set r (.number 0)
  | .move source target => (s.set target ((s target).plus (s source))).set source (.number 0)
  | .copy source a b =>
    .ofFn (fun j => if j = source then .number 0
      else if j == a || j == b then (s j).plus (s source) else s j)
  | .unpairQueue =>
    let code := ((s scratchOne).pairWith (s scratchTwo)).plus (s proofList)
    ((s.set proofList (.number 0)).set scratchOne code.left).set scratchTwo code.right
  | .push => s.push
  | .pushOne => s.push.set topWff (.number 1)
  | .topIncrementTwo => s.set topWff ((s topWff).plus (.number 2))
  | .saveOne => s.push.set topWff (s parameterOne)
  | .saveTwo => s.push.set topWff (s parameterTwo)
  | .implication =>
    let stack := s wffStack
    (s.set wffStack stack.right).set topWff (.scaled (stack.left.pairWith (s topWff)))
  | .functionValue =>
    let result := valueCode .number CounterExpr.tag (s parameterOne) (s parameterTwo) (s axiomIndex)
    (s.push.set topWff result).set parameterOne (.number 0)
      |>.set parameterTwo (.number 0) |>.set axiomIndex (.number 0)
  | .clearOnMatch =>
    let cleared := (s.set scratchOne (.number 0)).set parameterTwo (.number 0)
    cleared.set topWff (.ifEqual (s scratchOne) (s parameterTwo) (.number 0) (s topWff))

theorem Operation.eval_symbolic (op : Operation) (s : SymbolicRegisters) (input : Registers) :
    (op.symbolic s).eval input = op.apply (s.eval input) := by
  cases op with
  | inc r => simp [symbolic, apply, SymbolicRegisters.eval, CounterExpr.eval]
  | clear r => simp [symbolic, apply, SymbolicRegisters.eval_set, CounterExpr.eval]
  | move source target =>
    funext j
    by_cases src : j = source
    · simp [symbolic, apply, transferOne, putRegister, src, CounterExpr.eval]
    · by_cases dst : j = target
      · subst j
        simp [symbolic, apply, transferOne, putRegister, addAt, src,
          SymbolicRegisters.eval]
      · simp [symbolic, apply, transferOne, putRegister, addAt, src, dst,
          SymbolicRegisters.eval]
  | copy source a b =>
    funext j
    by_cases zero : j = source
    · simp [symbolic, apply, SymbolicRegisters.eval, putRegister, zero, CounterExpr.eval]
    · simp [symbolic, apply, SymbolicRegisters.eval, putRegister, addAt, zero]
      split <;> simp_all
  | unpairQueue =>
    simp [symbolic, apply, unpairPost, SymbolicRegisters.eval_set, CounterExpr.eval_plus,
      CounterExpr.eval_left, CounterExpr.eval_right, CounterExpr.eval_pairWith, CounterExpr.eval,
      SymbolicRegisters.eval]
  | push => exact SymbolicRegisters.eval_push s input
  | pushOne => simp only [symbolic, apply, SymbolicRegisters.eval_set, SymbolicRegisters.eval_push, CounterExpr.eval]
  | topIncrementTwo => simp only [symbolic, apply, SymbolicRegisters.eval_set, CounterExpr.eval_plus, CounterExpr.eval]; rfl
  | saveOne => simp [symbolic, apply, saveOperand, SymbolicRegisters.eval]
  | saveTwo => simp [symbolic, apply, dropResult, SymbolicRegisters.eval]
  | implication =>
    simp [symbolic, apply, implicationResult, Logic.imp, SymbolicRegisters.eval_set,
      CounterExpr.eval, SymbolicRegisters.eval]
  | functionValue =>
    simp only [symbolic, apply, SymbolicRegisters.eval_set, SymbolicRegisters.eval_push,
      CounterExpr.eval_valueCode, CounterExpr.eval]
    rfl
  | clearOnMatch =>
    simp only [symbolic, apply, clearPair, SymbolicRegisters.eval_set, CounterExpr.eval]
    let regs := s.eval input
    let cleared := putRegister (putRegister regs scratchOne 0) parameterTwo 0
    change putRegister cleared topWff (if regs scratchOne = regs parameterTwo then 0 else regs topWff) =
      if regs scratchOne = regs parameterTwo then putRegister cleared topWff 0 else cleared
    split
    · rfl
    · have unchanged : cleared topWff = regs topWff := by
        unfold cleared
        rw [putRegister_other _ (show topWff ≠ parameterTwo by decide),
          putRegister_other _ (show topWff ≠ scratchOne by decide)]
      rw [← unchanged, putRegister_read]

def symbolicRun : List Operation → SymbolicRegisters → Option SymbolicRegisters
  | [], s => some s
  | op :: rest, s =>
    if op.needsScratch && !(s scratchOne == .number 0 && s scratchTwo == .number 0) then none
    else symbolicRun rest (op.symbolic s)

/-- Run the entire symbolic plan, each time validating the scratch
register precondition required by the next block. -/
theorem symbolicRun_sound {ops : List Operation} {s t : SymbolicRegisters}
    (ran : symbolicRun ops s = some t) (input : Registers) :
    executeOperations ops (s.eval input) = some (t.eval input) := by
  induction ops generalizing s t with
  | nil =>
    cases ran
    rfl
  | cons op next ih =>
    simp only [symbolicRun] at ran
    split at ran
    · contradiction
    · rename_i applicable
      have ok : (op.needsScratch && !((s.eval input) scratchOne == 0 && (s.eval input) scratchTwo == 0)) =
          false := by
        cases needs : op.needsScratch
        · rfl
        · have scratches : s scratchOne = .number 0 ∧ s scratchTwo = .number 0 := by
            simpa [needs, Bool.not_eq_true, Bool.and_eq_true, beq_iff_eq] using applicable
          simp [SymbolicRegisters.eval, scratches.1, scratches.2, CounterExpr.eval]
      have gateFalse : ¬(op.needsScratch && !((s.eval input) scratchOne == 0 &&
          (s.eval input) scratchTwo == 0)) = true := by intro h; cases ok.symm.trans h
      rw [executeOperations, ite_eq_right gateFalse]
      rw [← op.eval_symbolic]
      exact ih ran

def symbolicInput (scratchEmpty : Bool) : SymbolicRegisters :=
  .ofFn fun r => if scratchEmpty && (r == scratchOne || r == scratchTwo) then .number 0 else .input r

theorem eval_symbolicInput (s : Registers) (firstZero : s scratchOne = 0)
    (secondZero : s scratchTwo = 0) : (symbolicInput true).eval s = s := by
  funext j
  by_cases first : j = scratchOne
  · simp [symbolicInput, SymbolicRegisters.eval, first, CounterExpr.eval, firstZero]
  · by_cases second : j = scratchTwo
    · simp [symbolicInput, SymbolicRegisters.eval, second, CounterExpr.eval, secondZero]
    · simp [symbolicInput, SymbolicRegisters.eval, first, second, CounterExpr.eval]

/-- A checked symbolic contract for a whole literal graph entry. -/
def checkFormulaBlockWith (blocks : List ClosedBlock) (fuel : Nat) (entry : Cursor) (initial expected : SymbolicRegisters) : Bool :=
  ((assembleWith blocks fuel (.branch entry)).bind fun ops => symbolicRun ops initial).any
    fun result => (List.finRange 9).all fun j => result j == expected j

abbrev checkFormulaBlock := checkFormulaBlockWith formulaBlocks

theorem checkFormulaBlock_sound {blocks : List ClosedBlock} {fuel : Nat} {entry : Cursor} {initial expected : SymbolicRegisters}
    (checked : checkFormulaBlockWith blocks fuel entry initial expected = true) (input : Registers) :
    Executes (.branch entry) (initial.eval input) .normal (expected.eval input) := by
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
      have same : result = expected := SymbolicRegisters.ext each
      rw [← same]
      exact assemble_sound plan (symbolicRun_sound ran input)

end I0451.Runtime
