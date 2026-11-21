module
public import I0451.ModusPonens

/-! Closed blocks in the formula-building part of the literal graph.
Each contract names a literal entry and proves its effect for arbitrary
register values. Sharing is checked on the extracted edges. -/
@[expose] public section
namespace I0451.Runtime

open M6.Source.Cantor

/-- Formula code for applying a set-coded function. The three local
binders are the fixed labels used by the literal evaluation routine. -/
def valueCode (number : Nat → α) (tag : Nat → α → α → α) (g x y : α) : α :=
  let p := number 6
  let s := number 7
  let a := number 8
  let mem := tag 1
  let equal := tag 3
  let imp := tag 0
  let all := tag 2
  let neg := fun f => imp f (number 1)
  let and := fun f h => neg (imp f (neg h))
  let or := fun f h => imp (neg f) h
  let iff := fun f h => and (imp f h) (imp h f)
  let pair := all s (iff (mem s p)
    (and (mem x s) (all a (imp (mem a s) (or (equal a x) (equal a y))))))
  neg (all p (neg (and (mem p g) pair)))

def numericTag (n a b : Nat) : Nat := 4 * pair a b + n

inductive Operation where
  | inc (r : Fin 9)
  | clear (r : Fin 9)
  | move (source target : Fin 9)
  | copy (source a b : Fin 9)
  | unpairQueue
  | push
  | pushOne
  | topIncrementTwo
  | saveOne
  | saveTwo
  | implication
  | functionValue
  | clearOnMatch
  deriving DecidableEq, Repr

def Operation.needsScratch : Operation → Bool
  | .push | .pushOne | .saveOne | .saveTwo | .implication | .functionValue => true
  | _ => false

def Operation.applicable (op : Operation) (s : Registers) : Prop :=
  op.needsScratch = true → s scratchOne = 0 ∧ s scratchTwo = 0

def Operation.apply (op : Operation) (s : Registers) : Registers :=
  match op with
  | .inc r => putRegister s r (s r + 1)
  | .clear r => putRegister s r 0
  | .move source target => transferOne source target s
  | .copy source a b => putRegister (addAt (fun j => j == a || j == b) (s source) s) source 0
  | .unpairQueue => unpairPost proofList (s proofList) s
  | .push => pushResult s
  | .pushOne => putRegister (pushResult s) topWff 1
  | .topIncrementTwo => putRegister s topWff (s topWff + 2)
  | .saveOne => saveOperand s
  | .saveTwo => dropResult s
  | .implication => implicationResult s
  | .functionValue =>
    let result := valueCode id numericTag (s parameterOne) (s parameterTwo) (s axiomIndex)
    let saved := pushResult s
    putRegister (putRegister (putRegister (putRegister saved topWff result) parameterOne 0)
      parameterTwo 0) axiomIndex 0
  | .clearOnMatch =>
    let cleared := clearPair scratchOne parameterTwo s
    if s scratchOne = s parameterTwo then putRegister cleared topWff 0 else cleared

structure ClosedBlock where
  cursor : Cursor
  op : Operation
  correct : ∀ s, op.applicable s → Executes (.branch cursor) s .normal (op.apply s)

def makeClear (cursor : Cursor) (r : Fin 9)
    (dec : outgoing cursor false = some (.instruction (.dec r)))
    (back : outgoing cursor true = some (.instruction (.restart 0))) : ClosedBlock :=
  ⟨cursor, .clear r, fun s _ => clear_counter dec back s⟩

def makeMove (entry loop : Cursor) (source target : Fin 9) (different : target ≠ source)
    (dec : outgoing entry false = some (.instruction (.dec source)))
    (body : outgoing entry true = some (.branch loop))
    (inc : outgoing loop false = some (.instruction (.inc target)))
    (back : outgoing loop true = some (.instruction (.restart 1))) : ClosedBlock :=
  ⟨entry, .move source target, fun s _ => move_one different dec body inc back s⟩

def makeCopy (entry loop body : Cursor) (source a b : Fin 9) (distinct : a ≠ b)
    (keep : (source == a || source == b) = false)
    (dec : outgoing entry false = some (.instruction (.dec source)))
    (bodyEdge : outgoing entry true = some (.branch loop))
    (incEdge : outgoing loop false = some (.branch body))
    (back : outgoing loop true = some (.instruction (.restart 1)))
    (first : outgoing body false = some (.instruction (.inc a)))
    (second : outgoing body true = some (.instruction (.inc b))) : ClosedBlock :=
  ⟨entry, .copy source a b, fun s _ =>
    while_add dec bodyEdge incEdge back _ keep (increment_two distinct first second) s⟩

theorem literal_clear_on_match (s : Registers) :
    Executes (.branch ⟨447, true, false⟩) s .normal ((Operation.clearOnMatch).apply s) := by
  let cleared := clearPair scratchOne parameterTwo s
  have compared := (compare_cache_gate s).share (target := .branch ⟨90, false, true⟩)
    (sameProgram_sound (fuel := 8) (by decide +kernel))
  by_cases same : s scratchOne = s parameterTwo
  · rw [ite_eq_left same] at compared
    simp only [Operation.apply, ite_eq_left same]
    have erased : Executes (.branch ⟨449, true, true⟩) cleared .normal
        (putRegister cleared topWff 0) :=
      clear_counter (by decide +kernel) (by decide +kernel) cleared
    exact executes_sequence (by decide +kernel) (by decide +kernel) compared erased
  · rw [ite_eq_right same] at compared
    simp only [Operation.apply, ite_eq_right same]
    exact .leftExit (by decide +kernel) compared rfl

theorem literal_push_one (s : Registers) (applicable : Operation.pushOne.applicable s) :
    Executes (.branch ⟨104, false, false⟩) s .normal (Operation.pushOne.apply s) := by
  have pushed := literal_stack_push s (applicable rfl).1 (applicable rfl).2
  have one := Executes.inc topWff (pushResult s)
  have zero : pushResult s topWff = 0 := by rfl
  rw [zero] at one
  exact executes_sequence (by decide +kernel) (by decide +kernel) pushed one

theorem literal_top_two (s : Registers) :
    Executes (.branch ⟨117, true, false⟩) s .normal (Operation.topIncrementTwo.apply s) := by
  let mid := putRegister s topWff (s topWff + 1)
  have one := Executes.inc topWff s
  have two := Executes.inc topWff mid
  simpa only [mid, putRegister_at, putRegister_overwrite, Operation.apply] using
    (executes_sequence (root := ⟨117, true, false⟩) (by decide +kernel) (by decide +kernel) one two)

/-- The basis of closed operations used by AX and EXTRA. -/
def formulaBlocks : List ClosedBlock :=
  [⟨stackPushCursor, .push, fun s h => literal_stack_push s (h rfl).1 (h rfl).2⟩,
   ⟨⟨104, false, false⟩, .pushOne, literal_push_one⟩,
   ⟨⟨117, true, false⟩, .topIncrementTwo, fun s _ => literal_top_two s⟩,
   ⟨saveOperandEntry, .saveOne, fun s h => literal_save_operand s (h rfl).1 (h rfl).2⟩,
   ⟨dropCursor, .saveTwo, fun s h => literal_drop s (h rfl).1 (h rfl).2⟩,
   ⟨buildImpEntry, .implication, fun s h => literal_build_imp s (h rfl).1 (h rfl).2⟩,
   ⟨⟨29, false, false⟩, .unpairQueue, fun s _ =>
      unpair_graph (loop := ⟨44, true, false⟩) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) (by decide) (by decide) s⟩,
   makeClear ⟨139, false, false⟩ parameterOne (by decide +kernel) (by decide +kernel),
   makeClear ⟨134, true, false⟩ parameterTwo (by decide +kernel) (by decide +kernel),
   makeClear ⟨373, true, true⟩ axiomIndex (by decide +kernel) (by decide +kernel),
   makeMove ⟨19, true, true⟩ ⟨32, true, true⟩ scratchOne axiomIndex
     (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
   makeMove ⟨30, true, false⟩ ⟨45, true, true⟩ scratchTwo proofList
     (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
   makeMove ⟨99, false, true⟩ ⟨89, true, false⟩ scratchTwo scratchOne
     (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
   makeMove ⟨102, true, false⟩ ⟨116, true, true⟩ scratchOne parameterTwo
     (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
   makeMove ⟨162, false, true⟩ ⟨152, true, false⟩ scratchOne topWff
     (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
   makeMove ⟨450, false, true⟩ ⟨116, true, false⟩ parameterOne parameterTwo
     (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
   makeCopy ⟨190, false, true⟩ ⟨127, true, false⟩ ⟨140, false, true⟩ axiomIndex scratchOne topWff
     (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel) (by decide +kernel),
   makeCopy ⟨446, false, false⟩ ⟨149, true, false⟩ ⟨157, false, true⟩ axiomIndex scratchOne scratchTwo
     (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
     (by decide +kernel) (by decide +kernel) (by decide +kernel),
   ⟨⟨447, true, false⟩, .clearOnMatch, fun s _ => literal_clear_on_match s⟩]

def ClosedBlock.matches (cursor : Cursor) (block : ClosedBlock) : Bool :=
  cursor.control == block.cursor.control &&
    sameProgram 12 (.branch block.cursor) (.branch cursor)

/-- Extract a sequential plan. Falling through a branch is justified
only when both sides are themselves closed blocks. -/
def assembleWith (blocks : List ClosedBlock) : Nat → Edge → Option (List Operation)
  | _, .instruction (.inc r) => some [.inc r]
  | n + 1, .branch cursor =>
    match blocks.find? (ClosedBlock.matches cursor) with
    | some block => some [block.op]
    | none => do
      let left ← cachedOutgoing cursor false
      let right ← cachedOutgoing cursor true
      let first ← assembleWith blocks n left
      let rest ← assembleWith blocks n right
      return first ++ rest
  | _, _ => none

abbrev assemble := assembleWith formulaBlocks

def executeOperations : List Operation → Registers → Option Registers
  | [], s => some s
  | op :: rest, s =>
    if op.needsScratch && !(s scratchOne == 0 && s scratchTwo == 0) then none
    else executeOperations rest (op.apply s)

theorem executeOperations_append (first rest : List Operation) (s : Registers) :
    executeOperations (first ++ rest) s = (executeOperations first s).bind (executeOperations rest) := by
  induction first generalizing s with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.cons_append, executeOperations]
    split
    · rfl
    · exact ih _

private theorem execute_one {op : Operation} {s t : Registers}
    (ran : executeOperations [op] s = some t) : op.applicable s ∧ op.apply s = t := by
  simp only [executeOperations] at ran
  split at ran
  · contradiction
  · rename_i ready
    refine ⟨fun needs => ?_, Option.some.inj ran⟩
    simpa [needs, Bool.not_eq_true, Bool.and_eq_true, beq_iff_eq] using ready

/-- A decoded sequential block with explicit local graph edges.
The checker is independent of the registers used to interpret the plan. -/
inductive AssemblyPlan (blocks : List ClosedBlock) : Edge → List Operation → Prop where
  | increment (r : Fin 9) : AssemblyPlan blocks (.instruction (.inc r)) [.inc r]
  | closed (block : ClosedBlock) (present : block ∈ blocks) {cursor : Cursor}
      (same : SameProgram (.branch block.cursor) (.branch cursor)) :
      AssemblyPlan blocks (.branch cursor) [block.op]
  | sequence {cursor : Cursor} {left right : Edge} {first rest : List Operation}
      (leftEdge : outgoing cursor false = some left) (rightEdge : outgoing cursor true = some right)
      (prefixPlan : AssemblyPlan blocks left first) (suffixPlan : AssemblyPlan blocks right rest) :
      AssemblyPlan blocks (.branch cursor) (first ++ rest)

theorem assemble_plan {blocks : List ClosedBlock} {fuel : Nat} {edge : Edge} {ops : List Operation}
    (extracted : assembleWith blocks fuel edge = some ops) : AssemblyPlan blocks edge ops := by
  induction fuel generalizing edge ops with
  | zero =>
    cases edge with
    | branch cursor => simp [assembleWith] at extracted
    | instruction op =>
      cases op <;> simp [assembleWith] at extracted
      subst ops
      exact .increment _
  | succ fuel ih =>
    cases edge with
    | instruction op =>
      cases op <;> simp [assembleWith] at extracted
      subst ops
      exact .increment _
    | branch cursor =>
      simp only [assembleWith] at extracted
      cases lookup : blocks.find? (ClosedBlock.matches cursor) with
      | some block =>
        simp only [lookup, Option.some.injEq] at extracted
        subst ops
        have matched := List.find?_some lookup
        exact .closed block (List.mem_of_find?_eq_some lookup)
          (sameProgram_sound (Bool.and_eq_true_iff.mp matched).2)
      | none =>
        rw [lookup] at extracted
        change ((cachedOutgoing cursor false).bind fun left => (cachedOutgoing cursor true).bind fun right =>
          (assembleWith blocks fuel left).bind fun first => (assembleWith blocks fuel right).bind fun rest =>
            some (first ++ rest)) = some ops at extracted
        simp only [Option.bind_eq_some_iff, Option.some.injEq] at extracted
        obtain ⟨left, hLeft, right, hRight, first, hFirst, rest, hRest, rfl⟩ := extracted
        exact .sequence (cachedOutgoing_sound hLeft) (cachedOutgoing_sound hRight) (ih hFirst) (ih hRest)

theorem AssemblyPlan.executes {blocks : List ClosedBlock} {edge : Edge} {ops : List Operation}
    (plan : AssemblyPlan blocks edge ops) {s t : Registers}
    (ran : executeOperations ops s = some t) : Executes edge s .normal t := by
  induction plan generalizing s t with
  | increment r =>
    obtain ⟨_, rfl⟩ := execute_one ran
    exact .inc r s
  | closed block present same =>
    obtain ⟨ok, rfl⟩ := execute_one ran
    exact (block.correct s ok).share same
  | sequence left right _ _ ihLeft ihRight =>
    rw [executeOperations_append, Option.bind_eq_some_iff] at ran
    obtain ⟨middle, first, last⟩ := ran
    exact executes_sequence left right (ihLeft first) (ihRight last)

theorem assemble_sound {blocks : List ClosedBlock} {fuel : Nat} {edge : Edge} {ops : List Operation}
    (extracted : assembleWith blocks fuel edge = some ops) {s t : Registers}
    (ran : executeOperations ops s = some t) : Executes edge s .normal t :=
  (assemble_plan extracted).executes ran

end I0451.Runtime
