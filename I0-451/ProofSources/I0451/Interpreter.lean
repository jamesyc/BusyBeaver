module
public import I0451.Frames

/-! Executable instruction semantics extracted from the literal decoder.
An invalid frame is explicit. A successful transition has a corresponding
positive-length literal run. -/
@[expose] public section
namespace I0451.Runtime

instance (n : Nat) (word : List Bool) : Decidable (SafeDispatch n word) :=
  match word with
  | [] => isTrue trivial
  | b :: bs =>
    haveI := instDecidableSafeDispatch (zeroRun n b) bs
    inferInstanceAs (Decidable (zeroRun n b ≤ 7 ∧ SafeDispatch (zeroRun n b) bs))

structure RegisterCut (α : Type := Nat) where
  before : List α
  last : α
  value : α
  after : List α
  deriving DecidableEq, Repr

/-- A register index counts from the right. The fixed prefix gives a
block immediately before every selectable register. -/
def cutRegister {α : Type} (index : Nat) (regs : List α) : Option (RegisterCut α) :=
  let rev := regs.reverse
  match rev.drop index with
  | value :: last :: before =>
    let after := (rev.take index).reverse
    if after.length = index then some ⟨before.reverse, last, value, after⟩ else none
  | _ => none

theorem cutRegister_sound {α : Type} {index : Nat} {regs : List α} {cut : RegisterCut α}
    (selected : cutRegister index regs = some cut) :
    regs = cut.before ++ cut.last :: cut.value :: cut.after ∧ cut.after.length = index := by
  unfold cutRegister at selected
  cases h : regs.reverse.drop index with
  | nil => simp [h] at selected
  | cons value rest =>
    cases rest with
    | nil => simp [h] at selected
    | cons last before =>
      simp only [h] at selected
      split at selected
      · rename_i length
        injection selected with same
        subst cut
        have split := List.take_append_drop index regs.reverse
        rw [h] at split
        have reversed := congrArg List.reverse split
        simp only [List.reverse_append, List.reverse_cons, List.reverse_reverse, List.append_assoc,
          List.singleton_append] at reversed
        exact ⟨reversed.symm, length⟩
      · contradiction

/-- Find the first copy of the given delimiter, returning the number
of opposite bits passed and the suffix beyond the delimiter. -/
def cutAddress (delimiter : Bool) : List Bool → Option (Nat × List Bool)
  | [] => none
  | b :: bs =>
    if b = delimiter then some (0, bs)
    else (cutAddress delimiter bs).map fun (n, rest) => (n + 1, rest)

theorem cutAddress_sound {delimiter : Bool} {word : List Bool} {n : Nat} {rest : List Bool}
    (cut : cutAddress delimiter word = some (n, rest)) :
    word = List.replicate n (!delimiter) ++ delimiter :: rest := by
  induction word generalizing n rest with
  | nil => simp [cutAddress] at cut
  | cons b bs ih =>
    by_cases same : b = delimiter
    · subst b
      simp [cutAddress] at cut
      obtain ⟨rfl, rfl⟩ := cut
      rfl
    · cases parsed : cutAddress delimiter bs with
      | none => simp [cutAddress, same, parsed] at cut
      | some pair =>
        obtain ⟨k, tail⟩ := pair
        simp [cutAddress, same, parsed] at cut
        obtain ⟨rfl, rfl⟩ := cut
        have bit : b = !delimiter := by cases b <;> cases delimiter <;> simp_all
        rw [ih parsed, List.replicate_succ, List.cons_append, bit]

def registerAddress (q : Nat) : Option (RegisterOp × Nat) :=
  let i := incStates.idxOf q
  if i < 9 then some (.inc, i)
  else
    let i := decStates.idxOf q
    if i < 9 then some (.dec, i) else none

theorem registerAddress_sound {q : Nat} {op : RegisterOp} {i : Nat}
    (address : registerAddress q = some (op, i)) : i < 9 ∧ q = op.issue i := by
  dsimp only [registerAddress] at address
  split at address
  · rename_i h
    injection address with eq
    cases eq
    refine ⟨h, ?_⟩
    have bound : incStates.idxOf q < incStates.length := h
    unfold RegisterOp.issue
    rw [List.getElem?_eq_getElem bound, List.getElem_idxOf bound]
    rfl
  · split at address
    · rename_i h
      injection address with eq
      cases eq
      refine ⟨h, ?_⟩
      have bound : decStates.idxOf q < decStates.length := h
      unfold RegisterOp.issue
      rw [List.getElem?_eq_getElem bound, List.getElem_idxOf bound]
      rfl
    · contradiction

/-- Construct a frame with the stated gap after its explicit address. -/
def makeFrame (word : List Bool) (gap : Nat) (regs : List Nat) : RegisterFrame :=
  ⟨word, word.length + gap, regs⟩

@[simp] theorem makeFrame_tape (word : List Bool) (gap : Nat) (regs : List Nat) :
    (makeFrame word gap regs).tape = frame word gap regs := by
  simp [makeFrame, RegisterFrame.tape]

inductive MacroResult where
  | invalid
  | halt
  | next (frame : RegisterFrame)
  deriving DecidableEq, Repr

/-- Register semantics after consuming the decoder word. -/
def runRegister (word : List Bool) (gap : Nat) (regs : List Nat)
    (op : RegisterOp) (i : Nat) : MacroResult :=
  if i + 4 ≤ gap then
    match cutRegister i regs with
    | none => .invalid
    | some cut =>
      let nextAddress := (carry word.reverse).reverse
      match op with
      | .inc => .next (makeFrame nextAddress gap
          (cut.before ++ cut.last :: (cut.value + 1) :: cut.after))
      | .dec =>
        match cut.value with
        | value + 1 => .next (makeFrame nextAddress (gap + 1)
            (cut.before ++ cut.last :: value :: cut.after))
        | 0 =>
          match cutAddress false word.reverse with
          | none => .invalid
          | some (n, rest) =>
            if SafeDispatch 0 rest then .next (makeFrame (carry rest).reverse (gap + n + 2) regs)
            else .invalid
  else .invalid

/-- Jump semantics after the decoder has erased its last marker cells. -/
def runJump (q : Nat) (reversed : List Bool) (gap : Nat) (regs : List Nat) : MacroResult :=
  if q = continueZero then
    if SafeDispatch 0 reversed then .next (makeFrame reversed.reverse gap regs) else .invalid
  else if q = continueOne then
    match cutAddress true reversed with
    | none => .invalid
    | some (n, rest) =>
      if SafeDispatch 0 rest then .next (makeFrame rest.reverse (gap + n + 1) regs)
      else .invalid
  else if q = breakOne then
    match cutAddress false reversed with
    | none => .invalid
    | some (n, rest) =>
      if SafeDispatch 0 rest then .next (makeFrame (carry rest).reverse (gap + n + 1) regs)
      else .invalid
  else .invalid

/-- Execute one abstract instruction by decoding the address in zero
padding. The guards state that the logical word is separated from the
register file. -/
def macroStep (f : RegisterFrame) : MacroResult :=
  match Decoder.decode 94 root true false (pack f.word 0) with
  | none => .invalid
  | some decoded =>
    if f.word.length ≤ f.slot ∧ decoded.word.length ≤ f.slot ∧ decoded.rest = 0 then
      let gap := f.slot - decoded.word.length
      match decoded.exit with
      | .issue q =>
        if q = 451 then .halt
        else if SafeDispatch 0 decoded.word.reverse then
          match registerAddress q with
          | none => .invalid
          | some (op, i) => runRegister decoded.word gap f.regs op i
        else .invalid
      | .erase q =>
        match decoded.word.reverse with
        | true :: earlier => runJump q earlier (gap + 1) f.regs
        | _ => .invalid
      | .fused =>
        match decoded.word.reverse with
        | true :: true :: earlier => runJump continueOne earlier (gap + 2) f.regs
        | _ => .invalid
    else .invalid

end I0451.Runtime
