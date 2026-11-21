module
public import I3_380.Engine.ControlWords
@[expose] public section

namespace PalomarI3380.Engine

open scoped PalomarI3380.Engine

/-- A decoded transition of the reference machine. -/
structure Transition where
  target : Nat
  write : Bool
  right : Bool
  deriving DecidableEq, Repr

def transition (q : Nat) (read : Bool) : Transition :=
  let packed := referenceMachine.row q (bit read)
  ⟨packed / 4, packed / 2 % 2 == 1, packed % 2 == 1⟩

theorem transition_row (q : Nat) (read : Bool) (hq : q < 394) :
    Row q read (transition q read).write (transition q read).right (transition q read).target := by
  refine ⟨hq, ?_⟩
  simp only [transition]
  generalize referenceMachine.row q (bit read) = value
  have low : value % 2 < 2 := Nat.mod_lt _ (by decide)
  have mid : value / 2 % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [bit, beq_iff_eq]
  split <;> split <;> omega

def height (q : Nat) : Nat := (DecoderData.bounds >>> (18 * q)) % 64
def zeroBound (q : Nat) : Nat := (DecoderData.bounds >>> (18 * q + 6)) % 64
def hasEarlierOne (q : Nat) : Bool := (DecoderData.bounds >>> (18 * q + 12)) % 2 == 1

inductive Exit where
  | register (decrement : Bool) (r : Fin 12)
  | break (skipZero : Bool)
  | continue (skipOne : Bool)
  | halt
  deriving DecidableEq, Repr

def Exit.port : Exit → Nat
  | .halt => 394
  | .register dec r => Port.registerEntry dec r.val
  | .break skip => Port.breakPort skip
  | .continue skip => if skip then Port.continueOne else Port.dispatch 0

def exitFor (q : Nat) : Option Exit :=
  let specials := [.halt, .break false, .break true, .continue false, .continue true]
  let registers := (List.finRange 12).flatMap fun r => [.register false r, .register true r]
  (specials ++ registers).find? (fun op => op.port == q)

theorem exit_port {q : Nat} {op : Exit} (h : exitFor q = some op) : op.port = q := by
  unfold exitFor at h
  have hb : (op.port == q) = true :=
    List.find?_some (p := fun item : Exit => item.port == q) h
  exact beq_iff_eq.mp hb

def checkEdge (q : Nat) (b : Bool) : Bool :=
  let e := transition q b
  let nextZeros := if b then 0 else zeroBound q + 1
  if 0 < height e.target then
    e.write == b && e.right && decide (e.target < 394) && decide (height e.target < height q) &&
      decide (nextZeros ≤ 6) && decide (nextZeros ≤ zeroBound e.target) &&
      (!hasEarlierOne e.target || hasEarlierOne q || b)
  else
    match exitFor e.target with
    | some (.register _ _) => e.right && (e.write == b) && decide (nextZeros ≤ 6)
    | some (.break _) => !e.right && !e.write
    | some (.continue k) => !e.right && !e.write && (!k || hasEarlierOne q)
    | some .halt => e.right
    | none => false

def checkDecoder : Bool :=
  (List.range 394).all fun q =>
    if 0 < height q then checkEdge q false && checkEdge q true else true

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem checkedDecoder : checkDecoder = true := by
  decide +kernel

theorem checked_edge (q : Nat) (b : Bool) (hq : q < 394) (hn : 0 < height q) :
    checkEdge q b = true := by
  have h := List.all_eq_true.mp checkedDecoder q (List.mem_range.mpr hq)
  simp only [hn, ↓reduceIte, Bool.and_eq_true] at h
  cases b
  · exact h.1
  · exact h.2

/-- Number of consecutive zeros next to the head, in a reversed path. -/
def leadingZeros : List Bool → Nat
  | [] => 0
  | true :: _ => 0
  | false :: rest => leadingZeros rest + 1

theorem shortZeros_of_leading (path : List Bool) (seen : Nat)
    (h : shortZeros 0 path = true) (bound : seen + leadingZeros path ≤ 6) :
    shortZeros seen path = true := by
  induction path generalizing seen with
  | nil => rfl
  | cons b path ih =>
    cases b
    · have tail := shortZeros_tail h
      simp only [leadingZeros] at bound
      simp only [shortZeros, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, ih (seen + 1) tail (by omega)⟩
    · exact h

structure PrefixValid (q : Nat) (reversed : List Bool) : Prop where
  limitedZeros : shortZeros 0 reversed = true
  lastZeros : leadingZeros reversed ≤ zeroBound q
  knownOne : hasEarlierOne q = true → true ∈ reversed

theorem extend_short {q : Nat} {b : Bool} {rev : List Bool} (h : PrefixValid q rev)
    (hNext : (if b then 0 else zeroBound q + 1) ≤ 6) :
    shortZeros 0 (b :: rev) = true := by
  cases b
  · have hPrev := h.lastZeros
    simp only [shortZeros, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by decide, shortZeros_of_leading rev 1 h.limitedZeros (by simp at hNext; omega)⟩
  · exact h.limitedZeros

/-- A verified internal arm preserves the path annotations. -/
theorem internal_arm (q : Nat) (read : Bool) (rev : List Bool)
    (hq : q < 394) (hActive : 0 < height q) (hp : PrefixValid q rev)
    (hInternal : 0 < height (transition q read).target) :
    let e := transition q read
    e.write = read ∧ e.right = true ∧ e.target < 394 ∧ height e.target < height q ∧
      PrefixValid e.target (read :: rev) := by
  have h := checked_edge q read hq hActive
  simp only [checkEdge, hInternal, ↓reduceIte, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hWrite, hRight⟩, hState⟩, hRank⟩, hZero⟩, hBound⟩, hOne⟩ := h
  refine ⟨hWrite, hRight, hState, hRank, ⟨extend_short hp hZero, ?_, ?_⟩⟩
  · cases read
    · have hz := hp.lastZeros
      simp only [leadingZeros, Bool.false_eq_true, ↓reduceIte] at hBound ⊢
      omega
    · simpa only [leadingZeros, ↓reduceIte] using hBound
  · intro hNeeded
    cases read
    · simp only [hNeeded, Bool.not_true, Bool.false_or, Bool.or_false] at hOne
      exact List.mem_cons_of_mem _ (hp.knownOne hOne)
    · exact List.mem_cons_self

theorem root_valid : PrefixValid Port.root [] := by
  constructor
  · rfl
  · decide +kernel
  · intro h
    have heq : hasEarlierOne Port.root = false := by decide +kernel
    simp only [heq, Bool.false_eq_true] at h

end PalomarI3380.Engine
