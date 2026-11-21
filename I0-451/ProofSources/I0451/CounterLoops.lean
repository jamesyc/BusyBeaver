module
public import I0451.InstructionGraph

/-! Reusable contracts for the two structured control patterns in the
proof-search program. -/
@[expose] public section
namespace I0451.Runtime

/-- One closed sequence, with both subprograms returning normally. -/
theorem executes_sequence {root : Cursor} {a b : Edge} {first mid last : Registers}
    (left : outgoing root false = some a) (right : outgoing root true = some b)
    (firstRun : Executes a first .normal mid) (lastRun : Executes b mid .normal last) :
    Executes (.branch root) first .normal last :=
  .rightExit left right firstRun lastRun rfl

/-- Conditional execution using the result of a decrement test.
On a positive register, execute only the decrement. On zero, execute
the body with the same register values. -/
theorem if_zero {root test : Cursor} {r : Fin 9} {body : Edge} {s done : Registers}
    (left : outgoing root false = some (.branch test))
    (right : outgoing root true = some body)
    (dec : outgoing test false = some (.instruction (.dec r)))
    (skip : outgoing test true = some (.instruction (.break 0)))
    (effect : s r = 0 → Executes body s .normal done) :
    Executes (.branch root) s .normal (if s r = 0 then done else putRegister s r (s r - 1)) := by
  cases value : s r with
  | zero =>
    have before : Executes (.branch test) s .normal s :=
      .leftExit dec (.decZero r s value) rfl
    simpa only [ite_true] using executes_sequence left right before (effect value)
  | succ n =>
    let t := putRegister s r n
    have before : Executes (.branch test) s (.break 0) t :=
      .rightExit dec skip (.decPositive r s n value) (.break 0 t) rfl
    simpa only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel] using
      (Executes.leftExit left before (show (Signal.break 0).leftExit = some .normal from rfl))

/-- Generic counting-loop contract. The loop body preserves the
source, and the postcondition accounts for its repeated application. -/
theorem while_effect {root block : Cursor} {body : Edge} {source : Fin 9}
    (left : outgoing root false = some (.instruction (.dec source)))
    (right : outgoing root true = some (.branch block))
    (bodyEdge : outgoing block false = some body)
    (backEdge : outgoing block true = some (.instruction (.restart 1)))
    (update : Registers → Registers) (post : Nat → Registers → Registers)
    (bodyRuns : ∀ s, Executes body s .normal (update s))
    (sourceFixed : ∀ s, update s source = s source)
    (atZero : ∀ s, s source = 0 → post 0 s = s)
    (atSucc : ∀ n s, s source = n + 1 →
      post (n + 1) s = post n (update (putRegister s source n))) (s : Registers) :
    Executes (.branch root) s .normal (post (s source) s) := by
  generalize value : s source = count
  induction count generalizing s with
  | zero =>
    rw [atZero s value]
    exact .leftExit left (.decZero source s value) rfl
  | succ count ih =>
    rw [atSucc count s value]
    let afterDec := putRegister s source count
    have bodyDone : Executes (.branch block) afterDec (.restart 0) (update afterDec) :=
      .rightExit bodyEdge backEdge (bodyRuns afterDec) (.restart 1 _) rfl
    have remaining : (update afterDec) source = count := by simp [sourceFixed, afterDec]
    exact .repeat left right (.decPositive source s count value) bodyDone (ih _ remaining)

def addAt (selected : Fin 9 → Bool) (amount : Nat) (s : Registers) : Registers :=
  fun j => if selected j then s j + amount else s j

/-- Run a decrement loop whose body adds one to a fixed set of
destination registers. The source register is not among them. -/
theorem while_add {root block : Cursor} {body : Edge} {source : Fin 9}
    (left : outgoing root false = some (.instruction (.dec source)))
    (right : outgoing root true = some (.branch block))
    (bodyEdge : outgoing block false = some body)
    (backEdge : outgoing block true = some (.instruction (.restart 1)))
    (selected : Fin 9 → Bool) (onlyDestinations : selected source = false)
    (bodyAdds : ∀ s, Executes body s .normal (addAt selected 1 s))
    (s : Registers) :
    Executes (.branch root) s .normal (putRegister (addAt selected (s source) s) source 0) := by
  generalize value : s source = count
  induction count generalizing s with
  | zero =>
    have unchanged : putRegister (addAt selected 0 s) source 0 = s := by
      funext j
      by_cases atSource : j = source
      · subst j
        simp [putRegister, value]
      · simp [putRegister, atSource, addAt]
    rw [unchanged]
    exact .leftExit left (.decZero source s value) rfl
  | succ count ih =>
    let consumed := putRegister s source count
    let added := addAt selected 1 consumed
    have sourceSame : added source = count := by simp [added, addAt, onlyDestinations, consumed]
    have loopBody : Executes (.branch block) consumed (.restart 0) added :=
      .rightExit bodyEdge backEdge (bodyAdds consumed) (.restart 1 added) rfl
    have equation : putRegister (addAt selected count added) source 0 =
        putRegister (addAt selected (count + 1) s) source 0 := by
      funext j
      by_cases atSource : j = source
      · simp [putRegister, atSource]
      · by_cases chosen : selected j
        · simp [putRegister, atSource, addAt, chosen, added, consumed, Nat.add_comm, Nat.add_left_comm]
        · simp [putRegister, atSource, addAt, chosen, added, consumed]
    have keepGoing := ih added sourceSame
    rw [equation] at keepGoing
    exact .repeat left right (.decPositive source s count value) loopBody keepGoing

theorem increment_one (register : Fin 9) (s : Registers) :
    Executes (.instruction (.inc register)) s .normal (addAt (· == register) 1 s) := by
  have same : putRegister s register (s register + 1) = addAt (· == register) 1 s := by
    funext j
    by_cases h : j = register <;> simp [putRegister, addAt, h]
  rw [← same]
  exact .inc register s

theorem increment_two {root : Cursor} {a b : Fin 9} (distinct : a ≠ b)
    (left : outgoing root false = some (.instruction (.inc a)))
    (right : outgoing root true = some (.instruction (.inc b))) (s : Registers) :
    Executes (.branch root) s .normal (addAt (fun j => j == a || j == b) 1 s) := by
  have both : addAt (· == b) 1 (addAt (· == a) 1 s) =
      addAt (fun j => j == a || j == b) 1 s := by
    funext j
    by_cases ha : j = a
    · subst j
      simp [addAt, distinct]
    · by_cases hb : j = b
      · simp [addAt, hb, Ne.symm distinct]
      · simp [addAt, ha, hb]
  rw [← both]
  exact executes_sequence left right (increment_one a s) (increment_one b _)

def transferOne (source target : Fin 9) (s : Registers) : Registers :=
  putRegister (addAt (· == target) (s source) s) source 0

theorem move_one {entry loop : Cursor} {source target : Fin 9} (different : target ≠ source)
    (dec : outgoing entry false = some (.instruction (.dec source)))
    (body : outgoing entry true = some (.branch loop))
    (inc : outgoing loop false = some (.instruction (.inc target)))
    (back : outgoing loop true = some (.instruction (.restart 1))) (s : Registers) :
    Executes (.branch entry) s .normal (transferOne source target s) :=
  while_add dec body inc back (· == target) (by simp [Ne.symm different]) (increment_one target) s

end I0451.Runtime
