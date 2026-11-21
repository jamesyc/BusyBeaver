module
public import I3_380.Engine.Paths
@[expose] public section

namespace PalomarI3380.Engine

open scoped PalomarI3380.Engine

structure RegisterState where
  path : List Bool
  gap : Nat
  registers : List Nat
  deriving DecidableEq, Repr

def RegisterState.config (s : RegisterState) : Configuration :=
  frame s.path s.gap s.registers

def RegisterState.span (s : RegisterState) : Nat := s.path.length + s.gap

/-- The decoder reads at most 59 bits. A register needs at most twelve
selector marks and two zeros. The remaining margin suffices for every arm. -/
def RegisterState.Prepared (s : RegisterState) : Prop :=
  Clean s.path ∧ 13 ≤ s.registers.length ∧ 74 ≤ s.span

inductive Outcome where
  | invalid
  | halt
  | next (state : RegisterState)
  deriving DecidableEq, Repr

def executeDecoded (rs : List Nat) (d : Decoded) : Outcome :=
  let gap := d.rest.length
  match d.command with
  | .halt => .halt
  | .break skip =>
    .next ⟨(breakPath skip d.before).reverse, gap + 1 + breakPadding skip d.before, rs⟩
  | .continue false => .next ⟨d.before.reverse, gap + 1, rs⟩
  | .continue true =>
    let path := stripThrough true d.before
    .next ⟨path.reverse, gap + 1 + (d.before.length - path.length), rs⟩
  | .register dec r =>
    if r.val + 3 ≤ gap then
      let index := rs.length - (r.val + 1)
      let value := rs[index]?.getD 0
      let skip := zeroDecrement dec value
      .next ⟨(breakPath skip d.path.reverse).reverse,
        gap + bit dec + breakPadding skip d.path.reverse, rs.set index (registerValue dec value)⟩
    else .invalid

def execute (s : RegisterState) : Outcome :=
  match follow 59 Port.root [] (s.path ++ zeros s.gap) with
  | none => .invalid
  | some d => executeDecoded s.registers d

def Realizes (s : RegisterState) : Outcome → Prop
  | .invalid => True
  | .halt => HaltsFrom referenceMachine s.config
  | .next t =>
    s.config ⟶+ t.config ∧ Clean t.path ∧ t.registers.length = s.registers.length ∧ s.span ≤ t.span

theorem split_register {α : Type} [OfNat α 0] (rs : List α) (r : Fin 12) (hLen : 13 ≤ rs.length) :
    ∃ a as v after,
      rs = (a :: as) ++ v :: after ∧ after.length = r.val ∧
      rs[rs.length - (r.val + 1)]?.getD 0 = v ∧
      ∀ value, rs.set (rs.length - (r.val + 1)) value = (a :: as) ++ value :: after := by
  let i := rs.length - (r.val + 1)
  have hIndex : i < rs.length := by dsimp only [i]; omega
  have positive : 0 < i := by have hr := r.isLt; dsimp only [i]; omega
  have hBefore : (rs.take i).length = i := List.length_take_of_le (by omega)
  obtain ⟨a, as, hTake⟩ := List.exists_cons_of_ne_nil (l := rs.take i)
    (by intro h; rw [h, List.length_nil] at hBefore; omega)
  refine ⟨a, as, rs[i], rs.drop (i + 1), ?_, ?_, ?_, ?_⟩
  · rw [← hTake]
    change rs = rs.take i ++ ([rs[i]] ++ rs.drop (i + 1))
    rw [← List.append_assoc, ← List.take_succ_eq_append_getElem hIndex, List.take_append_drop]
  · simp only [List.length_drop, i]
    omega
  · change rs[i]?.getD 0 = rs[i]
    rw [List.getElem?_eq_getElem hIndex]
    rfl
  · intro value
    change rs.set i value = _
    rw [← hTake, List.set_eq_take_append_cons_drop, ite_eq_left hIndex]

private theorem reference_terminal {c : Configuration} (hq : c.state = 394) :
    step referenceMachine c = none := by
  have h : referenceMachine.workingStates ≤ c.state := by rw [hq]; decide
  simp only [step, h, ↓reduceIte]

/-- A successful executable cycle has a positive literal run. It preserves
clean instruction pointers, register count, and the space available to the decoder. -/
theorem execute_realizes (s : RegisterState) (hClean : Clean s.path)
    (hRegisters : 13 ≤ s.registers.length) : Realizes s (execute s) := by
  cases hDecoded : follow 59 Port.root [] (s.path ++ zeros s.gap) with
  | none => simp only [execute, hDecoded, Realizes]
  | some d =>
    have hd := decode_facts (s.path ++ zeros s.gap) hDecoded
    let g := d.rest.length
    have hZeros : d.rest = zeros g := hd.rest_zeros hClean
    have hInput : s.config = frame d.path g s.registers := by
      have eq := hd.consumed
      rw [hZeros] at eq
      simp only [RegisterState.config, frame, ← List.append_assoc, eq]
    have hSpan : s.span = d.path.length + g := by
      have h := congrArg List.length hd.consumed
      simpa only [RegisterState.span, List.length_append, List.length_replicate, g] using h.symm
    have hLeafSpan : s.span = d.before.length + 1 + g := by
      simpa only [Decoded.path, List.length_append, List.length_reverse, List.length_singleton] using hSpan
    have beforeValid := hd.before_valid
    have literal := hd.progress [true] (zeros g ++ registers s.registers)
    simp only [List.nil_append] at literal
    change frame d.path g s.registers ⟶+
      d.destination [true] (zeros g ++ registers s.registers) at literal
    have shape := hd.shape
    have target := hd.port
    have leftExit (q : Nat) (hq : d.transition.target = q)
        (direction : d.transition.right = false) (writeBit : d.transition.write = false) :
        frame d.path g s.registers ⟶+
          atLeft q (d.before ++ [true]) (zeros (g + 1) ++ registers s.registers) := by
      simpa only [Decoded.destination, hq, direction, writeBit, Bool.false_eq_true, ↓reduceIte, List.replicate_succ,
        List.cons_append] using literal
    cases hCommand : d.command with
    | halt =>
      simp only [execute, hDecoded, executeDecoded, hCommand, Realizes]
      obtain ⟨n, _, hn⟩ := literal
      refine ⟨n, d.destination [true] (zeros g ++ registers s.registers), ?_, reference_terminal ?_⟩
      · rw [hInput]
        exact hn
      · rw [hCommand] at shape target
        change d.transition.right = true at shape
        simp only [Decoded.destination, shape, ↓reduceIte, atRight, ← target, Exit.port]
    | «break» skip =>
      simp only [execute, hDecoded, executeDecoded, hCommand, Realizes]
      rw [hCommand] at shape target
      rcases shape with ⟨hDir, hWrite, hShort⟩
      have advance : frame d.path g s.registers ⟶+
          atLeft (Port.breakPort skip) (d.before ++ [true]) (zeros (g + 1) ++ registers s.registers) :=
        leftExit _ target.symm hDir hWrite
      constructor
      · rw [hInput]
        refine advance.thenReach ?_
        have cycle := break_run skip d.before hShort (zeros (g + 1) ++ registers s.registers)
        have hPad : breakPadding skip d.before + (g + 1) = g + 1 + breakPadding skip d.before := by omega
        simpa only [RegisterState.config, frame, append_zeros, hPad] using cycle.reach
      · refine ⟨clean_break d.before skip beforeValid, trivial, ?_⟩
        have bound := break_length skip d.before
        rw [hLeafSpan]
        simp only [RegisterState.span, List.length_reverse, g]
        omega
    | «continue» skip =>
      cases skip with
      | false =>
        simp only [execute, hDecoded, executeDecoded, hCommand, Realizes]
        rw [hCommand] at shape target
        rcases shape with ⟨hDir, hWrite, hShort, _⟩
        have advance : frame d.path g s.registers ⟶+
            atLeft (Port.dispatch 0) (d.before ++ [true]) (zeros (g + 1) ++ registers s.registers) :=
          leftExit _ target.symm hDir hWrite
        constructor
        · rw [hInput]
          exact advance.thenReach (dispatch_from d.before 0 (by decide) hShort
            (zeros (g + 1) ++ registers s.registers)).reach
        · refine ⟨⟨d.before.reverse, 0, (List.append_nil _).symm, beforeValid⟩, trivial, ?_⟩
          rw [hLeafSpan]
          simp only [RegisterState.span, List.length_reverse, g]
          omega
      | true =>
        simp only [execute, hDecoded, executeDecoded, hCommand, Realizes]
        rw [hCommand] at shape target
        rcases shape with ⟨hDir, hWrite, hShort, hOne⟩
        have advance : frame d.path g s.registers ⟶+
            atLeft Port.continueOne (d.before ++ [true]) (zeros (g + 1) ++ registers s.registers) :=
          leftExit _ target.symm hDir hWrite
        constructor
        · rw [hInput]
          refine advance.thenReach ?_
          let cut := (stripThrough true d.before).length
          have cycle := continue_one d.before hShort (hOne rfl) (zeros (g + 1) ++ registers s.registers)
          have hPad : d.before.length - cut + (g + 1) = g + 1 + (d.before.length - cut) := by omega
          simpa only [RegisterState.config, frame, append_zeros, hPad, cut] using cycle.reach
        · refine ⟨clean_continue d.before beforeValid, trivial, ?_⟩
          have bound := stripThrough_length true d.before
          rw [hLeafSpan]
          simp only [RegisterState.span, List.length_reverse, g]
          omega
    | register dec r =>
      by_cases hGap : r.val + 3 ≤ g
      · have hGap' : r.val + 3 ≤ d.rest.length := hGap
        simp only [execute, hDecoded, executeDecoded, hCommand, hGap', ↓reduceIte, Realizes]
        obtain ⟨a, as, v, after, hFile, hIndex, hRead, hReplace⟩ := split_register s.registers r hRegisters
        rw [hRead, hReplace]
        have hSplit : g - (r.val + 3) + 2 + (r.val + 1) = g := by omega
        have hGapAdd : g - (r.val + 3) + 2 + bit dec + (r.val + 1) = g + bit dec := by omega
        constructor
        · rw [hInput, hFile]
          have cycle := register_cycle (hd.register_route hCommand) (g - (r.val + 3)) a v as after hIndex
          simpa only [RegisterState.config, hSplit, hGapAdd] using cycle
        · refine ⟨clean_break d.path.reverse _ ?_, ?_, ?_⟩
          · rw [List.reverse_reverse]
            exact hd.validPrefix
          · rw [hFile]
            simp only [List.length_append, List.length_cons]
          · have bound := break_length (zeroDecrement dec v) d.path.reverse
            rw [hSpan]
            simp only [RegisterState.span, List.length_reverse, g] at bound ⊢
            omega
      · have hGap' : ¬r.val + 3 ≤ d.rest.length := hGap
        simp only [execute, hDecoded, executeDecoded, hCommand, hGap', ↓reduceIte, Realizes]

theorem execute_safe (s : RegisterState) (h : s.Prepared) : execute s ≠ .invalid := by
  obtain ⟨_, _, hs⟩ := h
  have hInput : 59 ≤ (s.path ++ zeros s.gap).length := by
    simp only [RegisterState.span] at hs
    simp only [List.length_append, List.length_replicate]
    omega
  obtain ⟨d, hd⟩ := decode_root (s.path ++ zeros s.gap) hInput
  have bound := (decode_facts _ hd).lengthBound
  rw [rootHeight, List.length_append, List.length_replicate] at bound
  simp only [RegisterState.span] at hs
  cases hCommand : d.command with
  | halt => simp [execute, hd, executeDecoded, hCommand]
  | «break» k => simp [execute, hd, executeDecoded, hCommand]
  | «continue» k => cases k <;> simp [execute, hd, executeDecoded, hCommand]
  | register dec r =>
    have hGap : r.val + 3 ≤ d.rest.length := by have hr := r.isLt; omega
    simp [execute, hd, executeDecoded, hCommand, hGap]

end PalomarI3380.Engine
