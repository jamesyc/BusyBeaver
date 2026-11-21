module
public import I0451.ArithmeticDispatch
public import I0451.ArithmeticSelect
public import I0451.Issue

/-! Issue and selection from the literal decoder root. The instruction
and flag words have standard length. Register contents and the gap can
have any length in the arithmetic model. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open I0451.Runtime I0451.Runtime.IssueRows

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] modelRepeat modelPush modelFromLeft modelConfig trace

private theorem model_count_ones (op : RegisterOp) {i m : Nat}
    (bounded : i < 9) (available : m ≤ i) (l r : V) :
    ModelReaches literal
      (modelConfig (op.issue i) l (modelPack (List.replicate m true) r))
      (modelConfig (op.issue (i - m)) (modelPack (List.replicate m true) l) r) := by
  induction m generalizing i l with
  | zero => exact ModelReaches.refl literal _
  | succ m ih =>
    cases i with
    | zero => omega
    | succ i =>
      have diff : i + 1 - (m + 1) = i - m := by omega
      rw [diff]
      simp only [List.replicate_succ', modelPack_append, modelPack_cons, modelPack_nil]
      have head : modelPack (List.replicate m true) (modelPush true r) =
          modelPush true (modelPack (List.replicate m true) r) := by
        rw [← modelRepeat_nat, ← modelRepeat_nat, modelRepeat_push]
      rw [head]
      exact (ModelReaches.right (issueTrue op bounded) l _).trans
        (ih (by omega) (by omega) (modelPush true l))

theorem model_issued (op : RegisterOp) {i m : Nat} {word : List Bool}
    (bounded : i < 9) (available : m ≤ i)
    (path : Decoder.IssuePath root true false word (op.issue i)) (r : V) :
    ModelReaches literal (modelConfig root 1 (modelPack (word ++ List.replicate m true) r))
      (modelConfig (op.issue (i - m)) (modelPack (word ++ List.replicate m true).reverse 1) r) := by
  simp only [List.reverse_append, List.reverse_replicate, modelPack_append]
  have decoded := model_decoder_root path (modelPack (List.replicate m true) r)
  exact decoded.trans (model_count_ones op bounded available (modelPack word.reverse 1) r)

theorem model_select_pass (op : RegisterOp) {i m : Nat} {word : List Bool}
    (bounded : i < 9) (available : m ≤ i)
    (path : Decoder.IssuePath root true false word (op.issue i))
    (safe : SafeDispatch 0 word.reverse) (gap x : V) (xs : List V) (u r : V) :
    ModelReaches literal
      (modelConfig root 1 (modelPack (word ++ List.replicate m true)
        (modelRepeat false (gap + 1 + 1 + 1 + 1)
          (modelBlocks ((x :: xs) ++ [u]) (modelPush false r)))))
      (modelConfig root 1 (modelPack (word ++ List.replicate (m + 1) true)
        (modelRepeat false (gap + 1 + 1 + 1)
          (modelBlocks (x :: xs) (modelPush false (modelBlocks [u] r)))))) := by
  let flags := word ++ List.replicate m true
  let before := modelRepeat false (gap + 1 + 1) (modelBlocks ((x :: xs) ++ [u]) (modelPush false r))
  let after := modelRepeat false (gap + 1 + 1 + 1)
    (modelBlocks (x :: xs) (modelPush false (modelBlocks [u] r)))
  have issue := model_issued op bounded available path (modelPush false (modelPush false before))
  have enter := ModelReaches.right (issueFalse op (i := i - m) (by omega))
    (modelPack flags.reverse (1 : V)) (modelPush false before)
  have shift := model_select_preceding gap x xs u (modelPush false (modelPack flags.reverse 1)) r
  have safeFlags : SafeDispatch 0 flags.reverse := by
    simpa [flags, List.reverse_append] using safe.ones m
  have prepare := ModelReaches.moveLeft DispatchRows.breakZeroBit (modelPack flags.reverse (1 : V)) after
  have back := model_continue_zero (word := flags) safeFlags (modelPush true after)
  have before_unpack :
      modelRepeat false (gap + 1 + 1 + 1 + 1)
        (modelBlocks ((x :: xs) ++ [u]) (modelPush false r)) =
          modelPush false (modelPush false before) := by
    rw [modelRepeat_succ false (gap + 1 + 1 + 1), modelRepeat_succ false (gap + 1 + 1)]
  rw [before_unpack, List.replicate_succ', ← List.append_assoc]
  simpa only [flags, after, modelPack_append, modelPack_cons, modelPack_nil] using
    issue.trans (enter.trans (shift.trans (prepare.trans back)))

theorem model_enter_register (op : RegisterOp) {i : Nat} {word : List Bool} (bounded : i < 9)
    (path : Decoder.IssuePath root true false word (op.issue i)) (r : V) :
    ModelReaches literal (modelConfig root 1 (modelPack (word ++ List.replicate (i + 1) true) r))
      (modelConfig op.entry (modelPack (word ++ List.replicate (i + 1) true).reverse 1) r) := by
  have stage := model_issued op bounded (Nat.le_refl i) path (modelPush true r)
  rw [Nat.sub_self] at stage
  rw [List.replicate_succ', ← List.append_assoc, List.reverse_append, List.reverse_singleton]
  simpa only [modelPack_append, modelPack_cons, modelPack_nil] using
    stage.trans (ModelReaches.right (issueZeroRow op) _ r)

end I0451.Arithmetization
