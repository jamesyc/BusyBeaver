module
public import I0451.RegisterIncrement
public import I0451.Dispatch

/-! Direct proof of the moving double-zero selector. One pass moves the
extra zero one register to the left without changing any register value. -/

@[expose] public section
namespace I0451.Runtime

namespace SelectRows

theorem selectEntry :
    row literal select false = transition true true selectGap := by decide +kernel
theorem gapZero :
    row literal selectGap false = transition false true selectGap := by decide +kernel
theorem gapOne :
    row literal selectGap true = transition true true selectOnes := by decide +kernel
theorem scanOne :
    row literal selectOnes true = transition true true selectOnes := by decide +kernel
theorem scanZero :
    row literal selectOnes false = transition false true selectSeparator := by decide +kernel
theorem sepOne :
    row literal selectSeparator true = transition true true selectOnes := by decide +kernel
theorem sepZero :
    row literal selectSeparator false = transition false false selectBack := by decide +kernel
theorem backZero :
    row literal selectBack false = transition true false selectReverse := by decide +kernel
theorem reverseOne :
    row literal selectReverse true = transition true false selectReverse := by decide +kernel
theorem reverseZero :
    row literal selectReverse false = transition false true selectBack := by decide +kernel
theorem backOne :
    row literal selectBack true = transition false false returnStart := by decide +kernel

end SelectRows

open SelectRows

private theorem scanBlock {q : Nat} (entry : row literal q true = transition true true selectOnes)
    (x l r : Nat) :
    Reaches literal ⟨q, l, pack (blocks [x]) r⟩
      ⟨selectSeparator, pack (blocks [x]).reverse l, r⟩ := by
  have first := Reaches.right entry l (pack (List.replicate x true) (push false r))
  have middle : Reaches literal _ _ :=
    ⟨x, scan_right scanOne x (push true l) (push false r)⟩
  have all := first.trans (middle.trans (Reaches.right scanZero _ _))
  simpa [blocks, List.replicate_succ, pack_append, List.reverse_append] using all

private theorem scanBlocks (xs : List Nat) (l r : Nat) :
    Reaches literal ⟨selectSeparator, l, pack (blocks xs) r⟩
      ⟨selectSeparator, pack (blocks xs).reverse l, r⟩ := by
  induction xs generalizing l with
  | nil => exact ⟨0, rfl⟩
  | cons x xs ih =>
    rw [show x :: xs = [x] ++ xs from rfl, blocks_append, List.reverse_append,
      pack_append, pack_append]
    exact (scanBlock sepOne x l _).trans (ih _)

private theorem leading_zero (x : Nat) (xs : List Nat) :
    ∃ rest, (blocks (x :: xs)).reverse = false :: rest := by
  induction xs generalizing x with
  | nil => exact ⟨(List.replicate (x + 1) true).reverse, by
      simp [blocks, List.reverse_append]⟩
  | cons z zs ih =>
    obtain ⟨rest, eq⟩ := ih z
    refine ⟨rest ++ (blocks [x]).reverse, ?_⟩
    rw [show x :: z :: zs = [x] ++ z :: zs from rfl, blocks_append, List.reverse_append, eq]
    rfl

private theorem shiftBoundary (gap x : Nat) (xs : List Nat) (u l r : Nat) :
    Reaches literal
      ⟨select, l, push false (pack (List.replicate (gap + 2) false ++
        blocks (x :: xs ++ [u])) (push false r))⟩
      (fromLeft returnStart
        (pack (blocks (x :: xs)).reverse (pack (List.replicate (gap + 2) false) (push true l)))
        (push false (pack (blocks [u]) r))) := by
  let leftGap := pack (List.replicate (gap + 2) false) (push true l)
  let leftPrefix := pack (blocks (x :: xs)).reverse leftGap
  let rightBlock := pack (blocks [u]) (push false r)
  have initial : Reaches literal
      ⟨select, l, push false (pack (List.replicate (gap + 2) false ++
        blocks (x :: xs ++ [u])) (push false r))⟩
      ⟨selectGap, leftGap, pack (blocks (x :: xs)) rightBlock⟩ := by
    have rightShape : pack (List.replicate (gap + 2) false ++ blocks (x :: xs ++ [u])) (push false r)
        = pack (List.replicate (gap + 2) false) (pack (blocks (x :: xs)) rightBlock) := by
      rw [show x :: xs ++ [u] = (x :: xs) ++ [u] from rfl, blocks_append]
      simp [pack_append, rightBlock]
    rw [rightShape]
    exact (Reaches.right selectEntry l _).trans
      ⟨gap + 2, scan_right gapZero _ _ _⟩
  have across : Reaches literal
      ⟨selectGap, leftGap, pack (blocks (x :: xs)) rightBlock⟩
      ⟨selectSeparator, leftPrefix, rightBlock⟩ := by
    have eq : x :: xs = [x] ++ xs := rfl
    simp only [leftPrefix, eq, blocks_append, List.reverse_append, pack_append]
    exact (scanBlock gapOne x _ _).trans (scanBlocks xs _ _)
  have beforeShift := scanBlock sepOne u leftPrefix (push false r)
  have back : Reaches literal
      ⟨selectSeparator, pack (blocks [u]).reverse leftPrefix, push false r⟩
      (fromLeft selectReverse (pack (List.replicate (u + 1) true) leftPrefix)
        (push true (push false r))) := by
    have leftShape : pack (blocks [u]).reverse leftPrefix =
        push false (pack (List.replicate (u + 1) true) leftPrefix) := by
      simp [blocks, List.reverse_append]
    rw [leftShape]
    have second := Reaches.left' backZero (pack (List.replicate (u + 1) true) leftPrefix) (push false r)
    rw [fromLeft_push] at second
    exact (Reaches.left sepZero false _ _).trans second
  have backward := Reaches.scanLeft reverseOne (u + 1) leftPrefix (push true (push false r))
  have returnLeg : Reaches literal
      (fromLeft selectReverse leftPrefix (pack (List.replicate (u + 1) true) (push true (push false r))))
      (fromLeft returnStart leftPrefix (push false (pack (blocks [u]) r))) := by
    obtain ⟨rest, eq⟩ := leading_zero x xs
    have justBefore : leftPrefix = push false (pack rest leftGap) := by
      simp only [leftPrefix, eq, pack_cons]
    have after : pack (List.replicate (u + 1) true) (push true (push false r)) =
        push true (pack (blocks [u]) r) := by
      rw [← pack_repeat_last, List.replicate_succ, pack_cons]
      simp [blocks, pack_append]
    simp only [justBefore, after, fromLeft_push]
    exact (Reaches.right reverseZero _ _).trans (Reaches.left backOne false _ _)
  exact initial.trans (across.trans (beforeShift.trans (back.trans (backward.trans returnLeg))))

/-- Shift the extra delimiter from after register `u` to before it,
keeping the value of `u` and the rest of the tape intact. -/
theorem select_preceding (gap x : Nat) (xs : List Nat) (u l r : Nat) :
    Reaches literal
      ⟨select, l, push false (pack (List.replicate (gap + 2) false ++
        blocks (x :: xs ++ [u])) (push false r))⟩
      (fromLeft breakZero l
        (pack (List.replicate (gap + 3) false ++ blocks (x :: xs))
          (push false (pack (blocks [u]) r)))) :=
  (shiftBoundary gap x xs u l r).trans
    (return_over gap (x :: xs) l (push false (pack (blocks [u]) r)))

end I0451.Runtime
