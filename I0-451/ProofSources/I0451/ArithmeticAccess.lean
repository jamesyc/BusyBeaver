module
public import I0451.ArithmeticIssue
public import I0451.ArithmeticDecrement
public import I0451.RegisterAccess

/-! The literal register operations starting at a full decoder frame. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] modelRepeat modelPush modelFromLeft modelConfig trace

noncomputable def modelFrame (word : List Bool) (gap : V) (regs : List V) : V :=
  modelConfig root 1 (modelPack word (modelRepeat false gap (modelBlocks regs 0)))

private noncomputable def intermediate (word : List Bool) (m : Nat) (gap : V)
    (before after : List V) : V :=
  modelConfig root 1 (modelPack (word ++ List.replicate m true)
    (modelRepeat false gap (modelBlocks before (modelPush false (modelBlocks after 0)))))

private theorem model_select_many (op : RegisterOp) {i : Nat} {word : List Bool}
    (bounded : i < 9) (path : Decoder.IssuePath root true false word (op.issue i))
    (safe : SafeDispatch 0 word.reverse) (gap x : V) (xs todo selected : List V)
    (m : Nat) (within : m + todo.length ≤ i + 1) :
    ModelReaches literal
      (intermediate word m (gap + (todo.length : V) + 1 + 1 + 1)
        ((x :: xs) ++ todo.reverse) selected)
      (intermediate word (m + todo.length) (gap + 1 + 1 + 1)
        (x :: xs) (todo.reverse ++ selected)) := by
  induction todo generalizing selected m with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero, add_zero, List.reverse_nil, List.append_nil,
      List.nil_append]
    exact ModelReaches.refl literal _
  | cons u todo ih =>
    have available : m ≤ i := by simp only [List.length_cons] at within; omega
    have select := model_select_pass op bounded available path safe
      (gap + (todo.length : V)) x (xs ++ todo.reverse) u (modelBlocks selected 0)
    have placed : modelBlocks [u] (modelBlocks selected 0) = modelBlocks (u :: selected) 0 := rfl
    rw [placed] at select
    have tail := ih (u :: selected) (m + 1) (by simp only [List.length_cons] at within; omega)
    have joined := select.trans tail
    have firstGap : gap + ((todo.length + 1 : Nat) : V) + 1 + 1 + 1 =
        gap + (todo.length : V) + 1 + 1 + 1 + 1 := by
      rw [Nat.cast_succ, ← add_assoc]
    have flag : m + (todo.length + 1) = m + 1 + todo.length := by omega
    simpa only [intermediate, List.reverse_cons, List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append, List.length_cons, firstGap, flag] using joined

theorem model_reach_selected (op : RegisterOp) {i : Nat} {word : List Bool}
    (bounded : i < 9) (path : Decoder.IssuePath root true false word (op.issue i))
    (safe : SafeDispatch 0 word.reverse) (gap x value : V)
    (xs suffix : List V) (index : suffix.length = i) :
    ModelReaches literal
      (modelFrame word (gap + ((i + 1 : Nat) : V) + 1 + 1 + 1) ((x :: xs) ++ value :: suffix))
      (modelConfig op.entry (modelPack (word ++ List.replicate (i + 1) true).reverse 1)
        (modelPush false (modelRepeat false (gap + 1 + 1)
          (modelBlocks (x :: xs) (modelPush false (modelBlocks (value :: suffix) 0)))))) := by
  have length : (value :: suffix).reverse.length = i + 1 := by simp [index]
  have moved := model_select_many op bounded path safe gap x xs (value :: suffix).reverse [] 0
    (by rw [length, Nat.zero_add])
  have converted :
      ModelReaches literal
        (modelFrame word (gap + ((i + 1 : Nat) : V) + 1 + 1 + 1) ((x :: xs) ++ value :: suffix))
        (modelConfig root 1 (modelPack (word ++ List.replicate (i + 1) true)
          (modelPush false (modelRepeat false (gap + 1 + 1)
            (modelBlocks (x :: xs) (modelPush false (modelBlocks (value :: suffix) 0))))))) := by
    simpa only [length, List.reverse_reverse, Nat.zero_add, List.append_nil, intermediate,
      List.replicate_zero, modelBlocks, modelPush_false_zero, modelFrame,
      modelRepeat_succ false (gap + 1 + 1)] using moved
  exact converted.trans (model_enter_register op bounded path _)

private theorem carry_flags (n : Nat) (suffix : List Bool) :
    carry (List.replicate n true ++ suffix) = List.replicate n false ++ carry suffix := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, carry, ih]

private theorem return_after_flags {word : List Bool} (safe : SafeDispatch 0 word.reverse)
    (flags : Nat) (gap : V) (regs : List V) :
    ModelReaches literal
      (modelFromLeft breakZero (modelPack (word ++ List.replicate flags true).reverse 1)
        (modelRepeat false gap (modelBlocks regs 0)))
      (modelFrame (carry word.reverse).reverse (gap + (flags : V)) regs) := by
  have safeFlags : SafeDispatch 0 (word ++ List.replicate flags true).reverse := by
    simpa only [List.reverse_append, List.reverse_replicate] using safe.ones flags
  have back := model_break_zero safeFlags (modelRepeat false gap (modelBlocks regs 0))
  simpa only [List.reverse_append, List.reverse_replicate, carry_flags, modelPack_append,
    ← modelRepeat_nat, ← modelRepeat_add, modelFrame] using back

theorem model_increment_register {i : Nat} {word : List Bool} (bounded : i < 9)
    (path : Decoder.IssuePath root true false word (RegisterOp.inc.issue i))
    (safe : SafeDispatch 0 word.reverse) (gap x value : V)
    (xs suffix : List V) (index : suffix.length = i) :
    ModelReaches literal
      (modelFrame word (gap + ((i + 1 : Nat) : V) + 1 + 1 + 1) ((x :: xs) ++ value :: suffix))
      (modelFrame (carry word.reverse).reverse (gap + ((i + 1 : Nat) : V) + 1 + 1 + 1)
        ((x :: xs) ++ (value + 1) :: suffix)) := by
  let flags := word ++ List.replicate (i + 1) true
  have selected := model_reach_selected .inc bounded path safe gap x value xs suffix index
  have updated := model_increment_selected gap x xs (modelPack flags.reverse (1 : V))
    (modelBlocks (value :: suffix) 0)
  have updateTape : modelPush true (modelBlocks (value :: suffix) (0 : V)) =
      modelBlocks ((value + 1) :: suffix) 0 := by
    simp only [modelBlocks, modelRepeat_succ true (value + 1)]
  rw [updateTape, ← modelBlocks_append] at updated
  have back := return_after_flags safe (i + 1) (gap + 1 + 1 + 1) ((x :: xs) ++ (value + 1) :: suffix)
  rw [show gap + 1 + 1 + 1 + ((i + 1 : Nat) : V) =
      gap + ((i + 1 : Nat) : V) + 1 + 1 + 1 by ac_rfl] at back
  exact selected.trans (updated.trans back)

theorem model_decrement_register_pos {i : Nat} {word : List Bool} (bounded : i < 9)
    (path : Decoder.IssuePath root true false word (RegisterOp.dec.issue i))
    (safe : SafeDispatch 0 word.reverse) (gap x value : V)
    (xs suffix : List V) (index : suffix.length = i) :
    ModelReaches literal
      (modelFrame word (gap + ((i + 1 : Nat) : V) + 1 + 1 + 1) ((x :: xs) ++ (value + 1) :: suffix))
      (modelFrame (carry word.reverse).reverse (gap + ((i + 1 : Nat) : V) + 1 + 1 + 1 + 1)
        ((x :: xs) ++ value :: suffix)) := by
  let flags := word ++ List.replicate (i + 1) true
  have selected := model_reach_selected .dec bounded path safe gap x (value + 1) xs suffix index
  have updated := model_decrement_positive gap x value xs suffix (modelPack flags.reverse (1 : V))
  have back := return_after_flags safe (i + 1) (gap + 1 + 1 + 1 + 1) ((x :: xs) ++ value :: suffix)
  rw [show gap + 1 + 1 + 1 + 1 + ((i + 1 : Nat) : V) =
      gap + ((i + 1 : Nat) : V) + 1 + 1 + 1 + 1 by ac_rfl] at back
  exact selected.trans (updated.trans back)

theorem model_decrement_register_zero {i : Nat} {word rev : List Bool}
    (bounded : i < 9) (path : Decoder.IssuePath root true false word (RegisterOp.dec.issue i))
    (safe : SafeDispatch 0 word.reverse) (restSafe : SafeDispatch 0 rev)
    (gap last : V) (trailing : Nat) (before suffix : List V) (index : suffix.length = i)
    (split : word.reverse = List.replicate trailing true ++ false :: rev) :
    ModelReaches literal
      (modelFrame word (gap + ((i + 1 : Nat) : V) + 1 + 1 + 1) (before ++ last :: 0 :: suffix))
      (modelFrame (carry rev).reverse
        (gap + ((i + 1 : Nat) : V) + 1 + 1 + 1 + 1 + (trailing : V) + 1)
        (before ++ last :: 0 :: suffix)) := by
  let flags := word ++ List.replicate (i + 1) true
  let regs := before ++ last :: 0 :: suffix
  have selected : ModelReaches literal (modelFrame word (gap + ((i + 1 : Nat) : V) + 1 + 1 + 1) regs)
      (modelConfig decrement (modelPack flags.reverse 1)
        (modelPush false (modelRepeat false (gap + 1 + 1)
          (modelBlocks (before ++ [last]) (modelPush false (modelBlocks (0 :: suffix) 0)))))) := by
    cases before with
    | nil => exact model_reach_selected .dec bounded path safe gap last 0 [] suffix index
    | cons a as =>
      simpa only [regs, flags, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append, RegisterOp.entry]
        using model_reach_selected .dec bounded path safe gap a 0 (as ++ [last]) suffix index
  have checked := model_decrement_zero gap last before suffix (modelPack flags.reverse (1 : V))
  have reverseFlags : flags.reverse = List.replicate ((i + 1) + trailing) true ++ false :: rev := by
    simp [flags, List.reverse_append, split, ← List.append_assoc]
  rw [reverseFlags, modelPack_append, modelPack_cons, ← modelRepeat_nat] at selected checked
  have back := model_break_one restSafe (((i + 1) + trailing : Nat) : V)
    (modelRepeat false (gap + 1 + 1 + 1 + 1) (modelBlocks regs 0))
  have lengthOrder : gap + 1 + 1 + 1 + 1 + (((i + 1) + trailing : Nat) : V) + 1 =
      gap + ((i + 1 : Nat) : V) + 1 + 1 + 1 + 1 + (trailing : V) + 1 := by
    rw [Nat.cast_add]
    ac_rfl
  rw [← modelRepeat_add, ← modelRepeat_succ, lengthOrder] at back
  exact selected.trans (checked.trans back)

end I0451.Arithmetization
