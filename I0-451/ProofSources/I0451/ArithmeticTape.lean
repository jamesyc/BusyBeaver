module
public import I0451.ArithmeticRows
public import I0451.ArithmeticTrace
public import I0451.TapeRuns

/-! Literal tape transitions on model-valued tape contents. A finite
window run gives uniform identities for all choices of the two tails. -/
@[expose] public section
namespace I0451.Arithmetization

private theorem transition_decode (code : Nat) :
    transition (bit code) (bit (code / 2)) (code / 4) = code + 1 := by
  have to_nat (n : Nat) : (bit n).toNat = n % 2 := by
    unfold bit
    by_cases odd : n % 2 = 1
    · simp [odd]
    · rw [beq_false_of_ne odd]
      simp only [Bool.toNat_false]
      omega
  simp only [transition, to_nat]
  omega

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelPush (b : Bool) (tail : V) : V := 2 * tail + (b.toNat : V)

@[simp] theorem modelPush_false_zero : modelPush false (0 : V) = 0 := by
  simp [modelPush]

@[simp] theorem modelDiv_push (b : Bool) (tail : V) :
    modelDiv (modelPush b tail) 2 = tail := by
  apply div_mul_add'
  cases b <;> simp

@[simp] theorem modelRem_push (b : Bool) (tail : V) :
    modelRem (modelPush b tail) 2 = (b.toNat : V) := by
  unfold modelRem modelPush
  rw [mod_mul_add' _ _ (by simp)]
  apply mod_eq_self_of_lt
  cases b <;> simp

theorem modelPush_split (tape : V) :
    ∃ b : Bool, modelPush b (modelDiv tape 2) = tape := by
  rcases mod_two tape with zero | one
  · exact ⟨false, by simpa [modelPush, modelDiv, zero] using div_add_mod tape 2⟩
  · exact ⟨true, by simpa [modelPush, modelDiv, one] using div_add_mod tape 2⟩

noncomputable def modelConfig (q : Nat) (left right : V) : V := ⟪(q : V), left, right⟫

theorem model_two_mul_two : (2 : V) * 2 = 4 := by
  have numeric := congrArg (fun x : Nat => (x : V)) (show (2 : Nat) * 2 = 4 from rfl)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using numeric

private theorem move_code_fields (q : Nat) (w d : Bool) :
    let code := modelPush (V := V) w (modelPush d (q : V))
    code + 1 = (transition w d q : V) ∧
    code / 4 = (q : V) ∧ code % 2 = (w.toNat : V) ∧
    (code / 2) % 2 = (d.toNat : V) := by
  dsimp only
  have castCode :
      modelPush w (modelPush d (q : V)) + 1 = (transition w d q : V) := by
    unfold modelPush transition
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [mul_add, ← mul_assoc, model_two_mul_two]
  have div_w : modelPush w (modelPush d (q : V)) / 2 = modelPush d (q : V) :=
    modelDiv_push _ _
  refine ⟨castCode, ?_, modelRem_push _ _, ?_⟩
  · rw [← model_two_mul_two, Arithmetic.div_mul, div_w]
    exact modelDiv_push _ _
  · rw [div_w]
    exact modelRem_push _ _

private theorem apply_move {table : Table} {q t : Nat} {read write dir : Bool}
    (edge : row table q read = transition write dir t) (l r : V) :
    modelTick table (modelConfig q l (modelPush read r)) =
      if dir then modelConfig t (modelPush write l) r
      else modelConfig t (modelDiv l 2) (4 * r + 2 * (write.toNat : V) + modelRem l 2) := by
  let code := modelPush write (modelPush dir (t : V))
  have fields := move_code_fields (V := V) t write dir
  change code + 1 = _ ∧ code / 4 = _ ∧ code % 2 = _ ∧ (code / 2) % 2 = _ at fields
  have digit : modelDigit table (q : V) (modelPush read r) = code + 1 := by
    rw [modelDigit_literal_row _ _ _ _ (modelRem_push read r), edge, fields.1]
  symm
  apply (tickDef_eval table _ _).mp
  rw [tickDef_unpack]
  refine ⟨q, l, modelPush read r, rfl, Or.inr ⟨code, digit, ?_⟩⟩
  have h : modelPush read r / 2 = r := modelDiv_push _ _
  cases dir with
  | false =>
    refine Or.inr ⟨by simpa using fields.2.2.2, ?_⟩
    simp only [Bool.false_eq_true, ite_false, fields.2.1, fields.2.2.1, h]
    rfl
  | true =>
    refine Or.inl ⟨by simpa using fields.2.2.2, ?_⟩
    rw [h, fields.2.1, fields.2.2.1]
    rfl

theorem model_step_right {table : Table} {q t : Nat} {read write : Bool}
    (edge : row table q read = transition write true t) (l r : V) :
    modelTick table (modelConfig q l (modelPush read r)) =
      modelConfig t (modelPush write l) r := by
  simpa only [ite_true] using apply_move edge l r

theorem model_step_left {table : Table} {q t : Nat} {read write : Bool}
    (edge : row table q read = transition write false t) (a : Bool) (l r : V) :
    modelTick table (modelConfig q (modelPush a l) (modelPush read r)) =
      modelConfig t l (modelPush a (modelPush write r)) := by
  rw [apply_move edge]
  simp only [Bool.false_eq_true, ite_false, modelDiv_push, modelRem_push]
  unfold modelPush
  rw [mul_add, ← mul_assoc, model_two_mul_two, add_assoc]

noncomputable def modelWindow (w : Window) (l r : V) : V :=
  modelConfig w.state (w.left.foldr modelPush l) (w.right.foldr modelPush r)

theorem model_window_step {table : Table} {first last : Window}
    (step : first.step table = some last) (l r : V) :
    modelTick table (modelWindow first l r) = modelWindow last l r := by
  obtain ⟨q, left, right⟩ := first
  cases right with
  | nil => simp [Window.step] at step
  | cons read right =>
    cases row_eq : row table q read with
    | zero => simp [Window.step, row_eq] at step
    | succ code =>
      have edge : row table q read = transition (bit code) (bit (code / 2)) (code / 4) := by
        rw [transition_decode, row_eq]
      cases dir : bit (code / 2) with
      | false =>
        cases left with
        | nil => simp [Window.step, row_eq, dir] at step
        | cons a left =>
          simp [Window.step, row_eq, dir] at step
          subst last
          rw [dir] at edge
          exact model_step_left edge a _ _
      | true =>
        simp [Window.step, row_eq, dir] at step
        subst last
        rw [dir] at edge
        exact model_step_right edge _ _

theorem model_window_run {table : Table} {first last : Window} {n : Nat}
    (ran : first.run table n = some last) (l r : V) :
    trace table (n : V) (modelWindow first l r) = modelWindow last l r := by
  induction n generalizing first with
  | zero =>
    rw [show first = last from Option.some.inj ran]
    simp
  | succ n ih =>
    cases step : first.step table with
    | none => simp [Window.run, step] at ran
    | some next =>
      rw [show ((n + 1 : Nat) : V) = 1 + (n : V) by simp [add_comm], trace_add]
      have first_step : trace table (1 : V) (modelWindow first l r) = modelWindow next l r := by
        simpa only [zero_add, trace_zero] using
          (trace_succ table (0 : V) (modelWindow first l r)).trans (by
            rw [trace_zero]
            exact model_window_step step l r)
      rw [first_step]
      exact ih (by simpa [Window.run, step] using ran)

end I0451.Arithmetization
