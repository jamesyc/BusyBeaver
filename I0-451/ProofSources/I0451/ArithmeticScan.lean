module
public import I0451.ArithmeticTape

/-! A tape block can have any model-valued length. The scan proofs use
arithmetic induction on the consumed length, keeping the initial tape
and the full length fixed throughout the induction. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[definability] theorem modelPush_definable (b : Bool) :
    𝚺ᴬ₁-Function₁[V] (modelPush b : V → V) := by
  unfold modelPush
  definability

@[definability] theorem modelConfig_definable (q : Nat) :
    𝚺ᴬ₁-Function₂[V] (modelConfig q : V → V → V) := by
  unfold modelConfig
  definability

def repeatBlueprint (b : Bool) : PR.Blueprint 1 where
  zero := .mkSigma “result tail. result = tail”
  succ := .mkSigma “result prior time tail. result = 2 * prior + ↑(b.toNat)”

noncomputable def repeatConstruction (b : Bool) : PR.Construction V (repeatBlueprint b) where
  zero := fun v => v 0
  succ := fun _ _ prior => modelPush b prior
  zero_defined := .mk fun v => by simp [repeatBlueprint]
  succ_defined := .mk fun v => by simp [repeatBlueprint, modelPush, numeral_eq_natCast]

noncomputable def modelRepeat (b : Bool) (n tail : V) : V :=
  (repeatConstruction b).result ![tail] n

theorem repeat_eval (b : Bool) (result length tail : V) :
    (repeatBlueprint b).resultDef.val.Evalb ![result, length, tail] ↔
      result = modelRepeat b length tail := by
  simp only [(repeatConstruction b).result_defined_iff, Matrix.cons_val_zero,
    Matrix.cons_val_succ, modelRepeat]
  rfl

theorem repeat_defined (b : Bool) :
    𝚺ᴬ₁-Function₂[V] (modelRepeat b : V → V → V) via (repeatBlueprint b).resultDef := .mk fun v => by
  rw [Matrix.fun_eq_vec_three v]
  exact repeat_eval _ _ _ _

@[definability] instance repeat_definable (b : Bool) :
    𝚺ᴬ₁-Function₂[V] (modelRepeat b : V → V → V) :=
  (repeat_defined b).to_definable

@[simp] theorem modelRepeat_zero (b : Bool) (tail : V) : modelRepeat b 0 tail = tail := by
  unfold modelRepeat
  rw [PR.Construction.result_zero]
  rfl

@[simp] theorem modelRepeat_succ (b : Bool) (n tail : V) :
    modelRepeat b (n + 1) tail = modelPush b (modelRepeat b n tail) := by
  simp [modelRepeat, repeatConstruction]

theorem modelRepeat_add (b : Bool) (m n tail : V) :
    modelRepeat b (m + n) tail = modelRepeat b n (modelRepeat b m tail) := by
  induction n using ISigma1.sigma1_succ_induction with
  | zero => simp
  | succ n ih => rw [← add_assoc, modelRepeat_succ, modelRepeat_succ, ih]
  | hP => definability

theorem modelRepeat_push (b : Bool) (n tail : V) :
    modelRepeat b n (modelPush b tail) = modelPush b (modelRepeat b n tail) := by
  have one : modelRepeat b 1 tail = modelPush b tail := by
    simpa only [zero_add, modelRepeat_zero] using modelRepeat_succ b (0 : V) tail
  rw [← one, ← modelRepeat_add, add_comm (1 : V) n, modelRepeat_succ]

/-- Verify an internally finite sequence of configurations by checking its
definable formula for the configuration at each clock value. -/
theorem trace_follows (table : Nat) (limit : V) (path : V → V)
    (defined : 𝚺ᴬ₁-Function₁[V] path)
    (advance : ∀ j < limit, modelTick table (path j) = path (j + 1)) :
    ∀ j ≤ limit, trace table j (path 0) = path j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction with
  | zero => intro _; exact trace_zero table (path 0)
  | succ j ih =>
    intro fits
    have before := succ_le_iff_lt.mp fits
    rw [trace_succ, ih (le_of_lt before), advance j before]
  | hP => definability

private theorem remaining_succ {j limit : V} (before : j < limit) :
    limit - j = (limit - (j + 1)) + 1 := by
  simpa only [zero_add, add_zero] using (sub_succ_add_succ before (0 : V)).symm

theorem model_scan_right {table : Table} {q : Nat} {read write : Bool}
    (edge : row table q read = transition write true q) (n l r : V) :
    trace table n (modelConfig q l (modelRepeat read n r)) =
      modelConfig q (modelRepeat write n l) r := by
  let path (j : V) := modelConfig q (modelRepeat write j l) (modelRepeat read (n - j) r)
  have defined : 𝚺ᴬ₁-Function₁[V] path := by
    dsimp only [path, modelConfig]
    definability
  have advance (j : V) (before : j < n) : modelTick table (path j) = path (j + 1) := by
    dsimp only [path]
    rw [remaining_succ before, modelRepeat_succ, model_step_right edge, modelRepeat_succ]
  simpa only [path, modelRepeat_zero, Arithmetic.sub_zero, Arithmetic.sub_self] using
    trace_follows table n path defined advance n (le_refl n)

noncomputable def modelFromLeft (q : Nat) (l r : V) : V :=
  modelConfig q (modelDiv l 2) (2 * r + modelRem l 2)

@[definability] theorem modelFromLeft_definable (q : Nat) :
    𝚺ᴬ₁-Function₂[V] (modelFromLeft q : V → V → V) := by
  unfold modelFromLeft modelConfig modelDiv modelRem
  definability

@[simp] theorem modelFromLeft_push (q : Nat) (a : Bool) (l r : V) :
    modelFromLeft q (modelPush a l) r = modelConfig q l (modelPush a r) := by
  rw [modelFromLeft, modelDiv_push, modelRem_push]
  rfl

theorem model_move_left {table : Table} {q t : Nat} {read write : Bool}
    (edge : row table q read = transition write false t) (l r : V) :
    modelTick table (modelConfig q l (modelPush read r)) =
      modelFromLeft t l (modelPush write r) := by
  obtain ⟨a, split⟩ := modelPush_split l
  rw [← split, model_step_left edge a, modelFromLeft_push]

theorem model_scan_left {table : Table} {q : Nat} {read write : Bool}
    (edge : row table q read = transition write false q) (n l r : V) :
    trace table n (modelFromLeft q (modelRepeat read n l) r) =
      modelFromLeft q l (modelRepeat write n r) := by
  let path (j : V) := modelFromLeft q (modelRepeat read (n - j) l) (modelRepeat write j r)
  have defined : 𝚺ᴬ₁-Function₁[V] path := by
    dsimp only [path, modelConfig, modelFromLeft, modelDiv, modelRem]
    definability
  have advance (j : V) (before : j < n) : modelTick table (path j) = path (j + 1) := by
    dsimp only [path]
    rw [remaining_succ before, modelRepeat_succ, modelFromLeft_push,
      model_move_left edge, modelRepeat_succ]
  simpa only [path, modelRepeat_zero, Arithmetic.sub_zero, Arithmetic.sub_self] using
    trace_follows table n path defined advance n (le_refl n)

end I0451.Arithmetization
