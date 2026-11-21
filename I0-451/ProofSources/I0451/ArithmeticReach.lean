module
public import I0451.ArithmeticScan

/-! Composition of literal tape runs of model-valued length. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelPack (word : List Bool) (tail : V) : V := word.foldr modelPush tail

@[simp] theorem modelPack_nil (tail : V) : modelPack [] tail = tail := rfl

@[simp] theorem modelPack_cons (b : Bool) (word : List Bool) (tail : V) :
    modelPack (b :: word) tail = modelPush b (modelPack word tail) := rfl

theorem modelPack_append (a b : List Bool) (tail : V) :
    modelPack (a ++ b) tail = modelPack a (modelPack b tail) := by
  induction a with
  | nil => rfl
  | cons x a ih => simp only [List.cons_append, modelPack_cons, ih]

theorem modelRepeat_nat (b : Bool) (n : Nat) (tail : V) :
    modelRepeat b (n : V) tail = modelPack (List.replicate n b) tail := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.cast_succ, modelRepeat_succ, List.replicate_succ, modelPack_cons, ih]

def ModelReaches (table : Table) (start finish : V) : Prop := ∃ n, trace table n start = finish

namespace ModelReaches

theorem refl (table : Table) (config : V) : ModelReaches table config config :=
  ⟨0, trace_zero table config⟩

theorem trans {table : Table} {start middle finish : V}
    (first : ModelReaches table start middle) (last : ModelReaches table middle finish) :
    ModelReaches table start finish := by
  obtain ⟨m, first⟩ := first
  obtain ⟨n, last⟩ := last
  exact ⟨m + n, by rw [trace_add, first, last]⟩

theorem step {table : Table} {start finish : V}
    (moved : modelTick table start = finish) : ModelReaches table start finish :=
  ⟨1, by simpa only [zero_add, trace_zero, moved] using trace_succ table (0 : V) start⟩

theorem right {table : Table} {q t : Nat} {read write : Bool}
    (edge : row table q read = transition write true t) (l r : V) :
    ModelReaches table (modelConfig q l (modelPush read r))
      (modelConfig t (modelPush write l) r) :=
  .step (model_step_right edge l r)

theorem left {table : Table} {q t : Nat} {read write : Bool}
    (edge : row table q read = transition write false t) (a : Bool) (l r : V) :
    ModelReaches table (modelConfig q (modelPush a l) (modelPush read r))
      (modelConfig t l (modelPush a (modelPush write r))) :=
  .step (model_step_left edge a l r)

theorem enterLeft {table : Table} {q t : Nat} {read write : Bool}
    (edge : row table q read = transition write false t) (l r : V) :
    ModelReaches table (modelConfig q l (modelPush read r))
      (modelFromLeft t l (modelPush write r)) :=
  .step (model_move_left edge l r)

theorem moveLeft {table : Table} {q t : Nat} {read write : Bool}
    (edge : row table q read = transition write false t) (l r : V) :
    ModelReaches table (modelFromLeft q (modelPush read l) r)
      (modelFromLeft t l (modelPush write r)) := by
  rw [modelFromLeft_push]
  exact enterLeft edge l r

theorem leaveLeft {table : Table} {q t : Nat} {read write : Bool}
    (edge : row table q read = transition write true t) (l r : V) :
    ModelReaches table (modelFromLeft q (modelPush read l) r)
      (modelConfig t (modelPush write l) r) := by
  rw [modelFromLeft_push]
  exact right edge l r

theorem scanRight {table : Table} {q : Nat} {read write : Bool}
    (edge : row table q read = transition write true q) (n l r : V) :
    ModelReaches table (modelConfig q l (modelRepeat read n r))
      (modelConfig q (modelRepeat write n l) r) :=
  ⟨n, model_scan_right edge n l r⟩

theorem scanLeft {table : Table} {q : Nat} {read write : Bool}
    (edge : row table q read = transition write false q) (n l r : V) :
    ModelReaches table (modelFromLeft q (modelRepeat read n l) r)
      (modelFromLeft q l (modelRepeat write n r)) :=
  ⟨n, model_scan_left edge n l r⟩

theorem window {table : Table} {first last : Window} {n : Nat}
    (ran : first.run table n = some last) (l r : V) :
    ModelReaches table (modelWindow first l r) (modelWindow last l r) :=
  ⟨n, model_window_run ran l r⟩

/-- Internally finite paths can be composed even when each step uses a
different, model-valued number of tape moves. -/
theorem follow {table : Table} {path : V → V} {limit : V}
    (defined : 𝚺ᴬ₁-Function₁[V] path)
    (advance : ∀ j < limit, ModelReaches table (path j) (path (j + 1))) :
    ∀ j ≤ limit, ModelReaches table (path 0) (path j) := by
  intro j
  induction j using ISigma1.sigma1_succ_induction with
  | zero => intro _; exact ModelReaches.refl table _
  | succ j ih =>
    intro fits
    have before := succ_le_iff_lt.mp fits
    exact (ih (le_of_lt before)).trans (advance j before)
  | hP =>
    unfold ModelReaches
    definability

end ModelReaches

end I0451.Arithmetization
