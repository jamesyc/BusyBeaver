module
public import Foundation.FirstOrder.SetTheory.Basic.Model
@[expose] public section
/-! # Relativizing set-language formulas

An interpretation of the set language is given by three formulas: a domain,
membership and equality. `rel0` relativizes a formula to such an interpretation.
`rel1` does the same when the three formulas take one extra parameter, kept in the
outermost bound slot. The set language has no function symbols, so terms are
variables and relativization is a direct recursion. -/
namespace ZF209.Independence
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

/-- Interpretation formulas without a parameter. -/
structure RelData0 where
  dom : Semisentence ℒₛₑₜ 1
  mem : Semisentence ℒₛₑₜ 2
  eq : Semisentence ℒₛₑₜ 2

/-- Interpretation formulas with one parameter, the last argument. -/
structure RelData1 where
  dom : Semisentence ℒₛₑₜ 2
  mem : Semisentence ℒₛₑₜ 3
  eq : Semisentence ℒₛₑₜ 3

variable {ξ : Type*}

/-- Terms gain one bound variable on top. -/
def tcast {n : ℕ} : Semiterm ℒₛₑₜ ξ n → Semiterm ℒₛₑₜ ξ (n + 1)
  | .bvar i => .bvar i.castSucc
  | .fvar x => .fvar x
  | .func f _ => Empty.elim f

section Syntax
variable (D₀ : RelData0) (D₁ : RelData1)

/-- Relativization without a parameter. -/
def rel0 : ∀ {n : ℕ}, Semiformula ℒₛₑₜ ξ n → Semiformula ℒₛₑₜ ξ n
  | _, .verum => .verum
  | _, .falsum => .falsum
  | _, .rel Language.Set.Rel.eq ts => Rew.embSubsts ![ts 0, ts 1] ▹ D₀.eq
  | _, .rel Language.Set.Rel.mem ts => Rew.embSubsts ![ts 0, ts 1] ▹ D₀.mem
  | _, .nrel Language.Set.Rel.eq ts => ∼(Rew.embSubsts ![ts 0, ts 1] ▹ D₀.eq)
  | _, .nrel Language.Set.Rel.mem ts => ∼(Rew.embSubsts ![ts 0, ts 1] ▹ D₀.mem)
  | _, .and φ ψ => rel0 φ ⋏ rel0 ψ
  | _, .or φ ψ => rel0 φ ⋎ rel0 ψ
  | _, .all φ => ∀¹ ((Rew.embSubsts ![#0] ▹ D₀.dom) 🡒 rel0 φ)
  | _, .exs φ => ∃¹ ((Rew.embSubsts ![#0] ▹ D₀.dom) ⋏ rel0 φ)

/-- Relativization with a parameter in the outermost bound slot. -/
def rel1 : ∀ {n : ℕ}, Semiformula ℒₛₑₜ ξ n → Semiformula ℒₛₑₜ ξ (n + 1)
  | _, .verum => .verum
  | _, .falsum => .falsum
  | n, .rel Language.Set.Rel.eq ts =>
    Rew.embSubsts ![tcast (ts 0), tcast (ts 1), #(Fin.last n)] ▹ D₁.eq
  | n, .rel Language.Set.Rel.mem ts =>
    Rew.embSubsts ![tcast (ts 0), tcast (ts 1), #(Fin.last n)] ▹ D₁.mem
  | n, .nrel Language.Set.Rel.eq ts =>
    ∼(Rew.embSubsts ![tcast (ts 0), tcast (ts 1), #(Fin.last n)] ▹ D₁.eq)
  | n, .nrel Language.Set.Rel.mem ts =>
    ∼(Rew.embSubsts ![tcast (ts 0), tcast (ts 1), #(Fin.last n)] ▹ D₁.mem)
  | _, .and φ ψ => rel1 φ ⋏ rel1 ψ
  | _, .or φ ψ => rel1 φ ⋎ rel1 ψ
  | n, .all φ => ∀¹ ((Rew.embSubsts ![#0, #(Fin.last (n + 1))] ▹ D₁.dom) 🡒 rel1 φ)
  | n, .exs φ => ∃¹ ((Rew.embSubsts ![#0, #(Fin.last (n + 1))] ▹ D₁.dom) ⋏ rel1 φ)

end Syntax

section Semantics
variable {M N : Type*} [SetStructure M] [SetStructure N]

/-- Semantic hypotheses for `rel0`: the formulas read a set structure `N`. -/
structure Sem0 (D : RelData0) (π : M → N) : Prop where
  surj : ∀ y : N, ∃ x, M ⊧/![x] D.dom ∧ π x = y
  mem : ∀ x y, M ⊧/![x] D.dom → M ⊧/![y] D.dom → (M ⊧/![x, y] D.mem ↔ π x ∈ π y)
  eq : ∀ x y, M ⊧/![x] D.dom → M ⊧/![y] D.dom → (M ⊧/![x, y] D.eq ↔ π x = π y)

/-- Semantic hypotheses for `rel1` at the parameter value `e`. -/
structure Sem1 (D : RelData1) (e : M) (π : M → N) : Prop where
  surj : ∀ y : N, ∃ x, M ⊧/![x, e] D.dom ∧ π x = y
  mem : ∀ x y, M ⊧/![x, e] D.dom → M ⊧/![y, e] D.dom →
    (M ⊧/![x, y, e] D.mem ↔ π x ∈ π y)
  eq : ∀ x y, M ⊧/![x, e] D.dom → M ⊧/![y, e] D.dom →
    (M ⊧/![x, y, e] D.eq ↔ π x = π y)

lemma comp_cons' {n : ℕ} (π : M → N) (x : M) (b : Fin n → M) :
    π ∘ (x :> b) = π x :> (π ∘ b) := by
  funext i; cases i using Fin.cases <;> rfl

lemma val_comp {n : ℕ} (π : M → N) (b : Fin n → M) (f : ξ → M) (t : Semiterm ℒₛₑₜ ξ n) :
    π (t.val b f) = t.val (π ∘ b) (π ∘ f) := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func g _ => exact Empty.elim g

lemma val_dom {n : ℕ} {P : M → Prop} {b : Fin n → M} {f : ξ → M}
    (hb : ∀ i, P (b i)) (hf : ∀ x, P (f x)) (t : Semiterm ℒₛₑₜ ξ n) : P (t.val b f) := by
  cases t with
  | bvar i => exact hb i
  | fvar x => exact hf x
  | func g _ => exact Empty.elim g

lemma vec2_eq {α : Type*} (v : Fin 2 → α) : ![v 0, v 1] = v := by
  funext i; cases i using Fin.cases with
  | zero => rfl
  | succ j => rw [Subsingleton.elim j 0]; rfl

lemma comp_vec1 {n : ℕ} (b : Fin n → M) (f : ξ → M) (t : Semiterm ℒₛₑₜ ξ n) :
    (Semiterm.val b f ∘ ![t]) = ![t.val b f] := by
  funext i; rw [Subsingleton.elim i 0]; rfl

lemma comp_vec2 {n : ℕ} (b : Fin n → M) (f : ξ → M) (t₀ t₁ : Semiterm ℒₛₑₜ ξ n) :
    (Semiterm.val b f ∘ ![t₀, t₁]) = ![t₀.val b f, t₁.val b f] := by
  funext i; cases i using Fin.cases with
  | zero => rfl
  | succ j => rw [Subsingleton.elim j 0]; rfl

lemma comp_vec3 {n : ℕ} (b : Fin n → M) (f : ξ → M) (t₀ t₁ t₂ : Semiterm ℒₛₑₜ ξ n) :
    (Semiterm.val b f ∘ ![t₀, t₁, t₂]) = ![t₀.val b f, t₁.val b f, t₂.val b f] := by
  funext i; cases i using Fin.cases with
  | zero => rfl
  | succ j => cases j using Fin.cases with
    | zero => rfl
    | succ k => rw [Subsingleton.elim k 0]; rfl

/-- Meaning of `rel0`. -/
theorem eval_rel0 {D : RelData0} {π : M → N} (h : Sem0 D π) {n : ℕ}
    (φ : Semiformula ℒₛₑₜ ξ n) (b : Fin n → M) (f : ξ → M)
    (hb : ∀ i, M ⊧/![b i] D.dom) (hf : ∀ x, M ⊧/![f x] D.dom) :
    (rel0 D φ).Eval b f ↔ φ.Eval (π ∘ b) (π ∘ f) := by
  have hv : ∀ {n} {b : Fin n → M} (_ : ∀ i, M ⊧/![b i] D.dom) (t : Semiterm ℒₛₑₜ ξ n),
      M ⊧/![t.val b f] D.dom := fun hb t => val_dom (P := fun x => M ⊧/![x] D.dom) hb hf t
  have cons_dom : ∀ {n} {b : Fin n → M} (x : M), M ⊧/![x] D.dom → (∀ i, M ⊧/![b i] D.dom) →
      ∀ i, M ⊧/![(x :> b) i] D.dom := fun x hx hb i => by
    cases i using Fin.cases
    · exact hx
    · exact hb _
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r ts =>
    cases r with
    | eq =>
      simp only [rel0, Semiformula.eval_embSubsts, comp_vec2]
      change _ ↔ (ts 0).val (π ∘ b) (π ∘ f) = (ts 1).val (π ∘ b) (π ∘ f)
      rw [← val_comp, ← val_comp]
      exact h.eq _ _ (hv hb (ts 0)) (hv hb (ts 1))
    | mem =>
      simp only [rel0, Semiformula.eval_embSubsts, comp_vec2]
      change _ ↔ (ts 0).val (π ∘ b) (π ∘ f) ∈ (ts 1).val (π ∘ b) (π ∘ f)
      rw [← val_comp, ← val_comp]
      exact h.mem _ _ (hv hb (ts 0)) (hv hb (ts 1))
  | hnrel r ts =>
    cases r with
    | eq =>
      simp only [rel0, LogicalConnective.HomClass.map_neg, Semiformula.eval_embSubsts, comp_vec2]
      change ¬_ ↔ ¬(ts 0).val (π ∘ b) (π ∘ f) = (ts 1).val (π ∘ b) (π ∘ f)
      rw [← val_comp, ← val_comp]
      exact not_congr (h.eq _ _ (hv hb (ts 0)) (hv hb (ts 1)))
    | mem =>
      simp only [rel0, LogicalConnective.HomClass.map_neg, Semiformula.eval_embSubsts, comp_vec2]
      change ¬_ ↔ ¬(ts 0).val (π ∘ b) (π ∘ f) ∈ (ts 1).val (π ∘ b) (π ∘ f)
      rw [← val_comp, ← val_comp]
      exact not_congr (h.mem _ _ (hv hb (ts 0)) (hv hb (ts 1)))
  | hand φ ψ ihφ ihψ =>
    simp only [rel0, LogicalConnective.HomClass.map_and]
    exact and_congr (ihφ b hb) (ihψ b hb)
  | hor φ ψ ihφ ihψ =>
    simp only [rel0, LogicalConnective.HomClass.map_or]
    exact or_congr (ihφ b hb) (ihψ b hb)
  | hall φ ih =>
    simp only [rel0, Semiformula.eval_all, LogicalConnective.HomClass.map_imply,
      Semiformula.eval_embSubsts, comp_vec1]
    constructor
    · intro H X
      obtain ⟨x, hx, rfl⟩ := h.surj X
      rw [← comp_cons']
      exact (ih (x :> b) (cons_dom x hx hb)).mp (H x hx)
    · intro H x hx
      refine (ih (x :> b) (cons_dom x hx hb)).mpr ?_
      rw [comp_cons']
      exact H (π x)
  | hexs φ ih =>
    simp only [rel0, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
      Semiformula.eval_embSubsts, comp_vec1]
    constructor
    · rintro ⟨x, hx, H⟩
      exact ⟨π x, by rw [← comp_cons']; exact (ih (x :> b) (cons_dom x hx hb)).mp H⟩
    · rintro ⟨X, H⟩
      obtain ⟨x, hx, rfl⟩ := h.surj X
      exact ⟨x, hx, (ih (x :> b) (cons_dom x hx hb)).mpr (by rw [comp_cons']; exact H)⟩

lemma val_tcast {n : ℕ} (b : Fin n → M) (e : M) (f : ξ → M) (t : Semiterm ℒₛₑₜ ξ n) :
    (tcast t).val (Fin.snoc b e) f = t.val b f := by
  cases t with
  | bvar i => simp [tcast]
  | fvar x => rfl
  | func g _ => exact Empty.elim g

lemma val_last {n : ℕ} (b : Fin n → M) (e : M) (f : ξ → M) :
    (#(Fin.last n) : Semiterm ℒₛₑₜ ξ (n + 1)).val (Fin.snoc b e) f = e := by simp

lemma cons_snoc_last {n : ℕ} (x : M) (b : Fin n → M) (e : M) :
    (x :> Fin.snoc b e : Fin (n + 2) → M) (Fin.last (n + 1)) = e := by
  rw [show Fin.last (n + 1) = (Fin.last n).succ from rfl]; simp

lemma cons_snoc' {n : ℕ} (x : M) (b : Fin n → M) (e : M) :
    (x :> Fin.snoc b e : Fin (n + 2) → M) = Fin.snoc (x :> b) e := by
  show Fin.cons (α := fun _ => M) x (Fin.snoc (α := fun _ => M) b e) =
    Fin.snoc (α := fun _ => M) (Fin.cons (α := fun _ => M) x b) e
  exact Fin.cons_snoc_eq_snoc_cons (β := M) x b e

/-- Meaning of `rel1` at parameter `e`. -/
theorem eval_rel1 {D : RelData1} {e : M} {π : M → N} (h : Sem1 D e π) {n : ℕ}
    (φ : Semiformula ℒₛₑₜ ξ n) (b : Fin n → M) (f : ξ → M)
    (hb : ∀ i, M ⊧/![b i, e] D.dom) (hf : ∀ x, M ⊧/![f x, e] D.dom) :
    (rel1 D φ).Eval (Fin.snoc b e) f ↔ φ.Eval (π ∘ b) (π ∘ f) := by
  have hv : ∀ {n} {b : Fin n → M} (_ : ∀ i, M ⊧/![b i, e] D.dom) (t : Semiterm ℒₛₑₜ ξ n),
      M ⊧/![t.val b f, e] D.dom := fun hb t => val_dom (P := fun x => M ⊧/![x, e] D.dom) hb hf t
  have cons_dom : ∀ {n} {b : Fin n → M} (x : M), M ⊧/![x, e] D.dom →
      (∀ i, M ⊧/![b i, e] D.dom) → ∀ i, M ⊧/![(x :> b) i, e] D.dom := fun x hx hb i => by
    cases i using Fin.cases
    · exact hx
    · exact hb _
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r ts =>
    cases r with
    | eq =>
      simp only [rel1, Semiformula.eval_embSubsts, comp_vec3, val_tcast, val_last]
      change _ ↔ (ts 0).val (π ∘ b) (π ∘ f) = (ts 1).val (π ∘ b) (π ∘ f)
      rw [← val_comp, ← val_comp]
      exact h.eq _ _ (hv hb (ts 0)) (hv hb (ts 1))
    | mem =>
      simp only [rel1, Semiformula.eval_embSubsts, comp_vec3, val_tcast, val_last]
      change _ ↔ (ts 0).val (π ∘ b) (π ∘ f) ∈ (ts 1).val (π ∘ b) (π ∘ f)
      rw [← val_comp, ← val_comp]
      exact h.mem _ _ (hv hb (ts 0)) (hv hb (ts 1))
  | hnrel r ts =>
    cases r with
    | eq =>
      simp only [rel1, LogicalConnective.HomClass.map_neg, Semiformula.eval_embSubsts, comp_vec3,
        val_tcast, val_last]
      change ¬_ ↔ ¬(ts 0).val (π ∘ b) (π ∘ f) = (ts 1).val (π ∘ b) (π ∘ f)
      rw [← val_comp, ← val_comp]
      exact not_congr (h.eq _ _ (hv hb (ts 0)) (hv hb (ts 1)))
    | mem =>
      simp only [rel1, LogicalConnective.HomClass.map_neg, Semiformula.eval_embSubsts, comp_vec3,
        val_tcast, val_last]
      change ¬_ ↔ ¬(ts 0).val (π ∘ b) (π ∘ f) ∈ (ts 1).val (π ∘ b) (π ∘ f)
      rw [← val_comp, ← val_comp]
      exact not_congr (h.mem _ _ (hv hb (ts 0)) (hv hb (ts 1)))
  | hand φ ψ ihφ ihψ =>
    simp only [rel1, LogicalConnective.HomClass.map_and]
    exact and_congr (ihφ b hb) (ihψ b hb)
  | hor φ ψ ihφ ihψ =>
    simp only [rel1, LogicalConnective.HomClass.map_or]
    exact or_congr (ihφ b hb) (ihψ b hb)
  | hall φ ih =>
    simp only [rel1, Semiformula.eval_all, LogicalConnective.HomClass.map_imply,
      Semiformula.eval_embSubsts, comp_vec2, cons_snoc_last]
    constructor
    · intro H X
      obtain ⟨x, hx, rfl⟩ := h.surj X
      have := H x (by simpa using hx)
      rw [cons_snoc'] at this
      rw [← comp_cons']
      exact (ih (x :> b) (cons_dom x hx hb)).mp this
    · intro H x hx
      rw [cons_snoc']
      refine (ih (x :> b) (cons_dom x (by simpa using hx) hb)).mpr ?_
      rw [comp_cons']
      exact H (π x)
  | hexs φ ih =>
    simp only [rel1, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
      Semiformula.eval_embSubsts, comp_vec2, cons_snoc_last]
    constructor
    · rintro ⟨x, hx, H⟩
      rw [cons_snoc'] at H
      exact ⟨π x, by
        rw [← comp_cons']; exact (ih (x :> b) (cons_dom x (by simpa using hx) hb)).mp H⟩
    · rintro ⟨X, H⟩
      obtain ⟨x, hx, rfl⟩ := h.surj X
      refine ⟨x, by simpa using hx, ?_⟩
      rw [cons_snoc']
      exact (ih (x :> b) (cons_dom x hx hb)).mpr (by rw [comp_cons']; exact H)

end Semantics

end ZF209.Independence
