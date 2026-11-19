module
public import ConcreteChallengeSentenceTransport
public import Palomar207StatementDefinitions
public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy
public import ConcreteChallengeArithmetic
public import ConcreteArithmeticModelStructure
@[expose] public section
/-! # Σ1 soundness in the Challenge's form gives Foundation's form

A Foundation Σ1 formula is compiled structurally into the Challenge's
`SigmaFormula`. Atoms and connectives map to atoms and connectives; the only
universal quantifiers in a Σ1 formula are bounded by `<` and map to `forallLt`.
The compiled formula has the same meaning in ℕ, and in every ZF model its
relational meaning agrees with the formula read in ω. -/
namespace ZF207.Independence.SigmaBridge
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory
open ZF207.OmegaInterpretation PalomarZF207
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

abbrev ATerm (n : ℕ) := Semiterm ℒₒᵣ Empty n
abbrev AForm (n : ℕ) := Semiformula ℒₒᵣ Empty n

/-- Terms, reading the bound variable `#i` as `var (i - k)`. -/
def term {n : ℕ} (k : ℕ) : ATerm n → ArithTerm
  | .bvar i => .var (i.val - k)
  | .fvar x => x.elim
  | .func Language.ORing.Func.zero _ => .zero
  | .func Language.ORing.Func.one _ => .one
  | .func Language.ORing.Func.add v => .add (term k (v 0)) (term k (v 1))
  | .func Language.ORing.Func.mul v => .mul (term k (v 0)) (term k (v 1))

def atom {n : ℕ} (v : Fin 2 → ATerm n) (eq pos : Bool) : SigmaFormula :=
  .atom (term 0 (v 0)) (term 0 (v 1)) eq pos

/-- Formulas. A universal quantifier not of the form `∀ x < t` maps to falsity. -/
def formula : {n : ℕ} → AForm n → SigmaFormula
  | _, .verum => .atom .zero .zero true true
  | _, .falsum => .atom .zero .zero true false
  | _, .rel Language.ORing.Rel.eq v => atom v true true
  | _, .rel Language.ORing.Rel.lt v => atom v false true
  | _, .nrel Language.ORing.Rel.eq v => atom v true false
  | _, .nrel Language.ORing.Rel.lt v => atom v false false
  | _, .and φ ψ => .conj (formula φ) (formula ψ)
  | _, .or φ ψ => .disj (formula φ) (formula ψ)
  | _, .exs φ => .exists_ (formula φ)
  | _, .all (.or (.nrel Language.ORing.Rel.lt v) ψ) => .forallLt (term 1 (v 1)) (formula ψ)
  | _, .all _ => .atom .zero .zero true false

/-- Every universal quantifier has the form `∀ x < t`. -/
def Good : {n : ℕ} → AForm n → Prop
  | _, .and φ ψ => Good φ ∧ Good ψ
  | _, .or φ ψ => Good φ ∧ Good ψ
  | _, .exs φ => Good φ
  | _, .all (.or (.nrel Language.ORing.Rel.lt v) ψ) => v 0 = #0 ∧ (v 1).Positive ∧ Good ψ
  | _, .all _ => False
  | _, _ => True

lemma term_bShift {n : ℕ} (k : ℕ) : ∀ t : ATerm n, term (k + 1) (Rew.bShift t) = term k t
  | .bvar i => by simp [term]
  | .fvar x => x.elim
  | .func Language.ORing.Func.zero v => by simp [Rew.func, term]
  | .func Language.ORing.Func.one v => by simp [Rew.func, term]
  | .func Language.ORing.Func.add v => by
    simp only [Rew.func, term, Function.comp_apply]; rw [term_bShift k (v 0), term_bShift k (v 1)]
  | .func Language.ORing.Func.mul v => by
    simp only [Rew.func, term, Function.comp_apply]; rw [term_bShift k (v 0), term_bShift k (v 1)]

lemma term_bound {n : ℕ} : ∀ t : ATerm n, (term 0 t).bound n
  | .bvar i => by simp [term, ArithTerm.bound]
  | .fvar x => x.elim
  | .func Language.ORing.Func.zero _ => trivial
  | .func Language.ORing.Func.one _ => trivial
  | .func Language.ORing.Func.add v => ⟨term_bound (v 0), term_bound (v 1)⟩
  | .func Language.ORing.Func.mul v => ⟨term_bound (v 0), term_bound (v 1)⟩

lemma formula_bound : ∀ {n : ℕ} (φ : AForm n), Good φ → (formula φ).bound n
  | _, .verum, _ => ⟨trivial, trivial⟩
  | _, .falsum, _ => ⟨trivial, trivial⟩
  | _, .rel Language.ORing.Rel.eq v, _ => ⟨term_bound _, term_bound _⟩
  | _, .rel Language.ORing.Rel.lt v, _ => ⟨term_bound _, term_bound _⟩
  | _, .nrel Language.ORing.Rel.eq v, _ => ⟨term_bound _, term_bound _⟩
  | _, .nrel Language.ORing.Rel.lt v, _ => ⟨term_bound _, term_bound _⟩
  | _, .and φ ψ, h => ⟨formula_bound φ h.1, formula_bound ψ h.2⟩
  | _, .or φ ψ, h => ⟨formula_bound φ h.1, formula_bound ψ h.2⟩
  | _, .exs φ, h => formula_bound φ h
  | _, .all (.or (.nrel Language.ORing.Rel.lt v) ψ), h => by
    obtain ⟨-, hp, hψ⟩ : v 0 = #0 ∧ (v 1).Positive ∧ Good ψ := h
    obtain ⟨t, ht⟩ := Rew.positive_iff.mp hp
    refine ⟨?_, formula_bound ψ hψ⟩
    rw [ht, term_bShift]; exact term_bound t

/-! ## Meaning in ℕ -/

lemma term_nat {n : ℕ} (e : Fin n → ℕ) (s : ℕ → ℕ) (hs : ∀ i : Fin n, s i = e i) :
    ∀ t : ATerm n, (term 0 t).natValue s = t.val e Empty.elim
  | .bvar i => by simpa [term, ArithTerm.natValue] using hs i
  | .fvar x => x.elim
  | .func Language.ORing.Func.zero _ => rfl
  | .func Language.ORing.Func.one _ => rfl
  | .func Language.ORing.Func.add v => by
    show (term 0 (v 0)).natValue s + (term 0 (v 1)).natValue s = _
    rw [term_nat e s hs (v 0), term_nat e s hs (v 1)]; rfl
  | .func Language.ORing.Func.mul v => by
    show (term 0 (v 0)).natValue s * (term 0 (v 1)).natValue s = _
    rw [term_nat e s hs (v 0), term_nat e s hs (v 1)]; rfl

lemma push_nat {n : ℕ} {e : Fin n → ℕ} {s : ℕ → ℕ} (hs : ∀ i : Fin n, s i = e i) (x : ℕ) :
    ∀ i : Fin (n + 1), pushValue s x i = (x :> e) i := fun i =>
  Fin.cases rfl (fun j => hs j) i

theorem formula_nat : ∀ {n : ℕ} (φ : AForm n), Good φ → ∀ (e : Fin n → ℕ) (s : ℕ → ℕ),
    (∀ i : Fin n, s i = e i) → ((formula φ).natEval s ↔ Semiformula.Eval e Empty.elim φ)
  | _, .verum, _, _, _, _ => by simp [formula, SigmaFormula.natEval]; exact trivial
  | _, .falsum, _, _, _, _ => by simp [formula, SigmaFormula.natEval]; exact id
  | _, .rel Language.ORing.Rel.eq v, _, e, s, hs => by
    show (term 0 (v 0)).natValue s = (term 0 (v 1)).natValue s ↔
      (v 0).val e Empty.elim = (v 1).val e Empty.elim
    rw [term_nat e s hs, term_nat e s hs]
  | _, .rel Language.ORing.Rel.lt v, _, e, s, hs => by
    show (term 0 (v 0)).natValue s < (term 0 (v 1)).natValue s ↔
      (v 0).val e Empty.elim < (v 1).val e Empty.elim
    rw [term_nat e s hs, term_nat e s hs]
  | _, .nrel Language.ORing.Rel.eq v, _, e, s, hs => by
    show ¬ (term 0 (v 0)).natValue s = (term 0 (v 1)).natValue s ↔
      ¬ (v 0).val e Empty.elim = (v 1).val e Empty.elim
    rw [term_nat e s hs, term_nat e s hs]
  | _, .nrel Language.ORing.Rel.lt v, _, e, s, hs => by
    show ¬ (term 0 (v 0)).natValue s < (term 0 (v 1)).natValue s ↔
      ¬ (v 0).val e Empty.elim < (v 1).val e Empty.elim
    rw [term_nat e s hs, term_nat e s hs]
  | _, .and φ ψ, h, e, s, hs => and_congr (formula_nat φ h.1 e s hs) (formula_nat ψ h.2 e s hs)
  | _, .or φ ψ, h, e, s, hs => or_congr (formula_nat φ h.1 e s hs) (formula_nat ψ h.2 e s hs)
  | _, .exs φ, h, e, s, hs =>
    exists_congr fun x => formula_nat φ h (x :> e) (pushValue s x) (push_nat hs x)
  | _, .all (.or (.nrel Language.ORing.Rel.lt v) ψ), h, e, s, hs => by
    obtain ⟨h0, hp, hψ⟩ : v 0 = #0 ∧ (v 1).Positive ∧ Good ψ := h
    obtain ⟨t, ht⟩ := Rew.positive_iff.mp hp
    have hb : (term 1 (v 1)).natValue s = t.val e Empty.elim := by
      rw [ht, term_bShift, term_nat e s hs]
    show (∀ x, x < (term 1 (v 1)).natValue s → (formula ψ).natEval (pushValue s x)) ↔
      ∀ x : ℕ, ¬ ((v 0).val (x :> e) Empty.elim < (v 1).val (x :> e) Empty.elim) ∨
        Semiformula.Eval (x :> e) Empty.elim ψ
    refine forall_congr' fun x => ?_
    have h1 : (v 1).val (x :> e) Empty.elim = t.val e Empty.elim := by rw [ht]; simp
    have h0' : (v 0).val (x :> e) Empty.elim = x := by rw [h0]; rfl
    rw [hb, h0', h1, formula_nat ψ hψ (x :> e) (pushValue s x) (push_nat hs x)]
    exact imp_iff_not_or

/-! ## Meaning in ZF models -/

section ZF
variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "E" => (fun x y : V => x ∈ y)
local notation "A" => arithmeticTranslation.Model V

lemma val_inj {x y : A} : x.val = y.val ↔ x = y :=
  ⟨fun h => by cases x; cases y; cases h; rfl, fun h => h ▸ rfl⟩

lemma dom_of_mem_omega {x : V} (hx : x ∈ (ω : V)) : arithmeticTranslation.Dom x := by
  simpa [DirectTranslation.Dom, arithmeticTranslation, Semiformula.Operator.val] using hx

lemma term_graph {n : ℕ} (e : Fin n → A) (env : ℕ → V) (henv : ∀ i : Fin n, env i = (e i).val) :
    ∀ (t : ATerm n) (z : V), (term 0 t).graph E env z ↔ z = (t.val e Empty.elim).val
  | .bvar i, z => by
    show PalomarZF207History.NatObject E z ∧ z = env (i.val - 0) ↔ _
    rw [Nat.sub_zero, henv i, PalomarZF207History.natObject_iff]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ model_mem_omega _, h⟩⟩
  | .fvar x, _ => x.elim
  | .func Language.ORing.Func.zero _, z => by
    show PalomarZF207History.Numeral E 0 z ↔ z = (0 : A).val
    rw [PalomarZF207History.numeral_iff, val_zero, cast_zero_def]
  | .func Language.ORing.Func.one _, z => by
    show PalomarZF207History.Numeral E 1 z ↔ z = (1 : A).val
    rw [PalomarZF207History.numeral_iff, val_one, cast_one_def]
  | .func Language.ORing.Func.add v, z => by
    show (∃ a b, (term 0 (v 0)).graph E env a ∧ (term 0 (v 1)).graph E env b ∧ PalomarZF207History.Add E a b z) ↔
      z = ((v 0).val e Empty.elim + (v 1).val e Empty.elim).val
    simp only [term_graph e env henv (v 0), term_graph e env henv (v 1),
      PalomarZF207History.add_iff, val_add]
    exact ⟨fun ⟨_, _, h1, h2, h⟩ => by subst h1 h2; exact h.2.2,
      fun h => ⟨_, _, rfl, rfl, model_mem_omega _, model_mem_omega _, h⟩⟩
  | .func Language.ORing.Func.mul v, z => by
    show (∃ a b, (term 0 (v 0)).graph E env a ∧ (term 0 (v 1)).graph E env b ∧ PalomarZF207History.Mul E a b z) ↔
      z = ((v 0).val e Empty.elim * (v 1).val e Empty.elim).val
    simp only [term_graph e env henv (v 0), term_graph e env henv (v 1),
      PalomarZF207History.mul_iff, val_mul]
    exact ⟨fun ⟨_, _, h1, h2, h⟩ => by subst h1 h2; exact h.2.2,
      fun h => ⟨_, _, rfl, rfl, model_mem_omega _, model_mem_omega _, h⟩⟩

lemma push_zf {n : ℕ} {e : Fin n → A} {env : ℕ → V} (henv : ∀ i : Fin n, env i = (e i).val)
    (x : A) : ∀ i : Fin (n + 1), pushValue env x.val i = ((x :> e) i).val := fun i =>
  Fin.cases rfl (fun j => henv j) i

lemma atom_zf {n : ℕ} (e : Fin n → A) (env : ℕ → V) (henv : ∀ i : Fin n, env i = (e i).val)
    (v : Fin 2 → ATerm n) (eq pos : Bool) :
    (atom v eq pos).internalEval E env ↔
      (let a := ((v 0).val e Empty.elim).val; let b := ((v 1).val e Empty.elim).val
       if pos then (if eq then a = b else a ∈ b) else ¬(if eq then a = b else a ∈ b)) := by
  show (∃ a b, (term 0 (v 0)).graph E env a ∧ (term 0 (v 1)).graph E env b ∧ _) ↔ _
  simp only [term_graph e env henv]
  exact ⟨fun ⟨_, _, h1, h2, h⟩ => by subst h1 h2; exact h, fun h => ⟨_, _, rfl, rfl, h⟩⟩

theorem formula_zf : ∀ {n : ℕ} (φ : AForm n), Good φ → ∀ (e : Fin n → A) (env : ℕ → V),
    (∀ i : Fin n, env i = (e i).val) →
      ((formula φ).internalEval E env ↔ Semiformula.Eval e Empty.elim φ)
  | _, .verum, _, _, _, _ => by
    simp [formula, SigmaFormula.internalEval, ArithTerm.graph, PalomarZF207History.numeral_iff]
    exact trivial
  | _, .falsum, _, _, _, _ => by
    simp [formula, SigmaFormula.internalEval, ArithTerm.graph, PalomarZF207History.numeral_iff]
    exact id
  | _, .rel Language.ORing.Rel.eq v, _, e, env, henv => by
    rw [show formula (.rel Language.ORing.Rel.eq v) = atom v true true from rfl, atom_zf e env henv]
    show ((v 0).val e Empty.elim).val = ((v 1).val e Empty.elim).val ↔
      (v 0).val e Empty.elim = (v 1).val e Empty.elim
    exact val_inj
  | _, .rel Language.ORing.Rel.lt v, _, e, env, henv => by
    rw [show formula (.rel Language.ORing.Rel.lt v) = atom v false true from rfl, atom_zf e env henv]
    show ((v 0).val e Empty.elim).val ∈ ((v 1).val e Empty.elim).val ↔
      (v 0).val e Empty.elim < (v 1).val e Empty.elim
    exact (lt_iff_mem _ _).symm
  | _, .nrel Language.ORing.Rel.eq v, _, e, env, henv => by
    rw [show formula (.nrel Language.ORing.Rel.eq v) = atom v true false from rfl, atom_zf e env henv]
    show ¬ ((v 0).val e Empty.elim).val = ((v 1).val e Empty.elim).val ↔
      ¬ (v 0).val e Empty.elim = (v 1).val e Empty.elim
    exact not_congr val_inj
  | _, .nrel Language.ORing.Rel.lt v, _, e, env, henv => by
    rw [show formula (.nrel Language.ORing.Rel.lt v) = atom v false false from rfl, atom_zf e env henv]
    show ¬ ((v 0).val e Empty.elim).val ∈ ((v 1).val e Empty.elim).val ↔
      ¬ (v 0).val e Empty.elim < (v 1).val e Empty.elim
    exact not_congr (lt_iff_mem _ _).symm
  | _, .and φ ψ, h, e, env, henv =>
    and_congr (formula_zf φ h.1 e env henv) (formula_zf ψ h.2 e env henv)
  | _, .or φ ψ, h, e, env, henv =>
    or_congr (formula_zf φ h.1 e env henv) (formula_zf ψ h.2 e env henv)
  | _, .exs φ, h, e, env, henv => by
    show (∃ x : V, PalomarZF207History.NatObject E x ∧ (formula φ).internalEval E (pushValue env x)) ↔
      ∃ x : A, Semiformula.Eval (x :> e) Empty.elim φ
    constructor
    · rintro ⟨x, hx, hφ⟩
      have hd := dom_of_mem_omega ((PalomarZF207History.natObject_iff x).mp hx)
      exact ⟨⟨x, hd⟩, (formula_zf φ h (⟨x, hd⟩ :> e) _ (push_zf henv ⟨x, hd⟩)).mp hφ⟩
    · rintro ⟨x, hφ⟩
      exact ⟨x.val, (PalomarZF207History.natObject_iff _).mpr (model_mem_omega x),
        (formula_zf φ h (x :> e) _ (push_zf henv x)).mpr hφ⟩
  | _, .all (.or (.nrel Language.ORing.Rel.lt v) ψ), h, e, env, henv => by
    obtain ⟨h0, hp, hψ⟩ : v 0 = #0 ∧ (v 1).Positive ∧ Good ψ := h
    obtain ⟨t, ht⟩ := Rew.positive_iff.mp hp
    have hb : ∀ z, (term 1 (v 1)).graph E env z ↔ z = (t.val e Empty.elim).val := by
      rw [ht, term_bShift]; exact term_graph e env henv t
    have h1 : ∀ x : A, (v 1).val (x :> e) Empty.elim = t.val e Empty.elim := fun x => by
      rw [ht]; simp
    have h0' : ∀ x : A, (v 0).val (x :> e) Empty.elim = x := fun x => by rw [h0]; rfl
    show (∃ bound, (term 1 (v 1)).graph E env bound ∧
        ∀ x : V, PalomarZF207History.NatObject E x → x ∈ bound → (formula ψ).internalEval E (pushValue env x)) ↔
      ∀ x : A, ¬ ((v 0).val (x :> e) Empty.elim < (v 1).val (x :> e) Empty.elim) ∨
        Semiformula.Eval (x :> e) Empty.elim ψ
    simp only [hb, exists_eq_left, h0', h1, lt_iff_mem]
    constructor
    · intro H x
      by_cases hx : x.val ∈ (t.val e Empty.elim).val
      · exact Or.inr ((formula_zf ψ hψ (x :> e) _ (push_zf henv x)).mp
          (H x.val ((PalomarZF207History.natObject_iff _).mpr (model_mem_omega x)) hx))
      · exact Or.inl hx
    · intro H x hx hlt
      have hd := dom_of_mem_omega ((PalomarZF207History.natObject_iff x).mp hx)
      exact (formula_zf ψ hψ (⟨x, hd⟩ :> e) _ (push_zf henv ⟨x, hd⟩)).mpr
        ((H ⟨x, hd⟩).resolve_left (not_not.mpr hlt))

end ZF

/-! ## Σ1 formulas are compiled -/

lemma good_of_lt {n : ℕ} {R : Semiformula.Operator ℒₒᵣ 2} (hR : R ∈ ℬ[<, ℒₒᵣ])
    {t : ATerm (n + 1)} (ht : t.Positive) {φ : AForm (n + 1)} (hφ : Good φ) :
    Good (∀¹[R.operator ![#0, t]] φ) := by
  change R ∈ ({Semiformula.Operator.LT.lt} : Set (Semiformula.Operator ℒₒᵣ 2)) at hR
  rcases Set.mem_singleton_iff.mp hR with rfl
  rw [Semiformula.Operator.lt_def]
  exact ⟨rfl, ht, hφ⟩

lemma good_of_lt_exs {n : ℕ} {R : Semiformula.Operator ℒₒᵣ 2} (hR : R ∈ ℬ[<, ℒₒᵣ])
    {t : ATerm (n + 1)} {φ : AForm (n + 1)} (hφ : Good φ) :
    Good (∃¹[R.operator ![#0, t]] φ) := by
  change R ∈ ({Semiformula.Operator.LT.lt} : Set (Semiformula.Operator ℒₒᵣ 2)) at hR
  rcases Set.mem_singleton_iff.mp hR with rfl
  rw [Semiformula.Operator.lt_def]
  exact ⟨trivial, hφ⟩

lemma good_of_closure {n : ℕ} {φ : AForm n} (h : ℬ[<, ℒₒᵣ].Closure φ) : Good φ := by
  induction h with
  | verum => trivial
  | falsum => trivial
  | rel => trivial
  | nrel => trivial
  | and _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | or _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | ball hR ht _ ih => exact good_of_lt hR ht ih
  | bexs hR _ _ ih => exact good_of_lt_exs hR ih

lemma good_of_hierarchy {Γ : Polarity} {s n : ℕ} {φ : AForm n}
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ s φ) : (Γ = 𝚺 ∧ s ≤ 1) ∨ (Γ = 𝚷 ∧ s = 0) → Good φ := by
  induction h with
  | bounded _ _ _ hc => exact fun _ => good_of_closure hc
  | and _ _ ih₁ ih₂ => exact fun hs => ⟨ih₁ hs, ih₂ hs⟩
  | or _ _ ih₁ ih₂ => exact fun hs => ⟨ih₁ hs, ih₂ hs⟩
  | ball hR ht _ ih => exact fun hs => good_of_lt hR ht (ih hs)
  | bexs hR _ _ ih => exact fun hs => good_of_lt_exs hR (ih hs)
  | exs _ ih => exact fun hs => ih (by rcases hs with ⟨-, hs⟩ | ⟨h, -⟩ <;> simp_all)
  | all _ _ => exact fun hs => by rcases hs with ⟨h, -⟩ | ⟨-, h⟩ <;> simp_all
  | sigma _ ih => exact fun hs => ih (by rcases hs with ⟨-, hs⟩ | ⟨h, -⟩ <;> simp_all)
  | pi _ _ => exact fun hs => by rcases hs with ⟨h, -⟩ | ⟨-, h⟩ <;> simp_all
  | dummy_sigma _ _ => exact fun hs => by rcases hs with ⟨-, h⟩ | ⟨h, -⟩ <;> simp_all
  | dummy_pi _ _ => exact fun hs => by rcases hs with ⟨h, -⟩ | ⟨-, h⟩ <;> simp_all

/-! ## The bridge -/

/-- The compiled sentence represents the sentence read in ω, in every ZF model. -/
lemma represents (σ : AForm 0) (hσ : Good σ) :
    RepresentsArithmetic (formula σ) (ofFoundationSentence (arithmeticTranslation.translate σ)) := by
  refine ⟨ofFoundationSentence_closed _, ?_⟩
  intro V E hn hm s env _
  let _ : Nonempty V := hn
  let _ : SetStructure V := ⟨fun y x => E x y⟩
  have _ : V↓[Language.set] ⊧* 𝗭𝗙 := challenge_model_to_foundation hm
  have ht := DirectTranslation.Model.translate_iff (π := arithmeticTranslation) (M := V) (σ := σ)
  rw [interpreted_structure_eq_standard (V := V)] at ht
  have hz := formula_zf (V := V) σ hσ ![] env (fun i => i.elim0)
  calc eval E (ofFoundationSentence (arithmeticTranslation.translate σ)) s
      ↔ V↓[Language.set] ⊧ arithmeticTranslation.translate σ := ofFoundationSentence_eval _ s
    _ ↔ σ.Evalb (![] : Fin 0 → arithmeticTranslation.Model V) := by
        simpa only [models_iff] using ht
    _ ↔ (formula σ).internalEval E env := hz.symm

/-- The Challenge's Σ1 soundness gives Σ1 soundness of Foundation's ZF in ω
(`ArithmeticSigma1SoundZF`, stated here in full). -/
theorem standalone_sound_implies_production (hs : PalomarZF207.ArithmeticSigma1Sound) :
    ∀ σ : 𝚺ᴬ₁.Semisentence 0,
      (𝗭𝗙 : SetTheory) ⊢ arithmeticTranslation.translate σ.val → σ.val.Evalb (![] : Fin 0 → ℕ) := by
  intro σ hσ
  have hg : Good σ.val := good_of_hierarchy σ.sigma_prop (Or.inl ⟨rfl, le_rfl⟩)
  have hn := hs (formula σ.val) (formula_bound σ.val hg) _ (represents σ.val hg)
    ((provable_ofFoundationSentence_iff _).mpr hσ) (fun _ => 0)
  exact (formula_nat σ.val hg ![] (fun _ => 0) (fun i => i.elim0)).mp hn

end ZF207.Independence.SigmaBridge
