module
public import SourceSyntax
public import NumericCoding
@[expose] public section
namespace ZFR

/-- Mapping a named variable into a context extended by its nearest binder. -/
def bindName (i : Nat) (ρ : Nat → Nat) : Nat → Nat :=
  fun j => if j = i then 0 else ρ j + 1

/-- Exact named-formula to de Bruijn source translation. Truth is Bot→Bot. -/
def translate (ρ : Nat → Nat) : C209Soundness.Formula → Formula
  | .truth => .imp .bot .bot
  | .mem i j => .mem (ρ i) (ρ j)
  | .eq i j => .eq (ρ i) (ρ j)
  | .imp p q => .imp (translate ρ p) (translate ρ q)
  | .all i p => .all (translate (bindName i ρ) p)

theorem lift_bindName (σ ρ : Nat → Nat) (i : Nat) :
    (fun j => lift σ (bindName i ρ j)) = bindName i (fun j => σ (ρ j)) := by
  funext j
  by_cases h : j = i <;> simp [bindName, h, lift]

/-- Free renaming commutes with translation even through repeated named binders. -/
theorem rename_translate (p : C209Soundness.Formula) (σ ρ : Nat → Nat) :
    rename σ (translate ρ p) = translate (fun j => σ (ρ j)) p := by
  induction p generalizing σ ρ with
  | truth => rfl
  | mem i j => rfl
  | eq i j => rfl
  | imp p q ihp ihq => simp [translate, rename, ihp, ihq]
  | all i p ih =>
      simp only [translate, rename]
      rw [ih, lift_bindName]

/-- Renaming used for a C generalization at label i. It sends i to the new
    eigenvariable and shifts all other free indices. -/
def generalizeMap (i : Nat) : Nat → Nat := bindName i id

theorem generalize_translation (i : Nat) (p : C209Soundness.Formula) :
    rename (generalizeMap i) (translate id p) = translate (bindName i id) p := by
  simpa [generalizeMap] using rename_translate p (bindName i id) id

universe u
/-- Interpretation of a de Bruijn assignment after pushing an eigenvariable. -/
def pushValue {α : Type u} (s : Nat → α) (x : α) : Nat → α
  | 0 => x
  | n + 1 => s n

def eval {α : Type u} (mem : α → α → Prop) : Formula → (Nat → α) → Prop
  | .bot, _ => False
  | .mem i j, s => mem (s i) (s j)
  | .eq i j, s => s i = s j
  | .and p q, s => eval mem p s ∧ eval mem q s
  | .or p q, s => eval mem p s ∨ eval mem q s
  | .imp p q, s => eval mem p s → eval mem q s
  | .all p, s => ∀ x, eval mem p (pushValue s x)
  | .ex p, s => ∃ x, eval mem p (pushValue s x)

theorem pushed_binding {α : Type u} (s : Nat → α) (ρ : Nat → Nat)
    (i : Nat) (x : α) :
    (fun j => pushValue s x (bindName i ρ j)) =
      C209Soundness.update (fun j => s (ρ j)) i x := by
  funext j
  by_cases h : j = i <;> simp [pushValue, bindName, C209Soundness.update, h]

/-- Semantic preservation for the precise translation, including arbitrary
    repeated/shadowing binders. No injectivity or freshness assumption on ρ. -/
theorem eval_translate {α : Type u} (mem : α → α → Prop)
    (p : C209Soundness.Formula) (ρ : Nat → Nat) (s : Nat → α) :
    eval mem (translate ρ p) s ↔ p.eval mem (fun j => s (ρ j)) := by
  induction p generalizing ρ s with
  | truth => simp [translate, eval, C209Soundness.Formula.eval]
  | mem i j => rfl
  | eq i j => rfl
  | imp p q ihp ihq =>
      simp only [translate, eval, C209Soundness.Formula.eval, ihp, ihq]
  | all i p ih =>
      simp only [translate, eval, C209Soundness.Formula.eval]
      constructor
      · intro h x
        have hx := (ih (bindName i ρ) (pushValue s x)).mp (h x)
        rwa [pushed_binding] at hx
      · intro h x
        apply (ih (bindName i ρ) (pushValue s x)).mpr
        rw [pushed_binding]
        exact h x

end ZFR
