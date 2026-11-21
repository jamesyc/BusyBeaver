module
public import I0451.Logic.Formula
public import Foundation.FirstOrder.SetTheory.ZF.ZF

/-! Interpret the machine's named syntax in Foundation's first-order
membership language. The environment is explicit at every binder. -/
@[expose] public section
namespace I0451.Logic.SetSyntax

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

def bindTerms {ξ : Type} {n : Nat} (terms : Nat → Semiterm ℒₛₑₜ ξ n) (label : Nat) :
    Nat → Semiterm ℒₛₑₜ ξ (n + 1) :=
  fun i => if i = label then .bvar 0 else Rew.bShift (terms i)

def translate {ξ : Type} {n : Nat} (terms : Nat → Semiterm ℒₛₑₜ ξ n) :
    Logic.Formula → Semiformula ℒₛₑₜ ξ n
  | .truth => .verum
  | .mem a b => “!!(terms a) ∈ !!(terms b)”
  | .equal a b => “!!(terms a) = !!(terms b)”
  | .imp a b => “!!(translate terms a) → !!(translate terms b)”
  | .all label f => .all (translate (bindTerms terms label) f)

section
variable {V : Type} [Tarski.Structure ℒₛₑₜ V]

theorem bindTerms_values {ξ : Type} {n : Nat} (terms : Nat → Semiterm ℒₛₑₜ ξ n) (label : Nat)
    (bound : Fin n → V) (free : ξ → V) (v : V) :
    (fun i => (bindTerms terms label i).val (v :> bound) free) =
      assign (fun i => (terms i).val bound free) label v := by
  funext i
  by_cases same : i = label
  · simp [bindTerms, assign, same]
  · simp [bindTerms, assign, same]

end

variable {V : Type} [SetStructure V]

theorem translate_eval {ξ : Type} {n : Nat} (terms : Nat → Semiterm ℒₛₑₜ ξ n)
    (bound : Fin n → V) (free : ξ → V) (f : Logic.Formula) :
    (translate terms f).Eval bound free ↔
      f.eval (fun x y : V => x ∈ y) (fun i => (terms i).val bound free) := by
  induction f generalizing n with
  | truth => rfl
  | mem a b => simp [translate, Logic.Formula.eval]
  | equal a b => simp [translate, Logic.Formula.eval]
  | imp a b ia ib => simp [translate, Logic.Formula.eval, ia, ib]
  | all label f ih =>
    simp only [translate, Logic.Formula.eval]
    exact forall_congr' fun v => by
      change (translate (bindTerms terms label) f).Eval (v :> bound) free ↔ _
      rw [ih, bindTerms_values]

def relationWith (a b : Nat) (values : Nat → V) (code : Nat) : SetTheorySemiformula V 2 :=
  translate (fun i => if i = b then .bvar 1 else if i = a then .bvar 0 else .fvar (values i))
    (Logic.Formula.decode code)

theorem relationWith_eval (a b : Nat) (s : Nat → V) (code : Nat) (x y : V) :
    (relationWith a b s code).Eval ![x, y] id ↔
      Logic.Eval (fun u v : V => u ∈ v) (assign (assign s a x) b y) code := by
  unfold relationWith Logic.Eval
  rw [translate_eval]
  have same : (fun i => (if i = b then (Semiterm.bvar 1 : Semiterm ℒₛₑₜ V 2)
      else if i = a then .bvar 0 else .fvar (s i)).val ![x, y] id) =
      assign (assign s a x) b y := by
    funext i
    by_cases ib : i = b
    · simp [assign, ib]
    · by_cases ia : i = a
      · subst i
        simp [assign, ib]
      · simp [assign, ib, ia]
  rw [same]

theorem definable_code_relation (a b code : Nat) (s : Nat → V) :
    ℒₛₑₜ-relation (fun (x y : V) =>
      Logic.Eval (fun u v : V => u ∈ v) (assign (assign s a x) b y) code) := by
  refine ⟨relationWith a b s code, fun v => ?_⟩
  simpa only [← Matrix.fun_eq_vec_two v] using relationWith_eval a b s code (v 0) (v 1)

end I0451.Logic.SetSyntax
