module
public import I3_334Support.SetTheory.Forcing.Conservativity
@[expose] public section

namespace PalomarI3380

abbrev ClosedTerm := Term Empty

/-- Equational deduction on closed terms. Congruence can replace an argument
within any operation, with the other arguments held fixed by reflexivity. -/
inductive Derives (equations : List Equation) : ClosedTerm → ClosedTerm → Prop where
  | instanceOf {e : Equation} : e ∈ equations → (σ : Fin 3 → ClosedTerm) →
      Derives equations (e.1.subst σ) (e.2.subst σ)
  | refl (a) : Derives equations a a
  | symm : Derives equations a b → Derives equations b a
  | trans : Derives equations a b → Derives equations b c → Derives equations a c
  | neg : Derives equations a b → Derives equations (.neg a) (.neg b)
  | converse : Derives equations a b → Derives equations (.converse a) (.converse b)
  | choice : Derives equations a b → Derives equations (.choice a) (.choice b)
  | localRel : Derives equations a b → Derives equations (.localRel a) (.localRel b)
  | nand : Derives equations a b → Derives equations c d → Derives equations (.nand a c) (.nand b d)
  | product : Derives equations a b → Derives equations c d →
      Derives equations (.product a c) (.product b d)
  | node : Derives equations a b → Derives equations c d → Derives equations e f →
      Derives equations (.node a c e) (.node b d f)

namespace Derives

def setoid (equations : List Equation) : Setoid ClosedTerm where
  r := Derives equations
  iseqv := ⟨.refl, .symm, .trans⟩

abbrev Classes (equations : List Equation) := Quotient (setoid equations)

abbrev classOf (equations : List Equation) (a : ClosedTerm) : Classes equations :=
  Quotient.mk (setoid equations) a

noncomputable def representative {equations : List Equation} (x : Classes equations) : ClosedTerm :=
  Classical.choose (Quotient.exists_rep x)

theorem classOf_representative {equations : List Equation} (x : Classes equations) :
    classOf equations (representative x) = x :=
  Classical.choose_spec (Quotient.exists_rep x)

theorem representative_derives {equations : List Equation} (a : ClosedTerm) :
    Derives equations (representative (classOf equations a)) a :=
  Quotient.exact (classOf_representative (classOf equations a))

noncomputable def termAlgebra (equations : List Equation) : Algebra (Classes equations) where
  constant c := classOf equations (.const c)
  neg a := classOf equations (.neg (representative a))
  converse a := classOf equations (.converse (representative a))
  choice a := classOf equations (.choice (representative a))
  localRel a := classOf equations (.localRel (representative a))
  nand a b := classOf equations (.nand (representative a) (representative b))
  product a b := classOf equations (.product (representative a) (representative b))
  node a b c := classOf equations (.node (representative a) (representative b) (representative c))

theorem eval_termAlgebra {V : Type} (equations : List Equation) (σ : V → ClosedTerm) (t : Term V) :
    (termAlgebra equations).eval (fun x => classOf equations (σ x)) t =
      classOf equations (t.subst σ) := by
  induction t <;> simp only [Algebra.eval, Term.subst, *] <;> try rfl
  all_goals apply Quotient.sound
  · exact .neg (representative_derives _)
  · exact .converse (representative_derives _)
  · exact .choice (representative_derives _)
  · exact .localRel (representative_derives _)
  · exact .nand (representative_derives _) (representative_derives _)
  · exact .product (representative_derives _) (representative_derives _)
  · exact .node (representative_derives _) (representative_derives _) (representative_derives _)

theorem models_termAlgebra (equations : List Equation) :
    (termAlgebra equations).Models equations := by
  intro e he v
  change (termAlgebra equations).eval v e.1 = (termAlgebra equations).eval v e.2
  have hv : (fun x => classOf equations (representative (v x))) = v :=
    funext (fun x => classOf_representative (v x))
  rw [← hv, eval_termAlgebra, eval_termAlgebra]
  exact Quotient.sound (.instanceOf he _)

theorem sound {A : Type} {equations : List Equation} {a b : ClosedTerm}
    (M : Algebra A) (hM : M.Models equations) (h : Derives equations a b) :
    M.eval Empty.elim a = M.eval Empty.elim b := by
  induction h with
  | instanceOf he σ => simpa only [Algebra.eval_subst] using hM _ he (fun i => M.eval Empty.elim (σ i))
  | refl => rfl
  | symm _ h => exact h.symm
  | trans _ _ h₁ h₂ => exact h₁.trans h₂
  | neg _ h | converse _ h | choice _ h | localRel _ h => simp only [Algebra.eval, h]
  | nand _ _ h₁ h₂ | product _ _ h₁ h₂ => simp only [Algebra.eval, h₁, h₂]
  | node _ _ _ h₁ h₂ h₃ => simp only [Algebra.eval, h₁, h₂, h₃]

/-- The term algebra witnesses failure of a closed equation whenever there
is no ground equational deduction of it. -/
theorem complete {equations : List Equation} {a b : ClosedTerm}
    (valid : ∀ (A : Type) (M : Algebra A), M.Models equations →
      M.eval Empty.elim a = M.eval Empty.elim b) :
    Derives equations a b := by
  have h := valid _ (termAlgebra equations) (models_termAlgebra equations)
  have identity (t : ClosedTerm) : t.subst (fun x => x.elim) = t := by
    induction t <;> simp only [Term.subst, *]
    case var x => exact x.elim
  have hEval (t : ClosedTerm) : (termAlgebra equations).eval Empty.elim t = classOf equations t := by
    have hv : (fun x : Empty => classOf equations (x.elim : ClosedTerm)) =
        (Empty.elim : Empty → Classes equations) := funext (fun x => x.elim)
    simpa only [hv, identity] using eval_termAlgebra equations (fun x : Empty => x.elim) t
  rw [hEval, hEval] at h
  exact Quotient.exact h

/-- Eliminating the closed definitions of `T` and `S` preserves and reflects
ground provability of the unchanged acceptance equation. -/
theorem acceptance_iff :
    Derives Manifest.final (.const .D) (.const .J) ↔
      Derives Manifest.preceding (.const .D) (.const .J) := by
  constructor
  · intro h
    apply complete
    intro A M hM
    exact sound M (M.models_final_of_preceding hM) h
  · intro h
    apply complete
    intro A M hM
    exact sound M.withStages (M.models_final_iff.mp hM) h

end Derives
end PalomarI3380
