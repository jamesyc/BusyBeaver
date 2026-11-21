module
public import I3_380.Arithmetic.OmegaDomain
public import I3_380.Logic.Target
@[expose] public section

namespace PalomarI3380.Logic.Expanded.OmegaDomain

open SquareRepresentation

variable {V : Type} {E G : V → V → Prop}
variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

local notation "K" => (L.context inhabited)

theorem term_graph (t : Logic.ArithTerm) (env : Nat → D.Points) (out : V) :
    t.graph E (fun i => (env i).val) out ↔ out = (t.value env).val := by
  induction t generalizing out with
  | zero => exact (K).numeral_def 0 _
  | one => exact (K).numeral_def 1 _
  | var i =>
    refine ⟨And.right,fun h => ⟨?_,h⟩⟩
    exact (h.symm ▸ ⟨D.omega,D.specification,(env i).property⟩)
  | add a b ia ib =>
    simp only [ArithTerm.graph,ArithTerm.value,ia,ib,exists_eq_left,exists_and_left]
    exact D.add_result _ _ _
  | mul a b ia ib =>
    simp only [ArithTerm.graph,ArithTerm.value,ia,ib,exists_eq_left,exists_and_left]
    exact D.mul_result _ _ _

theorem sigma_eval (p : Logic.SigmaFormula) (env : Nat → D.Points) :
    p.internalEval E (fun i => (env i).val) ↔ p.value env := by
  have shifted (x : D.Points) (env : Nat → D.Points) :
      pushValue (fun i => (env i).val) x.val = (fun i => (pushValue env x i).val) := by
    funext i
    cases i <;> rfl
  induction p generalizing env with
  | atom a b eq pos =>
    simp only [SigmaFormula.internalEval,SigmaFormula.value,D.term_graph,exists_eq_left,exists_and_left]
    cases eq <;> cases pos
    · exact Iff.rfl
    · exact Iff.rfl
    · exact not_congr Subtype.ext_iff.symm
    · exact Subtype.ext_iff.symm
  | conj a b ia ib => exact and_congr (ia env) (ib env)
  | disj a b ia ib => exact or_congr (ia env) (ib env)
  | exists_ p ih =>
    constructor
    · rintro ⟨x,hn,h⟩
      let x' : D.Points := ⟨x,((K).natObject_iff D.specification _).mp hn⟩
      refine ⟨x',(ih (pushValue env x')).mp ?_⟩
      rwa [← shifted]
    · rintro ⟨x,h⟩
      refine ⟨x.val,⟨D.omega,D.specification,x.property⟩,?_⟩
      rw [shifted]
      exact (ih _).mpr h
  | forallLt b p ih =>
    simp only [SigmaFormula.internalEval,D.term_graph,exists_eq_left,SigmaFormula.value]
    constructor
    · intro h x below
      have hits := h x.val ⟨D.omega,D.specification,x.property⟩ below
      rw [shifted] at hits
      exact (ih _).mp hits
    · intro h x hx below
      let x' : D.Points := ⟨x,((K).natObject_iff D.specification _).mp hx⟩
      change p.internalEval E (pushValue (fun i => (env i).val) x'.val)
      rw [shifted]
      exact (ih _).mpr (h x' below)

end PalomarI3380.Logic.Expanded.OmegaDomain
