module
public import I3_334Support.Logic.Target
public import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy
@[expose] public section

namespace PalomarI3380.Logic

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def ofFoundationTerm {n : Nat} : ArithmeticSemiterm Empty n → ArithTerm
  | .bvar i => .var i.val
  | .fvar i => i.elim
  | .func .zero _ => .zero
  | .func .one _ => .one
  | .func .add v => .add (ofFoundationTerm (v 0)) (ofFoundationTerm (v 1))
  | .func .mul v => .mul (ofFoundationTerm (v 0)) (ofFoundationTerm (v 1))

theorem ofFoundationTerm_bound {n : Nat} (t : ArithmeticSemiterm Empty n) :
    (ofFoundationTerm t).bound n := by
  induction t with
  | bvar i => exact i.isLt
  | fvar i => exact i.elim
  | func op v ih =>
    cases op
    · trivial
    · trivial
    · exact ⟨ih 0,ih 1⟩
    · exact ⟨ih 0,ih 1⟩

theorem ofFoundationTerm_eval {n : Nat} (t : ArithmeticSemiterm Empty n)
    {M : Type} [ORingStructure M] (env : Nat → M) :
    Semiterm.valb (fun i => env i.val) t = (ofFoundationTerm t).value env := by
  induction t with
  | bvar i => rfl
  | fvar i => exact i.elim
  | func op v ih =>
    cases op
    · rfl
    · rfl
    · exact congrArg₂ (· + ·) (ih 0) (ih 1)
    · exact congrArg₂ (· * ·) (ih 0) (ih 1)

private def SigmaRepresentation (n : Nat) (φ : ArithmeticSemisentence n) : Prop :=
  ∃ p : SigmaFormula, p.bound n ∧ ∀ (M : Type) [ORingStructure M] (env : Nat → M),
    φ.Evalb (fun i => env i.val) ↔ p.value env

private theorem representsAtomic {n : Nat} (a b : ArithmeticSemiterm Empty n) (eq pos : Bool) :
    SigmaRepresentation n
      (if eq then if pos then .rel Language.ORing.Rel.eq ![a,b] else .nrel Language.ORing.Rel.eq ![a,b]
       else if pos then .rel Language.ORing.Rel.lt ![a,b] else .nrel Language.ORing.Rel.lt ![a,b]) := by
  refine ⟨.atom (ofFoundationTerm a) (ofFoundationTerm b) eq pos,
    ⟨ofFoundationTerm_bound a,ofFoundationTerm_bound b⟩,fun M _ env => ?_⟩
  have ha := ofFoundationTerm_eval a env
  have hb := ofFoundationTerm_eval b env
  cases eq <;> cases pos
  · change (¬Semiterm.valb (fun i => env i.val) a < Semiterm.valb (fun i => env i.val) b) ↔ _
    rw [ha,hb]
    exact Iff.rfl
  · change (Semiterm.valb (fun i => env i.val) a < Semiterm.valb (fun i => env i.val) b) ↔ _
    rw [ha,hb]
    exact Iff.rfl
  · change (Semiterm.valb (fun i => env i.val) a ≠ Semiterm.valb (fun i => env i.val) b) ↔ _
    rw [ha,hb]
    exact Iff.rfl
  · change (Semiterm.valb (fun i => env i.val) a = Semiterm.valb (fun i => env i.val) b) ↔ _
    rw [ha,hb]
    exact Iff.rfl

theorem sigma_representable {n : Nat} (φ : ArithmeticSemisentence n)
    (h : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ) :
    ∃ p : SigmaFormula, p.bound n ∧ ∀ (M : Type) [ORingStructure M] (env : Nat → M),
      φ.Evalb (fun i => env i.val) ↔ p.value env := by
  change SigmaRepresentation n φ
  apply Bounding.Hierarchy.arithmetic_sigma₁_induction' h (P := SigmaRepresentation)
  case hVerum =>
    intro m
    exact ⟨.atom .zero .zero true true,⟨trivial,trivial⟩,fun _ _ _ =>
      ⟨fun _ => rfl,fun _ => trivial⟩⟩
  case hFalsum =>
    intro m
    exact ⟨.atom .zero .zero true false,⟨trivial,trivial⟩,fun _ _ _ =>
      ⟨False.elim,fun h => h rfl⟩⟩
  case hEQ =>
    intro n a b
    exact representsAtomic a b true true
  case hNEQ =>
    intro n a b
    exact representsAtomic a b true false
  case hLT =>
    intro n a b
    exact representsAtomic a b false true
  case hNLT =>
    intro n a b
    exact representsAtomic a b false false
  case hAnd =>
    intro n p q _ _ ip iq

    obtain ⟨a,ha,ea⟩ := ip
    obtain ⟨b,hb,eb⟩ := iq
    exact ⟨.conj a b,⟨ha,hb⟩,fun M _ env => and_congr (ea M env) (eb M env)⟩
  case hOr =>
    intro n p q _ _ ip iq

    obtain ⟨a,ha,ea⟩ := ip
    obtain ⟨b,hb,eb⟩ := iq
    exact ⟨.disj a b,⟨ha,hb⟩,fun M _ env => or_congr (ea M env) (eb M env)⟩
  case hBall =>
    intro n t p _ ih

    obtain ⟨a,ha,meaning⟩ := ih
    refine ⟨.forallLt (ofFoundationTerm t) a,⟨ofFoundationTerm_bound t,ha⟩,fun M _ env => ?_⟩
    have extend (x : M) :
        (fun i : Fin (n+1) => pushValue env x i.val) = x :> (fun i : Fin n => env i.val) :=
      funext fun i => Fin.cases rfl (fun _ => rfl) i
    have valu := ofFoundationTerm_eval t env
    change (Semiformula.ballLT t p).Evalb (fun i => env i.val) ↔ _
    rw [Semiformula.eval_ballLT]
    change (∀ x < Semiterm.valb (fun i => env i.val) t, p.Evalb (x :> fun i => env i.val)) ↔ _
    rw [valu]
    exact forall_congr' fun x => imp_congr_right fun _ => by rw [← extend]; exact meaning M _
  case hExs =>
    intro n p _ ih

    obtain ⟨a,ha,meaning⟩ := ih
    refine ⟨.exists_ a,ha,fun M _ env => ?_⟩
    have extend (x : M) :
        (fun i : Fin (n+1) => pushValue env x i.val) = x :> (fun i : Fin n => env i.val) :=
      funext fun i => Fin.cases rfl (fun _ => rfl) i
    rw [Semiformula.eval_ex]
    exact exists_congr fun x => by rw [← extend]; exact meaning M _

end PalomarI3380.Logic
