module
public import I0451.Standalone.SigmaBridge

/-! Every bounded standalone arithmetic formula has a Σ₁ counterpart
in Foundation's language. The two syntax translations are inverse on
these formulas, so the standalone soundness assumption has its usual
extent. -/
@[expose] public section
namespace I0451.Standalone.SigmaBridge

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def reflectTerm (n : Nat) : (t : ArithTerm) → t.bound n → ATerm n
  | .zero, _ => .func Language.ORing.Func.zero ![]
  | .one, _ => .func Language.ORing.Func.one ![]
  | .var i, hi => .bvar ⟨i,hi⟩
  | .add a b, h => .func Language.ORing.Func.add ![reflectTerm n a h.1,reflectTerm n b h.2]
  | .mul a b, h => .func Language.ORing.Func.mul ![reflectTerm n a h.1,reflectTerm n b h.2]

theorem reflectTerm_plain {n : Nat} (t : ArithTerm) (within : t.bound n) :
    term 0 (reflectTerm n t within) = t := by
  induction t with
  | zero | one | var => simp [reflectTerm,term]
  | add a b ha hb => simp [reflectTerm,term,ha within.1,hb within.2]
  | mul a b ha hb => simp [reflectTerm,term,ha within.1,hb within.2]

theorem reflectTerm_pushed {n : Nat} (t : ArithTerm) (within : t.bound n) :
    term 1 (Rew.bShift (reflectTerm n t within)) = t := by
  induction t with
  | zero | one | var => simp [reflectTerm,term,Rew.func]
  | add a b ha hb => simp [reflectTerm,term,Rew.func,ha within.1,hb within.2]
  | mul a b ha hb => simp [reflectTerm,term,Rew.func,ha within.1,hb within.2]

structure Reflection (p : SigmaFormula) (n : Nat) where
  expression : 𝚺ᴬ₁.Semisentence n
  sameSyntax : formula expression.val = p

def reflect : (n : Nat) → (p : SigmaFormula) → p.bound n → Reflection p n
  | n, .atom a b eq pos, within => by
    let w : Fin 2 → ATerm n := ![reflectTerm n a within.1, reflectTerm n b within.2]
    cases eq <;> cases pos
    · exact ⟨.mkSigma (.nrel Language.ORing.Rel.lt w) (by simp),
        by simp [formula,atom,w,reflectTerm_plain]⟩
    · exact ⟨.mkSigma (.rel Language.ORing.Rel.lt w) (by simp),
        by simp [formula,atom,w,reflectTerm_plain]⟩
    · exact ⟨.mkSigma (.nrel Language.ORing.Rel.eq w) (by simp),
        by simp [formula,atom,w,reflectTerm_plain]⟩
    · exact ⟨.mkSigma (.rel Language.ORing.Rel.eq w) (by simp),
        by simp [formula,atom,w,reflectTerm_plain]⟩
  | n, .conj p q, within => by
    let a := reflect n p within.1
    let b := reflect n q within.2
    exact ⟨.mkSigma (a.expression.val ⋏ b.expression.val) (.and a.expression.sigma_prop b.expression.sigma_prop),
      by simp only [Bounding.HierarchySymbol.Semiformula.val_mkSigma,formula,a.sameSyntax,b.sameSyntax]⟩
  | n, .disj p q, within => by
    let a := reflect n p within.1
    let b := reflect n q within.2
    exact ⟨.mkSigma (a.expression.val ⋎ b.expression.val) (.or a.expression.sigma_prop b.expression.sigma_prop),
      by simp only [Bounding.HierarchySymbol.Semiformula.val_mkSigma,formula,a.sameSyntax,b.sameSyntax]⟩
  | n, .exists_ p, within => by
    let a := reflect (n+1) p within
    exact ⟨.mkSigma (∃¹ a.expression.val) (.exs a.expression.sigma_prop),
      by simp only [Bounding.HierarchySymbol.Semiformula.val_mkSigma,formula,a.sameSyntax]⟩
  | n, .forallLt t p, within => by
    let bound := reflectTerm n t within.1
    let a := reflect (n+1) p within.2
    have h : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 (Semiformula.ballLT bound a.expression.val) :=
      .ball (Set.mem_singleton _) (Rew.bShift_positive bound) a.expression.sigma_prop
    refine ⟨.mkSigma _ h, ?_⟩
    change SigmaFormula.forallLt (term 1 (Rew.bShift bound)) (formula a.expression.val) = _
    rw [reflectTerm_pushed, a.sameSyntax]

end I0451.Standalone.SigmaBridge
