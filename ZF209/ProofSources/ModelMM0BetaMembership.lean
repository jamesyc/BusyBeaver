module
public import ModelApplicationCertificates
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelPeano

/-- Literal t109 membership after exposing the two decoded components b,c.
This is divisibility-based finite graph coding, not ordinary beta remainders. -/
def mm0BetaMembershipFormula : ArithmeticSemiformula Nat 3 :=
 “k b c. (0 < b ∧ 0 < c) ∧
   ((∀ j, (0 < j ∧ j ≤ k) → ∃ q, q*j = b) ∧
    ∃ q, q*(1+b*(k+1)) = c)”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def mm0BetaMembership (b c k : M) : Prop :=
 (0<b ∧ 0<c) ∧ ((∀ j, (0<j ∧ j≤k) → ∃q,q*j=b) ∧
 ∃q,q*(1+b*(k+1))=c)

lemma mm0BetaMembership_eval (e : Nat → M) (k b c : M) :
 mm0BetaMembershipFormula.Eval ![k,b,c] e ↔ mm0BetaMembership b c k := by
 simp [mm0BetaMembershipFormula,mm0BetaMembership]

end ZF209.MM0ModelPeano
