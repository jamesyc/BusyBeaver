module
public import ModelLiteralHistoryStepCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def substituteZeroParameter (φ : ArithmeticSemiformula Nat 2) : ArithmeticSemiformula Nat 2 :=
 Rew.bind (L:=ℒₒᵣ) Semiterm.bvar (fun i=>Nat.casesOn i (Semiterm.func (L:=ℒₒᵣ) Language.Zero.zero ![]) Semiterm.fvar) ▹ φ
lemma substituteZeroParameter_eval (φ : ArithmeticSemiformula Nat 2) (e : Nat → M) (v : Fin 2 → M) :
 (substituteZeroParameter φ).Eval v e ↔ φ.Eval v (fun i=>Nat.casesOn i 0 e) := by
 rw [substituteZeroParameter,Semiformula.eval_rew]
 have hb : (fun i=>Semiterm.val v e (Semiterm.bvar i : ArithmeticSemiterm Nat 2))=v := rfl
 have he : (fun i=>Semiterm.val v e (Nat.casesOn i (Semiterm.func (L:=ℒₒᵣ) Language.Zero.zero ![]) Semiterm.fvar : ArithmeticSemiterm Nat 2))=(fun i=>Nat.casesOn i (0:M) e) := by
  funext i; cases i <;> simp
 change φ.Eval (fun i=>Semiterm.val v e (Semiterm.bvar i)) (fun i=>Semiterm.val v e (Nat.casesOn i (Semiterm.func (L:=ℒₒᵣ) Language.Zero.zero ![]) Semiterm.fvar)) ↔ _
 rw [hb,he]
noncomputable def literalHistory_certificate {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FunctionGraphCertificate e 1 (fun v=>t137 A (v 0)) := by
 let aa := a.prependParameter (0:M)
 let step := literalHistoryStep_certificate aa
 let rr := literalRecn_certificate step
 refine ⟨substituteZeroParameter rr.formula,?_⟩
 intro v y
 rw [substituteZeroParameter_eval]
 exact rr.correct v y
end ZF209.MM0ModelReplay
