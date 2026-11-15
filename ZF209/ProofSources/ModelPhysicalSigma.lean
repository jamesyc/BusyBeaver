module
public import ModelPhysicalTerminal
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation
lemma moveFormula_sigma (b w d:Bool) (n:Nat) :
 ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 (moveFormula b w d n) := by
 cases d <;> simp [moveFormula]
lemma siteFormula_sigma (q:Nat) (b:Bool) (r:M6.Reference230.Row) :
 ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 (siteFormula q b r) := by
 cases r with
 | none => simp [siteFormula]
 | some r => rcases r with ⟨w,d,n⟩; simp [siteFormula,moveFormula_sigma]
lemma tableFormula_sigma (tm:M6.Zip.TMN) (sites:List Nat) :
 ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 (tableFormula tm sites) := by
 induction sites with
 | nil => simp [tableFormula]
 | cons q sites ih =>
  change ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 (siteFormula q false (tm q false) ⋎ siteFormula q true (tm q true) ⋎ tableFormula tm sites)
  simp [siteFormula_sigma,ih]
lemma literalStepFormula_sigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 literalStepFormula :=
 tableFormula_sigma _ _
lemma stateGraph_sigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 stateGraph := by
 simp [stateGraph]
lemma physicalStepFormula_sigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 physicalStepFormula := by
 simp [physicalStepFormula,stateGraph_sigma,literalStepFormula_sigma]
lemma physicalRunFormula_sigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 physicalRunFormula := by
 simp [physicalRunFormula,physicalStepFormula_sigma]
def terminalFormula : ArithmeticSemisentence 1 :=
 Matrix.conj (fun q:Fin 209 => (“#0 ≠ ↑q.val”:ArithmeticSemisentence 1))
lemma terminalFormula_sigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 terminalFormula := by
 simp [terminalFormula]
lemma terminalFormula_eval {M:Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (q:M) :
 terminalFormula.Evalb ![q] ↔ ∀i:Fin 209,q≠(i.val:M) := by
 simp [terminalFormula,numeral_eq_natCast]
def physicalHaltSigma : 𝚺ᴬ₁.Semisentence 0 := .mkSigma
 “∃initial, ∃hist, ∃last, ∃q, ∃l, ∃r,
 !stateGraph initial 0 0 0 ∧ !physicalRunFormula initial hist ∧
 !listHeadGraph last hist ∧ !stateGraph last q l r ∧ !terminalFormula q”
 (by simp [stateGraph_sigma,physicalRunFormula_sigma,terminalFormula_sigma])
variable {M:Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma physicalHaltSigma_eval : physicalHaltSigma.val.Evalb (![]:Fin 0→M) ↔ physicalHalts (M:=M) := by
 rw [physicalHalts_terminal_iff]
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [physicalHaltSigma]
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,hv,
 stateGraph_eval,physicalRunFormula_eval,ruleHead_defined.iff,terminalFormula_eval]
 constructor
 · rintro ⟨hist,hh,q,⟨l,r,hs⟩,ht⟩
   exact ⟨hist,hh,⟨q,l,r⟩,hs,ht⟩
 · rintro ⟨hist,hh,⟨q,l,r⟩,hs,ht⟩
   exact ⟨hist,hh,q,⟨l,r,hs⟩,ht⟩
end ZF209.BinaryTape
