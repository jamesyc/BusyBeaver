module
public import ExactFullRuleFormula
public import NumericTheory
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
def fixedNumberGraph (n : Nat) : 𝚺ᴬ₁.Semisentence 1 := .mkSigma “z. z=↑n”
def fixedNodeGraph (tag : Nat) (a b : 𝚺ᴬ₁.Semisentence 1) : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
 “z. ∃ x, ∃ y, !a x ∧ !b y ∧ !sourceNodeGraph z ↑tag x y”
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma fixedNumberGraph_eval (n : Nat) (z : M) : (fixedNumberGraph n).val.Evalb ![z] ↔ z=(n:M) := by
 simp [fixedNumberGraph,numeral_eq_natCast]
lemma fixedNodeGraph_eval (tag : Nat) (a b : 𝚺ᴬ₁.Semisentence 1) (z : M) :
 (fixedNodeGraph tag a b).val.Evalb ![z] ↔ ∃x y, a.val.Evalb ![x] ∧ b.val.Evalb ![y] ∧ z=modelSourceNode (tag:M) x y := by
 simp [fixedNodeGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
 Matrix.comp_vecCons',Matrix.empty_eq,ruleNode_defined.iff,numeral_eq_natCast]
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv]

def fixedFormulaGraph : Formula → 𝚺ᴬ₁.Semisentence 1
 | .bot => fixedNumberGraph 0
 | .mem i j => fixedNodeGraph 1 (fixedNumberGraph i) (fixedNumberGraph j)
 | .eq i j => fixedNodeGraph 2 (fixedNumberGraph i) (fixedNumberGraph j)
 | .and a b => fixedNodeGraph 3 (fixedFormulaGraph a) (fixedFormulaGraph b)
 | .or a b => fixedNodeGraph 4 (fixedFormulaGraph a) (fixedFormulaGraph b)
 | .imp a b => fixedNodeGraph 5 (fixedFormulaGraph a) (fixedFormulaGraph b)
 | .all a => fixedNodeGraph 6 (fixedFormulaGraph a) (fixedNumberGraph 0)
 | .ex a => fixedNodeGraph 7 (fixedFormulaGraph a) (fixedNumberGraph 0)
noncomputable def modelFixedFormula : Formula → M
 | .bot => 0
 | .mem i j => modelSourceNode 1 (i:M) (j:M)
 | .eq i j => modelSourceNode 2 (i:M) (j:M)
 | .and a b => modelSourceNode 3 (modelFixedFormula a) (modelFixedFormula b)
 | .or a b => modelSourceNode 4 (modelFixedFormula a) (modelFixedFormula b)
 | .imp a b => modelSourceNode 5 (modelFixedFormula a) (modelFixedFormula b)
 | .all a => modelSourceNode 6 (modelFixedFormula a) 0
 | .ex a => modelSourceNode 7 (modelFixedFormula a) 0
lemma fixedFormulaGraph_eval (f : Formula) (z : M) :
 (fixedFormulaGraph f).val.Evalb ![z] ↔ z=modelFixedFormula f := by
 induction f generalizing z <;>
 simp only [fixedFormulaGraph,modelFixedFormula,fixedNumberGraph_eval,fixedNodeGraph_eval,
 Nat.cast_ofNat,exists_eq_left',exists_eq_left,and_true] <;> simp_all
lemma modelFixedFormula_nat (f : Formula) : modelFixedFormula (M:=Nat) f=encodeFormula f := by
 induction f <;> simp_all [modelFixedFormula,encodeFormula,modelSourceNode_nat,sourceNode]
end ZFR.ArithmeticRepresentation
