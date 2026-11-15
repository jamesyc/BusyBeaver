module
public import ExactSchemaConstructorGraphs
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma numericSeparationGraph_defined : 𝚺ᴬ₁.DefinedFunction₁ (modelNumericSeparation (M:=M)) numericSeparationGraph := .mk (by
 intro v
 have hv:v=![v 0,v 1] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]; exact numericSeparationGraph_eval _ _)
lemma numericReplacementGraph_defined : 𝚺ᴬ₁.DefinedFunction₃ (modelNumericReplacement (M:=M)) numericReplacementGraph := .mk (by
 intro v
 have hv:v=![v 0,v 1,v 2,v 3] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  refine Fin.cases rfl (fun j=>?_) j
  refine Fin.cases rfl (fun j=>?_) j
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]; exact numericReplacementGraph_eval _ _ _ _)
noncomputable def modelAllPrefix (n a : M) := (allPrefixConstruction (M:=M)).result ![a] n
lemma allPrefixGraph_defined : 𝚺ᴬ₁.DefinedFunction₂ (modelAllPrefix (M:=M)) allPrefixBlueprint.resultDef := .mk (by
 intro v
 have hv:v=![v 0,v 1,v 2] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  refine Fin.cases rfl (fun j=>?_) j
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]; exact allPrefixConstruction.result_defined_iff _)

def separationCodeGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z phi n. ∃ r, ∃ s, !(schemaRenameGraph .sep) r 0 phi ∧ !numericSeparationGraph s r ∧ !(allPrefixBlueprint.resultDef) z n s”
def replacementCodeGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z phi n. ∃ a, ∃ b, ∃ c, ∃ s, !(schemaRenameGraph .repA) a 0 phi ∧ !(schemaRenameGraph .repB) b 0 phi ∧ !(schemaRenameGraph .repC) c 0 phi ∧ !numericReplacementGraph s a b c ∧ !(allPrefixBlueprint.resultDef) z n s”
noncomputable def modelSeparationCode (phi n : M) := modelAllPrefix n (modelNumericSeparation (modelSchemaRename .sep 0 phi))
noncomputable def modelReplacementCode (phi n : M) := modelAllPrefix n (modelNumericReplacement (modelSchemaRename .repA 0 phi) (modelSchemaRename .repB 0 phi) (modelSchemaRename .repC 0 phi))
lemma separationCodeGraph_defined : 𝚺ᴬ₁.DefinedFunction₂ (modelSeparationCode (M:=M)) separationCodeGraph := .mk (by
 intro v
 simp [separationCodeGraph,modelSeparationCode,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,
 (schemaRenameGraph_defined .sep).iff,(schemaRenameGraph_defined .repA).iff,(schemaRenameGraph_defined .repB).iff,(schemaRenameGraph_defined .repC).iff,numericSeparationGraph_defined.iff,allPrefixGraph_defined.iff])
lemma replacementCodeGraph_defined : 𝚺ᴬ₁.DefinedFunction₂ (modelReplacementCode (M:=M)) replacementCodeGraph := .mk (by
 intro v
 simp [replacementCodeGraph,modelReplacementCode,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,
 (schemaRenameGraph_defined .sep).iff,(schemaRenameGraph_defined .repA).iff,(schemaRenameGraph_defined .repB).iff,(schemaRenameGraph_defined .repC).iff,numericReplacementGraph_defined.iff,allPrefixGraph_defined.iff])
lemma modelSeparationCode_nat (phi n : Nat) : modelSeparationCode phi n=numericSeparationCode phi n := by
 simp only [modelSeparationCode,modelSchemaRename_nat,modelNumericSeparation_nat,modelAllPrefix,allPrefix_result_exact,numericSeparationCode,schemaMap]
lemma modelReplacementCode_nat (phi n : Nat) : modelReplacementCode phi n=numericReplacementCode phi n := by
 simp only [modelReplacementCode,modelSchemaRename_nat,modelNumericReplacement_nat,modelAllPrefix,allPrefix_result_exact,numericReplacementCode,schemaMap]
end ZFR.ArithmeticRepresentation
