module
public import ExactSchemaIndexGraphs
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def schemaRenameGraph (kind : SchemaMap) : 𝚺ᴬ₁.Semisentence 3 := GenericTransform.transformGraph (schemaIndexGraph kind)
noncomputable def modelSchemaRename (kind : SchemaMap) (d n : M) : M :=
 GenericTransform.modelTransform (schemaIndexGraph kind) (schemaIndexGraph_total kind) d n
lemma schemaRenameGraph_eval (kind : SchemaMap) (z d n : M) :
 (schemaRenameGraph kind).val.Evalb ![z,d,n] ↔ z=modelSchemaRename kind d n :=
 GenericTransform.transformGraph_eval _ _ _ _ _
lemma schemaRenameGraph_defined (kind : SchemaMap) : 𝚺ᴬ₁.DefinedFunction₂ (modelSchemaRename (M:=M) kind) (schemaRenameGraph kind) := .mk (by
 intro v
 have hv : v=![v 0,v 1,v 2] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  refine Fin.cases rfl (fun j=>?_) j
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]; exact schemaRenameGraph_eval _ _ _ _)
lemma modelSchemaRename_nat (kind : SchemaMap) (d n : Nat) :
 modelSchemaRename kind d n=sourceRename (schemaMap kind) d n := by
 apply GenericTransform.modelTransform_nat
 intro d i
 have h := (graphValue_spec (schemaIndexGraph kind) (schemaIndexGraph_total kind) _ ![d,i]).mpr rfl
 exact ((schemaIndexGraph_eval kind _ d i).mp h).trans (modelSchemaIndex_nat kind d i)
end ZFR.ArithmeticRepresentation
