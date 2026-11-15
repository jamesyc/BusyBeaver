module
public import GenericSourceTransformNat
public import NumericTheory
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
inductive SchemaMap where | sep | repA | repB | repC
 def schemaMap : SchemaMap → Nat → Nat
 | .sep => sepIndex
 | .repA => repAIndex
 | .repB => repBIndex
 | .repC => repCIndex
def schemaIndexGraph : SchemaMap → 𝚺ᴬ₁.Semisentence 3
 | .sep => .mkSigma “y d i. (i<d ∧ y=i) ∨ (i≮d ∧ ((i=d ∧ y=d+0) ∨ (i≠d ∧ ((i=d+1 ∧ y=d+3) ∨ (i≠d+1 ∧ y=i+2)))))”
 | .repA => .mkSigma “y d i. (i<d ∧ y=i) ∨ (i≮d ∧ ((i=d ∧ y=d+2) ∨ (i≠d ∧ ((i=d+1 ∧ y=d+1) ∨ (i≠d+1 ∧ y=i+1)))))”
 | .repB => .mkSigma “y d i. (i<d ∧ y=i) ∨ (i≮d ∧ ((i=d ∧ y=d+2) ∨ (i≠d ∧ ((i=d+1 ∧ y=d+0) ∨ (i≠d+1 ∧ y=i+1)))))”
 | .repC => .mkSigma “y d i. (i<d ∧ y=i) ∨ (i≮d ∧ ((i=d ∧ y=d+0) ∨ (i≠d ∧ ((i=d+1 ∧ y=d+1) ∨ (i≠d+1 ∧ y=i+2)))))”
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def modelSchemaIndex (kind : SchemaMap) (d i : M) : M :=
 let z : M := match kind with | .sep => 0 | .repA => 2 | .repB => 2 | .repC => 0
 let o : M := match kind with | .sep => 3 | .repA => 1 | .repB => 0 | .repC => 1
 let k : M := match kind with | .sep => 2 | .repA => 1 | .repB => 1 | .repC => 2
 if i<d then i else if i=d then d+z else if i=d+1 then d+o else i+k
lemma schemaIndexGraph_eval (kind : SchemaMap) (z d i : M) :
 (schemaIndexGraph kind).val.Evalb ![z,d,i] ↔ z=modelSchemaIndex kind d i := by
 classical
 cases kind <;> by_cases h:i<d <;> by_cases h0:i=d <;> by_cases h1:i=d+1 <;>
 simp [schemaIndexGraph,modelSchemaIndex,h,h0,h1,numeral_eq_natCast]
lemma schemaIndexGraph_total (kind : SchemaMap) : GraphTotalIn (M:=M) (schemaIndexGraph kind) := by
 intro v
 have hv:v=![v 0,v 1] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]
 simp only [schemaIndexGraph_eval]
 exact ⟨_,rfl,fun _ h=>h⟩
lemma modelSchemaIndex_nat (kind : SchemaMap) (d i : Nat) :
 modelSchemaIndex kind d i=sourceRenameIndex (schemaMap kind) d i := by
 cases kind <;> simp only [modelSchemaIndex,sourceRenameIndex,schemaMap,sepIndex,repAIndex,repBIndex,repCIndex]
 all_goals split_ifs <;> omega
end ZFR.ArithmeticRepresentation
