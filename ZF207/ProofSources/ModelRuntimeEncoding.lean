module
public import ModelPhysicalIncrementFile
public import ModelPhysicalDecrementFile
public import ModelPhysicalMarkPrimary
public import ModelBitRunAlgebra
public import ModelResidualTail
public import M6.Runtime
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation M6.Runtime
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def primaryIncrement : Nat → List M → List M
 | _,[] => []
 | 0,v::vs => (v+1)::vs
 | n+1,v::vs => v::primaryIncrement n vs
noncomputable def primaryDecrement : Nat → List M → List M
 | _,[] => []
 | 0,v::vs => modelPredecessor v::vs
 | n+1,v::vs => v::primaryDecrement n vs
noncomputable def markedFile : Nat → List M → M → M
 | _,[],tail => tail
 | 0,v::vs,tail => markedBlock v (vs.foldr registerBlock tail)
 | n+1,v::vs,tail => registerBlock v (markedFile n vs tail)
/-- Symbolic boxes retain a genuine model-sized spare suffix. Effect tags apply
to the fixed finite primary list, never to a truncated file. -/
noncomputable def modelBox (values:List M) (spares:M) : BoxSt → M → M
 | .plain .none,tail => values.foldr registerBlock (spareRun spares tail)
 | .plain (.inc r),tail => (primaryIncrement r values).foldr registerBlock (spareRun (spares+1) tail)
 | .plain (.dec r),tail => (primaryDecrement r values).foldr registerBlock (spareRun spares tail)
 | .mark r,tail => markedFile r values (spareRun spares tail)
noncomputable def modelSeg (gap:M) (values:List M) (spares:M) : Seg → M → M
 | .bit b,tail => bitValue b+2*tail
 | .run b a c,tail => bitRun ((a:M)*gap+(c:M)) (bitValue b) tail
 | .box x,tail => modelBox values spares x tail
noncomputable def modelFlat (gap:M) (values:List M) (spares:M) (segs:List Seg) : M :=
 segs.foldr (modelSeg gap values spares) 0
noncomputable def modelConc (gap:M) (values:List M) (spares:M) : SConf → State M
 | (q,true,l,r) => namedLeft q (modelFlat gap values spares l) (modelFlat gap values spares r)
 | (q,false,l,r) => namedState q (modelFlat gap values spares l) (modelFlat gap values spares r)
lemma modelFlat_nil (gap:M) (values:List M) (spares:M) : modelFlat gap values spares []=0 := rfl
lemma modelFlat_cons (gap:M) (values:List M) (spares:M) (x:Seg) (xs:List Seg) :
 modelFlat gap values spares (x::xs)=modelSeg gap values spares x (modelFlat gap values spares xs) := rfl
lemma primaryIncrement_split (pre post:List M) (v:M) :
 primaryIncrement pre.length (pre++v::post)=pre++(v+1)::post := by
 induction pre with
 | nil => rfl
 | cons a pre ih => simp only [List.length_cons,List.cons_append,primaryIncrement,ih]
lemma primaryDecrement_split (pre post:List M) (v:M) :
 primaryDecrement pre.length (pre++v::post)=pre++modelPredecessor v::post := by
 induction pre with
 | nil => rfl
 | cons a pre ih => simp only [List.length_cons,List.cons_append,primaryDecrement,ih]
lemma markedFile_split (pre post:List M) (v tail:M) :
 markedFile pre.length (pre++v::post) tail=pre.foldr registerBlock (markedBlock v (post.foldr registerBlock tail)) := by
 induction pre with
 | nil => rfl
 | cons a pre ih => simp only [List.length_cons,List.cons_append,markedFile,List.foldr_cons,ih]
end ZF207.BinaryTape
