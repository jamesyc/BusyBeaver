module
public import ModelNativeFrameEncoding
public import ModelRuntimeEncoding
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation M6.Runtime
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def primaryList (r:Fin 9→M) : List M := [r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8]
noncomputable def incrementRegisters (r:Fin 9→M) (k:Fin 9) : Fin 9→M := fun i=>if i=k then r i+1 else r i
noncomputable def decrementRegisters (r:Fin 9→M) (k:Fin 9) : Fin 9→M := fun i=>if i=k then modelPredecessor (r i) else r i
lemma primary_increment (r:Fin 9→M) (k:Fin 9) : primaryIncrement k.val (primaryList r)=primaryList (incrementRegisters r k) := by
 rcases k with ⟨k,hk⟩
 have hh:k=0∨k=1∨k=2∨k=3∨k=4∨k=5∨k=6∨k=7∨k=8:=by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst k <;> simp [primaryList,incrementRegisters,primaryIncrement]
lemma primary_decrement (r:Fin 9→M) (k:Fin 9) : primaryDecrement k.val (primaryList r)=primaryList (decrementRegisters r k) := by
 rcases k with ⟨k,hk⟩
 have hh:k=0∨k=1∨k=2∨k=3∨k=4∨k=5∨k=6∨k=7∨k=8:=by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst k <;> simp [primaryList,decrementRegisters,primaryDecrement]
lemma primary_file (r:Fin 9→M) (spares:M) : (primaryList r).foldr registerBlock (spareRun spares 0)=registerFile r spares := rfl
lemma flat_path (path:List Bool) (gap spares:M) (values:List M) (tail:List Seg) :
 modelFlat gap values spares (path.map Seg.bit++tail)=bitPrefix path (modelFlat gap values spares tail) := by
 induction path with
 | nil=>rfl
 | cons b bs ih=>simp only [List.map_cons,List.cons_append,modelFlat_cons,modelSeg,bitPrefix,ih]
lemma root_frame_none (pc extra:Nat) (hlen:(M207.Source.paths pc).length≤48) (gap spares:M) (r:Fin 9→M) :
 modelConc gap (primaryList r) spares (M207.Source.rootFrame (M207.Source.paths pc) extra .none)=
 nativeFrame pc (gap+(extra:M)) r spares := by
 have hn:48+extra-(M207.Source.paths pc).length=extra+(48-(M207.Source.paths pc).length):=by omega
 simp only [M207.Source.rootFrame,modelConc,flat_path]
 simp [modelFlat,modelSeg,modelBox,bitValue,primary_file,nativeFrame,hn,Nat.cast_add,add_assoc]
lemma root_frame_inc (pc extra:Nat) (hlen:(M207.Source.paths pc).length≤48) (gap spares:M) (r:Fin 9→M) (k:Fin 9) :
 modelConc gap (primaryList r) spares (M207.Source.rootFrame (M207.Source.paths pc) extra (.inc k.val))=
 nativeFrame pc (gap+(extra:M)) (incrementRegisters r k) (spares+1) := by
 have hn:48+extra-(M207.Source.paths pc).length=extra+(48-(M207.Source.paths pc).length):=by omega
 simp only [M207.Source.rootFrame,modelConc,flat_path]
 simp [modelFlat,modelSeg,modelBox,bitValue,primary_increment,primary_file,nativeFrame,hn,Nat.cast_add,add_assoc]
lemma root_frame_dec (pc extra:Nat) (hlen:(M207.Source.paths pc).length≤48) (gap spares:M) (r:Fin 9→M) (k:Fin 9) :
 modelConc gap (primaryList r) spares (M207.Source.rootFrame (M207.Source.paths pc) extra (.dec k.val))=
 nativeFrame pc (gap+(extra:M)) (decrementRegisters r k) spares := by
 have hn:48+extra-(M207.Source.paths pc).length=extra+(48-(M207.Source.paths pc).length):=by omega
 simp only [M207.Source.rootFrame,modelConc,flat_path]
 simp [modelFlat,modelSeg,modelBox,bitValue,primary_decrement,primary_file,nativeFrame,hn,Nat.cast_add,add_assoc]
end ZF207.BinaryTape
