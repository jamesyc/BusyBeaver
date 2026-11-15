module
public import ModelPhysicalMarkFirst
public import ModelPhysicalReturnBlocks
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation M6.Runtime
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Skip a finite primary prefix; each unary block length is an arbitrary model
value and is traversed by the genuine internally proved physical scanner. -/
lemma named_skip_primary_prefix (values:List M) (m:Nat) (l tail:M)
 (bound:values.length+m<9) :
 Reaches (namedState (sk (values.length+m)) l (values.foldr registerBlock tail))
 (namedState (sk m) (values.foldl (fun acc v=>registerBlockLeft v acc) l) tail) := by
 induction values generalizing l with
 | nil => simpa only [List.length_nil,Nat.zero_add,List.foldr_nil,List.foldl_nil] using
   Reaches.refl (namedState (sk m) l tail)
 | cons v vs ih =>
  simp only [List.length_cons,List.foldr_cons,List.foldl_cons] at bound ⊢
  rw [show vs.length+1+m=(vs.length+m)+1 by omega]
  have hz:=M6.Native.sk_next M209.native_agreement (vs.length+m) (by omega)
  have ho:=M6.Native.sk_self M209.native_agreement (vs.length+m) (by omega)
  have h₁:Reaches (namedState (sk ((vs.length+m)+1)) l (registerBlock v (vs.foldr registerBlock tail)))
   (namedState (sk (vs.length+m)) (2*l) (bitRun (v+1) 1 (vs.foldr registerBlock tail))) := by
    simpa only [registerBlock,bitValue,Bool.false_eq_true,ite_false,zero_add] using
     named_right _ _ false false l (bitRun (v+1) 1 (vs.foldr registerBlock tail)) hz
  have h₂:Reaches (namedState (sk (vs.length+m)) (2*l) (bitRun (v+1) 1 (vs.foldr registerBlock tail)))
   (namedState (sk (vs.length+m)) (registerBlockLeft v l) (vs.foldr registerBlock tail)) := by
    simpa only [registerBlockLeft,bitValue,ite_true] using
     named_scan_right (sk (vs.length+m)) true (v+1) (2*l) (vs.foldr registerBlock tail) ho
  exact h₁.trans (h₂.trans (ih (registerBlockLeft v l) (by omega)))
private lemma model_values_snoc (values:List M) (h:values≠[]) : ∃pre v,values=pre++[v] := by
 induction values with
 | nil => contradiction
 | cons a vs ih =>
  cases vs with
  | nil => exact ⟨[],a,rfl⟩
  | cons b bs =>
   obtain ⟨pre,v,hp⟩:=ih (List.cons_ne_nil _ _)
   exact ⟨a::pre,v,by simp only [hp,List.cons_append]⟩
/-- Mark return enters the rightmost prior block at control1, then returns over
the rest at control3. These are the actual native rows1/2/3. -/
lemma native_mark_return_prefix (values:List M) (l tail:M) (hne:values≠[]) :
 Reaches (namedLeft 1 (values.foldl (fun acc v=>registerBlockLeft v acc) l) tail)
 (namedLeft 3 l (values.foldr registerBlock tail)) := by
 obtain ⟨pre,v,rfl⟩:=model_values_snoc values hne
 simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,List.foldr_append,List.foldr_cons,List.foldr_nil]
 exact (named_return_block 2 3 1 v (pre.foldl (fun acc v=>registerBlockLeft v acc) l) tail
  (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans
  (named_return_primary_prefix 2 3 pre l (registerBlock v tail)
   (by decide +kernel) (by decide +kernel) (by decide +kernel))
/-- Full native mark for any selected primary register (index<9). Only the
number of primary registers is externally finite; their values are model-sized. -/
lemma native_mark_primary (values:List M) (value l tail:M) (bound:values.length<9) :
 Reaches (namedState (sk values.length) l (values.foldr registerBlock (registerBlock value tail)))
 (namedLeft (markExit values.length) l (values.foldr registerBlock (markedBlock value tail))) := by
 have hs:=named_skip_primary_prefix values 0 l (registerBlock value tail) (by simpa using bound)
 simp only [Nat.add_zero] at hs
 have hm:=native_mark_first value (values.foldl (fun acc v=>registerBlockLeft v acc) l) tail
 have ht:=hs.trans hm
 by_cases hnil:values=[]
 · subst values
   simpa only [List.length_nil,List.foldr_nil,List.foldl_nil,markExit,ite_true] using ht
 · have hlen:values.length≠0 := by simpa using hnil
   have hr:=native_mark_return_prefix values l (markedBlock value tail) hnil
   simpa only [markExit,if_neg hlen] using ht.trans hr
end ZF209.BinaryTape
