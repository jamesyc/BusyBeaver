module
public import ModelPhysicalRightScan
public import ModelPhysicalLeftScan
public import M207.Permutation
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Exact physical macro contract retaining an arbitrary earlier rooted history. -/
def Reaches (s t:State M) : Prop := ∀initial hist:M,
 runHistory initial hist → modelListHead hist=stateCode s →
 ∃out,runHistory initial out ∧ modelListHead out=stateCode t
lemma Reaches.refl (s:State M) : Reaches s s := by
 intro initial hist hh he; exact ⟨hist,hh,he⟩
lemma Reaches.step {s t:State M} (h:literalStep s t) : Reaches s t := by
 intro initial hist hh he
 refine ⟨modelListCons (stateCode t) hist,?_,modelListHead_cons _ _⟩
 apply runHistory_extend hh
 rw [he]; exact ⟨s,t,rfl,rfl,h⟩
lemma Reaches.trans {s t u:State M} (h:Reaches s t) (g:Reaches t u) : Reaches s u := by
 intro initial hist hh he
 obtain ⟨middle,hm,hem⟩:=h initial hist hh he
 exact g initial middle hm hem
lemma physical_right (q target:Nat) (read write:Bool) (l r:M)
 (row:M207.literal q read=some (write,true,target)) :
 Reaches ⟨(q:M),l,bitValue read+2*r⟩ ⟨(target:M),bitValue write+2*l,r⟩ := by
 apply Reaches.step
 exact ⟨q,literal_row_bound _ _ _ _ _ row,rfl,read,write,true,target,row,r,rfl,rfl,rfl,rfl⟩
lemma physical_left (q target:Nat) (read write leftbit:Bool) (l r:M)
 (row:M207.literal q read=some (write,false,target)) :
 Reaches ⟨(q:M),bitValue leftbit+2*l,bitValue read+2*r⟩
  ⟨(target:M),l,bitValue leftbit+2*bitValue write+4*r⟩ := by
 apply Reaches.step
 exact ⟨q,literal_row_bound _ _ _ _ _ row,rfl,read,write,false,target,row,
 r,rfl,rfl,l,bitValue leftbit,bitValue_cases _,rfl,rfl,rfl⟩
lemma scan_right (q:Nat) (b:Bool) (n l r:M)
 (row:M207.literal q b=some (b,true,q)) :
 Reaches ⟨(q:M),l,bitRun n (bitValue b) r⟩ ⟨(q:M),bitRun n (bitValue b) l,r⟩ :=
 physical_scan_right q b row n l r
/-- Native frame labels are transported through the proved exact207 permutation. -/
noncomputable def namedState (q:Nat) (l r:M) : State M := ⟨(M207.forward q:M),l,r⟩
lemma literal_of_renamed_row {q target:Nat} {read write dir:Bool}
 (h:M207.renamed q read=some (write,dir,target)) :
 M207.literal (M207.forward q) read=some (write,dir,M207.forward target) := by
 have he:=M207.renamed_row M207.forward_inverse q read
 rw [h] at he
 exact he.symm
lemma named_right (q target:Nat) (read write:Bool) (l r:M)
 (row:M207.renamed q read=some (write,true,target)) :
 Reaches (namedState q l (bitValue read+2*r)) (namedState target (bitValue write+2*l) r) :=
 physical_right _ _ _ _ _ _ (literal_of_renamed_row row)
lemma named_left (q target:Nat) (read write leftbit:Bool) (l r:M)
 (row:M207.renamed q read=some (write,false,target)) :
 Reaches (namedState q (bitValue leftbit+2*l) (bitValue read+2*r))
 (namedState target l (bitValue leftbit+2*bitValue write+4*r)) :=
 physical_left _ _ _ _ _ _ _ (literal_of_renamed_row row)
lemma named_scan_right (q:Nat) (b:Bool) (n l r:M)
 (row:M207.renamed q b=some (b,true,q)) :
 Reaches (namedState q l (bitRun n (bitValue b) r)) (namedState q (bitRun n (bitValue b) l) r) :=
 scan_right (M207.forward q) b n l r (literal_of_renamed_row row)
lemma named_scan_left (q:Nat) (b:Bool) (n l r:M)
 (row:M207.renamed q b=some (b,false,q)) :
 Reaches (namedState q (bitRun n (bitValue b) l) (bitValue b+2*r))
 (namedState q l (bitRun n (bitValue b) (bitValue b+2*r))) :=
 physical_scan_left (M207.forward q) b (literal_of_renamed_row row) n l r
end ZF207.BinaryTape
