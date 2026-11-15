module
public import ModelPhysicalFileScan
public import ModelBinaryUncons
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Numeric counterpart of Zip.zl: head is on the first bit of the left word. -/
noncomputable def namedLeft (q:Nat) (l r:M) : State M :=
 namedState q (tailBits l) (lowBit l+2*r)
lemma namedLeft_cons (q:Nat) (b:Bool) (l r:M) :
 namedLeft q (bitValue b+2*l) r=namedState q l (bitValue b+2*r) := by
 simp only [namedLeft,lowBit_cons,tailBits_cons]
lemma named_left_any (q target:Nat) (read write:Bool) (l r:M)
 (row:M209.renamed q read=some (write,false,target)) :
 Reaches (namedState q l (bitValue read+2*r)) (namedLeft target l (bitValue write+2*r)) := by
 obtain ⟨b,lt,rfl⟩:=bits_surjective l
 rw [namedLeft_cons]
 have h4:(2:M)*2=4 := by norm_num
 simpa only [mul_add,←mul_assoc,h4,add_assoc] using named_left q target read write b lt r row
lemma named_scan_left_oriented (q:Nat) (b:Bool) (n l r:M)
 (row:M209.renamed q b=some (b,false,q)) :
 Reaches (namedLeft q (bitRun n (bitValue b) l) r)
 (namedLeft q l (bitRun n (bitValue b) r)) := by
 by_cases hn:n=0
 · subst n; simp only [bitRun_zero]; exact Reaches.refl _
 · obtain ⟨k,hk⟩:=eq_succ_of_pos (pos_iff_ne_zero.mpr hn)
   rw [hk]
   nth_rw 1 [bitRun_succ]
   rw [namedLeft_cons]
   have hs:=named_scan_left q b k l r row
   rw [bitRun_commute] at hs
   have hm:=named_left_any q q b b l (bitRun k (bitValue b) r) row
   rw [←bitRun_succ] at hm
   exact hs.trans hm
end ZF209.BinaryTape
