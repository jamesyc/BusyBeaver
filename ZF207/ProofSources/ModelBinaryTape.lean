module
public import ExactListDecoderGraphs
public import M6.Zip
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def bitValue (b:Bool) : M := if b then 1 else 0
noncomputable def bitsCode : List Bool → M
 | [] => 0
 | b::bs => bitValue b+2*bitsCode bs
lemma bitsCode_trim (bs:List Bool) : bitsCode (M:=M) (M6.Zip.trim bs)=bitsCode bs := by
 induction bs with
 | nil => rfl
 | cons b bs ih =>
   rw [M6.Zip.trim_cons]
   split
   · rename_i h
     have hz:bitsCode (M:=M) bs=0 := by rw [←ih,h.2]; rfl
     simp [bitsCode,h.1,bitValue,hz]
   · simpa only [bitsCode] using congrArg (fun z:M=>bitValue b+2*z) ih
lemma bitsCode_split (bs:List Bool) :
 bitsCode (M:=M) bs=bitValue (bs.headD false)+2*bitsCode bs.tail := by
 cases bs <;> simp [bitsCode,bitValue]
lemma bitValue_cases (b:Bool) : bitValue (M:=M) b=0 ∨ bitValue (M:=M) b=1 := by
 cases b <;> simp [bitValue]
structure State (M:Type*) where
 q:M
 left:M
 right:M
noncomputable def encode (c:M6.Zip.Conf) : State M := ⟨(c.q:M),bitsCode c.l,bitsCode c.r⟩
/-- One physical move, with read/write/direction fixed by a finite table row.
The tape sides are little-endian binary numerals, so blank trimming is automatic. -/
def move (read write dir:Bool) (next:M) (s s':State M) : Prop := ∃r,
 s.right=bitValue read+2*r ∧ s'.q=next ∧
 if dir then s'.left=bitValue write+2*s.left ∧ s'.right=r
 else ∃l b, (b=0 ∨ b=1) ∧ s.left=b+2*l ∧ s'.left=l ∧
 s'.right=b+2*bitValue write+4*r
lemma move_right_encoded (c:M6.Zip.Conf) (write:Bool) (next:Nat) :
 move (c.r.headD false) write true (next:M) (encode c)
 (encode (M6.Zip.zc next (write::c.l) c.r.tail)) := by
 refine ⟨bitsCode c.r.tail,bitsCode_split c.r,rfl,?_,?_⟩
 · exact bitsCode_trim _
 · exact bitsCode_trim _
lemma move_left_encoded (c:M6.Zip.Conf) (write:Bool) (next:Nat) :
 move (c.r.headD false) write false (next:M) (encode c)
 (encode (M6.Zip.zl next c.l (write::c.r.tail))) := by
 refine ⟨bitsCode c.r.tail,bitsCode_split c.r,rfl,bitsCode c.l.tail,bitValue (c.l.headD false),
 bitValue_cases _,bitsCode_split c.l,?_,?_⟩
 · exact bitsCode_trim _
 · change bitsCode (M6.Zip.trim (c.l.headD false::write::c.r.tail))=_
   rw [bitsCode_trim]
   have h4 : (2:M)*2=4 := by norm_num
   simp only [bitsCode,mul_add,←mul_assoc,h4,add_assoc]
lemma move_encoded_of_row (tm:M6.Zip.TMN) (c:M6.Zip.Conf) (w d:Bool) (next:Nat)
 (h:tm c.q (c.r.headD false)=some (w,d,next)) :
 ∃c',M6.Zip.step tm c=some c' ∧ move (c.r.headD false) w d (next:M) (encode c) (encode c') := by
 cases d with
 | false => exact ⟨_,by rw [M6.Zip.step,h],move_left_encoded c w next⟩
 | true => exact ⟨_,by rw [M6.Zip.step,h],move_right_encoded c w next⟩
end ZF207.BinaryTape
