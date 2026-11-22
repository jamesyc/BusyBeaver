module
public import ZF192.Tape.Determinism
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.BinaryTape
open ZFR.ArithmeticRepresentation M192
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalRows_length : M192.literalRows.length=192 := by decide +kernel
lemma literal_row_bound (q:Nat) (b w d:Bool) (n:Nat) (h:M192.literal q b=some (w,d,n)) : q<192 := by
 by_contra hn
 have hg : M192.literalRows.length≤q := by rw [literalRows_length]; omega
 have he : M192.literalRows[q]?=none := List.getElem?_eq_none hg
 simp only [M192.literal,tmOf,List.getD_eq_getElem?_getD,he,Option.getD_none] at h
 cases b <;> simp at h
lemma literalStep_of_zip_step (c c':BinaryTape.Conf) (h:BinaryTape.step M192.literal c=some c') :
 literalStep (encode (M:=M) c) (encode c') := by
 cases hr:M192.literal c.q (c.r.headD false) with
 | none => rw [BinaryTape.step,hr] at h; contradiction
 | some row =>
   rcases row with ⟨w,d,next⟩
   obtain ⟨out,ho,hm⟩:=move_encoded_of_row (M:=M) M192.literal c w d next hr
   have he:out=c' := Option.some.inj (ho.symm.trans h)
   subst out
   exact ⟨c.q,literal_row_bound _ _ _ _ _ hr,rfl,c.r.headD false,w,d,next,hr,hm⟩
/-- Exact standard-configuration binding, with arbitrary PA-model arithmetic values
as the proposed output. No extra arithmetic successor can appear. -/
lemma literalStep_encoded_iff (c:BinaryTape.Conf) (t:State M) :
 literalStep (encode c) t ↔ ∃c',BinaryTape.step M192.literal c=some c' ∧ t=encode c' := by
 constructor
 · intro hs
   rcases hs with ⟨q,hb,hq,b,w,d,next,hrow,hm⟩
   have heq:c.q=q := Nat.cast_inj.mp hq
   subst q
   obtain ⟨r,hr,rest⟩:=hm
   have hb' : b=c.r.headD false :=
    (binary_decomp_unique b (c.r.headD false) r (bitsCode c.r.tail)
     (hr.symm.trans (bitsCode_split c.r))).1
   subst b
   obtain ⟨c',hc',hmove⟩:=move_encoded_of_row (M:=M) M192.literal c w d next hrow
   exact ⟨c',hc',move_functional _ _ _ _ ⟨r,hr,rest⟩ hmove⟩
 · rintro ⟨c',hc',rfl⟩; exact literalStep_of_zip_step c c' hc'
end ZF192.BinaryTape
