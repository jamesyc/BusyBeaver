module
public import ModelReplay1890
public import ModelPsetInductionCertificate
public import LiteralRadix8ModelAlignment
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalPset_beta (b c k : M) : t109 (t63 b c) k ↔ mm0BetaMembership b c k := by
 classical
 have h := p1886 b k c
 simp [t3,t2,t0,t1,t8,t16,t58,t9,t10,t45,t29,t28,literalLt_order,literalLe_order,
 mm0BetaMembership,and_assoc,add_comm] at h ⊢
 constructor
 · intro hp
   obtain ⟨hb,hc,hd,q,hq⟩ := h.1 hp
   exact ⟨hb,pos_iff_ne_zero.mpr hc,hd,q,hq⟩
 · rintro ⟨hb,hc,hd,q,hq⟩
   exact h.2 hb (ne_of_gt hc) hd q hq
end ZF209.MM0ModelReplay
