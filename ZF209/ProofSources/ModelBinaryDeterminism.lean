module
public import ModelLiteral209Step
public import ModelNumeralOrder
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma twice_injective {x y:M} (h:2*x=2*y) : x=y := by
 rcases lt_trichotomy x y with hxy|he|hyx
 · have hh:=mul_lt_mul_of_pos_left hxy (by norm_num : (0:M)<2)
   rw [h] at hh; exact False.elim (_root_.lt_irrefl _ hh)
 · exact he
 · have hh:=mul_lt_mul_of_pos_left hyx (by norm_num : (0:M)<2)
   rw [h] at hh; exact False.elim (_root_.lt_irrefl _ hh)
lemma even_ne_odd (x y:M) : 2*x≠2*y+1 := by
 intro h
 rcases le_or_gt x y with hxy|hyx
 · have hh:2*x≤2*y := mul_le_mul_of_nonneg_left hxy (by simp)
   rw [h] at hh
   exact (not_le_of_gt (by simp : 2*y<2*y+1)) hh
 · have hh:2*(y+1)≤2*x := mul_le_mul_of_nonneg_left (succ_le_iff_lt.mpr hyx) (by simp)
   rw [h,mul_add,mul_one] at hh
   have ht:2*y+1<2*y+2 := by simp
   exact (not_le_of_gt ht) hh
lemma binary_decomp_unique (b c:Bool) (x y:M)
 (h:bitValue b+2*x=bitValue c+2*y) : b=c ∧ x=y := by
 cases b <;> cases c <;> simp only [bitValue,Bool.false_eq_true,ite_false,ite_true,zero_add] at h ⊢
 · exact ⟨trivial,twice_injective h⟩
 · exact False.elim (even_ne_odd x y (by simpa only [add_comm] using h))
 · exact False.elim (even_ne_odd y x (by simpa only [add_comm] using h.symm))
 · exact ⟨trivial,twice_injective (add_left_cancel h)⟩
lemma move_functional (read write dir:Bool) (next:M) {s t u:State M}
 (h₁:move read write dir next s t) (h₂:move read write dir next s u) : t=u := by
 obtain ⟨r₁,hr₁,hq₁,ht⟩:=h₁; obtain ⟨r₂,hr₂,hq₂,hu⟩:=h₂
 have hr:r₁=r₂ := (binary_decomp_unique _ _ _ _ (hr₁.symm.trans hr₂)).2
 subst r₂
 cases dir with
 | true =>
   obtain ⟨hl₁,hrr₁⟩:=ht; obtain ⟨hl₂,hrr₂⟩:=hu
   cases t; cases u; simp_all
 | false =>
   obtain ⟨l₁,b₁,hb₁,hl₁,htl,htr⟩:=ht; obtain ⟨l₂,b₂,hb₂,hl₂,hul,hur⟩:=hu
   have he : b₁=b₂ ∧ l₁=l₂ := by
    rcases hb₁ with h0|h1 <;> rcases hb₂ with g0|g1
    · rw [h0,g0]; exact ⟨rfl,twice_injective (by simpa [h0,g0] using hl₁.symm.trans hl₂)⟩
    · exact False.elim (even_ne_odd l₁ l₂ (by simpa [h0,g1,add_comm] using hl₁.symm.trans hl₂))
    · exact False.elim (even_ne_odd l₂ l₁ (by simpa [h1,g0,add_comm] using hl₂.symm.trans hl₁))
    · rw [h1,g1]; exact ⟨rfl,by simpa [h1,g1] using hl₁.symm.trans hl₂⟩
   rcases he with ⟨rfl,rfl⟩
   cases t; cases u; simp_all
end ZF209.BinaryTape
