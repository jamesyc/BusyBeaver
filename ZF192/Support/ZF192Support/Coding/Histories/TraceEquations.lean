module
public import ZF192Support.Coding.Lists.TailIterationLaws
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma modelTrace_zero (R : M → M → Prop) : modelTrace R 0 := by
 refine ⟨modelTailIter_zero 0,?_⟩
 intro k hk; exact False.elim (not_lt_zero hk)
lemma modelTrace_cons (R : M → M → Prop) (a b : M) : modelTrace R (modelListCons a b) ↔ modelTrace R b ∧ R a b := by
 let n := modelListCons a b
 have hn : 0<n := by dsimp [n,modelListCons]; simp
 have hb : b<n := by simpa only [n,modelListTail_cons] using modelListTail_lt n hn
 constructor
 · intro h
   have hr := h.2 0 hn
   simp only [modelTailIter_zero] at hr
   have hr' := hr.resolve_left (ne_of_gt hn)
   have hv : modelTrace R b := by
    refine ⟨modelTailIter_stops b b le_rfl,?_⟩
    intro k hk
    have hkn : k+1<n := lt_of_le_of_lt (succ_le_iff_lt.mpr hk) hb
    have he := h.2 (k+1) hkn
    rw [←modelTailIter_commute,show modelListTail n=b from modelListTail_cons a b] at he
    exact he
   exact ⟨hv,by simpa only [n,modelListHead_cons,modelListTail_cons] using hr'⟩
 · rintro ⟨h,hr⟩
   refine ⟨modelTailIter_stops n n le_rfl,?_⟩
   intro k hk
   by_cases hz:k=0
   · subst k
     right
     simpa only [modelTailIter_zero,n,modelListHead_cons,modelListTail_cons] using hr
   · obtain ⟨l,hl⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr hz)
     rw [hl,←modelTailIter_commute,show modelListTail n=b from modelListTail_cons a b]
     by_cases hlb:l<b
     · exact h.2 l hlb
     · exact Or.inl (modelTailIter_stops l b (le_of_not_gt hlb))
end ZFR.ArithmeticRepresentation
