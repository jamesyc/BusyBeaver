module
public import EqualityTemplates
@[expose] public section
namespace ZFR

def zfrSym : Formula := .all (.all (.imp (.eq 1 0) (.eq 0 1)))
def zfrPair : Formula := .all (.all (.ex (.all (.and
 (.imp (.mem 0 1) (.or (.eq 0 3) (.eq 0 2)))
 (.imp (.or (.eq 0 3) (.eq 0 2)) (.mem 0 1))))))
def zfrFoundation : Formula := .all (.imp (.ex (.mem 0 1))
 (.ex (.and (.mem 0 1) (.all (.imp (.mem 0 1) (.imp (.mem 0 2) .bot))))))

def singletonSpec (i s : Nat) : Formula := .all (.and
 (.imp (.mem 0 (s+1)) (.or (.eq 0 (i+1)) (.eq 0 (i+1))))
 (.imp (.or (.eq 0 (i+1)) (.eq 0 (i+1))) (.mem 0 (s+1))))
def minimalSpec (s : Nat) : Formula := .and (.mem 0 (s+1))
 (.all (.imp (.mem 0 1) (.imp (.mem 0 (s+2)) .bot)))

@[simp] theorem shift_zfrRefl : shift zfrRefl = zfrRefl := rfl
@[simp] theorem shift_zfrEqElem : shift zfrEqElem = zfrEqElem := rfl
@[simp] theorem shift_zfrSym : shift zfrSym = zfrSym := rfl
@[simp] theorem shift_zfrPair : shift zfrPair = zfrPair := rfl
@[simp] theorem shift_zfrFoundation : shift zfrFoundation = zfrFoundation := rfl

theorem shifted_member {a : Formula} {Γ : Context} (ha : a ∈ Γ) (h : shift a = a) : a ∈ shiftContext Γ := by
 exact List.mem_map.mpr ⟨a,ha,h⟩

theorem nd_sym_instance {Γ : Context} (h : zfrSym ∈ Γ) (a b : Nat) :
 ND (.seq Γ (.imp (.eq a b) (.eq b a))) := by
 have ht := ND.allE b (ND.allE a (ND.ctx h))
 simpa [zfrSym, subst, rename, lift, substMap] using ht

theorem nd_pair_singleton {Γ : Context} (h : zfrPair ∈ Γ) (i : Nat) :
 ND (.seq Γ (.ex (singletonSpec (i+1) 0))) := by
 have ht := ND.allE i (ND.allE i (ND.ctx h))
 simpa [zfrPair, singletonSpec, subst, rename, lift, substMap, Nat.add_assoc] using ht

theorem nd_foundation_instance {Γ : Context} (h : zfrFoundation ∈ Γ) (s : Nat) :
 ND (.seq Γ (.imp (.ex (.mem 0 (s+1))) (.ex (minimalSpec s)))) := by
 have ht := ND.allE s (ND.ctx h)
 simpa [zfrFoundation, minimalSpec, subst, rename, lift, substMap, Nat.add_assoc] using ht

theorem nd_singleton_instance {Γ : Context} {i s : Nat}
 (h : ND (.seq Γ (singletonSpec i s))) (a : Nat) :
 ND (.seq Γ (.and
 (.imp (.mem a s) (.or (.eq a i) (.eq a i)))
 (.imp (.or (.eq a i) (.eq a i)) (.mem a s)))) := by
 simpa [singletonSpec, subst, rename, lift, substMap] using ND.allE a h

theorem nd_or_self {Γ : Context} {a : Formula} (h : ND (.seq Γ (.or a a))) : ND (.seq Γ a) := by
 exact ND.de h (ND.branchPair (ND.ctx (by simp)) (ND.ctx (by simp)))

theorem nd_weaken_head {Γ : Context} {a b : Formula} (h : ND (.seq Γ a)) : ND (.seq (b::Γ) a) :=
 ND.wk (by intro x hx; simp [hx]) h

theorem shift_singletonSpec (i s : Nat) : shift (singletonSpec i s) = singletonSpec (i+1) (s+1) := by
 simp [singletonSpec, shift, rename, lift, Nat.add_assoc]

theorem nd_shift {Γ : Context} {a : Formula} (h : ND (.seq Γ a)) :
 ND (.seq (shiftContext Γ) (shift a)) := h.rename Nat.succ

theorem nd_singleton_foundation_contra {Γ : Context}
 (hr : zfrRefl ∈ Γ) (he : zfrEqElem ∈ Γ) (hs : zfrSym ∈ Γ)
 (hf : zfrFoundation ∈ Γ) (i s : Nat)
 (hsg : ND (.seq Γ (singletonSpec i s))) (hii : ND (.seq Γ (.mem i i))) :
 ND (.seq Γ .bot) := by
 have his : ND (.seq Γ (.mem i s)) := ND.ie
   (ND.ce2 (nd_singleton_instance hsg i)) (ND.di1 (nd_refl_instance hr i))
 have hn : ND (.seq Γ (.ex (.mem 0 (s+1)))) := by
   simpa [subst, rename, substMap] using
     (ND.exI (a := .mem 0 (s+1)) i (by simpa [subst, rename, substMap] using his))
 have hm := ND.ie (nd_foundation_instance hf s) hn
 apply ND.exE hm
 let Δ := minimalSpec s :: shiftContext Γ
 have hr' : zfrRefl ∈ Δ := List.mem_cons_of_mem _ (shifted_member hr shift_zfrRefl)
 have he' : zfrEqElem ∈ Δ := List.mem_cons_of_mem _ (shifted_member he shift_zfrEqElem)
 have hs' : zfrSym ∈ Δ := List.mem_cons_of_mem _ (shifted_member hs shift_zfrSym)
 have hsg' : ND (.seq Δ (singletonSpec (i+1) (s+1))) := by
   have hh := nd_weaken_head (b := minimalSpec s) (nd_shift hsg)
   simpa only [shift_singletonSpec] using hh
 have hii' : ND (.seq Δ (.mem (i+1) (i+1))) := nd_weaken_head (nd_shift hii)
 have hm' : ND (.seq Δ (minimalSpec s)) := ND.ctx (by simp [Δ])
 have hyS : ND (.seq Δ (.mem 0 (s+1))) := ND.ce1 hm'
 have hyi : ND (.seq Δ (.eq 0 (i+1))) :=
   nd_or_self (ND.ie (ND.ce1 (nd_singleton_instance hsg' 0)) hyS)
 have hiy := ND.ie (nd_sym_instance hs' 0 (i+1)) hyi
 have hiY : ND (.seq Δ (.mem (i+1) 0)) :=
   ND.ie (ND.ie (nd_mem_container_eq hr' he' (i+1) (i+1) 0) hiy) hii'
 have hiS : ND (.seq Δ (.mem (i+1) (s+1))) :=
   ND.ie (ND.ce2 (nd_singleton_instance hsg' (i+1))) (ND.di1 (nd_refl_instance hr' (i+1)))
 have hmin : ND (.seq Δ (.imp (.mem (i+1) 0) (.imp (.mem (i+1) (s+1)) .bot))) := by
   have hh := ND.allE (i+1) (ND.ce2 hm')
   simpa [minimalSpec, subst, rename, lift, substMap, Nat.add_assoc] using hh
 exact ND.ie (ND.ie hmin hiY) hiS

theorem nd_irreflexivity {Γ : Context}
 (hr : zfrRefl ∈ Γ) (he : zfrEqElem ∈ Γ) (hs : zfrSym ∈ Γ)
 (hp : zfrPair ∈ Γ) (hf : zfrFoundation ∈ Γ) (i : Nat) :
 ND (.seq Γ (.imp (.mem i i) .bot)) := by
 apply ND.ii
 let Δ := .mem i i :: Γ
 have hpair : ND (.seq Δ (.ex (singletonSpec (i+1) 0))) :=
   nd_pair_singleton (List.mem_cons_of_mem _ hp) i
 apply ND.exE hpair
 let Θ := singletonSpec (i+1) 0 :: shiftContext Δ
 have hr' : zfrRefl ∈ Θ := List.mem_cons_of_mem _
   (shifted_member (List.mem_cons_of_mem _ hr) shift_zfrRefl)
 have he' : zfrEqElem ∈ Θ := List.mem_cons_of_mem _
   (shifted_member (List.mem_cons_of_mem _ he) shift_zfrEqElem)
 have hs' : zfrSym ∈ Θ := List.mem_cons_of_mem _
   (shifted_member (List.mem_cons_of_mem _ hs) shift_zfrSym)
 have hf' : zfrFoundation ∈ Θ := List.mem_cons_of_mem _
   (shifted_member (List.mem_cons_of_mem _ hf) shift_zfrFoundation)
 have hsg : ND (.seq Θ (singletonSpec (i+1) 0)) := ND.ctx (by simp [Θ])
 have hii : ND (.seq Θ (.mem (i+1) (i+1))) :=
   nd_weaken_head (nd_shift (ND.ctx (Γ := Δ) (a := .mem i i) (by simp [Δ])))
 exact nd_singleton_foundation_contra hr' he' hs' hf' (i+1) 0 hsg hii

end ZFR
