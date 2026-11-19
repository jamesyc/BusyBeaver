module
public import FoundationExtensionalityBridge
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

def emptySpec (i : Nat) : ZFR.Formula := .all (.imp (.mem 0 (i+1)) .bot)
def successorSpec (i j : Nat) : ZFR.Formula := .all (.and
 (.imp (.mem 0 (i+1)) (.or (.mem 0 (j+1)) (.eq 0 (j+1))))
 (.imp (.or (.mem 0 (j+1)) (.eq 0 (j+1))) (.mem 0 (i+1))))

theorem shift_emptySpec (i : Nat) : shift (emptySpec i) = emptySpec (i+1) := by
 simp [shift,emptySpec,rename,lift,Nat.add_assoc]

theorem shift_successorSpec (i j : Nat) : shift (successorSpec i j) = successorSpec (i+1) (j+1) := by
 simp [shift,successorSpec,rename,lift,Nat.add_assoc]

theorem nd_all_fresh {Γ : Context} {p : ZFR.Formula} (h : ND (.seq Γ (.all p))) :
 ND (.seq (shiftContext Γ) p) := by
 have hs := h.rename Nat.succ
 have he := ND.allE 0 hs
 change ND (.seq (shiftContext Γ) (subst 0 (rename (lift Nat.succ) p))) at he
 simpa only [subst_lift_shift] using he

theorem nd_empty_equal {Γ : Context} (he : fixedExt ∈ Γ) (i j : Nat)
 (hi : ND (.seq Γ (emptySpec i))) (hj : ND (.seq Γ (emptySpec j))) : ND (.seq Γ (.eq i j)) := by
 apply ND.ie (ND.ie (nd_ext_instance he i j) ?_) ?_
 · apply ND.allI; apply ND.ii; apply ND.exp
   exact ND.ie (nd_all_fresh hi).weaken_cons (ND.ctx (by simp))
 · apply ND.allI; apply ND.ii; apply ND.exp
   exact ND.ie (nd_all_fresh hj).weaken_cons (ND.ctx (by simp))

theorem nd_successor_equal {Γ : Context} (he : fixedExt ∈ Γ) (i j k : Nat)
 (hi : ND (.seq Γ (successorSpec i k))) (hj : ND (.seq Γ (successorSpec j k))) :
 ND (.seq Γ (.eq i j)) := by
 apply ND.ie (ND.ie (nd_ext_instance he i j) ?_) ?_
 · apply ND.allI; apply ND.ii
   exact ND.ie (ND.ce2 (nd_all_fresh hj)).weaken_cons
     (ND.ie (ND.ce1 (nd_all_fresh hi)).weaken_cons (ND.ctx (by simp)))
 · apply ND.allI; apply ND.ii
   exact ND.ie (ND.ce2 (nd_all_fresh hi)).weaken_cons
     (ND.ie (ND.ce1 (nd_all_fresh hj)).weaken_cons (ND.ctx (by simp)))

theorem nd_transfer_member {Γ : Context} (ctx : EqualityContext Γ) (i j I : Nat)
 (hi : ND (.seq Γ (.mem i I))) (he : ND (.seq Γ (.eq i j))) : ND (.seq Γ (.mem j I)) :=
 ND.ie (ND.ie (nd_mem_element_eq ctx.refl ctx.elem i I j) hi) he

def existsEmptyMember (I : Nat) := ZFR.Formula.ex (.and (emptySpec 0) (.mem 0 (I+1)))
def allEmptyMember (I : Nat) := ZFR.Formula.all (.imp (emptySpec 0) (.mem 0 (I+1)))

theorem shift_existsEmptyMember (I : Nat) : shift (existsEmptyMember I) = existsEmptyMember (I+1) := by
 simp [shift,existsEmptyMember,emptySpec,rename,lift,Nat.add_assoc]

theorem nd_all_empty_members {Γ : Context} (ctx : EqualityContext Γ) (he : fixedExt ∈ Γ) (I : Nat)
 (h : ND (.seq Γ (existsEmptyMember I))) : ND (.seq Γ (allEmptyMember I)) := by
 apply ND.allI; apply ND.ii
 let Δ := emptySpec 0 :: shiftContext Γ
 have hc : EqualityContext Δ := ctx.shift.cons _
 have hex : fixedExt ∈ Δ := List.mem_cons_of_mem _ (shifted_member he fixedExt_shift)
 have hEx : ND (.seq Δ (existsEmptyMember (I+1))) := by
   have hs := h.rename Nat.succ
   change ND (.seq (shiftContext Γ) (shift (existsEmptyMember I))) at hs
   rw [shift_existsEmptyMember] at hs
   exact hs.weaken_cons
 apply ND.exE hEx
 let Θ := .and (emptySpec 0) (.mem 0 (I+2)) :: shiftContext Δ
 have hc' : EqualityContext Θ := hc.shift.cons _
 have hex' : fixedExt ∈ Θ := List.mem_cons_of_mem _ (shifted_member hex fixedExt_shift)
 have hw : ND (.seq Θ (.and (emptySpec 0) (.mem 0 (I+2)))) := ND.ctx (by simp [Θ])
 have hj : ND (.seq Θ (emptySpec 1)) := by
   apply ND.ctx
   simp [Θ,Δ,shiftContext,shift_emptySpec]
 have heq := nd_empty_equal hex' 0 1 (ND.ce1 hw) hj
 exact nd_transfer_member hc' 0 1 (I+2) (ND.ce2 hw) heq


def existsSuccessorMember (x I : Nat) := ZFR.Formula.ex (.and (successorSpec 0 (x+1)) (.mem 0 (I+1)))
def someSuccessors (I : Nat) := ZFR.Formula.all (.imp (.mem 0 (I+1)) (existsSuccessorMember 0 (I+1)))
def allSuccessors (I : Nat) := ZFR.Formula.all (.imp (.mem 0 (I+1))
 (.all (.imp (successorSpec 0 1) (.mem 0 (I+2)))))

theorem shift_existsSuccessorMember (x I : Nat) :
 shift (existsSuccessorMember x I) = existsSuccessorMember (x+1) (I+1) := by
 simp [shift,existsSuccessorMember,successorSpec,rename,lift,Nat.add_assoc]

theorem nd_all_successors {Γ : Context} (ctx : EqualityContext Γ) (he : fixedExt ∈ Γ) (I : Nat)
 (h : ND (.seq Γ (someSuccessors I))) : ND (.seq Γ (allSuccessors I)) := by
 apply ND.allI; apply ND.ii
 let Δ := .mem 0 (I+1) :: shiftContext Γ
 have hc : EqualityContext Δ := ctx.shift.cons _
 have hex : fixedExt ∈ Δ := List.mem_cons_of_mem _ (shifted_member he fixedExt_shift)
 have hEx : ND (.seq Δ (existsSuccessorMember 0 (I+1))) :=
   ND.ie (nd_all_fresh h).weaken_cons (ND.ctx (by simp [Δ]))
 apply ND.allI; apply ND.ii
 let Λ := successorSpec 0 1 :: shiftContext Δ
 have hc' : EqualityContext Λ := hc.shift.cons _
 have hex' : fixedExt ∈ Λ := List.mem_cons_of_mem _ (shifted_member hex fixedExt_shift)
 have hEx' : ND (.seq Λ (existsSuccessorMember 1 (I+2))) := by
   have hs := hEx.rename Nat.succ
   change ND (.seq (shiftContext Δ) (shift (existsSuccessorMember 0 (I+1)))) at hs
   rw [shift_existsSuccessorMember] at hs
   exact hs.weaken_cons
 apply ND.exE hEx'
 let Θ := .and (successorSpec 0 2) (.mem 0 (I+3)) :: shiftContext Λ
 have hc'' : EqualityContext Θ := hc'.shift.cons _
 have hex'' : fixedExt ∈ Θ := List.mem_cons_of_mem _ (shifted_member hex' fixedExt_shift)
 have hw : ND (.seq Θ (.and (successorSpec 0 2) (.mem 0 (I+3)))) := ND.ctx (by simp [Θ])
 have hj : ND (.seq Θ (successorSpec 1 2)) := by
   apply ND.ctx
   simp [Θ,Λ,shiftContext,shift_successorSpec]
 have heq := nd_successor_equal hex'' 0 1 2 (ND.ce1 hw) hj
 exact nd_transfer_member hc'' 0 1 (I+3) (ND.ce2 hw) heq

def normalInfinity : ZFR.Formula := .ex (.and (allEmptyMember 0) (allSuccessors 0))

theorem nd_normalInfinity {Γ : Context} (ctx : EqualityContext Γ)
 (he : fixedExt ∈ Γ) (hw : fixedOmega ∈ Γ) : ND (.seq Γ normalInfinity) := by
 apply ND.exE (ND.ctx hw)
 -- The leastness component of the source Omega axiom is unnecessary here.
 let B : ZFR.Formula := .and (existsEmptyMember 0) (someSuccessors 0)
 let C := match fixedOmega with | .ex p => p | _ => .bot
 let Δ := C :: shiftContext Γ
 have hc : EqualityContext Δ := ctx.shift.cons _
 have hex : fixedExt ∈ Δ := List.mem_cons_of_mem _ (shifted_member he fixedExt_shift)
 have hC : ND (.seq Δ C) := ND.ctx (by simp [Δ])
 have hb : ND (.seq Δ B) := ND.ce1 hC
 have ha := nd_all_empty_members hc hex 0 (ND.ce1 hb)
 have hs := nd_all_successors hc hex 0 (ND.ce2 hb)
 change ND (.seq Δ (shift normalInfinity))
 apply ND.exI 0
 -- Both target clauses are formulas about the new witness at index zero.
 have ht := ND.ci ha hs
 simpa [normalInfinity,shift,subst,allEmptyMember,allSuccessors,emptySpec,successorSpec,
   rename,lift,substMap] using ht


def bstInfinity : SetTheorySentence := “∃ I, (∀ e, !isEmpty e → e ∈ I) ∧
 (∀ x ∈ I, ∀ x', !isSucc x' x → x' ∈ I)”
def foundationSuccessor : Semiformula Language.set Nat 3 :=
 let P : Semiformula Language.set Nat 4 := .rel .mem ![.bvar 0,.bvar 1]
 let Q : Semiformula Language.set Nat 4 := .or (.rel .eq ![.bvar 0,.bvar 2]) (.rel .mem ![.bvar 0,.bvar 2])
 .all (.and (.or (Semiformula.neg P) Q) (.or (Semiformula.neg Q) P))

theorem or_comm_equiv (Γ : Context) (p q : ZFR.Formula) : NDEquiv Γ (.or p q) (.or q p) := by
 constructor
 · apply ND.ii; apply ND.de (a := p) (b := q) (ND.ctx (by simp)); apply ND.branchPair
   · exact ND.di2 (ND.ctx (by simp))
   · exact ND.di1 (ND.ctx (by simp))
 · apply ND.ii; apply ND.de (a := q) (b := p) (ND.ctx (by simp)); apply ND.branchPair
   · exact ND.di2 (ND.ctx (by simp))
   · exact ND.di1 (ND.ctx (by simp))

theorem foundation_successor_equiv (Γ : Context) :
 NDEquiv Γ (toSource foundationSuccessor) (successorSpec 0 1) := by
 apply NDEquiv.all
 apply (toSource_iff_equiv _
   (Semiformula.rel .mem ![.bvar 0,.bvar 1] : Semiformula Language.set Nat 4)
   (.or (.rel .eq ![.bvar 0,.bvar 2]) (.rel .mem ![.bvar 0,.bvar 2]))).trans
 have he := or_comm_equiv (shiftContext Γ) (.eq 0 2) (.mem 0 2)
 exact ((NDEquiv.refl _ _).imp he).and (he.imp (NDEquiv.refl _ _))

theorem infinity_equiv (Γ : Context) : NDEquiv Γ (axiomSource bstInfinity) normalInfinity := by
 apply NDEquiv.ex
 apply NDEquiv.and
 · apply NDEquiv.all
   exact toSource_arrow_equiv _
     (Semiformula.all (.nrel .mem ![.bvar 0,.bvar 1]) : Semiformula Language.set Nat 2)
     (.rel .mem ![.bvar 0,.bvar 1])
 · apply NDEquiv.all
   apply (toSource_arrow_equiv _
     (Semiformula.rel .mem ![.bvar 0,.bvar 1] : Semiformula Language.set Nat 2)
     (.all (.or (Semiformula.neg foundationSuccessor) (.rel .mem ![.bvar 0,.bvar 2])))).trans
   apply NDEquiv.imp (NDEquiv.refl _ _)
   apply NDEquiv.all
   apply (toSource_arrow_equiv _ foundationSuccessor (.rel .mem ![.bvar 0,.bvar 2])).trans
   exact (foundation_successor_equiv _).imp (NDEquiv.refl _ _)

def infinitySourceContext : Context := fixedOmega :: fixedExt :: equalitySourceContext

theorem source_bstInfinity : SourceTheorem (axiomSource bstInfinity) := by
 have hc : EqualityContext infinitySourceContext := equalitySourceContext_exact.cons _ |>.cons _
 have hp := nd_normalInfinity hc (by simp [infinitySourceContext]) (by simp [infinitySourceContext])
 refine ⟨infinitySourceContext,?_,ND.ie (infinity_equiv _).2 hp⟩
 intro p hp
 rcases List.mem_cons.mp hp with rfl | hp
 · exact Or.inl (by simp [sourceZfrFixed])
 · rcases List.mem_cons.mp hp with rfl | hp
   · exact Or.inl (by simp [sourceZfrFixed])
   · exact equalitySourceContext_in_zfr p hp

end ZFR.FoundationBridge
