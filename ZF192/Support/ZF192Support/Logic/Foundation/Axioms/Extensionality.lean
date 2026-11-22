module
public import ZF192Support.Logic.Foundation.Axioms.Equality
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

def bstExtensionality : SetTheorySentence := “∀ x y, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y”
def extBidirBody : ZFR.Formula := .and (.imp (.mem 0 2) (.mem 0 1)) (.imp (.mem 0 1) (.mem 0 2))
def extNormal : ZFR.Formula := .all (.all (.and
 (.imp (.eq 1 0) (.all extBidirBody)) (.imp (.all extBidirBody) (.eq 1 0))))

theorem extensionality_equiv (Γ : Context) :
 NDEquiv Γ (axiomSource bstExtensionality) extNormal := by
 apply NDEquiv.all; apply NDEquiv.all
 let P : Semiformula Language.set Nat 2 := .rel .eq ![.bvar 1,.bvar 0]
 let Q : Semiformula Language.set Nat 2 := .all (.and
   (.or (.nrel .mem ![.bvar 0,.bvar 2]) (.rel .mem ![.bvar 0,.bvar 1]))
   (.or (.nrel .mem ![.bvar 0,.bvar 1]) (.rel .mem ![.bvar 0,.bvar 2])))
 apply (toSource_iff_equiv _ P Q).trans
 have hq : NDEquiv (shiftContext (shiftContext Γ)) (toSource Q) (.all extBidirBody) := by
   apply NDEquiv.all
   exact toSource_iff_equiv _
     (Semiformula.rel .mem ![.bvar 0,.bvar 2] : Semiformula Language.set Nat 3)
     (.rel .mem ![.bvar 0,.bvar 1])
 exact ((NDEquiv.refl _ (toSource P)).imp hq).and (hq.imp (NDEquiv.refl _ (toSource P)))

theorem fixedExt_shift : shift fixedExt = fixedExt := rfl

theorem nd_ext_instance {Γ : Context} (he : fixedExt ∈ Γ) (i j : Nat) :
 ND (.seq Γ (.imp (.all (.imp (.mem 0 (i+1)) (.mem 0 (j+1))))
   (.imp (.all (.imp (.mem 0 (j+1)) (.mem 0 (i+1)))) (.eq i j)))) := by
 have h := ND.allE j (ND.allE i (ND.ctx he))
 simpa [fixedExt,subst,rename,lift,substMap] using h

theorem nd_ext_normal {Γ : Context} (ctx : EqualityContext Γ) (he : fixedExt ∈ Γ) :
 ND (.seq Γ extNormal) := by
 apply ND.allI; apply ND.allI
 apply ND.ci
 · apply ND.ii
   apply ND.allI
   let Δ := shiftContext (.eq 1 0 :: shiftContext (shiftContext Γ))
   have hc : EqualityContext Δ := (ctx.shift.shift.cons (.eq 1 0)).shift
   have h10 : ND (.seq Δ (.eq 2 1)) := ND.ctx (by simp [Δ,shiftContext,shift,rename])
   apply ND.ci
   · exact ND.ie (nd_mem_container_eq hc.refl hc.elem 0 2 1) h10
   · exact ND.ie (nd_mem_container_eq hc.refl hc.elem 0 1 2) (eq_symm hc h10)
 · apply ND.ii
   let Δ := .all extBidirBody :: shiftContext (shiftContext Γ)
   have hex : fixedExt ∈ Δ := List.mem_cons_of_mem _
     (shifted_member (shifted_member he fixedExt_shift) fixedExt_shift)
   have hfull : ND (.seq Δ (.all extBidirBody)) := ND.ctx (by simp [Δ])
   have hl : ND (.seq Δ (.all (.imp (.mem 0 2) (.mem 0 1)))) := by
     apply ND.ie (nd_all_monotone (p := extBidirBody) _ ) hfull
     exact ND.ii (ND.ce1 (b := .imp (.mem 0 1) (.mem 0 2)) (ND.ctx (by simp [extBidirBody])))
   have hr : ND (.seq Δ (.all (.imp (.mem 0 1) (.mem 0 2)))) := by
     apply ND.ie (nd_all_monotone (p := extBidirBody) _ ) hfull
     exact ND.ii (ND.ce2 (a := .imp (.mem 0 2) (.mem 0 1)) (ND.ctx (by simp [extBidirBody])))
   exact ND.ie (ND.ie (nd_ext_instance hex 1 0) hl) hr

def extensionalitySourceContext : Context := fixedExt :: equalitySourceContext

theorem source_bstExtensionality : SourceTheorem (axiomSource bstExtensionality) := by
 have hc : EqualityContext extensionalitySourceContext := equalitySourceContext_exact.cons _
 have hp := nd_ext_normal hc (by simp [extensionalitySourceContext])
 refine ⟨extensionalitySourceContext,?_,ND.ie (extensionality_equiv _).2 hp⟩
 intro p hp
 rcases List.mem_cons.mp hp with rfl | hp
 · exact Or.inl (by simp [SourceFixedAxiom, PalomarZF192Theory.FixedAxiom])
 · exact equalitySourceContext_in_zfr p hp

end ZFR.FoundationBridge
