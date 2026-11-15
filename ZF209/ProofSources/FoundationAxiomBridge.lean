module
public import FoundationNegationBridge
public import ProofTranslation
public import Foundation.FirstOrder.SetTheory.BST.Basic
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

def bstEmpty : SetTheorySentence := “∃ e, !isEmpty e”
def bstPair : SetTheorySentence := “∀ x y, ∃ z, ∀ w, w ∈ z ↔ w = x ∨ w = y”
def bstUnion : SetTheorySentence := “∀ x, ∃ y, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w”
def bstPower : SetTheorySentence := “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x”
def bstFoundation : SetTheorySentence := “∀ x, !isNonempty x → ∃ y ∈ x, ∀ z ∈ x, z ∉ y”

def axiomSource (p : SetTheorySentence) : ZFR.Formula := toSource (p : Proposition Language.set)

theorem empty_exact : axiomSource bstEmpty = fixedEmpty := rfl

theorem fixed_source_theorem (p : ZFR.Formula) (hp : sourceZfrFixed (encodeFormula p)) : SourceTheorem p := by
 refine ⟨[p],?_,ND.ctx (by simp)⟩
 intro a ha
 have ha' : a = p := by simpa using ha
 subst a
 exact Or.inl hp

theorem source_bstEmpty : SourceTheorem (axiomSource bstEmpty) := by
 rw [empty_exact]
 exact fixed_source_theorem fixedEmpty (by simp [sourceZfrFixed])

theorem toSource_iff_equiv (Γ : Context) {n : Nat}
 (p q : Semiformula Language.set Nat n) :
 NDEquiv Γ (toSource (.and (.or (Semiformula.neg p) q) (.or (Semiformula.neg q) p)))
 (.and (.imp (toSource p) (toSource q)) (.imp (toSource q) (toSource p))) :=
 (toSource_arrow_equiv Γ p q).and (toSource_arrow_equiv Γ q p)

theorem pair_equiv (Γ : Context) : NDEquiv Γ (axiomSource bstPair) fixedPair := by
 apply NDEquiv.all
 apply NDEquiv.all
 apply NDEquiv.ex
 apply NDEquiv.all
 exact toSource_iff_equiv _
   (Semiformula.rel .mem ![.bvar 0,.bvar 1] : Semiformula Language.set Nat 4)
   (.or (.rel .eq ![.bvar 0,.bvar 3]) (.rel .eq ![.bvar 0,.bvar 2]))


theorem union_equiv (Γ : Context) : NDEquiv Γ (axiomSource bstUnion) fixedUnion := by
 apply NDEquiv.all
 apply NDEquiv.ex
 apply NDEquiv.all
 exact toSource_iff_equiv _
   (Semiformula.rel .mem ![.bvar 0,.bvar 1] : Semiformula Language.set Nat 3)
   (.exs (.and (.rel .mem ![.bvar 0,.bvar 3]) (.rel .mem ![.bvar 1,.bvar 0])))

theorem power_equiv (Γ : Context) : NDEquiv Γ (axiomSource bstPower) fixedPower := by
 apply NDEquiv.all
 apply NDEquiv.ex
 apply NDEquiv.all
 let P : Semiformula Language.set Nat 3 := .rel .mem ![.bvar 0,.bvar 1]
 let Q : Semiformula Language.set Nat 3 :=
   .all (.or (.nrel .mem ![.bvar 0,.bvar 1]) (.rel .mem ![.bvar 0,.bvar 3]))
 apply (toSource_iff_equiv _ P Q).trans
 have hq : NDEquiv (shiftContext (shiftContext (shiftContext Γ))) (toSource Q)
   (.all (.imp (.mem 0 1) (.mem 0 3))) := by
   apply NDEquiv.all
   exact toSource_arrow_equiv _
     (Semiformula.rel .mem ![.bvar 0,.bvar 1] : Semiformula Language.set Nat 4)
     (.rel .mem ![.bvar 0,.bvar 3])
 exact ((NDEquiv.refl _ (toSource P)).imp hq).and (hq.imp (NDEquiv.refl _ (toSource P)))

theorem exchange_imp_equiv (Γ : Context) (p q r : ZFR.Formula) :
 NDEquiv Γ (.imp p (.imp q r)) (.imp q (.imp p r)) := by
 constructor
 all_goals
   apply ND.ii; apply ND.ii; apply ND.ii
 · exact ND.ie (a := q) (ND.ie (a := p) (ND.ctx (by simp)) (ND.ctx (by simp))) (ND.ctx (by simp))
 · exact ND.ie (a := p) (ND.ie (a := q) (ND.ctx (by simp)) (ND.ctx (by simp))) (ND.ctx (by simp))

theorem foundation_equiv (Γ : Context) : NDEquiv Γ (axiomSource bstFoundation) fixedFoundation := by
 apply NDEquiv.all
 let P : Semiformula Language.set Nat 1 := .exs (.rel .mem ![.bvar 0,.bvar 1])
 let Q : Semiformula Language.set Nat 1 := .exs (.and (.rel .mem ![.bvar 0,.bvar 1])
   (.all (.or (.nrel .mem ![.bvar 0,.bvar 2]) (.nrel .mem ![.bvar 0,.bvar 1]))))
 apply (toSource_arrow_equiv _ P Q).trans
 apply NDEquiv.imp (NDEquiv.refl _ _)
 apply NDEquiv.ex
 apply NDEquiv.and (NDEquiv.refl _ _)
 apply NDEquiv.all
 exact (toSource_arrow_equiv _
   (Semiformula.rel .mem ![.bvar 0,.bvar 2] : Semiformula Language.set Nat 3)
   (.nrel .mem ![.bvar 0,.bvar 1])).trans (exchange_imp_equiv _ _ _ _)

theorem source_theorem_of_equiv (p q : ZFR.Formula) (hp : SourceTheorem p)
 (he : ∀ Γ, NDEquiv Γ p q) : SourceTheorem q := by
 obtain ⟨Γ,hΓ,hp⟩ := hp
 exact ⟨Γ,hΓ,ND.ie (he Γ).1 hp⟩

theorem source_bstPair : SourceTheorem (axiomSource bstPair) :=
 source_theorem_of_equiv fixedPair _ (fixed_source_theorem _ (by simp [sourceZfrFixed]))
   (fun Γ => (pair_equiv Γ).symm)

theorem source_bstUnion : SourceTheorem (axiomSource bstUnion) :=
 source_theorem_of_equiv fixedUnion _ (fixed_source_theorem _ (by simp [sourceZfrFixed]))
   (fun Γ => (union_equiv Γ).symm)

theorem source_bstPower : SourceTheorem (axiomSource bstPower) :=
 source_theorem_of_equiv fixedPower _ (fixed_source_theorem _ (by simp [sourceZfrFixed]))
   (fun Γ => (power_equiv Γ).symm)

theorem source_bstFoundation : SourceTheorem (axiomSource bstFoundation) :=
 source_theorem_of_equiv fixedFoundation _ (fixed_source_theorem _ (by simp [sourceZfrFixed]))
   (fun Γ => (foundation_equiv Γ).symm)

end ZFR.FoundationBridge
