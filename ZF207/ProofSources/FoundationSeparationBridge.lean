module
public import FoundationClosureBridge
public import FoundationAxiomBridge
public import RankHullFiniteParameters
public import Foundation.FirstOrder.SetTheory.Schemata
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

def sepOpen (p : SetTheorySemiproposition 1) : Proposition Language.set :=
 “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ !p z”

theorem agrees_sep : RewAgrees
 (Rew.subst (fun _ : Fin 1 => (Semiterm.bvar 0 : Semiterm Language.set Nat 3))) sepIndex := by
 intro t
 cases t with
 | bvar i => have hi : i=0 := Fin.eq_zero i; subst i; simp [termIndex,sepIndex]
 | fvar j => simp [termIndex,sepIndex]; omega
 | func f v => exact Empty.elim f

theorem toSource_sep_subst (p : SetTheorySemiproposition 1) :
 toSource (Rewriting.subst p ![(Semiterm.bvar 0 : Semiterm Language.set Nat 3)]) = rename sepIndex (toSource p) := by
 have hv : (![(Semiterm.bvar 0 : Semiterm Language.set Nat 3)] : Fin 1 → Semiterm Language.set Nat 3) = (fun _ => .bvar 0) := by
   funext i; have hi : i=0 := Fin.eq_zero i; subst i; rfl
 change toSource (Semiformula.rewAux (Rew.subst ![(Semiterm.bvar 0 : Semiterm Language.set Nat 3)]) p) = _
 rw [hv]
 exact toSource_rew p _ sepIndex agrees_sep

theorem sepOpen_equiv (p : SetTheorySemiproposition 1) (Γ : Context) :
 NDEquiv Γ (toSource (sepOpen p)) (separationFormula (rename sepIndex (toSource p))) := by
 apply NDEquiv.all
 apply NDEquiv.ex
 apply NDEquiv.all
 have hh := toSource_iff_equiv (shiftContext (shiftContext (shiftContext Γ)))
   (.rel .mem ![.bvar 0,.bvar 1] : Semiformula Language.set Nat 3)
   (.and (.rel .mem ![.bvar 0,.bvar 2]) (Rewriting.subst p ![(Semiterm.bvar 0 : Semiterm Language.set Nat 3)]))
 convert hh using 1 <;> simp [toSource,atom,termIndex,toSource_sep_subst,sourceIff]
 all_goals exact ⟨⟨rfl,rfl⟩,rfl,rfl⟩

theorem source_sepOpen (p : SetTheorySemiproposition 1) : SourceTheorem (toSource (sepOpen p)) := by
 let phi := toSource p
 let n := parameterBound phi
 have hb : Bound phi (n+1) := (parameterBound_valid phi).mono (by omega)
 let Γ := [separationSchema n phi]
 have hs : sourceZfrAxiom (encodeFormula (separationSchema n phi)) := separationSchema_in_zfr n phi hb
 refine ⟨Γ,?_,?_⟩
 · intro a ha
   have he : a = separationSchema n phi := by simpa [Γ] using ha
   subst a; exact hs
 · exact ND.ie (sepOpen_equiv p Γ).2 (nd_separation_declose n phi hb (by simp [Γ]))

theorem source_separation_axiom (p : SetTheorySemiproposition 1) :
 SourceTheorem (axiomSource (Axiom.separationSchema p)) :=
 foundation_source_univCl (sepOpen p) (source_sepOpen p)

end ZFR.FoundationBridge
