module
public import FoundationRewriteBridge
public import FoundationTheoryBridge
public import RankHullParameterSpecialization
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder

theorem agrees_fixitr (n : Nat) : RewAgrees (Rew.fixitr (L := Language.set) 0 n) id := by
 intro t
 cases t with
 | bvar i => exact Fin.elim0 i
 | fvar j =>
   rw [Rew.fixitr_fvar]
   split
   · simp [termIndex]
   · simp only [termIndex,id_eq,Nat.zero_add]
     omega
 | func f v => exact Empty.elim f

theorem toSource_fixitr (n : Nat) (p : Proposition Language.set) :
 toSource (Semiformula.rewAux (Rew.fixitr 0 n) p) = toSource p := by
 rw [toSource_rew p (Rew.fixitr 0 n) id (agrees_fixitr n),ZFR.rename_id]

theorem allPrefix_all (n : Nat) (p : ZFR.Formula) :
 allPrefix n (.all p) = allPrefix (n+1) p := by
 induction n with
 | zero => rfl
 | succ n ih => simp only [allPrefix,ih]

theorem toSource_allClosure {n : Nat} (p : Semiformula Language.set Nat n) :
 toSource (∀¹* p) = allPrefix n (toSource p) := by
 induction n with
 | zero => rfl
 | succ n ih =>
   rw [allClosure_succ,ih]
   exact allPrefix_all n (toSource p)

theorem toSource_univCl (p : Proposition Language.set) :
 toSource (p.univCl : Proposition Language.set) = allPrefix p.fvSup (toSource p) := by
 rw [Semiformula.coe_univCl_eq_univCl']
 unfold Semiformula.univCl'
 rw [toSource_allClosure]
 simp only [Nat.zero_add]
 change allPrefix p.fvSup (toSource (Semiformula.rewAux (Rew.fixitr 0 p.fvSup) p)) = _
 rw [toSource_fixitr]

theorem sourceTheorem_allPrefix (n : Nat) (p : ZFR.Formula) (h : SourceTheorem p) :
 SourceTheorem (allPrefix n p) := by
 obtain ⟨Γ,hΓ,hp⟩ := h
 have hc : ClosedContext Γ := by
   intro a ha
   exact (sourceBound_encode a 0).mp (sourceZfrAxiom_closed (hΓ a ha))
 refine ⟨Γ,hΓ,?_⟩
 induction n with
 | zero => exact hp
 | succ n ih =>
   apply ND.allI
   simpa only [shiftContext_closed hc] using ih

theorem foundation_source_univCl (p : Proposition Language.set)
 (h : SourceTheorem (toSource p)) :
 SourceTheorem (toSource (p.univCl : Proposition Language.set)) := by
 rw [toSource_univCl]
 exact sourceTheorem_allPrefix _ _ h

end ZFR.FoundationBridge
