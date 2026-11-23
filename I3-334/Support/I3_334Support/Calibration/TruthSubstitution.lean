module
public import I3_334Support.Calibration.TruthShift
public import I3_334Support.Calibration.GraphSubstitution
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open Logic.Expanded
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} {E G : V → V → Prop} {L : ClassAxioms E G} {inhabited : Nonempty V}
variable (D : OmegaDomain L inhabited) {P : Presentation D} (T : TruthTable D P)

theorem tableRelation_substitute {k r ts w n b f a : D.Points}
    (terms : IsSemitermVec GraphLanguage k n ts) (size : len w=n)
    (values : Values a w ⟪b,f⟫ P.fallback) :
    TableRelation D P k r (termSubstVec GraphLanguage k w ts) ⟪b,f⟫ ↔
      TableRelation D P k r ts ⟪a,f⟫ := by
  apply exists_congr
  intro vals
  exact and_congr_left (fun _ => Values.substitute terms size values)

theorem TruthTable.holds_subst {p w n m b f a : D.Points}
    (typed : IsSemiformula GraphLanguage n p)
    (args : IsSemitermVec GraphLanguage n m w)
    (values : Values a w ⟪b,f⟫ P.fallback) :
    T.holds D (subst GraphLanguage w p) ⟪b,f⟫ ↔ T.holds D p ⟪a,f⟫ := by
  have go := T.transport_induction D substGuard.val (fun p ih => by
    intro q original modified agrees
    obtain ⟨n,m,w,a,b,f,checked,args,rfl,rfl,rfl,values⟩ :=
      (substGuard_eval p q original modified P.fallback).mp agrees
    have recurse (r : D.Points) (before : r<p) {k l w' a' b' : D.Points}
        (wellFormed : IsSemiformula GraphLanguage k r) (arguments : IsSemitermVec GraphLanguage k l w')
        (assigned : Values a' w' ⟪b',f⟫ P.fallback) :
        T.holds D r ⟪a',f⟫ ↔ T.holds D (subst GraphLanguage w' r) ⟪b',f⟫ :=
      ih r before _ _ _ ((substGuard_eval ..).mpr ⟨k,l,w',a',b',f,wellFormed,arguments,rfl,rfl,rfl,assigned⟩)
    rcases IsSemiformula.case_iff.mp checked with
      ⟨k,r,ts,symbol,terms,rfl⟩ | ⟨k,r,ts,symbol,terms,rfl⟩ | rfl | rfl |
      ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
    · rw [substs_rel symbol terms.isUTerm,T.holds_rel,T.holds_rel,tableRelation_substitute D terms args.lh values]
    · rw [substs_nrel symbol terms.isUTerm,T.holds_nrel,T.holds_nrel,tableRelation_substitute D terms args.lh values]
    · exact ⟨fun _ => by rw [substs_verum]; exact T.holds_true D _,fun _ => T.holds_true D _⟩
    · rw [substs_falsum]
      exact ⟨fun h => (T.holds_false D _ h).elim,fun h => (T.holds_false D _ h).elim⟩
    · rw [substs_and hp.isUFormula hq.isUFormula,T.holds_and,T.holds_and]
      exact and_congr (recurse p (by simp) hp args values) (recurse q (by simp) hq args values)
    · rw [substs_or hp.isUFormula hq.isUFormula,T.holds_or,T.holds_or]
      exact or_congr (recurse p (by simp) hp args values) (recurse q (by simp) hq args values)
    · rw [substs_all hp.isUFormula,T.holds_all,T.holds_all]
      exact forall_congr' (fun x => by
        simpa only [pushBound,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair] using
          recurse p (by simp) hp args.qVec (values.qVec args x.val))
    · rw [substs_ex hp.isUFormula,T.holds_exs,T.holds_exs]
      exact exists_congr (fun x => by
        simpa only [pushBound,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair] using
          recurse p (by simp) hp args.qVec (values.qVec args x.val)))
  exact (go p _ _ _ ((substGuard_eval ..).mpr ⟨n,m,w,a,b,f,typed,args,rfl,rfl,rfl,values⟩)).symm

theorem TruthTable.holds_substs1 {p term : D.Points} (typed : IsSemiformula GraphLanguage 1 p)
    (closed : IsTerm GraphLanguage term) (f : D.Points) :
    T.holds D (substs1 GraphLanguage term p) ⟪0,f⟫ ↔
      T.holds D p ⟪?[variableValue term ⟪0,f⟫ P.fallback],f⟫ := by
  have arguments : IsSemitermVec GraphLanguage 1 0 (?[term] : D.Points) := by simp [closed]
  have read :
      Values (?[variableValue term ⟪0,f⟫ P.fallback]) (?[term]) ⟪0,f⟫ P.fallback := by
    refine ⟨by simp,fun i fit => ?_⟩
    have zero : i=0 := lt_one_iff_eq_zero.mp (by simpa using fit)
    simp only [zero,nth_adjoin_zero]
  exact T.holds_subst D typed arguments read

theorem TruthTable.holds_free {p : D.Points} (typed : IsSemiformula GraphLanguage 1 p)
    (f x : D.Points) :
    T.holds D (free GraphLanguage p) ⟪0,x ∷ f⟫ ↔ T.holds D p ⟪?[x],f⟫ := by
  unfold free
  have closed : IsTerm GraphLanguage (^&0 : D.Points) := by simp
  rw [T.holds_substs1 D typed.shift closed,variableValue_free,lookup_zero]
  exact T.holds_shift D p typed.isUFormula _ _ _

end PalomarI3380.Calibration.CodedGraph
