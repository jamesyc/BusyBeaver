module
public import I3_334Support.Calibration.TruthTransport
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open Logic.Expanded
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

noncomputable def shiftGuard : 𝚺ᴬ₁.Semisentence 5 :=
  .mkSigma “p q original shifted fallback. !(isUFormula GraphLanguage).sigma p ∧
    !(shiftGraph GraphLanguage) q p ∧
    ∃ b f next, !pairDef original b f ∧ !pairDef shifted b next ∧
      ((∃ x, !adjoinDef next x f) ∨ (f=0 ∧ next=0))”

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def FreeAdvance (before after : M) : Prop :=
  (∃ x, after=x ∷ before) ∨ (before=0 ∧ after=0)

theorem FreeAdvance.lookup {a b : M} (read : FreeAdvance a b) (i fallback : M) :
    lookup b (i+1) fallback = lookup a i fallback := by
  rcases read with ⟨x,rfl⟩ | ⟨rfl,rfl⟩
  · exact lookup_succ ..
  · simp [CodedGraph.lookup]

theorem shiftGuard_eval (p q a b default : M) :
    shiftGuard.val.Evalb ![p,q,a,b,default] ↔
      IsUFormula GraphLanguage p ∧ q=shift GraphLanguage p ∧
        ∃ bound free next, a=⟪bound,free⟫ ∧ b=⟪bound,next⟫ ∧ FreeAdvance free next := by
  have valid : (isUFormula GraphLanguage).sigma.val.Evalb ![p] ↔ IsUFormula GraphLanguage p := by
    rw [Bounding.HierarchySymbol.Semiformula.val_sigma]
    exact IsUFormula.defined.iff
  have renamed : (shiftGraph GraphLanguage).val.Evalb ![q,p] ↔ q=shift GraphLanguage p :=
    shift.defined.iff
  simp [shiftGuard,valid,renamed,adjoin_defined.iff,pair_defined.iff,FreeAdvance]

theorem variableValue_shift {t : M} (typed : IsUTerm GraphLanguage t) (b f x fallback : M)
    (advance : FreeAdvance f x) :
    variableValue (termShift GraphLanguage t) ⟪b,x⟫ fallback =
      variableValue t ⟪b,f⟫ fallback := by
  rcases IsUTerm.case_iff.mp typed with ⟨n,rfl⟩ | ⟨n,rfl⟩ | ⟨_,_,_,invalid,_,_⟩
  · simp
  · simp [advance.lookup]
  · exact (graphLanguage_no_function invalid).elim

theorem Values.shift {k ts : M} (typed : IsUTermVec GraphLanguage k ts) (b f x fallback vals : M)
    (advance : FreeAdvance f x) :
    Values vals (termShiftVec GraphLanguage k ts) ⟪b,x⟫ fallback ↔
      Values vals ts ⟪b,f⟫ fallback := by
  have length : len (termShiftVec GraphLanguage k ts) = len ts :=
    (len_termShiftVec typed).trans typed.lh
  unfold Values
  rw [length]
  refine and_congr_right (fun _ => forall_congr' fun i => imp_congr_right fun inside => ?_)
  have hi : i<k := typed.lh.symm ▸ inside
  rw [nth_termShiftVec typed hi,variableValue_shift (typed.nth hi) _ _ _ _ advance]

variable {V : Type} {E G : V → V → Prop} {L : ClassAxioms E G} {inhabited : Nonempty V}
variable (D : OmegaDomain L inhabited) {P : Presentation D} (T : TruthTable D P)

theorem tableRelation_shift {k r ts : D.Points} (typed : IsUTermVec GraphLanguage k ts)
    (b f x : D.Points) (advance : FreeAdvance f x) :
    TableRelation D P k r (termShiftVec GraphLanguage k ts) ⟪b,x⟫ ↔
      TableRelation D P k r ts ⟪b,f⟫ := by
  apply exists_congr
  intro vals
  exact and_congr_left (fun _ => Values.shift typed _ _ _ _ _ advance)

theorem TruthTable.holds_shift_of_advance (p : D.Points) (typed : IsUFormula GraphLanguage p)
    (b f x : D.Points) (advance : FreeAdvance f x) :
    T.holds D (shift GraphLanguage p) ⟪b,x⟫ ↔ T.holds D p ⟪b,f⟫ := by
  have go := T.transport_induction D shiftGuard.val (fun p ih => by
    intro q original modified agrees
    obtain ⟨wellFormed,rfl,b,f,x,rfl,rfl,advance⟩ := (shiftGuard_eval p q original modified P.fallback).mp agrees
    have recurse (a : D.Points) (bound : a<p) (valid : IsUFormula GraphLanguage a) (z : D.Points) :
        T.holds D a ⟪z,f⟫ ↔ T.holds D (shift GraphLanguage a) ⟪z,x⟫ :=
      ih a bound _ _ _ ((shiftGuard_eval ..).mpr ⟨valid,rfl,z,f,x,rfl,rfl,advance⟩)
    rcases wellFormed.case with ⟨k,r,ts,symbol,terms,rfl⟩ | ⟨k,r,ts,symbol,terms,rfl⟩ |
      rfl | rfl | ⟨a,c,ha,hc,rfl⟩ | ⟨a,c,ha,hc,rfl⟩ | ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
    · rw [shift_rel symbol terms,T.holds_rel,T.holds_rel,tableRelation_shift D terms _ _ _ advance]
    · rw [shift_nrel symbol terms,T.holds_nrel,T.holds_nrel,tableRelation_shift D terms _ _ _ advance]
    · exact ⟨fun _ => by rw [shift_verum]; exact T.holds_true D _,fun _ => T.holds_true D _⟩
    · rw [shift_falsum]
      exact ⟨fun h => (T.holds_false D _ h).elim,fun h => (T.holds_false D _ h).elim⟩
    · rw [shift_and ha hc,T.holds_and,T.holds_and]
      exact and_congr (recurse a (by simp) ha _) (recurse c (by simp) hc _)
    · rw [shift_or ha hc,T.holds_or,T.holds_or]
      exact or_congr (recurse a (by simp) ha _) (recurse c (by simp) hc _)
    · rw [shift_all ha,T.holds_all,T.holds_all]
      exact forall_congr' fun z => by simpa [pushBound] using recurse a (by simp) ha (z.val ∷ b)
    · rw [shift_exs ha,T.holds_exs,T.holds_exs]
      exact exists_congr fun z => by simpa [pushBound] using recurse a (by simp) ha (z.val ∷ b))
  exact (go p _ _ _ ((shiftGuard_eval ..).mpr ⟨typed,rfl,b,f,x,rfl,rfl,advance⟩)).symm

theorem TruthTable.holds_shift (p : D.Points) (typed : IsUFormula GraphLanguage p)
    (b f x : D.Points) :
    T.holds D (shift GraphLanguage p) ⟪b,x ∷ f⟫ ↔ T.holds D p ⟪b,f⟫ :=
  T.holds_shift_of_advance D p typed b f (x ∷ f) (Or.inl ⟨x,rfl⟩)

end PalomarI3380.Calibration.CodedGraph
