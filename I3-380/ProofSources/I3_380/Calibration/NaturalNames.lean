module
public import I3_380.Calibration.ArithmeticTemplates
public import I3_380.Logic.SetScope
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder
open Logic (SetFormula)
open Logic.Expanded (ClassAxioms OmegaDomain)

variable {A : Type} [Tarski.Structure FilterLanguage A] [Tarski.Structure.Eq FilterLanguage A]
variable (C : FilterModel A)
variable {laws : ClassAxioms C.mem (fun _ _ => False)} {inhabited : Nonempty C.Domain}
variable (D : OmegaDomain laws inhabited)

theorem representative_injective : Function.Injective (fun r : C.Representative => r.val.val) :=
  fun _ _ same => Subtype.ext (Subtype.ext same)

def NamedNatural (x : A) : Prop :=
  ∃ r : C.Representative, r.val.val = x ∧ C.mem (C.asPoint r) D.omega

def Denotes (x : A) (number : D.Points) : Prop :=
  (∃ r : C.Representative, r.val.val = x ∧ C.asPoint r = number.val) ∨
  (¬NamedNatural C D x ∧ number = 0)

theorem denotes_unique (x : A) : ∃! number : D.Points, Denotes C D x number := by
  classical
  by_cases named : NamedNatural C D x
  · obtain ⟨r,raw,natural⟩ := named
    let number : D.Points := ⟨C.asPoint r,natural⟩
    refine ⟨number,Or.inl ⟨r,raw,rfl⟩,?_⟩
    intro other h
    rcases h with ⟨q,qx,point⟩ | ⟨bad,_⟩
    · have same := representative_injective C (qx.trans raw.symm)
      exact Subtype.ext (point.symm.trans (congrArg C.asPoint same))
    · exact (bad ⟨r,raw,natural⟩).elim
  · refine ⟨0,Or.inr ⟨named,rfl⟩,?_⟩
    intro other h
    rcases h with ⟨q,qx,point⟩ | ⟨_,eq⟩
    · exact (named ⟨q,qx,point.symm ▸ other.property⟩).elim
    · exact eq

noncomputable def readValue (x : A) : D.Points := Classical.choose (denotes_unique C D x)

theorem readValue_of_representative (r : C.Representative) (natural : C.mem (C.asPoint r) D.omega) :
    (readValue C D r.val.val).val = C.asPoint r := by
  have same : (⟨C.asPoint r,natural⟩ : D.Points) = readValue C D r.val.val :=
    (Classical.choose_spec (denotes_unique C D r.val.val)).2 _ (Or.inl ⟨r,rfl,rfl⟩)
  exact congrArg Subtype.val same.symm

theorem readValue_of_default {x : A} (unknown : ¬NamedNatural C D x) : readValue C D x = 0 :=
  ((Classical.choose_spec (denotes_unique C D x)).2 _ (Or.inr ⟨unknown,rfl⟩)).symm

theorem readValue_surjective : Function.Surjective (readValue C D) := by
  intro n
  obtain ⟨r,represents⟩ := C.asPoint_onto n.val
  have natural : C.mem (C.asPoint r) D.omega := represents.symm ▸ n.property
  exact ⟨r.val.val,Subtype.ext ((readValue_of_representative C D r natural).trans represents)⟩

theorem naturalName_eval (x : A) (default : C.Representative) :
    naturalName.Evalb ![x] ↔ NamedNatural C D x := by
  have bound := SetFormula.scope_natObject (d := 1) (a := 0) (by decide)
  rw [naturalName,namedSetFormula_eval C _ bound _ default]
  constructor
  · rintro ⟨v,same,truth⟩
    have natural := (SetFormula.holds_natObject (a := 0) (by decide : 0 < 1)).mp truth
    have inside := ((laws.context inhabited).natObject_iff D.specification _).mp natural
    change C.mem (pointLevels C v default 0) D.omega at inside
    exact ⟨v 0,same 0,by simpa [pointLevels] using inside⟩
  · rintro ⟨r,same,natural⟩
    refine ⟨![r],fun i => ?_,?_⟩
    · have equal : i = 0 := Subsingleton.elim _ _
      simpa [equal] using same
    · apply (SetFormula.holds_natObject (a := 0) (by decide : 0 < 1)).mpr
      apply ((laws.context inhabited).natObject_iff D.specification _).mpr
      change C.mem (pointLevels C ![r] default 0) D.omega
      simpa [pointLevels] using natural

theorem numeralName_eval (n : Nat) (x : A) (default : C.Representative) :
    (numeralName n).Evalb ![x] ↔
      ∃ r : C.Representative, r.val.val = x ∧ C.asPoint r = (D.numeral n).val := by
  have bound := SetFormula.scope_numeral n (d := 1) (a := 0) (by decide)
  rw [numeralName,namedSetFormula_eval C _ bound _ default]
  constructor
  · rintro ⟨v,same,truth⟩
    have hasValue := (SetFormula.holds_numeral n (a := 0) (by decide : 0 < 1)).mp truth
    have equal := ((laws.context inhabited).numeral_def n _).mp hasValue
    exact ⟨v 0,same 0,by simpa [pointLevels,OmegaDomain.numeral] using equal⟩
  · rintro ⟨r,same,hasValue⟩
    refine ⟨![r],fun i => ?_,?_⟩
    · have equal : i = 0 := Subsingleton.elim _ _
      simpa [equal] using same
    · apply (SetFormula.holds_numeral n (a := 0) (by decide : 0 < 1)).mpr
      apply ((laws.context inhabited).numeral_def n _).mpr
      simpa [pointLevels,OmegaDomain.numeral] using hasValue

theorem sameName_eval (x y : A) (default : C.Representative) :
    sameName.Evalb ![x,y] ↔
      ∃ r q : C.Representative, r.val.val = x ∧ q.val.val = y ∧ C.asPoint r = C.asPoint q := by
  rw [sameName,namedMembership_eval C (show Logic.Bound (.eq 0 1) 2 from ⟨by decide,by decide⟩) _ default]
  constructor
  · rintro ⟨v,same,equal⟩
    exact ⟨v 0,v 1,same 0,same 1,by simpa [Logic.eval] using equal⟩
  · rintro ⟨r,q,rx,qy,equal⟩
    refine ⟨![r,q],?_ ,?_⟩
    · intro i
      refine Fin.cases rx (fun j => ?_) i
      have only : j=0 := Subsingleton.elim _ _
      subst j
      exact qy
    · simpa [Logic.eval] using equal

theorem readsName_eval (x y : A) (default : C.Representative) :
    readsName.Evalb ![x,y] ↔
      ∃ q : C.Representative, q.val.val = y ∧ C.asPoint q = (readValue C D x).val := by
  have first (p : Semisentence FilterLanguage 1) :
      (p ⇜ ![.bvar 0]).Evalb ![x,y] ↔ p.Evalb ![x] := by
    simp [Semiformula.eval_substs,Semiterm.val,Function.comp_def,Matrix.constant_eq_singleton]
  have second (p : Semisentence FilterLanguage 1) :
      (p ⇜ ![.bvar 1]).Evalb ![x,y] ↔ p.Evalb ![y] := by
    simp [Semiformula.eval_substs,Semiterm.val,Function.comp_def,Matrix.constant_eq_singleton]
  simp only [readsName,LogicalConnective.HomClass.map_and,LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg,first,second,naturalName_eval C D _ default,
    sameName_eval C _ _ default,numeralName_eval C D _ _ default]
  constructor
  · rintro ⟨⟨q,qy,hq⟩,⟨⟨r,rx,hr⟩,a,b,ax,by',eq⟩ | ⟨fallback,b,by',zero⟩⟩
    · have sameA : a = r := representative_injective C (ax.trans rx.symm)
      have sameB : b = q := representative_injective C (by'.trans qy.symm)
      rw [sameA,sameB] at eq
      have read : (readValue C D x).val = C.asPoint r :=
        rx ▸ readValue_of_representative C D r hr
      exact ⟨q,qy,eq.symm.trans read.symm⟩
    · have same : b = q := representative_injective C (by'.trans qy.symm)
      rw [same] at zero
      rw [readValue_of_default C D fallback]
      exact ⟨q,qy,zero⟩
  · rintro ⟨q,qy,read⟩
    have hq : C.mem (C.asPoint q) D.omega := read.symm ▸ (readValue C D x).property
    refine ⟨⟨q,qy,hq⟩,?_⟩
    by_cases named : NamedNatural C D x
    · obtain ⟨r,rx,hr⟩ := named
      have value : (readValue C D x).val = C.asPoint r :=
        rx ▸ readValue_of_representative C D r hr
      exact Or.inl ⟨⟨r,rx,hr⟩,r,q,rx,qy,value.symm.trans read.symm⟩
    · rw [readValue_of_default C D named] at read
      exact Or.inr ⟨named,q,qy,read⟩

end PalomarI3380.Calibration
