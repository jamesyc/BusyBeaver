module
public import I3_380.Calibration.NaturalNames
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder
open Logic (SetFormula)
open Logic.Expanded (ClassAxioms OmegaDomain)

variable {A : Type} [Tarski.Structure FilterLanguage A] [Tarski.Structure.Eq FilterLanguage A]
variable (C : FilterModel A)
variable {laws : ClassAxioms C.mem (fun _ _ => False)} {inhabited : Nonempty C.Domain}
variable (D : OmegaDomain laws inhabited)

noncomputable def naturalLevels {n : Nat} (env : Fin n → A) (default : C.Representative) : Nat → C.Domain :=
  fun i => if inside : i < n then (readValue C D (env ⟨n-(i+1),by omega⟩)).val else C.asPoint default

theorem arithmeticTemplate_eval {n : Nat} (p : SetFormula) (bound : Logic.Bound (p n) n)
    (env : Fin n → A) (default : C.Representative) :
    (arithmeticTemplate n p).Evalb env ↔ SetFormula.holds C.mem p n
      (naturalLevels C D env default) (C.asPoint default) := by
  simp only [arithmeticTemplate,Semiformula.eval_exsItr,LogicalConnective.HomClass.map_and,eval_vector_conj,
    Semiformula.eval_substs,Semiterm.val,Function.comp_def,Matrix.comp_vecCons',
    Matrix.appeendr_addNat,Matrix.appeendr_addCast,Matrix.constant_eq_singleton,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.empty_eq]
  change (∃ v : Fin n → A, (∀ i, readsName.Evalb ![env i,v i]) ∧ (namedMembership n (p n)).Evalb v) ↔ _
  constructor
  · rintro ⟨v,reads,hasProperty⟩
    obtain ⟨q,same,truth⟩ := (namedSetFormula_eval C p bound v default).mp hasProperty
    have names (i : Fin n) : C.asPoint (q i) = (readValue C D (env i)).val := by
      obtain ⟨r,val,eq⟩ := (readsName_eval C D (env i) (v i) default).mp (reads i)
      have chosen : q i = r := representative_injective C ((same i).trans val.symm)
      rw [chosen]
      exact eq
    have levels : pointLevels C q default = naturalLevels C D env default := by
      funext i
      by_cases inside : i < n <;> simp [pointLevels,naturalLevels,inside,names]
    simpa only [levels] using truth
  · intro truth
    have representatives (i : Fin n) :
        ∃ q : C.Representative, C.asPoint q = (readValue C D (env i)).val :=
      C.asPoint_onto _
    let q := fun i => Classical.choose (representatives i)
    have names (i : Fin n) : C.asPoint (q i) = (readValue C D (env i)).val :=
      Classical.choose_spec (representatives i)
    have levels : pointLevels C q default = naturalLevels C D env default := by
      funext i
      by_cases inside : i < n <;> simp [pointLevels,naturalLevels,inside,names]
    let v := fun i => (q i).val.val
    refine ⟨v,fun i => (readsName_eval C D (env i) (v i) default).mpr ⟨q i,rfl,names i⟩,?_⟩
    exact (namedSetFormula_eval C p bound v default).mpr ⟨q,fun _ => rfl,levels.symm ▸ truth⟩

theorem markedTemplate_eval {n : Nat} (p : SetFormula) (bound : Logic.Bound (p n) n)
    (env : Fin n → A) (marker : A) (default : C.Representative) :
    letI := graphStructure (A := A)
    (markedTemplate n p).Evalb (marker :> env) ↔ SetFormula.holds C.mem p n
      (naturalLevels C D env default) (C.asPoint default) := by
  letI := graphStructure (A := A)
  rw [markedTemplate,graphFormula_eval,Semiformula.eval_bShift]
  exact arithmeticTemplate_eval C D p bound env default

end PalomarI3380.Calibration
