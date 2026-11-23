module
public import I3_334Support.Calibration.GroundQuotient
public import I3_334Support.Arithmetic.GuardedArithmetic
public import I3_334Support.Arithmetic.OmegaPeano
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def SameCode (a b : M) : Prop :=
  IsSemiterm FilterLanguage 0 a ∧ IsSemiterm FilterLanguage 0 b ∧
    Convertible (termTokens a) (termTokens b)

noncomputable def sameCodeDef : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “a b. !(isSemiterm FilterLanguage).sigma 0 a ∧ !(isSemiterm FilterLanguage).sigma 0 b ∧
    ∃ x y, !termTokensDef x a ∧ !termTokensDef y b ∧ !convertibleDef x y”

theorem sameCode_eval (a b : M) : sameCodeDef.val.Evalb ![a,b] ↔ SameCode a b := by
  have syntax' (t : M) :
      (isSemiterm FilterLanguage).sigma.val.Evalb ![0,t] ↔ IsSemiterm FilterLanguage 0 t := by
    rw [Bounding.HierarchySymbol.Semiformula.val_sigma]
    exact IsSemiterm.defined.iff (v := ![0,t])
  simp [sameCodeDef,SameCode,syntax',convertibleDef_eval,(termTokens_defined (M := M)).iff]

theorem SameCode.trans {a b c : M} (ab : SameCode a b) (bc : SameCode b c) : SameCode a c :=
  ⟨ab.1,bc.2.1,ab.2.2.trans bc.2.2⟩

def Canonical (code : M) : Prop :=
  IsSemiterm FilterLanguage 0 code ∧ ∀ j < code, ¬SameCode j code

noncomputable def canonicalDef : 𝚷ᴬ₁.Semisentence 1 :=
  .mkPi “code. !(isSemiterm FilterLanguage).pi 0 code ∧ ∀ j < code, ¬!sameCodeDef j code”

theorem canonical_eval (code : M) : canonicalDef.val.Evalb ![code] ↔ Canonical code := by
  have syntax' : (isSemiterm FilterLanguage).pi.val.Evalb ![(0 : M),code] ↔ IsSemiterm FilterLanguage 0 code :=
    (IsSemiterm.defined (L := FilterLanguage) (V := M)).proper.iff' _ |>.trans IsSemiterm.defined.iff
  simp [canonicalDef,Canonical,syntax',sameCode_eval]

abbrev CanonicalTerm (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :=
  {code : M // Canonical code}

def canonicalClass (code : CanonicalTerm M) : GroundClasses M :=
  groundClass ⟨code.val,by simpa using code.property.1⟩

theorem canonicalClass_injective : Function.Injective (canonicalClass (M := M)) := by
  intro a b same
  have path : Convertible (termTokens a.val) (termTokens b.val) :=
    Quotient.exact same
  rcases lt_trichotomy a.val b.val with before | identical | after
  · exact (b.property.2 _ before ⟨a.property.1,b.property.1,path⟩).elim
  · exact Subtype.ext identical
  · exact (a.property.2 _ after ⟨b.property.1,a.property.1,path.symm⟩).elim

theorem canonicalClass_surjective [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] :
    Function.Surjective (canonicalClass (M := M)) := by
  intro term
  let r := representative term
  have relation : 𝚺ᴬ₁-Predicate (fun a : M => SameCode a r.val) := by
    have h : 𝚺ᴬ₁-Relation (SameCode (M := M)) :=
      (show 𝚺ᴬ₁-Relation (SameCode (M := M)) via sameCodeDef from .mk fun v => by
        rw [Matrix.fun_eq_vec_two v]
        exact sameCode_eval ..).to_definable
    definability
  obtain ⟨code,related,minimal⟩ := InductionOnHierarchy.least_number_sigma 𝚺 1 relation
    (show SameCode r.val r.val from ⟨r.isSemiterm_zero,r.isSemiterm_zero,Convertible.refl _⟩)
  have least : Canonical code :=
    ⟨related.1,fun j before witness => minimal j before (witness.trans related)⟩
  exact ⟨⟨code,least⟩,(Quotient.sound related.2.2).trans (groundClass_representative term)⟩

theorem canonical_domain {V : Type} {E G : V → V → Prop}
    {laws : Logic.Expanded.ClassAxioms E G} {inhabited : Nonempty V}
    (D : Logic.Expanded.OmegaDomain laws inhabited) :
    letI : D.Points↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano
    ∃ domain : V, ∀ x, E x domain ↔ ∃ code : D.Points, code.val = x ∧ Canonical code := by
  letI : D.Points↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano
  obtain ⟨set,semantics⟩ := D.separate_arithmetic canonicalDef.val Empty.elim
  refine ⟨set,fun x => (semantics x).trans ?_⟩
  apply exists_congr
  intro b
  exact and_congr_right (fun _ => canonical_eval b)

end PalomarI3380.Calibration.TermWords
