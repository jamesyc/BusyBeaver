module
public import I3_380.Calibration.TruthClauses
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic
import Mathlib.Tactic.FinCases
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open Logic Logic.Expanded SquareRepresentation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

noncomputable def checkedDerivationDef : 𝚺ᴬ₁.Semisentence 4 :=
  .mkSigma “proof sequent free assignment. !(derivationOf graphTheory).sigma proof sequent ∧
    !pairDef assignment 0 free”

noncomputable def assignmentEntryDef : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “entry index free. ∃ length, !lenDef length free ∧ index<length ∧ !nthDef entry free index”

def containsCode : Semisentence ℒₒᵣ 2 := “p s. p ∈ s”

section Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem checkedDerivation_eval (proof sequent free assignment : M) :
    checkedDerivationDef.val.Evalb ![proof,sequent,free,assignment] ↔
      DerivationOf graphTheory proof sequent ∧ assignment=⟪0,free⟫ := by
  have checked : (derivationOf graphTheory).sigma.val.Evalb ![proof,sequent] ↔
      DerivationOf graphTheory proof sequent := by
    rw [Bounding.HierarchySymbol.Semiformula.val_sigma]
    exact DerivationOf.defined.iff
  simp [checkedDerivationDef,checked,pair_defined.iff]

theorem assignmentEntry_eval (entry index free : M) :
    assignmentEntryDef.val.Evalb ![entry,index,free] ↔ index<len free ∧ entry=free.[index] := by
  simp [assignmentEntryDef,len_defined.iff,nth_defined.iff]

theorem containsCode_eval (p s : M) : containsCode.Evalb ![p,s] ↔ p∈s := by
  simp [containsCode]

end Arithmetic

variable {V : Type} {E G : V → V → Prop} {L : ClassAxioms E G} {inhabited : Nonempty V}
variable (D : OmegaDomain L inhabited) {P : Presentation D} (T : TruthTable D P)

def AssignmentIn (f : D.Points) : Prop := ∀ i < len f, E (f.[i]).val P.domain

def TruthTable.SequentTrue (s : D.Points) : Prop :=
  ∀ f : D.Points, AssignmentIn D (P := P) f →
    ∃ p ∈ s, T.holds D p ⟪0,f⟫

def TruthTable.DerivationTrue (d : D.Points) : Prop :=
  ∀ s : D.Points, DerivationOf graphTheory d s → T.SequentTrue D s

set_option maxHeartbeats 700000 in
theorem derivationTrue_definable :
    ∃ pred : (Nat → V) → Prop, (context D).square.Definable 5 pred ∧
      ∀ d : D.Points, pred (parameterEnv [D.omega,P.domain,T.family] d.val D.omega) ↔ T.DerivationTrue D d := by
  let N := context D
  have check := arithmeticOn_definable (E := E) (G := G) checkedDerivationDef.val (scope := 8) (omega := 5)
    (arg := ![3,2,1,0]) (by decide) (by intro i; fin_cases i <;> decide)
  have entry := arithmeticOn_definable (E := E) (G := G) assignmentEntryDef.val (scope := 10) (omega := 7)
    (arg := ![0,1,3]) (by decide) (by intro i; fin_cases i <;> decide)
  have mem := Definable.mem (N := N) (n := 10) (i := 0) (j := 8) (by decide) (by decide)
  have belongs := arithmeticOn_definable (E := E) (G := G) containsCode (scope := 9) (omega := 6)
    (arg := ![0,3]) (by decide) (by intro i; fin_cases i <;> decide)
  simp only [Matrix.comp_vecCons',Matrix.empty_eq] at check entry belongs
  have truth := N.familyTruth_definable (n := 9) (i := 8) (j := 0) (k := 1) (by decide) (by decide) (by decide)
  have assignments := Definable.all (Definable.all (Definable.implies (S := N.square) entry mem))
  have someTrue := Definable.ex (Definable.and (S := N.square) belongs truth)
  have formula := Definable.all (Definable.all (Definable.all
    (Definable.implies (S := N.square) check (assignments.implies someTrue))))
  refine ⟨_,formula,fun d => ?_⟩
  let Valid (f : V) := ∀ i name : V,
    arith (E := E) (G := G) assignmentEntryDef.val D.omega ![name,i,f] → E name P.domain
  let TrueIn (s env : V) := ∃ p : V,
    arith (E := E) (G := G) containsCode D.omega ![p,s] ∧ N.FamilyTruth T.family p env
  have validFree (f : D.Points) : Valid f.val ↔ AssignmentIn D (P := P) f := by
    have elem (a i : D.Points) :
        arith (E := E) (G := G) assignmentEntryDef.val D.omega ![a.val,i.val,f.val] ↔
          i<len f ∧ a=f.[i] := by
      have h := arith_args D assignmentEntryDef.val ![a,i,f]
      simpa only [pointValues_cons,pointValues_nil,assignmentEntry_eval] using h
    constructor
    · intro valid i bound
      exact valid i.val f.[i].val ((elem _ _).mpr ⟨bound,rfl⟩)
    · intro valid i name checked
      obtain ⟨v,reads,_⟩ := (arithmeticOn_eval D assignmentEntryDef.val _).mp checked
      have x : (v 0).val=name := reads 0
      have j : (v 1).val=i := reads 1
      have check := (elem (v 0) (v 1)).mp (by rw [x,j]; exact checked)
      have equal : name=(f.[v 1]).val := x.symm.trans (congrArg Subtype.val check.2)
      exact equal.symm ▸ valid _ check.1
  have readSequent (s env : D.Points) :
      TrueIn s.val env.val ↔ ∃ p ∈ s, T.holds D p env := by
    have code (p : D.Points) : arith (E := E) (G := G) containsCode D.omega ![p.val,s.val] ↔ p∈s := by
      simpa only [pointValues_cons,pointValues_nil,containsCode_eval] using arith_args D containsCode ![p,s]
    constructor
    · rintro ⟨p,read,holds⟩
      obtain ⟨v,same,_⟩ := (arithmeticOn_eval D containsCode _).mp read
      have eq : (v 0).val=p := same 0
      refine ⟨v 0,(code _).mp (eq.symm ▸ read),?_⟩
      change N.FamilyTruth T.family (v 0).val env.val
      rwa [eq]
    · rintro ⟨p,belongs,truth⟩
      exact ⟨p.val,(code p).mpr belongs,truth⟩
  have checked (s free env : D.Points) :
      arith (E := E) (G := G) checkedDerivationDef.val D.omega ![d.val,s.val,free.val,env.val] ↔
        DerivationOf graphTheory d s ∧ env=⟪0,free⟫ := by
    simpa only [pointValues_cons,pointValues_nil,checkedDerivation_eval] using arith_args D checkedDerivationDef.val ![d,s,free,env]
  change (∀ s free env : V,
    arith (E := E) (G := G) checkedDerivationDef.val D.omega ![d.val,s,free,env] →
      Valid free → TrueIn s env) ↔ _
  constructor
  · intro h s derivation f assignment
    exact (readSequent s _).mp (h s.val f.val (⟪0,f⟫ : D.Points).val
      ((checked s f _).mpr ⟨derivation,rfl⟩) ((validFree f).mpr assignment))
  · intro h s free env verified assignment
    obtain ⟨v,rep,_⟩ := (arithmeticOn_eval D checkedDerivationDef.val _).mp verified
    have a : (v 1).val=s := rep 1
    have b : (v 2).val=free := rep 2
    have c : (v 3).val=env := rep 3
    obtain ⟨proof,equation⟩ := (checked (v 1) (v 2) (v 3)).mp (by rw [a,b,c]; exact verified)
    have defined := (validFree (v 2)).mp (b.symm ▸ assignment)
    have model := h (v 1) proof (v 2) defined
    have agrees : ∃ p ∈ v 1, T.holds D p (v 3) := equation.symm ▸ model
    exact a ▸ c ▸ (readSequent (v 1) (v 3)).mpr agrees

end PalomarI3380.Calibration.CodedGraph
