module
public import I3_334Support.Calibration.TruthTable
import Mathlib.Tactic.FinCases
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open Logic Logic.Expanded SquareRepresentation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} {E G : V → V → Prop} {L : ClassAxioms E G} {inhabited : Nonempty V}
variable (D : OmegaDomain L inhabited) (P : Presentation D)

def pointValues {n : Nat} (v : Fin n → D.Points) : Fin n → V := fun i => (v i).val

theorem pointValues_nil (v : Fin 0 → D.Points) : pointValues D v = ![] :=
  funext fun i => i.elim0

theorem pointValues_cons {n : Nat} (a : D.Points) (tail : Fin n → D.Points) :
    pointValues D (a :> tail) = a.val :> pointValues D tail :=
  funext (Fin.cases rfl (fun _ => rfl))

theorem arith_args {k : Nat} (formula : Semisentence ℒₒᵣ k) (v : Fin k → D.Points) :
    arith (E := E) (G := G) formula D.omega (pointValues D v) ↔ formula.Evalb v := by
  refine (arithmeticOn_eval D formula _).trans ?_
  constructor
  · rintro ⟨w,same,checked⟩
    have eq : w=v := funext fun i => Subtype.ext (same i)
    exact eq ▸ checked
  · exact fun h => ⟨v,fun _ => rfl,h⟩

theorem atomInput_shape {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (kind : Nat) (atom p e fallback : M) (positive : 0<p) :
    (atomInputDef kind).val.Evalb ![atom,p,e,fallback] ↔
      ∃ k r ts vals : M, p=⟪(kind : M),k,r,ts⟫+1 ∧ Values vals ts e fallback ∧ atom=⟪k,r,vals⟫ := by
  rw [atomInput_eval]
  constructor
  · rintro ⟨tag,vals,checked,rfl⟩
    refine ⟨π₁ (π₂ (p-1)),π₁ (π₂ (π₂ (p-1))),π₂ (π₂ (π₂ (p-1))),vals,?_,checked,rfl⟩
    have eq := (pair4_match (p-1) (kind : M) _ _ _).mpr ⟨tag,rfl,rfl,rfl⟩
    exact ((tsub_add_cancel_of_le (pos_iff_one_le.mp positive)).symm.trans (congrArg (·+1) eq))
  · rintro ⟨k,r,ts,vals,rfl,checked,rfl⟩
    exact ⟨by simp,vals,by simpa using checked,by simp⟩

def TableRelation (k r terms env : D.Points) : Prop :=
  ∃ vals, Values vals terms env P.fallback ∧ E (⟪k,r,vals⟫ : D.Points).val P.atoms

theorem atomLayer_eval (negative : Bool) (p env : D.Points) (pos : 0<p) :
    AtomLayer (E := E) (G := G) negative (P.data D) p.val env.val ↔
      ∃ k r terms : D.Points,
        p=⟪(↑(if negative then 1 else 0 : Nat) : D.Points),k,r,terms⟫+1 ∧
        (if negative then ¬TableRelation D P k r terms env else TableRelation D P k r terms env) := by
  let kind := if negative then 1 else 0
  let formula := (atomInputDef kind).val
  have message (input : D.Points) :
      arith (E := E) (G := G) formula D.omega ![input.val,p.val,env.val,P.fallback.val] ↔
        formula.Evalb ![input,p,env,P.fallback] := by
    have v := arith_args D formula ![input,p,env,P.fallback]
    simpa only [pointValues_cons,pointValues_nil] using v
  have typed :
      AtomLayer (E := E) (G := G) negative (P.data D) p.val env.val ↔
        ∃ a : D.Points, formula.Evalb ![a,p,env,P.fallback] ∧
          (if negative then ¬E a.val P.atoms else E a.val P.atoms) := by
    constructor
    · rintro ⟨a,checked,use⟩
      obtain ⟨points,same,truth⟩ := (arithmeticOn_eval D formula _).mp checked
      have rep : (points 0).val=a := same 0
      exact ⟨points 0,(message _).mp (rep.symm ▸ checked),rep.symm ▸ use⟩
    · rintro ⟨a,checked,use⟩
      exact ⟨a.val,(message _).mpr checked,use⟩
  rw [typed]
  constructor
  · rintro ⟨atom,good,answer⟩
    obtain ⟨k,r,terms,vals,shape,values,eq⟩ := (atomInput_shape kind atom p env P.fallback pos).mp good
    subst atom
    refine ⟨k,r,terms,shape,?_⟩
    cases negative
    · exact ⟨vals,values,answer⟩
    · rintro ⟨v,valid,member⟩
      obtain ⟨_,_,only⟩ := values_exist terms env P.fallback
      exact answer ((only v valid).trans (only vals values).symm ▸ member)
  · rintro ⟨k,r,terms,shape,answer⟩
    obtain ⟨v,values,only⟩ := values_exist terms env P.fallback
    refine ⟨⟪k,r,v⟫,(atomInput_shape kind _ p env P.fallback pos).mpr ⟨k,r,terms,v,shape,values,rfl⟩,?_⟩
    cases negative
    · obtain ⟨u,eval,member⟩ := answer
      exact only u eval ▸ member
    · intro h
      exact answer ⟨v,values,h⟩

theorem binaryLayer_eval (conjunctive : Bool) (p env : D.Points) (prior : V) :
    BinaryLayer conjunctive (context D) (P.data D) p.val prior env.val ↔
      ∃ a b : D.Points, p=⟪(↑(if conjunctive then 4 else 5 : Nat) : D.Points),a,b⟫+1 ∧
        if conjunctive then
          (context D).FamilyTruth prior a.val env.val ∧ (context D).FamilyTruth prior b.val env.val
        else
          (context D).FamilyTruth prior a.val env.val ∨ (context D).FamilyTruth prior b.val env.val := by
  let kind := if conjunctive then 4 else 5
  let formula := (binaryInputDef kind).val
  have message (a b : D.Points) :
      arith (E := E) (G := G) formula D.omega ![p.val,a.val,b.val] ↔
        p=⟪(kind : D.Points),a,b⟫+1 := by
    have v := arith_args D formula ![p,a,b]
    exact (by simpa only [pointValues_cons,pointValues_nil] using v :
      arith (E := E) (G := G) formula D.omega ![p.val,a.val,b.val] ↔ formula.Evalb ![p,a,b]).trans
      (binaryInput_eval kind p a b)
  constructor
  · rintro ⟨a,b,decoded,holds⟩
    obtain ⟨points,same,_⟩ := (arithmeticOn_eval D formula _).mp decoded
    have first : (points 1).val=a := same 1
    have second : (points 2).val=b := same 2
    exact ⟨points 1,points 2,(message _ _).mp (by rw [first,second]; exact decoded),by rwa [first,second]⟩
  · rintro ⟨a,b,shape,holds⟩
    exact ⟨a.val,b.val,(message _ _).mpr shape,holds⟩

theorem binderLayer_eval (universal : Bool) (p env : D.Points) (prior : V) :
    BinderLayer universal (context D) (P.data D) p.val prior env.val ↔
      ∃ a : D.Points, p=⟪(↑(if universal then 6 else 7 : Nat) : D.Points),a⟫+1 ∧
        if universal then ∀ x : P.Carrier D,
          (context D).FamilyTruth prior a.val (pushBound x.val env).val
        else ∃ x : P.Carrier D,
          (context D).FamilyTruth prior a.val (pushBound x.val env).val := by
  let kind := if universal then 6 else 7
  let formula := (unaryInputDef kind).val
  have message (a : D.Points) :
      arith (E := E) (G := G) formula D.omega ![p.val,a.val] ↔ p=⟪(kind : D.Points),a⟫+1 := by
    have v := arith_args D formula ![p,a]
    exact (by simpa only [pointValues_cons,pointValues_nil] using v :
      arith (E := E) (G := G) formula D.omega ![p.val,a.val] ↔ formula.Evalb ![p,a]).trans
      (unaryInput_eval kind p a)
  have body (x a : D.Points) :
      (∃ changed, arith (E := E) (G := G) pushInputDef.val D.omega ![changed,x.val,env.val] ∧
        (context D).FamilyTruth prior a.val changed) ↔
        (context D).FamilyTruth prior a.val (pushBound x env).val := by
    have changeEnv (a' : D.Points) :
        arith (E := E) (G := G) pushInputDef.val D.omega ![a'.val,x.val,env.val] ↔ a'=pushBound x env := by
      simpa only [pointValues_cons,pointValues_nil,pushInput_eval] using arith_args D pushInputDef.val ![a',x,env]
    constructor
    · rintro ⟨changed,checked,holds⟩
      obtain ⟨points,same,_⟩ := (arithmeticOn_eval D pushInputDef.val _).mp checked
      have eq : (points 0).val=changed := same 0
      have aligned := (changeEnv (points 0)).mp (eq.symm ▸ checked)
      exact (congrArg Subtype.val aligned) ▸ (eq.symm ▸ holds)
    · exact fun h => ⟨_,(changeEnv (pushBound x env)).mpr rfl,h⟩
  constructor
  · rintro ⟨a,decoded,holds⟩
    obtain ⟨points,same,_⟩ := (arithmeticOn_eval D formula _).mp decoded
    have eq : (points 1).val=a := same 1
    refine ⟨points 1,(message _).mp (eq.symm ▸ decoded),?_⟩
    cases universal
    · obtain ⟨x,inDomain,t⟩ := holds
      let point : P.Carrier D := ⟨⟨x,P.domain_natural x inDomain⟩,inDomain⟩
      exact ⟨point,(body point.val _).mp (eq.symm ▸ t)⟩
    · intro x
      exact (body x.val _).mp (eq.symm ▸ holds x.val.val x.property)
  · rintro ⟨a,shape,holds⟩
    refine ⟨a.val,(message _).mpr shape,?_⟩
    cases universal
    · obtain ⟨p,h⟩ := holds
      exact ⟨p.val.val,p.property,(body p.val _).mpr h⟩
    · dsimp only
      intro x inDomain
      let point : P.Carrier D := ⟨⟨x,P.domain_natural x inDomain⟩,inDomain⟩
      exact (body point.val _).mpr (holds point)

end PalomarI3380.Calibration.CodedGraph
