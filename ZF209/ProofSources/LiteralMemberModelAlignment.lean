module
public import ModelReplay2378
public import ModelLiteralContextCodeCertificate
public import LiteralSchemaCodeModelAlignment
public import ModelSourcePredicateUniqueness
public import ExactMemberDefinability
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def memberFixFirst (e : Nat → M) (P : M → M → Prop)
 (c : FormulaCertificate e 2 (fun v=>P (v 0) (v 1))) :
 FormulaCertificate e 1 (fun v=>P (e 0) (v 0)) where
 formula := “g. !c.formula &0 g”
 correct := by
  intro v
  have hv : (fun _ : Fin 1=>v 0)=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
  simpa [hv,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq] using c.correct ![e 0,v 0]
lemma literalMember_modelMember (a g : M) : t144 a g ↔ modelMember a g := by
 let e : Nat → M := fun _=>a
 let c := literalContextMembership_certificate e
 let p := memberFixFirst e (fun x y=>t144 x y) c
 let q : FormulaCertificate e 1 (fun v=>modelMember a (v 0)) := {
  formula := “g. !memberFormula &0 g”
  correct := by
   intro v
   have hv : (fun _ : Fin 1=>v 0)=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
   simpa [hv,Semiformula.eval_rew,Function.comp_def,e,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq] using (memberFormula_eval a (v 0)).symm }
 have all := (p.iffCert q).orderInduction (by
  intro n ih
  change t144 a n ↔ modelMember a n
  change ∀y<n,t144 a y ↔ modelMember a y at ih
  by_cases hz:n=0
  · subst n
    have hn : ¬t144 a 0 := by simpa [t1,t28] using p2375 (M:=M) a
    simp only [hn, modelMember, modelMemberCode_zero, zero_ne_one, iff_self]
  · have hp:0<n := pos_iff_ne_zero.mpr hz
    have he:n=modelListCons (modelListHead n) (modelListTail n) := (modelList_reconstruct n hp).symm
    have ht:=modelListTail_lt n hp
    have hc : t144 a (modelListCons (modelListHead n) (modelListTail n)) ↔
      a=modelListHead n ∨ t144 a (modelListTail n) := by
      simpa [t3,t2,t0,t1,t4,t10,literalCons_modelListCons,or_iff_not_imp_left,iff_iff_implies_and_implies] using p2376 (M:=M) a (modelListHead n) (modelListTail n)
    rw [he,hc,modelMember_cons,ih (modelListTail n) ht]
    rw [eq_comm])
 exact all g
end ZF209.MM0ModelReplay
