module
public import ModelLiteralC207Graph330
public import ModelLiteralContextCodeCertificate
public import ModelLiteralTraceCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def literalC207AxiomInstance_certificate (e : Nat → M) :
 FormulaCertificate e 5 (fun v=>t331 (v 0) (v 1) (v 2) (v 3) (v 4)) := by
 let c323 := literalC207Constructor323_certificate (M:=M) e
 let c324 := literalC207Constructor324_certificate (M:=M) e
 let c325 := literalC207Constructor325_certificate (M:=M) e
 let c326 := literalC207Constructor326_certificate (M:=M) e
 let c327 := literalC207Constructor327_certificate (M:=M) e
 let c328 := literalC207Constructor328_certificate (M:=M) e
 let c329 := literalC207Constructor329_certificate (M:=M) e
 let c330 := literalC207Constructor330_certificate (M:=M) e
 refine ⟨“x a b c d. x=0 ∨ !c323.formula x a b c ∨ !c324.formula x a b c ∨ !c325.formula x a b c ∨ !c326.formula x a b c ∨ !c327.formula x a b c ∨ !c328.formula x a b c ∨ (d≤b ∧ !c329.formula x a b c d) ∨ ((a≠b ∧ a≠c) ∧ !c330.formula x a b c)”,?_⟩
 intro v
 have h323 (x a b c:M) : c323.formula.Eval ![x,a,b,c] e ↔ x=t323 a b c := c323.correct ![a,b,c] x
 have h324 (x a b c:M) : c324.formula.Eval ![x,a,b,c] e ↔ x=t324 a b c := c324.correct ![a,b,c] x
 have h325 (x a b c:M) : c325.formula.Eval ![x,a,b,c] e ↔ x=t325 a b c := c325.correct ![a,b,c] x
 have h326 (x a b c:M) : c326.formula.Eval ![x,a,b,c] e ↔ x=t326 a b c := c326.correct ![a,b,c] x
 have h327 (x a b c:M) : c327.formula.Eval ![x,a,b,c] e ↔ x=t327 a b c := c327.correct ![a,b,c] x
 have h328 (x a b c:M) : c328.formula.Eval ![x,a,b,c] e ↔ x=t328 a b c := c328.correct ![a,b,c] x
 have h329 (x a b c d:M) : c329.formula.Eval ![x,a,b,c,d] e ↔ x=t329 a b c d := c329.correct ![a,b,c,d] x
 have h330 (x a b c:M) : c330.formula.Eval ![x,a,b,c] e ↔ x=t330 a b c := c330.correct ![a,b,c] x
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,t331,
 literalOr_iff,literalAnd_iff,literalLe_order,t13,t1,t10,t28,or_assoc,h323,h324,h325,h326,h327,h328,h329,h330]
noncomputable def literalC207Axioms_certificate (e : Nat → M) :
 FormulaCertificate e 1 (fun v=>t332 (v 0)) := by
 let ax := literalC207AxiomInstance_certificate e
 refine ⟨“x. ∃a, ∃b, ∃c, ∃d, !ax.formula x a b c d”,?_⟩
 intro v
 have ha (x a b c d:M) : ax.formula.Eval ![x,a,b,c,d] e ↔ t331 x a b c d := (ax.correct ![x,a,b,c,d]).symm
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',hv,ha,t332,t15,literalExists_iff]
noncomputable def literalC207MpRules_certificate (e : Nat → M) :
 FormulaCertificate e 1 (fun v=>t333 (v 0)) := by
 let fst := literalFst_certificate e
 let snd := literalSnd_certificate e
 let mem := literalContextMembership_certificate e
 let ax := literalC207Axioms_certificate e
 let imp := literalC207Constructor299_certificate (M:=M) e
 refine ⟨“k. ∃x, ∃l, !fst.formula x k ∧ !snd.formula l k ∧
 (!ax.formula x ∨ ∃p, ∃q, !imp.formula q p x ∧ !mem.formula p l ∧ !mem.formula q l)”,?_⟩
 intro v
 have hf (x k:M) := fst.correct ![k] x
 have hs (l k:M) := snd.correct ![k] l
 have hm (p l:M) : mem.formula.Eval ![p,l] e ↔ t144 p l := (mem.correct ![p,l]).symm
 have ha (x:M) : ax.formula.Eval ![x] e ↔ t332 x := (ax.correct ![x]).symm
 have hi (q p x:M) : imp.formula.Eval ![q,p,x] e ↔ q=t299 p x := imp.correct ![p,x] q
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',hv,hf,hs,hm,ha,hi]
 simp [t333,t73,t15,t25,t14,t16,t8,t0,t10,literalOr_iff,literalAnd_iff,literalExists_iff]
noncomputable def literalC207GenRules_certificate (e : Nat → M) :
 FormulaCertificate e 1 (fun v=>t334 (v 0)) := by
 let fst := literalFst_certificate e
 let snd := literalSnd_certificate e
 let mem := literalContextMembership_certificate e
 let gen := literalC207Constructor322_certificate (M:=M) e
 refine ⟨“k. ∃x, ∃l, !fst.formula x k ∧ !snd.formula l k ∧
 (∃a, ∃p, !mem.formula p l ∧ !gen.formula x a p)”,?_⟩
 intro v
 have hf (x k:M) := fst.correct ![k] x
 have hs (l k:M) := snd.correct ![k] l
 have hm (p l:M) : mem.formula.Eval ![p,l] e ↔ t144 p l := (mem.correct ![p,l]).symm
 have hg (x a p:M) : gen.formula.Eval ![x,a,p] e ↔ x=t322 a p := gen.correct ![a,p] x
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',hv,hf,hs,hm,hg]
 simp [t334,t73,t15,t25,t14,t16,t8,t0,t10,literalAnd_iff,literalExists_iff]
noncomputable def literalC207Rules_certificate (e : Nat → M) :
 FormulaCertificate e 1 (fun v=>t335 (v 0)) := by
 let mp := literalC207MpRules_certificate e
 let gen := literalC207GenRules_certificate e
 refine ⟨“k. !mp.formula k ∨ !gen.formula k”,?_⟩
 intro v
 simp [t335,t20,t15,t16,literalOr_iff]
 rw [←mp.correct v,←gen.correct v]
noncomputable def literalC207Derives_certificate (e : Nat → M) :
 FormulaCertificate e 2 (fun v=>t336 (v 0) (v 1)) := by
 let valid := literalTraceValid_certificate (literalC207Rules_certificate e)
 let mem := literalContextMembership_certificate e
 refine ⟨“p r. !valid.formula p ∧ !mem.formula r p”,?_⟩
 intro v
 have ht (p:M) : valid.formula.Eval ![p] e ↔ t172 t335 p := (valid.correct ![p]).symm
 have hm (r p:M) : mem.formula.Eval ![r,p] e ↔ t144 r p := (mem.correct ![r,p]).symm
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',hv,ht,hm,t336,t173,literalAnd_iff]
end ZF207.MM0ModelReplay
