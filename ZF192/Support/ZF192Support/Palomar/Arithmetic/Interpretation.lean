module
public import ZF192Support.Palomar.Arithmetic.SetPrimitives
public import ZF192Support.SetTheory.Omega.Multiplication
@[expose] public section
namespace PalomarZF192Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open ZF192Support.OmegaInterpretation
variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "E" => (fun x y : V => x ∈ y)
lemma cseq_value {k : Nat} {p : NaturalNumberRec.Blueprint k}
 (c : NaturalNumberRec.Construction V p) (v : Fin k → V) {n f i x : V}
 (hf : c.CSeq v n f) (hx : ⟨i,x⟩ₖ ∈ f) : x = c.result v i := by
 have hi := hf.index_mem hx
 obtain ⟨g,hg,hv⟩ := c.result_spec v hi
 exact hf.value_unique hg hi hx hv
lemma add_iff (a b c : V) : Add E a b c ↔
 a ∈ (ω : V) ∧ b ∈ (ω : V) ∧ c = add a b := by
 simp only [Add,natObject_iff,empty_iff,succ_iff,functionOn_iff,at_iff]
 constructor
 · rintro ⟨ha,hb,hc,z,d,f,rfl,rfl,⟨hf,hd⟩,hz,hv,_,hs⟩
   letI := hf
   have hseq : addConstruction.CSeq ![a] b f := {
    nat := hb, isFunction := hf, domain_eq := hd
    zero := by simpa [addConstruction,zero_def] using hz
    succ := by
     intro i hi x hx
     obtain ⟨j,u,y,rfl,hu,hy,he⟩ := hs i hi
     have hu' : u=x := IsFunction.unique hu hx
     subst u
     simpa [addConstruction,he] using hy }
   exact ⟨ha,hb,cseq_value addConstruction ![a] hseq hv⟩
 · rintro ⟨ha,hb,rfl⟩
   obtain ⟨f,hf,hv⟩ := addConstruction.result_spec ![a] hb
   refine ⟨ha,hb,add_mem_omega a b ha hb,∅,SetTheory.succ b,f,rfl,rfl,
    ⟨hf.isFunction,hf.domain_eq⟩,?_,hv,?_,?_⟩
   · simpa [addConstruction,zero_def] using hf.zero
   · intro i x hi hx
     have he := cseq_value addConstruction ![a] hf hx
     rw [he]
     exact add_mem_omega a i ha (hf.index_mem hx)
   · intro i hi
     obtain ⟨x,hx⟩ := hf.exists_value (mem_succ_iff.mpr (Or.inr hi))
     exact ⟨SetTheory.succ i,x,SetTheory.succ x,rfl,hx,hf.succ i hi x hx,rfl⟩
lemma mul_iff (a b c : V) : Mul E a b c ↔
 a ∈ (ω : V) ∧ b ∈ (ω : V) ∧ c = mul a b := by
 simp only [Mul,natObject_iff,empty_iff,succ_iff,functionOn_iff,at_iff,add_iff]
 constructor
 · rintro ⟨ha,hb,hc,z,d,f,rfl,rfl,⟨hf,hd⟩,hz,hv,_,hs⟩
   letI := hf
   have hseq : mulConstruction.CSeq ![a] b f := {
    nat := hb, isFunction := hf, domain_eq := hd
    zero := by simpa [mulConstruction,zero_def] using hz
    succ := by
     intro i hi x hx
     obtain ⟨j,u,y,rfl,hu,hy,_,_,he⟩ := hs i hi
     have hu' : u=x := IsFunction.unique hu hx
     subst u
     simpa [mulConstruction,he] using hy }
   exact ⟨ha,hb,cseq_value mulConstruction ![a] hseq hv⟩
 · rintro ⟨ha,hb,rfl⟩
   obtain ⟨f,hf,hv⟩ := mulConstruction.result_spec ![a] hb
   refine ⟨ha,hb,mul_mem_omega a b ha hb,∅,SetTheory.succ b,f,rfl,rfl,
    ⟨hf.isFunction,hf.domain_eq⟩,?_,hv,?_,?_⟩
   · simpa [mulConstruction,zero_def] using hf.zero
   · intro i x hi hx
     have he := cseq_value mulConstruction ![a] hf hx
     rw [he]
     exact mul_mem_omega a i ha (hf.index_mem hx)
   · intro i hi
     obtain ⟨x,hx⟩ := hf.exists_value (mem_succ_iff.mpr (Or.inr hi))
     have hxw : x ∈ (ω : V) := by
      rw [cseq_value mulConstruction ![a] hf hx]
      exact mul_mem_omega a i ha (hf.index_mem hx)
     exact ⟨SetTheory.succ i,x,add x a,rfl,hx,hf.succ i hi x hx,hxw,ha,rfl⟩
end PalomarZF192Arithmetic
