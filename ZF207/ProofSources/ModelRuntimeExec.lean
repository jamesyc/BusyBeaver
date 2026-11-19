module
public import ModelRuntimeStep
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation M6.Runtime
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
attribute [local irreducible] M207.renamed
/-- Existing finite symbolic certificates now expand into actual physical
histories in every PA model, including their internally sized run/box macros.
The fuel here is certificate size, not simulated runtime. -/
lemma model_exec_sound {br:Branch} {tgt:SConf→Bool} (gap spares:M) {vs:List M}
 (hv:modelValid br vs) : ∀(fuel:Nat)(s:SConf)(moved:Bool)(out:SConf),
 exec M207.renamed br tgt fuel s moved=some out → tgt out=true ∧
 Reaches (modelConc gap vs (spares+1) s) (modelConc gap vs (spares+1) out)
 | 0,_,_,_,h => by simp [exec] at h
 | fuel+1,s,moved,out,h => by
   simp only [exec] at h
   split at h
   · rename_i ht
     simp only [Option.some.injEq] at h
     subst h
     simp only [Bool.and_eq_true] at ht
     exact ⟨ht.2,Reaches.refl _⟩
   · split at h
     · simp at h
     · rename_i next advanced hs
       obtain ⟨hg,hr⟩:=model_exec_sound gap spares hv fuel next (moved||advanced) out h
       exact ⟨hg,(model_sstep_sound gap spares hs hv).trans hr⟩
end ZF207.BinaryTape
