module
public import ModelRuntimeCertificate
public import ModelPhysicalNatEquivalence
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation M6.Runtime
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literal_halt_no_step (s:State M) (hq:s.q=(209:M)) : ∀t,¬literalStep s t := by
 intro t hs
 rcases hs with ⟨q,hb,he,rest⟩
 have hn:(209:Nat)=q := model_natCast_strictMono.injective (hq.symm.trans he)
 omega
lemma literal_halt_no_coded_step (s:State M) (hq:s.q=(209:M)) : ∀next,¬codedStep (stateCode s) next := by
 rintro next ⟨t,u,ht,hu,hs⟩
 have he:s=t:=stateCode_injective ht
 subst t
 exact literal_halt_no_step s hq u hs
lemma modelConc_halt_control (gap spares:M) (vs:List M) (s:SConf)
 (hq:s.1=M209.inverse 209) : (modelConc gap vs spares s).q=(209:M) := by
 rcases s with ⟨q,onl,l,r⟩
 simp only at hq
 subst q
 cases onl <;> simp only [modelConc,namedLeft,namedState,M209.forward_inverse] <;> norm_num
/-- An actual checked halt certificate produces a physical terminal history,
for arbitrary model-sized frame data. -/
lemma model_certificate_halts (br:Branch) (fuel:Nat) (start:SConf)
 (checked:(exec M209.renamed br (fun s=>s.1==M209.inverse 209) fuel start false).isSome=true)
 (gap spares:M) (vs:List M) (valid:modelValid br vs)
 (hist:M) (hh:runHistory blankCode hist)
 (he:modelListHead hist=stateCode (modelConc gap vs (spares+1) start)) : physicalHalts (M:=M) := by
 obtain ⟨finish,hf,hr⟩:=model_certificate_sound br _ fuel start checked gap spares vs valid
 have hq:finish.1=M209.inverse 209 := by simpa using hf
 obtain ⟨out,ho,hend⟩:=hr blankCode hist hh he
 refine ⟨out,ho,?_⟩
 rw [hend]
 exact literal_halt_no_coded_step _ (modelConc_halt_control gap (spares+1) vs finish hq)
end ZF209.BinaryTape
