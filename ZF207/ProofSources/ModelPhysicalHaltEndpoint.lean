module
public import ModelRuntimeCertificate
public import ModelPhysicalNatEquivalence
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation M6.Runtime
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literal_halt_no_step (s:State M) (hq:s.q=(207:M)) : ∀t,¬literalStep s t := by
 intro t hs
 rcases hs with ⟨q,hb,he,rest⟩
 have hn:(207:Nat)=q := model_natCast_strictMono.injective (hq.symm.trans he)
 omega
lemma literal_halt_no_coded_step (s:State M) (hq:s.q=(207:M)) : ∀next,¬codedStep (stateCode s) next := by
 rintro next ⟨t,u,ht,hu,hs⟩
 have he:s=t:=stateCode_injective ht
 subst t
 exact literal_halt_no_step s hq u hs
lemma modelConc_halt_control (gap spares:M) (vs:List M) (s:SConf)
 (hq:s.1=M207.inverse 207) : (modelConc gap vs spares s).q=(207:M) := by
 rcases s with ⟨q,onl,l,r⟩
 simp only at hq
 subst q
 cases onl <;> simp only [modelConc,namedLeft,namedState,M207.forward_inverse] <;> norm_num
/-- An actual checked halt certificate produces a physical terminal history,
for arbitrary model-sized frame data. -/
lemma model_certificate_halts (br:Branch) (fuel:Nat) (start:SConf)
 (checked:(exec M207.renamed br (fun s=>s.1==M207.inverse 207) fuel start false).isSome=true)
 (gap spares:M) (vs:List M) (valid:modelValid br vs)
 (hist:M) (hh:runHistory blankCode hist)
 (he:modelListHead hist=stateCode (modelConc gap vs (spares+1) start)) : physicalHalts (M:=M) := by
 obtain ⟨finish,hf,hr⟩:=model_certificate_sound br _ fuel start checked gap spares vs valid
 have hq:finish.1=M207.inverse 207 := by simpa using hf
 obtain ⟨out,ho,hend⟩:=hr blankCode hist hh he
 refine ⟨out,ho,?_⟩
 rw [hend]
 exact literal_halt_no_coded_step _ (modelConc_halt_control gap (spares+1) vs finish hq)
end ZF207.BinaryTape
