module
public import ModelRuntimeEncoding
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation M6.Runtime
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma model_peelLeft_sound {q:Nat} {b:Bool} {a c:Nat} {l r:List Seg} {s':SConf} {m:Bool}
 (gap spares:M) (values:List M) (h:peelLeft q b a c l r=some (s',m)) :
 modelConc gap values spares (q,true,.run b a c::l,r)=modelConc gap values spares s' := by
 unfold peelLeft at h
 split at h
 · simp only [Option.some.injEq,Prod.mk.injEq] at h
   obtain ⟨rfl,rfl⟩:=h
   simp [modelConc,modelFlat_cons,modelSeg,←add_assoc,bitRun_succ]
 · simp only [Option.some.injEq,Prod.mk.injEq] at h
   obtain ⟨rfl,rfl⟩:=h
   simp [modelConc,modelFlat_cons,modelSeg,bitRun_zero]
 · simp at h
lemma model_peelRight_sound {q:Nat} {b:Bool} {a c:Nat} {l r:List Seg} {s':SConf} {m:Bool}
 (gap spares:M) (values:List M) (h:peelRight q b a c l r=some (s',m)) :
 modelConc gap values spares (q,false,l,.run b a c::r)=modelConc gap values spares s' := by
 unfold peelRight at h
 split at h
 · simp only [Option.some.injEq,Prod.mk.injEq] at h
   obtain ⟨rfl,rfl⟩:=h
   simp [modelConc,modelFlat_cons,modelSeg,←add_assoc,bitRun_succ]
 · simp only [Option.some.injEq,Prod.mk.injEq] at h
   obtain ⟨rfl,rfl⟩:=h
   simp [modelConc,modelFlat_cons,modelSeg,bitRun_zero]
 · simp at h
end ZF207.BinaryTape
