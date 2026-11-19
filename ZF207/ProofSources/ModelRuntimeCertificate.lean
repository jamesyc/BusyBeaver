module
public import ModelRuntimeExec
public import ModelRuntimeNormalization
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation M6.Runtime
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
attribute [local irreducible] M207.renamed
lemma model_certificate_sound (br:Branch) (target:SConf→Bool) (fuel:Nat) (start:SConf)
 (checked:(exec M207.renamed br target fuel start false).isSome=true)
 (gap spares:M) (vs:List M) (valid:modelValid br vs) :
 ∃finish,target finish=true ∧ Reaches (modelConc gap vs (spares+1) start)
   (modelConc gap vs (spares+1) finish) := by
 generalize he:exec M207.renamed br target fuel start false=answer at checked
 cases answer with
 | none => simp at checked
 | some finish =>
   obtain ⟨ht,hr⟩:=model_exec_sound gap spares valid fuel start false finish he
   exact ⟨finish,ht,hr⟩
/-- Reuses the exact frozen executable certificate, not a duplicate table or
new abstract simulation premise. Physical output is exactly the target frame. -/
lemma model_certificate_to_frame (br:Branch) (fuel:Nat) (start finish:SConf)
 (checked:(exec M207.renamed br (fun s=>sMatches s finish) fuel start false).isSome=true)
 (gap spares:M) (vs:List M) (valid:modelValid br vs) :
 Reaches (modelConc gap vs (spares+1) start) (modelConc gap vs (spares+1) finish) := by
 obtain ⟨actual,hm,hr⟩:=model_certificate_sound br _ fuel start checked gap spares vs valid
 rw [model_sMatches_conc gap vs (spares+1) hm] at hr
 exact hr
end ZF207.BinaryTape
