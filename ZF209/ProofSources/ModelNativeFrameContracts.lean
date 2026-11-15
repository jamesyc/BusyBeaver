module
public import ModelNativeFrameEffects
public import ModelRuntimeCertificate
public import ModelPhysicalHaltEndpoint
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation M6.Runtime M209.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
attribute [local irreducible] M209.renamed
def FrameImplements (pc:Nat) (code:Instruction) : Prop :=
 match code with
 | .inc r k => ∃hr:r<9,∀(gap spares:M)(regs:Fin 9→M),
   Reaches (nativeFrame pc gap regs (spares+1))
    (nativeFrame k gap (incrementRegisters regs ⟨r,hr⟩) (spares+2))
 | .dec r z p => ∃hr:r<9,∀(gap spares:M)(regs:Fin 9→M),
   (regs ⟨r,hr⟩=0 → Reaches (nativeFrame pc gap regs (spares+1)) (nativeFrame z gap regs (spares+1))) ∧
   (regs ⟨r,hr⟩≠0 → Reaches (nativeFrame pc gap regs (spares+1)) (nativeFrame p (gap+1) (decrementRegisters regs ⟨r,hr⟩) (spares+1)))
 | .jump k => ∀(gap spares:M)(regs:Fin 9→M),
   Reaches (nativeFrame pc gap regs (spares+1)) (nativeFrame k gap regs (spares+1))
 | .halt => ∀(gap spares:M)(regs:Fin 9→M)(hist:M),runHistory blankCode hist →
   modelListHead hist=stateCode (nativeFrame pc gap regs (spares+1)) → physicalHalts (M:=M)
lemma primaryList_getD (regs:Fin 9→M) (r:Nat) (hr:r<9) : (primaryList regs).getD r 0=regs ⟨r,hr⟩ := by
 have hh:r=0∨r=1∨r=2∨r=3∨r=4∨r=5∨r=6∨r=7∨r=8:=by omega
 rcases hh with h|h|h|h|h|h|h|h|h <;> subst r <;> rfl
lemma primaryList_valid_none (regs:Fin 9→M) : modelValid none (primaryList regs) := ⟨rfl,trivial⟩
lemma model_contract_inc (pc r k fuel:Nat) (hpc:(paths pc).length≤48) (hk:(paths k).length≤48) (hr:r<9)
 (hc:(exec M209.renamed none (fun s=>sMatches s (rootFrame (paths k) 0 (.inc r))) fuel (rootFrame (paths pc)) false).isSome=true) :
 FrameImplements (M:=M) pc (.inc r k) := by
 refine ⟨hr,?_⟩
 intro gap spares regs
 have h:=model_certificate_to_frame none fuel (rootFrame (paths pc)) (rootFrame (paths k) 0 (.inc r)) hc gap spares (primaryList regs) (primaryList_valid_none regs)
 rw [root_frame_none pc 0 hpc,root_frame_inc k 0 hk gap (spares+1) regs ⟨r,hr⟩] at h
 simpa only [Nat.cast_zero,add_zero,add_assoc,show (1:M)+1=2 by norm_num] using h
lemma model_contract_jump (pc k fuel:Nat) (hpc:(paths pc).length≤48) (hk:(paths k).length≤48)
 (hc:(exec M209.renamed none (fun s=>sMatches s (rootFrame (paths k))) fuel (rootFrame (paths pc)) false).isSome=true) :
 FrameImplements (M:=M) pc (.jump k) := by
 intro gap spares regs
 have h:=model_certificate_to_frame none fuel (rootFrame (paths pc)) (rootFrame (paths k)) hc gap spares (primaryList regs) (primaryList_valid_none regs)
 rw [root_frame_none pc 0 hpc,root_frame_none k 0 hk] at h
 simpa only [Nat.cast_zero,add_zero] using h
lemma model_contract_dec (pc r z p fz fp:Nat) (hpc:(paths pc).length≤48) (hz:(paths z).length≤48) (hp:(paths p).length≤48) (hr:r<9)
 (cz:(exec M209.renamed (some (r,true)) (fun s=>sMatches s (rootFrame (paths z))) fz (rootFrame (paths pc)) false).isSome=true)
 (cp:(exec M209.renamed (some (r,false)) (fun s=>sMatches s (rootFrame (paths p) 1 (.dec r))) fp (rootFrame (paths pc)) false).isSome=true) :
 FrameImplements (M:=M) pc (.dec r z p) := by
 refine ⟨hr,?_⟩
 intro gap spares regs
 constructor
 · intro he
   have hv:modelValid (some (r,true)) (primaryList regs) := ⟨rfl,by change (primaryList regs).getD r 0=0; rw [primaryList_getD regs r hr]; exact he⟩
   have h:=model_certificate_to_frame (some (r,true)) fz (rootFrame (paths pc)) (rootFrame (paths z)) cz gap spares (primaryList regs) hv
   rw [root_frame_none pc 0 hpc,root_frame_none z 0 hz] at h
   simpa only [Nat.cast_zero,add_zero] using h
 · intro he
   have hv:modelValid (some (r,false)) (primaryList regs) := ⟨rfl,by change (primaryList regs).getD r 0≠0; rw [primaryList_getD regs r hr]; exact he⟩
   have h:=model_certificate_to_frame (some (r,false)) fp (rootFrame (paths pc)) (rootFrame (paths p) 1 (.dec r)) cp gap spares (primaryList regs) hv
   rw [root_frame_none pc 0 hpc,root_frame_dec p 1 hp gap (spares+1) regs ⟨r,hr⟩] at h
   simpa only [Nat.cast_zero,Nat.cast_one,add_zero] using h
lemma model_contract_halt (pc fuel:Nat) (hpc:(paths pc).length≤48)
 (hc:(exec M209.renamed none (fun s=>s.1==M209.inverse 209) fuel (rootFrame (paths pc)) false).isSome=true) :
 FrameImplements (M:=M) pc .halt := by
 intro gap spares regs hist hh he
 apply model_certificate_halts none fuel (rootFrame (paths pc)) hc gap spares (primaryList regs) (primaryList_valid_none regs) hist hh
 simpa only [root_frame_none pc 0 hpc,Nat.cast_zero,add_zero] using he
end ZF209.BinaryTape
