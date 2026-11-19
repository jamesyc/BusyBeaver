module
public import ModelRuntimePeel
public import ModelRuntimeOracle
public import ModelRuntimeBoxHead
public import ModelPhysicalWriteRightScan
public import ModelPhysicalWriteLeftScan
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
set_option maxHeartbeats 200000
attribute [local irreducible] M207.renamed
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation M6.Runtime
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma model_sstep_sound {br : Branch} {s s' : SConf} {m : Bool} (n spares:M) {vs:List M}
 (h:sstep M207.renamed br s=some (s',m)) (hv:modelValid br vs) :
 Reaches (modelConc n vs (spares+1) s) (modelConc n vs (spares+1) s') := by
  obtain ⟨q, onl, l, r⟩ := s
  cases onl with
  | true =>
      cases l with
      | nil =>
          simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have e : modelConc n vs (spares+1) (q,true,[],r) = modelConc n vs (spares+1) (q,false,[],.bit false::r) := by
            have ht := tailBits_cons (M:=M) false 0
            have hb := lowBit_cons (M:=M) false 0
            simp only [bitValue,Bool.false_eq_true,ite_false,mul_zero,zero_add] at ht hb
            simp only [modelConc,modelFlat_nil,modelFlat_cons,modelSeg,namedLeft,ht,hb,bitValue,Bool.false_eq_true,ite_false,zero_add]
          rw [e]; exact Reaches.refl _
      | cons x l =>
          cases x with
          | bit x =>
              simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [modelConc,modelFlat_cons,modelSeg,namedLeft_cons]
              exact Reaches.refl _
          | box x => simp [sstep] at h
          | run b a c =>
              have hp : ∀ {s'' : SConf} {m' : Bool}, peelLeft q b a c l r = some (s'', m') →
                  Reaches (modelConc n vs (spares+1) (q,true,.run b a c::l,r)) (modelConc n vs (spares+1) s'') := fun hp => by
                have e:=model_peelLeft_sound n (spares+1) vs hp
                rw [e]; exact Reaches.refl _
              simp only [sstep] at h
              split at h
              · rename_i w q2 hm
                split at h
                · rename_i hq
                  subst hq
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  
                  simp only [modelConc,modelFlat_cons,modelSeg]
                  exact named_write_scan_left _ b w hm _ _ _
                · exact hp h
              · exact hp h
  | false =>
      cases r with
      | nil => simp [sstep] at h
      | cons x r =>
          cases x with
          | bit x =>
              simp only [sstep] at h
              split at h
              · rename_i w q2 hm
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                simp only [modelConc,modelFlat_cons,modelSeg]
                exact named_right q q2 x w _ _ hm
              · rename_i w q2 hm
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                simp only [modelConc,modelFlat_cons,modelSeg]
                exact named_left_any q q2 x w _ _ hm
              · simp at h
          | run b a c =>
              have hp : ∀ {s'' : SConf} {m' : Bool}, peelRight q b a c l r = some (s'', m') →
                  Reaches (modelConc n vs (spares+1) (q,false,l,.run b a c::r)) (modelConc n vs (spares+1) s'') := fun hp => by
                have e:=model_peelRight_sound n (spares+1) vs hp
                rw [e]; exact Reaches.refl _
              simp only [sstep] at h
              split at h
              · rename_i w q2 hm
                split at h
                · rename_i hq
                  subst hq
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  
                  simp only [modelConc,modelFlat_cons,modelSeg]
                  exact named_write_scan_right _ b w _ _ _ hm
                · exact hp h
              · exact hp h
          | box x =>
              cases r with
              | cons y r => simp [sstep] at h
              | nil =>
                  simp only [sstep] at h
                  split at h
                  · rename_i q2 x2 extra ho
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    
                    have := model_oracle_sound (modelFlat n vs (spares+1) l) spares ho hv
                    cases extra <;>
                      simpa [modelConc,modelFlat_cons,modelFlat_nil,modelSeg,bitValue] using this
                  · split at h
                    · rename_i q2 hm
                      simp only [Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      obtain ⟨t,ht⟩:=model_box_head vs (spares+1) x hv.1
                      simp only [modelConc,modelFlat_cons,modelFlat_nil,modelSeg,ht]
                      simpa only [bitValue,Bool.false_eq_true,ite_false,zero_add] using named_left_any q q2 false false (modelFlat n vs (spares+1) l) t hm
                    · simp at h

end ZF207.BinaryTape
