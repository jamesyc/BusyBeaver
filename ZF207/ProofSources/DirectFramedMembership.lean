module
public import DirectFramedContexts
@[expose] public section
namespace RosserDirect.Membership
open Turing
set_option backward.isDefEq.respectTransparency false

/-- The empty context terminator is simply an extra empty candidate frame.
Formula payloads are nonempty, so it can never produce a false match. This
reuses the existing concrete membership machine without a new parser. -/
theorem lookup_framed_context (p : ZFR.Formula) (Γ : ZFR.Context)
 (v : Option Symbol) (src : List Symbol) :
 ∃ rest, TM2.Reaches machine
 (cfg .next v (formulaPayload p ++ .frameEnd :: src) [] (FramedContext.encode Γ))
 (cfg (if p ∈ Γ then .found else .absent) none (formulaPayload p ++ .frameEnd :: src) [] rest) := by
 have valid : ∀ q ∈ Γ.map formulaPayload ++ [[]], ∀ x ∈ q, x ≠ .frameEnd := by
   intro q hq
   rcases List.mem_append.mp hq with hq | hq
   · obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hq
     exact payloadBits_no_end _
   · simp only [List.mem_singleton] at hq
     subst q
     simp
 have h := lookup_frames (formulaPayload p) (Γ.map formulaPayload ++ [[]]) (payloadBits_no_end _) valid v src
 have same : formulaPayload p ∈ Γ.map formulaPayload ++ [[]] ↔ p ∈ Γ := by
   rw [List.mem_append,List.mem_singleton]
   have hn := FramedContext.formula_nonempty p
   constructor
   · intro hp
     rcases hp with hp | hp
     · obtain ⟨q,hq,he⟩ := List.mem_map.mp hp
       exact formulaPayload_injective he ▸ hq
     · exact False.elim (hn hp)
   · intro hp
     exact Or.inl (List.mem_map.mpr ⟨p,hp,rfl⟩)
 simpa [same,frames,List.flatMap_append,FramedContext.encode,contextFrames] using h
end RosserDirect.Membership
