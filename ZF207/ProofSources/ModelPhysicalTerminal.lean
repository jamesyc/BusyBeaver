module
public import ModelPhysicalNatEquivalence
public import ModelBinaryUncons
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literal_rows_total : ∀q:Fin 207,∀b:Bool,(M207.literal q b).isSome=true := by decide +kernel
lemma move_exists (s:State M) (read write dir:Bool) (next r:M)
 (hr:s.right=bitValue read+2*r) : ∃t:State M,move read write dir next s t := by
 cases dir with
 | true => exact ⟨⟨next,bitValue write+2*s.left,r⟩,r,hr,rfl,rfl,rfl⟩
 | false =>
  obtain ⟨b,l,hl⟩:=bits_surjective s.left
  exact ⟨⟨next,l,bitValue b+2*bitValue write+4*r⟩,r,hr,rfl,l,bitValue b,bitValue_cases b,hl,rfl,rfl⟩
lemma literalStep_exists_iff (s:State M) : (∃t,literalStep s t) ↔ ∃q:Fin 207,s.q=(q.val:M) := by
 constructor
 · rintro ⟨t,q,hq,hs,rest⟩; exact ⟨⟨q,hq⟩,hs⟩
 · rintro ⟨q,hq⟩
   obtain ⟨b,r,hr⟩:=bits_surjective s.right
   have ht:=literal_rows_total q b
   cases he:M207.literal q.val b with
   | none => simp [he] at ht
   | some row =>
    rcases row with ⟨w,d,n⟩
    obtain ⟨t,hm⟩:=move_exists s b w d (n:M) r hr
    exact ⟨t,q.val,q.isLt,hq,b,w,d,n,he,hm⟩
lemma no_literalStep_iff (s:State M) : (∀t,¬literalStep s t) ↔ ∀q:Fin 207,s.q≠(q.val:M) := by
 simpa only [not_exists] using not_congr (literalStep_exists_iff s)
lemma codedStep_from_state_iff (s:State M) :
 (∃after,codedStep (stateCode s) after) ↔ ∃t,literalStep s t := by
 constructor
 · rintro ⟨after,u,t,hu,ht,hs⟩
   have he:s=u:=stateCode_injective hu
   subst u; exact ⟨t,hs⟩
 · rintro ⟨t,ht⟩; exact ⟨stateCode t,s,t,rfl,rfl,ht⟩
lemma no_codedStep_from_state_iff (s:State M) :
 (∀after,¬codedStep (stateCode s) after) ↔ ∀q:Fin 207,s.q≠(q.val:M) := by
 have h := (codedStep_from_state_iff s).trans (literalStep_exists_iff s)
 simpa only [not_exists] using not_congr h
lemma runHistory_head_state (hist:M) (hh:runHistory blankCode hist) :
 ∃s:State M,modelListHead hist=stateCode s := by
 have hp:0<hist:=pos_iff_ne_zero.mpr hh.1
 have hr:=modelList_reconstruct hist hp
 have ht:modelTrace (runEdge blankCode) (modelListCons (modelListHead hist) (modelListTail hist)) := by
  rw [hr]; exact hh.2
 have he:=((modelTrace_cons (runEdge blankCode) (modelListHead hist) (modelListTail hist)).mp ht).2
 rcases he with ⟨_,h⟩|⟨_,s,t,hs,ht,hstep⟩
 · exact ⟨⟨0,0,0⟩,h⟩
 · exact ⟨t,ht⟩
theorem physicalHalts_terminal_iff : physicalHalts (M:=M) ↔
 ∃hist:M,∃s:State M,runHistory blankCode hist ∧ modelListHead hist=stateCode s ∧
 ∀q:Fin 207,s.q≠(q.val:M) := by
 constructor
 · rintro ⟨hist,hh,hstop⟩
   obtain ⟨s,hs⟩:=runHistory_head_state hist hh
   refine ⟨hist,s,hh,hs,(no_codedStep_from_state_iff s).mp ?_⟩
   rwa [←hs]
 · rintro ⟨hist,s,hh,hs,ht⟩
   refine ⟨hist,hh,?_⟩
   rw [hs]; exact (no_codedStep_from_state_iff s).mpr ht
end ZF207.BinaryTape
