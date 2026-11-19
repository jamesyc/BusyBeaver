module
public import ConcreteChallengeTailGraph
public import ConcreteChallengeTransition
@[expose] public section
namespace PalomarZF207History
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open ZF207.OmegaInterpretation ZFR.ArithmeticRepresentation
open scoped FFL.FirstOrder.Arithmetic
variable {V:Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "A" => arithmeticTranslation.Model V
local notation "E" => (fun x y:V=>x∈y)
lemma head_natural {x a:V} (h:ListHead E x a) : a∈(ω:V) := by
 rcases h with ⟨hx,ha⟩|⟨b,hb⟩
 · rw [(empty_iff a).mp ha];exact zero_mem_ω
 · exact (listCons_naturals hb).1
lemma tail_natural {x b:V} (h:ListTail E x b) : b∈(ω:V) := by
 rcases h with ⟨hx,hb⟩|⟨a,ha⟩
 · rw [(empty_iff b).mp hb];exact zero_mem_ω
 · exact (listCons_naturals ha).2.1
lemma linkedRun_iff_trace (initial c:A) : LinkedRun E initial.val c.val ↔
 c≠0 ∧ modelTrace (fun a b:A=>RunEdge E initial.val a.val b.val) c := by
 constructor
 · rintro ⟨_,_,hc,zero,domain,f,hzero,hdom,hf,hstart,hend,hr,hs⟩
   have hz:zero=(0:A).val:=by rw [(empty_iff zero).mp hzero,val_zero,zero_def]
   have hd:domain=SetTheory.succ c.val:=(succ_iff _ _).mp hdom
   subst zero;subst domain
   have hu:=internal_tail_function_unique c f hf hstart hr (fun i hi=>by
    obtain ⟨j,x,y,hj,hx,hy,ht,_⟩:=hs i hi
    exact ⟨j,x,y,hj,hx,hy,ht⟩)
   refine ⟨fun he=>hc ((empty_val_iff c).mpr he),?_,?_⟩
   · exact (hu c 0 hend).symm
   · intro i hi
     obtain ⟨j,x,y,hj,hx,hy,ht,he⟩:=hs i.val ((lt_iff_mem i c).mp hi)
     have hxw: x∈(ω:V):=(natObject_iff x).mp (hr i.val x (mem_succ_iff.mpr (Or.inr ((lt_iff_mem i c).mp hi))) hx)
     let xx:A:=ofOmega x hxw
     have hxe:xx=modelTailIter i c:=hu i xx hx
     rcases he with he|⟨a,b,ha,hb,he⟩
     · exact Or.inl (hxe.symm.trans ((empty_val_iff xx).mp he))
     · let aa:A:=ofOmega a (head_natural ha)
       let bb:A:=ofOmega b (tail_natural hb)
       have hae:aa=modelListHead xx:=(listHead_iff xx aa).mp ha
       have hbe:bb=modelListTail xx:=(listTail_iff xx bb).mp hb
       have hh:RunEdge E initial.val aa.val bb.val:=he
       rw [hae,hbe,hxe] at hh
       exact Or.inr hh
 · rintro ⟨hc,hstop,htrace⟩
   obtain ⟨f,hf,hgraph⟩:=internal_tail_function_exists c
   have hat (i x:A) (hi:i.val∈SetTheory.succ c.val) (he:x=modelTailIter i c) : At E f i.val x.val:=
    (hgraph i.val x.val).mpr ⟨hi,model_mem_omega x,(tailIterSet_eval x i c).mpr he⟩
   refine ⟨(natObject_iff _).mpr (model_mem_omega initial),(natObject_iff _).mpr (model_mem_omega c),
    fun he=>hc ((empty_val_iff c).mp he),(0:A).val,SetTheory.succ c.val,f,
    (empty_val_iff 0).mpr rfl,(succ_iff _ _).mpr rfl,hf,?_,?_,?_,?_⟩
   · apply hat 0 c
     · rw [val_zero]
       apply mem_succ_iff.mpr
       rcases omega_lt_trichotomy 0 c.val zero_mem_ω (model_mem_omega c) with h|h|h
       · exact Or.inr h
       · exact Or.inl h
       · exact False.elim (omega_zero_le c.val (model_mem_omega c) h)
     · exact (modelTailIter_zero c).symm
   · exact hat c 0 (mem_succ_self _) hstop.symm
   · intro i x hi hx
     exact (natObject_iff x).mpr ((hgraph i x).mp hx).2.1
   · intro i hi
     have hiw:i∈(ω:V):=IsTransitive.ω.mem_trans hi (model_mem_omega c)
     let ii:A:=ofOmega i hiw
     let xx:A:=modelTailIter ii c
     let yy:A:=modelListTail xx
     have hii:ii<c:=(lt_iff_mem ii c).mpr hi
     have hjs:(ii+1).val∈SetTheory.succ c.val:=by
      rw [val_succ]
      exact omega_succ_lt_succ i c.val hiw (model_mem_omega c) hi
     refine ⟨(ii+1).val,xx.val,yy.val,(succ_iff _ _).mpr (val_succ ii),
      hat ii xx (mem_succ_iff.mpr (Or.inr hi)) rfl,hat (ii+1) yy hjs ?_,
      (listTail_iff xx yy).mpr rfl,?_⟩
     · exact (modelTailIter_succ ii c).symm
     · rcases htrace ii hii with hz|he
       · exact Or.inl ((empty_val_iff xx).mpr hz)
       · exact Or.inr ⟨(modelListHead xx).val,(modelListTail xx).val,
          (listHead_iff xx _).mpr rfl,(listTail_iff xx _).mpr rfl,he⟩
lemma runEdge_iff (initial next tail:A) : RunEdge E initial.val next.val tail.val ↔
 ZF207.BinaryTape.runEdge initial next tail := by
 simp only [RunEdge,ZF207.BinaryTape.runEdge,empty_val_iff,DirectTranslation.Model.val_inj_iff]
 constructor
 · rintro (h|⟨hn,p,hp,hs⟩)
   · exact Or.inl h
   · let pp:A:=ofOmega p (head_natural hp)
     have he:pp=modelListHead tail:=(listHead_iff tail pp).mp hp
     have hh:ZF207.BinaryTape.codedStep pp next:=(numericStep_iff pp next).mp hs
     exact Or.inr ⟨hn,he ▸ hh⟩
 · rintro (h|⟨hn,hs⟩)
   · exact Or.inl h
   · exact Or.inr ⟨hn,(modelListHead tail).val,(listHead_iff tail _).mpr rfl,
      (numericStep_iff _ next).mpr hs⟩
lemma linkedRun_iff (initial c:A) : LinkedRun E initial.val c.val ↔
 ZF207.BinaryTape.runHistory initial c := by
 rw [linkedRun_iff_trace]
 simp only [ZF207.BinaryTape.runHistory,modelTrace,runEdge_iff]
end PalomarZF207History
