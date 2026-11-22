module
public import ZF192.Palomar.LinkedRun
@[expose] public section
namespace PalomarZF192History
open PalomarZF192Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open ZF192Support.OmegaInterpretation ZFR.ArithmeticRepresentation
open scoped FFL.FirstOrder.Arithmetic
variable {V:Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "A" => arithmeticTranslation.Model V
local notation "E" => (fun x y:V=>x∈y)
lemma blankCode_zero : ZF192.BinaryTape.blankCode (M:=A)=0 := by
 simp only [ZF192.BinaryTape.blankCode,ZF192.BinaryTape.stateCode,modelCantor_zero]
/-- The standalone predicate agrees with the original exact machine in every
ZF model, including nonstandard internal times and histories. -/
lemma internalLinkedHalts_iff : InternalLinkedHalts E ↔ ZF192.BinaryTape.physicalHalts (M:=A) := by
 rw [ZF192.BinaryTape.physicalHalts_terminal_iff]
 constructor
 · rintro ⟨zero,hist,last,t,hzero,hr,hh,hcode,hvalid,hterminal⟩
   have hz:zero=(0:A).val:=by rw [(empty_iff _).mp hzero,val_zero,zero_def]
   subst zero
   let h:A:=ofOmega hist ((natObject_iff hist).mp hr.2.1)
   let l:A:=ofOmega last (head_natural hh)
   obtain ⟨s,rfl⟩:=liftConf_surjective hvalid
   have hrun:ZF192.BinaryTape.runHistory 0 h:=(linkedRun_iff 0 h).mp hr
   have hhead:l=modelListHead h:=(listHead_iff h l).mp hh
   have hc:l=ZF192.BinaryTape.stateCode s:=(numericConfCode_iff s.q s.left s.right l).mp hcode
   refine ⟨h,s,?_,hhead.symm.trans hc,?_⟩
   · rwa [blankCode_zero]
   · exact (ZF192.BinaryTape.no_literalStep_iff s).mp ((terminal_iff s).mp hterminal)
 · rintro ⟨hist,s,hr,hhead,ht⟩
   have hrun:ZF192.BinaryTape.runHistory 0 hist:=by simpa only [blankCode_zero] using hr
   refine ⟨(0:A).val,hist.val,(modelListHead hist).val,liftConf s,
    (empty_val_iff 0).mpr rfl,(linkedRun_iff 0 hist).mpr hrun,
    (listHead_iff hist _).mpr rfl,?_,valid_lift s,?_⟩
   · exact (numericConfCode_iff s.q s.left s.right _).mpr hhead
   · exact (terminal_iff s).mpr ((ZF192.BinaryTape.no_literalStep_iff s).mpr ht)
end PalomarZF192History
