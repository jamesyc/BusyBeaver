module
public import ConcreteChallengeCoding
public import ModelPhysicalTerminal
@[expose] public section
namespace PalomarZF209History
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open scoped FFL.FirstOrder.Arithmetic
open ZF209.OmegaInterpretation ZFR.ArithmeticRepresentation
variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "E" => (fun x y : V => x ∈ y)
local notation "A" => arithmeticTranslation.Model V
lemma val_nat (n:Nat) : ((n:A).val)=(n:V) := by
 induction n with
 | zero => simpa only [Nat.cast_zero,cast_zero_def] using (val_zero (V:=V))
 | succ n ih => rw [Nat.cast_succ,val_succ,ih,num_succ_def]
lemma bitCons_raw (bit:Bool) (x y:V) : BitCons E bit x y ↔
 x∈(ω:V) ∧ y=add ((if bit then 1 else 0):V) (mul (2:V) x) := by
 have hc2 : ((2:Nat):V)=(2:V) := (val_nat (V:=V) 2).symm.trans val_two
 simp only [BitCons,numeral_iff,mul_iff,add_iff]
 cases bit <;> simp only [Bool.false_eq_true,ite_false,ite_true,cast_zero_def,cast_one_def,hc2,
  zero_mem_ω,one_mem_ω,two_mem_ω,true_and]
 all_goals
  constructor
  · rintro ⟨b,t,m,rfl,rfl,⟨_,hx,rfl⟩,_,_,rfl⟩; exact ⟨hx,rfl⟩
  · rintro ⟨hx,rfl⟩
    exact ⟨_,_,_,rfl,rfl,⟨two_mem_ω,hx,rfl⟩,by simp,mul_mem_omega _ _ two_mem_ω hx,rfl⟩
lemma bitCons_naturals {bit:Bool} {x y:V} (h:BitCons E bit x y) :
 x∈(ω:V) ∧ y∈(ω:V) := by
 obtain ⟨hx,rfl⟩ := (bitCons_raw _ _ _).mp h
 exact ⟨hx,add_mem_omega _ _ (by cases bit <;> simp) (mul_mem_omega _ _ two_mem_ω hx)⟩
lemma bitCons_iff (bit:Bool) (x y:A) : BitCons E bit x.val y.val ↔
 y=ZF209.BinaryTape.bitValue bit+2*x := by
 rw [bitCons_raw]
 simp only [model_mem_omega,true_and]
 have hb : (ZF209.BinaryTape.bitValue (M:=A) bit).val = (if bit then 1 else 0:V) := by
  cases bit <;> simp [ZF209.BinaryTape.bitValue,val_one,val_zero]
 rw [←hb,←val_two,←val_mul,←val_add]
 exact DirectTranslation.Model.val_inj_iff
lemma row_exact (q:Fin 209)(b:Bool) :
 (if b then (literalRows.getD q.val (none,none)).2 else (literalRows.getD q.val (none,none)).1)=M209.literal q.val b := by
 rfl
noncomputable def liftConf (s:ZF209.BinaryTape.State A) : Conf V := ⟨s.q.val,s.left.val,s.right.val⟩
lemma terminal_iff (s:ZF209.BinaryTape.State A) : Terminal E (liftConf s) ↔
 ∀t,¬ZF209.BinaryTape.literalStep s t := by
 rw [ZF209.BinaryTape.no_literalStep_iff]
 unfold Terminal liftConf
 simp only [numeral_iff,←val_nat,DirectTranslation.Model.val_inj_iff]
lemma valid_lift (s:ZF209.BinaryTape.State A) : Valid E (liftConf s) :=
 ⟨(natObject_iff _).mpr (model_mem_omega _),(natObject_iff _).mpr (model_mem_omega _),
 (natObject_iff _).mpr (model_mem_omega _)⟩
lemma numeral_val_iff (n:Nat)(x:A) : Numeral E n x.val ↔ x=(n:A) := by
 rw [numeral_iff,←val_nat]
 exact DirectTranslation.Model.val_inj_iff
lemma two_bit_expand (b w r:A) : b+2*(w+2*r)=b+2*w+4*r := by
 rw [_root_.mul_add,←_root_.mul_assoc]
 have h:(2:A)*2=4 := by norm_num
 rw [h,_root_.add_assoc]
lemma move_iff (read write dir:Bool)(next:Nat)(s t:ZF209.BinaryTape.State A) :
 Move E read write dir next (liftConf s) (liftConf t) ↔
 ZF209.BinaryTape.move read write dir (next:A) s t := by
 constructor
 · rintro ⟨r,hr,hq,hs⟩
   let rr:A:=ofOmega r (bitCons_naturals hr).1
   have hr' : s.right=ZF209.BinaryTape.bitValue read+2*rr := (bitCons_iff read rr s.right).mp hr
   have hq' : t.q=(next:A) := (numeral_val_iff next t.q).mp hq
   refine ⟨rr,hr',hq',?_⟩
   cases dir with
   | true =>
     exact ⟨(bitCons_iff write s.left t.left).mp hs.1,
       DirectTranslation.Model.val_inj_iff.mp hs.2⟩
   | false =>
     obtain ⟨l,bit,middle,hl,htl,hm,htr⟩ := hs
     let ll:A:=ofOmega l (bitCons_naturals hl).1
     let mm:A:=ofOmega middle (bitCons_naturals hm).2
     have hm' : mm=ZF209.BinaryTape.bitValue write+2*rr := (bitCons_iff write rr mm).mp hm
     refine ⟨ll,ZF209.BinaryTape.bitValue bit,ZF209.BinaryTape.bitValue_cases bit,
       (bitCons_iff bit ll s.left).mp hl,DirectTranslation.Model.val_inj_iff.mp htl,?_⟩
     rw [(bitCons_iff bit mm t.right).mp htr,hm',two_bit_expand]
 · rintro ⟨r,hr,hq,hs⟩
   refine ⟨r.val,(bitCons_iff read r s.right).mpr hr,(numeral_val_iff next t.q).mpr hq,?_⟩
   cases dir with
   | true => exact ⟨(bitCons_iff write s.left t.left).mpr hs.1,congrArg DirectTranslation.Model.val hs.2⟩
   | false =>
     obtain ⟨l,b,hb,hl,htl,htr⟩ := hs
     have hb' : ∃bit:Bool,b=ZF209.BinaryTape.bitValue bit := by
      rcases hb with hb|hb
      · exact ⟨false,hb⟩
      · exact ⟨true,hb⟩
     obtain ⟨bit,rfl⟩ := hb'
     let m:A:=ZF209.BinaryTape.bitValue write+2*r
     refine ⟨l.val,bit,m.val,(bitCons_iff bit l s.left).mpr hl,
       congrArg DirectTranslation.Model.val htl,(bitCons_iff write r m).mpr rfl,?_⟩
     apply (bitCons_iff bit m t.right).mpr
     exact htr.trans (two_bit_expand _ _ _).symm
lemma step_iff (s t:ZF209.BinaryTape.State A) : Step E (liftConf s) (liftConf t) ↔
 ZF209.BinaryTape.literalStep s t := by
 constructor
 · rintro ⟨_,_,q,hq,read,write,dir,next,hrow,hm⟩
   exact ⟨q.val,q.isLt,(numeral_val_iff q.val s.q).mp hq,read,write,dir,next,
    (row_exact q read) ▸ hrow,(move_iff read write dir next s t).mp hm⟩
 · rintro ⟨q,hb,hq,read,write,dir,next,hrow,hm⟩
   refine ⟨valid_lift s,valid_lift t,⟨q,hb⟩,(numeral_val_iff q s.q).mpr hq,
    read,write,dir,next,?_,(move_iff read write dir next s t).mpr hm⟩
   rw [row_exact]; exact hrow
lemma liftConf_surjective {s:Conf V} (h:Valid E s) :
 ∃t:ZF209.BinaryTape.State A,s=liftConf t := by
 refine ⟨⟨ofOmega s.q ((natObject_iff _).mp h.1),
  ofOmega s.left ((natObject_iff _).mp h.2.1),ofOmega s.right ((natObject_iff _).mp h.2.2)⟩,?_⟩
 cases s; rfl
lemma numericStep_iff (before after:A) : NumericStep E before.val after.val ↔
 ZF209.BinaryTape.codedStep before after := by
 constructor
 · rintro ⟨s,t,hs,ht,hstep⟩
   obtain ⟨s',rfl⟩ := liftConf_surjective hstep.1
   obtain ⟨t',rfl⟩ := liftConf_surjective hstep.2.1
   exact ⟨s',t',(numericConfCode_iff _ _ _ _).mp hs,
    (numericConfCode_iff _ _ _ _).mp ht,(step_iff _ _).mp hstep⟩
 · rintro ⟨s,t,hs,ht,hstep⟩
   exact ⟨liftConf s,liftConf t,(numericConfCode_iff _ _ _ _).mpr hs,
    (numericConfCode_iff _ _ _ _).mpr ht,(step_iff _ _).mpr hstep⟩
end PalomarZF209History
