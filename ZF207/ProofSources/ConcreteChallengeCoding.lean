module
public import ConcreteChallengeArithmetic
public import ConcreteArithmeticPeano
public import ExactTailIterationModel
@[expose] public section
namespace PalomarZF207History
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open scoped FFL.FirstOrder.Arithmetic
open ZF207.OmegaInterpretation ZFR.ArithmeticRepresentation
variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "E" => (fun x y : V => x ∈ y)
local notation "A" => arithmeticTranslation.Model V
lemma cantor_raw (a b c : V) : Cantor E a b c ↔
 a ∈ (ω : V) ∧ b ∈ (ω : V) ∧ c ∈ (ω : V) ∧
 mul (2:V) c = add (mul (add a b) (SetTheory.succ (add a b))) (mul (2:V) b) := by
 simp only [Cantor,natObject_iff,numeral_iff,add_iff,mul_iff,succ_iff]
 constructor
 · rintro ⟨ha,hb,hc,two,s,n,p,tb,tc,total,rfl,⟨_,_,rfl⟩,rfl,⟨_,_,rfl⟩,
    ⟨_,_,rfl⟩,⟨_,_,rfl⟩,⟨_,_,rfl⟩,he⟩
   exact ⟨ha,hb,hc,he⟩
 · rintro ⟨ha,hb,hc,he⟩
   have h2 : (2:V) ∈ (ω:V) := two_mem_ω
   have hs := add_mem_omega a b ha hb
   have hn := ω_succ_closed hs
   have hp := mul_mem_omega (add a b) (SetTheory.succ (add a b)) hs hn
   have htb := mul_mem_omega (2:V) b h2 hb
   exact ⟨ha,hb,hc,2,add a b,SetTheory.succ (add a b),
    mul (add a b) (SetTheory.succ (add a b)),mul (2:V) b,mul (2:V) c,
    add (mul (add a b) (SetTheory.succ (add a b))) (mul (2:V) b),rfl,
    ⟨ha,hb,rfl⟩,rfl,⟨hs,hn,rfl⟩,⟨h2,hb,rfl⟩,⟨h2,hc,rfl⟩,⟨hp,htb,rfl⟩,he⟩
lemma val_two : (2:A).val = (2:V) := by
 have h := val_add_one (1:A)
 exact (show (2:A).val=SetTheory.succ (1:V) from by
  simpa only [one_add_one_eq_two,val_one] using h).trans (by
   ext x; simp [SetTheory.succ,one_def,two_def,or_comm])
lemma val_succ (x:A) : (x+1).val = SetTheory.succ x.val := val_add_one x
lemma cantor_iff (a b c:A) : Cantor E a.val b.val c.val ↔ c=modelCantor a b := by
 rw [cantor_raw]
 simp only [model_mem_omega,true_and]
 have he : mul (2:V) c.val = add (mul (add a.val b.val)
   (SetTheory.succ (add a.val b.val))) (mul (2:V) b.val) ↔
   2*c=(a+b)*((a+b)+1)+2*b := by
  rw [←val_two,←val_mul,←val_add a b,←val_succ (a+b),←val_mul,←val_mul,←val_add]
  exact DirectTranslation.Model.val_inj_iff
 exact he.trans ⟨fun h=>modelCantor_unique a b c h,fun h=>h ▸ modelCantor_equation a b⟩
lemma listCons_iff (a b c:A) : ListCons E a.val b.val c.val ↔ c=modelListCons a b := by
 constructor
 · rintro ⟨p,hp,hs⟩
   have hn := (cantor_raw _ _ _).mp hp |>.2.2.1
   let pp : A := ofOmega p hn
   have he : pp=modelCantor a b := (cantor_iff a b pp).mp hp
   apply DirectTranslation.Model.val_inj_iff.mp
   change c.val=(modelCantor a b+1).val
   rw [val_succ,←he]
   exact (succ_iff _ _).mp hs
 · intro hc
   refine ⟨(modelCantor a b).val,(cantor_iff _ _ _).mpr rfl,?_⟩
   apply (succ_iff _ _).mpr
   rw [hc]
   exact val_succ (modelCantor a b)
lemma listCons_naturals {a b c:V} (h:ListCons E a b c) :
 a∈(ω:V) ∧ b∈(ω:V) ∧ c∈(ω:V) := by
 obtain ⟨p,hp,hs⟩ := h
 obtain ⟨ha,hb,hp,_⟩ := (cantor_raw _ _ _).mp hp
 exact ⟨ha,hb,((succ_iff _ _).mp hs).symm ▸ ω_succ_closed hp⟩
lemma modelHead_zero : modelListHead (0:A)=0 := by
 have hp : modelPredecessor (0:A)=0 := by
  symm
  apply (predecessorGraph_value _ _).mp
  exact (predecessorGraph_eval _ _).mpr (Or.inl ⟨rfl,rfl⟩)
 rw [modelListHead,hp,←modelCantor_zero,modelUnpairLeft_pair]
 exact modelCantor_zero.symm
lemma empty_val_iff (x:A) : Empty E x.val ↔ x=0 := by
 rw [empty_iff,←zero_def,←val_zero]
 exact DirectTranslation.Model.val_inj_iff
lemma listHead_iff (x a:A) : ListHead E x.val a.val ↔ a=modelListHead x := by
 constructor
 · intro h
   rcases h with ⟨hx,ha⟩ | ⟨b,hb⟩
   · rw [(empty_val_iff x).mp hx,(empty_val_iff a).mp ha,modelHead_zero]
   · let bb : A := ofOmega b (listCons_naturals hb).2.1
     have he : x=modelListCons a bb := (listCons_iff a bb x).mp hb
     rw [he,modelListHead_cons]
 · rintro rfl
   by_cases hx:x=0
   · left; rw [hx,modelHead_zero]; exact ⟨(empty_val_iff _).mpr rfl,(empty_val_iff _).mpr rfl⟩
   · right
     exact ⟨(modelListTail x).val,(listCons_iff _ _ _).mpr
       (modelList_reconstruct x (pos_iff_ne_zero.mpr hx)).symm⟩
lemma listTail_iff (x b:A) : ListTail E x.val b.val ↔ b=modelListTail x := by
 constructor
 · intro h
   rcases h with ⟨hx,hb⟩ | ⟨a,ha⟩
   · rw [(empty_val_iff x).mp hx,(empty_val_iff b).mp hb,modelListTail_zero]
   · let aa : A := ofOmega a (listCons_naturals ha).1
     have he : x=modelListCons aa b := (listCons_iff aa b x).mp ha
     rw [he,modelListTail_cons]
 · rintro rfl
   by_cases hx:x=0
   · left; rw [hx,modelListTail_zero]; exact ⟨(empty_val_iff _).mpr rfl,(empty_val_iff _).mpr rfl⟩
   · right
     exact ⟨(modelListHead x).val,(listCons_iff _ _ _).mpr
       (modelList_reconstruct x (pos_iff_ne_zero.mpr hx)).symm⟩
lemma numericConfCode_iff (q l r c:A) :
 NumericConfCode E ⟨q.val,l.val,r.val⟩ c.val ↔ c=modelCantor q (modelCantor l r) := by
 constructor
 · rintro ⟨lr,h1,h2⟩
   let p : A := ofOmega lr ((cantor_raw _ _ _).mp h1).2.2.1
   have he : p=modelCantor l r := (cantor_iff l r p).mp h1
   have hc := (cantor_iff q p c).mp h2
   exact hc.trans (congrArg (modelCantor q) he)
 · intro hc
   exact ⟨(modelCantor l r).val,(cantor_iff _ _ _).mpr rfl,(cantor_iff _ _ _).mpr hc⟩
end PalomarZF207History
