module
public import ZF192.Tape.History
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma stateCode_injective : Function.Injective (stateCode (M:=M)) := by
 intro s t h
 have hq:=modelCantor_injective h
 have hlr:=modelCantor_injective hq.2
 cases s with
 | mk q l r =>
  cases t with
  | mk q' l' r' =>
   have hq':q=q' := hq.1
   have hl':l=l' := hlr.1
   have hr':r=r' := hlr.2
   subst q'; subst l'; subst r'; rfl
lemma codedStep_encoded_iff (c:BinaryTape.Conf) (after:M) :
 codedStep (stateCode (encode c)) after ↔
 ∃c',BinaryTape.step M192.literal c=some c' ∧ after=stateCode (encode c') := by
 constructor
 · rintro ⟨s,t,hs,ht,hstep⟩
   have he:encode c=s := stateCode_injective hs
   subst s
   obtain ⟨c',hc',he'⟩ := (literalStep_encoded_iff c t).mp hstep
   exact ⟨c',hc',ht.trans (congrArg stateCode he')⟩
 · rintro ⟨c',hc',rfl⟩
   exact ⟨encode c,encode c',rfl,rfl,literalStep_of_zip_step c c' hc'⟩
/-- Any external finite physical execution has an actual internally coded history,
in every PA model. This direction does not assert all model histories are standard. -/
lemma physical_run_history (k:Nat) (initial:M) (c c':BinaryTape.Conf) (hist:M)
 (hh:runHistory initial hist) (hhead:modelListHead hist=stateCode (encode c))
 (hr:BinaryTape.run M192.literal k c=some c') :
 ∃hist',runHistory initial hist' ∧ modelListHead hist'=stateCode (encode c') := by
 induction k generalizing c hist with
 | zero =>
  have he:c=c' := Option.some.inj hr
  subst c'
  exact ⟨hist,hh,hhead⟩
 | succ k ih =>
  cases hs:BinaryTape.step M192.literal c with
  | none => simp only [BinaryTape.run,hs] at hr; contradiction
  | some d =>
   have hd:codedStep (modelListHead hist) (stateCode (encode (M:=M) d)) := by
    rw [hhead]
    exact (codedStep_encoded_iff c _).mpr ⟨d,hs,rfl⟩
   exact ih d (modelListCons (stateCode (encode d)) hist)
    (runHistory_extend hh hd) (modelListHead_cons _ _) (by simpa only [BinaryTape.run,hs] using hr)
lemma physical_reach_history (c c':BinaryTape.Conf) (hr:BinaryTape.Reach M192.literal c c') :
 ∃hist:M,runHistory (stateCode (encode c)) hist ∧ modelListHead hist=stateCode (encode c') := by
 obtain ⟨k,hk⟩:=hr
 exact physical_run_history k _ c c' (modelListCons (stateCode (encode c)) 0)
  (runHistory_singleton _) (modelListHead_cons _ _) hk
/-- Only here do we specialize to the standard natural numbers. Strong induction
on the actual linked-list code extracts a finite external physical execution. -/
lemma nat_history_reach (c:BinaryTape.Conf) (hist:Nat)
 (hh:runHistory (stateCode (encode c)) hist) :
 ∃c',BinaryTape.Reach M192.literal c c' ∧ modelListHead hist=stateCode (encode (M:=Nat) c') := by
 induction hist using Nat.strong_induction_on with
 | h hist ih =>
  have hp:0<hist := Nat.pos_of_ne_zero hh.1
  have hrec:=modelList_reconstruct hist hp
  have ht : modelTrace (runEdge (stateCode (encode (M:=Nat) c)))
    (modelListCons (modelListHead hist) (modelListTail hist)) := by
   rw [hrec]; exact hh.2
  have hparts := (modelTrace_cons (runEdge (stateCode (encode (M:=Nat) c)))
   (modelListHead hist) (modelListTail hist)).mp ht
  rcases hparts.2 with ⟨ht0,ha⟩|⟨ht0,hs⟩
  · exact ⟨c,BinaryTape.Reach.refl _ _,ha⟩
  · obtain ⟨d,hd,hhhead⟩ := ih (modelListTail hist) (modelListTail_lt hist hp) ⟨ht0,hparts.1⟩
    rw [hhhead] at hs
    obtain ⟨d',hd',he⟩ := (codedStep_encoded_iff d (modelListHead hist)).mp hs
    exact ⟨d',hd.trans (BinaryTape.Reach.of_step hd'),he⟩
lemma blankCode_encoded : blankCode (M:=M)=stateCode (encode (BinaryTape.zc 0 [] [])) := rfl
/-- A standard finite halting run supplies a coded physical halting witness in every PA model. -/
lemma physicalHalts_of_zipHalts
 (h:BinaryTape.Halts M192.literal (BinaryTape.zc 0 [] [])) : physicalHalts (M:=M) := by
 obtain ⟨c,hc,hstop⟩:=h
 obtain ⟨hist,hh,hhead⟩:=physical_reach_history (M:=M) _ c hc
 refine ⟨hist,?_,?_⟩
 · simpa only [blankCode_encoded] using hh
 · intro after hs
   rw [hhead] at hs
   obtain ⟨d,hd,_⟩:=(codedStep_encoded_iff c after).mp hs
   rw [hstop] at hd
   contradiction
/-- A terminal coded history in the standard model yields an ordinary halting run. -/
lemma nat_halts_of_history (initial : BinaryTape.Conf) (hist : Nat)
    (run : runHistory (stateCode (encode initial)) hist)
    (stop : ∀ after, ¬ codedStep (modelListHead hist) after) :
    BinaryTape.Halts M192.literal initial := by
  obtain ⟨c, reached, head⟩ := nat_history_reach initial hist run
  refine ⟨c, reached, ?_⟩
  cases h : BinaryTape.step M192.literal c with
  | none => rfl
  | some d =>
    exfalso
    apply stop (stateCode (encode d))
    rw [head]
    exact (codedStep_encoded_iff c _).mpr ⟨d, h, rfl⟩

/-- The coded halting predicate agrees with literal blank-tape halting over Nat. -/
theorem physicalHalts_nat_iff : physicalHalts (M:=Nat) ↔
    BinaryTape.Halts M192.literal (BinaryTape.zc 0 [] []) := by
  constructor
  · rintro ⟨hist, run, stop⟩
    rw [blankCode_encoded] at run
    exact nat_halts_of_history _ hist run stop
  · exact physicalHalts_of_zipHalts

end ZF192.BinaryTape
