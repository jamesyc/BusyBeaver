module
public import ConcreteChallengeCoding
public import ConcreteArithmeticPeano
public import ExactTailIterationModel
@[expose] public section
namespace PalomarZF209History
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open ZF209.OmegaInterpretation ZFR.ArithmeticRepresentation
open scoped FFL.FirstOrder.Arithmetic
variable {V:Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "A" => arithmeticTranslation.Model V
local notation "E" => (fun x y:V=>x∈y)
def tailIterSetGraph : SetTheorySemisentence 3 :=
 arithmeticTranslation.translate tailIterationGraph.val
def tailIterSet (y i c:V):Prop:=tailIterSetGraph.Evalb ![y,i,c]
instance tailIterSet_defined : ℒₛₑₜ-relation₃ (tailIterSet (V:=V)) via tailIterSetGraph := by
 refine ⟨?_⟩
 intro v
 have hv:v=![v 0,v 1,v 2]:=by funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun z => Fin.elim0 z) k) j) i
 change tailIterSetGraph.Evalb v ↔ tailIterSetGraph.Evalb ![v 0,v 1,v 2]
 rw [←hv]
instance tailIterSet_definable : ℒₛₑₜ-relation₃ (tailIterSet (V:=V)) :=
 tailIterSet_defined.to_definable
lemma tailIterSet_eval (y i c:A):
 tailIterSet y.val i.val c.val ↔ y=modelTailIter i c := by
 have h:=DirectTranslation.Model.evalb_translate_iff (π:=arithmeticTranslation)
  (φ:=tailIterationGraph.val) (e:=![y,i,c])
 rw [interpreted_structure_eq_standard (V:=V)] at h
 have he : (fun j:Fin 3 => (![y,i,c] j).val) = ![y.val,i.val,c.val] := by
  funext j
  exact Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun z => Fin.elim0 z) l) k) j
 rw [he] at h
 exact h.trans (tailIterationGraph_defined.iff (v:=![y,i,c]))
/-- Every internally finite segment of the arithmetic tail iterator has an
actual set-function graph in the ZF model, obtained by Separation on omega².
No external list or standard-length assumption occurs. -/
lemma internal_tail_graph_exists (c:A) : ∃f:V,
 (∀p:V,p∈f ↔ ∃i y:V,i∈SetTheory.succ c.val ∧ y∈(ω:V) ∧ p=⟨i,y⟩ₖ ∧ tailIterSet y i c.val) := by
 let P:V→Prop:=fun p=>∃i y:V,i∈SetTheory.succ c.val ∧ y∈(ω:V) ∧ p=⟨i,y⟩ₖ ∧ tailIterSet y i c.val
 have hd:ℒₛₑₜ-predicate P:=by dsimp only [P];definability
 obtain ⟨f,hf⟩:=separation_exists ((ω:V) ×ˢ (ω:V)) P hd
 refine ⟨f,?_⟩
 intro p
 rw [hf]
 constructor
 · exact fun h=>h.2
 · intro h
   refine ⟨?_,h⟩
   obtain ⟨i,y,hi,hy,rfl,ht⟩:=h
   have hiw:i∈(ω:V):=IsTransitive.ω.mem_trans hi (ω_succ_closed (model_mem_omega c))
   exact mem_prod_iff.mpr ⟨i,hiw,y,hy,rfl⟩
lemma internal_tail_function_exists (c:A) : ∃f:V,
 FunctionOn E f (SetTheory.succ c.val) ∧
 ∀i y:V,At E f i y ↔ i∈SetTheory.succ c.val ∧ y∈(ω:V) ∧ tailIterSet y i c.val := by
 obtain ⟨f,hf⟩:=internal_tail_graph_exists c
 have hp (i y:V) : ⟨i,y⟩ₖ∈f ↔ i∈SetTheory.succ c.val ∧ y∈(ω:V) ∧ tailIterSet y i c.val := by
  rw [hf]
  constructor
  · rintro ⟨a,b,ha,hb,he,ht⟩
    obtain ⟨rfl,rfl⟩:=kpair_inj he
    exact ⟨ha,hb,ht⟩
  · rintro ⟨hi,hy,ht⟩;exact ⟨i,y,hi,hy,rfl,ht⟩
 refine ⟨f,?_,by intro i y;rw [at_iff];exact hp i y⟩
 simp only [FunctionOn,at_iff,orderedPair_iff]
 constructor
 · intro i hi
   have hiw:i∈(ω:V):=IsTransitive.ω.mem_trans hi (ω_succ_closed (model_mem_omega c))
   let im:A:=ofOmega i hiw
   let y:A:=modelTailIter im c
   refine ⟨y.val,(hp i y.val).mpr ⟨hi,model_mem_omega y,?_⟩,?_⟩
   · exact (tailIterSet_eval y im c).mpr rfl
   · intro z hz
     obtain ⟨_,hzω,hz⟩:=(hp i z).mp hz
     have he:(ofOmega z hzω:A)=y:=(tailIterSet_eval (ofOmega z hzω) im c).mp hz
     exact congrArg DirectTranslation.Model.val he
 · intro p hp'
   obtain ⟨i,y,hi,hy,rfl,ht⟩:=(hf p).mp hp'
   exact ⟨i,y,hi,rfl⟩
/-- Uniqueness against any internally finite set-function iterator. Induction
is ZF's omega induction with the actual set parameter f, not external Nat induction. -/
lemma internal_tail_function_unique (c:A) (f:V)
 (hf:FunctionOn E f (SetTheory.succ c.val))
 (hz:At E f (0:A).val c.val)
 (hr:∀i x:V,i∈SetTheory.succ c.val→At E f i x→NatObject E x)
 (hs:∀i:V,i∈c.val→∃j x y:V,Succ E i j ∧ At E f i x ∧ At E f j y ∧ ListTail E x y) :
 ∀(i x:A),At E f i.val x.val→x=modelTailIter i c := by
 obtain ⟨hfun,hd⟩:=(functionOn_iff f (SetTheory.succ c.val)).mp hf
 letI:=hfun
 have hz':⟨(0:V),c.val⟩ₖ∈f:=by simpa only [at_iff,val_zero] using hz
 have hh:∀i:V,i∈(ω:V)→∀y:V,y∈(ω:V)→⟨i,y⟩ₖ∈f→tailIterSet y i c.val := by
  apply naturalNumber_induction
  · definability
  case zero =>
   intro y hy hpair
   have he:y=c.val:=IsFunction.unique hpair hz'
   subst y
   simpa only [val_zero] using (tailIterSet_eval c (0:A) c).mpr (modelTailIter_zero c).symm
  case succ =>
   intro i hi ih y hy hpair
   have hdom:SetTheory.succ i∈SetTheory.succ c.val:=hd ▸ mem_domain_of_kpair_mem hpair
   have hic:i∈c.val:=by
    rcases mem_succ_iff.mp hdom with he|hm
    · exact he ▸ mem_succ_self i
    · exact (IsTransitive.nat (model_mem_omega c)).transitive _ hm _ (mem_succ_self i)
   obtain ⟨j,x,z,hj,hx,hz,hstep⟩:=hs i hic
   have hj':j=SetTheory.succ i:=(succ_iff i j).mp hj
   subst j
   have hz':⟨SetTheory.succ i,z⟩ₖ∈f:=(at_iff f _ _).mp hz
   have hezy:z=y:=IsFunction.unique hz' hpair
   subst z
   have hxw:x∈(ω:V):=(natObject_iff x).mp (hr i x (mem_succ_iff.mpr (Or.inr hic)) hx)
   let im:A:=ofOmega i hi
   let xm:A:=ofOmega x hxw
   let ym:A:=ofOmega y hy
   have hix:tailIterSet x i c.val:=ih x hxw ((at_iff f _ _).mp hx)
   have hxe:xm=modelTailIter im c:=(tailIterSet_eval xm im c).mp hix
   have hye:ym=modelListTail xm:=(listTail_iff xm ym).mp hstep
   have hout:tailIterSet ym.val (im+1).val c.val:=(tailIterSet_eval ym (im+1) c).mpr (by
    rw [modelTailIter_succ,←hxe];exact hye)
   simpa only [val_succ,ym,im,ofOmega] using hout
 intro i x hx
 exact (tailIterSet_eval x i c).mp (hh i.val (model_mem_omega i) x.val (model_mem_omega x) ((at_iff f _ _).mp hx))
end PalomarZF209History
