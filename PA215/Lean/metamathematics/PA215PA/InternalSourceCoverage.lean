import PA215PA.InternalSourcePrimitive
import PA215.Source.CachedV2.SelectedOriginal
import PA215.Source.ResolvedContractData
import PA215.Source.NonterminalPlan
import PA215.Source.AllContractDestinations
import PA215.AllRuntimeCertificates
import PA215.OriginalTerminalMetadata
set_option maxRecDepth 100000
namespace PA215.PA.InternalTrace.ModelSource
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open PA215.Runtime PA215.Census Symbolic PhysicalRegisters
attribute [local irreducible] Source.exactSites PA215.Census.all originalAt
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def zeroChoice (op : Source.Op) (xs : V) : Bool :=
  match op with
  | .dec r => decide (readFile xs r=0)
  | _ => true

lemma chosen_guard (op : Source.Op) (xs : V) :
    FileBoxes.Guard xs (Source.ObligationKeys.expectedBranch op (zeroChoice op xs)) := by
  cases op with
  | dec r =>
    by_cases hz : readFile xs r=0 <;>
      simp [Source.ObligationKeys.expectedBranch,zeroChoice,FileBoxes.Guard,
        FileLayout.value_nth,readFile] at hz ⊢ <;> simp_all
  | inc r => trivial
  | breakTo k => trivial
  | continueTo k => trivial
  | halt => trivial

lemma selected_original (i : Nat) (s : Source.Site) (xs : V)
    (hs : Source.exactSites[i]?=some s) :
    ∃ j : Fin 5134, (originalAt j).siteIndex=i ∧
      FileBoxes.Guard xs (originalAt j).branch ∧ Source.agreesWith s (originalAt j)=true := by
  obtain ⟨j,hi,hb⟩ := Source.CachedV2.source_original_indexed i s (zeroChoice s.op xs) hs
  refine ⟨j,hi,?_,?_⟩
  · rw [hb]
    exact chosen_guard s.op xs
  · have ha := Source.CachedV2.originalAt_agrees j
    unfold Source.recordAgrees at ha
    rw [hi,hs] at ha
    exact ha

lemma update_length_le : ∀ (r : Nat) (f : V → V) (xs : V),
    len xs≤len (FileEffects.update r f xs)
  | 0,f,xs => by
    rcases nil_or_adjoin xs with hz | ⟨a,as,ha⟩
    · simp [hz,FileEffects.update]
    · simp [ha,FileEffects.update]
  | n+1,f,xs => by
    rcases nil_or_adjoin xs with hz | ⟨a,as,ha⟩
    · simp [hz]
    · simp only [ha,FileEffects.update,fstIdx_adjoin,sndIdx_adjoin,len_adjoin,
        add_le_add_iff_right]
      exact update_length_le n f as

lemma effect_length_valid (e : Eff) (xs : V) (h : (10 : V)≤len xs) :
    (10 : V)≤len (FileEffects.effect e xs) := by
  cases e with
  | none => exact h
  | inc r =>
    simp only [FileEffects.effect,len_concat]
    exact le_trans h (le_trans (update_length_le r (·+1) xs) (by simp))
  | dec r => exact le_trans h (update_length_le r (·-1) xs)

/-- Every actual nonhalting literal source leaf now has its positive physical
simulation in every PA model. All finite census/runtime/destination suppliers
are the existing exact kernel-checked collections, not hypotheses. -/
theorem nonhalt_primitive (i : Nat) (s : Source.Site) (n xs : V)
    (hs : Source.exactSites[i]?=some s) (hh : s.op≠.halt) (hsize : (10 : V)≤len xs) :
    ∃ k next n' xs', Source.exactSites[k]?=some next ∧ (10 : V)≤len xs' ∧
      cycleStep ⟨.at i,readFile xs⟩=⟨.at k,readFile xs'⟩ ∧
      Progress true (PhysicalFrame.frame s.path n xs) (PhysicalFrame.frame next.path n' xs') := by
  obtain ⟨j,hj,hg,ha⟩ := selected_original i s xs hs
  obtain ⟨target,ht⟩ := Source.nonhalt_original_target ha hh
  have hjne : j.val≠5114 := by
    intro he
    have hn := (originalAt_target_none_iff j).mpr he
    rw [ht] at hn
    cases hn
  obtain ⟨cert⟩ := AllRuntimeCertificates.nonterminalCoverage j hjne
  have hd : Source.destinationAgrees (originalAt j)=true :=
    (List.all_eq_true.mp Source.original_all_destinations_agree) _ (Source.CachedV2.originalAt_mem j)
  have hsource : Source.exactSites[(originalAt j).siteIndex]?=some s := by rw [hj]; exact hs
  obtain ⟨inst,p,q,e,k,next,hi,hp,ho,hc,hn⟩ :=
    Source.resolved_nonterminal_data hsource ha cert.target_eq hd
  have hsim := checked_primitive (originalAt j) s inst p q e k next cert.target cert.fuel
    hsource hi hp ho hc hn cert.target_eq ha hd cert.accepted n xs hsize hg
  rw [hj] at hsim
  exact ⟨k,next,n+p.extra,FileEffects.effect p.effect xs,hn,
    effect_length_valid p.effect xs hsize,hsim.1,hsim.2⟩
end Models
#print axioms selected_original
#print axioms effect_length_valid
#print axioms nonhalt_primitive
end PA215.PA.InternalTrace.ModelSource
