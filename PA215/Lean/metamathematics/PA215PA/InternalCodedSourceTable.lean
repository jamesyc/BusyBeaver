import PA215PA.InternalCodedSourceProgram
import PA215PA.InternalSourceCoverage
set_option maxRecDepth 100000
namespace PA215.PA.InternalTrace.CodedSource
open PA215.Census
attribute [local irreducible] Source.exactSites PA215.Census.all originalAt

/-- Total resolution of the literal table follows from the accepted complete
source/certificate/destination collections; no fresh unchecked table is used. -/
theorem literal_resolved (i : Nat) (hi : i<3947) :
    ∃ inst, Source.resolveAt Source.exactSites i=some inst := by
  have hb : i<Source.exactSites.size := by simpa only [Source.exactSites_count] using hi
  let s := Source.exactSites[i]
  have hs : Source.exactSites[i]?=some s := Array.getElem?_eq_getElem hb
  by_cases hh : s.op=.halt
  · exact ⟨.halt,by simp [Source.resolveAt,hs,Source.resolve,hh]⟩
  · obtain ⟨j,hj,hg,ha⟩ := Source.CachedV2.selected_original i s (List.replicate 10 0) hs (by simp)
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
    obtain ⟨inst,p,q,e,k,next,hr,_,_,_,_⟩ :=
      Source.resolved_nonterminal_data hsource ha cert.target_eq hd
    rw [hj] at hr
    exact ⟨inst,hr⟩

lemma findSite_range (p : Source.Path) (sites : List Source.Site) (j : Nat)
    (h : Source.findSite p sites=some j) : j<sites.length := by
  induction sites generalizing j with
  | nil => simp [Source.findSite] at h
  | cons s sites ih =>
    simp only [Source.findSite] at h
    split at h
    · cases h; simp
    · cases ht : Source.findSite p sites with
      | none => simp [ht] at h
      | some k =>
        simp only [ht,Option.map_eq_map,Option.map_some,Option.some.injEq] at h
        subst j
        simpa using Nat.succ_lt_succ (ih k ht)

def DestinationBound (size : Nat) (n : Option Nat) : Prop := ∀ j, n=some j → j<size

def InstructionBound (size : Nat) : Source.Instruction → Prop
  | .inc _ n => DestinationBound size n
  | .dec _ z n => DestinationBound size z ∧ DestinationBound size n
  | .jump n => DestinationBound size n
  | .halt => True

lemma after_range (sites : Array Source.Site) (p : Source.Path) (n : Option Nat)
    (h : Source.after sites p=some n) : DestinationBound sites.size n := by
  cases hs : Source.successor p with
  | none => simp [Source.after,hs] at h; subst n; simp [DestinationBound]
  | some q =>
    cases hl : Source.locate sites q with
    | none => simp [Source.after,hs,hl] at h
    | some j =>
      simp only [Source.after,hs,hl,Option.map_eq_map,Option.map_some,Option.some.injEq] at h
      subst n
      intro k hk
      cases hk
      simpa only [Array.length_toList] using findSite_range q sites.toList j hl

lemma resolve_range (sites : Array Source.Site) (s : Source.Site) (i : Source.Instruction)
    (h : Source.resolve sites s=some i) : InstructionBound sites.size i := by
  cases ho : s.op with
  | inc r =>
    simp only [Source.resolve,ho,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff,Option.some.injEq] at h
    obtain ⟨n,hn,rfl⟩ := h
    exact after_range sites s.path n hn
  | dec r =>
    simp only [Source.resolve,ho,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff,Option.some.injEq] at h
    obtain ⟨p,hp,z,hz,n,hn,rfl⟩ := h
    exact ⟨after_range sites p z hz,after_range sites s.path n hn⟩
  | breakTo k =>
    simp only [Source.resolve,ho,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff,Option.some.injEq] at h
    obtain ⟨p,hp,n,hn,rfl⟩ := h
    exact after_range sites p n hn
  | continueTo k =>
    simp only [Source.resolve,ho,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff,Option.some.injEq] at h
    obtain ⟨p,hp,n,hn,rfl⟩ := h
    intro j hj
    cases hj
    simpa only [Array.length_toList] using findSite_range p sites.toList n hn
  | halt => simp [Source.resolve,ho] at h; subst i; trivial

/-- Every resolved literal target is either genuine cyclic exit or an actual
working ordinal; malformed sentinel is never a valid table target. -/
theorem literal_instruction_bound (i : Nat) (inst : Source.Instruction)
    (h : Source.resolveAt Source.exactSites i=some inst) : InstructionBound 3947 inst := by
  simp only [Source.resolveAt,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff] at h
  obtain ⟨s,hs,hr⟩ := h
  simpa only [Source.exactSites_count] using resolve_range Source.exactSites s inst hr
#print axioms literal_resolved
#print axioms literal_instruction_bound
end PA215.PA.InternalTrace.CodedSource
