module
public import FoundationLKBridge
public import ProofTranslation
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder

theorem sourceTheorems_finite (ps : List ZFR.Formula)
 (hs : ∀ p ∈ ps, SourceTheorem p) :
 ∃ Δ : Context, (∀ a ∈ Δ, sourceZfrAxiom (encodeFormula a)) ∧
 (∀ p ∈ ps, ND (.seq Δ p)) := by
 induction ps with
 | nil => exact ⟨[],by simp,by simp⟩
 | cons p ps ih =>
   obtain ⟨Γ,hΓ,hp⟩ := hs p (by simp)
   obtain ⟨Δ,hΔ,hps⟩ := ih (fun q hq => hs q (by simp [hq]))
   refine ⟨Γ++Δ,?_,?_⟩
   · intro a ha
     rcases List.mem_append.mp ha with ha | ha
     · exact hΓ a ha
     · exact hΔ a ha
   · intro q hq
     rcases List.mem_cons.mp hq with rfl | hq
     · exact ND.wk (fun a ha => List.mem_append_left Δ ha) hp
     · exact ND.wk (fun a ha => List.mem_append_right Γ ha) (hps q hq)

/-- Full actual-library proof object to source theorem, conditional only on
proved translations of the actual source theory axioms. -/
theorem foundation_source_theorem {T : Theory Language.set} {p : Sentence Language.set}
 (h : T ⊢ p)
 (hs : ∀ a ∈ T, SourceTheorem (toSource (a : Proposition Language.set))) :
 SourceTheorem (toSource (p : Proposition Language.set)) := by
 classical
 obtain ⟨Γ,hΓ,⟨hd⟩⟩ := Theory.Proof.provable_iff.mp h
 let ps := Γ.toList.map (fun (a : Sentence Language.set) => toSource (a : Proposition Language.set))
 have hp : ∀ q ∈ ps, SourceTheorem q := by
   intro q hq
   obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
   exact hs a (hΓ a (by simpa using ha))
 obtain ⟨Δ,hΔ,hps⟩ := sourceTheorems_finite ps hp
 refine ⟨Δ,hΔ,?_⟩
 apply external_theory_proof (S := LK.Sequent.embed Γ)
 · simpa [add_comm, Multiset.tilde_def, Semiformula.neg_eq] using hd
 · intro a ha
   change a ∈ Γ.map Rewriting.emb at ha
   obtain ⟨b,hb,rfl⟩ := Multiset.mem_map.mp ha
   apply hps
   exact List.mem_map.mpr ⟨b,by simpa using hb,rfl⟩

end ZFR.FoundationBridge
