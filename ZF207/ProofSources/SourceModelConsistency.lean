module
public import SourceNDSemanticSoundness
public import DirectZFCompleteness
@[expose] public section
namespace ZFR.NDSemantics
variable {V : Type*} (mem : V → V → Prop)
/-- Explicit intermediate calibration obligation, NOT a theorem asserting that
Foundation ZF models satisfy source axioms. -/
def AxiomsTrue : Prop := ∀ p : Formula, sourceZfrAxiom (encodeFormula p) → ∀ s : Nat → V, eval mem p s

theorem source_sound (ha : AxiomsTrue mem) {p : Formula}
 (hp : RosserDirect.ZFDriver.SourceCertificate p) (s : Nat → V) : eval mem p s := by
 obtain ⟨Γ,hΓ,hd⟩ := hp
 exact sound mem hd s (fun q hq => ha q (hΓ q hq) s)

/-- A nonempty model of the EXACT source axioms yields source consistency.
Existence of this model and its axiom validity remain explicit assumptions. -/
theorem consistent_of_model [Nonempty V] (ha : AxiomsTrue mem) :
 (¬ RosserDirect.ZFDriver.SourceCertificate Formula.bot) := by
 intro h
 let s : Nat → V := fun _ => Classical.choice (inferInstance : Nonempty V)
 exact source_sound mem ha h s

theorem fixed_refl_valid (s : Nat → V) : eval mem fixedRefl s := by
 simp [fixedRefl,eval]
theorem fixed_sym_valid (s : Nat → V) : eval mem fixedSym s := by
 simp only [fixedSym,eval,pushValue]
 exact fun x y h => h.symm
theorem fixed_trans_valid (s : Nat → V) : eval mem fixedTrans s := by
 simp only [fixedTrans,eval,pushValue]
 exact fun x y z h1 h2 => h1.trans h2
theorem fixed_eqElem_valid (s : Nat → V) : eval mem fixedEqElem s := by
 simp only [fixedEqElem,eval,pushValue]
 intro x y z w hx hy h
 simpa only [← hx,← hy] using h
end ZFR.NDSemantics
