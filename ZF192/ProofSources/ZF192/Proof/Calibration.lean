module
public import ZF192Support.Independence.Theory.Refutation
public import ZF192Support.SetTheory.Omega.ProofTransport
public import ZF192Support.Independence.SecondIncompleteness
public import ZF192.Simulation.Forward.Startup
public import ZF192.Tape.Halting.SetTheorySentence

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
namespace ZF192

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open ZF192Support.Halting ZF192Support.OmegaInterpretation ZF192Support.Internal.Arith ZFR.ArithmeticRepresentation

/-- The calibrated arithmetic theory's internal refutations compile into proofs
of the falsity code in the machine's calculus. -/
theorem refutation_in_C (ι : Interp) (hF : InterpFacts ι theoryU) (hMk : theoryU ⊢ markAx ι)
    {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (h : Bootstrapping.Provable (theoryT ι) (^⊥ : V)) : D.val.Evalb ![(1 : V)] := by
  obtain ⟨x, hx⟩ := stage_one (theoryT ι) hF (axStep ι) h
  have hex : Derivable theoryU (insert (^∃ (markAt ι (^#0 : V))) (0 : V)) := by
    have h1 := tprovable_iff_provable.mp (internal_provable_of_outer_provable (V := V) hMk)
    have h2 := internal_provable_iff_internal_derivable.mp h1
    simpa [markAt_bvar, markAx, Sentence.quote_def, emptyset_def, tmpl_val, tq_eq] using h2
  have hU : Bootstrapping.Provable theoryU (^⊥ : V) := refute_of_mark' ι hex hx
  exact (provRules (M := V)).refutation theoryU
    (fun p hp m => D_craig ((mem_craig_iff ℒₛₑₜ idFn p).mp hp) m) hU

theorem halts_of_D {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (h : D.val.Evalb ![(1 : V)]) : BinaryTape.physicalHalts (M := V) := by
  obtain ⟨p, hp, hm⟩ := (D_iff 1).mp h
  exact NativePhysicalLift.literalCRefutation_physical (ZF192Support.ModelCommands.refutation_compilable p hp hm)

theorem pa_not_halt_con (ι : Interp) (hF : InterpFacts ι theoryU) (hMk : theoryU ⊢ markAx ι) :
    𝗣𝗔 ⊢ ∼BinaryTape.physicalHaltSentence 🡒 (Theory.standardProvability (theoryT ι)).con := by
  apply Arithmetic.complete.{0}
  intro V _ _
  have hh := BinaryTape.physicalHaltSentence_eval (M := V)
  simp only [models_iff] at hh ⊢
  simp [hh]
  intro hn
  simp only [ProvabilityAbstraction.Provability.con, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq]
  intro hp
  have hp' := by simpa [models_iff, FFL.FirstOrder.Arithmetic.standardProvability_def] using hp
  exact hn (halts_of_D (refutation_in_C ι hF hMk hp'))

theorem internal (ι : Interp) (hF : InterpFacts ι theoryU) (hMk : theoryU ⊢ markAx ι) :
    (𝗭𝗙 : SetTheory) ⊢ ∼literal192PhysicalSentence 🡒
      arithmeticTranslation.translate (Theory.standardProvability (theoryT ι)).con := by
  simpa [literal192PhysicalSentence] using pa_proof_to_zf (pa_not_halt_con ι hF hMk)

end ZF192
