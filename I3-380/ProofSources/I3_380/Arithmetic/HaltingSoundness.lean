module
public import I3_380.Arithmetic.InternalHalting
public import I3_380.Arithmetic.OmegaSigma
public import I3_380.Arithmetic.SigmaTranslation
public import I3_380.Arithmetic.StandardRun
public import I3_380.Logic.SigmaSoundness
@[expose] public section

namespace PalomarI3380.Logic

open Expanded
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

theorem halting_is_sigma1 :
    ∃ p : SigmaFormula, p.bound 0 ∧ RepresentsArithmetic p haltingSentence ∧
      ∀ env : Nat → Nat, p.natEval env ↔ HaltsFrom machine blank := by
  let formula := ArithmeticMachine.haltsDef 380 packedLiteral
  obtain ⟨p,scope,reads⟩ := sigma_representable formula.val formula.sigma_prop
  refine ⟨p,scope,⟨haltingSentence_represents.1,?_⟩,?_⟩
  · intro V E inhabited model s env nat
    have ordinary : ZFCModel E := fun f h => model f (h.elim Or.inl (fun c => Or.inr (Or.inl c)))
    obtain ⟨w,omega⟩ := ordinary.omega s
    let L := ClassAxioms.from_ordinary ordinary
    let D : OmegaDomain L inhabited := ⟨w,omega⟩
    let m := L.context inhabited
    let family : Nat → D.Points := fun i => ⟨env i,(m.natObject_iff omega _).mp (nat i)⟩
    have same : (fun i : Fin 0 => family i.val) = ![] := funext fun i => i.elim0
    exact (haltingSentence_represents.2 V E inhabited model s).trans
      (D.internal_halts_iff_arithmetic.trans (((same ▸ reads D.Points family)).trans (D.sigma_eval p family).symm))
  · intro env
    have empty : (fun i : Fin 0 => env i.val) = ![] := funext fun i => i.elim0
    exact ((reads Nat env).symm.trans (empty.symm ▸ ArithmeticMachine.haltsDef_nat))

theorem halting_unprovable_of_nonhalting (soundness : ArithmeticSigma1Sound)
    (nonhalting : ¬HaltsFrom machine blank) : ¬ZFCI3Provable haltingSentence := by
  obtain ⟨p,scope,rep,meaning⟩ := halting_is_sigma1
  exact fun proof => nonhalting ((meaning _).mp (soundness p scope haltingSentence rep proof (fun _ => 0)))

end PalomarI3380.Logic
