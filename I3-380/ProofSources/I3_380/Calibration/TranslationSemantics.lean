module
public import I3_380.Calibration.ReadFilterArithmetic
public import I3_380.Calibration.GraphTranslation
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Logic.Expanded (ClassAxioms OmegaDomain)
open ArithmeticInterpretation

variable {A : Type} [Nonempty A] [Tarski.Structure FilterLanguage A] [Tarski.Structure.Eq FilterLanguage A]
variable (C : FilterModel A)
variable {laws : ClassAxioms C.mem (fun _ _ => False)} {inhabited : Nonempty C.Domain}
variable (D : OmegaDomain laws inhabited)

theorem translatedSentence_reads (φ : ArithmeticSentence) (default : C.Representative) :
    letI := graphStructure (A := A)
    A↓[GraphLanguage] ⊧ translatedSentence φ ↔ φ.Evalb (![] : Fin 0 → D.Points) := by
  letI := graphStructure (A := A)
  let assignment := fun _ : Nat => default.val.val
  have reading : A↓[GraphLanguage] ⊧ translatedSentence φ ↔
      (kaxP filterInterpretation φ).Eval ![] assignment := by
    rw [translatedSentence_spec,models_iff,Semiformula.eval_emb]
  rw [reading]
  have perMarker (a : A) :
      (∼tpl filterInterpretation.mark ![#0] ⋎
        Jx filterInterpretation #0 (Rew.castLE (by simp : 0 ≤ 1) ▹
          (Rewriting.emb φ : Proposition ℒₒᵣ))).Eval ![a] assignment ↔
        φ.Evalb (![] : Fin 0 → D.Points) := by
    have marker : (tpl filterInterpretation.mark (![Semiterm.bvar 0] :
        Fin 1 → Semiterm GraphLanguage Nat 1)).Eval ![a] assignment := by
      rw [eval_tpl]
      trivial
    simp only [LogicalConnective.HomClass.map_or,LogicalConnective.HomClass.map_neg,
      marker,LogicalConnective.Prop.neg_eq,LogicalConnective.Prop.or_eq,not_true,false_or]
    have meaning := eval_Jx (reads_filter_arithmetic C D a default)
      (Rew.castLE (by simp : 0 ≤ 1) ▹ (Rewriting.emb φ : Proposition ℒₒᵣ))
      (.bvar 0) ![a] assignment rfl
    simpa only [Semiformula.eval_castLE,Semiformula.eval_emb,Matrix.empty_eq,Empty.eq_elim] using meaning
  exact ⟨fun h => (perMarker default.val.val).mp (h default.val.val),fun h a => (perMarker a).mpr h⟩

end PalomarI3380.Calibration
