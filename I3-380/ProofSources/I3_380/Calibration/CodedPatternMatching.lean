module
public import I3_380.Search.Arithmetic.TrieCover
public import I3_380.Calibration.TermConsumption
public import I3_380.Calibration.GroundRewrites
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open PalomarI3380.Compiler PalomarI3380.Compiler.Source
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine.SourceWords (emitVector emitVector_nil emitVector_cons emitVector_append cons tail_cons
  decodeLeft_cons decodeRight_cons appendVector appendVector_nil appendVector_cons flattenTokens)
open ArithmeticMachine.SourceCantor (decode_pairValue)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def termDictionary (args : Fin 3 → GroundTerm M) : M :=
  modelDictionary (fun i => termWord (args i).val)

def CodedMatcher (args : Fin 3 → GroundTerm M) (ps : List Pattern) (tokens : M) : Prop :=
  ∀ (s : Store M) (rest : M), ClearScratch s → s dc = termDictionary args →
    s fr = emitVector tokens rest → CodedPatternTrace ps s (s.set fr rest)

theorem front_ready {s : Store M} (ready : ClearScratch s) (rest : M) :
    ClearScratch (s.set fr rest) :=
  ready.frame fun r f _ _ => Store.get_set_other _ _ _ _ f

theorem controlled_front (s : Store M) (rest p r : M) :
    (controls s p r).set fr rest = controls (s.set fr rest) p r := by
  simp only [controls,Store.set_comm _ (by decide : sel ≠ fr),Store.set_comm s (by decide : pl ≠ fr)]

theorem CodedMatcher.empty (args : Fin 3 → GroundTerm M) : CodedMatcher args [] 0 := by
  intro s rest _ _ stream
  rw [emitVector_nil] at stream
  rw [← stream,Store.set_same]
  exact .nil _

theorem CodedMatcher.append {args : Fin 3 → GroundTerm M} {ps qs : List Pattern} {a b : M}
    (first : CodedMatcher args ps a) (second : CodedMatcher args qs b) :
    CodedMatcher args (ps ++ qs) (appendVector a b) := by
  intro s rest clear dict input
  rw [emitVector_append] at input
  have readA := first s (emitVector b rest) clear dict input
  let intermediate := s.set fr (emitVector b rest)
  have still : intermediate dc = termDictionary args :=
    (Store.get_set_other _ _ _ _ (by decide : dc ≠ fr)).trans dict
  have readB := second intermediate rest (front_ready clear _) still (Store.get_set ..)
  change CodedPatternTrace qs (s.set fr (emitVector b rest)) ((s.set fr (emitVector b rest)).set fr rest) at readB
  rw [Store.set_set] at readB
  exact readA.trans readB

theorem CodedMatcher.variable (args : Fin 3 → GroundTerm M) (i : Fin 3) :
    CodedMatcher args [.variable i] (termTokens (args i).val) := by
  intro s rest ready dict input
  exact .cons (fun p r => by
    have word : controls s p r fr = emitVector (termTokens (args i).val) rest := by
      simpa only [controls,Store.get_set_other _ _ _ _ (by decide : fr ≠ sel),
        Store.get_set_other _ _ _ _ (by decide : fr ≠ pl)] using input
    have value : modelCoordinate (controls s p r dc) i = termWord (args i).val := by
      simp only [controls,Store.get_set_other _ _ _ _ (by decide : dc ≠ sel),
        Store.get_set_other _ _ _ _ (by decide : dc ≠ pl),dict,termDictionary,modelCoordinate_dictionary]
    rw [← controlled_front]
    exact coded_scanShared i (controls s p r) (ready.controls p r) _ rest value word
      (termTokens_consumes (args i).isUTerm)) (front_ready ready _) (.nil _)

theorem CodedMatcher.literal (args : Fin 3 → GroundTerm M) (token : Token) :
    CodedMatcher args [.literal token] (⟪(token.arity : M),(token.tag : M)⟫ ∷ (0 : M)) := by
  intro s rest ready _ input
  refine .cons (fun p r => ?_) (front_ready ready _) (.nil _)
  let start := controls s p r
  have front : start fr = cons (token.arity : M) (token.tag : M) rest := by
    simpa [start,controls,Store.set,fr,pl,sel] using input
  have marker : literalMarker start token = start gues := by
    unfold literalMarker
    rw [front,decodeLeft_cons,decodeRight_cons,(decode_pairValue _ _).1]
    simp
  have program := coded_literal start token (ready.controls p r).context
  rw [front,tail_cons,marker] at program
  have same : (start.set fr rest).set gues (start gues) = start.set fr rest := by
    rw [← Store.get_set_other start fr gues rest (by decide : gues ≠ fr),Store.set_same]
  rw [same,controlled_front] at program
  exact program

theorem CodedMatcher.leading {args : Fin 3 → GroundTerm M} {ps : List Pattern} {later : M}
    (token : Token) (rest : CodedMatcher args ps later) :
    CodedMatcher args (.literal token :: ps) (⟪(token.arity : M),(token.tag : M)⟫ ∷ later) := by
  simpa only [List.singleton_append,appendVector_cons,appendVector_nil] using
    (CodedMatcher.literal args token).append rest

theorem quote_complement_tag :
    (⌜(show FilterLanguage.Func 1 from FunctionSymbol.complement)⌝ : M) = 0 := rfl

theorem quote_choose_tag :
    (⌜(show FilterLanguage.Func 1 from FunctionSymbol.choose)⌝ : M) = 1 := by
  change ((1 : Nat) : M) = 1
  exact Nat.cast_one

theorem quote_localRelation_tag :
    (⌜(show FilterLanguage.Func 1 from FunctionSymbol.localRelation)⌝ : M) = 2 := rfl

theorem quote_converse_tag :
    (⌜(show FilterLanguage.Func 1 from FunctionSymbol.converse)⌝ : M) = 3 := rfl

theorem quote_nand_tag :
    (⌜(show FilterLanguage.Func 2 from FunctionSymbol.nand)⌝ : M) = 0 := rfl

theorem quote_product_tag :
    (⌜(show FilterLanguage.Func 2 from FunctionSymbol.product)⌝ : M) = 1 := by
  change ((1 : Nat) : M) = 1
  exact Nat.cast_one

theorem quote_node_tag :
    (⌜(show FilterLanguage.Func 3 from FunctionSymbol.node)⌝ : M) = 0 := rfl

attribute [local simp] quote_complement_tag quote_choose_tag quote_localRelation_tag quote_converse_tag quote_nand_tag quote_product_tag quote_node_tag

theorem coded_term_pattern (args : Fin 3 → GroundTerm M) (t : PalomarI3380.Term (Fin 3)) :
    CodedMatcher args (pattern t) (termTokens (groundAlgebra.eval args t).val) := by
  induction t with
  | var i => exact CodedMatcher.variable args i
  | const c =>
    have tag : (⌜(show FilterLanguage.Func 0 from FunctionSymbol.constant c)⌝ : M) = (c.tag : M) := by
      cases c <;> rfl
    simpa [pattern,groundAlgebra,Algebra.eval,application_tokens,tag] using
      (CodedMatcher.literal (M := M) args ⟨0,c.tag⟩)
  | neg x ih =>
    simpa [pattern,groundAlgebra,Algebra.eval,application_tokens,Matrix.vecHead,Matrix.vecTail] using ih.leading ⟨1,0⟩
  | choice x ih =>
    simpa [pattern,groundAlgebra,Algebra.eval,application_tokens,Matrix.vecHead,Matrix.vecTail] using ih.leading ⟨1,1⟩
  | localRel x ih =>
    simpa [pattern,groundAlgebra,Algebra.eval,application_tokens,Matrix.vecHead,Matrix.vecTail] using ih.leading ⟨1,2⟩
  | converse x ih =>
    simpa [pattern,groundAlgebra,Algebra.eval,application_tokens,Matrix.vecHead,Matrix.vecTail] using ih.leading ⟨1,3⟩
  | nand x y hx hy =>
    simpa [pattern,groundAlgebra,Algebra.eval,application_tokens,Matrix.vecHead,Matrix.vecTail] using (hx.append hy).leading ⟨2,0⟩
  | product x y hx hy =>
    simpa [pattern,groundAlgebra,Algebra.eval,application_tokens,Matrix.vecHead,Matrix.vecTail] using (hx.append hy).leading ⟨2,1⟩
  | node x y z hx hy hz =>
    simpa [pattern,groundAlgebra,Algebra.eval,application_tokens,Matrix.vecHead,Matrix.vecTail,List.append_assoc] using
      (hx.append (hy.append hz)).leading ⟨3,0⟩

end PalomarI3380.Calibration.TermWords
