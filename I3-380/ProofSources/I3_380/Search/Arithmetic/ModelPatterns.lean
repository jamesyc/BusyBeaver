module
public import I3_380.Search.Arithmetic.TokenPrograms
public import I3_380.Search.Arithmetic.ModelDispatch
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine.SourceWords (tail)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ClearScratch.context {s : Store M} (clear : ClearScratch s) : ContextScratch s :=
  ⟨clear.expZero,clear.tokZero,clear.auxZero⟩

theorem ClearScratch.frame {s t : Store M} (clear : ClearScratch s)
    (same : ∀ r, r ≠ fr → r ≠ lv → r ≠ gues → t r=s r) : ClearScratch t where
  expZero := (same «exp» (by decide) (by decide) (by decide)).trans clear.expZero
  tokZero := (same tok (by decide) (by decide) (by decide)).trans clear.tokZero
  auxZero := (same u (by decide) (by decide) (by decide)).trans clear.auxZero
  tempZero := (same tmp (by decide) (by decide) (by decide)).trans clear.tempZero
  goalZero := (same goal (by decide) (by decide) (by decide)).trans clear.goalZero

theorem ClearScratch.context_state {s : Store M} (clear : ClearScratch s) (a b g : M) :
    ClearScratch (replaceContext s a b g) :=
  clear.frame (fun r f l m => by simp [replaceContext,Store.set,f,l,m])

theorem replaceContext_keep_second (s : Store M) (a m : M) :
    replaceContext s a (s lv) m = (s.set fr a).set gues m := by
  have value : (s.set fr a) lv = s lv := Store.get_set_other _ _ _ _ (by decide)
  unfold replaceContext
  rw [← value,Store.set_same]

theorem replaceContext_replace (s : Store M) (a b g x y m : M) :
    replaceContext (replaceContext s a b g) x y m = replaceContext s x y m := by
  funext r
  by_cases f : r=fr <;> by_cases l : r=lv <;> by_cases mark : r=gues <;>
    simp [replaceContext,Store.set,f,l,mark]

theorem coded_pattern [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (p : Pattern) (s : Store M) (clear : ClearScratch s) :
    ∃ a b g, p.compile.Runs .normal s.code (replaceContext s a b g).code := by
  cases p with
  | «variable» i =>
    obtain ⟨a,g,result⟩ := coded_scan_total i s clear
    exact ⟨a,s lv,g,by simpa only [Pattern.compile,replaceContext_keep_second] using result⟩
  | literal t =>
    exact ⟨tail (s fr),s lv,literalMarker s t,by
      simpa only [Pattern.compile,replaceContext_keep_second] using coded_literal s t clear.context⟩
  | side =>
    let swapped := (s.set fr (s lv)).set lv (s fr)
    have marker : swapped gues = s gues := by
      simp [swapped,Store.set,fr,lv,gues]
    refine ⟨s lv,s fr,s gues,?_⟩
    change side.Runs .normal s.code (swapped.set gues (s gues)).code
    rw [← marker,Store.set_same]
    exact coded_side s clear.tempZero

theorem coded_patterns [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (ps : List Pattern) (s : Store M) (clear : ClearScratch s) :
    ∃ a b g, CodedLines (ps.map Pattern.compile) s.code (replaceContext s a b g).code := by
  induction ps generalizing s with
  | nil =>
    refine ⟨s fr,s lv,s gues,?_⟩
    simp only [List.map_nil,replaceContext_keep_second,Store.set_same]
    exact CodedLines.nil _
  | cons p ps ih =>
    obtain ⟨a,b,g,head⟩ := coded_pattern p s clear
    obtain ⟨a',b',g',rest⟩ := ih (replaceContext s a b g) (clear.context_state a b g)
    rw [replaceContext_replace] at rest
    exact ⟨_,_,_,CodedLines.cons head rest⟩

end PalomarI3380.Compiler.Source
