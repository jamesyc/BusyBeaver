module
public import I3_334.Search.SearchRegisters
public import I3_334.Search.NumericSearch
public import I3_334Support.Search.WordCompare
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (inc dec block whilePositive whilePositive_zero
  whilePositive_pos run_inc run_increments LineRuns)

structure Scratch {V : Type} [OfNat V 0] (s : Store V) : Prop where
  expectedEmpty : s expected = 0
  tokenEmpty : s tok = 0
  auxiliaryEmpty : s u = 0

theorem Scratch.iff_fields {V : Type} [OfNat V 0] {s : Store V} : Scratch s ↔
    s expected = 0 ∧ s tok = 0 ∧ s u = 0 :=
  ⟨fun h => ⟨h.expectedEmpty,h.tokenEmpty,h.auxiliaryEmpty⟩,fun ⟨a,b,c⟩ => ⟨a,b,c⟩⟩

def bias (slot : Fin 4) : Nat := if slot.val = 3 then 3 else 0

theorem bias_eq_offset (slot : Fin 4) : bias slot = Dictionary.offset slot := by
  revert slot
  decide +kernel

def markedIf {V : Type} [OfNat V 0] (marker : V) (matchOk : Prop) [Decidable matchOk] : V :=
  if matchOk then marker else 0

theorem markedIf_and {V : Type} [OfNat V 0] (value : V) (a b : Prop) [Decidable a] [Decidable b] :
    markedIf (markedIf value a) b = markedIf value (a ∧ b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [markedIf,ha,hb]

def consumeField (s : Store) : Store :=
  let field := Cantor.unpair (s fr)
  ((s.set fr field.2).set expected 0).set gues (markedIf (s gues) (s expected = field.1))

def scanBodyEffect (slot : Fin 4) (s : Store) : Store :=
  let (token, rest) := readRaw (bias slot) (s tmp)
  let actual := rawFields (s fr)
  (((s.set tmp rest).set fr actual.rest).set goal (s goal+token.arity)).set gues
    (markedIf (s gues) (token.arity+1 = actual.arityField ∧ token.tag = actual.tag))

/-- One body pass uses an unbiased dictionary arity, an offset tag in
slot d, and the corresponding two biased fields in the actual term. -/
theorem run_scanBody (slot : Fin 4) (s : Store) (clean : Scratch s) :
    Executes (scanBody slot) s .normal (scanBodyEffect slot s) := by
  let ar := Cantor.unpair (s tmp)
  let tag := Cantor.unpair ar.2
  let first := (s.set tmp ar.2).set expected ar.1
  let second := first.set goal (first goal + first expected)
  let third := second.set expected (second expected + 1)
  let fourth := consumeField third
  let fifth := (fourth.set tmp tag.2).set expected tag.1
  let sixth := fifth.set expected (fifth expected + bias slot)
  have r₁ : Executes (pop tmp expected) s .normal first :=
    run_pop (by decide) (by decide) (by decide) s clean.expectedEmpty clean.auxiliaryEmpty
  have r₂ : Executes (copy expected goal) first .normal second :=
    run_copy (by decide) (by decide) (by decide) first
      (by simpa [first, Store.set, tmp, expected, u] using clean.auxiliaryEmpty)
  have r₃ : Executes (inc expected) second .normal third := run_inc _ _
  have r₄ : Executes eat third .normal fourth :=
    run_eat third
      (by simpa [third,second,first,Store.set,goal,expected,tmp,tok] using clean.tokenEmpty)
      (by simpa [third,second,first,Store.set,goal,expected,tmp,u] using clean.auxiliaryEmpty)
  have nextTmp : fourth tmp = ar.2 := by
    simp [fourth,consumeField,third,second,first,Store.set,tmp,expected,goal,fr,gues]
  have r₅ : Executes (pop tmp expected) fourth .normal fifth := by
    have run := run_pop (source := tmp) (target := expected) (by decide) (by decide) (by decide) fourth
      (by simp [fourth,consumeField,Store.set,expected,gues])
      (by simpa [fourth,consumeField,third,second,first,Store.set,goal,expected,tmp,u,fr,gues]
        using clean.auxiliaryEmpty)
    simpa only [nextTmp] using run
  have r₆ : LineRuns (List.replicate (bias slot) (inc expected)) fifth sixth :=
    run_increments _ _ _
  have r₇ : Executes eat sixth .normal (consumeField sixth) :=
    run_eat sixth
      (by simpa [sixth,fifth,fourth,consumeField,third,second,first,Store.set,goal,expected,tmp,tok,fr,gues]
        using clean.tokenEmpty)
      (by simpa [sixth,fifth,fourth,consumeField,third,second,first,Store.set,goal,expected,tmp,u,fr,gues]
        using clean.auxiliaryEmpty)
  have code : LineRuns ([pop tmp expected, copy expected goal, inc expected, eat, pop tmp expected] ++
      List.replicate (bias slot) (inc expected) ++ [eat]) s (consumeField sixth) :=
    (LineRuns.cons r₁ (.cons r₂ (.cons r₃ (.cons r₄ (.cons r₅ .nil))))).append r₆ |>.append (.cons r₇ .nil)
  have value : consumeField sixth = scanBodyEffect slot s := by
    funext i
    by_cases ex : i = expected <;> by_cases g : i = gues <;>
      by_cases f : i = fr <;> by_cases t : i = tmp <;> by_cases pending : i = goal <;>
      simp [scanBodyEffect,readRaw,rawFields,consumeField,first,second,third,fourth,fifth,sixth,
        ar,tag,Store.set,ex,g,f,t,pending,expected,gues,fr,tmp,goal,
        clean.expectedEmpty, markedIf_and] <;> rfl
  rw [value] at code
  exact code.block

end PalomarI3334.SearchProgram
