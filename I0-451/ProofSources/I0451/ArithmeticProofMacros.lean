module
public import I0451.ArithmeticPackedCommands

/-! Fixed command sequences for proof steps in any arithmetic model.
Each proof step pushes exactly one formula on a neutral store. The
temporary entries created by AX and DROP are consumed within the step. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime
open I0451.Logic (Command ProofStore executeCommands executeCommands_append AxiomEncoding)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def neutralStore (stack : V) : ProofStore V := ⟨0, stack, 0, 0⟩

noncomputable def modelStack (forms : List V) (tail : V) : V := forms.foldr cantor tail

def ProofEffect (word : List (Command V)) (input output : ProofStore V) : Prop :=
  executeCommands runModelCommand word input = none ∨ executeCommands runModelCommand word input = some output

namespace ProofEffect

theorem singleton {cmd : Command V} {first last : ProofStore V}
    (ran : runModelCommand cmd first = some last) : ProofEffect [cmd] first last := by
  exact Or.inr (by simp [executeCommands, ran])

theorem append {first rest : List (Command V)} {a b c : ProofStore V}
    (before : ProofEffect first a b) (after : ProofEffect rest b c) :
    ProofEffect (first ++ rest) a c := by
  unfold ProofEffect at *
  rw [executeCommands_append]
  rcases before with stop | done
  · exact .inl (by rw [stop]; rfl)
  · rw [done]
    exact after

end ProofEffect

def modelNips (count : Nat) : List (Command V) := List.replicate count (.nip 0)

theorem model_nip_effect (top head tail operand cache : V) :
    ProofEffect [.nip 0] ⟨top, cantor head tail, operand, cache⟩ ⟨top, tail, operand, head⟩ := by
  unfold ProofEffect
  by_cases contradiction : cache = 1
  · exact .inl (by simp [executeCommands, runModelCommand, contradiction])
  · exact .inr (by simp [executeCommands, runModelCommand, contradiction])

theorem model_pop_prefix (prior : List V) (top last tail operand cache : V) :
    ProofEffect (modelNips (prior.length + 1))
      ⟨top, modelStack (prior ++ [last]) tail, operand, cache⟩ ⟨top, tail, operand, last⟩ := by
  induction prior generalizing cache with
  | nil => exact model_nip_effect top last tail operand cache
  | cons f rest ih =>
    have first := model_nip_effect top f (modelStack (rest ++ [last]) tail) operand cache
    simpa [modelNips, modelStack, List.replicate_succ, Nat.add_assoc] using first.append (ih f)

def saveModelTop (operand : V) : List (Command V) :=
  [.ax operand 0 0 0] ++ modelNips 9 ++ [.mp 0]

theorem save_model_top_effect (top stack operand cache : V) :
    ProofEffect (saveModelTop operand) ⟨top, stack, operand, cache⟩
      (neutralStore (cantor top stack)) := by
  let heads := modelEncoding.heads operand cache operand 0
  let general := modelEncoding.all operand cache
  let saved := cantor top stack
  have ax : ProofEffect [.ax operand 0 0 0] ⟨top, stack, operand, cache⟩
      ⟨0, modelStack (heads ++ [general]) saved, 0, 0⟩ := by
    apply ProofEffect.singleton
    simp [runModelCommand, runModelAxioms, modelStack, List.foldr_append, heads, general, saved]
  have pop := model_pop_prefix heads 0 general saved 0 0
  have amount : heads.length + 1 = 9 := rfl
  rw [amount] at pop
  have misses : general ≠ modelImp 0 0 := by
    simp [general, modelEncoding, modelTag, modelImp]
  have clear : ProofEffect [.mp 0] ⟨0, saved, 0, general⟩ (neutralStore saved) := by
    apply ProofEffect.singleton
    simp [runModelCommand, neutralStore, misses]
  exact ax.append (pop.append clear)

def setAside (before after : Nat) : List (Command V) :=
  modelNips (before + 1) ++ [.drop 0] ++ modelNips (after + 2) ++ saveModelTop 0

/-- Select one member of an AX stack and clear all other entries in
that AX frame. The final stack contains the selected formula and the old tail. -/
theorem model_select_formula (before after : List V) (selected top tail cache : V) :
    ProofEffect (setAside (V := V) before.length after.length)
      ⟨top, modelStack (before ++ selected :: after ++ [0]) tail, 0, cache⟩
      (neutralStore (cantor selected tail)) := by
  let remaining := modelStack (after ++ [0]) tail
  have pop := model_pop_prefix before top selected remaining 0 cache
  have firstStack : modelStack (before ++ [selected]) remaining =
      modelStack (before ++ selected :: after ++ [0]) tail := by
    simp [modelStack, remaining, List.foldr_append]
  rw [firstStack] at pop
  have choose : ProofEffect [.drop 0] ⟨top, remaining, 0, selected⟩
      ⟨selected, cantor top remaining, 0, selected⟩ := by
    apply ProofEffect.singleton
    simp [runModelCommand]
  have erase := model_pop_prefix (top :: after) selected 0 tail 0 selected
  have amount : (top :: after).length + 1 = after.length + 2 := by simp [Nat.add_assoc]
  have eraseFrom : modelStack ((top :: after) ++ [0]) tail = cantor top remaining := rfl
  rw [amount, eraseFrom] at erase
  simpa only [setAside, List.append_assoc] using
    pop.append (choose.append (erase.append (save_model_top_effect selected tail 0 0)))

theorem push_model_foundation (tail : V) :
    ProofEffect ([.extra 0] ++ setAside (V := V) 0 0) (neutralStore tail)
      (neutralStore (cantor (literalFoundationCode : V) tail)) := by
  let b := (literalBerkeleyCode : V)
  let f := (literalFoundationCode : V)
  have first : ProofEffect [.extra 0] (neutralStore tail)
      ⟨b, modelStack [f,0] tail, 0, 0⟩ := ProofEffect.singleton rfl
  exact first.append (model_select_formula [] [] f b tail 0)

theorem push_model_top (others : List V) (top tail cache : V) :
    ProofEffect (modelNips (others.length + 1) ++ saveModelTop 0)
      ⟨top, modelStack (others ++ [0]) tail, 0, cache⟩
      (neutralStore (cantor top tail)) :=
  (model_pop_prefix others top 0 tail 0 cache).append (save_model_top_effect top tail 0 0)

theorem push_model_berkeley (tail : V) :
    ProofEffect ([.extra 0] ++ modelNips 2 ++ saveModelTop 0) (neutralStore tail)
      (neutralStore (cantor (literalBerkeleyCode : V) tail)) := by
  let b := (literalBerkeleyCode : V)
  let f := (literalFoundationCode : V)
  have first : ProofEffect [.extra 0] (neutralStore tail)
      ⟨b, modelStack [f,0] tail, 0, 0⟩ := ProofEffect.singleton rfl
  exact first.append (push_model_top [f] b tail 0)

theorem push_model_bundle {a b c : V} (firstFresh : c ≠ a) (secondFresh : c ≠ b) (tail : V) :
    ProofEffect ([.ax c a b 0] ++ modelNips 10 ++ saveModelTop 0) (neutralStore tail)
      (neutralStore (cantor (modelEncoding.bundle a b c) tail)) := by
  let top := modelEncoding.bundle a b c
  let others := modelEncoding.heads a b c 0 ++ [modelEncoding.all a 0]
  have cmd : ProofEffect [.ax c a b 0] (neutralStore tail)
      ⟨top, modelStack (others ++ [0]) tail, 0, 0⟩ := by
    apply ProofEffect.singleton
    simp [runModelCommand, runModelAxioms, modelStack, List.foldr_append, neutralStore, top, others,
      firstFresh, secondFresh]
  have pushed := push_model_top others top tail 0
  have length : others.length + 1 = 10 := rfl
  rw [length] at pushed
  exact cmd.append pushed

theorem push_model_head {a b c x f : V} (present : f ∈ modelEncoding.heads a b c x) :
    ∃ word : List (Command V), ∀ tail,
      ProofEffect word (neutralStore tail) (neutralStore (cantor f tail)) := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp present
  let rest := after ++ [modelEncoding.all a 0]
  refine ⟨[.ax c a b x] ++ setAside before.length rest.length, fun tail => ?_⟩
  let top := if c = a ∨ c = b then 0 else modelEncoding.bundle a b c
  have cmd : ProofEffect [.ax c a b x] (neutralStore tail)
      ⟨top, modelStack (before ++ f :: rest ++ [0]) tail, 0, 0⟩ := by
    apply ProofEffect.singleton
    simp [runModelCommand, runModelAxioms, modelStack, List.foldr_append, neutralStore, split, rest, top]
  exact cmd.append (model_select_formula before rest f top tail 0)

def generalizeModelWord (label : V) : List (Command V) :=
  [.nip 0, .ax label label 0 0] ++ setAside 8 0

theorem generalize_model_effect (label form tail : V) :
    ProofEffect (generalizeModelWord label) (neutralStore (cantor form tail))
      (neutralStore (cantor (modelEncoding.all label form) tail)) := by
  let heads := modelEncoding.heads label form label 0
  let general := modelEncoding.all label form
  have read := model_nip_effect 0 form tail 0 0
  have ax : ProofEffect [.ax label label 0 0] ⟨0, tail, 0, form⟩
      ⟨0, modelStack (heads ++ [general, 0]) tail, 0, 0⟩ := by
    apply ProofEffect.singleton
    simp [runModelCommand, runModelAxioms, modelStack, List.foldr_append, heads, general]
  have length : heads.length = 8 := rfl
  have select := model_select_formula heads [] general 0 tail 0
  rw [length] at select
  exact read.append (ax.append select)

def detachModelWord (b : V) : List (Command V) :=
  [.nip 0, .drop 0, .nip 0, .nip 0, .mp b, .nip 0] ++ saveModelTop b

theorem detach_model_effect (a b tail : V) :
    ProofEffect (detachModelWord b) (neutralStore (cantor a (cantor (modelImp a b) tail)))
      (neutralStore (cantor b tail)) := by
  let conditional := modelImp a b
  have read := model_nip_effect 0 a (cantor conditional tail) 0 0
  have load : ProofEffect [.drop 0] ⟨0, cantor conditional tail, 0, a⟩
      ⟨a, cantor 0 (cantor conditional tail), 0, a⟩ := by
    apply ProofEffect.singleton
    simp [runModelCommand]
  have first := model_nip_effect a 0 (cantor conditional tail) 0 a
  have second := model_nip_effect a conditional tail 0 0
  have applyMp : ProofEffect [.mp b] ⟨a, tail, 0, conditional⟩ ⟨b, cantor 0 tail, b, 0⟩ := by
    apply ProofEffect.singleton
    simp [runModelCommand, conditional]
  have erase := model_nip_effect b 0 tail b 0
  have save := save_model_top_effect b tail b 0
  exact read.append (load.append (first.append (second.append (applyMp.append (erase.append save)))))

end I0451.Arithmetization
