module
public import ZF192Support.Calculus.Internal.StandardTrace
public import ZF192Support.Execution.Commands.Totality

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF192Support.ModelCommands
open ZFR.ArithmeticRepresentation CCodeSoundness CProofSearch
open ZF192Support.Halting (imp_nat all_nat)

/-- Empty stacks read as zeros, as in the literal SHIFT implementation. -/
inductive SoundStack : Nat → Prop
  | zero : SoundStack 0
  | push {head tail : Nat} : ExactProvable head → SoundStack tail → SoundStack (modelCantor head tail)

private theorem SoundStack.pop {w : Nat} (h : SoundStack w) :
    ExactProvable (modelUnpairLeft w) ∧ SoundStack (modelUnpairRight w) := by
  cases h with
  | zero =>
    have hl : modelUnpairLeft (0 : Nat) = 0 := by
      simpa only [modelCantor_zero] using modelUnpairLeft_pair (0 : Nat) 0
    have hr : modelUnpairRight (0 : Nat) = 0 := by
      simpa only [modelCantor_zero] using modelUnpairRight_pair (0 : Nat) 0
    rw [hl, hr]
    exact ⟨proved_zero, .zero⟩
  | push hp ht => simpa only [modelUnpairLeft_pair, modelUnpairRight_pair] using And.intro hp ht

private theorem SoundStack.prepend {xs : List Nat} (hp : ∀ x ∈ xs, ExactProvable x)
    {w : Nat} (hw : SoundStack w) : SoundStack (xs.foldr modelCantor w) := by
  induction xs with
  | nil => exact hw
  | cons x xs ih => exact .push (hp x (by simp)) (ih (fun y hy => hp y (by simp [hy])))

def soundStore (s : Store Nat) : Prop :=
  ExactProvable s.t ∧ ExactProvable s.h ∧ SoundStack s.w

private theorem heads_sound (a d h oldD oldH : Nat) (hD : oldD ≤ d)
    (hH : ExactProvable oldH) : ∀ x ∈ heads a d h oldD oldH, ExactProvable x := by
  intro x hx
  rw [heads, implicationHeads, ZF192Support.Internal.codes_nat] at hx
  simp only [CKernel.Generic.Codes.axImplicationHeads, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact CKernel.natSys.h6 d a h
  · exact CKernel.natSys.h5 d h
  · exact CKernel.natSys.h4 h d a
  · exact CKernel.natSys.h3 h d a
  · exact CKernel.natSys.h2 d a h
  · exact CKernel.natSys.h1 d h
  · exact CKernel.natSys.r8 d a h oldD hD
  · rw [all_nat]
    exact proved_gen oldD hH

private theorem gate_sound (a d h : Nat) : ExactProvable (gate a d h) := by
  unfold gate
  split
  · rename_i hn
    unfold axGate
    rw [ZF192Support.Internal.codes_nat]
    exact CKernel.natSys.gate h d a hn.2 hn.1
  · exact proved_zero

private theorem command_preserves {c : Command Nat} {s t : Store Nat}
    (he : modelCommandEval c s = some t) (hs : soundStore s) : soundStore t := by
  obtain ⟨hp, hh, hw⟩ := hs
  cases c with
  | shift =>
    simp only [modelCommandEval] at he
    split at he
    · contradiction
    · cases he
      exact ⟨hh, hw.pop.1, hw.pop.2⟩
  | mp x =>
    simp only [modelCommandEval] at he
    split at he
    · rename_i hm
      cases he
      have hi : ExactProvable (impCode s.t (s.d + x)) := by rw [← imp_nat, hm]; exact hh
      exact ⟨proved_mp hp hi, proved_zero, .push proved_zero hw⟩
    · cases he
      exact ⟨proved_zero, proved_zero, hw⟩
  | ax a x y =>
    cases he
    refine ⟨gate_sound _ _ _, proved_zero, SoundStack.prepend ?_ hw⟩
    intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · exact heads_sound _ _ _ _ _ (Nat.le_add_right _ _) hh n hn
    · exact (List.mem_singleton.mp hn) ▸ hp

private def soundConfig (z : Nat) : Prop := soundStore (storeDecode (modelUnpairRight z))

private theorem soundConfig_iff (n : Nat) (s : Store Nat) :
    soundConfig (commandCfgCode n s) ↔ soundStore s := by
  simp [soundConfig, commandCfgCode, modelUnpairRight_pair, storeDecode_code]

private theorem history_preserves {initial hist : Nat} (hr : runHistory initial hist)
    (h : soundConfig initial) : soundConfig (modelListHead hist) := by
  apply ModelScheduler.rooted_nat_induction hr h
  rintro _ _ ⟨c, tail, s, t, rfl, rfl, he⟩ hs
  exact (soundConfig_iff _ _).mpr (command_preserves he ((soundConfig_iff _ _).mp hs))

private theorem halt_refutes {z : Nat} (h : haltAt z) (hs : soundConfig z) : ExactProvable 1 := by
  obtain ⟨tail, s, rfl, hsum⟩ := h
  obtain ⟨hp, hh, _⟩ := (soundConfig_iff _ _).mp hs
  have h : s.t = 1 ∨ s.h = 1 := by omega
  exact h.elim (fun he => he ▸ hp) (fun he => he ▸ hh)

theorem sound_candidate_completes (hn : ¬ ExactProvable 1) (n : Nat) (s : Store Nat)
    (hs : soundStore s) :
    ∃ out hist, soundStore out ∧ runHistory (commandCfgCode (n + 1) s) hist ∧
      modelListHead hist = commandCfgCode 0 out := by
  let first := commandCfgCode (n + 1) s
  obtain ⟨hist, hr, hh⟩ := command_totality (n + 1 : Nat) s first (modelListCons first 0)
    (runHistory_singleton first) (modelListHead_cons _ _)
  have hp := history_preserves hr ((soundConfig_iff _ _).mpr hs)
  rcases hh with hh | ⟨out, he⟩
  · exact False.elim (hn (halt_refutes hh hp))
  · exact ⟨out, hist, (soundConfig_iff _ _).mp (he ▸ hp), hr, he⟩

theorem zeroStore_sound : soundStore ⟨0, 0, 0, 0⟩ :=
  ⟨proved_zero, proved_zero, .zero⟩


end ZF192Support.ModelCommands
