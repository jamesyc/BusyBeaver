module
public import I0451.ArithmeticEffects

/-! Induction for loops whose register contents are definable functions
of the number of iterations, including nonstandard iteration counts. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime _root_.I0451.Decoder

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ReachesAt (start : V) (word : List Bool) (regs : Fin 9 → V) : Prop :=
  ∃ gap : V, (107 : V) ≤ (word.length : V) + gap ∧
    ModelReaches literal start (modelFrame word gap (modelRegisters regs))

private theorem frame_registers_definable (word : List Bool) (regs : V → Fin 9 → V)
    (regDefined : ∀ i, 𝚺ᴬ₁-Function₁[V] (fun n => regs n i)) :
    𝚺ᴬ₁-Function₂[V] (fun gap n => modelFrame word gap (modelRegisters (regs n))) := by
  apply modelRegisterFrame_defined word (fun v : Fin 2 → V => v 0) (fun v => regs (v 1))
  · definability
  · intro i
    let : 𝚺ᴬ₁-Function₁[V] (fun n => regs n i) := regDefined i
    have projection : 𝚺ᴬ₁.DefinableFunction (V := V) (fun v : Fin 2 → V => v 1) := by
      definability
    exact Bounding.HierarchySymbol.DefinableFunction₁.comp (F := fun n => regs n i) projection

private theorem reach_predicate_definable (start width : V) (frame : V → V → V)
    (arithmetic : 𝚺ᴬ₁-Function₂[V] frame) :
    𝚺ᴬ₁-Predicate[V] (fun n => ∃ gap : V, (107 : V) ≤ width + gap ∧
      ∃ t : V, trace literal t start = frame gap n) := by
  definability

theorem reachesAt_definable (start : V) (word : List Bool) (regs : V → Fin 9 → V)
    (regDefined : ∀ i, 𝚺ᴬ₁-Function₁[V] (fun n => regs n i)) :
    𝚺ᴬ₁-Predicate[V] (fun n => ReachesAt start word (regs n)) :=
  reach_predicate_definable start (word.length : V) _ (frame_registers_definable word regs regDefined)

theorem reachesAt_of_frame {start : V} {word : List Bool} {regs : Fin 9 → V} {f : ModelFrame V}
    (reach : ModelReaches literal start f.tape) (view : ModelRepresents f (pack word 0) regs)
    (width : word.length ≤ 94) :
    ReachesAt start word regs := by
  have fits : (word.length : V) ≤ f.slot :=
    le_trans (Nat.cast_le.mpr (width.trans (by decide : (94 : Nat) ≤ 107))) view.good.space
  have layout : f.tape = modelFrame word (f.slot - (word.length : V)) (modelRegisters regs) := by
    unfold ModelFrame.tape
    rw [view.registers]
    exact modelFrame_equal view.address
      ((sub_add_self_of_le view.good.wordFits).trans (sub_add_self_of_le fits).symm) _
  have space : (107 : V) ≤ (word.length : V) + (f.slot - (word.length : V)) := by
    rw [add_tsub_cancel_of_le fits]
    exact view.good.space
  exact ⟨_, space, layout ▸ reach⟩

theorem ReachesAt.frame {start : V} {word : List Bool} {regs : Fin 9 → V}
    (reach : ReachesAt start word regs) (address : PackedAddress word) :
    ∃ f : ModelFrame V, ModelReaches literal start f.tape ∧
      ModelRepresents f (pack word 0) regs := by
  obtain ⟨gap, space, ran⟩ := reach
  let f := makeModelFrame word gap (modelRegisters regs)
  have permanent : ModelPermanent f :=
    ⟨space, by simp [f, makeModelFrame], by simp [f, makeModelFrame, modelRegisters_length], address⟩
  have tapeEq : f.tape = modelFrame word gap (modelRegisters regs) := makeModelFrame_tape _ _ _
  exact ⟨f, by rw [tapeEq]; exact ran, ⟨permanent, rfl, rfl⟩⟩

/-- Compose any internally finite number of loop iterations whose
register effects have an arithmetic description. -/
theorem ModelEffect.repeat_until {cursor : Cursor} {left right : Edge} {middle : V → Fin 9 → V}
    (l : outgoing cursor false = some left) (r : outgoing cursor true = some right)
    (regs : V → Fin 9 → V) (limit : V)
    (regDefined : ∀ i, 𝚺ᴬ₁-Function₁[V] (fun n => regs n i))
    (enter : ∀ j < limit, ModelEffect left (regs j) .normal (middle j))
    (repeatBody : ∀ j < limit, ModelEffect right (middle j) (.restart 0) (regs (j + 1)))
    {sig : Signal} {output : Fin 9 → V}
    (finish : ModelEffect (.branch cursor) (regs limit) sig output) :
    ModelEffect (.branch cursor) (regs 0) sig output := by
  intro actual same word f path view
  obtain ⟨moved, rfl, children⟩ := same.branch_view
  obtain ⟨_, leftMoved, compatibleLeft⟩ := children false _ l
  obtain ⟨_, rightMoved, compatibleRight⟩ := children true _ r
  have width := path.length_le
  obtain ⟨part, partPath, packed⟩ := view.good.address
  have address : PackedAddress word := ⟨part, partPath, packed.trans view.address⟩
  have each : ∀ j ≤ limit, ReachesAt f.tape word (regs j) := by
    intro j
    induction j using ISigma1.sigma1_succ_induction with
    | zero =>
      intro _
      exact reachesAt_of_frame (ModelReaches.refl literal f.tape) view width
    | succ j ih =>
      intro fits
      have before := succ_le_iff_lt.mp fits
      obtain ⟨current, reach, atAddress⟩ := (ih (le_of_lt before)).frame address
      obtain ⟨after, moved, sameAddress⟩ :=
        ModelEffect.loopOnce leftMoved rightMoved ((enter j before).share compatibleLeft)
          ((repeatBody j before).share compatibleRight) path atAddress
      exact reachesAt_of_frame (reach.trans moved) sameAddress width
    | hP =>
      have reachable := reachesAt_definable f.tape word regs regDefined
      definability
  obtain ⟨last, reaches, atLast⟩ := (each limit (le_refl limit)).frame address
  exact ((finish.share same).run path atLast).prepend reaches


theorem ModelEffect.sequence {root : Cursor} {a b : Edge}
    {first middle last : Fin 9 → V}
    (left : outgoing root false = some a) (right : outgoing root true = some b)
    (firstRun : ModelEffect a first .normal middle) (lastRun : ModelEffect b middle .normal last) :
    ModelEffect (.branch root) first .normal last :=
  ModelEffect.rightExit left right firstRun lastRun rfl

theorem ModelEffect.if_zero {root test : Cursor} {r : Fin 9} {body : Edge}
    {s done : Fin 9 → V}
    (left : outgoing root false = some (.branch test))
    (right : outgoing root true = some body)
    (dec : outgoing test false = some (.instruction (.dec r)))
    (skip : outgoing test true = some (.instruction (.break 0)))
    (effect : s r = 0 → ModelEffect body s .normal done) :
    ModelEffect (.branch root) s .normal (if s r = 0 then done else putRegister s r (s r - 1)) := by
  by_cases zero : s r = 0
  · rw [ite_eq_left zero]
    have before : ModelEffect (.branch test) s .normal s :=
      .leftExit dec (.dec_zero r s zero) rfl
    exact ModelEffect.sequence left right before (effect zero)
  · obtain ⟨n, positive⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr zero)
    rw [ite_eq_right zero, positive, add_tsub_cancel_right]
    have before : ModelEffect (.branch test) s (.break 0) (putRegister s r n) :=
      .rightExit dec skip (.dec_pos r s n positive) (.breakLeaf 0 _) rfl
    exact ModelEffect.leftExit left before rfl

/-- Counting with any definable state formula and a normally returning body. -/
theorem ModelEffect.while_count {root block : Cursor} {body : Edge} {source : Fin 9}
    (left : outgoing root false = some (.instruction (.dec source)))
    (right : outgoing root true = some (.branch block))
    (enterBody : outgoing block false = some body)
    (restart : outgoing block true = some (.instruction (.restart 1)))
    (states : V → Fin 9 → V) (limit : V)
    (definable : ∀ i, 𝚺ᴬ₁-Function₁[V] (fun j => states j i))
    (source_eq : ∀ j, states j source = limit - j)
    (bodyEffect : ∀ j < limit,
      ModelEffect body (putRegister (states j) source (limit - (j + 1))) .normal (states (j + 1))) :
    ModelEffect (.branch root) (states 0) .normal (states limit) := by
  have enters (j : V) (before : j < limit) :
      ModelEffect (.instruction (.dec source)) (states j) .normal
        (putRegister (states j) source (limit - (j + 1))) := by
    apply ModelEffect.dec_pos
    rw [source_eq]
    simpa only [zero_add, add_zero] using (sub_succ_add_succ before (0 : V)).symm
  have repeats (j : V) (before : j < limit) :
      ModelEffect (.branch block) (putRegister (states j) source (limit - (j + 1)))
        (.restart 0) (states (j + 1)) :=
    .rightExit enterBody restart (bodyEffect j before) (ModelEffect.restartLeaf 1 _) rfl
  have zero : states limit source = 0 := by rw [source_eq, Arithmetic.sub_self]
  have finish : ModelEffect (.branch root) (states limit) .normal (states limit) :=
    ModelEffect.leftExit left (ModelEffect.dec_zero source _ zero) rfl
  exact ModelEffect.repeat_until left right states limit definable enters repeats finish
def modelAddAt (selected : Fin 9 → Bool) (amount : V) (s : Fin 9 → V) : Fin 9 → V :=
  fun i => if selected i then s i + amount else s i

theorem ModelEffect.increment_one (r : Fin 9) (s : Fin 9 → V) :
    ModelEffect (.instruction (.inc r)) s .normal (modelAddAt (· == r) 1 s) := by
  have same : putRegister s r (s r + 1) = modelAddAt (· == r) 1 s := by
    funext i
    by_cases hit : i = r <;> simp [putRegister, modelAddAt, hit]
  rw [← same]
  exact ModelEffect.inc r s

/-- A closed counting loop clears its source and adds that source's
initial value multiplied by a fixed stride to each selected register. -/
theorem ModelEffect.while_add_scaled {root block : Cursor} {body : Edge} {source : Fin 9}
    (left : outgoing root false = some (.instruction (.dec source)))
    (right : outgoing root true = some (.branch block))
    (enterBody : outgoing block false = some body)
    (restart : outgoing block true = some (.instruction (.restart 1)))
    (selected : Fin 9 → Bool) (sourceFixed : selected source = false) (stride : V)
    (runs : ∀ regs : Fin 9 → V, ModelEffect body regs .normal (modelAddAt selected stride regs))
    (initial : Fin 9 → V) :
    ModelEffect (.branch root) initial .normal
      (putRegister (modelAddAt selected (stride * initial source) initial) source 0) := by
  let atClock (j : V) : Fin 9 → V :=
    putRegister (modelAddAt selected (stride * j) initial) source (initial source - j)
  have start : atClock 0 = initial := by
    funext i
    by_cases sourceIndex : i = source
    · subst i
      simp only [atClock, putRegister_at, Arithmetic.sub_zero]
    · simp [atClock, putRegister, sourceIndex, modelAddAt]
  have done : atClock (initial source) =
      putRegister (modelAddAt selected (stride * initial source) initial) source 0 := by
    simp only [atClock, Arithmetic.sub_self]
  have defined (i : Fin 9) : 𝚺ᴬ₁-Function₁[V] (fun j => atClock j i) := by
    by_cases isSource : i = source <;>
      by_cases chosen : selected i = true <;>
      simp only [atClock, putRegister, modelAddAt, isSource, chosen, ite_true, ite_false] <;> definability
  let afterDec (j : V) : Fin 9 → V :=
    putRegister (atClock j) source (initial source - (j + 1))
  have bodyEffect (j : V) :
      ModelEffect body (afterDec j) .normal (atClock (j + 1)) := by
    have updated : modelAddAt selected stride (afterDec j) = atClock (j + 1) := by
      funext i
      by_cases isSource : i = source
      · subst i
        simp [atClock, afterDec, modelAddAt, sourceFixed]
      · by_cases chosen : selected i = true <;>
          simp [atClock, afterDec, modelAddAt, putRegister, isSource, chosen, mul_add_distr, add_assoc]
    have bodyEffect := runs (afterDec j)
    rw [updated] at bodyEffect
    exact bodyEffect
  have exactSource (j : V) : atClock j source = initial source - j := putRegister_at _ _ _
  have all := ModelEffect.while_count left right enterBody restart atClock (initial source) defined exactSource
    (fun j _ => bodyEffect j)
  rw [start, done] at all
  exact all

theorem ModelEffect.while_add {root block : Cursor} {body : Edge} {source : Fin 9}
    (left : outgoing root false = some (.instruction (.dec source)))
    (right : outgoing root true = some (.branch block))
    (enterBody : outgoing block false = some body)
    (restart : outgoing block true = some (.instruction (.restart 1)))
    (selected : Fin 9 → Bool) (sourceFixed : selected source = false)
    (runs : ∀ regs : Fin 9 → V, ModelEffect body regs .normal (modelAddAt selected 1 regs))
    (initial : Fin 9 → V) :
    ModelEffect (.branch root) initial .normal
      (putRegister (modelAddAt selected (initial source) initial) source 0) := by
  simpa using ModelEffect.while_add_scaled left right enterBody restart selected sourceFixed 1 runs initial

def modelTransfer (source target : Fin 9) (regs : Fin 9 → V) : Fin 9 → V :=
  putRegister (modelAddAt (· == target) (regs source) regs) source 0

theorem ModelEffect.move_one {root block : Cursor} {source target : Fin 9}
    (distinct : target ≠ source)
    (left : outgoing root false = some (.instruction (.dec source)))
    (right : outgoing root true = some (.branch block))
    (enterBody : outgoing block false = some (.instruction (.inc target)))
    (restart : outgoing block true = some (.instruction (.restart 1)))
    (regs : Fin 9 → V) :
    ModelEffect (.branch root) regs .normal (modelTransfer source target regs) := by
  apply ModelEffect.while_add left right enterBody restart (· == target)
  · simp [Ne.symm distinct]
  · intro before
    exact ModelEffect.increment_one target before

end I0451.Arithmetization
