module
public import I0451.ArithmeticInterpreter

/-! A register frame with enough tape and a checked program address
continues to have both properties after a literal instruction, in
every model of the arithmetic base. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime _root_.I0451.Decoder

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

structure ModelPermanent (f : ModelFrame V) : Prop where
  space : (107 : V) ≤ f.slot
  wordFits : (f.word.length : V) ≤ f.slot
  enoughRegisters : 11 ≤ f.regs.length
  address : PackedAddress f.word

def ModelPreserves : ModelMacroResult V → Prop
  | .invalid => False
  | .halt => True
  | .next f => ModelPermanent f

private theorem permanent_frame {word : List Bool} {gap : V} {regs : List V}
    (space : (107 : V) ≤ (word.length : V) + gap)
    (enough : 11 ≤ regs.length) (address : PackedAddress word) :
    ModelPermanent (makeModelFrame word gap regs) :=
  ⟨space, by simp [makeModelFrame], enough, address⟩

private theorem carry_space {reversed : List Bool} {gap : V}
    (space : (107 : V) ≤ (reversed.length : V) + gap) :
    (107 : V) ≤ ((carry reversed).reverse.length : V) + gap := by
  have width : (reversed.length : V) + gap ≤ ((carry reversed).length : V) + gap := by
    simpa only [add_comm gap] using
      (_root_.add_le_add_right (Nat.cast_le.mpr (carry_length_ge reversed)) gap)
  simpa only [List.length_reverse] using le_trans space width

private theorem recover_space {left other : Nat} {gap : V} (n : Nat)
    (len : left = n + (other + 1)) (space : (107 : V) ≤ (left : V) + gap) :
    (107 : V) ≤ (other : V) + (gap + (n : V) + 1) := by
  have same : (left : V) + gap = (other : V) + (gap + (n : V) + 1) := by
    rw [len, Nat.cast_add, Nat.cast_succ]
    ac_rfl
  rwa [← same]

private theorem model_register_preserves {word : List Bool} {gap : V} {q i : Nat}
    {regs : List V} {op : RegisterOp}
    (space : (107 : V) ≤ (word.length : V) + gap)
    (room : ((i + 1 : Nat) : V) + 1 + 1 + 1 ≤ gap) (enough : 11 ≤ regs.length)
    (addr : registerAddress q = some (op, i))
    (path : AddressPath root true false word) (safe : SafeDispatch 0 word.reverse)
    (markers : decStates.contains q = true → 0 < word.reverse.count false) :
    ModelPreserves (modelRunRegister word gap regs op i) := by
  classical
  have bound := (registerAddress_sound addr).1
  obtain ⟨cut, cutEq⟩ := cutRegister_exists (i := i) (regs := regs) (by omega)
  simp only [modelRunRegister, ite_eq_left room, cutEq]
  have shape := (cutRegister_sound cutEq).1
  have safeSpace : (107 : V) ≤ ((carry word.reverse).reverse.length : V) + gap :=
    carry_space (by simpa only [List.length_reverse] using space)
  have updated := path.carry_packed
  cases op with
  | inc =>
    apply permanent_frame safeSpace _ updated
    rw [shape] at enough
    simpa using enough
  | dec =>
    by_cases zero : cut.value = 0
    · obtain ⟨n, rest, found⟩ := cutAddress_exists (markers (dec_issued addr))
      simp only [ite_eq_left zero, found]
      have split := cutAddress_sound found
      simp only [Bool.not_false] at split
      have join : word.reverse = (List.replicate n true ++ [false]) ++ rest := by
        simpa only [List.append_assoc, List.singleton_append, List.nil_append] using split
      have restSafe : SafeDispatch 0 rest := safe_suffix (join ▸ safe)
      rw [ite_eq_left restSafe]
      have earlier := path.reverse_suffix join
      have length := congrArg List.length split
      simp only [List.length_reverse, List.length_append, List.length_replicate, List.length_cons] at length
      have nextAddress : PackedAddress (carry rest).reverse := by
        simpa only [List.reverse_reverse] using earlier.carry_packed
      have roomRest := recover_space n length space
      have moved := carry_space (reversed := rest) roomRest
      apply permanent_frame _ enough nextAddress
      exact le_trans moved (by simp [← add_assoc])
    · rw [ite_eq_right zero]
      apply permanent_frame _ _ updated
      · exact le_trans safeSpace (by simp [← add_assoc])
      · rw [shape] at enough
        simpa using enough

private theorem model_jump_preserves {q : Nat} {gap : V} {rev : List Bool} {regs : List V}
    (space : (107 : V) ≤ (rev.length : V) + gap) (enough : 11 ≤ regs.length)
    (target : returning q = true) (zeroMarker : q = breakOne → 0 < rev.count false)
    (oneMarker : q = continueOne → 0 < rev.count true)
    (safe : SafeDispatch 0 rev) (path : AddressPath root true false rev.reverse) :
    ModelPreserves (modelRunJump q rev gap regs) := by
  by_cases q0 : q = continueZero
  · simp only [modelRunJump, ite_eq_left q0, ite_eq_left safe]
    apply permanent_frame (by simpa only [List.length_reverse] using space) enough path.packed
  · by_cases q1 : q = continueOne
    · obtain ⟨n, rest, cut⟩ := cutAddress_exists (oneMarker q1)
      have split := cutAddress_sound cut
      simp only [Bool.not_true] at split
      have join : rev = (List.replicate n false ++ [true]) ++ rest := by
        simpa only [List.append_assoc, List.singleton_append, List.nil_append] using split
      have safeRest : SafeDispatch 0 rest := safe_suffix (join ▸ safe)
      simp only [modelRunJump, ite_eq_right q0, ite_eq_left q1, cut, ite_eq_left safeRest]
      have earlier := path.reverse_suffix (by simpa only [List.reverse_reverse] using join)
      have length := congrArg List.length split
      simp only [List.length_append, List.length_replicate, List.length_cons] at length
      apply permanent_frame _ enough earlier.packed
      simpa only [List.length_reverse] using recover_space n length space
    · have qb : q = breakOne := by
        simpa only [returning, Bool.or_eq_true, beq_iff_eq, q0, q1, or_false] using target
      obtain ⟨n, rest, cut⟩ := cutAddress_exists (zeroMarker qb)
      have split := cutAddress_sound cut
      simp only [Bool.not_false] at split
      have join : rev = (List.replicate n true ++ [false]) ++ rest := by
        simpa only [List.append_assoc, List.singleton_append, List.nil_append] using split
      have safeRest : SafeDispatch 0 rest := safe_suffix (join ▸ safe)
      simp only [modelRunJump, ite_eq_right q0, ite_eq_right q1, ite_eq_left qb, cut, ite_eq_left safeRest]
      have earlier := path.reverse_suffix (by simpa only [List.reverse_reverse] using join)
      have length := congrArg List.length split
      simp only [List.length_append, List.length_replicate, List.length_cons] at length
      have nextAddress : PackedAddress (carry rest).reverse := by
        simpa only [List.reverse_reverse] using earlier.carry_packed
      apply permanent_frame _ enough nextAddress
      exact carry_space (recover_space n length space)

theorem modelMacroStep_preserves {f : ModelFrame V} (good : ModelPermanent f) :
    ModelPreserves (modelMacroStep f) := by
  classical
  have canDecode : (Decoder.decode 94 root true false (pack f.word 0)).isSome = true :=
    Decoder.decode_total (by simpa only [Decoder.root_rank] using (show 0 < 94 by decide))
      (by simp only [Decoder.root_rank]; exact le_refl _)
  obtain ⟨d, parsed⟩ := Option.isSome_iff_exists.mp canDecode
  have decoded := Decoder.decode_sound parsed
  have remains : d.rest = 0 := good.address.no_stray parsed
  have enough : (d.word.length : V) ≤ f.slot :=
    le_trans (Nat.cast_le.mpr (decoded.2.1.trans (by decide : (94 : Nat) ≤ 107))) good.space
  let gap := f.slot - (d.word.length : V)
  have slotEq : (d.word.length : V) + gap = f.slot := add_tsub_cancel_of_le enough
  have big : (107 : V) ≤ (d.word.length : V) + gap := slotEq.symm ▸ good.space
  have fitted : (f.word.length : V) ≤ f.slot ∧ (d.word.length : V) ≤ f.slot ∧ d.rest = 0 :=
    ⟨good.wordFits, enough, remains⟩
  simp only [modelMacroStep, parsed, ite_eq_left fitted]
  obtain ⟨safe, legal⟩ := root_decoded_safe parsed
  have path := decoded_address parsed
  cases exitEq : d.exit with
  | issue q =>
    have mark : LegalExit (.issue q) d.word.reverse := exitEq ▸ legal
    by_cases last : q = 451
    · simp [last, ModelPreserves]
    · obtain ⟨op, i, addr⟩ := registerAddress_exists mark.1 last
      have bounded := (registerAddress_sound addr).1
      have needed : d.word.length + (i + 1) + 3 ≤ 107 := by
        have width := decoded.2.1
        omega
      have three : (3 : V) = 1 + 1 + 1 := by
        have numeric := congrArg (fun n : Nat => (n : V)) (show (3 : Nat) = 1 + 1 + 1 from rfl)
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using numeric
      have device : (d.word.length : V) + (((i + 1 : Nat) : V) + 1 + 1 + 1) ≤ (107 : V) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, three, add_assoc] using
          (Nat.cast_le (α := V)).mpr needed
      have room : ((i + 1 : Nat) : V) + 1 + 1 + 1 ≤ gap :=
        le_of_add_le_add_left (le_trans device big)
      simpa only [ite_eq_right last, ite_eq_left safe, addr] using
        model_register_preserves big room good.enoughRegisters addr path safe mark.2
  | erase q =>
    have mark : LegalExit (.erase q) d.word.reverse := exitEq ▸ legal
    obtain ⟨returned, rev, split, zeroMarker, oneMarker⟩ := mark
    have before := path.reverse_suffix (cleared := [true]) (by simpa using split)
    have length := congrArg List.length split
    simp only [List.length_reverse, List.length_cons] at length
    have safeBefore : SafeDispatch 0 rev := by
      rw [split] at safe
      exact safe.tail
    have afterRemoval : (107 : V) ≤ (rev.length : V) + (gap + 1) := by
      rwa [length, Nat.cast_succ, add_assoc, add_comm (1 : V) gap] at big
    simpa only [split] using model_jump_preserves afterRemoval good.enoughRegisters returned
      zeroMarker oneMarker safeBefore before
  | fused =>
    have mark : LegalExit .fused d.word.reverse := exitEq ▸ legal
    obtain ⟨rev, split, oneMarker⟩ := mark
    have before := path.reverse_suffix (cleared := [true, true]) (by simpa using split)
    have length := congrArg List.length split
    simp only [List.length_reverse, List.length_cons] at length
    have safeBefore : SafeDispatch 0 rev := by
      rw [split] at safe
      exact safe.tail.tail
    have different : continueOne ≠ breakOne := by decide +kernel
    have afterRemoval : (107 : V) ≤ (rev.length : V) + (gap + 1 + 1) := by
      have eq : (d.word.length : V) + gap = (rev.length : V) + (gap + 1 + 1) := by
        rw [length, Nat.cast_succ, Nat.cast_succ]
        ac_rfl
      rwa [eq] at big
    simpa only [split] using
      model_jump_preserves afterRemoval good.enoughRegisters
        (show returning continueOne = true by decide +kernel)
        (fun h => (different h).elim) (fun _ => oneMarker) safeBefore before

end I0451.Arithmetization
