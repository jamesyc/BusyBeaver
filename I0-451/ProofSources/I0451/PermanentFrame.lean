module
public import I0451.Address
public import I0451.DecoderSafety
public import I0451.Bootstrap

/-! Once there is enough space, every instruction can execute without
crossing the first register. The interpreter preserves this invariant and
the decoder-prefix invariant for the next address. -/
@[expose] public section
namespace I0451.Runtime

open _root_.I0451.Decoder

structure Permanent (f : RegisterFrame) : Prop where
  space : 107 ≤ f.slot
  wordFits : f.word.length ≤ f.slot
  enoughRegisters : 11 ≤ f.regs.length
  address : PackedAddress f.word

def Preserves : MacroResult → Prop
  | .invalid => False
  | .halt => True
  | .next f => Permanent f

private theorem permanent_frame {word : List Bool} {gap : Nat} {regs : List Nat}
    (space : 107 ≤ word.length + gap) (enough : 11 ≤ regs.length)
    (address : PackedAddress word) : Permanent (makeFrame word gap regs) :=
  ⟨space, Nat.le_add_right _ _, enough, address⟩

theorem safe_suffix {left right : List Bool} {n : Nat}
    (safe : SafeDispatch n (left ++ right)) : SafeDispatch 0 right := by
  induction left generalizing n with
  | nil => exact safe.mono (Nat.zero_le _)
  | cons b bs ih => exact ih safe.2

theorem cutRegister_exists {α : Type} {i : Nat} {regs : List α} (bound : i + 2 ≤ regs.length) :
    ∃ cut, cutRegister i regs = some cut := by
  have remaining : 2 ≤ (regs.reverse.drop i).length := by
    simp only [List.length_drop, List.length_reverse]
    omega
  have suffix : (regs.reverse.take i).reverse.length = i := by
    simp [List.length_take, Nat.min_eq_left (show i ≤ regs.length by omega)]
  cases found : regs.reverse.drop i with
  | nil => simp [found] at remaining
  | cons value rest =>
    cases rest with
    | nil => simp [found] at remaining
    | cons last before =>
      exact ⟨⟨before.reverse, last, value, (regs.reverse.take i).reverse⟩,
        by simp [cutRegister, found, suffix]⟩

theorem registerAddress_exists {q : Nat} (issued : issuing q = true) (notHalt : q ≠ 451) :
    ∃ op i, registerAddress q = some (op, i) := by
  simp only [issuing, Bool.or_eq_true, beq_iff_eq] at issued
  have locate : incStates.contains q = true ∨ decStates.contains q = true := by
    rcases issued with ⟨h | h⟩ | h
    · exact (notHalt h).elim
    · exact Or.inl h
    · exact Or.inr h
  by_cases left : incStates.idxOf q < 9
  · exact ⟨.inc, incStates.idxOf q, by simp [registerAddress, left]⟩
  · have right : decStates.idxOf q < 9 := by
      rcases locate with h | h
      · exact (left (List.idxOf_lt_length_of_mem (List.contains_iff_mem.mp h))).elim
      · exact List.idxOf_lt_length_of_mem (List.contains_iff_mem.mp h)
    exact ⟨.dec, decStates.idxOf q, by simp [registerAddress, left, right]⟩

theorem dec_issued {q i : Nat} (eq : registerAddress q = some (.dec, i)) :
    decStates.contains q = true := by
  have ⟨bound, code⟩ := registerAddress_sound eq
  rw [code]
  change decStates.contains (decStates[i]?.getD decrement) = true
  have atIndex : i < decStates.length := bound
  rw [List.getElem?_eq_getElem atIndex]
  exact List.contains_iff_mem.mpr (List.mem_of_getElem rfl)

private theorem register_preserves {word : List Bool} {gap q i : Nat} {regs : List Nat}
    {op : RegisterOp} (space : 107 ≤ word.length + gap) (room : i + 4 ≤ gap)
    (enough : 11 ≤ regs.length)
    (addr : registerAddress q = some (op, i))
    (path : AddressPath root true false word) (safe : SafeDispatch 0 word.reverse)
    (markers : decStates.contains q = true → 0 < word.reverse.count false) :
    Preserves (runRegister word gap regs op i) := by
  have bound := (registerAddress_sound addr).1
  obtain ⟨cut, cutEq⟩ := cutRegister_exists (i := i) (regs := regs) (by omega)
  simp only [runRegister, ite_eq_left room, cutEq]
  have len := (cutRegister_sound cutEq).1
  have backwardsLength : word.length ≤ (carry word.reverse).reverse.length := by
    simpa only [List.length_reverse] using carry_length_ge word.reverse
  have updated := path.carry_packed
  cases op with
  | inc =>
    apply permanent_frame (by omega) _ updated
    rw [len] at enough
    simpa using enough
  | dec =>
    have someZero := markers (dec_issued addr)
    cases v : cut.value with
    | succ value =>
      apply permanent_frame (by omega) _ updated
      rw [len] at enough
      simpa using enough
    | zero =>
      obtain ⟨n, rest, found⟩ := cutAddress_exists someZero
      simp only [found]
      have split := cutAddress_sound found
      simp only [Bool.not_false] at split
      have eq : word.reverse = (List.replicate n true ++ [false]) ++ rest := by
        simpa only [List.append_assoc, List.singleton_append, List.nil_append] using split
      have safeRest : SafeDispatch 0 rest := safe_suffix (eq ▸ safe)
      rw [ite_eq_left safeRest]
      have earlier := path.reverse_suffix eq
      have pathLength := congrArg List.length split
      simp only [List.length_reverse, List.length_append, List.length_replicate, List.length_cons] at pathLength
      have larger := carry_length_ge rest
      have nextAddress : PackedAddress (carry rest).reverse := by
        simpa only [List.reverse_reverse] using earlier.carry_packed
      apply permanent_frame _ enough nextAddress
      simp only [List.length_reverse]
      omega

private theorem jump_preserves {q gap : Nat} {rev : List Bool} {regs : List Nat}
    (space : 107 ≤ rev.length + gap) (enough : 11 ≤ regs.length)
    (target : returning q = true)
    (zeroMarker : q = breakOne → 0 < rev.count false)
    (oneMarker : q = continueOne → 0 < rev.count true)
    (safe : SafeDispatch 0 rev) (path : AddressPath root true false rev.reverse) :
    Preserves (runJump q rev gap regs) := by
  by_cases q0 : q = continueZero
  · rw [runJump, ite_eq_left q0, ite_eq_left safe]
    apply permanent_frame (by simpa only [List.length_reverse] using space) enough path.packed
  · by_cases q1 : q = continueOne
    · obtain ⟨n, rest, cut⟩ := cutAddress_exists (oneMarker q1)
      have split := cutAddress_sound cut
      simp only [Bool.not_true] at split
      have join : rev = (List.replicate n false ++ [true]) ++ rest := by
        simpa only [List.append_assoc, List.singleton_append, List.nil_append] using split
      have safeRest : SafeDispatch 0 rest := safe_suffix (join ▸ safe)
      simp only [runJump, ite_eq_right q0, ite_eq_left q1, cut, ite_eq_left safeRest]
      have earlier := path.reverse_suffix (by simpa only [List.reverse_reverse] using join)
      have len := congrArg List.length split
      simp only [List.length_append, List.length_replicate, List.length_cons] at len
      apply permanent_frame _ enough earlier.packed
      simp only [List.length_reverse]
      omega
    · have qb : q = breakOne := by
        simp only [returning, Bool.or_eq_true, beq_iff_eq, q0, q1, or_false] at target
        exact target
      obtain ⟨n, rest, cut⟩ := cutAddress_exists (zeroMarker qb)
      have split := cutAddress_sound cut
      simp only [Bool.not_false] at split
      have join : rev = (List.replicate n true ++ [false]) ++ rest := by
        simpa only [List.append_assoc, List.singleton_append, List.nil_append] using split
      have safeRest : SafeDispatch 0 rest := safe_suffix (join ▸ safe)
      simp only [runJump, ite_eq_right q0, ite_eq_right q1, ite_eq_left qb, cut, ite_eq_left safeRest]
      have earlier := path.reverse_suffix (by simpa only [List.reverse_reverse] using join)
      have len := congrArg List.length split
      simp only [List.length_append, List.length_replicate, List.length_cons] at len
      have larger := carry_length_ge rest
      have nextAddress : PackedAddress (carry rest).reverse := by
        simpa only [List.reverse_reverse] using earlier.carry_packed
      apply permanent_frame _ enough nextAddress
      simp only [List.length_reverse]
      omega

theorem macroStep_preserves {f : RegisterFrame} (good : Permanent f) :
    Preserves (macroStep f) := by
  have canDecode : (Decoder.decode 94 root true false (pack f.word 0)).isSome = true :=
    Decoder.decode_total (by rw [Decoder.root_rank]; decide) (by rw [Decoder.root_rank]; decide)
  obtain ⟨d, parsed⟩ := Option.isSome_iff_exists.mp canDecode
  have decoded := Decoder.decode_sound parsed
  have remains : d.rest = 0 := good.address.no_stray parsed
  have enough : d.word.length ≤ f.slot := Nat.le_trans decoded.2.1 (by have := good.space; omega)
  have slotEq : d.word.length + (f.slot - d.word.length) = f.slot := by omega
  let gap := f.slot - d.word.length
  have big : 107 ≤ d.word.length + gap := slotEq.symm ▸ good.space
  have fitted : f.word.length ≤ f.slot ∧ d.word.length ≤ f.slot ∧ d.rest = 0 :=
    ⟨good.wordFits, enough, remains⟩
  simp only [macroStep, parsed, ite_eq_left fitted]
  obtain ⟨safe, legal⟩ := root_decoded_safe parsed
  have path := decoded_address parsed
  cases exitEq : d.exit with
  | issue q =>
    have mark : LegalExit (.issue q) d.word.reverse := exitEq ▸ legal
    by_cases last : q = 451
    · simp [last, Preserves]
    · obtain ⟨op, i, addr⟩ := registerAddress_exists mark.1 last
      have bounded := (registerAddress_sound addr).1
      have room : i + 4 ≤ gap := by have := decoded.2.1; omega
      simpa only [ite_eq_right last, ite_eq_left safe, addr] using
        register_preserves big room good.enoughRegisters addr path safe mark.2
  | erase q =>
    have mark : LegalExit (.erase q) d.word.reverse := exitEq ▸ legal
    obtain ⟨returned, rev, split, zeroMarker, oneMarker⟩ := mark
    have before := path.reverse_suffix (cleared := [true]) (by simpa using split)
    have len := congrArg List.length split
    simp only [List.length_reverse, List.length_cons] at len
    have safeBefore : SafeDispatch 0 rev := by
      rw [split] at safe
      exact safe.tail
    simpa only [split] using
      jump_preserves (gap := gap + 1) (by omega) good.enoughRegisters returned
        zeroMarker oneMarker safeBefore before
  | fused =>
    have mark : LegalExit .fused d.word.reverse := exitEq ▸ legal
    obtain ⟨rev, split, oneMarker⟩ := mark
    have before := path.reverse_suffix (cleared := [true, true]) (by simpa using split)
    have len := congrArg List.length split
    simp only [List.length_reverse, List.length_cons] at len
    have safeBefore : SafeDispatch 0 rev := by
      rw [split] at safe
      exact safe.tail.tail
    have different : continueOne ≠ breakOne := by decide +kernel
    simpa only [split] using
      jump_preserves (gap := gap + 2) (by omega) good.enoughRegisters
        (show returning continueOne = true by decide +kernel)
        (fun h => (different h).elim) (fun _ => oneMarker) safeBefore before

end I0451.Runtime
