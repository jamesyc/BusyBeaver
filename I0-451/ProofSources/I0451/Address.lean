module
public import I0451.Interpreter

/-! Valid instruction addresses are prefixes of decoder paths. A new
address is a previously visited prefix, or a switch to the other branch
at its last bit. Bits cleared by carry or jump become gap cells. -/

@[expose] public section
namespace I0451.Decoder

open _root_.I0451.Runtime

/-- A prefix can stop at either arm of its last control. Every read
before the last must be an internal transition. -/
inductive AddressPath : Nat → Bool → Bool → List Bool → Prop where
  | empty (q : Nat) (a b : Bool) : AddressPath q a b []
  | last (q : Nat) (a b read : Bool) : AddressPath q a b [read]
  | more (q : Nat) (a b read : Bool) (t : Nat) {word : List Bool}
      (edge : arm q a b read = some (.inl t)) (tail : AddressPath t read a word) :
      AddressPath q a b (read :: word)

theorem decoded_address {fuel q right : Nat} {a b : Bool} {result : Decoded}
    (parsed : decode fuel q a b right = some result) :
    AddressPath q a b result.word := by
  induction fuel generalizing q a b right result with
  | zero => simp [decode] at parsed
  | succ fuel ih =>
    cases edge : arm q a b (bit right) with
    | none => simp [decode, edge] at parsed
    | some choice =>
      cases choice with
      | inr exit =>
        simp only [decode, edge, Option.some.injEq] at parsed
        subst result
        exact .last q a b (bit right)
      | inl t =>
        cases child : decode fuel t (bit right) a (right / 2) with
        | none => simp [decode, edge, child] at parsed
        | some step =>
          simp only [decode, edge, child, Option.map_some, Option.some.injEq] at parsed
          subst result
          exact .more q a b (bit right) t edge (ih child)

theorem AddressPath.take {q : Nat} {a b : Bool} {word : List Bool}
    (proof : AddressPath q a b word) (len : Nat) :
    AddressPath q a b (word.take len) := by
  induction proof generalizing len with
  | empty q a b => simpa only [List.take_nil] using AddressPath.empty q a b
  | last q a b read =>
    cases len
    · exact .empty q a b
    · simpa only [List.take_succ_cons, List.take_nil] using AddressPath.last q a b read
  | more q a b read t edge tail ih =>
    cases len with
    | zero => exact .empty q a b
    | succ n => exact .more q a b read t edge (ih n)

theorem AddressPath.initial {q : Nat} {a b : Bool} {part rest : List Bool}
    (h : AddressPath q a b (part ++ rest)) : AddressPath q a b part := by
  simpa using h.take part.length

theorem AddressPath.reverse_suffix {q : Nat} {a b : Bool} {word cleared rev : List Bool}
    (path : AddressPath q a b word) (split : word.reverse = cleared ++ rev) :
    AddressPath q a b rev.reverse := by
  have eq := congrArg List.reverse split
  simp only [List.reverse_reverse, List.reverse_append] at eq
  rw [eq] at path
  exact path.initial

private theorem AddressPath.internal {q : Nat} {a b read : Bool} {tail : List Bool}
    (path : AddressPath q a b (read :: tail)) (nonempty : tail ≠ []) :
    ∃ t, arm q a b read = some (.inl t) ∧ AddressPath t read a tail := by
  cases path with
  | last => contradiction
  | more q a b read t edge path => exact ⟨t, edge, path⟩

theorem AddressPath.branch {q : Nat} {a b read : Bool} {part rest : List Bool}
    (path : AddressPath q a b (part ++ read :: rest)) (new : Bool) :
    AddressPath q a b (part ++ [new]) := by
  induction part generalizing q a b with
  | nil => exact .last q a b new
  | cons old part ih =>
    rw [List.cons_append] at path ⊢
    obtain ⟨t, edge, tail⟩ := path.internal (by simp)
    exact .more q a b old t edge (ih tail)

private theorem rest_of_zero {fuel q : Nat} {a b : Bool} {d : Decoded}
    (parsed : decode fuel q a b 0 = some d) : d.rest = 0 := by
  have h := (decode_sound parsed).1
  rw [pack_value d.word] at h
  have zero : 2 ^ d.word.length * d.rest = 0 := by omega
  exact (Nat.mul_eq_zero.mp zero).resolve_left (by exact Nat.ne_of_gt (Nat.pow_pos (by decide)))

theorem AddressPath.no_stray {q : Nat} {a b : Bool} {word : List Bool}
    (path : AddressPath q a b word) {fuel : Nat} {d : Decoded}
    (parsed : decode fuel q a b (pack word 0) = some d) : d.rest = 0 := by
  induction path generalizing fuel d with
  | empty q a b => exact rest_of_zero parsed
  | last q a b read =>
    cases fuel with
    | zero => simp [decode] at parsed
    | succ fuel =>
      cases edge : arm q a b read with
      | none => simp [decode, edge] at parsed
      | some target =>
        cases target with
        | inl t =>
          cases tail : decode fuel t read a 0 with
          | none => simp [decode, edge, tail] at parsed
          | some mid =>
            simp only [pack_cons, pack_nil, decode, bit_push, pop_push, edge, tail,
              Option.map_some, Option.some.injEq] at parsed
            subst d
            exact rest_of_zero (d := mid) tail
        | inr exit =>
          simp only [pack_cons, pack_nil, decode, bit_push, pop_push, edge,
            Option.some.injEq] at parsed
          subst d
          rfl
  | @more q a b read t word edge tail ih =>
    cases fuel with
    | zero => simp [decode] at parsed
    | succ fuel =>
      cases next : decode fuel t read a (pack word 0) with
      | none => simp [decode, edge, next] at parsed
      | some mid =>
        simp only [pack_cons, decode, bit_push, pop_push, edge, next,
          Option.map_some, Option.some.injEq] at parsed
        subst d
        exact ih (d := mid) next

/-- The nonzero part of an address is covered by a decoder prefix. -/
def PackedAddress (word : List Bool) : Prop :=
  ∃ part, AddressPath root true false part ∧ pack part 0 = pack word 0

theorem AddressPath.packed {word : List Bool} (h : AddressPath root true false word) :
    PackedAddress word := ⟨word, h, rfl⟩

theorem PackedAddress.no_stray {word : List Bool} (known : PackedAddress word)
    {d : Decoded} (parsed : decode 94 root true false (pack word 0) = some d) :
    d.rest = 0 := by
  obtain ⟨part, path, same⟩ := known
  rw [← same] at parsed
  exact path.no_stray parsed

theorem cutAddress_none {delimiter : Bool} {word : List Bool}
    (cut : cutAddress delimiter word = none) :
    word = List.replicate word.length (!delimiter) := by
  induction word with
  | nil => rfl
  | cons b bs ih =>
    by_cases same : b = delimiter
    · simp [cutAddress, same] at cut
    · cases tail : cutAddress delimiter bs with
      | none =>
        have bit : b = !delimiter := by cases b <;> cases delimiter <;> simp at same ⊢
        have sameTail := ih tail
        rw [List.length_cons, List.replicate_succ]
        exact congr (congrArg List.cons bit) sameTail
      | some pair => simp [cutAddress, same, tail] at cut

theorem cutAddress_exists {delimiter : Bool} {word : List Bool} (someBit : 0 < word.count delimiter) :
    ∃ n rest, cutAddress delimiter word = some (n, rest) := by
  cases cut : cutAddress delimiter word with
  | none =>
    have uniform := cutAddress_none cut
    rw [uniform] at someBit
    cases delimiter <;> simp at someBit
  | some pair => exact ⟨pair.1, pair.2, rfl⟩

theorem carry_ones (n : Nat) (rev : List Bool) :
    carry (List.replicate n true ++ rev) = List.replicate n false ++ carry rev := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, carry, ih]

theorem carry_length_ge (rev : List Bool) : rev.length ≤ (carry rev).length := by
  induction rev with
  | nil => decide
  | cons bit rev ih =>
    cases bit
    · exact Nat.le_refl _
    · simp only [carry, List.length_cons]
      omega

/-- Carry chooses the other arm at the last flipped bit. An overflow
leaves the all-zero address. -/
theorem AddressPath.carry_packed {word : List Bool} (path : AddressPath root true false word) :
    PackedAddress (carry word.reverse).reverse := by
  cases cut : cutAddress false word.reverse with
  | none =>
    have uniform := cutAddress_none cut
    simp only [Bool.not_false] at uniform
    have overflow (n : Nat) : carry (List.replicate n true) = List.replicate (n + 1) false := by
      rw [List.replicate_succ']
      simpa only [List.append_nil, carry] using carry_ones n []
    refine ⟨[], .empty _ _ _, ?_⟩
    rw [uniform, overflow, List.reverse_replicate, pack_zero_word]
    rfl
  | some pair =>
    obtain ⟨n, rest⟩ := pair
    have split := cutAddress_sound cut
    simp only [Bool.not_false] at split
    have old := congrArg List.reverse split
    simp only [List.reverse_reverse, List.reverse_append, List.reverse_replicate,
      List.reverse_cons, List.append_assoc, List.singleton_append] at old
    have original : AddressPath root true false (rest.reverse ++ false :: List.replicate n true) :=
      old ▸ path
    refine ⟨rest.reverse ++ [true], original.branch true, ?_⟩
    rw [split, carry_ones, carry, List.reverse_append, List.reverse_cons, List.reverse_replicate]
    simp [pack_append, pack_zero_word]

end I0451.Decoder
