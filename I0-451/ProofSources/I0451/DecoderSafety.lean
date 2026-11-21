module
public import I0451.Decoder
public import I0451.Dispatch

/-! Safety of all paths in the literal decoder. The finite data bounds
the trailing zeros and the number of already read jump delimiters. Lean
checks the bounds locally and propagates them along arbitrary paths. -/

@[expose] public section
namespace I0451.Decoder

open _root_.I0451.Runtime

def leadingZeros : List Bool → Nat
  | false :: rest => leadingZeros rest + 1
  | _ => 0

private theorem safe_from_bound {word : List Bool} (safe : SafeDispatch 0 word)
    {n : Nat} (bound : n + leadingZeros word ≤ 7) : SafeDispatch n word := by
  induction word generalizing n with
  | nil => trivial
  | cons b rest ih =>
    cases b
    · have next : n + 1 + leadingZeros rest ≤ 7 := by
        simp only [leadingZeros] at bound
        omega
      exact ⟨by simp [zeroRun]; omega, ih safe.tail next⟩
    · exact ⟨by simp [zeroRun], safe.tail⟩

private theorem safe_extend {word : List Bool} (safe : SafeDispatch 0 word)
    {b : Bool} (bound : leadingZeros (b :: word) ≤ 7) : SafeDispatch 0 (b :: word) := by
  cases b
  · simp only [leadingZeros] at bound
    exact ⟨by decide, safe_from_bound (n := 1) safe (by omega)⟩
  · exact ⟨by decide, safe⟩

structure Safety where
  live : Bool
  run : Nat
  zeros : Nat
  ones : Nat

def safety (q : Nat) (a b : Bool) : Safety :=
  if q < 451 then
    let code := digit decoderSafety (4 * q + a.toNat + 2 * b.toNat)
    let value := code - 1
    ⟨code != 0, value % 8, value / 8 % 2, value / 16⟩
  else ⟨false, 0, 0, 0⟩

def Safety.withRead (s : Safety) (b : Bool) : Safety :=
  ⟨s.live, zeroRun s.run b, s.zeros + (!b).toNat, s.ones + b.toNat⟩

def Safety.Fits (s : Safety) (reversed : List Bool) : Prop :=
  s.live = true ∧ leadingZeros reversed ≤ s.run ∧
    s.zeros ≤ reversed.count false ∧ s.ones ≤ reversed.count true

private theorem Safety.extend_fits {s : Safety} {word : List Bool} (fits : s.Fits word) (b : Bool) :
    (s.withRead b).Fits (b :: word) := by
  obtain ⟨live, zeroBound, zeros, ones⟩ := fits
  cases b <;> simp [Safety.Fits, Safety.withRead, leadingZeros, zeroRun, live, zeros, ones, zeroBound]

def LegalExit (exit : Exit) (rev : List Bool) : Prop :=
  match exit with
  | .issue q => issuing q = true ∧ (decStates.contains q = true → 0 < rev.count false)
  | .erase q => returning q = true ∧ ∃ old, rev = true :: old ∧
      (q = breakOne → 0 < old.count false) ∧ (q = continueOne → 0 < old.count true)
  | .fused => ∃ old, rev = true :: true :: old ∧ 0 < old.count true

private def checkLeaf (s : Safety) (b : Bool) (exit : Exit) : Bool :=
  match exit with
  | .issue q => !decStates.contains q || 0 < (s.withRead b).zeros
  | .erase q => (q != breakOne || 0 < s.zeros) && (q != continueOne || 0 < s.ones)
  | .fused => 2 ≤ s.ones

private def checkMove (q : Nat) (a b read : Bool) : Bool :=
  let s := safety q a b
  let extended := s.withRead read
  !s.live || (extended.run ≤ 7 &&
    match arm q a b read with
    | none => false
    | some (.inl t) =>
      let target := safety t read a
      target.live && (extended.run ≤ target.run) &&
        (target.zeros ≤ extended.zeros) && (target.ones ≤ extended.ones)
    | some (.inr exit) => checkLeaf s read exit)

private def checkMoves (states : List Nat) : Bool :=
  states.all (fun q => [false, true].all (fun a => [false, true].all
    (fun b => [false, true].all (checkMove q a b))))

private theorem checkedLow : checkMoves (List.range 226) = true := by decide +kernel
private theorem checkedHigh : checkMoves (List.range' 226 225) = true := by decide +kernel

private theorem check_move {q : Nat} {a b read : Bool} {rev : List Bool}
    (fits : (safety q a b).Fits rev) : checkMove q a b read = true := by
  have live := fits.1
  have bound : q < 451 := by
    by_cases inRange : q < 451
    · exact inRange
    · simp [safety, inRange] at live
  have all : [false, true].all (fun a => [false, true].all
      (fun b => [false, true].all (checkMove q a b))) = true := by
    by_cases low : q < 226
    · exact List.all_eq_true.mp checkedLow q (List.mem_range.mpr low)
    · apply List.all_eq_true.mp checkedHigh q
      simp only [List.mem_range'_1]
      omega
  have member (bit : Bool) : bit ∈ [false, true] := by cases bit <;> decide
  exact List.all_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp all a (member a)) b (member b))
    read (member read)

private theorem legalLeaf {q : Nat} {a b read : Bool} {rev : List Bool}
    {w : Window} {exit : Exit}
    (outcome : Outcome q a b read w (.inr exit))
    (fits : (safety q a b).Fits rev)
    (head : rev.head? = none ∨ rev.head? = some a)
    (passed : checkLeaf (safety q a b) read exit = true) :
    LegalExit exit (read :: rev) := by
  cases outcome with
  | issue t issued =>
    refine ⟨issued, fun dec => ?_⟩
    have after := Safety.extend_fits fits read
    simp only [checkLeaf, dec, Bool.not_true, Bool.false_or, decide_eq_true_eq] at passed
    exact Nat.lt_of_lt_of_le passed after.2.2.1
  | one t returned isOne =>
    subst read
    refine ⟨returned, rev, rfl, ?_, ?_⟩
    · intro label
      have h := (Bool.and_eq_true _ _).mp passed |>.1
      simp only [label, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at h
      exact Nat.lt_of_lt_of_le h fits.2.2.1
    · intro label
      have h := (Bool.and_eq_true _ _).mp passed |>.2
      simp only [label, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at h
      exact Nat.lt_of_lt_of_le h fits.2.2.2
  | two isOne previous =>
    subst read
    subst a
    have bound : 2 ≤ rev.count true :=
      Nat.le_trans (by simpa only [checkLeaf, decide_eq_true_eq] using passed) fits.2.2.2
    cases rev with
    | nil => simp at bound
    | cons x rest =>
      have first : x = true := by simpa using head
      subst x
      refine ⟨rest, rfl, ?_⟩
      have count : (true :: rest).count true = rest.count true + 1 := by simp
      rw [count] at bound
      omega

/-- Any completed parse from a suitable prefix has a safe reversed word
and enough genuine markers for its return operation. -/
theorem decoded_safe {fuel q right : Nat} {a b : Bool} {result : Decoded} {rev : List Bool}
    (parsed : decode fuel q a b right = some result)
    (fits : (safety q a b).Fits rev) (safe : SafeDispatch 0 rev)
    (head : rev.head? = none ∨ rev.head? = some a) :
    SafeDispatch 0 (result.word.reverse ++ rev) ∧ LegalExit result.exit (result.word.reverse ++ rev) := by
  induction fuel generalizing q right a b result rev with
  | zero => simp [decode] at parsed
  | succ fuel ih =>
    cases found : arm q a b (bit right) with
    | none => simp [decode, found] at parsed
    | some target =>
      have checked := check_move (read := bit right) fits
      have extended := Safety.extend_fits fits (bit right)
      simp only [checkMove, fits.1, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        decide_eq_true_eq, found] at checked
      have safeNext : SafeDispatch 0 (bit right :: rev) :=
        safe_extend safe (Nat.le_trans extended.2.1 checked.1)
      cases target with
      | inl t =>
        cases tail : decode fuel t (bit right) a (right / 2) with
        | none => simp [decode, found, tail] at parsed
        | some mid =>
          simp only [decode, found, tail, Option.map_some, Option.some.injEq] at parsed
          subst result
          have constraints := checked.2
          simp only [Bool.and_eq_true, decide_eq_true_eq] at constraints
          obtain ⟨⟨⟨live, retainedRun⟩, retainedZeros⟩, retainedOnes⟩ := constraints
          have child : (safety t (bit right) a).Fits (bit right :: rev) :=
            ⟨live, Nat.le_trans extended.2.1 retainedRun,
              Nat.le_trans retainedZeros extended.2.2.1, Nat.le_trans retainedOnes extended.2.2.2⟩
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using
            ih tail child safeNext (Or.inr rfl)
      | inr exit =>
        obtain ⟨n, win, _, _, outcome⟩ := arm_sound found
        simp only [decode, found, Option.some.injEq] at parsed
        subst result
        exact ⟨safeNext, legalLeaf outcome fits head checked.2⟩

theorem root_decoded_safe {right : Nat} {d : Decoded}
    (parsed : decode 94 root true false right = some d) :
    SafeDispatch 0 d.word.reverse ∧ LegalExit d.exit d.word.reverse := by
  have initial : (safety root true false).Fits [] := by
    change (safety root true false).live = true ∧ 0 ≤ (safety root true false).run ∧
      (safety root true false).zeros ≤ 0 ∧ (safety root true false).ones ≤ 0
    decide +kernel
  simpa only [List.append_nil] using decoded_safe parsed initial trivial (Or.inl rfl)

end I0451.Decoder
