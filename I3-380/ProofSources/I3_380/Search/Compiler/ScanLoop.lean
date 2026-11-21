module
public import I3_380.Search.Compiler.TokenComparison
@[expose] public section

namespace PalomarI3380.Compiler.Source

theorem le_pair_sum (a b : Nat) : a + b ≤ Cantor.pair a b := by
  have triangle : ∀ n, n ≤ Cantor.triangle n := by
    intro n
    cases n <;> simp [Cantor.triangle]
  rw [Cantor.pair_as_triangle]
  have h := triangle (a + b)
  omega

theorem rawFields_progress (code : Nat) :
    (rawFields code).rest + (rawFields code).arityField ≤ code := by
  have first := le_pair_sum (Cantor.unpair code).1 (Cantor.unpair code).2
  have second := Cantor.right_le
    (Cantor.unpair (Cantor.unpair code).2).1 (Cantor.unpair (Cantor.unpair code).2).2
  rw [Cantor.pair_unpair] at first second
  simp only [rawFields]
  omega

structure ScanResult where
  valid : Bool
  dictionaryRest : Nat
  frontRest : Nat

def scanLoop (need dictionary front : Nat) : ScanResult :=
  match need with
  | 0 => ⟨true, dictionary, front⟩
  | n + 1 =>
    let template := rawFields dictionary
    let actual := rawFields front
    let rest := scanLoop (n + (template.arityField - 1)) template.rest actual.rest
    ⟨(template.arityField != 0) && (template.arityField == actual.arityField) &&
      (template.tag == actual.tag) && rest.valid, rest.dictionaryRest, rest.frontRest⟩
termination_by need + dictionary
decreasing_by
  have h := rawFields_progress dictionary
  omega

theorem scanLoop_zero (dictionary front : Nat) :
    scanLoop 0 dictionary front = ⟨true, dictionary, front⟩ := by
  rw [scanLoop]

/-- Successful scanning recognizes exactly a forest of the required
size, and consumes matching words from the two streams. -/
theorem scanLoop_sound (need dictionary front : Nat)
    (accepted : (scanLoop need dictionary front).valid = true) :
    ∃ trees : List RawTerm, trees.length = need ∧
      dictionary = encodeTokens (trees.flatMap RawTerm.tokens) (scanLoop need dictionary front).dictionaryRest ∧
      front = encodeTokens (trees.flatMap RawTerm.tokens) (scanLoop need dictionary front).frontRest := by
  induction measureEq : need + dictionary using Nat.strongRecOn generalizing need dictionary front with
  | ind measure ih =>
    cases need with
    | zero => exact ⟨[], rfl, by rw [scanLoop_zero]; rfl, by rw [scanLoop_zero]; rfl⟩
    | succ count =>
      rw [scanLoop] at accepted ⊢
      simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at accepted
      obtain ⟨⟨⟨nonzero, sameArity⟩, sameTag⟩, valid⟩ := accepted
      let field := rawFields dictionary
      let input := rawFields front
      let arity := field.arityField - 1
      let rest := scanLoop (count + arity) field.rest input.rest
      have smaller : count + arity + field.rest < measure := by
        have h := rawFields_progress dictionary
        dsimp only [arity, field]
        omega
      obtain ⟨forest, hLen, hDictionary, hFront⟩ := ih _ smaller _ _ _ valid rfl
      change forest.length = count + arity at hLen
      let children := forest.take arity
      let siblings := forest.drop arity
      let tree := RawTerm.app field.tag children
      have childrenLen : children.length = arity := by
        simp only [children, List.length_take, hLen]
        omega
      have forestSplit : (children.flatMap RawTerm.tokens) ++ (siblings.flatMap RawTerm.tokens) =
          forest.flatMap RawTerm.tokens := by
        rw [← List.flatMap_append, List.take_append_drop]
      have hEncode (tail : Nat) :
          encodeTokens ((tree :: siblings).flatMap RawTerm.tokens) tail =
            Cantor.pair field.arityField
              (Cantor.pair field.tag (encodeTokens (forest.flatMap RawTerm.tokens) tail)) := by
        have bias : arity + 1 = field.arityField := by simp only [arity, field]; omega
        simp only [List.flatMap_cons, tree, RawTerm.tokens_app, List.cons_append, encodeTokens,
          childrenLen, bias, forestSplit]
      have rebuildDictionary : Cantor.pair field.arityField (Cantor.pair field.tag field.rest) = dictionary :=
        rawFields_rebuild dictionary
      have rebuildFront : Cantor.pair field.arityField (Cantor.pair field.tag input.rest) = front := by
        rw [sameArity, sameTag]
        exact rawFields_rebuild front
      refine ⟨tree :: siblings, ?_, ?_, ?_⟩
      · simp only [List.length_cons, siblings, List.length_drop, hLen]
        omega
      · change dictionary = encodeTokens ((tree :: siblings).flatMap RawTerm.tokens) rest.dictionaryRest
        rw [hEncode, ← hDictionary]
        exact rebuildDictionary.symm
      · change front = encodeTokens ((tree :: siblings).flatMap RawTerm.tokens) rest.frontRest
        rw [hEncode, ← hFront]
        exact rebuildFront.symm

theorem scanLoop_encoded (forest : List RawTerm) (dictionaryTail frontTail : Nat) :
    scanLoop forest.length (encodeTokens (forest.flatMap RawTerm.tokens) dictionaryTail)
      (encodeTokens (forest.flatMap RawTerm.tokens) frontTail) = ⟨true, dictionaryTail, frontTail⟩ := by
  induction measureEq : (forest.flatMap RawTerm.tokens).length using Nat.strongRecOn generalizing forest with
  | ind measure ih =>
    cases forest with
    | nil => exact scanLoop_zero dictionaryTail frontTail
    | cons t siblings =>
      cases t with
      | app tag children =>
        let expanded := children ++ siblings
        have size : (expanded.flatMap RawTerm.tokens).length < measure := by
          simp only [List.flatMap_cons, RawTerm.tokens_app, List.cons_append, List.length_cons,
            expanded, List.flatMap_append] at measureEq ⊢
          omega
        have rest := ih _ size expanded rfl
        have count : expanded.length = siblings.length + children.length := by
          simp [expanded, Nat.add_comm]
        simp only [List.length_cons, List.flatMap_cons, RawTerm.tokens_app, List.cons_append]
        simp only [← List.flatMap_append]
        change scanLoop (siblings.length + 1)
          (Cantor.pair (children.length + 1) (Cantor.pair tag
            (encodeTokens (expanded.flatMap RawTerm.tokens) dictionaryTail)))
          (Cantor.pair (children.length + 1) (Cantor.pair tag
            (encodeTokens (expanded.flatMap RawTerm.tokens) frontTail))) = _
        rw [scanLoop]
        simp only [rawFields_encode ⟨children.length, tag⟩, Nat.add_sub_cancel, ← count, rest]
        simp

theorem scanLoop_matches (dictionary front : Nat)
    (accepted : (scanLoop 1 dictionary front).valid = true) :
    ∃ t, readTree dictionary = some (t, (scanLoop 1 dictionary front).dictionaryRest) ∧
      matchTokens t.tokens front = some (scanLoop 1 dictionary front).frontRest := by
  obtain ⟨trees, len, coded, consumed⟩ := scanLoop_sound 1 dictionary front accepted
  obtain ⟨t, rfl⟩ := List.length_eq_one_iff.mp len
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at coded consumed
  refine ⟨t, ?_, ?_⟩
  · calc
      readTree dictionary = readTree (encodeTokens t.tokens (scanLoop 1 dictionary front).dictionaryRest) :=
        congrArg readTree coded
      _ = _ := readTree_complete _ _
  · calc
      matchTokens t.tokens front = matchTokens t.tokens (encodeTokens t.tokens (scanLoop 1 dictionary front).frontRest) :=
        congrArg (matchTokens t.tokens) consumed
      _ = _ := matchTokens_encoded _ _

end PalomarI3380.Compiler.Source
