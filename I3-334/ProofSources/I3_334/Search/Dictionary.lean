module
public import I3_334Support.Search.Cantor
@[expose] public section

namespace PalomarI3334

open PalomarI3380

structure Dictionary where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving DecidableEq, Repr

namespace Dictionary

def encode (values : Dictionary) : Nat :=
  Cantor.pair (Cantor.pair (Cantor.pair values.d values.c) values.b) values.a

def decode (word : Nat) : Dictionary :=
  let (abc, a) := Cantor.unpair word
  let (dc, b) := Cantor.unpair abc
  let (d, c) := Cantor.unpair dc
  ⟨a, b, c, d⟩

theorem decode_encode (values : Dictionary) : decode values.encode = values := by
  rcases values with ⟨a, b, c, d⟩
  simp [decode, encode, Cantor.unpair_pair]

theorem encode_decode (word : Nat) : (decode word).encode = word := by
  unfold decode encode
  rcases h₁ : Cantor.unpair word with ⟨abc, a⟩
  rcases h₂ : Cantor.unpair abc with ⟨dc, b⟩
  rcases h₃ : Cantor.unpair dc with ⟨d, c⟩
  have un₁ : Cantor.pair abc a = word := by simpa [h₁] using Cantor.pair_unpair word
  have un₂ : Cantor.pair dc b = abc := by simpa [h₂] using Cantor.pair_unpair abc
  have un₃ : Cantor.pair d c = dc := by simpa [h₃] using Cantor.pair_unpair dc
  simp [h₂, h₃, un₁, un₂, un₃]

end Dictionary

/-- Read an unbiased raw arity. The guarded slot adds three to every raw
tag, including the default tag of an exhausted dictionary word. -/
def readRaw (offset word : Nat) : Token × Nat :=
  let (arity, suffix) := Cantor.unpair word
  let (tag, tail) := Cantor.unpair suffix
  (⟨arity, tag + offset⟩, tail)

def writeRaw (offset : Nat) : List Token → Nat → Nat
  | [], tail => tail
  | token :: rest, tail =>
    Cantor.pair token.arity (Cantor.pair (token.tag - offset) (writeRaw offset rest tail))

def readRawPrefix (offset : Nat) : Nat → Nat → List Token × Nat
  | 0, word => ([], word)
  | n + 1, word =>
    let (token, next) := readRaw offset word
    let (rest, tail) := readRawPrefix offset n next
    (token :: rest, tail)

theorem readRaw_writeRaw (offset : Nat) (tokens : List Token) (tail : Nat)
    (allowed : ∀ token ∈ tokens, offset ≤ token.tag) :
    readRawPrefix offset tokens.length (writeRaw offset tokens tail) = (tokens, tail) := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
    have tag : token.tag - offset + offset = token.tag :=
      Nat.sub_add_cancel (allowed token List.mem_cons_self)
    have remaining := ih (fun t ht => allowed t (List.mem_cons_of_mem token ht))
    cases token
    simp only [readRawPrefix, readRaw, writeRaw, List.length_cons, Cantor.unpair_pair,
      tag, remaining]

theorem readRaw_guard (word : Nat) : 3 ≤ (readRaw 3 word).1.tag := by
  unfold readRaw
  split
  split
  exact Nat.le_add_left 3 _

theorem raw_default (offset : Nat) : readRaw offset 0 = (⟨0, offset⟩, 0) := by
  have zero : Cantor.unpair 0 = (0, 0) := by
    simpa only [show Cantor.pair 0 0 = 0 from rfl] using Cantor.unpair_pair 0 0
  simp [readRaw, zero]

end PalomarI3334
