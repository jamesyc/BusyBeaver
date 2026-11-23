module
public import I3_334.Search.Templates
public import I3_334Support.Search.Compiler.Source
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (inc dec break_ continue_ halt block ifPositive ifZero
  whilePositive clear move unpair)
open Templates (Instruction equations equationInstructions)

abbrev np : Register := 0
abbrev pl : Register := 1
abbrev goal : Register := 2
abbrev fr : Register := 3
abbrev gues : Register := 4
abbrev lv : Register := 5
abbrev dc : Register := 6
abbrev u : Register := 7
abbrev tmp : Register := 8
abbrev tok : Register := 9
abbrev expected : Register := 10

/-- Copy through the only auxiliary register. The copy finishes with
that register cleared, ready for the next unpair or exchange. -/
def copy (source target : Register) : Program :=
  .seq (whilePositive source (.seq (inc target) (inc u))) (move u source)

def pop (source target : Register) : Program :=
  .seq (unpair target u source) (move u source)

def read (target : Register) : Program := .seq (pop pl tok) (move tok target)

def compare : Program :=
  .seq (whilePositive tok (ifZero expected (clear gues)))
    (ifPositive expected (.seq (clear expected) (clear gues)))

def eat : Program := .seq (pop fr tok) compare

def exchange : Program := block [move fr u, move lv fr, move u lv]

def dictionaryPart (takeLeft : Bool) : Program :=
  let selected := if takeLeft then expected else u
  let discarded := if takeLeft then u else expected
  block [unpair expected u tmp, move selected tmp, clear discarded]

def dictionarySlot (slot : Fin 4) : List Program :=
  List.replicate slot.val (dictionaryPart true) ++
    if slot.val < 3 then [dictionaryPart false] else []

def scanBody (slot : Fin 4) : Program :=
  block ([pop tmp expected, copy expected goal, inc expected, eat, pop tmp expected] ++
    List.replicate (if slot.val = 3 then 3 else 0) (inc expected) ++ [eat])

def scan (slot : Fin 4) : Program :=
  block ([clear goal, clear tmp, copy dc tmp] ++ dictionarySlot slot ++
    [inc goal, whilePositive goal (scanBody slot)])

def literalToken (token : Token) : Program :=
  block (List.replicate (token.arity+1) (inc expected) ++ [eat] ++
    List.replicate token.tag (inc expected) ++ [eat])

def instruction : Instruction → Program
  | .literal token => literalToken token
  | .capture slot => scan slot
  | .reverse => exchange

def dispatchBy (counter : Register) : List Program → Program
  | [] => break_ 0
  | [p] => p
  | p :: q :: rest =>
    .seq (.seq (dec counter) (.seq (dispatchBy counter (q :: rest)) (break_ 1))) p

abbrev dispatch := dispatchBy goal

def branchKeys (rows : List (List Instruction)) : List (Option Instruction) :=
  (rows.map List.head?).eraseDups

def branchRows (key : Option Instruction) (rows : List (List Instruction)) : List (List Instruction) :=
  (rows.filter fun row => row.head? == key).map List.tail

/-- The right-identity and associativity split is the only branch that
uses slot a's unused dictionary suffix as its selector. -/
def suffixFork (keys : List (Option Instruction)) : Bool :=
  keys == [some (.literal ⟨0, 5⟩), some (.literal ⟨2, 4⟩)]

def choose (keys : List (Option Instruction)) (branches : Option Instruction → List Program) :
    List Program :=
  match keys with
  | [] => []
  | [key] => branches key
  | first :: second :: rest =>
    if suffixFork keys then
      [dispatchBy tmp [block (branches first), block (branches second)]]
    else [read goal, dispatch ((first :: second :: rest).map fun key => block (branches key))]

def trie : Nat → List (List Instruction) → List Program
  | 0, _ => []
  | _ + 1, [] => []
  | _ + 1, [row] => row.map instruction
  | fuel + 1, first :: second :: rest =>
    let rows := first :: second :: rest
    choose (branchKeys rows) fun key => match key with
      | none => []
      | some t => instruction t :: trie fuel (branchRows key rows)

def rows : List Program :=
  let words := equations.map equationInstructions
  trie (words.foldl (fun n word => max n word.length) 0) words

def restart : Program := block ([copy np pl, inc np, clear fr] ++ List.replicate 4 (inc fr))

def produce : Program :=
  block [pop pl tok, whilePositive tok (.seq (inc gues) (inc lv))]

def contextField : Program := .seq (pop lv expected) eat

/-- Zero ends the context section without swapping. A positive code
spends pairs of units on context tokens, and the final odd unit exchanges
the two sides. -/
def contextScan : Program :=
  .seq (dec goal) (.seq
    (.seq (dec goal) (.seq (.seq contextField contextField) (continue_ 2)))
    exchange)

def output : List Program :=
  [clear goal, move fr expected, move lv tok, compare, clear dc]

def accept : Program :=
  ifPositive gues (block [ifZero gues halt, inc fr, inc fr, move gues fr])

def main : Program :=
  block ([ifZero pl restart, produce, read goal, contextScan, read dc] ++ rows ++ output ++ [accept])

end PalomarI3334.SearchProgram
