module
public import I3_380.WordCode
public import I3_380.Search.Compiler.Program
@[expose] public section

namespace PalomarI3380.Compiler.Source

open Term Manifest

def np : Register := 0
def pl : Register := 1
def sel : Register := 2
def goal : Register := 3
def fr : Register := 4
def gues : Register := 5
def lv : Register := 6
def dc : Register := 7
def u : Register := 8
def tmp : Register := 9
def tok : Register := 10
def exp : Register := 11

def inc (r : Register) : Program := .op (.inc r)
def dec (r : Register) : Program := .op (.decNZ r)
def break_ (n : Nat) : Program := .op (.break_ n)
def continue_ (extra : Nat) : Program := .op (.continue_ extra)
def halt : Program := .op .halt

/-- Sequences in the source builder associate to the right, with an empty
list used as an identity. -/
def block : List Program → Program
  | [] => break_ 0
  | [p] => p
  | p :: q :: ps => .seq p (block (q :: ps))

def whilePositive (r : Register) (body : Program) : Program :=
  .seq (dec r) (.seq body (continue_ 1))

def clear (r : Register) : Program := .seq (dec r) (continue_ 0)

def ifPositive (r : Register) (body : Program) : Program := .seq (dec r) body

def ifZero (r : Register) (body : Program) : Program :=
  .seq (.seq (dec r) (break_ 1)) body

def move (src dst : Register) : Program := whilePositive src (inc dst)

def copy (src dst : Register) : Program :=
  .seq (whilePositive src (.seq (inc dst) (inc u))) (move u src)

def unpair (first second src : Register) : Program :=
  whilePositive src (.seq (inc second) (ifZero first (move second first)))

/-- These scratch registers are clear at trie boundaries. -/
structure ClearScratch {V : Type} [OfNat V 0] (s : Store V) : Prop where
  expZero : s exp = 0
  tokZero : s tok = 0
  auxZero : s u = 0
  tempZero : s tmp = 0
  goalZero : s goal = 0

def read (dst : Register) : Program :=
  block [unpair tok u pl, move u pl, move tok dst]

def pop (src dst : Register) : Program :=
  .seq (unpair dst u src) (move u src)

def mismatch : Program := .seq (clear gues) (clear exp)
def compareHeads : Program := whilePositive exp (ifZero tok mismatch)
def compare : Program := .seq compareHeads (whilePositive tok (clear gues))

def eat : Program := .seq (pop fr tok) compare

def dropField : Program := block [unpair exp u tmp, clear exp, move u tmp]
def grabField : Program := block [unpair exp u tmp, clear u, move exp tmp]
def arity : Program := block [ifZero exp (clear gues), copy exp goal, inc exp]

def scanBody : Program := block [pop tmp exp, arity, eat, pop tmp exp, eat]

def scan (index : Fin 3) : Program :=
  block ([copy dc tmp] ++ List.replicate index.val dropField ++
    [grabField, inc goal,
      whilePositive goal scanBody, clear tmp])

def eatLiteral (token : Token) : Program :=
  block (List.replicate (token.arity + 1) (inc exp) ++
    [eat] ++ List.replicate token.tag (inc exp) ++ [eat])

def side : Program := block [move fr tmp, move lv fr, move tmp lv]

inductive Pattern where
  | variable (index : Fin 3)
  | literal (token : Token)
  | side
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def Pattern.compile : Pattern → Program
  | .variable i => scan i
  | .literal t => eatLiteral t
  | .side => Source.side

def pattern : Term (Fin 3) → List Pattern
  | .var v => [.variable v]
  | .const c => [.literal ⟨0, c.tag⟩]
  | .neg x => .literal ⟨1, 0⟩ :: pattern x
  | .choice x => .literal ⟨1, 1⟩ :: pattern x
  | .localRel x => .literal ⟨1, 2⟩ :: pattern x
  | .converse x => .literal ⟨1, 3⟩ :: pattern x
  | .nand x y => .literal ⟨2, 0⟩ :: pattern x ++ pattern y
  | .product x y => .literal ⟨2, 1⟩ :: pattern x ++ pattern y
  | .node x y z => .literal ⟨3, 0⟩ :: pattern x ++ pattern y ++ pattern z

/-- The five rows that are reassociated or commuted in the release.
The remaining rows come directly from the conservative manifest. -/
def preserved : Equation :=
  (nand (product (converse (const .J)) (product (localRel b) (const .J))) (neg (localRel b)), const .U)

def recurseStage : Equation :=
  let s : Term (Fin 3) := stage subset
  let earlier := product s (converse (const .E))
  (product earlier (product s (converse subset)), earlier)

def extensional : Equation := (meet (converse subset) subset, const .I)

def image : Equation :=
  let before := product (converse (const .E)) (choice a)
  let after := product (converse (const .E)) (product (choice a) (neg (const .E)))
  (product (meet (neg (product (neg before) (const .E))) (neg after)) (const .U), const .U)

def active : Equation :=
  (meet (const .I) (product (product (const .E) (meet (const .D) (stage subset))) (const .U)), const .D)

def swapEquation (r : Equation) : Equation := (r.2, r.1)

def swapVariables (r : Equation) : Equation :=
  let σ := fun i : Fin 3 => Term.var (if i = 0 then 1 else if i = 1 then 0 else i)
  (r.1.subst σ, r.2.subst σ)

/-- Each pair records the original equation and the form used at the
corresponding trie leaf. The left column is a permutation of the basis. -/
def rowLayout : List (Equation × Equation) :=
  let same := fun e : Equation => (e, e)
  let swap := fun e : Equation => (e, swapEquation e)
  [
    swap (reduce converseMeet),
    same (reduce rightIdentity),
    (final[18]'(by decide), preserved),
    (reduce converseInvolution, swapEquation (swapVariables (reduce converseInvolution))),
    swap (reduce choiceDomain),
    same (reduce peirce),
    (reduce stageLaw, recurseStage),
    swap meredith1,
    (reduce extensionality, extensional),
    same (reduce choiceSub),
    swap (final[17]'(by decide)),
    same (reduce productAssociative),
    same (reduce productMonotonicity),
    (reduce imageEquation, image),
    swap (reduce defineDomain),
    same (reduce choiceFunctional),
    swap meredith2,
    (reduce domainClosed, active),
    same (final[16]'(by decide))
  ]

/-- Literal order, orientation and coordinate choices of the trie. -/
def rows : List Equation := rowLayout.map Prod.snd

def rowPattern (r : Equation) : List Pattern := pattern r.1 ++ [.side] ++ pattern r.2

def dispatch : List Program → Program
  | [] => break_ 0
  | [p] => p
  | p :: q :: qs =>
    .seq (.seq (dec sel) (.seq (dispatch (q :: qs)) (break_ 1))) p

def branchKeys (rows : List (List Pattern)) : List (Option Pattern) :=
  (rows.map List.head?).eraseDups

def branchTail (key : Option Pattern) (rows : List (List Pattern)) : List (List Pattern) :=
  (rows.filter fun row => row.head? == key).map List.tail

def trieBranch (next : List (List Pattern) → List Program) (rows : List (List Pattern)) :
    Option Pattern → List Program
  | none => []
  | some sym => sym.compile :: next (branchTail (some sym) rows)

def chooseBranches (branch : Option Pattern → List Program) : List (Option Pattern) → List Program
  | [] => []
  | [key] => branch key
  | keys => [read sel, dispatch (keys.map fun k => block (branch k))]

/-- Stable prefix-trie construction. A selector is fetched only when
there is more than one next token. -/
def trie : Nat → List (List Pattern) → List Program
  | 0, _ => []
  | _ + 1, [] => []
  | _ + 1, [row] => row.map Pattern.compile
  | fuel + 1, a :: b :: rows =>
    chooseBranches (trieBranch (trie fuel) (a :: b :: rows)) (branchKeys (a :: b :: rows))

def compiledRows : List Program :=
  let patterns := rows.map rowPattern
  trie (patterns.foldl (fun n p => max n p.length) 0) patterns

def contextField : Program := .seq (pop lv exp) eat
def contextScan : Program := whilePositive sel (.seq contextField contextField)

def resetTask : Program :=
  block [copy np pl, inc np, clear goal, block (List.replicate 4 (inc goal))]

def mainInput : List Program :=
  [ifZero pl resetTask, read gues, copy gues lv, move goal fr, read sel, contextScan,
    read sel, ifPositive sel side, clear sel, read dc]

def mainOutput : List Program :=
  [clear sel, move fr exp, move lv tok, compare, clear dc]

def acceptGate : Program :=
  ifPositive gues (block [ifZero gues halt, inc goal, inc goal, move gues goal])

def main : Program :=
  block (mainInput ++ compiledRows ++ mainOutput ++ [acceptGate])

end PalomarI3380.Compiler.Source
