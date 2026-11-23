module
public import I3_334Support.Search.RawTerms
@[expose] public section

namespace PalomarI3334
namespace Templates

open PalomarI3380

/-- Static axiom templates. A capture can instantiate a raw term of
any arity; the compiler's literal symbols have at most two arguments. -/
inductive Pattern where
  | capture (slot : Fin 4)
  | constant (tag : Nat)
  | unary (tag : Nat) (arg : Pattern)
  | binary (tag : Nat) (left right : Pattern)

inductive Instruction where
  | literal (token : Token)
  | capture (slot : Fin 4)
  | reverse
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def Pattern.instructions : Pattern → List Instruction
  | .capture slot => [.capture slot]
  | .constant tag => [.literal ⟨0, tag⟩]
  | .unary tag arg => .literal ⟨1, tag⟩ :: arg.instructions
  | .binary tag left right => .literal ⟨2, tag⟩ :: (left.instructions ++ right.instructions)

def Pattern.instantiate (values : Fin 4 → RawTerm) : Pattern → RawTerm
  | .capture slot => values slot
  | .constant tag => .app tag []
  | .unary tag arg => .app tag [arg.instantiate values]
  | .binary tag left right => .app tag [left.instantiate values, right.instantiate values]

/-- Slot d ranges over closed terms whose tags are all at least three,
including uninterpreted symbols. -/
def Guarded (t : RawTerm) : Prop := ∀ token ∈ t.tokens, 3 ≤ token.tag

def substituteInstruction (values : Fin 4 → RawTerm) : Instruction → List Token
  | .literal token => [token]
  | .capture slot => (values slot).tokens
  | .reverse => []

theorem Pattern.instantiate_instructions (values : Fin 4 → RawTerm) (pattern : Pattern) :
    (pattern.instantiate values).tokens =
      pattern.instructions.flatMap (substituteInstruction values) := by
  induction pattern <;> simp_all [Pattern.instantiate, Pattern.instructions, substituteInstruction]

abbrev Equation := Pattern × Pattern

def a : Pattern := .capture 0
def b : Pattern := .capture 1
def c : Pattern := .capture 2
def d : Pattern := .capture 3
def J : Pattern := .constant 0
def D : Pattern := .constant 1
def E : Pattern := .constant 2
def K : Pattern := .constant 3
def I : Pattern := .constant 5
def choice : Pattern → Pattern := .unary 1
def neg : Pattern → Pattern := .unary 3
def converse : Pattern → Pattern := .unary 4
def nand : Pattern → Pattern → Pattern := .binary 3
def product : Pattern → Pattern → Pattern := .binary 4

def inclusion : Pattern := neg (product (converse E) (neg E))
def stages : Pattern := product (converse (choice inclusion)) (choice inclusion)
def top : Pattern := nand (neg E) E

def converse_nand : Equation :=
  ((nand (converse a) (converse b)),
   (converse (nand a b)))

def right_identity : Equation :=
  ((product a I),
   a)

/-- Boolean meet written using the exact NAND and complement tags. -/
def meet (x y : Pattern) : Pattern := neg (nand x y)

def factorImage : Pattern :=
  (product
    (neg
      (nand
        (neg (product (neg (product (converse E) (neg (nand (choice a) a)))) E))
        (neg (product (converse E) (product (neg (nand (choice a) a)) (neg E))))))
    top)

def factorAdjunction : Pattern :=
  (nand (product (converse a) (neg (nand (neg (product a b)) c))) b)

def factorPreservation : Pattern :=
  (nand (product d J) (product J (neg d)))

def factorCoverage : Pattern :=
  (nand a (neg (product (neg (nand (choice a) a)) top)))

def factorFunction : Pattern :=
  (nand (product (converse (choice a)) (choice a)) (neg I))

def factorExtensionality : Pattern :=
  (nand (converse inclusion) (neg (nand inclusion (neg I))))

def guarded_bundle : Equation :=
  (meet factorImage (meet factorAdjunction
    (meet factorPreservation (meet factorCoverage (meet factorFunction factorExtensionality)))), top)

def stage_equation : Equation :=
  ((product inclusion (product stages (product E stages))),
   (product E stages))

def boolean_left : Equation :=
  (a,
   (neg (nand (neg (neg (nand (neg a) b))) a)))

def product_assoc : Equation :=
  ((product a (product b c)),
   (product (product a b) c))

def domain : Equation :=
  ((neg (nand I (product J top))),
   D)

def boolean_right : Equation :=
  ((neg (nand b (neg (nand c a)))),
   (neg (nand (neg (neg (nand (neg a) b))) (neg (nand c b)))))

def domain_closure : Equation :=
  ((neg (nand I (product K (product stages top)))),
   D)

def membership_seed : Equation :=
  (K,
   (product E D))

/-- The emitted template order, with the compiler's orientation and slot numbering. -/
def equations : List Equation :=
  [converse_nand, right_identity, guarded_bundle, stage_equation, boolean_left,
   product_assoc, domain, boolean_right, domain_closure, membership_seed]

def equationInstructions (eq : Equation) : List Instruction :=
  eq.1.instructions ++ .reverse :: eq.2.instructions

def isGuardedCapture : Instruction → Bool
  | .capture slot => slot.val == 3
  | _ => false

theorem template_shape :
    equations.length = 10 ∧
    (equations.map fun eq => eq.1.instructions.length + eq.2.instructions.length).sum = 258 ∧
    ((equations.flatMap equationInstructions).filter isGuardedCapture).length = 2 := by
  decide +kernel

end Templates
end PalomarI3334
