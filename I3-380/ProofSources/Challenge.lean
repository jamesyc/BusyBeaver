module
public import Std
@[expose] public section

/-! Standalone statements for the literal machine and its independence claim. -/

namespace PalomarI3380

/-- Each natural encodes one side of the tape, with the closest bit least
significant. The scanned cell is the least significant bit of `right`. -/
structure Configuration where
  state : Nat
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

def blank : Configuration := ⟨0, 0, 0⟩

/-- Rows are ordered by working state, then by read bit. Each 11-bit row
stores `4 * next + 2 * write + direction`, with right = 1. Packing permits
constant-index arithmetic lookup during kernel replay. -/
structure Machine where
  workingStates : Nat
  packedRows : Nat

def Machine.row (m : Machine) (state read : Nat) : Nat :=
  (m.packedRows >>> (11 * (2 * state + read))) % 2048

def step (m : Machine) (c : Configuration) : Option Configuration :=
  if m.workingStates ≤ c.state then none else
    let row := m.row c.state (c.right % 2)
    let written := row / 2 % 2
    let next := row / 4
    let tail := c.right / 2
    if row % 2 = 1 then
      some ⟨next, 2 * c.left + written, tail⟩
    else
      some ⟨next, c.left / 2, 4 * tail + 2 * written + c.left % 2⟩

def run (m : Machine) : Nat → Configuration → Option Configuration
  | 0, c => some c
  | n + 1, c => match step m c with
    | some next => run m n next
    | none => none

-- BEGIN LITERAL ROWS
/-- Exact rows of `data/zfc-i3-native-380.tm`. -/
def literal : Array Nat := #[
  7, 8, 9, 5, 14, 17, 16, 20, 2, 4, 24, 31,
  20, 20, 33, 39, 41, 47, 49, 55, 48, 58, 61, 67,
  69, 75, 77, 83, 85, 91, 93, 99, 101, 107, 109, 115,
  117, 123, 124, 131, 133, 139, 141, 144, 149, 152, 157, 163,
  117, 167, 169, 175, 177, 183, 169, 159, 185, 188, 169, 195,
  197, 188, 201, 75, 205, 188, 209, 79, 213, 219, 169, 223,
  224, 144, 169, 231, 232, 154, 169, 239, 241, 188, 101, 188,
  247, 248, 255, 175, 257, 152, 261, 263, 265, 271, 188, 152,
  169, 275, 169, 103, 221, 144, 169, 279, 149, 283, 257, 287,
  289, 295, 169, 299, 154, 224, 169, 259, 300, 154, 307, 310,
  197, 267, 245, 315, 316, 250, 253, 323, 169, 327, 329, 331,
  169, 335, 201, 339, 169, 151, 169, 331, 341, 188, 277, 188,
  49, 347, 349, 355, 169, 119, 356, 154, 305, 361, 364, 371,
  373, 315, 376, 250, 381, 323, 169, 111, 169, 387, 169, 391,
  392, 399, 389, 402, 221, 407, 325, 411, 289, 415, 416, 154,
  423, 363, 424, 366, 431, 369, 432, 315, 376, 224, 250, 323,
  169, 199, 169, 207, 437, 443, 445, 188, 241, 115, 385, 188,
  449, 188, 453, 459, 460, 154, 465, 361, 468, 366, 168, 467,
  474, 248, 273, 479, 117, 343, 169, 483, 485, 487, 488, 494,
  497, 503, 504, 154, 236, 467, 468, 144, 433, 474, 509, 188,
  169, 267, 393, 515, 517, 523, 525, 531, 325, 152, 49, 535,
  537, 154, 265, 543, 545, 551, 325, 555, 557, 563, 565, 571,
  573, 579, 581, 587, 537, 31, 85, 591, 593, 599, 601, 607,
  609, 144, 613, 571, 617, 623, 625, 631, 633, 639, 640, 646,
  625, 627, 124, 651, 653, 659, 117, 663, 229, 115, 392, 287,
  141, 667, 221, 671, 617, 675, 625, 679, 681, 627, 685, 615,
  689, 515, 689, 695, 229, 699, 597, 703, 705, 711, 713, 719,
  333, 188, 289, 723, 497, 727, 689, 188, 729, 188, 89, 188,
  733, 739, 689, 683, 689, 743, 745, 751, 169, 447, 689, 679,
  481, 402, 297, 394, 617, 755, 757, 763, 765, 771, 557, 615,
  773, 779, 781, 787, 201, 791, 793, 799, 801, 807, 689, 627,
  808, 562, 793, 815, 749, 819, 820, 826, 705, 735, 685, 831,
  625, 695, 325, 835, 837, 843, 229, 663, 337, 847, 89, 851,
  853, 583, 857, 815, 861, 571, 865, 863, 869, 495, 873, 879,
  837, 863, 881, 887, 889, 687, 741, 515, 893, 144, 829, 899,
  289, 903, 549, 907, 141, 152, 193, 911, 701, 915, 793, 919,
  617, 923, 741, 743, 701, 43, 925, 931, 733, 819, 933, 939,
  749, 571, 941, 947, 681, 515, 949, 955, 957, 963, 697, 188,
  849, 927, 857, 799, 617, 967, 540, 699, 969, 975, 889, 979,
  817, 735, 325, 983, 985, 991, 325, 995, 997, 1003, 193, 152,
  149, 1007, 749, 735, 329, 1011, 297, 152, 1013, 1019, 1021, 144,
  617, 291, 1025, 1031, 1033, 144, 741, 683, 289, 1039, 1041, 1047,
  257, 1051, 837, 831, 932, 1054, 1057, 1063, 325, 1067, 749, 1071,
  1073, 1079, 1081, 1087, 1089, 1523, 261, 1095, 1097, 188, 1101, 1107,
  325, 1111, 1113, 1119, 1121, 144, 289, 1127, 325, 1131, 685, 827,
  325, 1135, 1017, 1055, 149, 144, 149, 1139, 1141, 1147, 757, 999,
  837, 967, 1149, 144, 897, 1155, 289, 1159, 1161, 1167, 1169, 1175,
  1177, 144, 1181, 144, 329, 402, 701, 927, 57, 1187, 1189, 1195,
  617, 999, 1197, 1203, 325, 1207, 1209, 1215, 325, 1219, 525, 751,
  1221, 1227, 1229, 1235, 1237, 1243, 325, 1247, 1101, 1251, 325, 1255,
  1257, 1263, 1265, 144, 1269, 771, 1269, 1275, 489, 144, 325, 1279,
  985, 1283, 1285, 1291, 1293, 567, 141, 1299, 589, 1303, 1305, 144,
  997, 735, 1309, 144, 1312, 1114, 617, 1319, 1013, 1323, 617, 1259,
  1293, 1211, 1325, 144, 1329, 1335, 829, 1339, 829, 771, 1229, 571,
  1137, 188, 1341, 515, 1345, 759, 1349, 1355, 577, 1359, 1361, 1367,
  617, 1371, 1373, 1379, 325, 1383, 869, 1387, 1153, 771, 625, 1143,
  325, 1391, 325, 1395, 749, 1399, 1401, 455, 869, 735, 1405, 1411,
  1285, 1415, 325, 1419, 565, 1423, 1425, 144, 1429, 1435, 809, 144,
  1437, 144, 829, 1443, 1153, 1447, 1257, 831, 869, 575, 685, 1451,
  821, 144, 985, 1455, 965, 643, 1017, 1363, 897, 1459, 685, 1463,
  921, 575, 1465, 1467, 769, 1471, 1473, 1479, 1361, 1483, 765, 747,
  745, 1231, 1285, 1487, 325, 1491, 1257, 455, 869, 1495, 617, 647,
  1497, 144, 801, 1503, 573, 1507, 869, 1511, 837, 1315, 1513, 1519,
  677, 515, 965, 863
]

/-- The same rows packed for kernel evaluation. -/
def packedLiteral : Nat := 0x6bef1501aa5bdf7a691b45bced96f1a3dbbec84485d950e9a6ebb6538f3a6e9945b9f41667ae95d6bf6e5d51b8f706dfb01b776e51fb99b6eab6d9b81aa6fe541bc5b5ef6448335b56ab51fb6567f3a6d3c81b46cf44859d120ca6cdd95121646c7a35b16516c3d05b075f56fb6538f5e6bbaedae6516b79458ee9c581c81ad6d96b3945ac7576ada69aaf546a7a41a975157bd414074f45e47147733581b3da76cf69bd311214b65dd0d9d69a695bf5a4e9a62d5201214756fbe51214668ba4da262351bd0da1741681bd99fe514481e99f73d581cf51213c677ce99ce51671c4d9be5166dcd59a733665cc55de8366194597f2e65b9459672b5f3a699572965183973eaf4c91491212744849992f24647c8990e48641b811211f5e3b457cebd63dc758e62544809583efe637945676ab6359458ce484484618bf1662b9458a71345e44988e416f9c4187f0e61bc3185ebb61594584f0860f3a467ed160d90182f04607921556b944840980f00491a69120ff5fdbf51304a5f99495bebb5f7895130305f5be57c6515efbd97ae5156fb317a6de5e7bc9576871e3a6963ed65cfb51178ae5e1bbd776ed501aa9766eb51daed756e9599add746e7415abd5ceb95cda6972ec65c9abd71e3044c08d716895c3921706cf44837d406b9557b796eedc5afb456deda4f7b656bed851db5d65ed6523b556a6165a795152e395a5b456865155ba7167eab56fac1674cd199aed65ec65193284e6ac593b2163ec658b8c9626c3585b054ce8b581afd5f6bd579a693144a4c91e154eac4df8a95deba573ab1556ac571add1781645e2d9178ac56b9f15a64845e14d59eb2563ac157e9555d8e556eac501ab14ceab539aa954e9c551a6953e3754d88d23e620398e552e1d549a8d5161f139a7150ca013fa794ee9c537a69476994482614be9652ba5149e1540fa1949691521a3d4768d519a2d45651513a2143e4244d21942e0c44c14542683505a05406624858a91787f4ed1b1120750e98ec1347e0fb9f13dc7a0f39e53c62a4ab8753be4447c1da3a62a0b71d42d27444d1cc3967145e1c1178604398f11786f4dd9b519e2a4638a92863e8701782766c0b89af2dc6a0b59a7134680cf921336514cb8dd324614c798830e2a4c18a90de2a4a197d1f45e09d9752e65b0b49311345903b8a92c6574ad8311784545e1552962a44b8a92a6324a78a9296524a38a92863f47d13c2763d4858c526c4cc4d12c2062a47009a2562a49392123e4048d89522e2a4480dd0ce2a4898a91302f08790920e4144c10115e3fc7c0f71781945e0f11de2a44d0e81ce2a4480e01be2a46d8d509e3445e0cd0963245e0c51862a45e0b913e2a45b8b115e2a4538751462744c095120234458851061f03d8750e61b4358650c61742d8550a6134258450860f41d03006e0c41782904e0840a01403e060020020280400880e00a02404007
-- END LITERAL ROWS

def machine : Machine := ⟨380, packedLiteral⟩

/-- Full tape, relative to the head, at the end of the parity loader. -/
def loaderExit : Configuration :=
  ⟨7, 1, 0x15555555555555555555555555555555555aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000⟩

/-- Statement of the finite loader result, proved in Solution. -/
theorem loaderReplay :
    machine.workingStates = 380 ∧ literal.size = 760 ∧
    (literal.toList.zipIdx.all fun (row, i) => machine.row (i / 2) (i % 2) == row) = true ∧
    run machine 39753 blank = some loaderExit := by
  sorry

end PalomarI3380

-- BEGIN PRINCIPAL STATEMENT
namespace PalomarI3380

/-- A terminal configuration reached after finitely many literal steps. -/
def HaltsFrom (m : Machine) (c : Configuration) : Prop :=
  ∃ n terminal, run m n c = some terminal ∧ step m terminal = none

end PalomarI3380

/-! De Bruijn syntax, proof rules, and axiom schemas for ZF.
The I3 theory adds Choice and the rank-embedding sentence. -/
namespace PalomarI3380.Logic
inductive Formula where
 | bot : Formula
 | mem : Nat → Nat → Formula
 | eq : Nat → Nat → Formula
 | and : Formula → Formula → Formula
 | or : Formula → Formula → Formula
 | imp : Formula → Formula → Formula
 | all : Formula → Formula
 | ex : Formula → Formula
 deriving DecidableEq, Repr

def lift (σ : Nat → Nat) : Nat → Nat
 | 0 => 0
 | n+1 => σ n + 1

def rename (σ : Nat → Nat) : Formula → Formula
 | .bot => .bot
 | .mem i j => .mem (σ i) (σ j)
 | .eq i j => .eq (σ i) (σ j)
 | .and a b => .and (rename σ a) (rename σ b)
 | .or a b => .or (rename σ a) (rename σ b)
 | .imp a b => .imp (rename σ a) (rename σ b)
 | .all a => .all (rename (lift σ) a)
 | .ex a => .ex (rename (lift σ) a)


def shift (a:Formula) := rename Nat.succ a
def substMap (t:Nat) : Nat→Nat | 0=>t | n+1=>n
def subst (t:Nat) (a:Formula) := rename (substMap t) a

def Bound : Formula → Nat → Prop
  | .bot, _ => True
  | .mem i j, n => i < n ∧ j < n
  | .eq i j, n => i < n ∧ j < n
  | .and p q, n => Bound p n ∧ Bound q n
  | .or p q, n => Bound p n ∧ Bound q n
  | .imp p q, n => Bound p n ∧ Bound q n
  | .all p, n => Bound p (n+1)
  | .ex p, n => Bound p (n+1)


universe u
/-- Interpretation of a de Bruijn assignment after pushing an eigenvariable. -/
def pushValue {α : Type u} (s : Nat → α) (x : α) : Nat → α
  | 0 => x
  | n + 1 => s n

def eval {α : Type u} (mem : α → α → Prop) : Formula → (Nat → α) → Prop
  | .bot, _ => False
  | .mem i j, s => mem (s i) (s j)
  | .eq i j, s => s i = s j
  | .and p q, s => eval mem p s ∧ eval mem q s
  | .or p q, s => eval mem p s ∨ eval mem q s
  | .imp p q, s => eval mem p s → eval mem q s
  | .all p, s => ∀ x, eval mem p (pushValue s x)
  | .ex p, s => ∃ x, eval mem p (pushValue s x)


abbrev Context := List Formula

def ContextSub (Γ Δ : Context) : Prop := ∀ a, a ∈ Γ → a ∈ Δ
inductive Row where
 | seq : Context → Formula → Row
 | branches : Context → Formula → Formula → Formula → Row
 deriving DecidableEq, Repr


def shiftContext (Γ:Context):=Γ.map shift

inductive ND : Row → Prop where
 | ctx {Γ a} : a ∈ Γ → ND (.seq Γ a)
 | pc (Γ a b) : ND (.seq Γ (.imp (.imp (.imp a b) a) a))
 | ii {Γ a b} : ND (.seq (a :: Γ) b) → ND (.seq Γ (.imp a b))
 | ie {Γ a b} : ND (.seq Γ (.imp a b)) → ND (.seq Γ a) → ND (.seq Γ b)
 | exp {Γ a} : ND (.seq Γ .bot) → ND (.seq Γ a)
 | ci {Γ a b} : ND (.seq Γ a) → ND (.seq Γ b) → ND (.seq Γ (.and a b))
 | ce1 {Γ a b} : ND (.seq Γ (.and a b)) → ND (.seq Γ a)
 | ce2 {Γ a b} : ND (.seq Γ (.and a b)) → ND (.seq Γ b)
 | di1 {Γ a b} : ND (.seq Γ a) → ND (.seq Γ (.or a b))
 | di2 {Γ a b} : ND (.seq Γ b) → ND (.seq Γ (.or a b))
 | branchPair {Γ a b c} : ND (.seq (a :: Γ) c) → ND (.seq (b :: Γ) c) → ND (.branches Γ a b c)
 | de {Γ a b c} : ND (.seq Γ (.or a b)) → ND (.branches Γ a b c) → ND (.seq Γ c)
 | wk {Γ Δ a} : ContextSub Γ Δ → ND (.seq Γ a) → ND (.seq Δ a)
 | allI {Γ a} : ND (.seq (shiftContext Γ) a) → ND (.seq Γ (.all a))
 | allE {Γ a} (t : Nat) : ND (.seq Γ (.all a)) → ND (.seq Γ (subst t a))
 | exI {Γ a} (t : Nat) : ND (.seq Γ (subst t a)) → ND (.seq Γ (.ex a))
 | exE {Γ a c} : ND (.seq Γ (.ex a)) → ND (.seq (a :: shiftContext Γ) (shift c)) → ND (.seq Γ c)


def fixedRefl : Formula := (.all (.eq 0 0))

def fixedSym : Formula := (.all (.all (.imp (.eq 1 0) (.eq 0 1))))

def fixedTrans : Formula := (.all (.all (.all (.imp (.eq 2 1) (.imp (.eq 1 0) (.eq 2 0))))))

def fixedEqElem : Formula := (.all (.all (.all (.all (.imp (.eq 3 1) (.imp (.eq 2 0) (.imp (.mem 3 2) (.mem 1 0))))))))

def fixedExt : Formula := (.all (.all (.imp (.all (.imp (.mem 0 2) (.mem 0 1))) (.imp (.all (.imp (.mem 0 1) (.mem 0 2))) (.eq 1 0)))))

def fixedEmpty : Formula := (.ex (.all (.imp (.mem 0 1) (.bot))))

def fixedPair : Formula := (.all (.all (.ex (.all (.and (.imp (.mem 0 1) (.or (.eq 0 3) (.eq 0 2))) (.imp (.or (.eq 0 3) (.eq 0 2)) (.mem 0 1)))))))

def fixedUnion : Formula := (.all (.ex (.all (.and (.imp (.mem 0 1) (.ex (.and (.mem 0 3) (.mem 1 0)))) (.imp (.ex (.and (.mem 0 3) (.mem 1 0))) (.mem 0 1))))))

def fixedPower : Formula := (.all (.ex (.all (.and (.imp (.mem 0 1) (.all (.imp (.mem 0 1) (.mem 0 3)))) (.imp (.all (.imp (.mem 0 1) (.mem 0 3))) (.mem 0 1))))))

def fixedOmega : Formula := (.ex (.and (.and (.ex (.and (.all (.imp (.mem 0 1) (.bot))) (.mem 0 1))) (.all (.imp (.mem 0 1) (.ex (.and (.all (.and (.imp (.mem 0 1) (.or (.mem 0 2) (.eq 0 2))) (.imp (.or (.mem 0 2) (.eq 0 2)) (.mem 0 1)))) (.mem 0 2)))))) (.all (.imp (.and (.ex (.and (.all (.imp (.mem 0 1) (.bot))) (.mem 0 1))) (.all (.imp (.mem 0 1) (.ex (.and (.all (.and (.imp (.mem 0 1) (.or (.mem 0 2) (.eq 0 2))) (.imp (.or (.mem 0 2) (.eq 0 2)) (.mem 0 1)))) (.mem 0 2)))))) (.all (.imp (.mem 0 2) (.mem 0 1)))))))

def fixedFoundation : Formula := (.all (.imp (.ex (.mem 0 1)) (.ex (.and (.mem 0 1) (.all (.imp (.mem 0 1) (.imp (.mem 0 2) (.bot))))))))


def sourceIff (a b : Formula) := Formula.and (.imp a b) (.imp b a)
def separationFormula (body : Formula) := Formula.all (.ex (.all
 (sourceIff (.mem 0 1) (.and (.mem 0 2) body))))
def functionalityFormula (a b : Formula) := Formula.all (.all (.all
 (.imp a (.imp b (.eq 1 0)))))
def replacementFormula (a b c : Formula) := Formula.imp (functionalityFormula a b)
 (.all (.ex (.all (sourceIff (.mem 0 1) (.ex (.and (.mem 0 3) c))))))
def allPrefix : Nat → Formula → Formula
 | 0, a => a
 | n+1, a => .all (allPrefix n a)

def sepIndex (i : Nat) := if i=0 then 0 else i+2
def repAIndex (i : Nat) := if i=0 then 2 else if i=1 then 1 else i+1
def repBIndex (i : Nat) := if i=0 then 2 else if i=1 then 0 else i+1
def repCIndex (i : Nat) := if i=0 then 0 else if i=1 then 1 else i+2

def separationSchema (n : Nat) (phi : Formula) := allPrefix n (separationFormula (rename sepIndex phi))
def replacementSchema (n : Nat) (phi : Formula) := allPrefix n
 (replacementFormula (rename repAIndex phi) (rename repBIndex phi) (rename repCIndex phi))


/-- All fixed axioms, including logical equality, omega, and foundation. -/
def FixedAxiom (p:Formula):Prop:=
 p=fixedRefl ∨ p=fixedSym ∨ p=fixedTrans ∨ p=fixedEqElem ∨ p=fixedExt ∨
 p=fixedEmpty ∨ p=fixedPair ∨ p=fixedUnion ∨ p=fixedPower ∨ p=fixedOmega ∨ p=fixedFoundation
/-- Full standard schemas, with arbitrary finite parameter lists. -/
def Axiom (p:Formula):Prop:= FixedAxiom p ∨
 (∃ n body,Bound body (n+1) ∧ p=separationSchema n body) ∨
 (∃ n body,Bound body (n+2) ∧ p=replacementSchema n body)
def Provable (p:Formula):Prop:=∃Γ:Context,(∀q,q∈Γ→Axiom q) ∧ ND (.seq Γ p)
def Consistent:Prop:=¬Provable .bot
def Closed (p:Formula):Prop:=Bound p 0
def Neg (p:Formula):Formula:=.imp p .bot
/-- Nonemptiness is separately required at every quantified model use. -/
def Model {V:Type} (E:V→V→Prop):Prop:=∀p,Axiom p→∀s:Nat→V,eval E p s
end PalomarI3380.Logic

namespace PalomarI3380.Logic.Internal

/-! A run is a function graph indexed by the model's finite ordinals. -/

section InternalSets
variable {V : Type} (E : V → V → Prop)
def Empty (a : V) : Prop := ∀ x, ¬ E x a
def Succ (a b : V) : Prop := ∀ x, E x b ↔ E x a ∨ x = a
def Pair (a b p : V) : Prop := ∀ x, E x p ↔ x = a ∨ x = b
def OrderedPair (a b p : V) : Prop :=
 ∃ aa ab, Pair E a a aa ∧ Pair E a b ab ∧ Pair E aa ab p
def At (f x y : V) : Prop := ∃ p, E p f ∧ OrderedPair E x y p
/-- The function and its domain are elements of the model, not external maps. -/
def FunctionOn (f domain : V) : Prop :=
 (∀ x, E x domain → ∃ y, At E f x y ∧ ∀ z, At E f x z → z = y) ∧
 (∀ p, E p f → ∃ x y, E x domain ∧ OrderedPair E x y p)
def Inductive (a : V) : Prop :=
 (∃ z, Empty E z ∧ E z a) ∧ ∀ x, E x a → ∃ y, Succ E x y ∧ E y a
def Omega (w : V) : Prop :=
 Inductive E w ∧ ∀ a, Inductive E a → ∀ x, E x w → E x a
/-- Meaningful on actual ZF models, where a unique omega exists. -/
def NatObject (x : V) : Prop := ∃ w, Omega E w ∧ E x w
def Numeral : Nat → V → Prop
 | 0, x => Empty E x
 | n + 1, x => ∃ y, Numeral n y ∧ Succ E y x
/-- Internal finite recursion, including nonstandard finite lengths. -/
def Add (a b c : V) : Prop :=
 NatObject E a ∧ NatObject E b ∧ NatObject E c ∧
 ∃ z domain f, Empty E z ∧ Succ E b domain ∧ FunctionOn E f domain ∧
 At E f z a ∧ At E f b c ∧
 (∀ i x, E i domain → At E f i x → NatObject E x) ∧
 ∀ i, E i b → ∃ j x y, Succ E i j ∧ At E f i x ∧ At E f j y ∧ Succ E x y
def Mul (a b c : V) : Prop :=
 NatObject E a ∧ NatObject E b ∧ NatObject E c ∧
 ∃ z domain f, Empty E z ∧ Succ E b domain ∧ FunctionOn E f domain ∧
 At E f z z ∧ At E f b c ∧
 (∀ i x, E i domain → At E f i x → NatObject E x) ∧
 ∀ i, E i b → ∃ j x y, Succ E i j ∧ At E f i x ∧ At E f j y ∧ Add E x a y
/-- y = bit + 2*x, using arithmetic internal to the set model. -/
def BitCons (bit : Bool) (x y : V) : Prop :=
 ∃ b two twice, Numeral E (if bit then 1 else 0) b ∧ Numeral E 2 two ∧
 Mul E two x twice ∧ Add E b twice y
structure Configuration (V : Type) where
  state : V
  left : V
  right : V

/-- Triple `(state, (left, right))` of internal natural numbers. -/
def ConfigurationCode (c : Configuration V) (code : V) : Prop :=
  NatObject E c.state ∧ NatObject E c.left ∧ NatObject E c.right ∧
    ∃ tapes, OrderedPair E c.left c.right tapes ∧ OrderedPair E c.state tapes code

def Move (read write right : Bool) (next : Nat) (s t : Configuration V) : Prop :=
  ∃ tail, BitCons E read tail s.right ∧ Numeral E next t.state ∧
    if right then BitCons E write s.left t.left ∧ t.right = tail
    else ∃ left head middle, BitCons E head left s.left ∧ t.left = left ∧
      BitCons E write tail middle ∧ BitCons E head middle t.right

def LiteralStep (s t : Configuration V) : Prop :=
  ∃ q : Fin 380, Numeral E q.val s.state ∧ ∃ read : Bool,
    let row := literal[2 * q.val + (if read then 1 else 0)]?.getD 0
    Move E read (row / 2 % 2 == 1) (row % 2 == 1) (row / 4) s t

/-- A model-internal finite history of the exact table from blank to halt.
The length, all indices, and every tape value belong to the model's `ω`. -/
def Halts : Prop :=
  ∃ n domain history zero start finish,
    NatObject E n ∧ Succ E n domain ∧ FunctionOn E history domain ∧ Empty E zero ∧
      ConfigurationCode E ⟨zero, zero, zero⟩ start ∧ At E history zero start ∧
      At E history n finish ∧
      (∃ final, ConfigurationCode E final finish ∧ Numeral E 380 final.state) ∧
      ∀ i, E i n → ∃ next s t before after, Succ E i next ∧
        At E history i before ∧ At E history next after ∧
        ConfigurationCode E s before ∧ ConfigurationCode E t after ∧ LiteralStep E s t

end InternalSets
end PalomarI3380.Logic.Internal

namespace PalomarI3380.Logic

/-- Build de Bruijn formulas using levels that are fixed at their binders.
The builder's argument is the number of binders currently in scope. -/
abbrev SetFormula := Nat → Formula

namespace SetFormula

def falsity : SetFormula := fun _ => .bot
def eq (x y : Nat) : SetFormula := fun d => .eq (d - (x + 1)) (d - (y + 1))
def mem (x y : Nat) : SetFormula := fun d => .mem (d - (x + 1)) (d - (y + 1))
def both (p q : SetFormula) : SetFormula := fun d => .and (p d) (q d)
def either (p q : SetFormula) : SetFormula := fun d => .or (p d) (q d)
def implies (p q : SetFormula) : SetFormula := fun d => .imp (p d) (q d)
def neg (p : SetFormula) : SetFormula := implies p falsity
def iff (p q : SetFormula) : SetFormula := both (implies p q) (implies q p)

def every (body : Nat → SetFormula) : SetFormula := fun d => .all (body d (d + 1))
def someSet (body : Nat → SetFormula) : SetFormula := fun d => .ex (body d (d + 1))
def eachIn (domain : Nat) (body : Nat → SetFormula) : SetFormula :=
  every fun x => implies (mem x domain) (body x)
def someIn (domain : Nat) (body : Nat → SetFormula) : SetFormula :=
  someSet fun x => both (mem x domain) (body x)

def allOf : List SetFormula → SetFormula
  | [] => neg falsity
  | p :: ps => both p (allOf ps)

def anyOf : List SetFormula → SetFormula
  | [] => falsity
  | p :: ps => either p (anyOf ps)

def empty (a : Nat) : SetFormula :=
  every fun x => neg (mem x a)

def subset (a b : Nat) : SetFormula :=
  eachIn a fun x => mem x b

def successor (a b : Nat) : SetFormula :=
  every fun x => iff (mem x b) (either (mem x a) (eq x a))

def numeral : Nat → Nat → SetFormula
  | 0, a => empty a
  | n + 1, a => someSet fun b => both (numeral n b) (successor b a)

def unorderedPair (a b p : Nat) : SetFormula :=
  every fun x => iff (mem x p) (either (eq x a) (eq x b))

def orderedPair (a b p : Nat) : SetFormula :=
  someSet fun singleton => someSet fun double =>
    allOf [unorderedPair a a singleton, unorderedPair a b double, unorderedPair singleton double p]

def graphValue (graph x y : Nat) : SetFormula :=
  someIn graph fun p => orderedPair x y p

def functionOn (graph domain : Nat) : SetFormula :=
  both
    (eachIn graph fun p => someIn domain fun x => someSet fun y => orderedPair x y p)
    (eachIn domain fun x => someSet fun y =>
      both (graphValue graph x y) (every fun z => implies (graphValue graph x z) (eq z y)))

def functionInto (graph domain codomain : Nat) : SetFormula :=
  both (functionOn graph domain)
    (eachIn domain fun x => every fun y => implies (graphValue graph x y) (mem y codomain))

def inductiveSet (a : Nat) : SetFormula :=
  both (someIn a empty) (eachIn a fun x => someIn a (successor x))

def omegaSet (w : Nat) : SetFormula :=
  both (inductiveSet w) (every fun a => implies (inductiveSet a) (subset w a))

def transitive (a : Nat) : SetFormula :=
  eachIn a fun x => subset x a

def ordinal (a : Nat) : SetFormula :=
  both (transitive a) (eachIn a transitive)

/-- The cumulative hierarchy equation, starting graphValue the empty set.
At stage `b`, a set is present exactly when it is a subset of an earlier stage. -/
def hierarchy (graph domain : Nat) : SetFormula :=
  both (functionOn graph domain)
    (eachIn domain fun b => every fun stage => implies (graphValue graph b stage)
      (every fun x => iff (mem x stage)
        (someIn b fun a => someSet fun earlier => both (graphValue graph a earlier) (subset x earlier))))

def rank (height stage : Nat) : SetFormula :=
  both (ordinal height)
    (someSet fun domain => someSet fun graph =>
      allOf [successor height domain, hierarchy graph domain, graphValue graph height stage])

end SetFormula

open SetFormula in
/-- Every set of nonempty sets has a choice function. -/
def choiceAxiom : Formula :=
  (every fun family =>
    implies (eachIn family fun x => someIn x fun y => eq y y)
      (someSet fun f =>
        both (functionOn f family)
          (eachIn family fun x => every fun y => implies (graphValue f x y) (mem y x)))) 0

end PalomarI3380.Logic

namespace PalomarI3380.Logic

open SetFormula

/-- A postorder syntax row is a tagged pair of operands. The five tags
denote equality, membership, negation, conjunction and existential binding. -/
def syntaxRow (rows i : Nat) (body : Nat → Nat → Nat → SetFormula) : SetFormula :=
  someSet fun row => someSet fun tag => someSet fun operands =>
    someSet fun first => someSet fun second =>
      allOf [graphValue rows i row, orderedPair tag operands row,
        orderedPair first second operands, body tag first second]

def validRow (arity i tag first second : Nat) : SetFormula :=
  anyOf [
    allOf [numeral 0 tag, mem first arity, mem second arity],
    allOf [numeral 1 tag, mem first arity, mem second arity],
    both (numeral 2 tag) (mem first i),
    allOf [numeral 3 tag, mem first i, mem second i],
    allOf [numeral 4 tag, mem first arity, mem second i]
  ]

def syntaxCode (w arity count rows : Nat) : SetFormula :=
  allOf [mem arity w, mem count w, neg (empty count), functionOn rows count,
    eachIn count fun i => syntaxRow rows i fun tag first second =>
      allOf [mem first w, mem second w, validRow arity i tag first second]]

def agreesAway (arity old new index : Nat) : SetFormula :=
  eachIn arity fun i => implies (neg (eq i index))
    (every fun x => iff (graphValue old i x) (graphValue new i x))

def atomicTruth (relation : Nat → Nat → SetFormula) (env first second : Nat) : SetFormula :=
  someSet fun x => someSet fun y =>
    allOf [graphValue env first x, graphValue env second y, relation x y]

def rowTruth (arity stage sat env tag first second : Nat) : SetFormula :=
  anyOf [
    both (numeral 0 tag) (atomicTruth eq env first second),
    both (numeral 1 tag) (atomicTruth mem env first second),
    both (numeral 2 tag) (neg (graphValue sat first env)),
    allOf [numeral 3 tag, graphValue sat first env, graphValue sat second env],
    both (numeral 4 tag)
      (someSet fun amended =>
        allOf [functionInto amended arity stage, agreesAway arity env amended first,
          graphValue sat second amended])
  ]

/-- A truth set contains the pairs (syntax node, assignment) at which
the finite formula is true. The recursion ranges over the model's own
natural numbers and function graphs. -/
def truthSet (arity count rows stage sat : Nat) : SetFormula :=
  eachIn count fun i => every fun env => implies (functionInto env arity stage)
    (syntaxRow rows i fun tag first second =>
      iff (graphValue sat i env) (rowTruth arity stage sat env tag first second))

def mappedAssignment (arity embedding source target : Nat) : SetFormula :=
  eachIn arity fun i => every fun x => every fun y =>
    implies (both (graphValue source i x) (graphValue embedding x y)) (graphValue target i y)

def elementaryOnRank (w stage embedding : Nat) : SetFormula :=
  every fun arity => every fun count => every fun rows =>
    implies (syntaxCode w arity count rows)
      (someSet fun sat =>
        both (truthSet arity count rows stage sat)
          (eachIn count fun i => every fun source => every fun target =>
            implies (allOf [functionInto source arity stage, functionInto target arity stage,
                mappedAssignment arity embedding source target])
              (iff (graphValue sat i source) (graphValue sat i target))))

/-- There is a nonidentity elementary self-embedding at a nonzero
limit rank. Elementarity uses one uniform truth-set formula, including all internally
coded formulas in models with nonstandard natural numbers. -/
def i3Axiom : Formula :=
  (someSet fun w => someSet fun height => someSet fun stage => someSet fun embedding =>
    allOf [
      omegaSet w,
      rank height stage,
      inductiveSet height,
      functionInto embedding stage stage,
      someIn stage fun x => someIn stage fun y => both (graphValue embedding x y) (neg (eq x y)),
      elementaryOnRank w stage embedding
    ]) 0

def ZFCI3Axiom (p : Formula) : Prop := Axiom p ∨ p = choiceAxiom ∨ p = i3Axiom

def ZFCI3Provable (p : Formula) : Prop :=
  ∃ Γ : Context, (∀ q, q ∈ Γ → ZFCI3Axiom q) ∧ ND (.seq Γ p)

def ZFCI3Consistent : Prop := ¬ ZFCI3Provable .bot

def ZFCI3Model {V : Type} (E : V → V → Prop) : Prop :=
  ∀ p, ZFCI3Axiom p → ∀ s : Nat → V, eval E p s

end PalomarI3380.Logic

namespace PalomarI3380.Logic

inductive ArithTerm where
 | zero | one
 | var (index:Nat)
 | add (left right:ArithTerm)
 | mul (left right:ArithTerm)
inductive SigmaFormula where
 | atom (left right:ArithTerm) (equality positive:Bool)
 | conj (left right:SigmaFormula)
 | disj (left right:SigmaFormula)
 | exists_ (body:SigmaFormula)
 | forallLt (bound:ArithTerm) (body:SigmaFormula)
def ArithTerm.bound : ArithTerm→Nat→Prop
 | .zero,_ | .one,_=>True
 | .var i,n=>i<n
 | .add p q,n | .mul p q,n=>p.bound n ∧ q.bound n
def SigmaFormula.bound : SigmaFormula→Nat→Prop
 | .atom p q _ _,n=>p.bound n ∧ q.bound n
 | .conj p q,n | .disj p q,n=>p.bound n ∧ q.bound n
 | .exists_ p,n=>p.bound (n+1)
 | .forallLt t p,n=>t.bound n ∧ p.bound (n+1)
def ArithTerm.value {V : Type} [Zero V] [One V] [Add V] [Mul V] :
    ArithTerm → (Nat → V) → V
 | .zero,_=>0 | .one,_=>1 | .var i,s=>s i
 | .add p q,s=>p.value s+q.value s
 | .mul p q,s=>p.value s*q.value s

def SigmaFormula.value {V : Type} [Zero V] [One V] [Add V] [Mul V] [LT V] :
    SigmaFormula → (Nat → V) → Prop
 | .atom p q eq pos,s=>
   let P:=if eq then p.value s=q.value s else p.value s<q.value s
   if pos then P else ¬P
 | .conj p q,s=>p.value s ∧ q.value s
 | .disj p q,s=>p.value s ∨ q.value s
 | .exists_ p,s=>∃x,p.value (pushValue s x)
 | .forallLt b p,s=>∀x,x<b.value s→p.value (pushValue s x)

abbrev ArithTerm.natValue (t : ArithTerm) (s : Nat → Nat) : Nat := t.value s
abbrev SigmaFormula.natEval (φ : SigmaFormula) (s : Nat → Nat) : Prop := φ.value s

open Internal
/-- Fully relational evaluation, including arithmetic internal to a set model. -/
def ArithTerm.graph {V:Type} (E:V→V→Prop):ArithTerm→(Nat→V)→V→Prop
 | .zero,_,z=>Numeral E 0 z
 | .one,_,z=>Numeral E 1 z
 | .var i,s,z=>NatObject E z ∧ z=s i
 | .add p q,s,z=>∃a b,p.graph E s a ∧ q.graph E s b ∧ Add E a b z
 | .mul p q,s,z=>∃a b,p.graph E s a ∧ q.graph E s b ∧ Mul E a b z
def SigmaFormula.internalEval {V:Type} (E:V→V→Prop):SigmaFormula→(Nat→V)→Prop
 | .atom p q eq pos,s=>∃a b,p.graph E s a ∧ q.graph E s b ∧
   (if pos then (if eq then a=b else E a b) else ¬(if eq then a=b else E a b))
 | .conj p q,s=>p.internalEval E s ∧ q.internalEval E s
 | .disj p q,s=>p.internalEval E s ∨ q.internalEval E s
 | .exists_ p,s=>∃x:V,NatObject E x ∧ p.internalEval E (pushValue s x)
 | .forallLt b p,s=>∃bound,b.graph E s bound ∧
   ∀x:V,NatObject E x→E x bound→p.internalEval E (pushValue s x)
/-- Correct arithmetic meaning in every ZFC + I3 model, not just well-founded or
omega-standard models. Both syntax objects are fixed finite external syntax. -/
def RepresentsArithmetic (φ:SigmaFormula) (ψ:Formula):Prop:=
 Closed ψ ∧ ∀(V:Type) (E:V→V→Prop),Nonempty V→ZFCI3Model E→
 ∀(s env:Nat→V),(∀i,NatObject E (env i))→(eval E ψ s ↔ φ.internalEval E env)
/-- Arithmetic Σ₁-soundness of ZFC + I3 under the standard interpretation in its natural numbers. -/
def ArithmeticSigma1Sound:Prop:=
 ∀φ:SigmaFormula,φ.bound 0→∀ψ:Formula,RepresentsArithmetic φ ψ→
 ZFCI3Provable ψ→∀s:Nat→Nat,φ.natEval s

def RepresentsHalting (H : Formula) : Prop :=
  Closed H ∧ ∀ (V : Type) (E : V → V → Prop), Nonempty V → ZFCI3Model E →
    ∀ env : Nat → V, eval E H env ↔ Internal.Halts E

/-- The principal proposition. Its consistency and arithmetic soundness
premises refer to the ordinary ZFC + I3 proof system. -/
def ExactClaim : Prop :=
  ∃ H : Formula, RepresentsHalting H ∧
    (ZFCI3Consistent → ¬ HaltsFrom machine blank ∧ ¬ ZFCI3Provable (Neg H)) ∧
    (ArithmeticSigma1Sound → ¬ ZFCI3Provable H ∧ ¬ ZFCI3Provable (Neg H))

end PalomarI3380.Logic

namespace PalomarI3380

theorem exactClaim : Logic.ExactClaim := by
  sorry

end PalomarI3380
-- END PRINCIPAL STATEMENT
