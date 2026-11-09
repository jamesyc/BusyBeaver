module

public import PA215PA.NativeVacuity

@[expose] public section

/-! Finite native proofs for the literal AX variants establish the forward invariant. The bundle retains the numeric syntax tree, including its double negations. -/
namespace PA215.PA.NativeCalculus.ActualAX

def head3 (a b c : Nat) := wim (weq a b) (wim (wel c a) (wel c b))
def head5 (a b c : Nat) := wim (weq c a) (wim (wel c b) (wel a b))
def head7 (a b c : Nat) :=
  wim (weq c a) (wim (weq c b) (wal (wel a b) (weq a b)))

def separationBody (a b c : Nat) :=
  wal b (wa (wim (wel a b) (wim c (wel c b))) (wim (wel c b) c))
def point (b c : Nat) := wim c (wel c b)
def memVacuity (a b c : Nat) := wim (wel a b) (wal c (wel a b))
def rawBundle (a b c : Nat) :=
  wn (wim (memVacuity a b c) (wal c (wim (separationBody a b c) (wn (point b c)))))

def head3_proof (a b c : Nat) : Derivation (head3 a b c) := by
  let he : Context [wel c a,weq a b] (weq a b) := .assumption (by simp)
  let hm : Context [wel c a,weq a b] (wel c a) := .assumption (by simp)
  exact (Context.mp he (.mp hm (.closed (.r3 c a b)))).deduction.deduction.empty

def head5_proof (a b c : Nat) : Derivation (head5 a b c) := .r5 c a b

def head7_proof (a b c : Nat) : Derivation (head7 a b c) := by
  have hp := NumericDecode.pair_bounds a b
  have hka : wel a b ≠ a := by simp only [wel]; omega
  have hkb : wel a b ≠ b := by simp only [wel]; omega
  let heca : Context [weq c b,weq c a] (weq c a) := .assumption (by simp)
  let hecb : Context [weq c b,weq c a] (weq c b) := .assumption (by simp)
  let heab : Context [weq c b,weq c a] (weq a b) :=
    .mp hecb (.mp heca (.closed (.r7 c a b)))
  exact (Context.mp heab (.closed (equalityVacuity a b (wel a b) hka hkb))).deduction.deduction.empty

def doubleNegationIntroduction (a : Nat) : Derivation (wim a (wn (wn a))) := by
  let ha : Context [wn a,a] a := .assumption (by simp)
  let hn : Context [wn a,a] (wn a) := .assumption (by simp)
  exact (Context.mp ha hn).deduction.deduction.empty

def rawBundle_proof (a b c : Nat) (ha : c ≠ a) (hb : c ≠ b) :
    Derivation (rawBundle a b c) := by
  let old : Context [] (bundle a b c) := .closed (.guardedBundle a b c ha hb)
  let hv : Derivation (memVacuity a b c) := old.andRight.andRight.empty
  let he : Derivation (wex c (wa (separationBody a b c) (point b c))) := old.andLeft.empty
  let f := wim (memVacuity a b c) (wal c (wim (separationBody a b c) (wn (point b c))))
  let hf : Context [f] f := .assumption (by simp)
  let hall : Context [f] (wal c (wim (separationBody a b c) (wn (point b c)))) :=
    .mp (.closed hv) hf
  let hallnot : Context [f] (wal c (wn (wa (separationBody a b c) (point b c)))) :=
    hall.forallMP c (.closed (.all c (doubleNegationIntroduction
      (wim (separationBody a b c) (wn (point b c))))))
  exact (Context.mp hallnot (.closed he)).deduction.empty

#print axioms head3_proof
#print axioms head5_proof
#print axioms head7_proof
#print axioms rawBundle_proof
end PA215.PA.NativeCalculus.ActualAX
