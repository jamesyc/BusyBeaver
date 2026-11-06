import PA215PA.ActualBasisLogic

/-! Classical extraction of the pointed existential from the literal AX bundle. -/
namespace PA215.PA.NativeCalculus.ActualCore
def negatedImplicationRight (a b : Nat) : Proof (wim (wn (wim a b)) (wn b)) := by
  let hb : Context [b,wn (wim a b)] b := .assumption (by simp)
  let hn : Context [b,wn (wim a b)] (wn (wim a b)) := .assumption (by simp)
  exact (Context.mp (hb.lift a) hn).deduction.deduction.empty
end PA215.PA.NativeCalculus.ActualCore

namespace PA215.PA.NativeCalculus.ActualBasis
open PA215.Source

def pointedExistential (a b c : Nat) (ha : c ≠ a) (hb : c ≠ b) :
    Proof (wex c (wa (ActualAXCode.separation a b c) (ActualAXCode.point a b c))) := by
  let s := ActualAXCode.separation a b c
  let p := ActualAXCode.point a b c
  let m := ActualAXCode.memVac a b c
  have he : ActualAXCode.bundle a b c = wn (wim m (wal c (wim s (wn p)))) := by
    simp only [ActualAXCode.bundle,AXCode.wn,AXCode.wim,AXCode.wal,wn,wim,wal,m,s,p]
  let hraw : Proof (wn (wim m (wal c (wim s (wn p))))) := he ▸ Proof.bundle a b c ha hb
  let hn : Proof (wn (wal c (wim s (wn p)))) :=
    .mp hraw (fromCore (ActualCore.negatedImplicationRight m _))
  let hforall : Proof (wim (wal c (wn (wn (wim s (wn p))))) (wal c (wim s (wn p)))) :=
    .mp (.all c (doubleNegationElimination (wim s (wn p)))) (r2 c _ _)
  exact .mp hn (contrapose hforall)

#print axioms pointedExistential
end PA215.PA.NativeCalculus.ActualBasis
