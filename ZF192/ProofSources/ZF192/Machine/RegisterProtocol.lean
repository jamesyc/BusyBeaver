module
public import ZF192.Machine.Literal
@[expose] public section

namespace M192

def copy0 : Nat := 79
def copy1 : Nat := 96
def delBegin : Nat := 118
def delTest : Nat := 111
def retS : Nat := 125
def retZ : Nat := 124
def readSuccess : Nat := 117
def readZero : Nat := 129
def gateArith : Nat := 134
def root : Nat := 157
def halt : Nat := 192

def chainI : List Nat := [79, 59, 42, 26, 67, 69, 49, 52, 33, 89, 102]
def chainD : List Nat := [118, 106, 91, 74, 56, 70, 51, 36, 50, 66, 103]

def ChainRows (chain:List Nat) : Prop :=
 (∀k:Fin 10,M192.literal (chain.getD (k.val+1) 0) false=some (false,false,chain.getD k.val 0)) ∧
 (∀k:Fin 10,M192.literal (chain.getD (k.val+1) 0) true=some (true,false,chain.getD (k.val+1) 0))
theorem chainI_rows : ChainRows chainI := by unfold ChainRows; decide +kernel
theorem chainD_rows : ChainRows chainD := by unfold ChainRows; decide +kernel
theorem chainI_zero : chainI.getD 0 0=copy0 := rfl
theorem chainD_zero : chainD.getD 0 0=delBegin := rfl

theorem row_copy0_0 : literal copy0 false = some (true, false, copy1) := by decide +kernel
theorem row_copy0_1 : literal copy0 true = some (true, false, copy0) := by decide +kernel
theorem row_copy1_0 : literal copy1 false = some (true, true, delTest) := by decide +kernel
theorem row_copy1_1 : literal copy1 true = some (false, false, copy0) := by decide +kernel
theorem row_delBegin_0 : literal delBegin false = some (false, true, readZero) := by decide +kernel
theorem row_delBegin_1 : literal delBegin true = some (true, false, delTest) := by decide +kernel
theorem row_delTest_0 : literal delTest false = some (false, true, retZ) := by decide +kernel
theorem row_delTest_1 : literal delTest true = some (false, true, retS) := by decide +kernel
theorem row_gateArith_0 : literal gateArith false = some (true, true, readSuccess) := by decide +kernel
theorem row_gateArith_1 : literal gateArith true = some (true, false, copy1) := by decide +kernel
theorem row_retS_0 : literal retS false = some (false, true, gateArith) := by decide +kernel
theorem row_retS_1 : literal retS true = some (true, false, retS) := by decide +kernel
theorem row_retZ_0 : literal retZ false = some (false, true, delBegin) := by decide +kernel
theorem row_retZ_1 : literal retZ true = some (true, true, retZ) := by decide +kernel
theorem row_readSuccess_1 : literal readSuccess true = some (true, true, readSuccess) := by decide +kernel
theorem row_readZero_1 : literal readZero true = some (true, true, readZero) := by decide +kernel

end M192
