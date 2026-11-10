import PA215.Contracts
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.ContractPilot
open PA215.Runtime PA215.Contracts
def c0 : Contract := ⟨some (1, true), (84, false, [.run true 0 1], [.run false 1 64, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 2, .run true 0 1, .run false 1 61, .run true 0 1, .box (.plain .none)])⟩
def c1 : Contract := ⟨some (1, false), (84, false, [.run true 0 1], [.run false 1 64, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 3, .run true 0 1, .run false 1 61, .run true 0 1, .box (.plain (.dec 1))])⟩
def c2 : Contract := ⟨none, (84, false, [.run true 0 1], [.run false 0 3, .run true 0 1, .run false 1 60, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 1 62, .run true 0 1, .box (.plain .none)])⟩
def c5 : Contract := ⟨none, (84, false, [.run true 0 1], [.run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 59, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 58, .run true 0 1, .box (.plain (.inc 1))])⟩
def c6 : Contract := ⟨none, (84, false, [.run true 0 1], [.run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 58, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 2, .run true 0 1, .run false 0 1, .run true 0 3, .run false 1 57, .run true 0 1, .box (.plain (.inc 8))])⟩
def c7 : Contract := ⟨none, (84, false, [.run true 0 1], [.run false 0 2, .run true 0 1, .run false 0 1, .run true 0 3, .run false 1 57, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 2, .run true 0 1, .run false 1 61, .run true 0 1, .box (.plain .none)])⟩
def c5085 : Contract := ⟨some (2, true), (84, false, [.run true 0 1], [.run true 0 2, .run false 1 62, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 3, .run false 1 61, .run true 0 1, .box (.plain .none)])⟩
def c5086 : Contract := ⟨some (2, false), (84, false, [.run true 0 1], [.run true 0 2, .run false 1 62, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 2, .run false 0 1, .run true 0 1, .run false 1 61, .run true 0 1, .box (.plain (.dec 2))])⟩
def c5087 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 2, .run false 0 1, .run true 0 1, .run false 1 60, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 2, .run false 0 1, .run true 0 2, .run false 1 59, .run true 0 1, .box (.plain (.inc 8))])⟩
def c5088 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 2, .run false 0 1, .run true 0 2, .run false 1 59, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 2, .run false 1 62, .run true 0 1, .box (.plain .none)])⟩
theorem checked0 : check 4000 c0 = true := by decide

theorem uniform0 (n : Nat) (vs : List Nat) (hv : Valid c0.branch vs) :
    PA215.Zip.Reach1 PA215.NativeTable.machine (conc n vs c0.initial) (conc n vs c0.target) :=
  sound 4000 c0 checked0 n vs hv

theorem checked1 : check 4000 c1 = true := by decide

theorem uniform1 (n : Nat) (vs : List Nat) (hv : Valid c1.branch vs) :
    PA215.Zip.Reach1 PA215.NativeTable.machine (conc n vs c1.initial) (conc n vs c1.target) :=
  sound 4000 c1 checked1 n vs hv

theorem checked2 : check 4000 c2 = true := by decide

theorem uniform2 (n : Nat) (vs : List Nat) (hv : Valid c2.branch vs) :
    PA215.Zip.Reach1 PA215.NativeTable.machine (conc n vs c2.initial) (conc n vs c2.target) :=
  sound 4000 c2 checked2 n vs hv

theorem checked5 : check 4000 c5 = true := by decide

theorem uniform5 (n : Nat) (vs : List Nat) (hv : Valid c5.branch vs) :
    PA215.Zip.Reach1 PA215.NativeTable.machine (conc n vs c5.initial) (conc n vs c5.target) :=
  sound 4000 c5 checked5 n vs hv

theorem checked6 : check 4000 c6 = true := by decide

theorem uniform6 (n : Nat) (vs : List Nat) (hv : Valid c6.branch vs) :
    PA215.Zip.Reach1 PA215.NativeTable.machine (conc n vs c6.initial) (conc n vs c6.target) :=
  sound 4000 c6 checked6 n vs hv

theorem checked7 : check 4000 c7 = true := by decide

theorem uniform7 (n : Nat) (vs : List Nat) (hv : Valid c7.branch vs) :
    PA215.Zip.Reach1 PA215.NativeTable.machine (conc n vs c7.initial) (conc n vs c7.target) :=
  sound 4000 c7 checked7 n vs hv

theorem checked5085 : check 4000 c5085 = true := by decide

theorem uniform5085 (n : Nat) (vs : List Nat) (hv : Valid c5085.branch vs) :
    PA215.Zip.Reach1 PA215.NativeTable.machine (conc n vs c5085.initial) (conc n vs c5085.target) :=
  sound 4000 c5085 checked5085 n vs hv

theorem checked5086 : check 4000 c5086 = true := by decide

theorem uniform5086 (n : Nat) (vs : List Nat) (hv : Valid c5086.branch vs) :
    PA215.Zip.Reach1 PA215.NativeTable.machine (conc n vs c5086.initial) (conc n vs c5086.target) :=
  sound 4000 c5086 checked5086 n vs hv

theorem checked5087 : check 4000 c5087 = true := by decide

theorem uniform5087 (n : Nat) (vs : List Nat) (hv : Valid c5087.branch vs) :
    PA215.Zip.Reach1 PA215.NativeTable.machine (conc n vs c5087.initial) (conc n vs c5087.target) :=
  sound 4000 c5087 checked5087 n vs hv

theorem checked5088 : check 4000 c5088 = true := by decide

theorem uniform5088 (n : Nat) (vs : List Nat) (hv : Valid c5088.branch vs) :
    PA215.Zip.Reach1 PA215.NativeTable.machine (conc n vs c5088.initial) (conc n vs c5088.target) :=
  sound 4000 c5088 checked5088 n vs hv

end PA215.ContractPilot
