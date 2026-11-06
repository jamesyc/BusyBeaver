import PA215.CertifiedContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard000Part5
open PA215.Contracts PA215.Runtime

def c86 : Contract := ⟨some (8, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 47, .run true 0 1, .box (.plain (.dec 8))])⟩

theorem checked86 : check 4000 c86 = true := by decide

def c87 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 46, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 45, .run true 0 1, .box (.plain (.inc 2))])⟩

theorem checked87 : check 4000 c87 = true := by decide

def c88 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 45, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain .none)])⟩

theorem checked88 : check 4000 c88 = true := by decide

def c89 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 48, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 52, .run true 0 1, .box (.plain .none)])⟩

theorem checked89 : check 4000 c89 = true := by decide

def c90 : Contract := ⟨some (5, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 3, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 2, .run false 1 54, .run true 0 1, .box (.plain .none)])⟩

theorem checked90 : check 4000 c90 = true := by decide

def c91 : Contract := ⟨some (5, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 3, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 4, .run false 1 51, .run true 0 1, .box (.plain (.dec 5))])⟩

theorem checked91 : check 4000 c91 = true := by decide

def c92 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 4, .run false 1 50, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 5, .run false 1 49, .run true 0 1, .box (.plain (.inc 0))])⟩

theorem checked92 : check 4000 c92 = true := by decide

def c93 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 5, .run false 1 49, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 3, .run false 1 51, .run true 0 1, .box (.plain .none)])⟩

theorem checked93 : check 4000 c93 = true := by decide

def c94 : Contract := ⟨some (7, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 2, .run false 1 54, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 3, .run false 1 53, .run true 0 1, .box (.plain .none)])⟩

theorem checked94 : check 4000 c94 = true := by decide

def c95 : Contract := ⟨some (7, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 2, .run false 1 54, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 53, .run true 0 1, .box (.plain (.dec 7))])⟩

theorem checked95 : check 4000 c95 = true := by decide

def c96 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 52, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 51, .run true 0 1, .box (.plain (.inc 2))])⟩

theorem checked96 : check 4000 c96 = true := by decide

def c97 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 50, .run true 0 1, .box (.plain (.inc 8))])⟩

theorem checked97 : check 4000 c97 = true := by decide

def c98 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 50, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 2, .run false 1 54, .run true 0 1, .box (.plain .none)])⟩

theorem checked98 : check 4000 c98 = true := by decide

def c99 : Contract := ⟨some (8, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 3, .run false 1 53, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 56, .run true 0 1, .box (.plain .none)])⟩

theorem checked99 : check 4000 c99 = true := by decide

def c100 : Contract := ⟨some (8, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 3, .run false 1 53, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 4, .run false 1 53, .run true 0 1, .box (.plain (.dec 8))])⟩

theorem checked100 : check 4000 c100 = true := by decide

def c101 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 4, .run false 1 52, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 5, .run false 1 51, .run true 0 1, .box (.plain (.inc 7))])⟩

theorem checked101 : check 4000 c101 = true := by decide

def records : List Certified := [
  ⟨86, c86, 4000, checked86⟩,
  ⟨87, c87, 4000, checked87⟩,
  ⟨88, c88, 4000, checked88⟩,
  ⟨89, c89, 4000, checked89⟩,
  ⟨90, c90, 4000, checked90⟩,
  ⟨91, c91, 4000, checked91⟩,
  ⟨92, c92, 4000, checked92⟩,
  ⟨93, c93, 4000, checked93⟩,
  ⟨94, c94, 4000, checked94⟩,
  ⟨95, c95, 4000, checked95⟩,
  ⟨96, c96, 4000, checked96⟩,
  ⟨97, c97, 4000, checked97⟩,
  ⟨98, c98, 4000, checked98⟩,
  ⟨99, c99, 4000, checked99⟩,
  ⟨100, c100, 4000, checked100⟩,
  ⟨101, c101, 4000, checked101⟩]

end PA215.ContractShards.Shard000Part5
