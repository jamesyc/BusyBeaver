import PA215.CertifiedContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard000Part7
open PA215.Contracts PA215.Runtime

def c118 : Contract := ⟨some (2, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 1 52, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 50, .run true 0 1, .box (.plain .none)])⟩

theorem checked118 : check 4000 c118 = true := by decide

def c119 : Contract := ⟨some (2, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 1 52, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 2, .run true 0 1, .run false 1 50, .run true 0 1, .box (.plain (.dec 2))])⟩

theorem checked119 : check 4000 c119 = true := by decide

def c120 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 2, .run true 0 1, .run false 1 49, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 2, .run true 0 2, .run false 1 48, .run true 0 1, .box (.plain (.inc 5))])⟩

theorem checked120 : check 4000 c120 = true := by decide

def c121 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 2, .run true 0 2, .run false 1 48, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 2, .run true 0 3, .run false 1 47, .run true 0 1, .box (.plain (.inc 8))])⟩

theorem checked121 : check 4000 c121 = true := by decide

def c122 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 2, .run true 0 3, .run false 1 47, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 1 52, .run true 0 1, .box (.plain .none)])⟩

theorem checked122 : check 4000 c122 = true := by decide

def c123 : Contract := ⟨some (8, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 50, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 2, .run false 1 51, .run true 0 1, .box (.plain .none)])⟩

theorem checked123 : check 4000 c123 = true := by decide

def c124 : Contract := ⟨some (8, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 50, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 50, .run true 0 1, .box (.plain (.dec 8))])⟩

theorem checked124 : check 4000 c124 = true := by decide

def c125 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 49, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain (.inc 5))])⟩

theorem checked125 : check 4000 c125 = true := by decide

def c126 : Contract := ⟨some (8, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 3, .run false 1 48, .run true 0 1, .box (.plain .none)])⟩

theorem checked126 : check 4000 c126 = true := by decide

def c127 : Contract := ⟨some (8, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 47, .run true 0 1, .box (.plain (.dec 8))])⟩

theorem checked127 : check 4000 c127 = true := by decide

def c128 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 46, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 45, .run true 0 1, .box (.plain (.inc 2))])⟩

theorem checked128 : check 4000 c128 = true := by decide

def c129 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 45, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain .none)])⟩

theorem checked129 : check 4000 c129 = true := by decide

def c130 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 3, .run false 1 48, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 1 52, .run true 0 1, .box (.plain .none)])⟩

theorem checked130 : check 4000 c130 = true := by decide

def c131 : Contract := ⟨some (5, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 2, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 1 53, .run true 0 1, .box (.plain .none)])⟩

theorem checked131 : check 4000 c131 = true := by decide

def c132 : Contract := ⟨some (5, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 2, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 3, .run false 1 51, .run true 0 1, .box (.plain (.dec 5))])⟩

theorem checked132 : check 4000 c132 = true := by decide

def c133 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 3, .run false 1 50, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 3, .run false 0 2, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain (.inc 2))])⟩

theorem checked133 : check 4000 c133 = true := by decide

def records : List Certified := [
  ⟨118, c118, 4000, checked118⟩,
  ⟨119, c119, 4000, checked119⟩,
  ⟨120, c120, 4000, checked120⟩,
  ⟨121, c121, 4000, checked121⟩,
  ⟨122, c122, 4000, checked122⟩,
  ⟨123, c123, 4000, checked123⟩,
  ⟨124, c124, 4000, checked124⟩,
  ⟨125, c125, 4000, checked125⟩,
  ⟨126, c126, 4000, checked126⟩,
  ⟨127, c127, 4000, checked127⟩,
  ⟨128, c128, 4000, checked128⟩,
  ⟨129, c129, 4000, checked129⟩,
  ⟨130, c130, 4000, checked130⟩,
  ⟨131, c131, 4000, checked131⟩,
  ⟨132, c132, 4000, checked132⟩,
  ⟨133, c133, 4000, checked133⟩]

end PA215.ContractShards.Shard000Part7
