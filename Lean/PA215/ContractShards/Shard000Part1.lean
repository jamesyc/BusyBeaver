import PA215.CertifiedContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard000Part1
open PA215.Contracts PA215.Runtime

def c22 : Contract := ⟨none, (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 3, .run false 1 57, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 1 62, .run true 0 1, .box (.plain .none)])⟩

theorem checked22 : check 4000 c22 = true := by decide

def c23 : Contract := ⟨some (5, true), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 60, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 2, .run false 1 61, .run true 0 1, .box (.plain .none)])⟩

theorem checked23 : check 4000 c23 = true := by decide

def c24 : Contract := ⟨some (5, false), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 60, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 60, .run true 0 1, .box (.plain (.dec 5))])⟩

theorem checked24 : check 4000 c24 = true := by decide

def c25 : Contract := ⟨none, (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 59, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 1, .run true 0 3, .run false 1 58, .run true 0 1, .box (.plain (.inc 1))])⟩

theorem checked25 : check 4000 c25 = true := by decide

def c26 : Contract := ⟨none, (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 1, .run true 0 3, .run false 1 58, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 60, .run true 0 1, .box (.plain .none)])⟩

theorem checked26 : check 4000 c26 = true := by decide

def c27 : Contract := ⟨some (8, true), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 2, .run false 1 61, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 1 63, .run true 0 1, .box (.plain .none)])⟩

theorem checked27 : check 4000 c27 = true := by decide

def c28 : Contract := ⟨some (8, false), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 2, .run false 1 61, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 3, .run false 1 61, .run true 0 1, .box (.plain (.dec 8))])⟩

theorem checked28 : check 4000 c28 = true := by decide

def c29 : Contract := ⟨none, (84, false, [.run true 0 1], [.run false 0 1, .run true 0 3, .run false 1 60, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 4, .run false 1 59, .run true 0 1, .box (.plain (.inc 4))])⟩

theorem checked29 : check 4000 c29 = true := by decide

def c30 : Contract := ⟨none, (84, false, [.run true 0 1], [.run false 0 1, .run true 0 4, .run false 1 59, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 2, .run false 1 61, .run true 0 1, .box (.plain .none)])⟩

theorem checked30 : check 4000 c30 = true := by decide

def c31 : Contract := ⟨some (4, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 1 63, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 2, .run false 1 62, .run true 0 1, .box (.plain .none)])⟩

theorem checked31 : check 4000 c31 = true := by decide

def c32 : Contract := ⟨some (4, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 1 63, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 1 62, .run true 0 1, .box (.plain (.dec 4))])⟩

theorem checked32 : check 4000 c32 = true := by decide

def c33 : Contract := ⟨some (4, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 1 61, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 59, .run true 0 1, .box (.plain .none)])⟩

theorem checked33 : check 4000 c33 = true := by decide

def c34 : Contract := ⟨some (4, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 1 61, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 1 59, .run true 0 1, .box (.plain (.dec 4))])⟩

theorem checked34 : check 4000 c34 = true := by decide

def c35 : Contract := ⟨some (2, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 1 58, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 1, .run false 1 53, .run true 0 1, .box (.plain .none)])⟩

theorem checked35 : check 4000 c35 = true := by decide

def c36 : Contract := ⟨some (2, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 1 58, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 5, .run true 0 1, .run false 1 53, .run true 0 1, .box (.plain (.dec 2))])⟩

theorem checked36 : check 4000 c36 = true := by decide

def c37 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 5, .run true 0 1, .run false 1 52, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 5, .run true 0 2, .run false 1 51, .run true 0 1, .box (.plain (.inc 8))])⟩

theorem checked37 : check 4000 c37 = true := by decide

def records : List Certified := [
  ⟨22, c22, 4000, checked22⟩,
  ⟨23, c23, 4000, checked23⟩,
  ⟨24, c24, 4000, checked24⟩,
  ⟨25, c25, 4000, checked25⟩,
  ⟨26, c26, 4000, checked26⟩,
  ⟨27, c27, 4000, checked27⟩,
  ⟨28, c28, 4000, checked28⟩,
  ⟨29, c29, 4000, checked29⟩,
  ⟨30, c30, 4000, checked30⟩,
  ⟨31, c31, 4000, checked31⟩,
  ⟨32, c32, 4000, checked32⟩,
  ⟨33, c33, 4000, checked33⟩,
  ⟨34, c34, 4000, checked34⟩,
  ⟨35, c35, 4000, checked35⟩,
  ⟨36, c36, 4000, checked36⟩,
  ⟨37, c37, 4000, checked37⟩]

end PA215.ContractShards.Shard000Part1
