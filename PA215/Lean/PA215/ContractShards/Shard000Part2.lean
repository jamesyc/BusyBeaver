import PA215.CertifiedContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard000Part2
open PA215.Contracts PA215.Runtime

def c38 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 5, .run true 0 2, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 1 58, .run true 0 1, .box (.plain .none)])⟩

theorem checked38 : check 4000 c38 = true := by decide

def c39 : Contract := ⟨some (0, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 1, .run false 1 53, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 1 52, .run true 0 1, .box (.plain .none)])⟩

theorem checked39 : check 4000 c39 = true := by decide

def c40 : Contract := ⟨some (0, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 1, .run false 1 53, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 52, .run true 0 1, .box (.plain (.dec 0))])⟩

theorem checked40 : check 4000 c40 = true := by decide

def c41 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 50, .run true 0 1, .box (.plain (.inc 2))])⟩

theorem checked41 : check 4000 c41 = true := by decide

def c42 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 50, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 1, .run false 1 53, .run true 0 1, .box (.plain .none)])⟩

theorem checked42 : check 4000 c42 = true := by decide

def c43 : Contract := ⟨some (2, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 1 52, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 50, .run true 0 1, .box (.plain .none)])⟩

theorem checked43 : check 4000 c43 = true := by decide

def c44 : Contract := ⟨some (2, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 1 52, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 2, .run true 0 1, .run false 1 50, .run true 0 1, .box (.plain (.dec 2))])⟩

theorem checked44 : check 4000 c44 = true := by decide

def c45 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 2, .run true 0 1, .run false 1 49, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 2, .run true 0 2, .run false 1 48, .run true 0 1, .box (.plain (.inc 5))])⟩

theorem checked45 : check 4000 c45 = true := by decide

def c46 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 2, .run true 0 2, .run false 1 48, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 2, .run true 0 3, .run false 1 47, .run true 0 1, .box (.plain (.inc 8))])⟩

theorem checked46 : check 4000 c46 = true := by decide

def c47 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 2, .run true 0 3, .run false 1 47, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 1 52, .run true 0 1, .box (.plain .none)])⟩

theorem checked47 : check 4000 c47 = true := by decide

def c48 : Contract := ⟨some (8, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 50, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 3, .run false 1 51, .run true 0 1, .box (.plain .none)])⟩

theorem checked48 : check 4000 c48 = true := by decide

def c49 : Contract := ⟨some (8, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 50, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 50, .run true 0 1, .box (.plain (.dec 8))])⟩

theorem checked49 : check 4000 c49 = true := by decide

def c50 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 49, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain (.inc 5))])⟩

theorem checked50 : check 4000 c50 = true := by decide

def c51 : Contract := ⟨some (8, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 48, .run true 0 1, .box (.plain .none)])⟩

theorem checked51 : check 4000 c51 = true := by decide

def c52 : Contract := ⟨some (8, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 47, .run true 0 1, .box (.plain (.dec 8))])⟩

theorem checked52 : check 4000 c52 = true := by decide

def c53 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 46, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 45, .run true 0 1, .box (.plain (.inc 2))])⟩

theorem checked53 : check 4000 c53 = true := by decide

def records : List Certified := [
  ⟨38, c38, 4000, checked38⟩,
  ⟨39, c39, 4000, checked39⟩,
  ⟨40, c40, 4000, checked40⟩,
  ⟨41, c41, 4000, checked41⟩,
  ⟨42, c42, 4000, checked42⟩,
  ⟨43, c43, 4000, checked43⟩,
  ⟨44, c44, 4000, checked44⟩,
  ⟨45, c45, 4000, checked45⟩,
  ⟨46, c46, 4000, checked46⟩,
  ⟨47, c47, 4000, checked47⟩,
  ⟨48, c48, 4000, checked48⟩,
  ⟨49, c49, 4000, checked49⟩,
  ⟨50, c50, 4000, checked50⟩,
  ⟨51, c51, 4000, checked51⟩,
  ⟨52, c52, 4000, checked52⟩,
  ⟨53, c53, 4000, checked53⟩]

end PA215.ContractShards.Shard000Part2
