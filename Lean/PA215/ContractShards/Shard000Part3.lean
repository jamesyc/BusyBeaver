import PA215.CertifiedContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard000Part3
open PA215.Contracts PA215.Runtime

def c54 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 45, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain .none)])⟩

theorem checked54 : check 4000 c54 = true := by decide

def c55 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 48, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 2, .run false 1 52, .run true 0 1, .box (.plain .none)])⟩

theorem checked55 : check 4000 c55 = true := by decide

def c56 : Contract := ⟨some (5, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 3, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 1, .run false 1 54, .run true 0 1, .box (.plain .none)])⟩

theorem checked56 : check 4000 c56 = true := by decide

def c57 : Contract := ⟨some (5, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 3, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 4, .run false 1 51, .run true 0 1, .box (.plain (.dec 5))])⟩

theorem checked57 : check 4000 c57 = true := by decide

def c58 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 4, .run false 1 50, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 5, .run false 1 49, .run true 0 1, .box (.plain (.inc 0))])⟩

theorem checked58 : check 4000 c58 = true := by decide

def c59 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 5, .run false 1 49, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 4, .run true 0 3, .run false 1 51, .run true 0 1, .box (.plain .none)])⟩

theorem checked59 : check 4000 c59 = true := by decide

def c60 : Contract := ⟨some (3, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 1, .run false 1 54, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 2, .run false 1 53, .run true 0 1, .box (.plain .none)])⟩

theorem checked60 : check 4000 c60 = true := by decide

def c61 : Contract := ⟨some (3, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 1, .run false 1 54, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 53, .run true 0 1, .box (.plain (.dec 3))])⟩

theorem checked61 : check 4000 c61 = true := by decide

def c62 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 52, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 51, .run true 0 1, .box (.plain (.inc 2))])⟩

theorem checked62 : check 4000 c62 = true := by decide

def c63 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 3, .run false 1 50, .run true 0 1, .box (.plain (.inc 8))])⟩

theorem checked63 : check 4000 c63 = true := by decide

def c64 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 1, .run false 0 1, .run true 0 3, .run false 1 50, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 1, .run false 1 54, .run true 0 1, .box (.plain .none)])⟩

theorem checked64 : check 4000 c64 = true := by decide

def c65 : Contract := ⟨some (8, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 2, .run false 1 53, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 1 55, .run true 0 1, .box (.plain .none)])⟩

theorem checked65 : check 4000 c65 = true := by decide

def c66 : Contract := ⟨some (8, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 2, .run false 1 53, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 3, .run false 1 53, .run true 0 1, .box (.plain (.dec 8))])⟩

theorem checked66 : check 4000 c66 = true := by decide

def c67 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 3, .run false 1 52, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 4, .run false 1 51, .run true 0 1, .box (.plain (.inc 3))])⟩

theorem checked67 : check 4000 c67 = true := by decide

def c68 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 4, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 3, .run true 0 2, .run false 1 53, .run true 0 1, .box (.plain .none)])⟩

theorem checked68 : check 4000 c68 = true := by decide

def c69 : Contract := ⟨some (2, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 1 55, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 53, .run true 0 1, .box (.plain .none)])⟩

theorem checked69 : check 4000 c69 = true := by decide

def records : List Certified := [
  ⟨54, c54, 4000, checked54⟩,
  ⟨55, c55, 4000, checked55⟩,
  ⟨56, c56, 4000, checked56⟩,
  ⟨57, c57, 4000, checked57⟩,
  ⟨58, c58, 4000, checked58⟩,
  ⟨59, c59, 4000, checked59⟩,
  ⟨60, c60, 4000, checked60⟩,
  ⟨61, c61, 4000, checked61⟩,
  ⟨62, c62, 4000, checked62⟩,
  ⟨63, c63, 4000, checked63⟩,
  ⟨64, c64, 4000, checked64⟩,
  ⟨65, c65, 4000, checked65⟩,
  ⟨66, c66, 4000, checked66⟩,
  ⟨67, c67, 4000, checked67⟩,
  ⟨68, c68, 4000, checked68⟩,
  ⟨69, c69, 4000, checked69⟩]

end PA215.ContractShards.Shard000Part3
