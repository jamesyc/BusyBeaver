import PA215.CertifiedContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard000Part0
open PA215.Contracts PA215.Runtime

def c3 : Contract := ⟨some (6, true), (84, false, [.run true 0 1], [.run false 0 2, .run true 0 1, .run false 1 61, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 2, .run true 0 2, .run false 1 60, .run true 0 1, .box (.plain .none)])⟩

theorem checked3 : check 4000 c3 = true := by decide

def c4 : Contract := ⟨some (6, false), (84, false, [.run true 0 1], [.run false 0 2, .run true 0 1, .run false 1 61, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 60, .run true 0 1, .box (.plain (.dec 6))])⟩

theorem checked4 : check 4000 c4 = true := by decide

def c8 : Contract := ⟨none, (84, false, [.run true 0 1], [.run false 0 2, .run true 0 2, .run false 1 60, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 2, .run true 0 3, .run false 1 59, .run true 0 1, .box (.plain (.inc 6))])⟩

theorem checked8 : check 4000 c8 = true := by decide

def c9 : Contract := ⟨some (8, true), (84, false, [.run true 0 1], [.run false 0 2, .run true 0 3, .run false 1 59, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 1 62, .run true 0 1, .box (.plain .none)])⟩

theorem checked9 : check 4000 c9 = true := by decide

def c10 : Contract := ⟨some (8, false), (84, false, [.run true 0 1], [.run false 0 2, .run true 0 3, .run false 1 59, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 2, .run true 0 4, .run false 1 59, .run true 0 1, .box (.plain (.dec 8))])⟩

theorem checked10 : check 4000 c10 = true := by decide

def c11 : Contract := ⟨none, (84, false, [.run true 0 1], [.run false 0 2, .run true 0 4, .run false 1 58, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 2, .run true 0 2, .run false 1 60, .run true 0 1, .box (.plain .none)])⟩

theorem checked11 : check 4000 c11 = true := by decide

def c12 : Contract := ⟨some (1, true), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 1 62, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 60, .run true 0 1, .box (.plain .none)])⟩

theorem checked12 : check 4000 c12 = true := by decide

def c13 : Contract := ⟨some (1, false), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 1 62, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 1 60, .run true 0 1, .box (.plain (.dec 1))])⟩

theorem checked13 : check 4000 c13 = true := by decide

def c14 : Contract := ⟨none, (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 1 59, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 2, .run false 1 58, .run true 0 1, .box (.plain (.inc 5))])⟩

theorem checked14 : check 4000 c14 = true := by decide

def c15 : Contract := ⟨some (8, true), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 2, .run false 1 58, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 56, .run true 0 1, .box (.plain .none)])⟩

theorem checked15 : check 4000 c15 = true := by decide

def c16 : Contract := ⟨some (8, false), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 2, .run false 1 58, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 2, .run true 0 1, .run false 1 56, .run true 0 1, .box (.plain (.dec 8))])⟩

theorem checked16 : check 4000 c16 = true := by decide

def c17 : Contract := ⟨none, (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 2, .run true 0 1, .run false 1 55, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 3, .run false 1 57, .run true 0 1, .box (.plain .none)])⟩

theorem checked17 : check 4000 c17 = true := by decide

def c18 : Contract := ⟨some (5, true), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 56, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 3, .run false 1 57, .run true 0 1, .box (.plain .none)])⟩

theorem checked18 : check 4000 c18 = true := by decide

def c19 : Contract := ⟨some (5, false), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 56, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 56, .run true 0 1, .box (.plain (.dec 5))])⟩

theorem checked19 : check 4000 c19 = true := by decide

def c20 : Contract := ⟨none, (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 55, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 54, .run true 0 1, .box (.plain (.inc 8))])⟩

theorem checked20 : check 4000 c20 = true := by decide

def c21 : Contract := ⟨none, (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 54, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run false 0 1, .run true 0 1, .run false 0 2, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 56, .run true 0 1, .box (.plain .none)])⟩

theorem checked21 : check 4000 c21 = true := by decide

def records : List Certified := [
  ⟨3, c3, 4000, checked3⟩,
  ⟨4, c4, 4000, checked4⟩,
  ⟨8, c8, 4000, checked8⟩,
  ⟨9, c9, 4000, checked9⟩,
  ⟨10, c10, 4000, checked10⟩,
  ⟨11, c11, 4000, checked11⟩,
  ⟨12, c12, 4000, checked12⟩,
  ⟨13, c13, 4000, checked13⟩,
  ⟨14, c14, 4000, checked14⟩,
  ⟨15, c15, 4000, checked15⟩,
  ⟨16, c16, 4000, checked16⟩,
  ⟨17, c17, 4000, checked17⟩,
  ⟨18, c18, 4000, checked18⟩,
  ⟨19, c19, 4000, checked19⟩,
  ⟨20, c20, 4000, checked20⟩,
  ⟨21, c21, 4000, checked21⟩]

end PA215.ContractShards.Shard000Part0
