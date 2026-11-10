import PA215.CertifiedContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard000Part6
open PA215.Contracts PA215.Runtime

def c102 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 5, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 3, .run false 1 53, .run true 0 1, .box (.plain .none)])⟩

theorem checked102 : check 4000 c102 = true := by decide

def c103 : Contract := ⟨some (0, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 56, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 4, .run true 0 1, .run false 1 51, .run true 0 1, .box (.plain .none)])⟩

theorem checked103 : check 4000 c103 = true := by decide

def c104 : Contract := ⟨some (0, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 56, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 1, .run false 1 51, .run true 0 1, .box (.plain (.dec 0))])⟩

theorem checked104 : check 4000 c104 = true := by decide

def c105 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 1, .run false 1 50, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 2, .run false 1 49, .run true 0 1, .box (.plain (.inc 5))])⟩

theorem checked105 : check 4000 c105 = true := by decide

def c106 : Contract := ⟨some (8, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 2, .run false 1 49, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain .none)])⟩

theorem checked106 : check 4000 c106 = true := by decide

def c107 : Contract := ⟨some (8, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 2, .run false 1 49, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 2, .run false 0 2, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain (.dec 8))])⟩

theorem checked107 : check 4000 c107 = true := by decide

def c108 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 2, .run false 0 2, .run true 0 1, .run false 1 46, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 3, .run false 1 48, .run true 0 1, .box (.plain .none)])⟩

theorem checked108 : check 4000 c108 = true := by decide

def c109 : Contract := ⟨some (5, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 3, .run false 1 48, .run true 0 1, .box (.plain .none)])⟩

theorem checked109 : check 4000 c109 = true := by decide

def c110 : Contract := ⟨some (5, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 47, .run true 0 1, .box (.plain (.dec 5))])⟩

theorem checked110 : check 4000 c110 = true := by decide

def c111 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 46, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 45, .run true 0 1, .box (.plain (.inc 8))])⟩

theorem checked111 : check 4000 c111 = true := by decide

def c112 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 45, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain .none)])⟩

theorem checked112 : check 4000 c112 = true := by decide

def c113 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 5, .run true 0 3, .run false 1 48, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 56, .run true 0 1, .box (.plain .none)])⟩

theorem checked113 : check 4000 c113 = true := by decide

def c114 : Contract := ⟨some (5, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 4, .run true 0 1, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 3, .run true 0 1, .run false 1 52, .run true 0 1, .box (.plain .none)])⟩

theorem checked114 : check 4000 c114 = true := by decide

def c115 : Contract := ⟨some (5, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 4, .run true 0 1, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 4, .run true 0 2, .run false 1 51, .run true 0 1, .box (.plain (.dec 5))])⟩

theorem checked115 : check 4000 c115 = true := by decide

def c116 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 4, .run true 0 2, .run false 1 50, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 4, .run true 0 3, .run false 1 49, .run true 0 1, .box (.plain (.inc 0))])⟩

theorem checked116 : check 4000 c116 = true := by decide

def c117 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 4, .run true 0 3, .run false 1 49, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 4, .run true 0 1, .run false 1 51, .run true 0 1, .box (.plain .none)])⟩

theorem checked117 : check 4000 c117 = true := by decide

def records : List Certified := [
  ⟨102, c102, 4000, checked102⟩,
  ⟨103, c103, 4000, checked103⟩,
  ⟨104, c104, 4000, checked104⟩,
  ⟨105, c105, 4000, checked105⟩,
  ⟨106, c106, 4000, checked106⟩,
  ⟨107, c107, 4000, checked107⟩,
  ⟨108, c108, 4000, checked108⟩,
  ⟨109, c109, 4000, checked109⟩,
  ⟨110, c110, 4000, checked110⟩,
  ⟨111, c111, 4000, checked111⟩,
  ⟨112, c112, 4000, checked112⟩,
  ⟨113, c113, 4000, checked113⟩,
  ⟨114, c114, 4000, checked114⟩,
  ⟨115, c115, 4000, checked115⟩,
  ⟨116, c116, 4000, checked116⟩,
  ⟨117, c117, 4000, checked117⟩]

end PA215.ContractShards.Shard000Part6
