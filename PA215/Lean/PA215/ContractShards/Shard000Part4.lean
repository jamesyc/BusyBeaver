import PA215.CertifiedContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard000Part4
open PA215.Contracts PA215.Runtime

def c70 : Contract := ⟨some (2, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 1 55, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 1 53, .run true 0 1, .box (.plain (.dec 2))])⟩

theorem checked70 : check 4000 c70 = true := by decide

def c71 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 1 52, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 2, .run false 1 51, .run true 0 1, .box (.plain (.inc 8))])⟩

theorem checked71 : check 4000 c71 = true := by decide

def c72 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 2, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 1 55, .run true 0 1, .box (.plain .none)])⟩

theorem checked72 : check 4000 c72 = true := by decide

def c73 : Contract := ⟨some (0, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 53, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 52, .run true 0 1, .box (.plain .none)])⟩

theorem checked73 : check 4000 c73 = true := by decide

def c74 : Contract := ⟨some (0, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 53, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 52, .run true 0 1, .box (.plain (.dec 0))])⟩

theorem checked74 : check 4000 c74 = true := by decide

def c75 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 51, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 50, .run true 0 1, .box (.plain (.inc 2))])⟩

theorem checked75 : check 4000 c75 = true := by decide

def c76 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 50, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 1, .run false 1 53, .run true 0 1, .box (.plain .none)])⟩

theorem checked76 : check 4000 c76 = true := by decide

def c77 : Contract := ⟨some (2, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 52, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 50, .run true 0 1, .box (.plain .none)])⟩

theorem checked77 : check 4000 c77 = true := by decide

def c78 : Contract := ⟨some (2, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 52, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 2, .run true 0 1, .run false 1 50, .run true 0 1, .box (.plain (.dec 2))])⟩

theorem checked78 : check 4000 c78 = true := by decide

def c79 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 2, .run true 0 1, .run false 1 49, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 2, .run true 0 2, .run false 1 48, .run true 0 1, .box (.plain (.inc 5))])⟩

theorem checked79 : check 4000 c79 = true := by decide

def c80 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 2, .run true 0 2, .run false 1 48, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 2, .run true 0 3, .run false 1 47, .run true 0 1, .box (.plain (.inc 8))])⟩

theorem checked80 : check 4000 c80 = true := by decide

def c81 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 2, .run true 0 3, .run false 1 47, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 1 52, .run true 0 1, .box (.plain .none)])⟩

theorem checked81 : check 4000 c81 = true := by decide

def c82 : Contract := ⟨some (8, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 50, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 3, .run false 1 51, .run true 0 1, .box (.plain .none)])⟩

theorem checked82 : check 4000 c82 = true := by decide

def c83 : Contract := ⟨some (8, false), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 50, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 50, .run true 0 1, .box (.plain (.dec 8))])⟩

theorem checked83 : check 4000 c83 = true := by decide

def c84 : Contract := ⟨none, (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 1 49, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain (.inc 5))])⟩

theorem checked84 : check 4000 c84 = true := by decide

def c85 : Contract := ⟨some (8, true), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 1, .run false 1 47, .run true 0 1, .box (.plain .none)]), (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 2, .run true 0 1, .run false 0 1, .run true 0 2, .run false 0 1, .run true 0 3, .run false 1 48, .run true 0 1, .box (.plain .none)])⟩

theorem checked85 : check 4000 c85 = true := by decide

def records : List Certified := [
  ⟨70, c70, 4000, checked70⟩,
  ⟨71, c71, 4000, checked71⟩,
  ⟨72, c72, 4000, checked72⟩,
  ⟨73, c73, 4000, checked73⟩,
  ⟨74, c74, 4000, checked74⟩,
  ⟨75, c75, 4000, checked75⟩,
  ⟨76, c76, 4000, checked76⟩,
  ⟨77, c77, 4000, checked77⟩,
  ⟨78, c78, 4000, checked78⟩,
  ⟨79, c79, 4000, checked79⟩,
  ⟨80, c80, 4000, checked80⟩,
  ⟨81, c81, 4000, checked81⟩,
  ⟨82, c82, 4000, checked82⟩,
  ⟨83, c83, 4000, checked83⟩,
  ⟨84, c84, 4000, checked84⟩,
  ⟨85, c85, 4000, checked85⟩]

end PA215.ContractShards.Shard000Part4
