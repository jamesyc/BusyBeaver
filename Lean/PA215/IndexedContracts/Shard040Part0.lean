import PA215.OriginalRegistry
import PA215.OriginalSelectors
import PA215.ContractShards.Shard040Part0
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.IndexedContracts.Shard040Part0
open PA215.Census
attribute [local irreducible] originalAt

def indexed5133 : OriginalCertified ⟨5133, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard040Part0.c5133 4000 (by
    have h : originalAt ⟨5133, by decide⟩ = PA215.ContractShards.Shard040Part0.original5133 :=
      originalAt_C040 ⟨13, by decide⟩
    rw [h]
    exact PA215.ContractShards.Shard040Part0.binding5133) PA215.ContractShards.Shard040Part0.checked5133

def records : OriginalRegistry := [
  ⟨⟨5133, by decide⟩, indexed5133⟩]

theorem exact_ids : records.map (fun e => e.1.val) = [5133] := rfl

end PA215.IndexedContracts.Shard040Part0
