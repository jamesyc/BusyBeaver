import PA215.OriginalRegistry
import PA215.OriginalSelectors
import PA215.ContractShards.Shard000Part0
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.IndexedContracts.Shard000Part0
open PA215.Census
attribute [local irreducible] originalAt

def indexed3 : OriginalCertified ⟨3, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c3 4000 (by
    have h : originalAt ⟨3, by decide⟩ = C000.records[3]'(by decide) :=
      originalAt_C000 ⟨3, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked3

def indexed4 : OriginalCertified ⟨4, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c4 4000 (by
    have h : originalAt ⟨4, by decide⟩ = C000.records[4]'(by decide) :=
      originalAt_C000 ⟨4, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked4

def indexed8 : OriginalCertified ⟨8, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c8 4000 (by
    have h : originalAt ⟨8, by decide⟩ = C000.records[8]'(by decide) :=
      originalAt_C000 ⟨8, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked8

def indexed9 : OriginalCertified ⟨9, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c9 4000 (by
    have h : originalAt ⟨9, by decide⟩ = C000.records[9]'(by decide) :=
      originalAt_C000 ⟨9, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked9

def indexed10 : OriginalCertified ⟨10, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c10 4000 (by
    have h : originalAt ⟨10, by decide⟩ = C000.records[10]'(by decide) :=
      originalAt_C000 ⟨10, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked10

def indexed11 : OriginalCertified ⟨11, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c11 4000 (by
    have h : originalAt ⟨11, by decide⟩ = C000.records[11]'(by decide) :=
      originalAt_C000 ⟨11, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked11

def indexed12 : OriginalCertified ⟨12, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c12 4000 (by
    have h : originalAt ⟨12, by decide⟩ = C000.records[12]'(by decide) :=
      originalAt_C000 ⟨12, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked12

def indexed13 : OriginalCertified ⟨13, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c13 4000 (by
    have h : originalAt ⟨13, by decide⟩ = C000.records[13]'(by decide) :=
      originalAt_C000 ⟨13, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked13

def indexed14 : OriginalCertified ⟨14, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c14 4000 (by
    have h : originalAt ⟨14, by decide⟩ = C000.records[14]'(by decide) :=
      originalAt_C000 ⟨14, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked14

def indexed15 : OriginalCertified ⟨15, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c15 4000 (by
    have h : originalAt ⟨15, by decide⟩ = C000.records[15]'(by decide) :=
      originalAt_C000 ⟨15, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked15

def indexed16 : OriginalCertified ⟨16, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c16 4000 (by
    have h : originalAt ⟨16, by decide⟩ = C000.records[16]'(by decide) :=
      originalAt_C000 ⟨16, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked16

def indexed17 : OriginalCertified ⟨17, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c17 4000 (by
    have h : originalAt ⟨17, by decide⟩ = C000.records[17]'(by decide) :=
      originalAt_C000 ⟨17, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked17

def indexed18 : OriginalCertified ⟨18, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c18 4000 (by
    have h : originalAt ⟨18, by decide⟩ = C000.records[18]'(by decide) :=
      originalAt_C000 ⟨18, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked18

def indexed19 : OriginalCertified ⟨19, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c19 4000 (by
    have h : originalAt ⟨19, by decide⟩ = C000.records[19]'(by decide) :=
      originalAt_C000 ⟨19, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked19

def indexed20 : OriginalCertified ⟨20, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c20 4000 (by
    have h : originalAt ⟨20, by decide⟩ = C000.records[20]'(by decide) :=
      originalAt_C000 ⟨20, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked20

def indexed21 : OriginalCertified ⟨21, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractShards.Shard000Part0.c21 4000 (by
    have h : originalAt ⟨21, by decide⟩ = C000.records[21]'(by decide) :=
      originalAt_C000 ⟨21, by decide⟩
    rw [h]
    rfl) PA215.ContractShards.Shard000Part0.checked21

def records : OriginalRegistry := [
  ⟨⟨3, by decide⟩, indexed3⟩,
  ⟨⟨4, by decide⟩, indexed4⟩,
  ⟨⟨8, by decide⟩, indexed8⟩,
  ⟨⟨9, by decide⟩, indexed9⟩,
  ⟨⟨10, by decide⟩, indexed10⟩,
  ⟨⟨11, by decide⟩, indexed11⟩,
  ⟨⟨12, by decide⟩, indexed12⟩,
  ⟨⟨13, by decide⟩, indexed13⟩,
  ⟨⟨14, by decide⟩, indexed14⟩,
  ⟨⟨15, by decide⟩, indexed15⟩,
  ⟨⟨16, by decide⟩, indexed16⟩,
  ⟨⟨17, by decide⟩, indexed17⟩,
  ⟨⟨18, by decide⟩, indexed18⟩,
  ⟨⟨19, by decide⟩, indexed19⟩,
  ⟨⟨20, by decide⟩, indexed20⟩,
  ⟨⟨21, by decide⟩, indexed21⟩]

theorem exact_ids : records.map (fun e => e.1.val) = [3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21] := rfl

end PA215.IndexedContracts.Shard000Part0
