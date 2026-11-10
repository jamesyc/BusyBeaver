import PA215.OriginalRegistry
import PA215.OriginalSelectors
import PA215.ContractPilot
import PA215.Contract4942
import PA215.Contract5084
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.IndexedContracts.Base
open PA215.Census PA215.Contracts
attribute [local irreducible] originalAt

def c4942 : Contract := ⟨none, PA215.Contract4942.initial, PA215.Contract4942.target⟩
theorem checked4942 : check 500 c4942 = true := PA215.Contract4942.accepted

def indexed0 : OriginalCertified ⟨0, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractPilot.c0 4000 (by
    have h : originalAt ⟨0, by decide⟩ = C000.records[0]'(by decide) :=
      originalAt_C000 ⟨0, by decide⟩
    rw [h]
    rfl) PA215.ContractPilot.checked0

def indexed1 : OriginalCertified ⟨1, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractPilot.c1 4000 (by
    have h : originalAt ⟨1, by decide⟩ = C000.records[1]'(by decide) :=
      originalAt_C000 ⟨1, by decide⟩
    rw [h]
    rfl) PA215.ContractPilot.checked1

def indexed2 : OriginalCertified ⟨2, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractPilot.c2 4000 (by
    have h : originalAt ⟨2, by decide⟩ = C000.records[2]'(by decide) :=
      originalAt_C000 ⟨2, by decide⟩
    rw [h]
    rfl) PA215.ContractPilot.checked2

def indexed5 : OriginalCertified ⟨5, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractPilot.c5 4000 (by
    have h : originalAt ⟨5, by decide⟩ = C000.records[5]'(by decide) :=
      originalAt_C000 ⟨5, by decide⟩
    rw [h]
    rfl) PA215.ContractPilot.checked5

def indexed6 : OriginalCertified ⟨6, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractPilot.c6 4000 (by
    have h : originalAt ⟨6, by decide⟩ = C000.records[6]'(by decide) :=
      originalAt_C000 ⟨6, by decide⟩
    rw [h]
    rfl) PA215.ContractPilot.checked6

def indexed7 : OriginalCertified ⟨7, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractPilot.c7 4000 (by
    have h : originalAt ⟨7, by decide⟩ = C000.records[7]'(by decide) :=
      originalAt_C000 ⟨7, by decide⟩
    rw [h]
    rfl) PA215.ContractPilot.checked7

def indexed4942 : OriginalCertified ⟨4942, by decide⟩ :=
  OriginalCertified.ofContract _ c4942 500 (by
    have h : originalAt ⟨4942, by decide⟩ = C038.records[78]'(by decide) :=
      originalAt_C038 ⟨78, by decide⟩
    rw [h]
    rfl) checked4942

def indexed5084 : OriginalCertified ⟨5084, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.Contract5084.contract 4000 (by
    have h : originalAt ⟨5084, by decide⟩ = C039.records[92]'(by decide) :=
      originalAt_C039 ⟨92, by decide⟩
    rw [h]
    rfl) PA215.Contract5084.checked

def indexed5085 : OriginalCertified ⟨5085, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractPilot.c5085 4000 (by
    have h : originalAt ⟨5085, by decide⟩ = C039.records[93]'(by decide) :=
      originalAt_C039 ⟨93, by decide⟩
    rw [h]
    rfl) PA215.ContractPilot.checked5085

def indexed5086 : OriginalCertified ⟨5086, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractPilot.c5086 4000 (by
    have h : originalAt ⟨5086, by decide⟩ = C039.records[94]'(by decide) :=
      originalAt_C039 ⟨94, by decide⟩
    rw [h]
    rfl) PA215.ContractPilot.checked5086

def indexed5087 : OriginalCertified ⟨5087, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractPilot.c5087 4000 (by
    have h : originalAt ⟨5087, by decide⟩ = C039.records[95]'(by decide) :=
      originalAt_C039 ⟨95, by decide⟩
    rw [h]
    rfl) PA215.ContractPilot.checked5087

def indexed5088 : OriginalCertified ⟨5088, by decide⟩ :=
  OriginalCertified.ofContract _ PA215.ContractPilot.c5088 4000 (by
    have h : originalAt ⟨5088, by decide⟩ = C039.records[96]'(by decide) :=
      originalAt_C039 ⟨96, by decide⟩
    rw [h]
    rfl) PA215.ContractPilot.checked5088

def records : OriginalRegistry := [
  ⟨⟨0, by decide⟩, indexed0⟩,
  ⟨⟨1, by decide⟩, indexed1⟩,
  ⟨⟨2, by decide⟩, indexed2⟩,
  ⟨⟨5, by decide⟩, indexed5⟩,
  ⟨⟨6, by decide⟩, indexed6⟩,
  ⟨⟨7, by decide⟩, indexed7⟩,
  ⟨⟨4942, by decide⟩, indexed4942⟩,
  ⟨⟨5084, by decide⟩, indexed5084⟩,
  ⟨⟨5085, by decide⟩, indexed5085⟩,
  ⟨⟨5086, by decide⟩, indexed5086⟩,
  ⟨⟨5087, by decide⟩, indexed5087⟩,
  ⟨⟨5088, by decide⟩, indexed5088⟩]

theorem exact_ids : records.map (fun e => e.1.val) = [0, 1, 2, 5, 6, 7, 4942, 5084, 5085, 5086, 5087, 5088] := rfl
end PA215.IndexedContracts.Base
