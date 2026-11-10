import PA215.OriginalRegistry
import PA215.CertificateSchedule
import PA215.IndexedContracts.Base
import PA215.IndexedContracts.Terminal
import PA215.IndexedContracts.Shard000
import PA215.IndexedContracts.Shard001
import PA215.IndexedContracts.Shard002
import PA215.IndexedContracts.Shard003
import PA215.IndexedContracts.Shard004
import PA215.IndexedContracts.Shard005
import PA215.IndexedContracts.Shard006
import PA215.IndexedContracts.Shard007
import PA215.IndexedContracts.Shard008
import PA215.IndexedContracts.Shard009
import PA215.IndexedContracts.Shard010
import PA215.IndexedContracts.Shard011
import PA215.IndexedContracts.Shard012
import PA215.IndexedContracts.Shard013
import PA215.IndexedContracts.Shard014
import PA215.IndexedContracts.Shard015
import PA215.IndexedContracts.Shard016
import PA215.IndexedContracts.Shard017
import PA215.IndexedContracts.Shard018
import PA215.IndexedContracts.Shard019
import PA215.IndexedContracts.Shard020
import PA215.IndexedContracts.Shard021
import PA215.IndexedContracts.Shard022
import PA215.IndexedContracts.Shard023
import PA215.IndexedContracts.Shard024
import PA215.IndexedContracts.Shard025
import PA215.IndexedContracts.Shard026
import PA215.IndexedContracts.Shard027
import PA215.IndexedContracts.Shard028
import PA215.IndexedContracts.Shard029
import PA215.IndexedContracts.Shard030
import PA215.IndexedContracts.Shard031
import PA215.IndexedContracts.Shard032
import PA215.IndexedContracts.Shard033
import PA215.IndexedContracts.Shard034
import PA215.IndexedContracts.Shard035
import PA215.IndexedContracts.Shard036
import PA215.IndexedContracts.Shard037
import PA215.IndexedContracts.Shard038
import PA215.IndexedContracts.Shard039
import PA215.IndexedContracts.Shard040
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace PA215.AllRuntimeCertificates
open PA215.Census

def records : OriginalRegistry :=
  PA215.IndexedContracts.Base.records ++
  PA215.IndexedContracts.Shard000.records ++
  PA215.IndexedContracts.Shard001.records ++
  PA215.IndexedContracts.Shard002.records ++
  PA215.IndexedContracts.Shard003.records ++
  PA215.IndexedContracts.Shard004.records ++
  PA215.IndexedContracts.Shard005.records ++
  PA215.IndexedContracts.Shard006.records ++
  PA215.IndexedContracts.Shard007.records ++
  PA215.IndexedContracts.Shard008.records ++
  PA215.IndexedContracts.Shard009.records ++
  PA215.IndexedContracts.Shard010.records ++
  PA215.IndexedContracts.Shard011.records ++
  PA215.IndexedContracts.Shard012.records ++
  PA215.IndexedContracts.Shard013.records ++
  PA215.IndexedContracts.Shard014.records ++
  PA215.IndexedContracts.Shard015.records ++
  PA215.IndexedContracts.Shard016.records ++
  PA215.IndexedContracts.Shard017.records ++
  PA215.IndexedContracts.Shard018.records ++
  PA215.IndexedContracts.Shard019.records ++
  PA215.IndexedContracts.Shard020.records ++
  PA215.IndexedContracts.Shard021.records ++
  PA215.IndexedContracts.Shard022.records ++
  PA215.IndexedContracts.Shard023.records ++
  PA215.IndexedContracts.Shard024.records ++
  PA215.IndexedContracts.Shard025.records ++
  PA215.IndexedContracts.Shard026.records ++
  PA215.IndexedContracts.Shard027.records ++
  PA215.IndexedContracts.Shard028.records ++
  PA215.IndexedContracts.Shard029.records ++
  PA215.IndexedContracts.Shard030.records ++
  PA215.IndexedContracts.Shard031.records ++
  PA215.IndexedContracts.Shard032.records ++
  PA215.IndexedContracts.Shard033.records ++
  PA215.IndexedContracts.Shard034.records ++
  PA215.IndexedContracts.Shard035.records ++
  PA215.IndexedContracts.Shard036.records ++
  PA215.IndexedContracts.Shard037.records ++
  PA215.IndexedContracts.Shard038.records ++
  PA215.IndexedContracts.Shard039.records ++
  PA215.IndexedContracts.Shard040.records

theorem records_ids : records.map (fun e => e.1.val) = PA215.CertificateSchedule.plannedIds := by
  simp only [records, List.map_append, PA215.IndexedContracts.Base.exact_ids, PA215.IndexedContracts.Shard000.exact_ids, PA215.IndexedContracts.Shard001.exact_ids, PA215.IndexedContracts.Shard002.exact_ids, PA215.IndexedContracts.Shard003.exact_ids, PA215.IndexedContracts.Shard004.exact_ids, PA215.IndexedContracts.Shard005.exact_ids, PA215.IndexedContracts.Shard006.exact_ids, PA215.IndexedContracts.Shard007.exact_ids, PA215.IndexedContracts.Shard008.exact_ids, PA215.IndexedContracts.Shard009.exact_ids, PA215.IndexedContracts.Shard010.exact_ids, PA215.IndexedContracts.Shard011.exact_ids, PA215.IndexedContracts.Shard012.exact_ids, PA215.IndexedContracts.Shard013.exact_ids, PA215.IndexedContracts.Shard014.exact_ids, PA215.IndexedContracts.Shard015.exact_ids, PA215.IndexedContracts.Shard016.exact_ids, PA215.IndexedContracts.Shard017.exact_ids, PA215.IndexedContracts.Shard018.exact_ids, PA215.IndexedContracts.Shard019.exact_ids, PA215.IndexedContracts.Shard020.exact_ids, PA215.IndexedContracts.Shard021.exact_ids, PA215.IndexedContracts.Shard022.exact_ids, PA215.IndexedContracts.Shard023.exact_ids, PA215.IndexedContracts.Shard024.exact_ids, PA215.IndexedContracts.Shard025.exact_ids, PA215.IndexedContracts.Shard026.exact_ids, PA215.IndexedContracts.Shard027.exact_ids, PA215.IndexedContracts.Shard028.exact_ids, PA215.IndexedContracts.Shard029.exact_ids, PA215.IndexedContracts.Shard030.exact_ids, PA215.IndexedContracts.Shard031.exact_ids, PA215.IndexedContracts.Shard032.exact_ids, PA215.IndexedContracts.Shard033.exact_ids, PA215.IndexedContracts.Shard034.exact_ids, PA215.IndexedContracts.Shard035.exact_ids, PA215.IndexedContracts.Shard036.exact_ids, PA215.IndexedContracts.Shard037.exact_ids, PA215.IndexedContracts.Shard038.exact_ids, PA215.IndexedContracts.Shard039.exact_ids, PA215.IndexedContracts.Shard040.exact_ids]
  all_goals rfl

theorem records_count : records.length = 5133 := by
  have h := congrArg List.length records_ids
  simpa only [List.length_map, PA215.CertificateSchedule.planned_count] using h

/-- Every original nonterminal obligation has an exact indexed kernel certificate. -/
theorem nonterminalCoverage : ∀ j : Fin 5134, j.val ≠ 5114 → Nonempty (OriginalCertified j) := by
  intro j hj
  have hm : j.val ∈ records.map (fun e => e.1.val) := by
    rw [records_ids, PA215.CertificateSchedule.mem_plannedIds]
    exact ⟨j.isLt, hj⟩
  obtain ⟨entry, _, he⟩ := List.mem_map.mp hm
  have hindex : entry.1 = j := Fin.ext he
  exact ⟨hindex ▸ entry.2⟩

def terminalCertificate : OriginalHaltCertified ⟨5114, by decide⟩ :=
  PA215.IndexedContracts.terminal5114

end PA215.AllRuntimeCertificates
