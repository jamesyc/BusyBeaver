import User211Source
namespace PA211.UserCandidate.Source
open PA215.Source PA215.Source.PathTrie
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

def blockCheck (base count : Nat) : Bool := decide
  (((sites.toList.drop base).take count).map (PA213.FastResolve.resolveTree trie)=
   ((PA213.SourceProgram.codes.toList.drop base).take count).map some)

theorem block_sound {base count i : Nat} (h : blockCheck base count=true)
    (lo : base≤i) (hi : i<base+count) :
    (sites[i]?).bind (PA213.FastResolve.resolveTree trie)=PA213.SourceProgram.codes[i]? := by
  have he := of_decide_eq_true h
  have hh := congrArg (fun xs => xs[i-base]?) he
  have hb : i-base<count := by omega
  simp only [List.getElem?_map,List.getElem?_take_of_lt hb,List.getElem?_drop,
    Nat.add_sub_of_le lo,Array.getElem?_toList] at hh
  cases hs : sites[i]? <;> cases hc : PA213.SourceProgram.codes[i]? <;> simp_all

theorem all_paths_short : sites.toList.all (fun s=>decide (s.path.length ≤ 64))=true := by decide +kernel
#print axioms block_sound
#print axioms all_paths_short
end PA211.UserCandidate.Source
