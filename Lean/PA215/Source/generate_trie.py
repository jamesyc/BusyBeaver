"""Untrusted literal compact trie; Lean checks flatten equality to pinned source."""
import json,hashlib
from pathlib import Path
root=Path(__file__).resolve().parents[2]
p=root/'data/candidate_source.json'
b=p.read_bytes()
assert hashlib.sha256(b).hexdigest()=='e4814e0d968b86a8cd4cf2df2623b2f5558a7a61bf43b99f798c73156eb91c45'
data=dict(json.loads(b))
def node(p):
 if p in data:
  tag,arg=data[p]
  op={'EInc':'.inc','EDecnz':'.dec','EBreak':'.breakTo','EContinue':'.continueTo','EHalt':'.halt'}[tag]
  return '(.leaf ('+op+(' '+str(arg) if arg is not None else '')+'))'
 assert any(q.startswith(p) for q in data),'incomplete tree'
 return '(.node '+node(p+'0')+' '+node(p+'1')+')'
s='''import PA215.Source.PathTrie
import PA215.Source.ExactSource
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA215.Source.PathTrie

def exactTrie : Tree := '''+node('')+'''

/-- Full literal transcription check, not a trusted generator assertion. -/
theorem exact_flatten : flatten exactTrie = exactSites.toList := by rfl

theorem exact_lookup (p : Path) : lookup exactTrie p = locate exactSites p := by
  rw [lookup_eq,exact_flatten]
  rfl
#print axioms exact_flatten
#print axioms exact_lookup
end PA215.Source.PathTrie
'''
(root/'PA215/Source/ExactTrie.lean').write_text(s)
