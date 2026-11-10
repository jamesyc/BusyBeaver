#!/usr/bin/env python3
"""Generate proof scripts, not trusted certificates, for original/source joins.
Every emitted literal lookup is proved by rfl; every frame check by decide.
Usage: SOURCE.json ORIGINAL.json.gz OUTPUT_DIR FIRST LAST
"""
import gzip
import hashlib
import json
import pathlib
import sys

source, census, out, first, last = sys.argv[1:]
source, census, out = pathlib.Path(source), pathlib.Path(census), pathlib.Path(out)
assert hashlib.sha256(source.read_bytes()).hexdigest() == "e4814e0d968b86a8cd4cf2df2623b2f5558a7a61bf43b99f798c73156eb91c45"
assert hashlib.sha256(census.read_bytes()).hexdigest() == "4dd3e8b97540fe0420de80db200ba4e13dc3bf98e63a159b44fb1afae6769245"
source = json.loads(source.read_text())
records = json.loads(gzip.decompress(census.read_bytes()))
assert len(source) == 3947 and len(records) == 5134
first, last = int(first), int(last)
assert 1 <= first <= last <= 40
out.mkdir(parents=True, exist_ok=True)
for j in range(first, last + 1):
    k = f"{j:03d}"
    rs = records[128*j:128*(j+1)]
    text = f"import PA215.Source.ContractJoinPilot\nimport PA215.Census.C{k}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\nnamespace PA215.Source.CensusJoin.J{k}\n"
    for i in sorted({r["site_index"] for r in rs}):
        path, (tag, arg) = source[i]
        path = "[" + ",".join("true" if b == "1" else "false" for b in path) + "]"
        op = {"EInc": "inc", "EDecnz": "dec", "EBreak": "breakTo", "EContinue": "continueTo", "EHalt": "halt"}[tag]
        op = "." + op + (" " + str(arg) if arg is not None else "")
        text += f"private def site{i} : Site := ⟨{path},{op}⟩\nprivate theorem lookup{i} : exactSites[{i}]? = some site{i} := by rfl\n"
    for i, r in enumerate(rs):
        idx = r["site_index"]
        text += f"private def raw{i} := PA215.Census.C{k}.records[{i}]'(by decide)\nprivate theorem row{i} : recordAgrees raw{i} = true := by\n  unfold recordAgrees\n  rw [show raw{i}.siteIndex = {idx} from rfl,lookup{idx}]\n  decide\n"
    text += f"private theorem enumeration : PA215.Census.C{k}.records.toList = [" + ",".join(f"raw{i}" for i in range(len(rs))) + "] := by rfl\n"
    text += f"theorem checked : PA215.Census.C{k}.records.toList.all recordAgrees = true := by\n  rw [enumeration]\n  simp only [List.all_cons,List.all_nil," + ",".join(f"row{i}" for i in range(len(rs))) + f",Bool.and_self]\n#print axioms checked\nend PA215.Source.CensusJoin.J{k}\n"
    (out / f"J{k}.lean").write_text(text)
