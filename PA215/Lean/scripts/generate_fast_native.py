from pathlib import Path
import re,ast,hashlib
root=Path(__file__).resolve().parents[1]
data=(root/'data/pa215.tm').read_bytes();assert hashlib.sha256(data).hexdigest()=='89c0a1007a7a670463fd6edb78f14d1312a1ad9dc949916d39ce7aebbde4e2ac'
labels=ast.literal_eval(re.search(r'def sparseLabels : List Nat := (\[[^\n]+\])',(root/'PA215/NativeTable.lean').read_text()).group(1));assert len(labels)==215
labels=[302 if q==120 else 120 if q==302 else q for q in labels]
rows={}
for line in data.decode().splitlines():
 if line.startswith('#') or not line.strip():continue
 q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n));assert(q,b)not in rows;rows[q,b]=(bool(w),d=='R',254 if n==215 else labels[n])
assert len(rows)==430
boolstr=lambda b:'true' if b else 'false'
def act(t):return f'({boolstr(t[0])}, {boolstr(t[1])}, {t[2]})'
s='''import PA215.Contracts
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.FastNativeTable
open PA215 PA215.Zip PA215.NativeTable PA215.Runtime PA215.Contracts

abbrev FlatAction := Bool × Bool × Nat
abbrev FlatRow := Nat × FlatAction × FlatAction

/-- Constant-folded rows of the exact fixed machine. This literal is checked
against the existing table below, not trusted as a new machine. -/
def literalRows : List FlatRow := [
'''+',\n'.join(f'  ({labels[q]}, {act(rows[q,0])}, {act(rows[q,1])})' for q in range(215))+''']

def actionOf (q : WorkingState) (b : Bool) : FlatAction :=
  let a := row q b
  (a.write, a.right, labelControl a.next)

def semanticRows : List FlatRow :=
  workingStates.map fun q => (label q, actionOf q false, actionOf q true)

/-- All430 actions and215 labels equal the previously accepted definitions. -/
theorem literalRows_eq : literalRows = semanticRows := by decide

def fastMachine (q : Nat) (b : Bool) : Option FlatAction :=
  (literalRows.find? (fun r => r.1 == q)).map fun r => if b then r.2.2 else r.2.1

/-- Extensional equality includes unknown and terminal labels, not merely
working-state samples. -/
theorem machine_eq (q : Nat) (b : Bool) : fastMachine q b = machine q b := by
  unfold fastMachine
  rw [literalRows_eq]
  simp only [semanticRows, List.find?_map, Option.map_map, Function.comp_def]
  cases b <;> rfl

theorem machine_ext : fastMachine = machine := funext fun q => funext fun b => machine_eq q b

def fastCheck (fuel : Nat) (c : Contract) : Bool :=
  (exec fastMachine c.branch (fun s => sMatches s c.target) fuel c.initial false).isSome

/-- Optimized certificate evaluation returns a proof of the ORIGINAL checker
statement through a kernel-checked all-input function equality. -/
theorem fastCheck_eq_check (fuel : Nat) (c : Contract) : fastCheck fuel c = check fuel c := by
  simp only [fastCheck, machine_ext, check]

end PA215.FastNativeTable
'''
p=root/'PA215/FastNativeTable.lean'
if p.exists(): assert p.read_text()==s, 'Refusing differing output'
else: p.write_text(s)
print('Revalidated exact flattened native table; kernel proof is separate.')
