import pathlib,re,json,hashlib
r=pathlib.Path(__file__).resolve().parents[1]; out=r/'PA215/Source/AXTypedBindings'
ps=sorted((r/'PA215/Source/AXBindings').glob('B*.lean'))+sorted((r/'PA215/Source').glob('AXHead3Bindings[012].lean'))
ledger=[]; blocks={}; aliases={}; modules=[]
for p in ps:
 src=p.read_text(); mod=str(p.relative_to(r)).removesuffix('.lean').replace('/','.')
 ns='AXHead3' if 'AXHead3Bindings' in p.name else 'AXAll'; target=p.stem
 pairs=re.findall(r'private theorem (\w+)\s*:(.*?) :=',src,re.S)
 selected=[(n,t.strip()) for n,t in pairs if n.startswith('bound') or n.endswith('_i0')]
 text=f'import {mod}\nimport PA215.Source.AXTypedPlan\nimport PA215.Source.ExistingPrivateBound\nnamespace PA215.Source.AXModelBounds\n'
 for n,t in selected:
  assert n not in aliases,n
  orig=f'_private.{mod}.0.PA215.Source.{ns}.{n}'
  text+=f'theorem {n} : {t} :=\n  existingPrivateBound% \"{mod}\" \"PA215.Source.{ns}.{n}\"\n'
  aliases[n]=orig
  ledger.append(dict(export=f'PA215.Source.AXModelBounds.{n}',original=orig,original_module=mod,original_repository_path='BB/Lean/'+str(p.relative_to(r)),original_source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),type=t,type_sha256=hashlib.sha256(t.encode()).hexdigest()))
 for match in re.finditer(r'theorem block(\d+)\s*:\s*AXMacro.Realizes exactSites \.(\w+) (\d+) (\d+)\s*:=\s*(.*?)(?=\n(?:private theorem|theorem|def|#print|end)|\Z)',src,re.S):
  no,op,start,end,body=match.groups();start=int(start);end=int(end)
  if 'AXHead3.block' in body: continue
  assert start not in blocks
  args=re.findall(r'\b(?:bound\d+_\w+|row\d+_i0)\b',body)
  assert all(a in aliases for a in args),(start,args)
  base=start-25 if op=='push' else start-20 if op=='cons' else start
  text+=f'theorem block{start} : AXTyped.Bound .{op} {start} {end} :=\n  AXTyped.Bound.{op} {base} (by decide) '+ ' '.join(args)+'\n'
  blocks[start]=dict(start=start,stop=end,op=op,bindings=args,module=f'PA215.Source.AXTypedBindings.{target}')
 text+='end PA215.Source.AXModelBounds\n'
 (out/(target+'.lean')).write_text(text);modules.append(f'PA215.Source.AXTypedBindings.{target}')
bs=sorted(blocks.values(),key=lambda x:x['start']);assert len(bs)==276,len(bs)
assert bs[0]['start']==25 and bs[-1]['stop']==3769
assert all(a['stop']==b['start'] for a,b in zip(bs,bs[1:]))
t=''.join('import '+m+'\n' for m in modules)+'import PA215.Source.AXMacroProgram\nnamespace PA215.Source.AXModelBounds\nset_option maxRecDepth 100000\ntheorem full_plan : AXTyped.Plan 25 3769 AXMacro.program :=\n  '
t+=''.join(f'AXTyped.Plan.cons block{x["start"]} (' for x in bs)+'AXTyped.Plan.nil 3769'+')'*len(bs)+'\n#print axioms full_plan\nend PA215.Source.AXModelBounds\n'
(r/'PA215/Source/AXTypedFullPlan.lean').write_text(t)
(r/'data/ax_typed_exports.json').write_text(json.dumps(dict(scope='Exact finite binding aliases only; no model execution inference',aliases=ledger,blocks=bs,macro_count=len(bs),primitive_leaf_count=3769-25),indent=2)+'\n')
print(len(ledger),'aliases',len(bs),'blocks',len(modules),'modules')
