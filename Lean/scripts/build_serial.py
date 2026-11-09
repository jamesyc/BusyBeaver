#!/usr/bin/env python3
"""Build the imported core closure serially; never sweep unimported draft files.

This controls scheduling only. Lake and Lean still check every target normally.
External Std/Lean imports are supplied by the pinned toolchain.
"""
import argparse
from pathlib import Path
import re
import subprocess
from check_source_hygiene import without_comments

NAME = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')

def build_order(root, target='PA211', package_roots=None):
    roots = {'PA215': root, 'PA213': root, 'PA211': root, 'TreeSite': root,
             **(package_roots or {})}
    # The frozen publication uses flat User211 module names. Keep its bytes
    # unchanged and resolve each module in the package that owns its source.
    for base in set(roots.values()):
        roots.update({p.stem: base for p in base.glob('User211*.lean')})
    def local(name):
        return name.split('.')[0] in roots
    states, order = {}, []
    def visit(name):
        if not NAME.fullmatch(name) or not local(name):
            raise ValueError(f'Invalid core target: {name}')
        if states.get(name) == 1:
            raise ValueError(f'Import cycle at {name}')
        if states.get(name) == 2:
            return
        source = roots[name.split('.')[0]].joinpath(*name.split('.')).with_suffix('.lean')
        if not source.is_file():
            raise ValueError(f'Missing imported source: {name}')
        states[name] = 1
        for line in without_comments(source.read_text()).splitlines():
            words = line.split()
            while words and words[0] in ('public', 'private', 'meta'):
                words = words[1:]
            if words[:1] == ['import']:
                imports = words[1:]
                if imports[:1] == ['all']:
                    imports = imports[1:]
                for dep in imports:
                    if not NAME.fullmatch(dep):
                        raise ValueError(f'Unsupported import syntax in {name}: {line}')
                    if local(dep):
                        visit(dep)
        states[name] = 2
        order.append(name)
    visit(target)
    return order

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--target')
    p.add_argument('--metamathematics', action='store_true',
                   help='Also schedule local metamathematics and pinned Foundation imports')
    p.add_argument('--list', action='store_true', help='Print plan without building')
    args = p.parse_args()
    root = Path(__file__).resolve().parents[1]
    cwd = root / 'metamathematics' if args.metamathematics else root
    extra = {}
    if args.metamathematics:
        extra = {'PA215PA': cwd, 'PA213PA': cwd, 'PA211PA': cwd,
                 'Foundation': cwd / '.lake/packages/Foundation'}
    target = args.target or ('PA211PA' if args.metamathematics else 'PA211')
    try:
        order = build_order(root, target, extra)
    except ValueError as e:
        raise SystemExit(str(e))
    if args.list:
        print('\n'.join(order))
        return
    for i, name in enumerate(order, 1):
        print(f'[{i}/{len(order)}] serial target {name}', flush=True)
        subprocess.run(['lake', 'build', '+' + name], cwd=cwd, check=True)
    print(f'PASS: {len(order)} imported scheduled modules built serially.')

if __name__ == '__main__':
    main()
