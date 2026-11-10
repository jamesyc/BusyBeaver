#!/usr/bin/env python3
"""Conservative source lint, not a replacement for a theorem axiom audit."""
from pathlib import Path
import re
import sys

def without_comments(text):
    """Mask nested Lean comments, preserving newlines and string contents.

    This is lexical lint only: escaped strings are retained, not interpreted.
    A comment opener inside a string must never hide subsequent Lean code.
    """
    out = []
    i, depth, quoted = 0, 0, False
    while i < len(text):
        c = text[i]
        pair = text[i:i + 2]
        if depth:
            if pair == '/-':
                depth += 1
                out.extend('  ')
                i += 2
            elif pair == '-/':
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if c == '\n' else ' ')
                i += 1
        elif quoted:
            out.append(c)
            i += 1
            if c == '\\' and i < len(text):
                out.append(text[i])
                i += 1
            elif c == '"':
                quoted = False
        elif pair == '/-':
            depth = 1
            out.extend('  ')
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            out.extend(' ' * (end - i))
            i = end
        else:
            out.append(c)
            quoted = c == '"'
            i += 1
    return ''.join(out)


def main():
    root = Path(__file__).resolve().parents[1]
    forbidden = re.compile(r'\b(sorry|admit|native_decide|native_eval|axiom)\b')
    failed = []
    sources = []
    for package in (root / 'PA215', root / 'PA213', root / 'PA211',
                    root / 'metamathematics/PA215PA', root / 'metamathematics/PA213PA',
                    root / 'metamathematics/PA211PA'):
        sources.extend(sorted(package.rglob('*.lean')))
    sources.extend(root.glob('User211*.lean'))
    sources.extend((root / 'metamathematics').glob('User211*.lean'))
    sources.extend([root / 'TreeSite.lean', root / 'PA211.lean',
                    root / 'metamathematics/PA211PA.lean'])
    for source in sources:
        for line_no, line in enumerate(without_comments(source.read_text()).splitlines(), 1):
            if forbidden.search(line):
                failed.append(f'{source.relative_to(root)}:{line_no}: {line}')
    if failed:
        print('\n'.join(failed), file=sys.stderr)
        return 1
    print('Project source lint passed; separately inspect theorem axioms.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
