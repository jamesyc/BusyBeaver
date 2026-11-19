"""Write paper/machine-table.tex from the exact rows in data/zf207.tm.

Optional arguments: TABLE OUTPUT, for checking against another table."""

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TABLE = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "data/zf207.tm"
OUTPUT = Path(sys.argv[2]) if len(sys.argv) > 2 else ROOT / "paper/machine-table.tex"
GROUPS, HEIGHT = 5, 42

rows = {}
for line in TABLE.read_text().splitlines():
    q, b, w, d, t = line.split()
    rows[int(q), int(b)] = f"\\texttt{{{w}{d}{t}}}"
states = len(rows) // 2
assert set(rows) == {(q, b) for q in range(states) for b in (0, 1)}
assert states <= GROUPS * HEIGHT

lines = [
    "\\begin{center}",
    "\\scriptsize",
    "\\setlength{\\tabcolsep}{4pt}",
    "\\begin{tabular}{" + "@{\\qquad}".join(["rll"] * GROUPS) + "}",
    "\\toprule",
    " & ".join(["$q$ & $0$ & $1$"] * GROUPS) + " \\\\",
    "\\midrule",
]
for i in range(HEIGHT):
    cells = []
    for g in range(GROUPS):
        q = g * HEIGHT + i
        cells.append(f"{q} & {rows[q, 0]} & {rows[q, 1]}" if q < states else " &  & ")
    lines.append(" & ".join(cells) + " \\\\")
lines += ["\\bottomrule", "\\end{tabular}", "\\end{center}"]
OUTPUT.write_text("\n".join(lines) + "\n")
print(f"Wrote {states} states.")
