"""Synchronize the literal table and standalone Challenge with the proof sources."""

import argparse
from hashlib import sha256
from pathlib import Path

PROJECT = Path(__file__).resolve().parents[1]
DIGEST = "b9479f0a460656f93a13d0328a52dfdf410eaae7f1a8861f0b95141a0612c1cf"


def read_rows():
    raw = (PROJECT / "data/zfc-i3-native-380.tm").read_bytes()
    if sha256(raw).hexdigest() != DIGEST:
        raise ValueError("The literal machine bytes changed")
    start, *lines = raw.decode("ascii").splitlines()
    if start != "#! start 0" or len(lines) != 760:
        raise ValueError("Expected 760 rows starting in state 0")
    rows = []
    for index, line in enumerate(lines):
        state, read, write, direction, target = line.split()
        if (int(state), int(read)) != divmod(index, 2):
            raise ValueError(f"Unexpected row order at row {index}")
        if write not in ("0", "1") or direction not in ("L", "R") or not 0 <= int(target) <= 380:
            raise ValueError(f"Invalid row {index}")
        rows.append(4 * int(target) + 2 * int(write) + int(direction == "R"))
    if [index for index, row in enumerate(rows) if row // 4 == 380] != [521]:
        raise ValueError("The unique halt transition must be state 260 on bit 1")
    return rows


def literal(rows):
    lines = [", ".join(map(str, rows[i:i + 12])) for i in range(0, len(rows), 12)]
    return "def literal : Array Nat := #[\n  " + ",\n  ".join(lines) + "\n]\n"


def write_or_check(path, content, check):
    if check:
        if path.read_text() != content:
            raise SystemExit(f"Regenerate {path.relative_to(PROJECT)}")
    else:
        path.write_text(content)


def source_declarations(name):
    path = PROJECT / "ProofSources/I3_380" / name
    return path.read_text().split("@[expose] public section\n", 1)[1].strip()


def principal_statement():
    i3 = source_declarations("Logic/I3.lean").split("\ndef checkBound ", 1)[0]
    history = source_declarations("Simulation.lean").split("\ninductive Terminates", 1)[0]
    sections = [
        history.rstrip() + "\n\nend PalomarI3380",
        source_declarations("Logic/Syntax.lean"),
        source_declarations("Logic/History.lean"),
        source_declarations("Logic/SetFormulas.lean"),
        i3.rstrip() + "\n\nend PalomarI3380.Logic",
        source_declarations("Logic/Target.lean"),
        "namespace PalomarI3380\n\n"
        "theorem exactClaim : Logic.ExactClaim := by\n"
        "  sorry\n\n"
        "end PalomarI3380",
    ]
    return "\n\n".join(sections) + "\n"


def replace_section(text, name, body):
    start = f"-- BEGIN {name}\n"
    stop = f"-- END {name}\n"
    header, rest = text.split(start, 1)
    _, footer = rest.split(stop, 1)
    return header + start + body + stop + footer


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    check = parser.parse_args().check
    rows = read_rows()
    packed = sum(row << (11 * i) for i, row in enumerate(rows))
    table = (
        "/-- Exact rows of `data/zfc-i3-native-380.tm`. -/\n"
        + literal(rows)
        + "\n/-- The same rows packed for kernel evaluation. -/\n"
        + f"def packedLiteral : Nat := 0x{packed:x}\n"
    )
    source = (
        "module\npublic import Std\n@[expose] public section\n\n"
        "namespace PalomarI3380\n\n" + table + "\nend PalomarI3380\n"
    )
    path = PROJECT / "ProofSources/I3_380/Literal.lean"
    write_or_check(path, source, check)

    challenge = PROJECT / "ProofSources/Challenge.lean"
    synchronized = replace_section(challenge.read_text(), "LITERAL ROWS", table)
    synchronized = replace_section(synchronized, "PRINCIPAL STATEMENT", principal_statement())
    write_or_check(challenge, synchronized, check)
    print("Verified the exact 760-row I3-380 literal" if check else "Generated the I3-380 literal")


if __name__ == "__main__":
    main()
