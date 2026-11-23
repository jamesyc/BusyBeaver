"""Synchronize the exact machine data and standalone statement."""

import argparse
from collections import deque
from functools import cache
from hashlib import sha256
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[1]
SUPPORT = PROJECT / "Support" / "I3_334Support"
SOURCES = PROJECT / "ProofSources" / "I3_334"
MACHINE = SOURCES / "Machine"
DIGESTS = {
    334: "50b86af5fde24402b7e2326171deff3b781c66b799f0a9854090f23edf68399d",
    344: "bd2e0cda528a747e2db167d21367786f077c5ea5dca94d7c971d87777f022a8c",
}


def read_rows(states):
    name = "decoder-reference-344.tm" if states == 344 else f"zfc-i3-native-{states}.tm"
    path = PROJECT / "data" / name
    raw = path.read_bytes()
    if sha256(raw).hexdigest() != DIGESTS[states]:
        raise ValueError(f"Machine bytes changed in {path.name}")
    header, *lines = raw.decode("ascii").splitlines()
    if header != "#! start 0" or len(lines) != 2 * states:
        raise ValueError(f"Expected {2 * states} rows starting in state zero")
    rows = []
    for index, line in enumerate(lines):
        q, read, write, direction, target = line.split()
        if (int(q), int(read)) != divmod(index, 2):
            raise ValueError(f"Unexpected row order at row {index}")
        if write not in ("0", "1") or direction not in ("L", "R") or not 0 <= int(target) <= states:
            raise ValueError(f"Invalid row {index}")
        rows.append(4 * int(target) + 2 * int(write) + int(direction == "R"))
    return rows


def array(name, rows):
    chunks = [", ".join(map(str, rows[i:i + 12])) for i in range(0, len(rows), 12)]
    return f"def {name} : Array Nat := #[\n  " + ",\n  ".join(chunks) + "\n]\n"


def packed(rows, width=11):
    return sum(row << (width * i) for i, row in enumerate(rows))


def declarations(path):
    return path.read_text().split("@[expose] public section\n", 1)[1].strip() + "\n"


def shared(path, before=None, ending=""):
    body = declarations(SUPPORT / path)
    if before:
        body = body.split(before, 1)[0].rstrip() + "\n" + ending
    return body


def extract(body, start, end):
    return body[body.index(start):].split(end, 1)[0].rstrip()


def sync(path, content, check):
    if check:
        if path.read_text() != content:
            raise SystemExit(f"Regenerate {path.relative_to(PROJECT)}")
    else:
        path.write_text(content)


REGISTER_INC = [36, 55, 90, 85, 72, 73, 86, 69, 121, 112, 138]
REGISTER_DEC = [32, 23, 75, 67, 89, 71, 54, 39, 56, 41, 168]
REFERENCE_EXITS = set(REGISTER_INC + REGISTER_DEC + [7, 8, 9, 24, 33, 344])


def decoder_shape(rows):
    # Store one DAG height and two prefix bounds per reference control.
    # Lean verifies every local implication against the literal reference rows.
    @cache
    def height(q):
        if q in REFERENCE_EXITS:
            return 0
        return 1 + max(height(row // 4) for row in rows[2*q:2*q+2])

    bounds = {}
    pending = deque([(16, 0, 0)])
    seen = set()
    while pending:
        q, zeros, ones = pending.popleft()
        if q in REFERENCE_EXITS or (q, zeros, ones) in seen:
            continue
        seen.add((q, zeros, ones))
        old_zeros, old_ones = bounds.get(q, (0, 4))
        bounds[q] = max(zeros, old_zeros), min(ones, old_ones)
        for bit, row in enumerate(rows[2*q:2*q+2]):
            pending.append((row // 4, 0 if bit else zeros + 1, min(4, ones + bit)))
    return [
        height(q) + (bounds[q][0] << 7) + (bounds[q][1] << 10) if q in bounds else 0
        for q in range(344)
    ]


def table_tex(rows):
    """Render the two transitions per state in four side-by-side groups."""
    states = len(rows) // 2
    groups = 4
    height = (states + groups - 1) // groups

    def action(row):
        target, flags = divmod(row, 4)
        write, right = divmod(flags, 2)
        direction = "R" if right else "L"
        return f"\\texttt{{{write}{direction}{target:03d}}}"

    end = r" \\"
    head = " & ".join(["$q$ & $0$ & $1$"] * groups) + end
    lines = [r"\begingroup", r"\small", r"\setlength{\tabcolsep}{3pt}",
             r"\begin{longtable}{" + r"@{\qquad}".join(["rll"] * groups) + "}",
             r"\toprule", head, r"\midrule", r"\endhead"]
    for offset in range(height):
        cells = []
        for group in range(groups):
            q = group * height + offset
            cells.extend([str(q), action(rows[2*q]), action(rows[2*q+1])]
                         if q < states else ["", "", ""])
        lines.append(" & ".join(cells) + end)
    return "\n".join(lines + [r"\bottomrule", r"\end{longtable}", r"\endgroup", ""])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    check = parser.parse_args().check
    rows = read_rows(334)
    sync(PROJECT / "paper" / "machine-table.tex", table_tex(rows), check)
    halt_rows = [(i, row) for i, row in enumerate(rows) if row // 4 == 334]
    if halt_rows != [(379, 4 * 334 + 3)]:
        raise ValueError("Unexpected I3-334 halt transition")
    reachable = {0}
    pending = [0]
    for q in pending:
        for row in rows[2 * q:2 * q + 2]:
            target = row // 4
            if target < 334 and target not in reachable:
                reachable.add(target)
                pending.append(target)
    if len(reachable) != 334:
        raise ValueError("Some working labels are disconnected")

    header = "module\npublic import Std\n@[expose] public section\n\n"
    literal = (
        "namespace PalomarI3334\n\n"
        "/-- Exact rows of `data/zfc-i3-native-334.tm`. -/\n" + array("literal", rows)
        + f"\ndef packedLiteral : Nat := 0x{packed(rows):x}\n"
        + "\ndef machine : PalomarI3380.Machine := ⟨334, packedLiteral⟩\n\nend PalomarI3334\n"
    )
    machine_header = header.replace("public import Std", "public import I3_334Support.Machine")
    sync(SOURCES / "Literal.lean", machine_header + literal, check)
    reference_rows = read_rows(344)
    shape = decoder_shape(reference_rows)
    linked = machine_header + (
        "namespace PalomarI3334\n\n"
        "/-- Decoder reference table, numbered by breadth-first search. -/\n"
        f"def decoderReference : PalomarI3380.Machine := ⟨344, 0x{packed(reference_rows):x}⟩\n\n"
        f"def referenceIncPorts : Array Nat := #[{', '.join(map(str, REGISTER_INC))}]\n"
        f"def referenceDecPorts : Array Nat := #[{', '.join(map(str, REGISTER_DEC))}]\n"
        f"def referenceDecoderShape : Nat := 0x{packed(shape, 13):x}\n"
        "end PalomarI3334\n"
    )
    sync(MACHINE / "ReferenceData.lean", linked, check)

    loader_exit = extract(declarations(SUPPORT / "Machine/Loader.lean"), "def loaderExit ", "\nend PalomarI3380")
    bindings = declarations(MACHINE / "Bindings.lean")
    startup = declarations(MACHINE / "Startup.lean")
    binding_claim = extract(bindings, "theorem literal_binding ", " := by")
    startup_claim = extract(startup, "theorem literal_startup ", " := by")
    decoder_entry = extract(startup, "def decoderEntry ", "\nprivate theorem")
    challenge = header + "/-! Standalone statement for the exact I3-334 machine. -/\n\n"
    challenge += "\n".join((
        shared("Machine.lean", "\ntheorem run_add", "\nend PalomarI3380\n"),
        shared("Machine/Simulation.lean", "\ninductive Terminates", "\nend PalomarI3380\n"),
        shared("Logic/Syntax.lean"),
        shared("Logic/History.lean", "\nend InternalSets",
               "\nend InternalSets\nend PalomarI3380.Logic.Internal\n"),
        shared("Logic/SetFormulas.lean"),
        shared("Logic/I3.lean", "\ndef checkBound ", "\nend PalomarI3380.Logic\n"),
        shared("Logic/Target.lean"),
        f"namespace PalomarI3380\n\n{loader_exit}\n\nend PalomarI3380\n",
        literal,
        declarations(SOURCES / "Statement.lean"),
        "namespace PalomarI3334\n\nopen PalomarI3380\n\n"
        f"{decoder_entry}\n\n{binding_claim} := by\n  sorry\n\n"
        f"{startup_claim} := by\n  sorry\n\n"
        "theorem exactClaim : ExactClaim := by\n"
        "  sorry\n\nend PalomarI3334\n",
    ))
    sync(SOURCES / "Challenge.lean", challenge, check)
    print("Verified the exact 668-row I3-334 literal" if check else "Synchronized I3-334 declarations")


if __name__ == "__main__":
    main()
