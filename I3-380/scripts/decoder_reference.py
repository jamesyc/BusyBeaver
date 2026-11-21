"""Pack the named reference table and its state map without generating proofs."""

import argparse
from collections import deque
from functools import cache
import json
from pathlib import Path

from literal import PROJECT, read_rows, write_or_check


def load_table(path):
    header, *rows = path.read_text().splitlines()
    start = header.removeprefix("#! start ")
    table = {}
    for row in rows:
        source, read, write, direction, target = row.split()
        table[source, int(read)] = (int(write), direction, target)
    table.setdefault(("1.inc", 1), (1, "R", "1.inc"))
    return start, table


def number_states(start, table):
    queue = deque([start])
    numbers = {start: 0}
    while queue:
        source = queue.popleft()
        for bit in (0, 1):
            target = table[source, bit][2]
            if target != "halt" and target not in numbers:
                numbers[target] = len(numbers)
                queue.append(target)
    if len(table) != 2 * len(numbers):
        raise ValueError("Named table contains unreachable or incomplete states")
    numbers["halt"] = len(numbers)
    return numbers


def packed_row(numbers, row):
    write, direction, target = row
    return 4 * numbers[target] + 2 * write + int(direction == "R")


def extract(reference, physical, link):
    ref_start, ref_table = load_table(reference)
    phys_start, phys_table = load_table(physical)
    ref_ids = number_states(ref_start, ref_table)
    phys_ids = number_states(phys_start, phys_table)
    observed = [
        packed_row(phys_ids, phys_table[q, b])
        for q in phys_ids if q != "halt"
        for b in (0, 1)
    ]
    if observed != read_rows():
        raise ValueError("Physical named table does not give the exact literal table")
    aliases = {item["q"]: item["p"] for item in json.loads(link.read_text())["merges"]}
    decoders = {q for q, b in ref_table if not q[0].isdigit()}
    masks = {q: 0 for q in ref_ids}
    masks["main().0"] = 3
    for (q, read), (write, direction, target) in ref_table.items():
        if q in decoders and target in decoders:
            if write != read or direction != "R":
                raise ValueError("Expected internal reference decoder rows to move right")
            masks[target] |= 1 << read
    lines = []
    for q in ref_ids:
        row = [ref_ids[q], phys_ids[aliases.get(q, q)], masks[q]]
        if q != "halt":
            row += [packed_row(ref_ids, ref_table[q, b]) for b in (0, 1)]
        lines.append("\t".join(map(str, row)) + "\t" + q)
    return "\n".join(lines) + "\n"


def pack(values, width):
    if any(not 0 <= value < 1 << width for value in values):
        raise ValueError(f"A packed value is outside {width} bits")
    return sum(value << (width * i) for i, value in enumerate(values))


def decoder_bounds(fields):
    """Derive rank and prefix facts for the unmerged reference decoder."""
    decoders = {row[0] for row in fields[:-1] if row[2]}
    root = 7

    @cache
    def successors(q):
        return [(read, row // 4) for read, row in enumerate(fields[q][3:])]

    @cache
    def height(q):
        if q not in decoders:
            return 0
        return 1 + max(height(t) for _, t in successors(q))

    zeros = {root: 0}
    has_one = {root: False}
    for q in sorted(decoders, key=height, reverse=True):
        for read, target in successors(q):
            if target in decoders:
                next_zeros = 0 if read else zeros[q] + 1
                next_one = bool(read) or has_one[q]
                zeros[target] = max(zeros.get(target, 0), next_zeros)
                has_one[target] = has_one.get(target, True) and next_one
    return [
        pack([height(q), zeros.get(q, 0), int(has_one.get(q, False))], 6)
        for q in range(len(fields))
    ]


def lean_source(table):
    parsed = [line.split("\t") for line in table.splitlines()]
    fields = [[int(value) for value in line[:-1]] for line in parsed]
    if [row[0] for row in fields] != list(range(395)):
        raise ValueError("Expected 394 reference working states and one halt state")
    if any(len(row) != 5 for row in fields[:-1]) or len(fields[-1]) != 3:
        raise ValueError("Expected two transition rows at every working state")
    ref_rows = pack([value for row in fields[:-1] for value in row[3:]], 11)
    state_map = pack([row[1] for row in fields], 9)
    entry_masks = pack([row[2] for row in fields], 2)
    bounds = pack(decoder_bounds(fields), 18)
    return (
        "module\nimport Std\n@[expose] public section\n\n"
        "namespace PalomarI3380.DecoderData\n\n"
        "/-! Packed reference rows, state map, and entry masks from "
        "`data/decoder-reference.tsv`. -/\n\n"
        f"def referenceRows : Nat := 0x{ref_rows:x}\n"
        f"def stateMap : Nat := 0x{state_map:x}\n"
        f"def entryMasks : Nat := 0x{entry_masks:x}\n"
        f"def bounds : Nat := 0x{bounds:x}\n"
        "\nend PalomarI3380.DecoderData\n"
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--named-tables", nargs=3, type=Path,
                        metavar=("REFERENCE", "PHYSICAL", "LINK"))
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data_path = PROJECT / "data/decoder-reference.tsv"
    if args.named_tables:
        write_or_check(data_path, extract(*args.named_tables), args.check)
    lean = lean_source(data_path.read_text())
    write_or_check(PROJECT / "ProofSources/I3_380/DecoderData.lean", lean, args.check)


if __name__ == "__main__":
    main()
