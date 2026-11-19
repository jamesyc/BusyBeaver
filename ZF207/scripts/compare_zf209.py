"""Finite comparison of the ZF209 and ZF207 decoders. Run with Python 3.8 or later.

The Lean proof does not depend on this check. Run from the repository checkout:
    python3 scripts/compare_zf209.py
"""

from hashlib import sha256
from pathlib import Path


PACKAGE = Path(__file__).resolve().parent.parent
PATHS = {207: PACKAGE / "data/zf207.tm", 209: PACKAGE.parent / "ZF209/data/zf209.tm"}
ENTRY = 74
OMITTED = {126, 178}
OLD_HASH = "6b8acf3cf8523e2c2db2020f69c19f7ced2b1343e1b09621697515ed54b6eabd"
NEW_HASH = "e8bbb3d03034a24b27d1255533910581e981b1cdda63e11696ee06b02a18e9b2"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_table(n, digest):
    data = PATHS[n].read_bytes()
    require(sha256(data).hexdigest() == digest, "literal table digest differs")
    rows = {}
    for line in data.decode("ascii").splitlines():
        q, b, w, direction, t = line.split()
        q, b, w, t = map(int, (q, b, w, t))
        require(direction in ("L", "R") and w in (0, 1), "invalid action")
        require(0 <= t <= n and (q, b) not in rows, "invalid target or duplicate")
        rows[q, b] = (w, 1 if direction == "R" else -1, t)
    require(set(rows) == {(q, b) for q in range(n) for b in (0, 1)}, "bad domain")
    return rows


def decoder_states(old):
    # Reachability in the ordinary state graph with vertex 74 removed.
    reached = set()
    work = [0]
    while work:
        q = work.pop()
        if q == ENTRY or q == 209 or q in reached:
            continue
        reached.add(q)
        work.extend(old[q, b][2] for b in (0, 1))
    return {q for q in range(209) if q not in reached
            and all(old[q, b][2] != q for b in (0, 1))}


def compare(old, new, region):
    # Each node fixes only the original values at addresses read so far.
    # initial and current have identical domains. Unknown cells stay symbolic.
    work = [(ENTRY, 0, {-1: 1}, {-1: 1}, 0)]
    cases = max_reference = max_candidate = max_cells = 0
    while work:
        q, head, initial, current, steps = work.pop()
        if q in region:
            require(steps < 100, "reference decoder did not exit within bound")
            choices = [current[head]] if head in current else [0, 1]
            for b in choices:
                start = initial if head in current else {**initial, head: b}
                w, move, target = old[q, b]
                after = current.copy()
                after[head] = w
                work.append((target, head + move, start, after, steps + 1))
            continue

        # Replay the candidate from the same entry. It may use old states
        # outside the decoder as long as it reaches the exact reference exit.
        tape = initial.copy()
        state, pos = ENTRY, 0
        for length in range(1, 101):
            require(pos in tape, "candidate read a cell not fixed by this case")
            require((state, tape[pos]) in new, "candidate halted before matching")
            w, move, state = new[state, tape[pos]]
            tape[pos] = w
            pos += move
            if (state, pos) == (q, head) and tape == current:
                break
        else:
            raise ValueError("candidate failed to reach the reference exit")
        cases += 1
        max_reference = max(max_reference, steps)
        max_candidate = max(max_candidate, length)
        max_cells = max(max_cells, len(initial))
    return cases, max_reference, max_candidate, max_cells


def main():
    old = read_table(209, OLD_HASH)
    dense = read_table(207, NEW_HASH)
    labels = [q for q in range(210) if q not in OMITTED]
    new = {(labels[q], b): (w, d, labels[t]) for (q, b), (w, d, t) in dense.items()}
    require((labels[0], labels[-1]) == (0, 209), "start or halt differs")
    region = decoder_states(old)
    require(ENTRY in region and 0 not in region and OMITTED <= region, "bad boundary")
    require(all(new[k] == row for k, row in old.items() if k[0] not in region),
            "different action at a common boundary state")
    incoming = [(q, b, w, d, t) for (q, b), (w, d, t) in old.items()
                if q not in region and t in region]
    require(incoming == [(68, 1, 1, 1, ENTRY)], "unexpected decoder entrance")
    cases, max_old, max_new, max_cells = compare(old, new, region)
    changes = sum(row != old[key] for key, row in new.items())
    print(f"PASS. 207 working states, {len(new)} rows, {changes} changed surviving rows.")
    print(f"{len(region)} reference decoder states, {cases:,} exhaustive tape cases.")
    print(f"At most {max_cells} fixed cells per case, including the entry marker.")
    print(f"Maximum decoder steps: ZF209 {max_old}, ZF207 {max_new}.")


if __name__ == "__main__":
    main()
