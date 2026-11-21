"""Generate transition and decoder data checked by the Lean proof."""
import argparse
from collections import deque
from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
SOURCES = ROOT / "ProofSources"
DEST = SOURCES / "I0451" / "Tables.lean"
CHALLENGE = SOURCES / "Challenge.lean"
LITERAL_HASH = "034c26fb655f32123c516bfab93be38d5e055415058eb29e856c4c9a80e74d64"
NAMED_HASH = "aa7e8978f6ea40145009b7eb5e043974d161c5c9c71b6af73060fbb5dec3fca7"
HALT = 451
ROOT_STATE = "main().0"



def standalone_claim():
    """Copy the public statement and pure model definitions into Challenge."""
    source = SOURCES / "I0451"
    proofs = (source / "Logic" / "NamedProofs.lean").read_text()
    language = proofs[proofs.index("inductive NamedFormula"):proofs.index("namespace NamedFormula")]
    closure = (source / "Logic" / "CloseNamed.lean").read_text()
    free_labels = closure[closure.index("noncomputable def freeLabels"):closure.index("@[simp] theorem freeLabels_all")]
    bodies = []
    for name in ("ArithmeticSyntax", "SetModel", "Statement"):
        lean = (source / "Standalone" / f"{name}.lean").read_text()
        body = lean[lean.index("namespace I0451.Standalone"):]
        if name == "Statement":
            for definition in ("berkeleyAxiom", "i0Axiom", "targetConsistency", "haltingArithmetic"):
                head = body.index(f"def {definition} ")
                start = body.index(":=", head) + 2
                end = body.index("\n\n", start)
                body = body[:start] + " by sorry" + body[end:]
        bodies.append(body)
    return (
        "\n/-! Independent statement of the conditional result. The four formula\n"
        "definitions below have their fixed values supplied by Solution. -/\n"
        "namespace I0451.Logic\n" + language + "namespace NamedFormula\n" + free_labels + "end NamedFormula\nend I0451.Logic\n\n"
        + "\n".join(bodies)
        + "\nnamespace I0451.Standalone\n"
        "theorem exact451Claim : Claim451 := by sorry\n"
        "end I0451.Standalone\n"
    )


def parse(path):
    header, *lines = path.read_text().splitlines()
    prefix = "#! start "
    assert header.startswith(prefix)
    start = header.removeprefix(prefix)
    rows = {}
    for line in lines:
        if not line or line.startswith("#"):
            continue
        state, read, write, direction, target = line.split()
        assert read in ("0", "1") and write in ("0", "1") and direction in ("L", "R")
        key = state, int(read)
        assert key not in rows
        rows[key] = int(write), direction == "R", target
    return start, rows


def totalize(rows):
    states = {state for state, _ in rows}
    assert {(q, b) for q in states for b in (0, 1)} - rows.keys() == {("1.inc", 1)}
    return {**rows, ("1.inc", 1): (1, True, "1.inc")}


def enumerate_states(start, rows, terminal):
    numbers = {start: 0}
    pending = deque([start])
    while pending:
        state = pending.popleft()
        for bit in (0, 1):
            target = rows[state, bit][2]
            if target != terminal and target not in numbers:
                numbers[target] = len(numbers)
                pending.append(target)
    assert numbers.keys() == {state for state, _ in rows}
    numbers[terminal] = len(numbers)
    return numbers


def encode(rows, numbers):
    values = [0] * (2 * (max(numbers.values()) + 1))
    for (state, read), (write, right, target) in rows.items():
        values[2 * numbers[state] + read] = 1 + 4 * numbers[target] + 2 * right + write
    return values


def table_source(name, values):
    assert max(values) < 2048
    packed = sum(value << (11 * i) for i, value in enumerate(values))
    return f"def {name} : Table := 0x{packed:x}\n"


def decoder_tables(rows, numbers, registers):
    """Find the finite decoder graph in the literal machine.

    A vertex is a control and the two bits to the left of the head. The
    checker independently verifies the local contractions and uses the
    emitted ranks only as upper bounds on the remaining path lengths.
    """
    decoder = {q for q, _ in rows if not q[0].isdigit()}

    def move(state):
        q, left, right = state
        if not right or (q, right[0]) not in rows:
            return None
        write, go_right, target = rows[q, right[0]]
        if go_right:
            return target, (write, *left), right[1:]
        if left:
            return target, left[1:], (left[0], write, *right[1:])

    def classify(window, left, read):
        target, after_left, after_right = window
        if (after_left, after_right) == ((read, *left), ()):
            if target in decoder:
                return "next", target, read + 2 * left[0]
            if target == "halt" or target.startswith("3."):
                return "issue", target
        if read == 1 and target in {"6.break.1", "6.continue.0", "6.continue.1"}:
            if (after_left, after_right) == (left[1:], (left[0], 0)):
                return "erase", target
            if (left[0] == 1 and target == "6.continue.1"
                    and (after_left, after_right) == ((), (left[1], 0, 0))):
                return "fused", target
        return None

    ranks = {}
    arms = {}
    visiting = set()

    def height(q, context):
        key = q, context
        if key in ranks:
            return ranks[key]
        assert key not in visiting, f"Cyclic decoder at {key}"
        visiting.add(key)
        left = context % 2, context // 2
        successors = []
        arms[key] = []
        for read in (0, 1):
            window = q, left, (read,)
            for _ in range(3):
                window = move(window)
                assert window is not None, (key, read)
                outcome = classify(window, left, read)
                if outcome is not None:
                    arms[key].append(outcome)
                    successors.append(height(*outcome[1:]) if outcome[0] == "next" else 0)
                    break
            else:
                raise ValueError(f"No bounded decoder arm for {(key, read)}")
        visiting.remove(key)
        ranks[key] = max(successors) + 1
        return ranks[key]

    assert [height(ROOT_STATE, c) for c in range(4)] == [94] * 4
    packed_ranks = [0] * (4 * HALT)
    for (q, context), rank in ranks.items():
        packed_ranks[4 * numbers[q] + context] = rank
    # Abstract interpretation from the actual left marker (one followed
    # by blank cells). The joins bound a trailing zero run from above and
    # count the number of available jump markers from below.
    summaries = {(ROOT_STATE, 1): (0, 0, 0)}
    for key in sorted(ranks, key=ranks.get, reverse=True):
        if key not in summaries:
            continue
        zero_run, zeros, ones = summaries[key]
        for bit, outcome in enumerate(arms[key]):
            run = 0 if bit else zero_run + 1
            assert run <= 7
            false_count = min(1, zeros + (not bit))
            true_count = min(3, ones + bit)
            kind, target, *context = outcome
            if kind == "next":
                successor = target, context[0]
                other = summaries.get(successor)
                candidate = run, false_count, true_count
                if other:
                    candidate = max(other[0], run), min(other[1], false_count), min(other[2], true_count)
                summaries[successor] = candidate
            elif kind == "issue" and target.endswith(".decnz"):
                assert false_count >= 1
            elif kind == "erase" and target == "6.break.1":
                assert zeros >= 1
            elif kind == "erase" and target == "6.continue.1":
                assert ones >= 1
            elif kind == "fused":
                assert ones >= 2
    packed_safety = [0] * (4 * HALT)
    for (q, ctx), (run, zeros, ones) in summaries.items():
        packed_safety[4 * numbers[q] + ctx] = 1 + run + 8 * zeros + 16 * ones
    packed_graph = [0] * (8 * HALT)
    jumps = {"6.break.1": 470, "6.continue.0": 471, "6.continue.1": 472}
    for (q, ctx), exits in arms.items():
        for read, (kind, target, *_) in enumerate(exits):
            if kind == "next":
                code = numbers[target] + 1
            elif kind == "fused":
                code = 473
            elif kind == "erase":
                code = jumps[target]
            elif target == "halt":
                code = 474
            elif target.endswith(".inc"):
                code = 452 + registers.index(target.removesuffix(".inc"))
            else:
                assert target.endswith(".decnz")
                code = 461 + registers.index(target.removesuffix(".decnz"))
            packed_graph[8 * numbers[q] + 2 * ctx + read] = code
    return packed_ranks, packed_safety, packed_graph


def register_names(rows):
    """Follow the register selectors toward the first register."""
    successors = {q: rows[q, 1][2] for q, read in rows
                  if read == 1 and q.startswith("3.") and q.endswith(".inc")}
    names = []
    previous = "1.inc"
    while successors:
        current, = (q for q, target in successors.items() if target == previous)
        del successors[current]
        names.append(current.removesuffix(".inc"))
        previous = current
    assert len(names) == 9
    return names


def main():
    assert sha256((DATA / "final-451.named.tm").read_bytes()).hexdigest() == NAMED_HASH
    literal_path = DATA / "zf-berkeley-451.tm"
    assert sha256(literal_path.read_bytes()).hexdigest() == LITERAL_HASH
    literal_start, literal = parse(literal_path)
    assert literal_start == "0"
    literal_numbers = {str(q): q for q in range(HALT + 1)}
    assert len(literal) == 2 * HALT and set(literal) == {
        (str(q), b) for q in range(HALT) for b in (0, 1)
    }
    values = encode(literal, literal_numbers)[:2 * HALT]

    final_start, final = parse(DATA / "final-451.named.tm")
    final = totalize(final)
    numbers = enumerate_states(final_start, final, "halt")
    assert numbers["halt"] == HALT
    assert encode(final, numbers)[:2 * HALT] == values
    registers = register_names(final)
    ranks, safety, graph = decoder_tables(final, numbers, registers)
    tables = [
        table_source("literal", values),
        table_source("decoderRanks", ranks),
        table_source("decoderSafety", safety),
        table_source("decoderGraph", graph),
    ]
    definitions = [
        f"def root : Nat := {numbers[ROOT_STATE]}",
        f"def breakOne : Nat := {numbers['6.break.1']}",
        f"def continueZero : Nat := {numbers['6.continue.0']}",
        f"def continueOne : Nat := {numbers['6.continue.1']}",
        f"def dispatchStates : List Nat := {[numbers['6.continue.0']] + [numbers[f'4.dispatch.{i}'] for i in range(1, 8)]}",
        f"def incStates : List Nat := {[numbers[name + '.inc'] for name in registers]}",
        f"def decStates : List Nat := {[numbers[name + '.decnz'] for name in registers]}",
        *[f"def {lean} : Nat := {numbers[source]}" for lean, source in (
            ("increment", "1.inc"),
            ("decrement", "1.decnz"),
            ("incrementGap", "1.inc.b"),
            ("incrementOnes", "1.inc.c"),
            ("incrementSeparator", "1.inc.d"),
            ("returnStart", "2.ret1"),
            ("returnOneZero", "2.ret1.1"),
            ("returnGap", "2.ret1.2"),
            ("returnFail", "2.ret2"),
            ("returnFailOneZero", "2.ret2.1"),
            ("returnFailGap", "2.ret2.2"),
            ("decGap", "1.decnz.b"),
            ("decOnes", "1.decnz.c"),
            ("decSeparator", "1.decnz.d"),
            ("decSeek", "1.decnz.e"),
            ("decInspect", "1.decnz.g"),
            ("decShift", "1.decnz.h"),
            ("decCheckTail", "1.decnz.i"),
            ("breakZero", "6.break.0"),
            ("scanRoot", "5.root"),
            ("select", "1.sel"),
            ("selectGap", "1.sel.b"),
            ("selectOnes", "1.sel.c"),
            ("selectSeparator", "1.sel.d"),
            ("selectBack", "1.sel.e"),
            ("selectReverse", "1.sel.f"),
        )],
    ]
    text = ("module\npublic import I0451.Machine\n\n"
            "/-! Transition and decoder data generated by scripts/gen_tables.py. -/\n\n"
            "@[expose] public section\nnamespace I0451\n\n"
            + "\n".join(tables) + "\n" + "\n\n".join(definitions) + "\n\nend I0451\n")
    machine = (SOURCES / "I0451" / "Machine.lean").read_text().removesuffix("end I0451\n")
    challenge = machine + tables[0] + """
/-- The literal table has 902 rows and a single edge into halt label 451. -/
def literalShape : Prop :=
  literal < 2048 ^ 902 ∧
  (List.range 902).all (fun i => let code := digit literal i
      code != 0 && (code - 1) / 4 ≤ 451) = true ∧
  ((List.range 902).filter (fun i => (digit literal i - 1) / 4 == 451)).length = 1

theorem literal_shape : literalShape := by
  unfold literalShape
  decide +kernel

end I0451
""" + standalone_claim()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    check = parser.parse_args().check
    for path, expected in ((DEST, text), (CHALLENGE, challenge)):
        if check:
            assert path.read_text() == expected, f"Stale generated file: {path}"
        else:
            path.write_text(expected)


if __name__ == "__main__":
    main()
