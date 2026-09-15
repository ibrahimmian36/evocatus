"""Numbers in the prose must be computed, not typed (Phase 10, D2).

Checks README.md against: the gate's name list, the count of `#print axioms`
directives under lean/Checks, and the latest ledger record per test.
"""
import json, pathlib, re, sys
from harness import ROOT, ledger

def latest(rows):
    out = {}
    for r in rows: out[r["test"]] = r
    return out

def main():
    readme = (ROOT / "README.md").read_text()
    gate_src = (ROOT / "tools" / "axiom_gate.py").read_text()
    names = re.findall(r'"(AC\.[A-Za-z0-9_.]+)"', gate_src.split("default=[")[1].split("])")[0])
    kernel = 0
    for f in (ROOT / "lean" / "Checks").rglob("*.lean"):
        kernel += len(re.findall(r"^#print axioms", f.read_text(), re.M))
    rows = latest([json.loads(l) for l in open(ROOT / "ledger" / "tests.jsonl")])
    checks = []
    m = re.search(r"\| Axiom gate \| (\d+) named theorems and all (\d+) kernel theorems", readme)
    checks.append(("gate names", int(m.group(1)) if m else None, len(names)))
    checks.append(("kernel theorems (#print axioms under Checks)", int(m.group(2)) if m else None, kernel))
    def num(pattern):
        mm = re.search(pattern, readme); return int(mm.group(1).replace(",", "")) if mm else None
    checks.append(("golden compared", num(r"\| (\d+)/\d+ comparable vectors"), rows["golden_vectors"]["compared"]))
    checks.append(("fuzz cases", num(r"\| ([\d,]+) cases \(two seeds\)"), 2 * rows["fuzz_step"]["cases"]))
    checks.append(("training stable", num(r"\| (\d+)/\d+ Stable AC"), rows["training_stable"]["accepted"]))
    checks.append(("generated", num(r"\| (\d+)/\d+ accepted by the official verifier and by the checker"), rows["generated_paths"]["accepted"]))
    checks.append(("mutants", num(r"\| ([\d,]+) mutants"), rows["mutations"]["tested"]))
    checks.append(("kernel_theorems tool", num(r"\| (\d+) certificates: 6 golden"), rows["kernel_theorems"]["theorems"]))
    checks.append(("family instances", num(r"\| (\d+) random and forced instances"), rows["family_extraction"]["instances"]))
    checks.append(("lemma11 instances", num(r"\| (\d+) instances built by reverse substitution"), rows["lemma11_extraction"]["instances"]))
    checks.append(("exe fuzz hostile lines", num(r"\| (\d+) hostile lines"), rows["exe_fuzz_hostile"]["lines"]))
    checks.append(("exe fuzz edge cases", num(r"; ([\d,]+) edge queries"), rows["exe_fuzz_edge_ranks"]["cases"]))
    bad = [(n, w, g) for n, w, g in checks if w != g]
    for n, w, g in checks:
        print(f"  {'ok ' if w == g else 'BAD'} {n}: readme={w} computed={g}")
    ledger("consistency", not bad, checks=len(checks), mismatches=[n for n, _, _ in bad], gate_names=len(names), kernel_theorems=kernel)
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
