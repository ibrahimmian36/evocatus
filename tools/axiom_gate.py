"""Axiom gate: every listed theorem must depend on a subset of the three allowed axioms.

Runs `lake env lean` on a generated file containing `#print axioms` for each name and
parses the output. A name that produces no axiom line fails. The negative control
(`--negative-control`) compiles a theorem closed by `sorry` and asserts the gate FAILS.
"""
import argparse, pathlib, re, subprocess, sys, tempfile
from harness import ROOT, ledger

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
LEAN_DIR = ROOT / "lean"

def run_lean(src: str):
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=LEAN_DIR, delete=False) as f:
        f.write(src); path = pathlib.Path(f.name)
    try:
        r = subprocess.run(["lake", "env", "lean", str(path)], cwd=LEAN_DIR,
                           capture_output=True, text=True)
    finally:
        path.unlink()
    return r

def gate(names, imports):
    src = "\n".join(f"import {i}" for i in imports) + "\n" + \
          "\n".join(f"#print axioms {n}" for n in names) + "\n"
    r = run_lean(src)
    found = {}
    for line in r.stdout.splitlines():
        m = re.match(r".*'([^']+)' depends on axioms: \[(.*)\]", line)
        if m:
            found[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
        m2 = re.match(r".*'([^']+)' does not depend on any axioms", line)
        if m2:
            found[m2.group(1)] = set()
    verdicts = {}
    for n in names:
        if n not in found:
            verdicts[n] = ("MISSING", None)
        elif found[n] - ALLOWED:
            verdicts[n] = ("FORBIDDEN", sorted(found[n]))
        else:
            verdicts[n] = ("ok", sorted(found[n]))
    ok = r.returncode == 0 and all(v[0] == "ok" for v in verdicts.values())
    return ok, verdicts, r

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--names", nargs="*", default=[
        "AC.Stable.checkEncoded_sound", "AC.Stable.check_sound", "AC.Stable.step_sound",
        "AC.Stable.stab_sound", "AC.Stable.destab_sound",
        "AC.Reachable.equivalence", "AC.StableReachable.equivalence",
        "AC.stableConjecture_iff_empty", "AC.stableReachable_standard_iff_permuted",
        "AC.Chain.chain_reachable", "AC.Chain.chain_stableReachable",
        "AC.StableReachable.presentsTrivialGroup_iff", "AC.presentsTrivialGroup_of_stableReachable_standard",
        "AC.stableConjecture_iff_forall_iff", "AC.Stable.checkEncoded_presentsTrivialGroup",
        "AC.Reachable.mulRight_normalClosure", "AC.Reachable.standard_of_congr_generator",
        "AC.Chain.tree_reachable", "AC.Chain.tree_with_root_reachable",
        "AC.Chain.tree_with_root_presentsTrivialGroup", "AC.conjecture19_reduction",
        "AC.conjecture19_iff_generator", "AC.Stable.checkEncodedAt_sound"])
    ap.add_argument("--imports", nargs="*", default=["StableCertificate"])
    ap.add_argument("--negative-control", action="store_true")
    a = ap.parse_args()
    ok, verdicts, r = gate(a.names, a.imports)
    for n, v in verdicts.items():
        print(f"  {v[0]:9} {n} {v[1]}")
    ledger("axiom_gate", ok, names=len(a.names), verdicts={n: v[0] for n, v in verdicts.items()},
           allowed=sorted(ALLOWED))
    if a.negative_control:
        src = ("import StableCertificate\n"
               "theorem negative_control_sorry : AC.Stable.checkEncoded [[1],[2]] [] = true := by sorry\n"
               "theorem negative_control_native : AC.Stable.checkEncoded [[1],[2]] [16,15] = true := by native_decide\n"
               "#print axioms negative_control_sorry\n#print axioms negative_control_native\n")
        r2 = run_lean(src)
        found = re.findall(r"'([^']+)' depends on axioms: \[(.*)\]", r2.stdout)
        axioms = {n: {x.strip() for x in ax.split(",")} for n, ax in found}
        sorry_caught = "negative_control_sorry" in axioms and bool(axioms["negative_control_sorry"] - ALLOWED)
        native_caught = "negative_control_native" in axioms and bool(axioms["negative_control_native"] - ALLOWED)
        neg_ok = sorry_caught and native_caught
        ledger("axiom_gate_negative_control", neg_ok, sorry_axioms=sorted(axioms.get("negative_control_sorry", [])),
               native_axioms=sorted(axioms.get("negative_control_native", [])))
        ok = ok and neg_ok
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
