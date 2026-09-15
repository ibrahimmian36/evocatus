"""Validate the CI workflow offline (Phase 10, D3): parse the YAML, extract the embedded
ledger check, run it on synthetic ledgers (pass / failure / missing test), and confirm
every tool it calls exists and accepts its flags (`--help` exit 0).
"""
import json, pathlib, re, subprocess, sys, tempfile, yaml
from harness import ROOT, ledger

def main():
    wf = yaml.safe_load(open(ROOT / ".github" / "workflows" / "verify.yml"))
    steps = wf["jobs"]["verify"]["steps"]
    run_blocks = "\n".join(s.get("run", "") for s in steps)
    # 1. embedded ledger check
    step = next(s for s in steps if "need =" in s.get("run", ""))
    code = re.search(r'python3 -c "(.*)"', step["run"], re.S).group(1)
    need = set(re.findall(r"'([a-z_0-9]+)'", code.split("need =")[1].split("}")[0]))
    outcomes = {}
    with tempfile.TemporaryDirectory() as d:
        good = [{"test": t, "passed": True} for t in need]
        cases = {"pass": good, "failure": good + [{"test": "golden_vectors", "passed": False}],
                 "missing": [r for r in good if r["test"] != "axiom_gate"]}
        for name, rows in cases.items():
            p = pathlib.Path(d) / f"{name}.jsonl"
            p.write_text("\n".join(json.dumps(r) for r in rows) + "\n")
            src = code.replace("/tmp/ci_ledger.jsonl", str(p))
            r = subprocess.run([sys.executable, "-c", src], capture_output=True, text=True)
            outcomes[name] = r.returncode
    ok1 = outcomes == {"pass": 0, "failure": 1, "missing": 1}
    # 2. tools and flags
    tools = sorted(set(re.findall(r"python3 (tools/[a-z_0-9]+\.py)([^\n]*)", run_blocks)))
    flag_ok = True; checked = []
    for tool, flags in tools:
        exists = (ROOT / tool).exists()
        r = subprocess.run([sys.executable, tool, "--help"], cwd=ROOT, capture_output=True, text=True) if exists else None
        wanted = re.findall(r"(--[a-z-]+)", flags)
        accepted = exists and (not wanted or (r.returncode == 0 and all(f in r.stdout for f in wanted)))
        flag_ok &= accepted; checked.append((tool, accepted))
    ledger("ci_validate", ok1 and flag_ok, ledger_check=outcomes, required_tests=sorted(need), tools=checked)
    sys.exit(0 if ok1 and flag_ok else 1)

if __name__ == "__main__":
    main()
