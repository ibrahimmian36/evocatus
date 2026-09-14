"""Re-serialize the Lean table and diff it against the official specification rows."""
import json, sys
from harness import load_verifier, data_path, StableCheck, ledger

def main():
    root, core, sc = load_verifier()
    spec = json.load(open(data_path(root, "stable_move_spec.json")))
    want = [json.dumps(r, sort_keys=True, separators=(",", ":")) for r in spec["moves"]]
    got = StableCheck().table_rows()
    mism = [(i, want[i], got[i]) for i in range(257) if want[i] != got[i]]
    ok = len(want) == len(got) == 257 and not mism
    for i, w, g in mism[:5]:
        print("MISMATCH", i, "\n  spec:", w, "\n  lean:", g)
    ledger("table_roundtrip", ok, rows=len(got), mismatches=len(mism),
           spec_hash=spec["move_spec_hash"])
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
