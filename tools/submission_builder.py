"""Submission builder: from (presentation, moves) pairs to a verified `submission.txt`.

Each candidate is matched to a pool id through the index, replayed by the official
verifier under both specifications where applicable (AC needs the exact (x, y)
endpoint; Stable AC needs the empty presentation, so an AC path gets `[16, 15]`
appended), and written only if it verifies. Limits enforced: 500 solution lines and
10,000,000 bytes per file. A receipt lists every accepted and refused candidate.
Nothing is uploaded.
"""
import argparse, json, sys
from harness import ROOT, load_verifier, ledger, DEFAULT_LIMITS
from pool_index import load, lookup

def verify_ac(core, ch, moves):
    return core.verify(ch, moves, "ac-r2-v1", DEFAULT_LIMITS)

def verify_sac(sc, ch, moves):
    return sc.verify(ch, moves, "sac-r8-v1", DEFAULT_LIMITS)

def build(root, core, sc, candidates, out_path):
    """candidates: list of {"relators": [[..],[..]], "moves": [...], "source": str}."""
    index = load(root, core)
    manifest = {ch["challenge_id"]: ch for ch in json.load(open(root / "competition/tools/verifier/data/manifest.json"))["challenges"]}
    lines = []; receipt = []
    for c in candidates:
        cid = lookup(index, core, c["relators"])
        if cid is None:
            receipt.append({"source": c.get("source"), "status": "refused", "reason": "not in pool"}); continue
        ch = manifest[cid]
        moves = list(c["moves"])
        # the candidate may start from a rotation/inversion of the pool relators; the
        # verifier replays from the pool's exact words, so require exact equality
        if [list(w) for w in ch["initial_relators"]] != [list(w) for w in c["relators"]]:
            receipt.append({"source": c.get("source"), "status": "refused", "reason": "start differs from pool words (rotation/inversion); re-derive the path from the pool words", "id": cid}); continue
        r_ac = verify_ac(core, ch, moves) if all(0 <= m <= 13 for m in moves) else {"ok": False, "code": "ids beyond ac-r2-v1"}
        sid = "sac-" + cid[3:]
        smoves = moves + [16, 15] if all(0 <= m <= 13 for m in moves) else moves
        r_sac = verify_sac(sc, manifest[sid], smoves)
        entry = {"source": c.get("source"), "id": cid, "ac_ok": r_ac["ok"], "sac_ok": r_sac["ok"],
                 "ac_len": len(moves), "sac_len": len(smoves)}
        if r_ac["ok"]: lines.append(f"{cid}: {json.dumps(moves)}")
        if r_sac["ok"]: lines.append(f"{sid}: {json.dumps(smoves)}")
        entry["status"] = "accepted" if (r_ac["ok"] or r_sac["ok"]) else "refused"
        if not (r_ac["ok"] or r_sac["ok"]): entry["reason"] = {"ac": r_ac.get("code"), "sac": r_sac.get("code")}
        receipt.append(entry)
    if len(lines) > 500:
        raise SystemExit(f"{len(lines)} solution lines exceed the 500-line limit; split the file")
    text = "# evocatus draft submission; every line verified by the official verifier\n" + "\n".join(lines) + "\n"
    if len(text.encode()) > 10_000_000:
        raise SystemExit("file exceeds 10,000,000 bytes")
    open(out_path, "w").write(text)
    return lines, receipt

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--candidates", required=True, help="JSONL of {relators, moves, source}")
    ap.add_argument("--out", default="corpus/submission_draft.txt")
    a = ap.parse_args()
    root, core, sc = load_verifier()
    cands = [json.loads(l) for l in open(a.candidates) if l.strip()]
    lines, receipt = build(root, core, sc, cands, a.out)
    json.dump(receipt, open(a.out + ".receipt.json", "w"), indent=1)
    acc = sum(1 for r in receipt if r["status"] == "accepted")
    ledger("submission_builder", True, candidates=len(cands), accepted=acc, lines=len(lines), out=a.out)
    print(f"{acc}/{len(cands)} candidates accepted, {len(lines)} lines -> {a.out}")

if __name__ == "__main__":
    main()
