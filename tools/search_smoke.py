"""Bounded greedy baseline on random pool instances (Phase 9, D3). Hard caps: total CPU
seconds and nodes per instance. Records the hit rate so the starting point of any
future search is in the ledger. Found paths go through the submission builder.
"""
import argparse, heapq, json, random, resource, sys, time
from harness import ROOT, load_verifier, ledger, DEFAULT_LIMITS
from submission_builder import build

def greedy(core, start, max_nodes):
    """Best-first on total length over ac-r2-v1 moves; returns a move list or None."""
    target = ((1,), (2,))
    start = tuple(tuple(w) for w in start)
    seen = {start: None}; heap = [(sum(map(len, start)), 0, start)]; nodes = 0; tie = 0
    while heap and nodes < max_nodes:
        _, _, s = heapq.heappop(heap); nodes += 1
        if s == target:
            path = []; cur = s
            while seen[cur] is not None:
                prev, m = seen[cur]; path.append(m); cur = prev
            return path[::-1]
        for m in range(14):
            t = core.apply_move(s, m)
            if t in seen or sum(map(len, t)) > 60: continue
            seen[t] = (s, m); tie += 1
            heapq.heappush(heap, (sum(map(len, t)), tie, t))
    return None

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=50)
    ap.add_argument("--seed", type=int, default=20260914)
    ap.add_argument("--max-nodes", type=int, default=10000)
    ap.add_argument("--cpu-cap", type=int, default=60)
    a = ap.parse_args()
    resource.setrlimit(resource.RLIMIT_CPU, (a.cpu_cap, a.cpu_cap))
    root, core, sc = load_verifier()
    manifest = [ch for ch in json.load(open(root / "competition/tools/verifier/data/manifest.json"))["challenges"] if ch["challenge_id"].startswith("ac-")]
    rng = random.Random(a.seed); picks = rng.sample(manifest, a.n)
    cands = []; t0 = time.time()
    for ch in picks:
        path = greedy(core, ch["initial_relators"], a.max_nodes)
        if path is not None:
            cands.append({"relators": ch["initial_relators"], "moves": path, "source": "greedy " + ch["challenge_id"]})
    out = str(ROOT / "corpus" / "submission_draft.txt")
    lines, receipt = build(root, core, sc, cands, out)
    json.dump(receipt, open(out + ".receipt.json", "w"), indent=1)
    acc = sum(1 for r in receipt if r["status"] == "accepted")
    ledger("search_smoke", True, instances=a.n, found=len(cands), accepted=acc, lines=len(lines),
           max_nodes=a.max_nodes, seconds=round(time.time() - t0, 1), seed=a.seed,
           note="greedy best-first on total length, no learning; baseline only")
    print(f"greedy: {len(cands)}/{a.n} found, {acc} accepted by the builder, {round(time.time()-t0,1)} s")

if __name__ == "__main__":
    main()
