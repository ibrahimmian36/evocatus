"""Pool index: canonical form of every Discovery challenge, keyed by the official
matching rule (relator order, cyclic rotation, inversion; no generator swap, which the
data README does not mention). Builds `corpus/pool_index.json` on first use.

Self-test (`--check`): every training instance maps to itself and to no pool id; for
1,000 random pool instances, random rotations, inversions and relator swaps return the
same id; distinct pool ids never collide.
"""
import argparse, json, random, sys
from harness import ROOT, load_verifier, ledger

INDEX = ROOT / "corpus" / "pool_index.json"

def cyclic_canon(core, w):
    """Minimal rotation of the cyclically reduced word or its inverse, as a tuple."""
    w = list(core.free_reduce(tuple(w)))
    while len(w) >= 2 and w[0] == -w[-1]:
        w = w[1:-1]
    if not w:
        return ()
    cands = []
    for u in (w, [-a for a in reversed(w)]):
        for k in range(len(u)):
            cands.append(tuple(u[k:] + u[:k]))
    return min(cands)

def canon(core, relators):
    return tuple(sorted(cyclic_canon(core, r) for r in relators))

def key(c):
    return json.dumps([list(r) for r in c])

def build(root, core):
    manifest = json.load(open(root / "competition/tools/verifier/data/manifest.json"))
    index = {}
    dup = 0
    for ch in manifest["challenges"]:
        cid = ch["challenge_id"]
        if not cid.startswith("ac-"):
            continue
        k = key(canon(core, ch["initial_relators"]))
        if k in index:
            dup += 1
        index.setdefault(k, cid)
    assert dup == 0, f"{dup} duplicate canonical forms in the pool"
    INDEX.parent.mkdir(exist_ok=True)
    json.dump(index, open(INDEX, "w"))
    return index

def load(root, core):
    if INDEX.exists():
        return json.load(open(INDEX))
    return build(root, core)

def lookup(index, core, relators):
    """Returns the ac- id, or None. The sac- id is the same suffix."""
    return index.get(key(canon(core, relators)))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--seed", type=int, default=20260914)
    a = ap.parse_args()
    root, core, sc = load_verifier()
    index = build(root, core)
    print("pool index:", len(index), "canonical forms")
    if not a.check:
        return
    rng = random.Random(a.seed)
    manifest = json.load(open(root / "competition/tools/verifier/data/manifest.json"))
    ac = {ch["challenge_id"]: ch for ch in manifest["challenges"] if ch["challenge_id"].startswith("ac-")}
    # training instances never match the pool
    train = json.load(open(root / "competition/examples/training_424.json"))["instances"]
    leaks = sum(1 for it in train if lookup(index, core, it["initial_relators"]) is not None)
    # random symmetries preserve the id
    ids = list(ac)
    stable_hits = 0; trials = 1000
    for _ in range(trials):
        cid = rng.choice(ids); rel = [list(w) for w in ac[cid]["initial_relators"]]
        out = []
        for w in rel:
            k = rng.randrange(max(1, len(w))); w = w[k:] + w[:k]
            if rng.random() < 0.5: w = [-x for x in reversed(w)]
            out.append(w)
        if rng.random() < 0.5: out.reverse()
        stable_hits += lookup(index, core, out) == cid
    ok = leaks == 0 and stable_hits == trials and len(index) == len(ac)
    ledger("pool_index", ok, forms=len(index), pool_ac=len(ac), training_leaks=leaks,
           symmetry_trials=trials, symmetry_hits=stable_hits, seed=a.seed)
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
