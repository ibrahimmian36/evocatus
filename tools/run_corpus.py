"""Path-level agreement: training corpus, generated corpus, and one-move mutations.

For every path, the official verifier's `ok` and the Lean checker's `accepted`
must agree. Mutations (replace, delete, insert, transpose one move) are applied to
every accepted path; both checkers must agree on each mutant, whatever the verdict.
"""
import argparse, json, random, sys
from harness import load_verifier, StableCheck, ledger, DEFAULT_LIMITS

def py_ok(sc, start, moves):
    ch = {"challenge_id": "x", "move_spec_version": "sac-r8-v1",
          "initial_relators": [list(w) for w in start], "target_relators": []}
    return sc.verify(ch, moves, "sac-r8-v1", DEFAULT_LIMITS)

def mutants(rng, moves, n):
    out = []
    for _ in range(n):
        m = list(moves)
        kind = rng.choice(["replace", "delete", "insert", "transpose"])
        if kind == "replace" and m:
            i = rng.randrange(len(m)); m[i] = rng.randint(0, 256)
        elif kind == "delete" and m:
            del m[rng.randrange(len(m))]
        elif kind == "insert":
            m.insert(rng.randint(0, len(m)), rng.randint(0, 256))
        elif kind == "transpose" and len(m) >= 2:
            i = rng.randrange(len(m) - 1); m[i], m[i + 1] = m[i + 1], m[i]
        out.append((kind, m))
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260913)
    ap.add_argument("--mutants-per-path", type=int, default=4)
    ap.add_argument("--generated", default="corpus/generated.jsonl")
    a = ap.parse_args()
    root, core, sc = load_verifier()
    rng = random.Random(a.seed)
    chk = StableCheck()
    ex = root / "competition" / "examples"
    stable = json.load(open(ex / "stable_training_424.json"))["instances"]
    ac = json.load(open(ex / "training_424.json"))["instances"]
    gen = [json.loads(l) for l in open(a.generated)] if a.generated else []

    # 1. training stable paths
    n_ok = 0
    for it in stable:
        p = py_ok(sc, it["initial_relators"], it["moves"])["ok"]
        l = chk.check(it["initial_relators"], it["moves"])
        if not (p and l):
            ledger("training_stable", False, id=it["training_id"], python=p, lean=l); sys.exit(1)
        n_ok += 1
    ledger("training_stable", n_ok == 424, accepted=n_ok, total=len(stable))
    # 2. training AC paths: official ac-r2-v1 verifier vs the stable engine replaying rows 0-13
    #    (identical rows) with the exact (x, y) endpoint; the upstream compiled checker is
    #    exponential in path length and is exercised on the short golden vectors instead
    n_ok = 0
    for it in ac:
        ch = {"challenge_id": "x", "move_spec_version": "ac-r2-v1",
              "initial_relators": it["initial_relators"], "target_relators": [[1], [2]]}
        p = core.verify(ch, it["moves"], "ac-r2-v1", DEFAULT_LIMITS)["ok"]
        assert all(0 <= m <= 13 for m in it["moves"])
        rep = chk.path(it["initial_relators"], it["moves"])
        l = rep["ok"] and rep["final"] == [[1], [2]]
        if not (p and l):
            ledger("training_ac", False, id=it["training_id"], python=p, lean=l); sys.exit(1)
        n_ok += 1
    ledger("training_ac", n_ok == 424, accepted=n_ok, total=len(ac))
    # 3. generated paths
    n_ok = 0
    for it in gen:
        p = py_ok(sc, it["initial_relators"], it["moves"])["ok"]
        l = chk.check(it["initial_relators"], it["moves"])
        if not (p and l):
            ledger("generated_paths", False, id=it["challenge_id"], python=p, lean=l); sys.exit(1)
        n_ok += 1
    ledger("generated_paths", n_ok == len(gen) and len(gen) > 0, accepted=n_ok, total=len(gen))
    # 4. mutations
    paths = [(it["initial_relators"], it["moves"]) for it in stable] + \
            [(it["initial_relators"], it["moves"]) for it in gen]
    tested = agreed = mut_accepted = 0
    by_kind = {}
    for start, moves in paths:
        for kind, m in mutants(rng, moves, a.mutants_per_path):
            p = py_ok(sc, start, m)["ok"]
            l = chk.check(start, m)
            tested += 1
            by_kind[kind] = by_kind.get(kind, 0) + 1
            if p != l:
                ledger("mutations", False, start=start, moves=m, kind=kind, python=p, lean=l)
                sys.exit(1)
            agreed += 1
            mut_accepted += p
    ledger("mutations", tested == agreed and tested > 0, seed=a.seed, tested=tested, agreed=agreed,
           accepted_by_both=mut_accepted, by_kind=by_kind)

if __name__ == "__main__":
    main()
