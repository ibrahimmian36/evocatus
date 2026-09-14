"""Generate stable certificates that exercise stabilization, moves at ranks up to 8,
and destabilization of non-final relators with nontrivial generator relabelling.

Construction (all forward, all checked by the official verifier before use):

  certificate = V⁻¹ ++ L₁ ++ … ++ Lₙ ++ [16, 15]

* V is a random ordinary walk from (x, y) to the start S at rank 2, so V⁻¹ (table
  inverses, reversed) brings S back to (x, y).
* Each Lᵢ is a closed loop at (x, y). Three kinds:
    pair    : U ++ U⁻¹ for a random ordinary sequence U at rank 2.
    nest    : 14ᵈ, then U ++ U⁻¹ at rank 2+d using any of the 257 rows, then the
              d singleton relators removed in a random order (any positions:
              standard tuples relabel to standard tuples).
    relabel : 14ᵈ, then a sequence P that modifies relators other than r_j using
              conjugators and multipliers that avoid generator j+1, then
              destabilize r_j (the isolated singleton), then P⁻¹ translated to the
              renumbered generators and relator indices, then the remaining
              singletons removed. This exercises the relabelling of nontrivial
              words through a non-final destabilization.
"""
import argparse, json, random, sys
from harness import load_verifier, ledger, DEFAULT_LIMITS

def build_lookup(sc):
    lut = {}
    for r in sc.MOVE_TABLE:
        c = r["category"]
        if c == "inversion": key = ("inv", r["relator"])
        elif c == "multiplication": key = ("mul", r["relator"], r["other"], r["invert_other"])
        elif c == "conjugation": key = ("conj", r["relator"], r["conjugator"])
        else: continue
        lut[key] = r["id"]
    return lut

def translate(sc, lut, m, j, g):
    """Row id m at rank k+1, re-expressed at rank k after deleting relator j and generator g."""
    r = sc.MOVE_TABLE[m]
    sh = lambda a: a - (1 if a > j else 0)
    gsh = lambda c: (1 if c > 0 else -1) * (abs(c) - (1 if abs(c) > g else 0))
    c = r["category"]
    if c == "inversion": return lut[("inv", sh(r["relator"]))]
    if c == "multiplication": return lut[("mul", sh(r["relator"]), sh(r["other"]), r["invert_other"])]
    if c == "conjugation": return lut[("conj", sh(r["relator"]), gsh(r["conjugator"]))]
    raise AssertionError(m)

def apply_all(sc, state, moves, max_total):
    for m in moves:
        state, reason = sc.apply_move(state, m)
        if reason is not None or sum(len(w) for w in state) > max_total:
            return None
    return state

def random_ordinary(rng, sc, state, n, max_total, allow=None):
    """n applicable ordinary moves from `state`; returns (moves, end_state)."""
    rows = [r for r in sc.MOVE_TABLE if r["category"] in ("inversion", "multiplication", "conjugation")]
    out = []
    for _ in range(n):
        for _ in range(60):
            r = rng.choice(rows)
            if allow is not None and not allow(r):
                continue
            new, reason = sc.apply_move(state, r["id"])
            if reason is None and sum(len(w) for w in new) <= max_total:
                state = new; out.append(r["id"]); break
    return out, state

def inverse_path(sc, moves):
    return [sc.INVERSE_MOVE[m] for m in reversed(moves)]

def loop_pair(rng, sc, max_total):
    u, _ = random_ordinary(rng, sc, ((1,), (2,)), rng.randint(1, 8), max_total)
    return u + inverse_path(sc, u)

def loop_nest(rng, sc, max_total):
    d = rng.randint(1, 6)
    state = ((1,), (2,))
    moves = [14] * d
    state = apply_all(sc, state, moves, max_total)
    u, _ = random_ordinary(rng, sc, state, rng.randint(1, 10), max_total)
    moves += u + inverse_path(sc, u)
    for _ in range(d):
        k = len(state)          # rank before this destabilization
        j = rng.randint(0, k - 1)
        moves.append(15 + j)
        state = state[:j] + state[j + 1:]   # standard tuple stays standard after relabel
        state = tuple((i + 1,) for i in range(len(state)))
    return moves

def loop_relabel(rng, sc, lut, max_total):
    d = rng.randint(1, 6)
    k = 2 + d
    moves = [14] * d
    j = rng.randint(0, k - 1)   # relator to destabilize; its letter is g = j+1 on a standard tuple
    g = j + 1
    def allow(r):
        if r["relator"] == j: return False
        if r["category"] == "multiplication" and r["other"] == j: return False
        if r["category"] == "conjugation" and abs(r["conjugator"]) == g: return False
        return True
    std = tuple((i + 1,) for i in range(k))
    p, _ = random_ordinary(rng, sc, std, rng.randint(1, 8), max_total, allow)
    moves += p
    moves.append(15 + j)
    moves += [translate(sc, lut, m, j, g) for m in inverse_path(sc, p)]
    # now at the standard tuple of rank k-1; remove the remaining singletons
    rank = k - 1
    while rank > 2:
        jj = rng.randint(0, rank - 1)
        moves.append(15 + jj); rank -= 1
    return moves

def make_certificate(rng, sc, lut, max_total):
    v, start = random_ordinary(rng, sc, ((1,), (2,)), rng.randint(0, 10), max_total)
    moves = inverse_path(sc, v)
    for _ in range(rng.randint(1, 5)):
        kind = rng.choice(["pair", "nest", "nest", "relabel", "relabel", "relabel"])
        moves += {"pair": lambda: loop_pair(rng, sc, max_total),
                  "nest": lambda: loop_nest(rng, sc, max_total),
                  "relabel": lambda: loop_relabel(rng, sc, lut, max_total)}[kind]()
    moves += [16, 15]
    return start, moves

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=400)
    ap.add_argument("--seed", type=int, default=20260913)
    ap.add_argument("--out", default="corpus/generated.jsonl")
    ap.add_argument("--max-total", type=int, default=120)
    a = ap.parse_args()
    root, core, sc = load_verifier()
    lut = build_lookup(sc)
    rng = random.Random(a.seed)
    accepted = rejected = 0; max_rank_seen = 0; with_middle = 0
    with open(a.out, "w") as f:
        for idx in range(a.n):
            start, moves = make_certificate(rng, sc, lut, a.max_total)
            ch = {"challenge_id": f"gen-{a.seed}-{idx:05d}", "move_spec_version": "sac-r8-v1",
                  "initial_relators": [list(w) for w in start], "target_relators": []}
            res = sc.verify(ch, moves, "sac-r8-v1", DEFAULT_LIMITS)
            if not res["ok"]:
                rejected += 1
                print("python rejected generated path", idx, res, start, moves[:40])
                continue
            st = tuple(tuple(w) for w in start); ranks = [len(st)]; middle = False
            for m in moves:
                row = sc.MOVE_TABLE[m]
                if row["category"] == "destabilize" and row["relator"] < len(st) - 1:
                    middle = True
                st, _ = sc.apply_move(st, m); ranks.append(len(st))
            max_rank_seen = max(max_rank_seen, max(ranks)); with_middle += middle
            f.write(json.dumps({"challenge_id": ch["challenge_id"], "seed": a.seed, "index": idx,
                                "initial_relators": ch["initial_relators"], "moves": moves,
                                "length": len(moves), "max_rank": max(ranks),
                                "middle_destabilize": middle, "work": res["work"],
                                "certificate_hash": res["certificate_hash"]}) + "\n")
            accepted += 1
    ok = accepted == a.n and rejected == 0
    ledger("gen_paths", ok, seed=a.seed, requested=a.n, accepted=accepted, rejected=rejected,
           max_rank=max_rank_seen, with_middle_destabilize=with_middle, out=a.out)
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
