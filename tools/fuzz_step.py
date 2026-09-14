"""Move-by-move differential fuzzing: official `stable_core.apply_move` vs the Lean step.

Seeded. Any disagreement stops the run and is logged in full.
"""
import argparse, random, sys
from harness import load_verifier, StableCheck, ledger

def random_state(rng, core, k):
    words = []
    for _ in range(k):
        n = rng.choice([0, 1, 1, 2, 3, 4, 5, 6, 8])
        w = core.free_reduce(tuple(rng.choice([1, -1]) * rng.randint(1, k) for _ in range(n)))
        words.append(w)
    return tuple(words)

def singleton_state(rng, core, k):
    """States where destabilization has a real chance to apply."""
    s = list(random_state(rng, core, k))
    for j in range(k):
        if rng.random() < 0.5:
            g = rng.randint(1, k)
            s[j] = (g if rng.random() < 0.85 else -g,)
    return tuple(s)

def random_id(rng):
    r = rng.random()
    if r < 0.30: return rng.randint(14, 22)
    if r < 0.60: return rng.randint(23, 256)
    if r < 0.80: return rng.randint(0, 13)
    if r < 0.90: return rng.choice([-3, -2, -1, 257, 258, 259, 260])
    return rng.randint(-3, 260)

def python_verdict(sc, state, m):
    if type(m) is not int or not (0 <= m < sc.NUM_MOVES):
        return ("reject", "E_BAD_MOVE_ID")
    new, reason = sc.apply_move(state, m)
    if reason is not None:
        return ("reject", reason)
    return ("accept", [list(w) for w in new])

def lean_verdict(chk, state, m):
    rep = chk.step(state, m)
    if rep["ok"]:
        return ("accept", rep["state"])
    return ("reject", rep["reason"])

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=100000)
    ap.add_argument("--seed", type=int, default=20260913)
    a = ap.parse_args()
    root, core, sc = load_verifier()
    rng = random.Random(a.seed)
    chk = StableCheck()
    by_reason = {}
    for i in range(a.n):
        k = rng.choice([2, 2, 3, 3, 4, 5, 6, 7, 8, 8])
        state = singleton_state(rng, core, k) if rng.random() < 0.5 else random_state(rng, core, k)
        m = random_id(rng)
        pv = python_verdict(sc, state, m)
        lv = lean_verdict(chk, state, m)
        key = pv[0] if pv[0] == "accept" else pv[1]
        by_reason[key] = by_reason.get(key, 0) + 1
        if pv != lv:
            ledger("fuzz_step", False, seed=a.seed, cases_before_failure=i, state=[list(w) for w in state],
                   move=m, python=pv, lean=lv)
            print("DISAGREEMENT", state, m, pv, lv)
            sys.exit(1)
    assert sum(by_reason.values()) == a.n
    assert by_reason.get("accept", 0) > 0 and by_reason.get("destabilize_precondition", 0) > 0
    assert by_reason.get("max_rank_exceeded", 0) > 0 and by_reason.get("generator_out_of_rank", 0) > 0
    assert by_reason.get("relator_out_of_rank", 0) > 0 and by_reason.get("E_BAD_MOVE_ID", 0) > 0
    ledger("fuzz_step", True, seed=a.seed, cases=a.n, breakdown=by_reason)

if __name__ == "__main__":
    main()
