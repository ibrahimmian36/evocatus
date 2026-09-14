"""Hostile-input fuzz of the `stablecheck` front end (Phase 8, D3).

Every line sent must produce exactly one JSON reply, an `error` or a verdict, and the
process must still answer a valid query afterwards. Well-formed edge inputs (ranks 9
and 10, boundary ids) are compared with `stable_core.apply_move`, which has no rank
cap except stabilize. Peak resident memory is recorded.
"""
import argparse, json, random, resource, subprocess, sys
from harness import EXE, load_verifier, ledger

def send(p, line):
    p.stdin.write(line + "\n"); p.stdin.flush()
    out = p.stdout.readline()
    if not out: raise RuntimeError("no reply (process died?) for line: " + line[:120])
    return json.loads(out)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260914)
    ap.add_argument("--n", type=int, default=2000)
    a = ap.parse_args()
    root, core, sc = load_verifier()
    rng = random.Random(a.seed)
    p = subprocess.Popen([str(EXE)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
    canary = json.dumps({"kind": "path", "start": [[1], [2]], "moves": [16, 15]})
    hostile = [
        "", "   ", "not json", "{", "[]", "{}", '{"kind": 3}', '{"kind": "nope"}', '{"kind": "step"}',
        '{"kind":"step","state":[[1],[2]]}', '{"kind":"step","move":3}', '{"kind":"step","state":"x","move":3}',
        '{"kind":"step","state":[[0],[2]],"move":3}', '{"kind":"step","state":[[3],[2]],"move":3}',
        '{"kind":"step","state":[[1.5],[2]],"move":3}', '{"kind":"step","state":[["1"],[2]],"move":3}',
        '{"kind":"step","state":[[1],[2]],"move":1.5}', '{"kind":"step","state":[[1],[2]],"move":"3"}',
        '{"kind":"step","state":[[1],[2]],"move":true}', '{"kind":"step","state":[[1],[2]],"move":null}',
        '{"kind":"step","state":[[1],[2]],"move":-1}', '{"kind":"step","state":[[1],[2]],"move":257}',
        '{"kind":"step","state":[[1],[2]],"move":4611686018427387904}', '{"kind":"step","state":[],"move":14}',
        '{"kind":"step","state":[],"move":15}', '{"kind":"step","state":[[1],[2],[3],[4],[5],[6],[7],[8],[9]],"move":14}',
        '{"kind":"path","start":[[1],[2]],"moves":[]}', '{"kind":"path","start":[[1],[2]],"moves":"x"}',
        '{"kind":"path","start":[[1],[2]],"moves":[16,15,15]}', '{"kind":"path","start":[[1],[2]],"moves":[-5]}',
        '{"kind":"check","start":[[1],[2],[3]],"moves":[16,15]}', '{"kind":"check","start":[[1]],"moves":[15]}',
        '{"kind":"check","start":[[1],[2]],"moves":[16,15],"kind":"step"}',
        '{"kind":"path","start":[[1],[2]],"moves":' + json.dumps([6, 7] * 50000) + '}',
        '{"kind":"step","state":[[1],[2]],"move":3,"junk":"' + "x" * 1000000 + '"}',
    ]
    replies = 0; errors = 0; verdicts = 0
    for line in hostile:
        rep = send(p, line); replies += 1
        if "error" in rep: errors += 1
        else: verdicts += 1
        assert send(p, canary).get("ok") is True, "canary failed after: " + line[:80]
    ok_hostile = replies == len(hostile)
    ledger("exe_fuzz_hostile", ok_hostile, lines=len(hostile), replies=replies, errors=errors, verdicts=verdicts)
    # well-formed edge inputs at ranks 9-10 and boundary ids vs apply_move
    mism = 0; cases = 0
    def rand_state(k):
        ws = []
        for _ in range(k):
            L = rng.randint(0, 4)
            ws.append(core.free_reduce(tuple(rng.choice([1, -1]) * rng.randint(1, k) for _ in range(L))))
        return tuple(ws)
    for _ in range(a.n):
        k = rng.choice([0, 1, 2, 8, 9, 10])
        state = rand_state(k)
        m = rng.choice([0, 13, 14, 15, 16, 22, 23, 28, 29, 136, 137, 160, 161, 256, 257, -1, rng.randint(0, 256)])
        if type(m) is int and 0 <= m < 257:
            new, reason = sc.apply_move(state, m)
            expect = ("accept", [list(w) for w in new]) if reason is None else ("reject", reason)
        else:
            expect = ("reject", "E_BAD_MOVE_ID")
        rep = send(p, json.dumps({"kind": "step", "state": [list(w) for w in state], "move": m}))
        got = ("accept", rep["state"]) if rep.get("ok") else ("reject", rep.get("reason", rep.get("error")))
        cases += 1
        if got != expect:
            mism += 1; print("MISMATCH", state, m, expect, got)
            if mism > 5: break
    ledger("exe_fuzz_edge_ranks", mism == 0, cases=cases, mismatches=mism, seed=a.seed, ranks=[0, 1, 2, 8, 9, 10])
    p.stdin.close(); p.wait(timeout=30)
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    ledger("exe_fuzz_memory", True, peak_rss_mb=round(ru.ru_maxrss / (1024 * 1024), 1), note="peak RSS of stablecheck over the fuzz run (macOS reports bytes)")
    sys.exit(0 if ok_hostile and mism == 0 else 1)

if __name__ == "__main__":
    main()
