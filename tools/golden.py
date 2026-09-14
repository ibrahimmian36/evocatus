"""Replay the 33 official verify vectors through the Lean checkers.

Stable-spec vectors go through `path` (verdict + reason + index) and `check`
(accept only). AC-spec vectors go through the upstream ordinary checker
(`check_ac`, accept only). Three categories have no Lean analogue and are
recorded, not compared: E_SPEC_MISMATCH (the Lean checker has no spec field),
and the resource limits E_PATH_TOO_LONG / E_LENGTH_LIMIT / E_WORK_BUDGET.
"""
import json, sys
from harness import load_verifier, data_path, StableCheck, ledger, moves_ok_for_lean

NO_ANALOGUE = {"E_SPEC_MISMATCH", "E_PATH_TOO_LONG", "E_LENGTH_LIMIT", "E_WORK_BUDGET"}

def lean_stable_verdict(chk, start, moves):
    bad = moves_ok_for_lean(moves)
    if bad is not None:
        return {"ok": False, "code": "E_BAD_MOVE_ID", "move_index": bad, "typed": False}
    rep = chk.path(start, moves)
    if rep["ok"]:
        if rep["empty"]:
            return {"ok": True}
        return {"ok": False, "code": "E_NOT_TARGET", "final_shape": [len(w) for w in rep["final"]]}
    if rep["reason"] == "E_BAD_MOVE_ID":
        return {"ok": False, "code": "E_BAD_MOVE_ID", "move_index": rep["move_index"]}
    return {"ok": False, "code": "E_MOVE_NOT_APPLICABLE", "move_index": rep["move_index"],
            "reason": rep["reason"]}

def lean_ac_verdict(chk, start, moves):
    """`ac-r2-v1` semantics replayed by the stable engine: rows 0-13 are identical, any id
    outside 0..13 is E_BAD_MOVE_ID, and the endpoint must be exactly [[1],[2]]."""
    bad = moves_ok_for_lean(moves)
    if bad is not None:
        return {"ok": False, "code": "E_BAD_MOVE_ID", "move_index": bad, "typed": False}
    for i, m in enumerate(moves):
        if not 0 <= m <= 13:
            return {"ok": False, "code": "E_BAD_MOVE_ID", "move_index": i}
    rep = chk.path(start, moves)
    assert rep["ok"], rep
    if rep["final"] == [[1], [2]]:
        return {"ok": True}
    return {"ok": False, "code": "E_NOT_TARGET", "final_shape": [len(w) for w in rep["final"]]}

UPSTREAM_MAX_MOVES = 30   # the upstream compiled checker is exponential in path length

def main():
    root, core, sc = load_verifier()
    gv = json.load(open(data_path(root, "golden_vectors.json")))
    chk = StableCheck()
    compared = agreed = recorded = 0
    details = []
    for v in gv["verify_vectors"]:
        ch = gv["challenges"][v["challenge_id"]]
        exp = v["expected"]
        spec = v.get("move_spec_version", ch["move_spec_version"])
        code = exp.get("code")
        entry = {"name": v["name"], "spec": spec, "expected": exp}
        if code in NO_ANALOGUE:
            if code != "E_SPEC_MISMATCH":
                f = lean_stable_verdict if ch["move_spec_version"] == "sac-r8-v1" else lean_ac_verdict
                entry["lean"] = f(chk, ch["initial_relators"], v["moves"])
            entry["status"] = "recorded_no_analogue"
            recorded += 1
            details.append(entry); print("  recorded", v["name"], code, entry.get("lean"))
            continue
        if ch["move_spec_version"] == "sac-r8-v1":
            lv = lean_stable_verdict(chk, ch["initial_relators"], v["moves"])
            keys = ["ok"] + [k for k in ("code", "move_index", "reason", "final_shape") if k in exp]
            same = all(lv.get(k) == exp.get(k) for k in keys)
            accepted = None
            if moves_ok_for_lean(v["moves"]) is None:
                accepted = chk.check(ch["initial_relators"], v["moves"])
                same = same and (accepted == exp["ok"])
            entry.update(lean=lv, check_accepted=accepted)
        else:
            lv = lean_ac_verdict(chk, ch["initial_relators"], v["moves"])
            keys = ["ok"] + [k for k in ("code", "move_index", "final_shape") if k in exp]
            same = all(lv.get(k) == exp.get(k) for k in keys)
            upstream = None
            if moves_ok_for_lean(v["moves"]) is None and len(v["moves"]) <= UPSTREAM_MAX_MOVES:
                upstream = chk.check_ac(ch["initial_relators"], v["moves"])
                same = same and (upstream == exp["ok"])
            entry.update(lean=lv, upstream_check_ac=upstream)
        entry["status"] = "agree" if same else "DISAGREE"
        compared += 1; agreed += same
        details.append(entry)
        print(("  ok      " if same else "  MISMATCH"), v["name"])
    ok = compared == agreed and compared + recorded == 33
    json.dump(details, open("ledger/golden_details.json", "w"), indent=1)
    ledger("golden_vectors", ok, compared=compared, agreed=agreed, recorded_no_analogue=recorded)
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
