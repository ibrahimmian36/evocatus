"""Tests for the conjugation-tree family (Phase 6, D6).

1. Extraction: for random (n, p, z, s) the Lean `tree` relators, evaluated by
   `lake env lean` and printed as integer words, must equal an independent Python
   construction byte for byte. Edge cases are forced in.
2. Paths: the three-moves-per-relator trivialization is emitted as `sac-r8-v1` ids
   (a conjugation by a word is a sequence of letter conjugations), followed by the
   destabilizations; the official verifier must accept every path from the extracted
   presentation, and a sample is kernel-checked through `checkEncodedAt`.
3. The braid-chain witness showing the exponent-sum form fails is recorded.
4. A rank-2 instance of the normal-closure mechanism (multiply a relator by a
   conjugate of the other) is verified and kernel-checked.
"""
import argparse, json, pathlib, random, re, subprocess, sys
from harness import ROOT, load_verifier, ledger, DEFAULT_LIMITS, moves_ok_for_lean

LEAN_DIR = ROOT / "lean"

def free_reduce(core, w): return list(core.free_reduce(tuple(w)))
def inv(w): return [-a for a in reversed(w)]

def py_tree(core, n, p, z, s):
    rel = []
    for i in range(n):
        if i + 1 < n:
            x = [p[i] + 1]
            if s[i]: x = inv(x)
            rel.append(free_reduce(core, [i + 1] + z[i] + x + inv(z[i])))
        else:
            rel.append([n])
    return rel

def lean_word(n, w):
    return f"mkWord {n} {json.dumps(w)}"

def lean_eval_block(idx, n, p, z, s):
    pl = "fun i => (⟨(" + json.dumps(p) + ").getD i.val 0 % " + str(n) + ", Nat.mod_lt _ (by omega)⟩ : Fin " + str(n) + ")"
    zl = "fun i => (" + "[" + ", ".join(lean_word(n, w) for w in z) + "]" + ").getD i.val 1"
    sl = "fun i => (" + json.dumps(s).replace("true", "true").replace("false", "false") + ").getD i.val false"
    return (f"#eval IO.println (\"T{idx} \" ++ toString ((List.ofFn (AC.Chain.tree (n := {n}) ({pl}) ({zl}) ({sl}))).map "
            f"(fun w => (FreeGroup.toWord w).map AC.Stable.encodeLetter)))\n")

def random_instance(rng, n, kind):
    if kind == "chain": p = [min(i + 1, n - 1) for i in range(n)]
    elif kind == "star": p = [n - 1] * n
    else: p = [rng.randint(i + 1, n - 1) if i + 1 < n else i for i in range(n)]
    z = []
    for i in range(n):
        L = rng.choice([0, 0, 1, 2, 3, 4])
        w = [rng.choice([1, -1]) * rng.randint(1, n) for _ in range(L)]
        if kind == "self" and i + 1 < n: w = [i + 1] + w + [-(p[i] + 1)]   # z contains x_i and x_{p i}
        z.append(w)
    s = [rng.random() < 0.5 for _ in range(n)] if kind != "neg" else [True] * n
    return p, z, s

def path_moves(sc, lut, n, p, z, s):
    """Forward moves trivializing the tree, then destabilizations to the empty presentation."""
    moves = []
    def conj_by_word(i, w):   # r_i <- w r_i w^-1 : apply letters of w from last to first
        for c in reversed(w): moves.append(lut[("conj", i, c)])
    for m in range(n - 2, -1, -1):
        conj_by_word(m, inv(z[m]))
        moves.append(lut[("mul", m, p[m], not s[m])])   # s true: relator has x_p^-1, multiply by r_p; else by r_p^-1
        conj_by_word(m, z[m])
    for k in range(n - 1, -1, -1): moves.append(15 + k)
    return moves

def build_lookup(sc):
    lut = {}
    for r in sc.MOVE_TABLE:
        c = r["category"]
        if c == "multiplication": lut[("mul", r["relator"], r["other"], r["invert_other"])] = r["id"]
        elif c == "conjugation": lut[("conj", r["relator"], r["conjugator"])] = r["id"]
    return lut

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=120)
    ap.add_argument("--seed", type=int, default=20260914)
    ap.add_argument("--kernel", type=int, default=20)
    a = ap.parse_args()
    root, core, sc = load_verifier()
    rng = random.Random(a.seed); lut = build_lookup(sc)
    insts = []
    forced = [(1, "chain"), (1, "star"), (2, "chain"), (2, "self"), (3, "neg"), (8, "star"), (8, "chain"), (8, "self"), (5, "random")]
    for n, kind in forced: insts.append((n, kind) + random_instance(rng, n, kind))
    while len(insts) < a.n:
        n = rng.randint(1, 8); kind = rng.choice(["chain", "star", "random", "self", "neg"])
        insts.append((n, kind) + random_instance(rng, n, kind))
    # 1. extraction via Lean #eval
    src = ["import StableCertificate", "open AC AC.Stable", "",
           "def mkWord (k : ℕ) (ls : List ℤ) : AC.Word k := FreeGroup.mk (ls.filterMap (parseLetterAt k))", ""]
    for idx, (n, kind, p, z, s) in enumerate(insts):
        src.append(lean_eval_block(idx, n, p, z, s))
    scratch = pathlib.Path("/tmp/evocatus_family_eval.lean"); scratch.write_text("\n".join(src))
    r = subprocess.run(["lake", "env", "lean", str(scratch)], cwd=LEAN_DIR, capture_output=True, text=True)
    scratch.unlink()
    if r.returncode != 0:
        print(r.stdout[-3000:], r.stderr[-3000:]); ledger("family_extraction", False, detail="lean eval failed"); sys.exit(1)
    got = {}
    for line in r.stdout.splitlines():
        m = re.match(r"T(\d+) (.*)", line)
        if m: got[int(m.group(1))] = json.loads(m.group(2))
    mism = 0
    for idx, (n, kind, p, z, s) in enumerate(insts):
        want = py_tree(core, n, p, z, s)
        if got.get(idx) != want:
            mism += 1; print("MISMATCH", idx, n, kind, p, z, s, "\n lean:", got.get(idx), "\n py:  ", want)
    ok1 = mism == 0 and len(got) == len(insts)
    ledger("family_extraction", ok1, instances=len(insts), mismatches=mism, seed=a.seed,
           kinds={k: sum(1 for t in insts if t[1] == k) for k in ("chain", "star", "random", "self", "neg")})
    if not ok1: sys.exit(1)
    # 2. paths through the official verifier, sample kernel-checked
    accepted = 0; rows = []
    for idx, (n, kind, p, z, s) in enumerate(insts):
        start = got[idx]; moves = path_moves(sc, lut, n, p, z, s)
        ch = {"challenge_id": f"tree-{idx}", "move_spec_version": "sac-r8-v1",
              "initial_relators": start, "target_relators": []}
        res = sc.verify(ch, moves, "sac-r8-v1", DEFAULT_LIMITS)
        if not res["ok"]:
            print("python rejected tree path", idx, res, start, moves); ledger("family_paths", False, index=idx); sys.exit(1)
        accepted += 1; rows.append((idx, n, start, moves))
    ledger("family_paths", accepted == len(insts), accepted=accepted, total=len(insts),
           max_moves=max(len(m) for _, _, _, m in rows))
    # kernel sample: highest ranks first, plus the forced edge cases
    sample = rows[:len(forced)] + sorted(rows[len(forced):], key=lambda t: (-t[1], -len(t[3])))[:max(0, a.kernel - len(forced))]
    src = ["import StableCertificate", "open AC.Stable", ""]
    for idx, n, start, moves in sample:
        src.append(f"theorem tree_{idx} : checkEncodedAt {json.dumps(start)} {json.dumps(moves)} = true := by\n  decide +kernel\n"
                   f"#print axioms tree_{idx}\n")
    scratch = pathlib.Path(LEAN_DIR / "Checks" / "FamilyKernel.lean"); scratch.write_text("\n".join(src))
    r = subprocess.run(["lake", "env", "lean", str(scratch)], cwd=LEAN_DIR, capture_output=True, text=True)
    axl = re.findall(r"'tree_(\d+)' depends on axioms: \[(.*)\]", r.stdout)
    okk = r.returncode == 0 and len(axl) == len(sample) and all(set(x.strip() for x in ax.split(",")) <= {"propext", "Classical.choice", "Quot.sound"} for _, ax in axl)
    if not okk: print(r.stdout[-2000:], r.stderr[-2000:])
    ledger("family_kernel", okk, theorems=len(sample), max_rank=max(n for _, n, _, _ in sample),
           max_moves=max(len(m) for _, _, _, m in sample))
    # 3. braid witness
    wit = json.load(open(ROOT / "corpus" / "braid_witness.json"))
    ledger("braid_witness_recorded", wit["exponent_sum"] == 1 and wit["image_SL25"] == "identity",
           w=wit["w"], relator=wit["chain"]["relator0"], note="exponent-sum form fails for general chains")
    # 4. rank-2 normal-closure mechanism: r0 <- r0 * (x y x^-1) * y^-1 from (x, y), then undo, then finish
    start = [[1], [2]]
    forward = [lut[("conj", 1, 1)], lut[("mul", 0, 1, False)], lut[("conj", 1, -1)], lut[("mul", 0, 1, True)]]
    undo = [sc.INVERSE_MOVE[m] for m in reversed(forward)]
    moves = forward + undo + [16, 15]
    st = tuple(tuple(w) for w in start)
    for m in forward: st, _ = sc.apply_move(st, m)
    mid = [list(w) for w in st]
    res = sc.verify({"challenge_id": "nc", "move_spec_version": "sac-r8-v1", "initial_relators": start, "target_relators": []}, moves, "sac-r8-v1", DEFAULT_LIMITS)
    expected_mid = [free_reduce(core, [1] + [1, 2, -1] + [-2]), [2]]
    src = ("import StableCertificate\nopen AC.Stable\n"
           f"theorem nc_mechanism : checkEncoded [[1],[2]] {json.dumps(moves)} = true := by\n  decide +kernel\n#print axioms nc_mechanism\n")
    scratch = pathlib.Path("/tmp/evocatus_nc.lean"); scratch.write_text(src)
    r = subprocess.run(["lake", "env", "lean", str(scratch)], cwd=LEAN_DIR, capture_output=True, text=True); scratch.unlink()
    m4 = re.search(r"'nc_mechanism' depends on axioms: \[(.*)\]", r.stdout)
    ax4 = {x.strip() for x in m4.group(1).split(",")} if m4 else None
    ok4 = res["ok"] and mid == expected_mid and r.returncode == 0 and ax4 is not None and ax4 <= {"propext", "Classical.choice", "Quot.sound"}
    ledger("normal_closure_mechanism_rank2", ok4, moves=moves, intermediate=mid, python_ok=res["ok"],
           mid_matches=(mid == expected_mid), lean_exit=r.returncode, axioms=sorted(ax4) if ax4 else None)
    if not ok4: print(r.stdout[-1500:], r.stderr[-1500:])
    sys.exit(0 if (ok1 and okk and ok4) else 1)

if __name__ == "__main__":
    main()
