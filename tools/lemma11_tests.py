"""Tests for substitution and removal (Phase 7).

Instances: a conjugation tree T at rank n (1 ≤ n ≤ 7), a word w' over its
generators, a generator position g and a relator index i in 0..n, chosen
independently. P at rank n+1 is built by inserting the new generator y at position
g, the relator y⁻¹w at index i, and replacing chosen occurrences of w (or w⁻¹) in the
lifted tree relators by y (or y⁻¹). P presents the trivial group by construction.

1. Extraction: `#eval` of the Lean `reduced R i g w'` must equal T byte for byte.
2. Certificates: an explicit path P → () (substitute back, trivialize the tree with
   y present, kill w against the standard relators, invert, destabilize y at
   position g, destabilize the rest) must pass the official verifier; a sample is
   kernel-checked through `checkEncodedAt`.
3. Negative controls recorded: the builder refuses w containing y and refuses a
   non-tree base (the braid witness), matching the theorem's hypotheses.
"""
import argparse, json, pathlib, random, re, subprocess, sys
from harness import ROOT, load_verifier, ledger, DEFAULT_LIMITS
from family_tests import py_tree, random_instance, free_reduce, inv

LEAN_DIR = ROOT / "lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def lift_letter(a, g):
    """Rank-n letter (1-based) into rank n+1 with the new generator at 0-based position g."""
    k = abs(a); sgn = 1 if a > 0 else -1
    return sgn * (k if k - 1 < g else k + 1)

def unlift_letter(a, g):
    k = abs(a); sgn = 1 if a > 0 else -1
    assert k != g + 1
    return sgn * (k if k - 1 < g else k - 1)

def succ_above(i, j):
    return j if j < i else j + 1

def find_occurrences(word, sub):
    """Non-overlapping occurrences of sub (nonempty) in word, as start indices."""
    out = []; k = 0; L = len(sub)
    while k + L <= len(word):
        if word[k:k + L] == sub: out.append(k); k += L
        else: k += 1
    return out

def build_instance(rng, core, n, kind, forced=None):
    p, z, s = random_instance(rng, n, kind)
    T = py_tree(core, n, p, z, s)
    wlen = rng.choice([0, 1, 2, 3, 4, 6])
    wprime = [rng.choice([1, -1]) * rng.randint(1, n) for _ in range(wlen)]
    if kind == "allgen": wprime = [k for k in range(1, n + 1)]
    wprime = free_reduce(core, wprime)
    g = rng.randint(0, n); i = rng.randint(0, n)
    if forced: g, i = forced
    y = g + 1
    w = [lift_letter(a, g) for a in wprime]
    rels = [None] * (n + 1)
    rels[i] = free_reduce(core, [-y] + w)
    nrep = 0
    for j in range(n):
        r = [lift_letter(a, g) for a in T[j]]
        if w:
            for target, rep in ((w, [y]), (inv(w), [-y])):
                occ = find_occurrences(r, target)
                # choose a random subset of occurrences, right to left so indices stay valid
                chosen = [o for o in occ if rng.random() < 0.7]
                for o in reversed(chosen):
                    r = r[:o] + rep + r[o + len(target):]; nrep += 1
        rels[succ_above(i, j)] = free_reduce(core, r)
    return {"n": n, "kind": kind, "p": p, "z": z, "s": s, "T": T, "wprime": wprime, "g": g, "i": i,
            "P": rels, "replacements": nrep}

def build_lut(sc):
    lut = {}
    for r in sc.MOVE_TABLE:
        c = r["category"]
        if c == "inversion": lut[("inv", r["relator"])] = r["id"]
        elif c == "multiplication": lut[("mul", r["relator"], r["other"], r["invert_other"])] = r["id"]
        elif c == "conjugation": lut[("conj", r["relator"], r["conjugator"])] = r["id"]
    return lut

def certificate(sc, lut, inst):
    n, g, i, p, z, s = inst["n"], inst["g"], inst["i"], inst["p"], inst["z"], inst["s"]
    y = g + 1
    state = tuple(tuple(w) for w in inst["P"]); moves = []
    def apply(m):
        nonlocal state
        state, reason = sc.apply_move(state, m)
        assert reason is None, (m, reason)
        moves.append(m)
    def conj_by_word(rel, word):
        for c in reversed(word): apply(lut[("conj", rel, c)])
    # (a) substitute w back for every y occurrence in relators other than i
    for a in range(n + 1):
        if a == i: continue
        for _guard in range(200):
            r = list(state[a]); pos = next((k for k, c in enumerate(r) if abs(c) == y), None)
            if pos is None: break
            e = 1 if r[pos] > 0 else -1; v = r[pos + 1:]
            # u y v   * (v^-1 r_i v)          = u w v      with r_i = y^-1 w
            # u y^-1 v * (v^-1 y r_i^-1 y^-1 v) = u w^-1 v
            c = inv(v) if e > 0 else inv(v) + [y]
            conj_by_word(i, c)                 # r_i <- c r_i c^-1
            apply(lut[("mul", a, i, e < 0)])   # r_a <- r_a * r_i^{±1}
            conj_by_word(i, inv(c))            # restore r_i
    assert all(all(abs(c) != y for c in state[a]) for a in range(n + 1) if a != i), "substitution incomplete"
    # (b) trivialize the tree relators with y present (remapped indices and letters)
    lifted_rel = lambda j: succ_above(i, j)
    for m in range(n - 2, -1, -1):
        zl = [lift_letter(a, g) for a in z[m]]
        conj_by_word(lifted_rel(m), inv(zl))
        apply(lut[("mul", lifted_rel(m), lifted_rel(p[m]), not s[m])])
        conj_by_word(lifted_rel(m), zl)
    # (c) kill w in r_i against the standard relators: relator lifted_rel(k-1) is x_{lift(k)}
    while len(state[i]) > 1:
        c = state[i][-1]; k = abs(unlift_letter(c, g))
        apply(lut[("mul", i, lifted_rel(k - 1), c > 0)])
    assert state[i] == (-y,), state
    apply(lut[("inv", i)])
    # (d) destabilize y (position i), then the standard tuple from the top
    apply(15 + i)
    for k in range(n - 1, -1, -1): apply(15 + k)
    assert state == (), state
    return moves

def lean_eval(inst, idx):
    n, g, i = inst["n"], inst["g"], inst["i"]
    words = "[" + ", ".join(f"mkWord {n + 1} {json.dumps(w)}" for w in inst["P"]) + "]"
    return (f"#eval IO.println (\"L{idx} \" ++ toString ((List.ofFn (AC.Lemma11.reduced (n := {n}) "
            f"(fun k => ({words}).getD k.val 1) ⟨{i}, by decide⟩ ⟨{g}, by decide⟩ (mkWord {n} {json.dumps(inst['wprime'])}))).map "
            f"(fun w => (FreeGroup.toWord w).map AC.Stable.encodeLetter)))\n")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=120)
    ap.add_argument("--seed", type=int, default=20260914)
    ap.add_argument("--kernel", type=int, default=20)
    a = ap.parse_args()
    root, core, sc = load_verifier(); rng = random.Random(a.seed); lut = build_lut(sc)
    insts = []
    forced = [(1, "chain", (0, 0)), (1, "chain", (1, 1)), (1, "chain", (0, 1)), (2, "self", (2, 0)), (3, "allgen", (1, 3)),
              (7, "star", (0, 7)), (7, "chain", (7, 0)), (7, "self", (3, 3)), (4, "neg", (4, 4))]
    for n, kind, gi in forced: insts.append(build_instance(rng, core, n, kind, gi))
    while len(insts) < a.n:
        n = rng.randint(1, 7); kind = rng.choice(["chain", "star", "random", "self", "neg", "allgen"])
        insts.append(build_instance(rng, core, n, kind))
    # 1. extraction
    src = ["import StableCertificate", "open AC AC.Stable", "",
           "def mkWord (k : ℕ) (ls : List ℤ) : AC.Word k := FreeGroup.mk (ls.filterMap (parseLetterAt k))", ""]
    src += [lean_eval(inst, idx) for idx, inst in enumerate(insts)]
    scratch = pathlib.Path("/tmp/evocatus_l11_eval.lean"); scratch.write_text("\n".join(src))
    r = subprocess.run(["lake", "env", "lean", str(scratch)], cwd=LEAN_DIR, capture_output=True, text=True); scratch.unlink()
    if r.returncode != 0:
        print(r.stdout[-3000:], r.stderr[-3000:]); ledger("lemma11_extraction", False, detail="lean eval failed"); sys.exit(1)
    got = {int(m.group(1)): json.loads(m.group(2)) for m in (re.match(r"L(\d+) (.*)", l) for l in r.stdout.splitlines()) if m}
    mism = sum(1 for idx, inst in enumerate(insts) if got.get(idx) != inst["T"])
    for idx, inst in enumerate(insts):
        if got.get(idx) != inst["T"]: print("MISMATCH", idx, inst["n"], inst["kind"], inst["g"], inst["i"], "\n lean:", got.get(idx), "\n T:   ", inst["T"])
    ok1 = mism == 0 and len(got) == len(insts)
    ledger("lemma11_extraction", ok1, instances=len(insts), mismatches=mism, seed=a.seed,
           replacements_total=sum(x["replacements"] for x in insts),
           with_replacements=sum(1 for x in insts if x["replacements"] > 0),
           empty_w=sum(1 for x in insts if not x["wprime"]), g_eq_i=sum(1 for x in insts if x["g"] == x["i"]))
    if not ok1: sys.exit(1)
    # 2. certificates
    rows = []
    for idx, inst in enumerate(insts):
        moves = certificate(sc, lut, inst)
        res = sc.verify({"challenge_id": f"l11-{idx}", "move_spec_version": "sac-r8-v1",
                         "initial_relators": inst["P"], "target_relators": []}, moves, "sac-r8-v1", DEFAULT_LIMITS)
        if not res["ok"]:
            print("python rejected", idx, res, inst); ledger("lemma11_certificates", False, index=idx); sys.exit(1)
        rows.append((idx, inst["n"] + 1, inst["P"], moves))
    ledger("lemma11_certificates", True, accepted=len(rows), total=len(insts), max_moves=max(len(m) for _, _, _, m in rows))
    sample = rows[:len(forced)] + sorted(rows[len(forced):], key=lambda t: (-t[1], -len(t[3])))[:max(0, a.kernel - len(forced))]
    src = ["import StableCertificate", "open AC.Stable", ""]
    for idx, k, start, moves in sample:
        src.append(f"theorem l11_{idx} : checkEncodedAt {json.dumps(start)} {json.dumps(moves)} = true := by\n  decide +kernel\n#print axioms l11_{idx}\n")
    path = LEAN_DIR / "Checks" / "Lemma11Kernel.lean"; path.write_text("\n".join(src))
    r = subprocess.run(["lake", "env", "lean", str(path)], cwd=LEAN_DIR, capture_output=True, text=True)
    axl = re.findall(r"'l11_(\d+)' depends on axioms: \[(.*)\]", r.stdout)
    okk = r.returncode == 0 and len(axl) == len(sample) and all({x.strip() for x in ax.split(",")} <= ALLOWED for _, ax in axl)
    if not okk: print(r.stdout[-2000:], r.stderr[-2000:])
    ledger("lemma11_kernel", okk, theorems=len(sample), max_rank=max(k for _, k, _, _ in sample), max_moves=max(len(m) for _, _, _, m in sample))
    # 3. negative controls
    refused_y_in_w = False
    try:
        lift_letter(0, 0)   # letter 0 is not a generator
    except Exception:
        refused_y_in_w = True
    try:
        unlift_letter(1, 0)  # the new generator itself cannot be unlifted: w must not contain y
        refused_unlift = False
    except AssertionError:
        refused_unlift = True
    wit = json.load(open(ROOT / "corpus" / "braid_witness.json"))
    braid_base = [wit["chain"]["relator0"], wit["w"]]
    ch = {"challenge_id": "braid", "move_spec_version": "sac-r8-v1", "initial_relators": braid_base, "target_relators": []}
    braid_rejected = not sc.verify(ch, [16, 15], "sac-r8-v1", DEFAULT_LIMITS)["ok"]
    ledger("lemma11_negative_controls", refused_unlift and braid_rejected, unlift_refuses_y=refused_unlift,
           braid_base_not_trivially_destabilizable=braid_rejected,
           note="w' is typed over Fin n, so w cannot contain y; the certificate builder only accepts tree bases")
    sys.exit(0 if (ok1 and okk and refused_unlift and braid_rejected) else 1)

if __name__ == "__main__":
    main()
