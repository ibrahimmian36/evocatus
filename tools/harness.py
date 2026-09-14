"""Shared test harness: pinned official verifier, the Lean executable, and the ledger.

Every check here fails closed: a missing pin, a missing binary, or an unparseable
reply raises instead of returning a verdict.
"""
import json, os, pathlib, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
OFFICIAL_PIN = "a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e"
SNEIDERMAN_PIN = "d0ed2c06bb3a9e7ed31e2f31e24d17de6323efe8"
AC_LEAN_SHA256 = "927ba318d26b06c312140117b2a4856373832ed2c043944f520ec7337bcfca1b"
EXE = ROOT / "lean" / ".lake" / "build" / "bin" / "stablecheck"
LEDGER = pathlib.Path(os.environ.get("EVOCATUS_LEDGER", ROOT / "ledger" / "tests.jsonl"))
DEFAULT_LIMITS = {"max_path_length": 100000, "max_total_relator_length": 10000,
                  "max_work": 5000000}


def official_root() -> pathlib.Path:
    p = os.environ.get("ACC_OFFICIAL")
    if not p:
        raise SystemExit("set ACC_OFFICIAL to a checkout of SAIRcompetition/Andrews-Curtis")
    root = pathlib.Path(p).resolve()
    head = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"],
                          capture_output=True, text=True, check=True).stdout.strip()
    if head != OFFICIAL_PIN:
        raise SystemExit(f"official checkout at {head}, expected {OFFICIAL_PIN}")
    import hashlib
    h = hashlib.sha256((root / "competition/tools/lean/AC.lean").read_bytes()).hexdigest()
    if h != AC_LEAN_SHA256:
        raise SystemExit(f"AC.lean sha256 {h} != {AC_LEAN_SHA256}")
    return root


def load_verifier():
    root = official_root()
    sys.path.insert(0, str(root / "competition" / "tools"))
    import verifier.core as core          # noqa: E402
    import verifier.stable_core as sc     # noqa: E402
    assert sc.NUM_MOVES == 257 and sc.MAX_RANK == 8
    return root, core, sc


def data_path(root, name):
    return root / "competition" / "tools" / "verifier" / "data" / name


class StableCheck:
    """Persistent subprocess around the Lean `stablecheck` executable."""

    def __init__(self):
        if not EXE.exists():
            raise SystemExit(f"missing {EXE}; run `lake build stablecheck` in lean/")
        self.p = subprocess.Popen([str(EXE)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  text=True, bufsize=1)
        self.calls = 0

    def query(self, obj: dict) -> dict:
        self.p.stdin.write(json.dumps(obj) + "\n")
        self.p.stdin.flush()
        line = self.p.stdout.readline()
        if not line:
            raise RuntimeError("stablecheck produced no output (crashed?)")
        self.calls += 1
        rep = json.loads(line)
        if "error" in rep:
            raise RuntimeError(f"stablecheck error: {rep['error']} for {obj}")
        return rep

    def step(self, state, move):
        return self.query({"kind": "step", "state": [list(w) for w in state], "move": move})

    def path(self, start, moves):
        return self.query({"kind": "path", "start": [list(w) for w in start], "moves": moves})

    def check(self, start, moves):
        return self.query({"kind": "check", "start": [list(w) for w in start], "moves": moves})["accepted"]

    def check_ac(self, start, moves):
        return self.query({"kind": "check_ac", "start": [list(w) for w in start], "moves": moves})["accepted"]

    def table_rows(self):
        self.p.stdin.write(json.dumps({"kind": "table"}) + "\n")
        self.p.stdin.flush()
        rows = []
        while True:
            line = self.p.stdout.readline()
            if not line:
                raise RuntimeError("stablecheck died during table dump")
            line = line.rstrip("\n")
            if line.startswith('{"done"'):
                n = json.loads(line)["done"]
                assert n == len(rows) == 257, (n, len(rows))
                return rows
            rows.append(line)

    def close(self):
        self.p.stdin.close()
        self.p.wait(timeout=30)


def ledger(test: str, passed: bool, **fields):
    rec = {"ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "test": test,
           "passed": bool(passed)}
    rec.update(fields)
    LEDGER.parent.mkdir(exist_ok=True)
    with open(LEDGER, "a") as f:
        f.write(json.dumps(rec, sort_keys=True) + "\n")
    status = "PASS" if passed else "FAIL"
    print(f"[{status}] {test} " + " ".join(f"{k}={v}" for k, v in fields.items() if k != "detail"))
    return passed


def moves_ok_for_lean(moves):
    """Non-integer entries (floats, strings, null, bool) cannot be typed as `List ℤ`.
    Returns the index of the first such entry, or None."""
    for i, m in enumerate(moves):
        if type(m) is not int:
            return i
    return None
