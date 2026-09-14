# Phase 8 prompt — pre-submission hardening

Written 2026-09-14. Sections 0 of PHASE6 and PHASE7 (constraints) apply unchanged.
No mathematics beyond one packaging corollary; the value here is that nothing in
the entry can be wrong, crash, or overclaim when a stranger runs it.

## R1 — research before acting
1. Re-read competition/rules/proof.md for form constraints; re-read the SAIR
   description draft sentence by sentence and list, for each sentence that
   asserts a result, the theorem and hypotheses it rests on.
2. Re-read `stable_core.verify` for what Python does with out-of-range starting
   ranks (it raises) and with ranks above 8 in `apply_move` (no cap except
   stabilize), to define expected behaviour for the executable fuzz.
3. Machine status: memory pressure, disk, stray processes.

## D1 — Remark 17 class as a theorem (Lean, 1 h)
Define `AC.Lemma11.Iterated : Presentation → Presentation → Prop` inductively: reflexive,
and one substitution-and-removal step `⟨n+1, R⟩ → ⟨n, reduced R i g w'⟩` whenever
`R i = rel g w'`. Prove `iterated_stableTrivial`: if `P` is stably trivial then every
`Q` with `Iterated P Q` is stably trivial and presents the trivial group (the
trivial-group hypothesis of each step is supplied by invariance, not assumed).
Corollary `remark17`: with `P` a conjugation tree. Do not claim more than this.

## D2 — boundary theorems (Lean, 30 min)
`lean/Checks/Edge.lean`: rank 0 and rank 1 instances of `chain`, `tree`, Lemma 11
(`n = 0`, so `w' : Word 0`), `empty_to_standard 0`, and `#eval`/`decide +kernel`
checks that the decoder rejects ids 257 and accepts the block boundaries
0, 13, 14, 15, 22, 23, 28, 29, 136, 137, 256 at the ranks where they apply and
rejects them where they do not. Every check is a theorem or a `decide`, never a
printed value someone has to read.

## D3 — executable front-end fuzz (Python, 1 h)
`tools/exe_fuzz.py`, seeded, ledgered. Feed `stablecheck` malformed and hostile
lines: invalid JSON, unknown kind, missing fields, letters 0, letters beyond the
rank, non-integer letters, empty state, rank 9 and rank 10 states, ids −1, 257,
2^62, floats, booleans, a 100,000-move list, duplicate keys, a 1 MB line. The
process must answer every line with one JSON object (`error` or a verdict) and
must still answer a valid query afterwards. For well-formed edge inputs (ranks 9
and 10, ids at boundaries) compare the step verdict with `stable_core.apply_move`,
which has no rank cap except stabilize. Record peak resident memory of the
process over the run with `/usr/bin/time -l`.

## D4 — resource measurement (30 min)
Record in docs/NOTES.md: peak RSS and wall time of `lake build Checks` for a single
kernel file, of the full `tools/run_all.sh`, and of a 5,000-move replay. State the
disk used by `lean/.lake`. These numbers are what a reproducer needs.

## D5 — semantic audit document (1 h)
`docs/AUDIT.md`: a table with one row per claim sentence in README.md and
docs/SAIR_SUBMISSION.md: the sentence, the theorem, its hypotheses in words, the
test that exercises it, and any wording that outruns the theorem. Fix the wording
in place; the table must end with zero open rows.

## R2 — after D1 compiles
Confirm that `Iterated` steps carry no hidden hypothesis: the step must not assume
`PresentsTrivialGroup`; check by `#print` that the constructor's type mentions only
`R i = rel g w'`.

## R3 — after completion
Full suite; gate including `iterated_stableTrivial` and `remark17`; prose scan;
statement audit; `pgrep` empty; no scratch files; NOTES; memory. Report the exact
list of things a reviewer could still object to.

Time boxes: R1 30 min, D1 1 h, D2 30 min, D3 1 h, D4 30 min, D5 1 h, R3 30 min.
