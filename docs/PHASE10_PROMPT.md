# Phase 10 prompt — referee pass

Written 2026-09-14. Constraints of PHASE6 section 0 apply. No new mathematics; the
aim is that a hostile reader finds nothing vacuous, nothing stale, and nothing that
breaks on first contact.

## R1 — research before acting
1. List every theorem in the package whose statement carries a hypothesis beyond
   type-correctness, with the hypothesis: `tree_reachable` (Ascending),
   `tree_with_root_reachable` (normal-closure membership), `standard_of_congr_generator`,
   `conjecture19_reduction` (GeneratorsCongruent), `conjecture19_iff_generator`
   (also InfiniteOrderMod), `substitution_removal` (`R i = rel g w'`,
   PresentsTrivialGroup), `iterated_stableTrivial` (base stably trivial),
   `checkEncodedAt_sound` (parsePres). For each, decide a concrete witness that
   satisfies the hypothesis nontrivially, and one that violates it, where a
   violation is expressible.
2. Re-read competition/rules/proof.md on assessment: organizers assess selected
   claims; being published does not certify correctness. The reader is a
   mathematician, not the platform.
3. Check the CI workflow for any step that runs code not exercised locally.

## D1 — non-vacuity witnesses (Lean, 1 h)
`lean/Checks/NonVacuous.lean`: an `example` per theorem above instantiating its
hypotheses with concrete data at rank 2 or 3 and concluding the theorem, plus the
`GeneratorsCongruent` and `InfiniteOrderMod` witnesses for `⟨x, y | x y⁻¹, ·⟩` proved
through a homomorphism to `Multiplicative ℤ`, and a two-step `Iterated` chain
rank 3 → 2 → 1. Every example must depend only on the three axioms.

## D2 — computed numbers (Python, 30 min)
`tools/consistency.py`: reads the gate's name list, counts `#print axioms` lines in a
`lake build Checks` log, reads the latest ledger record per test, and asserts that
every number in README.md's test table and the form draft (named theorems, kernel
theorems, instance counts, mutants, fuzz cases) equals the computed value. Fails on
any mismatch; ledgered.

## D3 — CI validation offline (30 min)
Parse `.github/workflows/verify.yml`; extract the embedded Python ledger check and
run it against a synthetic ledger that (a) passes, (b) has a failure, (c) is missing
a test; the check must accept (a) and reject (b) and (c). Confirm every tool the
workflow calls exists and accepts the flags used.

## D4 — fresh-export run (30 min)
Copy the working tree without `lean/.lake` to a temporary directory (a few MB), run
`tools/gen_table.py` diff, `tools/pool_index.py --check` and `tools/diff_table.py`
there. The first two must pass; the third must fail closed with the exact message
about the missing binary. Delete the copy.

## R2 — after D1 compiles
`#print axioms` on every example; grep the file for `sorry`; confirm no example is
closed by `decide` on a hypothesis that is actually `True` by definition.

## R3 — after completion
Gate, build, consistency, scan, statement audit, `pgrep`, scratch files, NOTES,
memory. Report the residual objections a referee could still raise.
