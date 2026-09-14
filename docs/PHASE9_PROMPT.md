# Phase 9 prompt — Discovery Track groundwork at zero compute

Written 2026-09-14. Constraints of PHASE6 section 0 apply; in addition: no search
runs on this machine beyond a bounded smoke test (≤ 60 s CPU, ≤ 500 MB), no uploads,
no leaderboard queries without a key that Ibrahim supplies. The Proof Track package
is final; this phase prepares the only remaining source of score.

## R1 — research before acting (decides whether D2 exists)
1. Pool semantics: read `competition/tools/verifier/data/ms1190_metadata.csv` and the
   data README to learn what "certified", "uncertified" and "open" mean and how pool
   ids map to Miller–Schupp parameters.
2. Public solution data: inspect, without cloning anything large, the trees of
   Math-AI-Caltech/ACSolverX, joe-carr-data/ac-certificates, shehper/AC-Solver and
   Lisitsa's Zenodo record for files that contain complete trivializations (paths
   ending at the standard presentation), not equivalences between presentations.
   Record file names, formats, and move conventions (AC′ moves `h_i` of Shehper
   Appendix B, Carreras's format, ACSolverX's format).
3. Decide: if any public trivialization concerns a pool instance, D2 is live;
   otherwise D2 is dropped and the phase ends with D1 and D3.

## D1 — pool index and submission builder (Python, no Lean, 1 h)
`tools/pool_index.py`: canonical form of every pool presentation (relator order,
cyclic rotation, inversion, and the generator swap, as the official README's
matching states; verify the convention against the official canon module),
indexed to `ac-`/`sac-` ids, cached as a small JSON. `tools/submission_builder.py`:
takes `(presentation, moves)` pairs, matches to pool ids through the index, verifies
each with the official verifier for both specs, applies the 500-line and 10 MB
limits, and writes `submission.txt` plus a receipt; refuses anything unverified.
Tests: every one of the 424 training instances must map to itself and to no pool id;
the two paths found by the 09-13 greedy smoke test, if reproducible, must verify.

## D2 — harvest (only if R1 says so, 2 h)
Translate each public trivialization into official ids, verify, match, and add to
the draft submission; ledger every accepted and rejected item with its source and
licence. Never include a path whose licence forbids reuse.

## D3 — bounded search smoke (30 min)
Re-run the 09-13 greedy baseline through the builder on 50 random pool instances
with a hard 60 s CPU cap and record the hit rate, so the search stack's starting
point is in the ledger. No more compute than that.

## R2 — after D1 compiles
Cross-check the canonical form: for 1,000 random pool instances, apply random
rotations, inversions, relator swaps and the generator swap and confirm the index
returns the same id; confirm that distinct pool ids never collide.

## R3 — after completion
Ledger, scan, `pgrep`, scratch files, NOTES, memory; a written GO/NO-GO on the
Discovery Track with the evidence: hit rate, what public data exists, what a
budget would buy.
