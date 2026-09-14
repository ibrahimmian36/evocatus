# SAIR Proof Track submission — DRAFT, NOT SUBMITTED

Ibrahim submits. Nothing below has been entered anywhere. Before submitting:
the repository must be public under the chosen name, the commit SHA below must be
replaced with the verified public commit, and the AK(3) paragraph (Version A) must
be kept or removed per docs/AK3_NOTE.md.

| Field | Value |
|---|---|
| Title | Kernel-checked Stable AC certificates against the official statement |
| Authors | Ibrahim Mian |
|  | Shayaan Siddique |
| Conjecture | Stable AC |
| Direction | proof |
| Completeness | partial |
| Public GitHub repository | https://github.com/ibrahimmian36/evocatus (provisional name) |
| Git commit hash | (full 40-character SHA of the verified commit) |
| arXiv or paper link | (blank) |
| Reference to a published ACC result | Rob Sneiderman, "Explicit AC constructions for divisibility subfamilies of square presentations" (ACC-P000002) |
| Sharing agreement | (Ibrahim checks the box) |

## Description (Markdown; 5,600 characters, limit 10,000)

**Result.** A Lean 4 checker for all 257 moves of the Discovery Track's `sac-r8-v1`
table, proved sound against the official `AC.StableStep` relation in the unchanged
`AC.lean`. Replaying an accepted Stable AC certificate inside the kernel yields the
theorem `AC.StableReachable ⟨2, R⟩ ⟨2, AC.standard 2⟩` for its starting presentation
`R`. The Discovery verifier ends at the empty presentation while the official
conjecture ends at `⟨2, standard 2⟩`; the proof closes that gap with two official
stabilizations. This is a partial result in the sense of the Proof Track: it turns
search output into machine-checked statements about the official relation. It does
not bear on either conjecture.

**What is proved.** In namespace `AC.Stable`: `stab_sound` (move 14 is one official
`StableStep.stabilize`), `destab_sound` (an accepted destabilization of any relator
is one official `StableStep.destabilize`, with the executable renumbering shown to
invert `Fin.succAbove`), `step_sound` (every accepted table row is an official
`StableReachable` step; ordinary rows reuse the upstream `Move.sound`),
`check_sound` and `checkEncoded_sound` (an accepted replay from rank 2 to the empty
presentation is an official stable path to `⟨2, standard 2⟩`).

**Trust base.** Lean 4.29.1, Mathlib 5e932f97, the official `AC.lean` at a0fd6e6
byte-identical (sha256 asserted in CI), axioms exactly `propext`,
`Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`. The move table is
generated from the official `stable_move_spec.json` and re-serialized in Lean for a
byte diff against the specification, so no row was typed by hand.

**What is not claimed.** No progress on the ordinary or stable conjecture. No
resource limits: the Discovery verifier also rejects on path length, relator length
and work, and this checker does not, so acceptance here does not imply acceptance
there. No proved equivalence with the reference verifier; agreement is tested.

**How it was tested.** Two implementations, one truth: the official Python verifier
at a0fd6e6 and the Lean executable, with the kernel as final judge. Table round
trip 257/257. The 33 official golden verify vectors: 27 comparable vectors agree on
verdict, error code, reason and move index; the remaining 6 (spec mismatch, path
length, relator length, work budget) have no analogue and are recorded. Move-level
differential fuzzing of `stable_core.apply_move` against the Lean step at ranks 2–8
with ids −3…260, weighted toward moves 14–256: 200,000 cases, no disagreement.
Training corpus: 424/424 Stable AC and 424/424 AC paths accepted by both. A
generated corpus of 400 certificates built from loops returning to (x, y) through ranks up to 8,
each containing non-final destabilizations with renumbering of nontrivial words:
400/400 accepted by both, every one of the 257 ids exercised. One-move mutations of
every accepted path: 3,296 mutants, 3,296 agreements. Kernel theorems by
`decide +kernel` for 46 certificates (6 golden including the rank-3 detour, 20
training including the 161-move longest, 20 generated reaching rank 8), each under
three seconds; `#print axioms` on all of them and on the soundness theorems is
within the three axioms, and a `sorry` and a `native_decide` control both fail the
gate. Every test is seeded and logged to an append-only ledger in the repository.

**Check it yourself.**
```
git clone https://github.com/SAIRcompetition/Andrews-Curtis.git official && git -C official checkout a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e
cd lean && lake exe cache get && lake build StableCertificate Checks stablecheck && cd ..
ACC_OFFICIAL=$PWD/official tools/run_all.sh
```

**What it builds on.** Rob Sneiderman's `ac-square-divisibility` (commit d0ed2c0,
Apache-2.0), consumed as a Lake dependency: the unchanged `AC` module, his ordinary
`ac-r2-v1` checker (`Move`, `Move.sound`, `replay`, `parseTuple`) and his stable
lemmas (`stabilize_at`, `stabilize_succAbove`, `stabilize_standard_same`) are used
directly; this package adds decoding of `sac-r8-v1`, the executable stabilize and
destabilize with their soundness proofs, and the endpoint bridge. The official
statement, specification and reference verifier are SAIR's. Earlier Lean
formalization work on the conjecture by Zhang, Zhou, George, Gukov and Anandkumar
(NeurIPS 2025 MATH-AI workshop) predates the official statement and is not built on
here.

**On AK(3).** [Version A paragraph from docs/AK3_NOTE.md, or omit.]

**References.** SAIRcompetition/Andrews-Curtis a0fd6e6; Robby955/ac-square-divisibility
d0ed2c0; Shehper et al., arXiv:2408.15332v2; Myasnikov, Myasnikov, Shpilrain,
arXiv:math/0302080; Lisitsa, arXiv:2501.18601 and J. Comput. Algebra 16 (2025) 100041.
