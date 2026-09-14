# Phase 0 memo — SAIR ACC Stable AC checker

Written 2026-09-13. Re-verification of `~/Desktop/3kvc/SAIR_ACC_STABLE_HANDOFF.md`
sections 4 to 7 against primary sources. Where this memo contradicts the handoff,
the memo wins. Section 3 lists every premise that failed or changed.

Repository name `evocatus` is provisional (offered in August, unused). Rename is Ibrahim's call.

## 1. What was checked and how

| Item | Method | Result |
|---|---|---|
| Official repo at `a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e` | clone, checkout, read rules, verifier, both move specs, golden vectors | as described; HEAD of `main` is still a0fd6e6 |
| Official golden vectors | `python3 -m verifier --golden …` | 63/63 pass (33 verify + 30 submission) |
| Official quick test / negative control | sample_submission.txt on training manifest; invalid_submission.txt on official manifest | quick: both `ok: true`; invalid: `accepted: true`, `ok: false`, `E_NOT_TARGET`, `final_shape [9,18]` |
| AC.lean identity | sha256 of official vs Sneiderman `lean/AC.lean` | identical: `927ba318d26b06c312140117b2a4856373832ed2c043944f520ec7337bcfca1b` |
| Sneiderman repo | clone; `git diff --stat d0ed2c0 HEAD`; trust grep over `lean/*.lean` | HEAD 16fd2c6 differs from d0ed2c0 only in README.md and MANIFEST.json; no sorry / native_decide / axiom / implemented_by / extern / unsafe outside AC.lean |
| Sneiderman entry timing | `git log --date=iso` | d0ed2c0 committed 2026-09-12 23:32 UTC; entry published 2026-09-13 00:19 UTC; last push 2026-09-13 02:29 UTC |
| Contributor Network | `GET https://api.sair.foundation/api/competitions/acc/contributor-network` | 2 entries: ACC-P000001 Idén (EUREKA, ACC01-T00067), ACC-P000002 Sneiderman (NavierStoked, ACC01-T00011, commit d0ed2c0, claim ac / proof / partial). No stable checker |
| Other Lean stable checkers | GitHub code search: `"sac-r8-v1"`, `"StableStep" language:Lean`, `"Andrews-Curtis" language:Lean`, `"destabilize" language:Lean`; repo search `Andrews-Curtis pushed:>2026-08-01`; Math-AI-Caltech org languages | none. All hits are the official repo, Sneiderman, or unrelated projects. Every other recent AC repo is Python/C++/notebooks |
| Training corpus | parse `stable_training_424.json` | 424/424 paths equal the AC path followed by `[16, 15]`; ids used are 0–13, 15, 16; none uses 14 or any id above 22; lengths 9–161, mean 35.6 |
| Golden stable vectors | listed by name | 11 stable verify vectors as the handoff says; move 14 appears in 9 vectors, ids above 22 in 3 (161, 162, 257) |
| Rank-3 detour | replayed through `stable_core.apply_move` | `[14,161,162,17,16,15]` on (x,y): (x,y,g3) → (x,y,x g3 x⁻¹) → (x,y,g3) → (x,y) → (x) → () |
| AK(3) instance | `problems/stable_ac.jsonl` line 399 | sac-00399 = ⟨x,y ∣ y⁻¹x⁻¹y⁻¹xyx ; y⁻⁴x³⟩, a rotation/inversion of AK(3) |
| Shehper et al. arXiv:2408.15332 | abs page (versions), both PDFs, pdftotext, grep | only v1 (2024-08-27) and v2 (2025-02-11) exist. v1 abstract: AK(3) "is stably AC-trivial"; v1 has no "misprint". v2 introduction p.4: misprint in [MMS02, p.10] "undermines the claim that (1) is stably AC-trivial"; Remark 14 (13th relator, affects [MMS02, Thm 1.4]); Appendix F: presentations "are not necessarily stably AC-trivial", plus the 53-move AC path (1)→AK(3) |
| Lisitsa arXiv:2501.18601 | abs page, PDF, Crossref | arXiv has v1 only (2025-01-17). Abstract: "alternative proof" of Shehper's result. §2.1: stable triviality of the source presentation is taken from [2] = MMS02. Journal version: Journal of Computational Algebra 16 (2025) 100041, Crossref record created 2025-10-15, published 2025-12, CC-BY; no `update-to` or relation records (no corrigendum registered) |
| Lisitsa Zenodo 14567743 | API + README.txt | CC-BY-4.0, 2024-12-29; files are AC-equivalence proofs P → AK(3) and extracted AC sequences S1, S2, S5; none is an end-to-end stable trivialization |
| shehper/AC-Solver | raw README, commits API | README line 139 still says AK(3) is stably AC-trivial; last commit 2025-08-11 |
| Later literature | arXiv HTML search "Andrews-Curtis", 46 results, newest first; PDFs of 2412.12293, 2506.23031, 2606.06122, 2606.21611 grepped | no paper since 2025-02 restates or repairs the AK(3) stable claim. Two-Hump (2606.21611, Fagan, Shehper, Gukov et al., June 2026) calls AK(3) the shortest potential two-generator counterexample and does not mention stable triviality. Lackenby 2606.06122 lists AK(k), k ≥ 3, among candidates. Gilman–Myasnikov 2506.23031: AK(3) shortest potential counterexample |
| Mathlib names | source checkout of mathlib4 at `5e932f97…`, grep | see §4 |
| Lean toolchain | `elan toolchain install leanprover/lean4:v4.29.1` | installed |

## 2. Premises confirmed

Sections 4, 5, 6, 7 of the handoff hold on every point checked above, including: the
form fields (rules/proof.md), the deadline and limits (rules/discovery.md), the 257-row
layout and the four `E_MOVE_NOT_APPLICABLE` reasons (stable_core.py lines 42–44, 127–185),
the endpoint gap (Python target `()` vs official `⟨n, standard n⟩`), Sneiderman's API
(Steps, Move, decode, replay, check, checkTrace, checkEncoded, checkEncodedTrace,
checkEncodedBetween, NoAddStep, noAdd_to_empty_iff_ordinary), and the absence of any
stable decoding in his package.

Block boundaries in `sac-r8-v1`, from the official table: destabilize r_i = 15+i;
invert r_i (i ≥ 2) = 21+i; multiplication r_i ← r_i r_j^{±1} occupies 29–136 in
(i, j, sign) order skipping the four rank-2 rows; conjugation of r_i occupies
137–148 (r0, g3..g8), 149–160 (r1, g3..g8), then 161+16(i−2) .. 176+16(i−2) for
i = 2..7 over g = 1..8, sign + then −. So 161 = r2 ← x r2 x⁻¹ and 162 = r2 ← x⁻¹ r2 x.

## 3. Premises refuted or changed

1. **Disk.** The handoff says the workstation disk hit 100% and every build must go on the pod.
   On 2026-09-13 the disk is 19% used with 70 GiB free after installing Lean 4.29.1,
   and no pod connection string was available. Decision: Phase 1 builds locally under
   `~/Desktop/3kvc/evocatus/lean/.lake` (about 7 GB, deletable, no cost). The rule's
   stated reason no longer holds; if builds must go on the pod anyway, the package
   moves unchanged.

2. **Lisitsa journal version.** The handoff cites ScienceDirect S2772827725000129.
   Crossref resolves it to Journal of Computational Algebra 16 (2025) 100041, created
   2025-10-15, i.e. eight months after Shehper v2. ScienceDirect returns 403 to
   scripted fetches, so whether the journal text reflects the v2 correction is
   UNRESOLVED; the page opens in a browser. The note must not claim either way.

3. **Prior Lean formalization exists, outside SAIR.** Sneiderman's PRIOR_WORK.md cites
   Zhang, Zhou, George, Gukov and Anandkumar, "AI-Driven Mathematical Discovery for the
   Andrews–Curtis Conjecture", NeurIPS 2025 MATH-AI workshop (OpenReview lt3Lpa4d2d),
   whose abstract describes a Lean formalization and an ACC autoformalizer. OpenReview
   returns 403 here; the Math-AI-Caltech org has no Lean code; GitHub has no other Lean
   AC repository. It predates the official AC.lean (2026-09) so it cannot be a checker
   against `AC.StableStep`, and kill criterion 1 is not triggered. It must be cited as
   prior formalization work in the submission. Reading the paper is a Phase 4 item.

4. **Zulip.** zulip.sair.foundation redirects to login; anonymous reading is not possible.
   No discussion was read.

5. **Mathlib name corrections** (see §4): `Fin.succAbove_predAbove` exists but has the
   shape `p.castSucc.succAbove (p.predAbove i) = i` for `p : Fin n`, which does not
   invert `g.succAbove` for an arbitrary `g : Fin (n+1)`. The right lemmas for the
   destabilize relabelling are `Fin.succAbove_castPred_of_lt` and
   `Fin.succAbove_pred_of_lt`. Everything else in the handoff's list exists at the pin.

6. **Free reduction.** Mathlib's `FreeGroup.reduce` is a right fold (`List.rec`)
   cancelling at the head; Python's is a left-fold stack. They agree because reduced
   representatives are unique (`reduce.min`, `reduce.idem`, `reduce.exact`), not by
   construction. The differential test in Phase 3 covers it.

7. **Sneiderman's manifest.** His `lean/lake-manifest.json` carries `"name": "ACStatement"`
   while his lakefile names the package `ac_square_family`. Lake accepted the
   dependency with `subDir = "lean"` at d0ed2c0 and is resolving Mathlib through it;
   whether the name mismatch causes trouble at build time is a Phase 1 observation.

8. **Contributor Network payload** includes team members' email addresses. Do not copy
   that JSON into the repository.

Nothing in sections 4–7 was found wrong on a mathematical point.

## 4. Mathlib names at 5e932f97dd25535344f80f9dd8da3aab83df0fe6

Confirmed by grep of the source tree (file:line):

- `Fin.succAbove` — Data/Fin/SuccPred.lean:463, `if castSucc i < p then i.castSucc else i.succ`
- `Fin.succAbove_last` — SuccPred.lean:581 (`succAbove (last n) = castSucc`)
- `Fin.succAbove_ne` :525, `Fin.succAbove_right_injective` :536, `Fin.exists_succAbove_eq` :626
- `Fin.succAbove_castPred_of_lt` :511, `Fin.succAbove_pred_of_lt` :501, `Fin.succAbove_of_castSucc_lt` :468, `Fin.succAbove_of_le_castSucc` :477, `Fin.succAbove_lt_iff_castSucc_lt` :588
- `Fin.castPred` :322, `Fin.castSucc_castPred` :336, `Fin.predAbove` :702, `Fin.succAbove_predAbove` :817 (shape noted above)
- `Fin.insertNth` — Data/Fin/Tuple/Basic.lean:840, `Fin.insertNth_apply_same` :845, `Fin.insertNth_apply_succAbove` :849, `Fin.insertNth_last` :935, `Fin.insertNth_last'` :948, `Fin.insertNth_zero` :924
- `Fin.snoc` :506, `Fin.snoc_castSucc` :517, `Fin.snoc_last` :530, `Fin.succAboveCases` :775, `Fin.removeNth` :835, `Fin.removeNth_insertNth` :874, `Fin.insertNth_removeNth` :1021
- `FreeGroup.mk` — GroupTheory/FreeGroup/Basic.lean:481, `FreeGroup.of` :623, `FreeGroup.map` :744, `FreeGroup.map.mk` :752 (`map f (mk L) = mk (L.map fun x => (f x.1, x.2))`), `FreeGroup.map.of` :768, `FreeGroup.invRev` :535, `FreeGroup.mul_mk` :529, `FreeGroup.inv_mk` :580
- `FreeGroup.reduce` — Reduce.lean:39, `reduce.self` :178, `reduce.red` :69, `reduce.min` :121, `reduce.idem` :132, `reduce.eq_of_red` :142, `reduce.sound` :164, `reduce.exact` :172, `toWord` :191, `toWord_mk` :206, `mk_toWord` :195, `reduce_toWord` :214

Not present: `FreeGroup.map_mk`, `FreeGroup.mk_eq_mk_iff`, `FreeGroup.Red.reduced`. `Fin.succAbove` and its lemmas live in Mathlib at this pin, not in Lean core.

## 5. Design confirmations for Phase 1

- State: `(k : ℕ) × RawTuple k` with `k ≤ 8` enforced by the decoder, `denoteP ⟨k, R⟩ = ⟨k, denote R⟩ : AC.Presentation`.
- Move 14 = `StableStep.stabilize R (Fin.last k) (Fin.last k)`; executable form is `Fin.snoc` of the letter-lifted tuple with `[(Fin.last k, true)]`; lifting a letter uses `Fin.castSucc` (= `(Fin.last k).succAbove` by `succAbove_last`).
- Destabilize r_i with letter g: executable precondition = relator i is exactly `[(g, true)]` and no other relator mentions `g`; executable relabel of a letter `v ≠ g` is `if v < g then v.castPred _ else v.pred _`; soundness via `succAbove_castPred_of_lt` / `succAbove_pred_of_lt`, then `StableStep.destabilize R' g i` with `R' j := relabel (S (i.succAbove j))` and the equation `stabilize R' g i = S` by `Fin.succAboveCases`.
- Endpoint: rank-0 tuple is unique (`Fin.elim0`), then `stabilize_standard_same` twice lifts `⟨0, standard 0⟩` to `⟨2, standard 2⟩`.
- Ordinary moves at rank k reuse `AC.Certificate.Move k` and `Move.sound`; `Steps.reachable` then `Reachable.stable`.

## 6. Recommendation

GO to Phase 1 (local build). Gate unchanged: the rank-3 detour vector must kernel-check
in under five minutes.
