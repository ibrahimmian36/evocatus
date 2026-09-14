# Phase 6 prompt — from one family to the substitution lemma, and the reduction of Conjecture 19

Written 2026-09-14 for the evocatus repository (github.com/ibrahimmian36/evocatus).
Read all of it before writing or running anything. Every claim here that is not
a theorem in the repository is a lead to be re-verified in R1.

## 0. Binding constraints

- Nothing is submitted, pushed, or sent by the executor. Commits are Ibrahim's,
  under his own author line, with the attribution grep at zero.
- Lean 4.29.1, Mathlib 5e932f97, official AC.lean unchanged. Axioms exactly
  {propext, Classical.choice, Quot.sound}; no sorry, no native_decide. The gate
  in tools/axiom_gate.py must list every new theorem and must keep passing its
  negative controls.
- Names in public files: Ibrahim Mian, never a nickname; contact ibrahimnmian@gmail.com.
- No overclaiming. Never write that Theorem 16, Proposition 12 or Conjecture 19 of
  Shehper et al. was proved. Say which step was formalized and under which hypothesis.
- Machine capacity: one `lake build` at a time, targeted at `StableCertificate` or a
  single check file; never rebuild Mathlib; never leave `stablecheck` or `lean`
  processes running (`pgrep -fl 'stablecheck|bin/lean'` must be empty at the end of
  every phase); scratch files go in the session scratchpad, not the repository;
  kernel checks are limited to instances of rank ≤ 8 and at most 200 moves; no new
  dependencies, no new caches, no downloads beyond individual source files.
- Fail closed: every test asserts its own evidence and writes to the ledger.

## 1. Research, before acting (R1)

1. Re-read Shehper et al. arXiv:2408.15332v2 Lemma 11, Lemma 15, Theorem 16,
   Remark 17, Conjecture 18 and 19 from the extracted text. Record their exact
   hypotheses. Note that Lemma 15's proof is a sketch that uses membership in the
   normal closure, not an explicit word.
2. Establish, with a computation, that the exponent-sum form is false for general
   conjugation chains: the rank-2 chain with `z₁ = x₂x₁` and sign + is the braid
   relation `x₁x₂x₁ = x₂x₁x₂`; B₃ surjects onto SL(2,5), which is perfect, so some
   word `w` of exponent sum 1 lies in the kernel and `⟨x₁,x₂ | braid, w⟩` is
   nontrivial. Find such a `w` by breadth-first search over SL(2,5) with
   A = [[1,1],[0,1]], B = [[1,0],[-1,1]] (these satisfy ABA = BAB mod 5), and check
   that it also fails the official verifier's trivialization in a small search, or
   at least that its exponent sum is 1 and its image is the identity. Keep the
   witness in the ledger. This fixes the hypothesis of the main theorem.
3. Confirm the Mathlib names at the pin, by grep of the source checkout, for:
   `Subgroup.normalClosure` (definition as closure of `conjugatesOfSet`),
   `Subgroup.closure_induction` (exact binder shape at this pin),
   `Group.conjugatesOfSet`/`Subgroup.mem_conjugatesOfSet_iff`, `FreeGroup.ext_hom`,
   `FreeGroup.lift`, `Multiplicative.ofAdd`, `zpow` lemmas (`zpow_neg`, `zpow_one`),
   `Function.update_noteq`/`update_of_ne`, `Equiv.Perm` for reindexing.
4. Check the SAIR Contributor Network again for any new Lean entry; check
   Sneiderman's repository for new commits touching stable moves. Kill if a sound
   stable checker or the same lemma has been published.

## 2. Deliverables

D1. `Reachable.mulRight_normalClosure` (core lemma). For `R : Relators n`, `i : Fin n`
    and `v` in the normal closure of `{R j | j ≠ i}`,
    `Reachable R (Function.update R i (R i * v))`.
    Proof plan: `Subgroup.closure_induction` on the normal closure (closure of
    conjugates) with predicate `∀ R' agreeing with R off i, Reachable R' (update R' i (R' i * v))`;
    generator case `g * R j * g⁻¹`: conjugate `R j` by `g`, right-multiply, conjugate
    back (all official steps); product case by transitivity; inverse case by
    `Reachable.symm` from the state `update R' i (R' i * v⁻¹)`; unit case refl.
    Then also `mulLeft` and inverse variants as corollaries if cheap.

D2. `Reachable.replaceRelator_of_mem_normalClosure` (Lemma 15, exact form). If
    `(R i)⁻¹ * w ∈ normalClosure {R j | j ≠ i}` then `Reachable R (update R i w)`.
    Corollary `Reachable.trivial_of_lastRelator`: if `Reachable (update R i (of g)) (standard n)`
    and `(R i)⁻¹ * (of g)^e ∈ normalClosure {R j | j ≠ i}` with `e ∈ {1, -1}`, then
    `Reachable R (standard n)`.

D3. Trees. Generalize `AC.Chain.chain` to a parent function `p : Fin n → Fin n` with
    `i < p i` for every non-root index and root = `n-1`: relator `i` is
    `x_i z_i x_{p i}^{s_i} z_i⁻¹`, the root relator is `x_{n-1}`. Prove
    `tree_reachable` by the same three moves per relator, eliminating from the top.
    Chains are the special case `p i = i+1`; keep `chain_reachable` as a corollary.

D4. The family theorem. For a tree `T` with root relator replaced by any `w` such that
    `w⁻¹ * x_{n-1}^{e} ∈ normalClosure {tree relators}` for some `e ∈ {1,-1}`,
    `Reachable (update T root w) (standard n)`, hence stably reachable, hence the
    presentation presents the trivial group (by Invariance).

D5. Conjecture 19, stated and reduced. State `Conjecture19` against AC.lean: for
    `R : Relators n`, index `i`, if every generator is congruent to `x_i^{±1}` modulo
    the normal closure of `{R j | j ≠ i}`, then for every `w` with signed exponent
    sum ±1 the presentation `update R i w` is AC-trivial. Prove the reduction
    theorem: under that hypothesis, if `update R i (of i)` is AC-trivial then so is
    `update R i w` for every such `w`. The signed exponent sum is the lift of the
    generators to `Multiplicative ℤ` weighted by the signs; use `FreeGroup.ext_hom`
    to show `w ≡ x_i^{signedSum w}` on all of the free group from the hypothesis on
    generators. Do not claim anything about Conjecture 19 beyond this reduction.

D6. Tests, all seeded, all in the ledger:
    - Executable extraction for D3: `#eval` the tree relators to integer words and
      compare byte-for-byte with an independent Python construction for random
      `(n, p, z, s)` at ranks 1–8, including edge cases `n = 1`, `z_i = 1`, `z_i`
      containing `x_i` and `x_{p i}`, `s` all negative, star trees, chains, and
      trees with repeated `z`.
    - Path extraction for D3: the three moves per relator as `sac-r8-v1` ids
      (conjugation by a word = letter conjugations), verified by the official
      verifier from the extracted presentation to the empty presentation, then
      kernel-checked through `checkEncoded` for 20 instances up to rank 8.
    - Edge case for D4's hypothesis: the braid-chain witness from R1 must be
      recorded as a presentation for which the exponent-sum form fails.
    - Rank-2 instances of D2's mechanism: choose `v` as an explicit product of
      conjugates, build the move sequence by hand in Python, verify it, and
      kernel-check it.
    - Axiom gate on every new theorem; negative controls.
    - Full test suite unchanged and green; CI green on the pushed commit.

## 3. Research, right after starting (R2)

After D1's statement compiles and before its proof: check the exact closure-
induction lemma shape and whether `normalClosure` unfolds to
`closure (conjugatesOfSet s)` definitionally at this pin; if not, use
`Subgroup.normalClosure_eq_iInf`-free routes: prove the predicate is a normal
subgroup containing `s` and apply `normalClosure_le_normal`. Re-read the official
`Step.conj` convention (`w * R i * w⁻¹`) before writing the generator case.

## 4. Research, after completing (R3)

1. Statement audit: for every theorem named in README.md and docs/SAIR_SUBMISSION.md,
   open the Lean statement and confirm the prose matches it exactly, including the
   hypotheses. Remove or weaken any sentence that outruns the theorem.
2. Re-run the prose scan for AI tells, names, addresses, and the words solved,
   closed, resolved.
3. Re-run tools/run_all.sh and the axiom gate; confirm `pgrep` empty; confirm the
   working tree contains no scratch files.
4. Update docs/NOTES.md with what broke and why; update project memory.

## 5. Order of work and time boxes

R1 (1 h) → D3 (1 h) → D1 (3 h; if the closure induction fights, fall back to the
"predicate is a normal subgroup" route) → D2 (30 min) → D4 (30 min) → D5 (1 h) →
D6 (2 h) → R3 (1 h). Stop and report if D1 exceeds its box by a factor of two.
