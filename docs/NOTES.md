# Build and test notes, Phases 1–3 (2026-09-13)

Observations that were not in the handoff and that future work needs.

1. **Lake dependency on a subdirectory works.** `[[require]] … subDir = "lean"` on
   Sneiderman's repository at d0ed2c0 fetched Mathlib and the rest through his
   manifest. His manifest's `"name": "ACStatement"` versus his package name
   `ac_square_family` caused no trouble.

2. **The table must be `@[irreducible]`.** With a plain `def table : Array Row := #[…]`
   any `rw`/`change` involving `replayFrom` hit `maximum recursion depth`: the
   elaborator unfolded `step` into the 257-element literal during definitional
   equality checks. Irreducibility stops that; the kernel still evaluates the table
   under `decide +kernel`. `table.size = 257` is proved by `decide +kernel` for the
   same reason.

3. **Replay state is a list, not a function.** The first version kept the state as
   `(k : ℕ) × RawTuple k` with `RawTuple k = Fin k → RawWord k` and applied the
   upstream `Move.apply`, which builds `Function.update` closures. The compiled
   executable then took time exponential in the path length (about 1 s at 22
   moves, minutes at 26) once the final words were forced; the upstream compiled
   `checkEncoded` shows the same growth (13 s at 26 moves). Inserting a
   materialization step made it worse. The fix is to keep the state as
   `(k : ℕ) × List (RawWord k)` and convert to a function only inside a single
   move (`toTuple`, `List.ofFn`), with `toTuple_ofFn` making the round trip
   propositionally the identity. Replay is now linear: 5,000 moves in 0.03 s.
   Consequence for tests: `ac-r2-v1` vectors are replayed by this engine (rows
   0–13 are byte-identical) and the upstream compiled checker is only exercised
   on vectors of at most 30 moves.

4. **The kernel needs no trace variant at these sizes.** `decide +kernel` proves the
   161-move training certificate and 115-move rank-8 generated certificates in
   under three seconds each including imports. The untrusted-intermediate-state
   design from the handoff was not needed and was not built.

5. **Generator design.** Random walks that blow up word length or that leave the
   rank above 2 were abandoned. The final generator composes closed loops at
   (x, y): a stabilize prefix, moves that avoid one singleton's generator, a
   non-final destabilization of that singleton, and the inverse moves translated
   to the renumbered generators and relator indices, then the remaining singletons
   removed. Every one of the 400 outputs was accepted by the official verifier on
   the first run, and all 257 ids occur.

6. **Deprecations in Lean 4.29.1 core** (`String.trimRight`, `String.dropRightWhile`,
   `String.mk`) are errors under `warningAsError`; the executable avoids them.

7. **Not done.** Phase 5 (a stable search on sac-00399) was not started; it needs an
   explicit budget. The AC-spec resource-limit vectors have no analogue and are
   recorded, not compared.

8. **Structural modules (2026-09-14).** `Official.lean`: `Step.reverse` needs three
   official steps for right multiplication (via the upstream `Steps.mulInvRight`) and
   one each for inversion and conjugation. `Invariance.lean`: normal-closure equality
   for ordinary moves via `normalClosure_le_normal` in both directions; stabilization
   via the retraction `unstab g := FreeGroup.lift (Fin.insertNth g 1 of)` and the
   comap argument `map_mem_normalClosure_image`. `Chain.lean`: the family is stated
   with `upTo z s m` (relators below `m` in chain form), trivialized from the top by
   conjugate, multiply, conjugate. Pitfalls: `rw [h]` with `h : R i = …` rewrites
   inside `Function.update R i …` too, so `set` the updated tuple first; anonymous
   constructors for `subset_normalClosure ⟨i, rfl⟩` need a known expected type, so
   use `refine … ?_` then `exact`.

9. **Phase 6 (2026-09-14), see docs/PHASE6_PROMPT.md.** The plan's target changed
   during research: the "any relator of exponent sum ±1" form of Theorem 16 is false
   for general conjugation chains. The rank-2 chain with `z₁ = x₂x₁` and sign `+` is
   `x₁x₂x₁ = x₂x₁x₂`, the braid relation; B₃ maps onto SL(2,5) with
   A = [[1,1],[0,1]], B = [[1,0],[-1,1]] mod 5, and a breadth-first search found
   `w = x₁² x₂⁻¹ x₁ x₂⁻¹ x₁ x₂⁻¹ x₁² x₂⁻²` of exponent sum 1 in the kernel
   (`corpus/braid_witness.json`), so `⟨x₁,x₂ | braid, w⟩` surjects onto SL(2,5).
   The correct hypothesis is congruence of `w` to the root generator modulo the
   tree relators, which is what `tree_with_root_reachable` assumes. The core lemma
   `Reachable.mulRight_normalClosure` is proved by `Subgroup.closure_induction` over
   `normalClosure = closure (conjugatesOfSet _)` with the predicate quantified over
   the current value of relator `i`; the inverse case uses `Reachable.symm`. Lean
   pitfalls: `Group.mem_conjugatesOfSet_iff`, not `Subgroup.…`; `let`-bound indices
   must be given to `simp` explicitly; `omega` needs `Fin.lt_def` facts as naturals;
   rank-2 certificates print axioms `[propext, Quot.sound]`, so gates must test
   subsets, not exact strings.

10. **Phase 7 (2026-09-14), see docs/PHASE7_PROMPT.md.** Lemma 11 proved in one
    build after one fix (a forgotten `subset_normalClosure` before a witness). The
    substitution over indices is an induction on a list with the partial tuple
    `substOn`, whose value at `k` is `subst (R k)` iff `k ≠ i ∧ k ∈ L`; a relator
    already substituted contributes `1` to the normal closure, an unsubstituted one
    contributes `r⁻¹ · r[w/y]`, in the normal closure of `{y⁻¹w}` by the two-homomorphism
    argument. Triviality transfers to the reduced tuple through `retract g w'`
    (`y ↦ w'`), using `map_mem_normalClosure_image` twice. The test builder had a
    real bug: for an inverse occurrence `u y⁻¹ v` the multiplier is the conjugate of
    `r_i⁻¹` by `v⁻¹y`, not by `v⁻¹`; the wrong conjugator left the occurrence in place
    and the scan looped. The loop is now bounded and asserts completion.

11. **Phase 8 (2026-09-14), see docs/PHASE8_PROMPT.md.** Hardening before submission.
    Machine requirements measured on an Apple Silicon laptop (macOS 25.5): `lean/.lake`
    is 7.2 GB after `lake exe cache get`; an incremental `lake build Checks` peaks at
    1.8 GB resident and takes about 5 s, a build of every check file from scratch
    peaks at 2.0 GB and takes about 30 s; a 5,000-move replay by `stablecheck` uses
    46 MB and 0.2 s; the whole front-end fuzz keeps `stablecheck` under 90 MB; the
    full `tools/run_all.sh` takes about six minutes, dominated by 86 kernel checks at
    about two seconds each. Nothing needs more than 2 GB of memory once the Mathlib
    cache is present. Defect found and fixed: a whitespace-only input line produced
    no reply from `stablecheck`, so a caller would wait forever; every non-EOF line
    now gets a JSON reply. The `Iterated` class packages repeated substitution and
    removal; its step constructor carries only `R i = rel g w'` (checked by `#print`),
    the trivial-group hypothesis being supplied by invariance along the way.

12. **Phase 9 (2026-09-14), see docs/PHASE9_PROMPT.md.** Discovery Track groundwork
    at zero compute. Research outcome: the pool's `uncertified` label means the
    literature reports a solution but no public replayable certificate exists. The
    Caltech ACSolverX repository publishes its datasets under CC BY 4.0, but those
    files are starting presentations; the solution paths are stored inside model
    checkpoints with no stated licence, and shehper/AC-Solver has no licence file.
    Harvesting was therefore dropped: no path enters a submission without a licence
    that permits it. Carreras's certificates are equivalences between presentations,
    not trivializations. Built: `tools/pool_index.py` (canonical form under relator
    order, rotation and inversion, the rule the data README states; 10,115 forms, no
    collisions, no training leak, 1,000/1,000 symmetry trials), and
    `tools/submission_builder.py` (verifies every candidate under both
    specifications from the pool's exact words, enforces the 500-line and 10 MB
    limits, writes a receipt; refuses non-pool starts and rotated starts).
    `tools/search_smoke.py` is a capped greedy baseline: 0/50 at 10,000 nodes in
    10 s and 130 MB, and 4/300 at the same budget in 58 s, all four accepted by the
    builder and written as eight lines (AC and Stable AC). The Discovery Track needs a
    real search stack and a compute budget; nothing here scores.

13. **Phase 10 (2026-09-14), see docs/PHASE10_PROMPT.md.** Referee pass. Added
    `Checks/NonVacuous.lean` (ten named witnesses, all within the three axioms; the
    violation of `Ascending` needs only `propext`), `tools/consistency.py` (which
    immediately caught the kernel-theorem count in the README lagging by twelve),
    `tools/ci_validate.py` (the embedded ledger check accepts a passing ledger and
    rejects a failing or incomplete one; every workflow tool exists with its flags),
    and a fresh-export run: a 2 MB copy of the tree without `lean/.lake` regenerates
    the table identically, passes the pool-index self-test, and fails closed on the
    missing binary with the expected message. Lean pitfall recorded: `simp`
    normalizes `Fin.succAbove 2 1` to `1` before `retract_of_succAbove` can fire, so
    concrete retraction facts are derived by `rw` on the lemma instance, not by
    `simpa`. Residual objections a referee could still raise: the family theorems
    rest on a normal-closure hypothesis that is a Prop, not decidable, so instances
    beyond the witnesses need a proof each; `checkEncodedAt_sound` trusts `parsePres`;
    the Discovery tooling has produced no score.
