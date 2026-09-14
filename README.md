# evocatus — kernel-checked Stable AC certificates against the official statement

A Lean 4 checker for the 257-move `sac-r8-v1` table of the SAIR Andrews–Curtis
Challenge, proved sound against the organizers' official `AC.StableStep` relation.
An accepted Stable AC certificate becomes a kernel-checked theorem

```lean
AC.StableReachable ⟨2, R⟩ ⟨2, AC.standard 2⟩
```

for the presentation `R` it starts from. Nothing here bears on either conjecture.

## What is proved

`lean/StableCertificate/Core.lean`, namespace `AC.Stable`:

| Name | Statement |
|---|---|
| `stab_sound` | move 14 is one official `StableStep.stabilize` at positions `(Fin.last k, Fin.last k)` |
| `destab_sound` | an accepted move 15–22 is one official `StableStep.destabilize`, with the executable relabelling shown to invert `g.succAbove` |
| `step_sound` | every accepted table row is an official `StableReachable` step (ordinary rows reuse the upstream `Move.sound`) |
| `check_sound` | `check R ids = true → StableReachable ⟨2, denote R⟩ ⟨2, standard 2⟩` |
| `checkEncoded_sound` | the same for the integer-encoded input the challenge uses |

The endpoint gap is bridged inside the proof: the Discovery verifier ends at the
empty presentation, the official conjecture ends at `⟨2, standard 2⟩`, and two
official stabilizations connect them (`empty_to_standard2`).

Three further modules prove facts about the official relations themselves.

`lean/StableCertificate/Official.lean` proves the claims that `AC.lean` states in
prose but leaves unproved: every ordinary and stable move can be undone by moves
(`Step.reverse`, `StableStep.reverse`), so `Reachable` and `StableReachable` are
equivalence relations (`Reachable.equivalence`, `StableReachable.equivalence`);
ending at `⟨n, standard n⟩` is equivalent to ending at the empty presentation
(`stableReachable_standard_iff_empty`, `stableConjecture_iff_empty`); and the
ordered endpoint adds nothing, since every relator permutation is reachable
(`stableReachable_standard_iff_permuted`).

`lean/StableCertificate/Invariance.lean` proves that presenting the trivial group is
invariant along stable paths (`StableReachable.presentsTrivialGroup_iff`), by showing
ordinary moves preserve the normal closure of the relators and stabilization
preserves the presented group. Consequences: anything stably reachable to a standard
tuple presents the trivial group, so the conjecture can be stated as a biconditional
(`stableConjecture_iff_forall_iff`), and every accepted certificate proves that its
starting presentation presents the trivial group (`checkEncoded_presentsTrivialGroup`).

`lean/StableCertificate/NormalClosure.lean` proves the mechanism behind the
substitution arguments of Shehper et al. (arXiv:2408.15332v2, Lemmas 11 and 15):
relator `i` may be right-multiplied by any element of the normal closure of the
other relators (`Reachable.mulRight_normalClosure`; each conjugate factor is three
official moves), hence replaced by any word congruent to it modulo that normal
closure, and Lemma 15 follows in its exact form (`Reachable.standard_of_congr_generator`).

`lean/StableCertificate/Chain.lean` and `Family.lean` prove an infinite family
AC-trivial at every rank: conjugation trees, whose relators say
`x_i = z_i x_{p(i)}^{±1} z_i⁻¹` for arbitrary words `z_i` and any parent function
with `i < p(i)`, with the last generator killed (`tree_reachable`, three official
moves per relator; chains are the case `p(i) = i+1`). The root relator may be
replaced by any word congruent to the root generator or its inverse modulo the
tree relators (`tree_with_root_reachable`, stably reachable, presents the trivial
group). This is the substitution step of Theorem 16 and Remark 17 without the
knot-diagram hypothesis. The congruence hypothesis cannot be weakened to
"exponent sum ±1" for general trees: the rank-2 chain with `z₁ = x₂x₁` is the braid
relation, and `corpus/braid_witness.json` records a word of exponent sum 1 in the
kernel of B₃ → SL(2,5), so that presentation is nontrivial.

`lean/StableCertificate/Conjecture19.lean` states Conjecture 19 of Shehper et al.
against the official definitions (relators of ℤ with every generator congruent to
`x_i^{±1}`, `x_i` of infinite order, any `w` of signed exponent sum ±1) and proves
that it reduces to the single case `w = x_i` (`conjecture19_reduction`,
`conjecture19_iff_generator`). Nothing beyond the reduction is claimed.

`lean/StableCertificate/AnyRank.lean` adds `checkEncodedAt`, a checker for
certificates starting at any rank, with `checkEncodedAt_sound`.

`lean/StableCertificate/Lemma11.lean` proves Lemma 11 of Shehper et al.,
substitution and removal, against the official stable relation: if
`⟨x₁,…,xₙ, y | r₁,…,rₙ, y⁻¹w⟩` presents the trivial group and `w` is a word in the
`x`, then it is stably reachable to `⟨x | r₁[w/y],…,rₙ[w/y]⟩`
(`Lemma11.substitution_removal`), with `y` at any generator position and `y⁻¹w` at
any relator index; stable triviality transfers both ways (`Lemma11.stableTrivial_iff`)
and the reduced presentation presents the trivial group. This is the paper's
stable-specific lemma, the supermove that lowers rank. The proof substitutes `w` for
`y` through the normal-closure lemma (each occurrence is congruence modulo `y⁻¹w`),
transfers triviality to the reduced tuple through the retraction `y ↦ w`, replaces
`y⁻¹w` by `y`, and removes the pair by one official destabilization. The iterated
class (`Lemma11.Iterated`, whose step carries only the syntactic hypothesis) is
stably trivial whenever its base is (`iterated_stableTrivial`); with a conjugation
tree as base this is the class of Remark 17 (`Remark17.lean`). Nothing is claimed
about ordinary AC-triviality of that class, which is their Conjecture 18.

Trust base: Lean 4.29.1, Mathlib `5e932f97`, the official `AC.lean` at commit
`a0fd6e6` unchanged (sha256 `927ba318…cfca1b`, asserted in CI), and the axioms
`propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`, no
`implemented_by` on the trusted path. The move table is generated from the
official `stable_move_spec.json` by `tools/gen_table.py`, never typed by hand, and
CI regenerates it and diffs.

## What is not claimed

* No progress on the ordinary or stable Andrews–Curtis conjecture.
* No resource limits. The Discovery verifier also rejects on path length, total
  relator length and work; this checker replays any finite path. A certificate
  accepted here may still be rejected by the Discovery Track for exceeding a limit.
* No equivalence claim. Agreement with the official verifier is tested, not proved.

## How it was tested

Every test is seeded and appends to `ledger/tests.jsonl`; a check that cannot
fail is not a check, and the axiom gate is run against a `sorry` and a
`native_decide` negative control that must both fail it.

| Test | Result |
|---|---|
| Table round trip: Lean rows re-serialized and diffed against the specification | 257/257 identical |
| Official golden vectors (33 verify vectors) | 27/27 comparable vectors agree on verdict, code, reason and index; 6 recorded with no analogue (spec mismatch and the three resource limits) |
| Move-by-move differential fuzz against `stable_core.apply_move`, ranks 2–8, ids −3…260 | 200,000 cases (two seeds), 0 disagreements |
| Training corpus | 424/424 Stable AC and 424/424 AC paths accepted by both implementations |
| Generated corpus: loops through ranks up to 8 with non-final destabilizations and translated undo | 400/400 accepted by the official verifier and by the checker; all 257 ids exercised |
| One-move mutations (replace, delete, insert, transpose) of every accepted path | 3,296 mutants, 3,296 agreements, 469 accepted by both |
| Kernel theorems (`decide +kernel`) | 46 certificates: 6 golden, 20 training, 20 generated; up to 161 moves and rank 8; longest 2.96 s wall including imports |
| Conjugation-tree family (`tools/family_tests.py`) | 120 random and forced instances at ranks 1–8 (chains, stars, random trees, `z` containing `x_i` and `x_{p(i)}`, all-negative signs): Lean `#eval` of `tree` equals the independent Python construction 120/120; the extracted three-moves-per-relator certificates are accepted by the official verifier 120/120 and 20 are kernel-checked through `checkEncodedAt` (up to rank 8, 73 moves); the braid witness and a rank-2 instance of the normal-closure mechanism are verified and kernel-checked |
| Substitution and removal (`tools/lemma11_tests.py`) | 120 instances built by reverse substitution from conjugation trees at ranks 2–8, with `y` and `y⁻¹w` at independent positions including the corners and `g = i`, `w` empty, one letter, or containing every generator, and inverse and repeated occurrences: Lean `reduced` equals the tree 120/120; explicit certificates (substitute back, trivialize, kill `w`, invert, destabilize at position `g`) accepted by the official verifier 120/120, 20 kernel-checked; negative controls recorded |
| Boundary theorems (`lean/Checks/Edge.lean`) | ranks 0 and 1 of chains, trees and Lemma 11; the decoder's block edges 0, 13, 14, 15, 16, 17, 22, 23, 137, 256, 257 accepted or rejected at the ranks where the specification says so, as kernel-checked theorems |
| Front-end fuzz (`tools/exe_fuzz.py`) | 35 hostile lines (invalid JSON, missing fields, letters 0 or out of rank, floats, booleans, ids −1, 257 and 2⁶², a 100,000-move list, a 1 MB line): one JSON reply each and the process still answers afterwards; 2,000 edge queries at ranks 0–10 agree with `stable_core.apply_move`; peak memory 85 MB |
| Axiom gate | 29 named theorems and all 86 kernel theorems within the three axioms; negative controls fail as required |

Timings are in `ledger/kernel_timings.json`; machine requirements are in
`docs/NOTES.md` (under 2 GB of memory once the Mathlib cache is present). Compiled
replay is linear in path length; a 5,000-move path replays in 0.2 s.

## Check it yourself

```sh
git clone https://github.com/SAIRcompetition/Andrews-Curtis.git official && git -C official checkout a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e
cd lean && lake exe cache get && lake build StableCertificate Checks stablecheck && cd ..
ACC_OFFICIAL=$PWD/official tools/run_all.sh
```

The second line builds the library, every kernel theorem under `lean/Checks/`, and
the `stablecheck` executable the tests drive; `#print axioms` output appears in the
build log. The third line runs the whole table above and the axiom gate.

## Layout

| Path | Contents |
|---|---|
| `lean/StableCertificate/Row.lean` | the five row kinds and their canonical JSON |
| `lean/StableCertificate/Table.lean` | generated: the 257 frozen rows |
| `lean/StableCertificate/Core.lean` | executable moves, decoder, replay, soundness theorems |
| `lean/StableCertificate/Encode.lean` | untrusted integer encoding at every rank, for the tests |
| `lean/StableCertificate/Official.lean` | symmetry, equivalence, endpoint and permutation lemmas for the official relations |
| `lean/StableCertificate/Invariance.lean` | the presented group is invariant along stable paths |
| `lean/StableCertificate/NormalClosure.lean` | relators may be multiplied by the normal closure of the others; Lemma 15 |
| `lean/StableCertificate/Chain.lean`, `Family.lean` | conjugation trees are AC-trivial at every rank; arbitrary root relator |
| `lean/StableCertificate/Conjecture19.lean` | Conjecture 19 stated against the official definitions and reduced to `w = x_i` |
| `lean/StableCertificate/AnyRank.lean` | certificates from any starting rank |
| `lean/StableCertificate/Lemma11.lean` | substitution and removal (Lemma 11) against the official stable relation; the iterated class |
| `lean/StableCertificate/Remark17.lean` | the Remark 17 class over a conjugation tree is stably trivial |
| `docs/AUDIT.md` | every claim sentence mapped to its theorem, hypotheses and test |
| `lean/Main.lean` | `stablecheck`, a line-oriented JSON front end |
| `lean/Checks/` | kernel-checked certificates and boundary theorems; `Checks/Kernel/` is generated |
| `tools/` | table generator, differential tests, corpus generator, kernel suite, axiom gate |
| `corpus/generated.jsonl` | the 400 generated certificates with official receipts |
| `ledger/` | append-only test ledger, golden details, kernel timings |
| `docs/` | Phase 0 memo, build notes, the SAIR form draft, the AK(3) note |

## Discovery Track tools

`tools/pool_index.py` canonicalizes the 10,115 pool presentations under the
official matching rule and checks itself; `tools/submission_builder.py` turns
`(presentation, moves)` pairs into a `submission.txt` in which every line was
verified by the official verifier from the pool's exact words, with a receipt for
refused candidates; `tools/search_smoke.py` is a capped greedy baseline. These
produce no score by themselves; they exist so that any future search result is
attributed, verified and formatted correctly before an upload.

## Built on

Robert Sneiderman's `ac-square-divisibility` (Apache-2.0, commit `d0ed2c0`) is a
Lake dependency and supplies the unchanged official `AC` module, the ordinary-move
checker with `Move.sound`, and the stable lemmas in `ACDeferral`. The official
challenge repository (Apache-2.0, commit `a0fd6e6`) supplies the statement, the
specification and the reference verifier. See `NOTICE`.

## License

Apache-2.0. Contact: ibrahimnmian@gmail.com.
