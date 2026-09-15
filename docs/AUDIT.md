# Claim audit

One row per sentence in README.md and in the Contributor Network description that asserts a result.
Hypotheses are stated in words; the test column names the ledger record that
exercises the statement. A row is open if the prose outruns the theorem. Open rows: 0.

| Claim (prose) | Theorem | Hypotheses | Test |
|---|---|---|---|
| Accepted stable certificate gives `StableReachable ⟨2, R⟩ ⟨2, standard 2⟩` | `AC.Stable.checkEncoded_sound` | `checkEncoded words ids = true`; parser is the upstream rank-2 `parseTuple` | golden_vectors, training_stable, generated_paths, kernel_theorems |
| Move 14 is one official stabilization at positions `(last, last)` | `AC.Stable.stab_sound` | none | fuzz_step (accept cases of id 14) |
| Accepted moves 15–22 are one official destabilization | `AC.Stable.destab_sound` | `destabApply S i = some R` | fuzz_step, generated_paths (367 non-final destabilizations) |
| Every accepted table row is an official stable step | `AC.Stable.step_sound` | `step P id = .ok Q` | fuzz_step, table_roundtrip |
| Endpoint gap bridged by two stabilizations | `AC.Stable.empty_to_standard2`, `AC.empty_to_standard` | none | kernel_theorems (all end at the empty presentation) |
| Certificates from any rank | `AC.Stable.checkEncodedAt_sound` | `checkEncodedAt words ids = true`; parser `parsePres` is part of the statement | family_kernel, lemma11_kernel |
| Every ordinary and stable move can be undone by moves | `AC.Step.reverse`, `AC.StableStep.reverse` | none | mutations (accept/reject agreement only) |
| Both reachability relations are equivalence relations | `AC.Reachable.equivalence`, `AC.StableReachable.equivalence` | none | — (structural) |
| Standard endpoint equivalent to empty endpoint; conjecture unchanged | `AC.stableReachable_standard_iff_empty`, `AC.stableConjecture_iff_empty` | none | — |
| Ordered endpoint adds nothing (permutations reachable) | `AC.stableReachable_standard_iff_permuted` | none | — |
| Presenting the trivial group is invariant along stable paths | `AC.StableReachable.presentsTrivialGroup_iff` | none | — |
| Conjecture equivalent to a biconditional | `AC.stableConjecture_iff_forall_iff` | none | — |
| Accepted certificate proves the start presents the trivial group | `AC.Stable.checkEncoded_presentsTrivialGroup` | `checkEncoded words ids = true` | — |
| Relator may be multiplied by the normal closure of the others | `AC.Reachable.mulRight_normalClosure` | `v ∈ normalClosure (others R i)` | normal_closure_mechanism_rank2 |
| Lemma 15 in exact form | `AC.Reachable.standard_of_congr_generator` | `e = ±1`; `(R i)⁻¹ * x_g^e` in the normal closure of the others; `update R i x_g` AC-trivial | — |
| Conjugation trees AC-trivial at every rank, three moves per relator | `AC.Chain.tree_reachable` | `Ascending p` (`i < p i` off the root) | family_extraction, family_paths, family_kernel |
| Root relator may be any word congruent to `x_root^{±1}` | `AC.Chain.tree_with_root_reachable` | as above plus `w⁻¹ * x_root^e` in the normal closure of the tree relators, `e = ±1` | — (hypothesis is a normal-closure membership) |
| Exponent-sum form fails for general trees | corpus/braid_witness.json (computation, not a theorem) | B₃ → SL(2,5) with the stated matrices | braid_witness_recorded |
| Conjecture 19 stated and reduced to `w = x_i` | `AC.Conjecture19`, `AC.conjecture19_reduction`, `AC.conjecture19_iff_generator` | `GeneratorsCongruent R i ε`; for the iff also `InfiniteOrderMod R i` | — |
| Lemma 11: substitution and removal, any positions | `AC.Lemma11.substitution_removal` | `R i = rel g w'`; `PresentsTrivialGroup R` | lemma11_extraction, lemma11_certificates, lemma11_kernel |
| Stable triviality transfers both ways across the lemma | `AC.Lemma11.stableTrivial_iff` | same | — |
| Iterated class stably trivial; Remark 17 class over a tree | `AC.Lemma11.iterated_stableTrivial`, `AC.Lemma11.remark17_stableTrivial` | base stably trivial; steps carry only `R i = rel g w'` | — |
| No resource limits, no equivalence with the reference verifier | (scope statement) | — | golden_vectors records the 6 no-analogue vectors |

Sentences checked and found not to outrun their theorems: 2026-09-14.
