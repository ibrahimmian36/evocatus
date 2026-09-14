# Phase 7 prompt — Lemma 11, substitution and removal, as a stable-AC theorem

Written 2026-09-14 for github.com/ibrahimmian36/evocatus. Read all of it first.
Section 0 of docs/PHASE6_PROMPT.md (binding constraints: no submission, no AI
attribution, three axioms, one build at a time, no stray processes, no scratch
files in the repository, no overclaiming) applies unchanged.

## 1. The target

Lemma 11 of Shehper et al. (arXiv:2408.15332v2): if
`P = ⟨x₁…xₙ, y | r₁…rₙ, y⁻¹w⟩` presents the trivial group and `w` is a word in the
`x` alone, then `P` is stably AC-equivalent to `P' = ⟨x | r₁[w/y] … rₙ[w/y]⟩`.
It is the paper's only stable-specific lemma, the supermove that lowers rank, and
the tool behind the Remark 17 class. Their proof: substitute `w` for `y` (AC moves,
Definition 1), observe `P'` is trivial, write `w` as a product of conjugates of the
substituted relators, turn `y⁻¹w` into `y` with (AC1)–(AC3), remove `y` with (AC5).

Official-relation form to prove, with generator `g : Fin (n+1)` playing `y` and
relator index `i : Fin (n+1)` holding `y⁻¹w`, both at arbitrary positions:

```
theorem AC.Lemma11.substitution_removal (R : Relators (n+1)) (i g : Fin (n+1)) (w' : Word n)
    (hRi : R i = (FreeGroup.of g)⁻¹ * FreeGroup.map g.succAbove w')
    (htriv : PresentsTrivialGroup R) :
    StableReachable ⟨n+1, R⟩ ⟨n, fun j => retract g w' (R (i.succAbove j))⟩
```

where `retract g w' : Word (n+1) →* Word n := FreeGroup.lift (Fin.insertNth g w' FreeGroup.of)`
sends `y ↦ w'` and `x_j ↦ x_j`, i.e. performs the substitution and drops `y`.

## 2. Proof plan, each step a separate theorem

S1. `subst g w := (FreeGroup.map g.succAbove).comp (retract g w')`, so `subst` of any
    word lies in the image of `map g.succAbove` and agrees with `y ↦ w, x ↦ x` on
    generators (`retract_of_same`, `retract_of_succAbove`, `retract_map` = id).
S2. Congruence: for every word `r`, `r⁻¹ * subst g w r ∈ normalClosure {(of g)⁻¹ * w}`.
    Proof by `FreeGroup.ext_hom` on the two homomorphisms into the quotient, exactly
    as `GeneratorsCongruent.congr_all`.
S3. Substitution as AC moves: with `R i = (of g)⁻¹ * w`, the tuple
    `substituted R i g w' := fun j => if j = i then R i else subst g w (R j)` is
    `Reachable` from `R`. Induct over the list `(List.finRange (n+1)).filter (· ≠ i)`
    with the partial tuple `substOn L`, replacing one relator at a time by
    `Reachable.replace_of_mem_normalClosure`; the membership comes from S2 and
    `normalClosure_mono`, because `R i` is always among the other relators.
S4. Triviality transfers to the substituted rank-`n` tuple:
    `PresentsTrivialGroup (substituted …) → normalClosure (Set.range R'') = ⊤` for
    `R'' j := retract g w' (R (i.succAbove j))`. Apply `retract` with
    `map_mem_normalClosure_image`: it kills relator `i` (`w'⁻¹ w' = 1`) and maps the
    others onto `R''`; every generator `x_j` of `Word n` is `retract (of (g.succAbove j))`.
    `PresentsTrivialGroup R → PresentsTrivialGroup (substituted …)` is
    `Reachable.presentsTrivialGroup_iff` from S3.
S5. Hence `w' ∈ normalClosure (range R'')`, so `w = map g.succAbove w'` lies in the
    normal closure of the other relators of the substituted tuple
    (`map_mem_normalClosure_image` again). Replace relator `i` by `(of g)⁻¹` via
    `Reachable.replace_of_mem_normalClosure` (`(R i)⁻¹ * (of g)⁻¹ = w⁻¹`), then
    `Step.inv` gives relator `of g`.
S6. The resulting tuple equals `stabilize R'' g i` (`Fin.succAboveCases`, using
    `retract_map` on the substituted relators), so `StableStep.destabilize R'' g i`
    finishes. Compose S3, S5, S6.
S7. Corollaries: the symmetric statement (by `StableReachable.symm`); stable
    triviality transfers both ways between `P` and `P'`
    (`stableReachable_standard_iff_empty`, `standard_to_empty`); combined with
    `tree_stableReachable`, every presentation reached from a conjugation tree by
    repeated substitution-and-removal is stably trivial (state one iteration; do not
    formalize "repeated" unless it is a one-line induction).

## 3. Research

R1, before acting: re-read Lemma 11 and Definition 1 in the extracted text; confirm
`Fin.insertNth` applied lemmas, `FreeGroup.ext_hom`, `FreeGroup.lift`, `map.of`,
`QuotientGroup.eq`, `Subgroup.normalClosure_mono`, `List.finRange`, `List.filter`
membership lemmas at the pin by grep; check the Contributor Network and Sneiderman's
repository once more.
R2, after S1–S2 compile: confirm `subst` reduces on generators by `simp` alone; if
`Fin.insertNth_apply_succAbove` does not fire through `FreeGroup.lift`, add the two
`@[simp]` generator lemmas by hand before S3.
R3, after completion: statement audit of every name in README and the form draft;
prose scan; full suite; `pgrep`; scratch files; NOTES; memory.

## 4. Tests (tools/lemma11_tests.py, ledgered, seeded)

Instances are built from a known stably trivial base so certificates are explicit:
take a conjugation tree `T` at rank `n` (1 ≤ n ≤ 7), a word `w'` over its generators
(edge cases: empty, one letter, containing every generator, length up to 6), choose
`g` and `i` in `0..n` independently (edge cases: `g = 0`, `g = n`, `i = 0`, `i = n`,
`g = i`), and reverse-substitute: in some relators of `T` replace some occurrences
of the subword `w'` by `y`, including inverse occurrences, zero occurrences in some
relators, and several in one relator. The resulting rank-`(n+1)` presentation `P`
with relator `y⁻¹w` at index `i` is trivial by construction.
1. Extraction: `#eval` of the Lean `retract`-substituted tuple equals the Python
   forward substitution, byte for byte, for 120 instances.
2. Certificates: the official verifier accepts a path from `P` to the empty
   presentation built as: substitute `w` for each `y` occurrence (right-multiply by
   the conjugate `v⁻¹ (y⁻¹w)^{±1} v`, three moves per conjugate letter block),
   trivialize the tree relators with `y` present (rank `n+1` ids), kill the letters
   of `w` in `y⁻¹w` using the now standard relators, invert, destabilize `y` at
   position `g`, destabilize the rest. 120/120 must pass; 20 kernel-checked through
   `checkEncodedAt` at ranks up to 8.
3. Negative controls: a `P` whose `y⁻¹w` has `w` containing `y` must be rejected by
   the Lean statement's hypothesis (type-level: `w'` is over `Fin n`), and a `P`
   built from a nontrivial base (the braid witness) must be one the certificate
   builder refuses; record both.
4. Axiom gate on `substitution_removal` and its corollaries; negative controls.
5. Full suite green; CI green on the pushed commit.

## 5. Time boxes

R1 1 h → S1–S2 1 h → S3 2 h → S4 2 h → S5–S6 1.5 h → S7 0.5 h → tests 2 h → R3 1 h.
Stop and report if S3 or S4 exceeds its box by a factor of two; the fallback for S4
is to take `w' ∈ normalClosure (range R'')` as an explicit hypothesis and state the
theorem in that form, which is still Lemma 11's mechanism.
