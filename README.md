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
| Axiom gate | five soundness theorems and all 46 kernel theorems within the three axioms; negative controls fail as required |

Timings are in `ledger/kernel_timings.json`. The official verifier's compiled
replay is linear in path length; a 5,000-move path replays in 0.03 s.

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
| `lean/Main.lean` | `stablecheck`, a line-oriented JSON front end |
| `lean/Checks/` | kernel-checked certificates; `Checks/Kernel/` is generated |
| `tools/` | table generator, differential tests, corpus generator, kernel suite, axiom gate |
| `corpus/generated.jsonl` | the 400 generated certificates with official receipts |
| `ledger/` | append-only test ledger, golden details, kernel timings |
| `docs/` | Phase 0 memo, build notes, the SAIR form draft, the AK(3) note |

## Built on

Robert Sneiderman's `ac-square-divisibility` (Apache-2.0, commit `d0ed2c0`) is a
Lake dependency and supplies the unchanged official `AC` module, the ordinary-move
checker with `Move.sound`, and the stable lemmas in `ACDeferral`. The official
challenge repository (Apache-2.0, commit `a0fd6e6`) supplies the statement, the
specification and the reference verifier. See `NOTICE`.

## License

Apache-2.0. Contact: ibrahimnmian@gmail.com.
