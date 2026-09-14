# Note on the stable status of AK(3) — two drafts, one to be chosen by Ibrahim

Both versions state only what the sources say. Neither says that AK(3) is or is not
stably AC-trivial, that anyone erred, or that we found anything. Shehper et al.
found and corrected the issue themselves; credit goes to them first.

Sources, all read on 2026-09-13:

- Shehper, Medina-Mardones, Fagan, Lewandowski, Gruen, Qiu, Kucharski, Wang, Gukov,
  "What makes math problems hard for reinforcement learning: a case study",
  arXiv:2408.15332. v1 (2024-08-27), abstract: AK(3) is stably AC-trivial.
  v2 (2025-02-11), introduction: a misprint in [MMS02, p.10] undermines the claim
  that presentation (1) is stably AC-trivial; Remark 14 and Appendix F give the
  details and the 53-move AC path from (1) to AK(3), and state that such
  presentations are not necessarily stably AC-trivial.
- Myasnikov, Myasnikov, Shpilrain, "On the Andrews–Curtis equivalence",
  arXiv:math/0302080 (MMS02).
- Lisitsa, "Stable Andrews-Curtis trivialization of AK(3) revisited. A case study
  using automated deduction", arXiv:2501.18601 (2025-01-17); Journal of
  Computational Algebra 16 (2025) 100041. Gives automated-deduction proofs of the
  AC-equivalence between the MMS02 presentation and AK(3); its stable-triviality
  conclusion rests on MMS02. The arXiv version predates Shehper v2 by 25 days.
  Whether the journal text was updated could not be checked from here.
- shehper/AC-Solver README and notebooks/Stable-AK3.ipynb still state the v1 claim
  (last commit 2025-08-11).
- The challenge scores sac-00399, which is AK(3) up to rotation and inversion, as
  an open instance.

## Version A — paragraph for the SAIR description (about 900 characters)

**On AK(3).** The pool lists AK(3) as sac-00399. A 2024 preprint (Shehper et al.,
arXiv:2408.15332v1) stated that AK(3) is stably AC-trivial; the authors withdrew
that statement in v2 (February 2025), tracing it to a misprint in the 13th relator
of the Wirtinger presentation in Myasnikov–Myasnikov–Shpilrain (2003) and noting in
Appendix F that the presentations involved are not necessarily stably AC-trivial.
Lisitsa's independent automated-deduction paper (arXiv:2501.18601, January 2025)
re-derives the AC-equivalence to AK(3) and inherits the stable step from the same
source. Some later citations and the AC-Solver repository still carry the v1
wording. As far as we can tell, no public replayable stable certificate for AK(3)
exists, and the challenge correctly scores it as unsolved. If one appears, the
checker here turns it into a kernel theorem `StableReachable ⟨2, AK(3)⟩ ⟨2, standard 2⟩`.

## Version B — no paragraph in the description

The description says nothing about AK(3). The repository README carries one
sentence: "The pool includes AK(3) as sac-00399; the status of its stable
trivialization is discussed in the literature (arXiv:2408.15332v2, Appendix F)."

## Choosing

Version A helps the correction propagate and is fair to every party. Its risk is
that a co-organizer is a co-author of the corrected preprint; the paragraph is
written so that it reads as citing their own correction, which it is. Version B
avoids the topic entirely. The choice is Ibrahim's.
