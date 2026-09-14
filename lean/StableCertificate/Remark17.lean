import StableCertificate.Lemma11
import StableCertificate.Family

/-!
# The class of Remark 17

Shehper et al. (arXiv:2408.15332v2, Remark 17) consider the presentations obtained
from a Theorem 16 presentation by repeated substitution and removal. Here the base is
any conjugation tree and the steps are the official-relation form of Lemma 11; every
member of the class is stably trivial and presents the trivial group. Nothing is
claimed about ordinary AC-triviality of the class, which is their Conjecture 18.
-/

namespace AC.Lemma11

open AC AC.Chain

variable {n : ℕ}

theorem remark17_stableTrivial (p : Fin n → Fin n) (hp : Ascending p) (z : Fin n → Word n)
    (s : Fin n → Bool) {Q : Presentation} (h : Iterated ⟨n, tree p z s⟩ Q) :
    StableReachable Q ⟨Q.1, standard Q.1⟩ :=
  iterated_stableTrivial h (tree_stableReachable p hp z s)

theorem remark17_presentsTrivialGroup (p : Fin n → Fin n) (hp : Ascending p)
    (z : Fin n → Word n) (s : Fin n → Bool) {Q : Presentation} (h : Iterated ⟨n, tree p z s⟩ Q) :
    PresentsTrivialGroup Q.2 :=
  iterated_presentsTrivialGroup h (tree_stableReachable p hp z s)

end AC.Lemma11
