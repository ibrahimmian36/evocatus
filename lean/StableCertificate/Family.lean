import StableCertificate.Chain
import StableCertificate.NormalClosure
import StableCertificate.Invariance

/-!
# Conjugation trees with an arbitrary root relator

Theorem 16 of Shehper et al. allows the last relator to be any word `w` of exponent
sum ±1, for Wirtinger presentations of unknot diagrams, where the other relators
present ℤ. For general conjugation trees that hypothesis is not automatic: the
rank-2 chain with `z₁ = x₂x₁` is the braid relation, and B₃ has nontrivial perfect
quotients, so some words of exponent sum 1 give nontrivial groups (see
docs/NOTES.md). The correct general hypothesis is that `w` is congruent to the root
generator or its inverse modulo the tree relators; under it the presentation is
AC-trivial, stably trivial, and presents the trivial group.
-/

namespace AC.Chain

open AC Subgroup

variable {n : ℕ}

/-- The root index `n - 1`. -/
def root (n : ℕ) (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

theorem tree_root (p : Fin n → Fin n) (z : Fin n → Word n) (s : Fin n → Bool) (hn : 0 < n) :
    tree p z s (root n hn) = FreeGroup.of (root n hn) := by
  have h2 : ¬ ((root n hn).val + 1 < n) := by
    show ¬ (n - 1 + 1 < n)
    omega
  simp [tree, upTo, h2]

/-- A conjugation tree whose root relator is replaced by any word congruent to the
root generator or its inverse modulo the tree relators is AC-trivial. -/
theorem tree_with_root_reachable (p : Fin n → Fin n) (hp : Ascending p) (z : Fin n → Word n)
    (s : Fin n → Bool) (hn : 0 < n) (w : Word n) (e : ℤ) (he : e = 1 ∨ e = -1)
    (hw : w⁻¹ * (FreeGroup.of (root n hn)) ^ e ∈
      normalClosure (others (tree p z s) (root n hn))) :
    Reachable (Function.update (tree p z s) (root n hn) w) (standard n) := by
  apply Reachable.standard_of_congr_generator _ (root n hn) (root n hn) e he
  · rw [Function.update_self, others_update]; exact hw
  · rw [Function.update_idem, ← tree_root p z s hn, Function.update_eq_self]
    exact tree_reachable p hp z s

theorem tree_with_root_stableReachable (p : Fin n → Fin n) (hp : Ascending p)
    (z : Fin n → Word n) (s : Fin n → Bool) (hn : 0 < n) (w : Word n) (e : ℤ)
    (he : e = 1 ∨ e = -1)
    (hw : w⁻¹ * (FreeGroup.of (root n hn)) ^ e ∈
      normalClosure (others (tree p z s) (root n hn))) :
    StableReachable ⟨n, Function.update (tree p z s) (root n hn) w⟩ ⟨n, standard n⟩ :=
  (tree_with_root_reachable p hp z s hn w e he hw).stable

theorem tree_with_root_presentsTrivialGroup (p : Fin n → Fin n) (hp : Ascending p)
    (z : Fin n → Word n) (s : Fin n → Bool) (hn : 0 < n) (w : Word n) (e : ℤ)
    (he : e = 1 ∨ e = -1)
    (hw : w⁻¹ * (FreeGroup.of (root n hn)) ^ e ∈
      normalClosure (others (tree p z s) (root n hn))) :
    PresentsTrivialGroup (Function.update (tree p z s) (root n hn) w) :=
  presentsTrivialGroup_of_stableReachable_standard
    (tree_with_root_stableReachable p hp z s hn w e he hw)

end AC.Chain
