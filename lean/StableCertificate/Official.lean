import ACCertificate

/-!
# Facts about the official relations that `AC.lean` states but does not prove

The official file's docstrings assert that every move can be undone, that
reachability is an equivalence relation, and that the stable conjecture may
equivalently end at the empty presentation. This module proves those claims
against the unchanged definitions, so that they need not be taken on trust by
anyone stating a result in terms of `AC.StableReachable`.
-/

namespace AC

open AC.Certificate

variable {n : ℕ}

/-! ## Every ordinary move can be undone by ordinary moves. -/

/-- Inversion is its own inverse. -/
theorem Step.inv_reverse (R : Relators n) (i : Fin n) :
    Reachable (Function.update R i (R i)⁻¹) R := by
  have heq : Function.update (Function.update R i (R i)⁻¹) i
      ((Function.update R i (R i)⁻¹) i)⁻¹ = R := by
    ext k
    by_cases hk : k = i
    · subst k; simp
    · simp [hk]
  simpa [heq] using Reachable.single (Step.inv (Function.update R i (R i)⁻¹) i)

/-- Right multiplication is undone by right multiplication by the inverse, which is
three official steps. -/
theorem Step.mulRight_reverse (R : Relators n) (i j : Fin n) (hij : i ≠ j) :
    Reachable (Function.update R i (R i * R j)) R := by
  set S := Function.update R i (R i * R j) with hS
  have heq : Function.update S i (S i * (S j)⁻¹) = R := by
    ext k
    by_cases hk : k = i
    · subst k; simp [hS, hij.symm, mul_assoc]
    · simp [hS, hk]
  have := (Steps.mulInvRight S i j hij).reachable
  rwa [heq] at this

/-- Conjugation by `w` is undone by conjugation by `w⁻¹`. -/
theorem Step.conj_reverse (R : Relators n) (i : Fin n) (w : Word n) :
    Reachable (Function.update R i (w * R i * w⁻¹)) R := by
  set S := Function.update R i (w * R i * w⁻¹) with hS
  have heq : Function.update S i (w⁻¹ * S i * w) = R := by
    ext k
    by_cases hk : k = i
    · subst k; simp [hS, mul_assoc]
    · simp [hS, hk]
  have h := Reachable.single (Step.conj S i w⁻¹)
  rw [inv_inv, heq] at h
  exact h

theorem Step.reverse {R S : Relators n} (h : Step R S) : Reachable S R := by
  cases h with
  | inv i => exact Step.inv_reverse R i
  | mulRight i j hij => exact Step.mulRight_reverse R i j hij
  | conj i w => exact Step.conj_reverse R i w

/-- Ordinary reachability is symmetric, hence an equivalence relation. -/
theorem Reachable.symm {R S : Relators n} (h : Reachable R S) : Reachable S R := by
  induction h with
  | refl => exact Reachable.refl _
  | tail _ step ih => exact step.reverse.trans ih

theorem Reachable.equivalence : Equivalence (Reachable (n := n)) :=
  ⟨Reachable.refl, Reachable.symm, Reachable.trans⟩

/-! ## Every stable move can be undone by stable moves. -/

theorem StableReachable.refl (P : Presentation) : StableReachable P P :=
  Relation.ReflTransGen.refl

theorem StableReachable.trans {P Q T : Presentation} (h : StableReachable P Q)
    (h' : StableReachable Q T) : StableReachable P T :=
  Relation.ReflTransGen.trans h h'

theorem StableStep.reverse {P Q : Presentation} (h : StableStep P Q) : StableReachable Q P := by
  cases h with
  | ac h => exact h.reverse.stable
  | stabilize R g i => exact Relation.ReflTransGen.single (StableStep.destabilize R g i)
  | destabilize R g i => exact Relation.ReflTransGen.single (StableStep.stabilize R g i)

/-- Stable reachability is symmetric, hence an equivalence relation. -/
theorem StableReachable.symm {P Q : Presentation} (h : StableReachable P Q) :
    StableReachable Q P := by
  induction h with
  | refl => exact StableReachable.refl _
  | tail _ step ih => exact step.reverse.trans ih

theorem StableReachable.equivalence : Equivalence StableReachable :=
  ⟨StableReachable.refl, StableReachable.symm, StableReachable.trans⟩

/-- Two stably trivial presentations of the same rank are stably equivalent. -/
theorem StableReachable.of_both_standard {R S : Relators n}
    (hR : StableReachable ⟨n, R⟩ ⟨n, standard n⟩) (hS : StableReachable ⟨n, S⟩ ⟨n, standard n⟩) :
    StableReachable ⟨n, R⟩ ⟨n, S⟩ :=
  hR.trans hS.symm

/-! ## The standard tuple of any rank and the empty presentation are stably equivalent. -/

theorem standard_to_empty (n : ℕ) : StableReachable ⟨n, standard n⟩ ⟨0, standard 0⟩ :=
  (NoAddReachable.standard_to_empty n).toStable

theorem empty_to_standard (n : ℕ) : StableReachable ⟨0, standard 0⟩ ⟨n, standard n⟩ := by
  induction n with
  | zero => exact StableReachable.refl _
  | succ n ih =>
    exact ih.tail (by simpa using StableStep.stabilize (standard n) (Fin.last n) (Fin.last n))

/-- Ending at the official endpoint `⟨n, standard n⟩` is the same as ending at the
empty presentation, as the official docstring claims. -/
theorem stableReachable_standard_iff_empty (R : Relators n) :
    StableReachable ⟨n, R⟩ ⟨n, standard n⟩ ↔ StableReachable ⟨n, R⟩ ⟨0, standard 0⟩ :=
  ⟨fun h => h.trans (standard_to_empty n), fun h => h.trans (empty_to_standard n)⟩

/-- The stable conjecture with the empty presentation as endpoint. -/
def StableConjectureEmpty : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (R : Relators n),
    PresentsTrivialGroup R → StableReachable ⟨n, R⟩ ⟨0, standard 0⟩

theorem stableConjecture_iff_empty : StableConjecture ↔ StableConjectureEmpty :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun R => forall_congr' fun _ =>
    stableReachable_standard_iff_empty R

/-! ## The ordered endpoint adds no restriction: any relator permutation is reachable. -/

theorem StableReachable.permute (R : Relators n) (σ : Equiv.Perm (Fin n)) :
    StableReachable ⟨n, R⟩ ⟨n, R ∘ σ⟩ :=
  (Reachable.permute R σ).stable

theorem stableReachable_standard_iff_permuted (R : Relators n) (σ : Equiv.Perm (Fin n)) :
    StableReachable ⟨n, R⟩ ⟨n, standard n⟩ ↔ StableReachable ⟨n, R⟩ ⟨n, standard n ∘ σ⟩ :=
  ⟨fun h => h.trans (StableReachable.permute _ σ),
   fun h => h.trans (StableReachable.permute _ σ).symm⟩

/-- A counterexample witnesses the failure of a symmetric relation, so it is also a
counterexample when the direction of the path is reversed. -/
theorem IsStableCounterexample.iff_reverse (R : Relators n) :
    IsStableCounterexample R ↔
      PresentsTrivialGroup R ∧ ¬ StableReachable ⟨n, standard n⟩ ⟨n, R⟩ := by
  unfold IsStableCounterexample
  constructor
  · rintro ⟨h, hn⟩; exact ⟨h, fun hr => hn hr.symm⟩
  · rintro ⟨h, hn⟩; exact ⟨h, fun hr => hn hr.symm⟩

end AC
