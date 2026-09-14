import ACCertificate
import StableCertificate.Official
import Mathlib.Tactic.Group

/-!
# Multiplying a relator by the normal closure of the others

The substitution arguments of Shehper et al. (arXiv:2408.15332v2, Lemma 11 and
Lemma 15) rest on one mechanism: a relator may be multiplied by any product of
conjugates of the other relators, because each such factor is three official moves
(conjugate the other relator, multiply, conjugate it back). This module proves the
mechanism in full against `AC.Reachable`: relator `i` may be right-multiplied by any
element of the normal closure of the other relators, and hence replaced by any word
congruent to it modulo that normal closure. Lemma 15 follows in its exact form.
-/

namespace AC

open Subgroup

variable {n : ℕ}

/-- The relators other than the `i`-th, as a set of words. -/
def others (R : Relators n) (i : Fin n) : Set (Word n) := {w | ∃ j, j ≠ i ∧ R j = w}

theorem mem_others (R : Relators n) {i j : Fin n} (hj : j ≠ i) : R j ∈ others R i :=
  ⟨j, hj, rfl⟩

theorem others_update (R : Relators n) (i : Fin n) (w : Word n) :
    others (Function.update R i w) i = others R i := by
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, by simp [Function.update_of_ne hj]⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, by simp [Function.update_of_ne hj]⟩

/-- Right-multiplying relator `i` by a conjugate of relator `j` is three official moves. -/
theorem Reachable.mulRight_conj (R : Relators n) {i j : Fin n} (hij : i ≠ j) (g : Word n) :
    Reachable R (Function.update R i (R i * (g * R j * g⁻¹))) := by
  set R1 := Function.update R j (g * R j * g⁻¹) with hR1
  set R2 := Function.update R1 i (R1 i * R1 j) with hR2
  set R3 := Function.update R2 j (g⁻¹ * R2 j * g⁻¹⁻¹) with hR3
  have h1 : Step R R1 := Step.conj R j g
  have h2 : Step R1 R2 := Step.mulRight R1 i j hij
  have h3 : Step R2 R3 := Step.conj R2 j g⁻¹
  have heq : R3 = Function.update R i (R i * (g * R j * g⁻¹)) := by
    ext k
    by_cases hk : k = i
    · subst hk
      simp [hR3, hR2, hR1, hij, hij.symm]
    · by_cases hk' : k = j
      · subst hk'
        simp [hR3, hR2, hR1, hij, hij.symm, mul_assoc]
      · simp [hR3, hR2, hR1, hk, hk']
  rw [← heq]
  exact ((Reachable.single h1).trans (Reachable.single h2)).trans (Reachable.single h3)

/-- Relator `i` may be right-multiplied by any element of the normal closure of the
other relators. -/
theorem Reachable.mulRight_normalClosure (R : Relators n) (i : Fin n) {v : Word n}
    (hv : v ∈ normalClosure (others R i)) :
    Reachable R (Function.update R i (R i * v)) := by
  have key : ∀ u : Word n,
      Reachable (Function.update R i u) (Function.update R i (u * v)) := by
    unfold normalClosure at hv
    induction hv using Subgroup.closure_induction with
    | mem x hx =>
      intro u
      obtain ⟨a, ⟨j, hj, rfl⟩, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
      have := Reachable.mulRight_conj (Function.update R i u) (Ne.symm hj) g
      simpa [Function.update_of_ne hj] using this
    | one =>
      intro u
      rw [mul_one]
      exact Reachable.refl _
    | mul x y _ _ hx hy =>
      intro u
      rw [← mul_assoc]
      exact (hx u).trans (hy (u * x))
    | inv x _ hx =>
      intro u
      have := hx (u * x⁻¹)
      rw [inv_mul_cancel_right] at this
      exact this.symm
  simpa using key (R i)

/-- Relator `i` may be replaced by any word congruent to it modulo the normal closure
of the other relators. -/
theorem Reachable.replace_of_mem_normalClosure (R : Relators n) (i : Fin n) {w : Word n}
    (hw : (R i)⁻¹ * w ∈ normalClosure (others R i)) :
    Reachable R (Function.update R i w) := by
  have := Reachable.mulRight_normalClosure R i hw
  simpa using this

/-- Lemma 15 of Shehper et al., in its exact form: if relator `i` is congruent to a
generator or its inverse modulo the other relators, and the presentation with that
generator in slot `i` is AC-trivial, then so is the original presentation. -/
theorem Reachable.standard_of_congr_generator (R : Relators n) (i g : Fin n) (e : ℤ)
    (he : e = 1 ∨ e = -1)
    (hw : (R i)⁻¹ * (FreeGroup.of g) ^ e ∈ normalClosure (others R i))
    (hstd : Reachable (Function.update R i (FreeGroup.of g)) (standard n)) :
    Reachable R (standard n) := by
  have h1 := Reachable.replace_of_mem_normalClosure R i hw
  rcases he with rfl | rfl
  · rw [zpow_one] at h1
    exact h1.trans hstd
  · have h2 : Reachable (Function.update R i ((FreeGroup.of g) ^ (-1 : ℤ)))
        (Function.update R i (FreeGroup.of g)) := by
      have := Reachable.single (Step.inv (Function.update R i ((FreeGroup.of g) ^ (-1 : ℤ))) i)
      simpa [Function.update_idem] using this
    exact (h1.trans h2).trans hstd

end AC
