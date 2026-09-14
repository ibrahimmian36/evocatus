import ACCertificate
import StableCertificate.Official
import Mathlib.Tactic.Group

/-!
# Conjugation chains are AC-trivial at every rank

Shehper et al. (arXiv:2408.15332v2, Theorem 16 and Remark 17) observe that a
balanced presentation whose relators say `x_i = z_i x_{i+1}^{±1} z_i^{-1}` for
arbitrary words `z_i`, with the last generator killed by the last relator, is
trivialized by substituting the last generator and iterating. Their statement is
about Wirtinger presentations of unknot diagrams; the argument only uses the chain
shape. This module proves the chain shape AC-trivial against the official
`AC.Reachable`, for every rank and every choice of conjugating words and signs.
Three official moves per relator: conjugate by `z_i⁻¹`, right-multiply by the
(already standard) next relator or its inverse, conjugate by `z_i`.
-/

namespace AC.Chain

open AC AC.Certificate

variable {n : ℕ}

/-- `x_{i+1}` or its inverse, according to the sign. -/
def signed (x : Word n) : Bool → Word n
  | true => x⁻¹
  | false => x

/-- Relators `0 ≤ i < m` in chain form (when `i + 1 < n`), all others standard. -/
def upTo (z : Fin n → Word n) (s : Fin n → Bool) (m : ℕ) : Relators n := fun i =>
  if h : i.val < m ∧ i.val + 1 < n then
    FreeGroup.of i * z i * signed (FreeGroup.of ⟨i.val + 1, h.2⟩) (s i) * (z i)⁻¹
  else FreeGroup.of i

/-- The conjugation chain: relator `i` is `x_i z_i x_{i+1}^{±1} z_i⁻¹`, and the last
relator is `x_{n-1}`. -/
def chain (z : Fin n → Word n) (s : Fin n → Bool) : Relators n := upTo z s n

theorem upTo_zero (z : Fin n → Word n) (s : Fin n → Bool) : upTo z s 0 = standard n := by
  funext i
  simp [upTo, standard]

/-- Chain relators of index at least `m` agree between `upTo (m+1)` and `upTo m` except at `m`. -/
theorem upTo_succ_of_ne (z : Fin n → Word n) (s : Fin n → Bool) (m : ℕ) (k : Fin n)
    (hk : k.val ≠ m) : upTo z s (m + 1) k = upTo z s m k := by
  unfold upTo
  have : (k.val < m + 1 ∧ k.val + 1 < n) ↔ (k.val < m ∧ k.val + 1 < n) := by omega
  simp only [this]

/-- One relator is trivialized by three official moves. -/
theorem upTo_step (z : Fin n → Word n) (s : Fin n → Bool) (m : ℕ) (hm : m + 1 < n) :
    Reachable (upTo z s (m + 1)) (upTo z s m) := by
  set R := upTo z s (m + 1) with hR
  let mi : Fin n := ⟨m, by omega⟩
  let mi1 : Fin n := ⟨m + 1, hm⟩
  have hne : mi ≠ mi1 := fun h => by simp [mi, mi1, Fin.ext_iff] at h
  have hRm : R mi = FreeGroup.of mi * z mi * signed (FreeGroup.of mi1) (s mi) * (z mi)⁻¹ := by
    simp [hR, upTo, mi, mi1, hm]
  have hRm1 : R mi1 = FreeGroup.of mi1 := by
    simp [hR, upTo, mi1]
  -- step 1: conjugate by z⁻¹
  set R1 := Function.update R mi ((z mi)⁻¹ * R mi * (z mi)⁻¹⁻¹) with hR1
  have s1 : Step R R1 := Step.conj R mi (z mi)⁻¹
  have hR1m : R1 mi = (z mi)⁻¹ * FreeGroup.of mi * z mi * signed (FreeGroup.of mi1) (s mi) := by
    simp only [hR1, Function.update_self, hRm]
    group
  have hR1m1 : R1 mi1 = FreeGroup.of mi1 := by
    simp [hR1, Function.update_of_ne hne.symm, hRm1]
  -- step 2: multiply by the next relator or its inverse, so that x_{m+1} cancels
  have step2 : ∃ R2 : Relators n, Reachable R1 R2 ∧
      R2 = Function.update R1 mi ((z mi)⁻¹ * FreeGroup.of mi * z mi) := by
    cases hs : s mi with
    | true =>
      refine ⟨_, (Reachable.single (Step.mulRight R1 mi mi1 hne)), ?_⟩
      congr 1
      rw [hR1m, hR1m1, hs]
      simp [signed]
    | false =>
      refine ⟨_, (Steps.mulInvRight R1 mi mi1 hne).reachable, ?_⟩
      congr 1
      rw [hR1m, hR1m1, hs]
      simp [signed]
  obtain ⟨R2, h12, hR2⟩ := step2
  -- step 3: conjugate by z
  have hR2m : R2 mi = (z mi)⁻¹ * FreeGroup.of mi * z mi := by
    simp [hR2]
  set R3 := Function.update R2 mi (z mi * R2 mi * (z mi)⁻¹) with hR3
  have s3 : Step R2 R3 := Step.conj R2 mi (z mi)
  have hR3m : R3 mi = FreeGroup.of mi := by
    simp only [hR3, Function.update_self, hR2m]
    group
  have hend : R3 = upTo z s m := by
    funext k
    by_cases hk : k = mi
    · subst hk
      rw [hR3m]
      simp [upTo, mi]
    · have hk' : k.val ≠ m := fun h => hk (Fin.ext h)
      rw [← upTo_succ_of_ne z s m k hk', ← hR]
      simp only [hR3, hR2, hR1, Function.update_of_ne hk]
  rw [← hend]
  exact ((Reachable.single s1).trans h12).trans (Reachable.single s3)

theorem upTo_reachable (z : Fin n → Word n) (s : Fin n → Bool) (m : ℕ) :
    Reachable (upTo z s m) (standard n) := by
  induction m with
  | zero => rw [upTo_zero]; exact Reachable.refl _
  | succ m ih =>
    by_cases hm : m + 1 < n
    · exact (upTo_step z s m hm).trans ih
    · have : upTo z s (m + 1) = upTo z s m := by
        funext k
        unfold upTo
        have hk := k.isLt
        have : (k.val < m + 1 ∧ k.val + 1 < n) ↔ (k.val < m ∧ k.val + 1 < n) := by omega
        simp only [this]
      rw [this]; exact ih

/-- Every conjugation chain reaches the standard tuple by ordinary AC moves,
at most three per relator. -/
theorem chain_reachable (z : Fin n → Word n) (s : Fin n → Bool) :
    Reachable (chain z s) (standard n) :=
  upTo_reachable z s n

/-- Hence every conjugation chain is stably trivial, and so is every relator
permutation of one. -/
theorem chain_stableReachable (z : Fin n → Word n) (s : Fin n → Bool) :
    StableReachable ⟨n, chain z s⟩ ⟨n, standard n⟩ :=
  (chain_reachable z s).stable

theorem chain_permuted_reachable (z : Fin n → Word n) (s : Fin n → Bool)
    (σ : Equiv.Perm (Fin n)) : Reachable (chain z s ∘ σ) (standard n) :=
  (Reachable.permute (chain z s) σ).symm.trans (chain_reachable z s)

end AC.Chain
