import ACCertificate
import StableCertificate.Official
import Mathlib.Tactic.Group

/-!
# Conjugation trees are AC-trivial at every rank

Shehper et al. (arXiv:2408.15332v2, Theorem 16 and Remark 17) observe that a
balanced presentation whose relators say `x_i = z_i x_{p(i)}^{±1} z_i^{-1}` for
arbitrary words `z_i`, where following `p` always leads to a last generator that is
killed by the last relator, is trivialized by substituting that generator and
iterating. Their statements are about Wirtinger presentations of unknot diagrams
and the presentations obtained from them by substitution and removal; the argument
only uses the tree shape. This module proves the tree shape AC-trivial against the
official `AC.Reachable`, for every rank, every parent function with `i < p i`, every
choice of conjugating words and every choice of signs. Three official moves per
relator: conjugate by `z_i⁻¹`, right-multiply by the already standard parent relator
or its inverse, conjugate by `z_i`. Chains (`p i = i + 1`) are the special case.
-/

namespace AC.Chain

open AC AC.Certificate

variable {n : ℕ}

/-- `x` or its inverse, according to the sign. -/
def signed (x : Word n) : Bool → Word n
  | true => x⁻¹
  | false => x

/-- Relators `0 ≤ i < m` in tree form (when `i + 1 < n`), all others standard. -/
def upTo (p : Fin n → Fin n) (z : Fin n → Word n) (s : Fin n → Bool) (m : ℕ) : Relators n :=
  fun i =>
    if i.val < m ∧ i.val + 1 < n then
      FreeGroup.of i * z i * signed (FreeGroup.of (p i)) (s i) * (z i)⁻¹
    else FreeGroup.of i

/-- The conjugation tree: relator `i` is `x_i z_i x_{p i}^{±1} z_i⁻¹` for `i + 1 < n`,
and the last relator is `x_{n-1}`. The parent function is only meaningful on
non-root indices; the lemmas assume `i < p i` there. -/
def tree (p : Fin n → Fin n) (z : Fin n → Word n) (s : Fin n → Bool) : Relators n :=
  upTo p z s n

/-- The chain parent `i ↦ i + 1` (and the root to itself). -/
def succParent (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else i

/-- The conjugation chain: the tree with parent `i ↦ i + 1`. -/
def chain (z : Fin n → Word n) (s : Fin n → Bool) : Relators n := tree succParent z s

/-- Every non-root index points strictly upward. -/
def Ascending (p : Fin n → Fin n) : Prop := ∀ i : Fin n, i.val + 1 < n → i < p i

theorem succParent_ascending : Ascending (succParent (n := n)) := by
  intro i hi
  simp [succParent, hi, Fin.lt_def]

theorem upTo_zero (p : Fin n → Fin n) (z : Fin n → Word n) (s : Fin n → Bool) :
    upTo p z s 0 = standard n := by
  funext i
  simp [upTo, standard]

theorem upTo_succ_of_ne (p : Fin n → Fin n) (z : Fin n → Word n) (s : Fin n → Bool) (m : ℕ)
    (k : Fin n) (hk : k.val ≠ m) : upTo p z s (m + 1) k = upTo p z s m k := by
  unfold upTo
  have : (k.val < m + 1 ∧ k.val + 1 < n) ↔ (k.val < m ∧ k.val + 1 < n) := by omega
  simp only [this]

/-- One relator is trivialized by three official moves, using its parent, which is
already standard because it lies above `m`. -/
theorem upTo_step (p : Fin n → Fin n) (hp : Ascending p) (z : Fin n → Word n)
    (s : Fin n → Bool) (m : ℕ) (hm : m + 1 < n) :
    Reachable (upTo p z s (m + 1)) (upTo p z s m) := by
  set R := upTo p z s (m + 1) with hR
  let mi : Fin n := ⟨m, by omega⟩
  let mi1 : Fin n := p mi
  have hlt : mi < mi1 := hp mi hm
  have hne : mi ≠ mi1 := ne_of_lt hlt
  have hRm : R mi = FreeGroup.of mi * z mi * signed (FreeGroup.of mi1) (s mi) * (z mi)⁻¹ := by
    simp [hR, upTo, mi, mi1, hm]
  have hRm1 : R mi1 = FreeGroup.of mi1 := by
    have hv : m < (p mi).val := Fin.lt_def.mp hlt
    have : ¬ ((p mi).val < m + 1 ∧ (p mi).val + 1 < n) := by omega
    simp [hR, upTo, mi1, this]
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
  have hend : R3 = upTo p z s m := by
    funext k
    by_cases hk : k = mi
    · subst hk
      rw [hR3m]
      simp [upTo, mi]
    · have hk' : k.val ≠ m := fun h => hk (Fin.ext h)
      rw [← upTo_succ_of_ne p z s m k hk', ← hR]
      simp only [hR3, hR2, hR1, Function.update_of_ne hk]
  rw [← hend]
  exact ((Reachable.single s1).trans h12).trans (Reachable.single s3)

theorem upTo_reachable (p : Fin n → Fin n) (hp : Ascending p) (z : Fin n → Word n)
    (s : Fin n → Bool) (m : ℕ) : Reachable (upTo p z s m) (standard n) := by
  induction m with
  | zero => rw [upTo_zero]; exact Reachable.refl _
  | succ m ih =>
    by_cases hm : m + 1 < n
    · exact (upTo_step p hp z s m hm).trans ih
    · have : upTo p z s (m + 1) = upTo p z s m := by
        funext k
        unfold upTo
        have hk := k.isLt
        have : (k.val < m + 1 ∧ k.val + 1 < n) ↔ (k.val < m ∧ k.val + 1 < n) := by omega
        simp only [this]
      rw [this]; exact ih

/-- Every conjugation tree reaches the standard tuple by ordinary AC moves,
at most three per relator. -/
theorem tree_reachable (p : Fin n → Fin n) (hp : Ascending p) (z : Fin n → Word n)
    (s : Fin n → Bool) : Reachable (tree p z s) (standard n) :=
  upTo_reachable p hp z s n

theorem tree_stableReachable (p : Fin n → Fin n) (hp : Ascending p) (z : Fin n → Word n)
    (s : Fin n → Bool) : StableReachable ⟨n, tree p z s⟩ ⟨n, standard n⟩ :=
  (tree_reachable p hp z s).stable

theorem tree_permuted_reachable (p : Fin n → Fin n) (hp : Ascending p) (z : Fin n → Word n)
    (s : Fin n → Bool) (σ : Equiv.Perm (Fin n)) : Reachable (tree p z s ∘ σ) (standard n) :=
  (Reachable.permute (tree p z s) σ).symm.trans (tree_reachable p hp z s)

/-- Chains are trees with the successor parent. -/
theorem chain_reachable (z : Fin n → Word n) (s : Fin n → Bool) :
    Reachable (chain z s) (standard n) :=
  tree_reachable succParent succParent_ascending z s

theorem chain_stableReachable (z : Fin n → Word n) (s : Fin n → Bool) :
    StableReachable ⟨n, chain z s⟩ ⟨n, standard n⟩ :=
  (chain_reachable z s).stable

theorem chain_permuted_reachable (z : Fin n → Word n) (s : Fin n → Bool)
    (σ : Equiv.Perm (Fin n)) : Reachable (chain z s ∘ σ) (standard n) :=
  tree_permuted_reachable succParent succParent_ascending z s σ

end AC.Chain
