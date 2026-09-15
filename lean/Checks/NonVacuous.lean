import StableCertificate
import Mathlib.Tactic.FinCases

/-! Non-vacuity witnesses: every hypothesis-laden theorem of the package instantiated
on concrete data, and a violation of each hypothesis where one is expressible. Every
item is a named theorem so that its axioms are printed. -/

open AC AC.Stable AC.Chain AC.Lemma11 Subgroup

namespace NonVacuous

/-! ### Conjugation trees: `Ascending` is satisfiable and violable. -/

theorem ascending_succ : Ascending (succParent (n := 3)) := succParent_ascending

theorem not_ascending_const : ¬ Ascending (fun _ : Fin 2 => (0 : Fin 2)) :=
  fun h => absurd (h 0 (by decide)) (by decide)

/-- The rank-2 chain with `z₀ = x₂`, sign `+`, is the concrete tuple `(x₁x₂, x₂)`. -/
def chain2 : Relators 2 := fun i => if i = 0 then FreeGroup.of 0 * FreeGroup.of 1 else FreeGroup.of 1

theorem chain2_eq : chain (fun _ => FreeGroup.of (1 : Fin 2)) (fun _ => false) = chain2 := by
  funext i
  fin_cases i <;> simp [chain, tree, upTo, succParent, chain2, signed]

theorem chain2_reachable : Reachable chain2 (standard 2) :=
  chain2_eq ▸ chain_reachable _ _

/-! ### Arbitrary root relator: a nontrivial `w` congruent to the root generator. -/

/-- `w = x₂ · r₀` with `r₀ = x₁x₂`, so `w⁻¹ x₂ = r₀⁻¹` lies in the normal closure of `r₀`. -/
theorem root_witness :
    Reachable (Function.update chain2 1 (FreeGroup.of 1 * chain2 0)) (standard 2) := by
  have hroot : root 2 (by norm_num) = 1 := rfl
  have e : tree succParent (fun _ => FreeGroup.of (1 : Fin 2)) (fun _ => false) = chain2 := chain2_eq
  have h := tree_with_root_reachable succParent succParent_ascending
    (fun _ => FreeGroup.of (1 : Fin 2)) (fun _ => false) (by norm_num)
    (FreeGroup.of 1 * chain2 0) 1 (Or.inl rfl) ?_
  · rw [e, hroot] at h; exact h
  · rw [e, hroot]
    have : (FreeGroup.of (1 : Fin 2) * chain2 0)⁻¹ * FreeGroup.of 1 ^ (1 : ℤ) = (chain2 0)⁻¹ := by
      group
    rw [this]
    exact inv_mem (subset_normalClosure (mem_others chain2 (by decide : (0 : Fin 2) ≠ 1)))

/-! ### Lemma 15 with `e = -1`. -/

theorem congr_generator_witness :
    Reachable (Function.update chain2 1 (FreeGroup.of 1)⁻¹) (standard 2) := by
  apply Reachable.standard_of_congr_generator _ 1 1 (-1) (Or.inr rfl)
  · simp only [Function.update_self]
    have : ((FreeGroup.of (1 : Fin 2))⁻¹)⁻¹ * FreeGroup.of 1 ^ (-1 : ℤ) = 1 := by group
    rw [this]; exact one_mem _
  · rw [Function.update_idem]
    have : Function.update chain2 1 (FreeGroup.of 1) = chain2 := by
      funext i; fin_cases i <;> simp [chain2]
    rw [this]; exact chain2_reachable

/-! ### Conjecture 19's hypotheses are satisfiable: `⟨x, y | x y⁻¹⟩` presents ℤ with `x ≡ y`. -/

def zRel : Relators 2 := fun i => if i = 0 then FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ else 1

theorem zRel_congruent : GeneratorsCongruent zRel 1 (fun _ => 1) := by
  refine ⟨fun _ => Or.inl rfl, fun j => ?_⟩
  fin_cases j
  · -- x⁻¹ y = x⁻¹ (x y⁻¹)⁻¹ x
    have hr : zRel 0 ∈ normalClosure (others zRel 1) :=
      subset_normalClosure (mem_others zRel (by decide : (0 : Fin 2) ≠ 1))
    have := Subgroup.normalClosure_normal.conj_mem _ (inv_mem hr) (FreeGroup.of 0)⁻¹
    simp only [zRel, if_true] at this
    have e : (FreeGroup.of (0 : Fin 2))⁻¹ * (FreeGroup.of 0 * (FreeGroup.of 1)⁻¹)⁻¹ * (FreeGroup.of 0)⁻¹⁻¹ =
        (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 ^ (1 : ℤ) := by group
    rw [e] at this; exact this
  · simp

/-- The exponent-sum homomorphism kills `x y⁻¹`, so `y` has infinite order modulo it. -/
theorem zRel_infiniteOrder : InfiniteOrderMod zRel 1 := by
  intro k hk
  let φ : Word 2 →* Multiplicative ℤ := FreeGroup.lift fun _ => Multiplicative.ofAdd 1
  have hker : normalClosure (others zRel 1) ≤ φ.ker := by
    apply normalClosure_le_normal
    rintro _ ⟨j, hj, rfl⟩
    fin_cases j
    · simp [MonoidHom.mem_ker, zRel, φ]
    · exact absurd rfl hj
  have h := hker hk
  rw [MonoidHom.mem_ker, map_zpow] at h
  simp [φ] at h
  exact h

theorem conjecture19_hypotheses_satisfiable :
    ∃ (R : Relators 2) (i : Fin 2) (ε : Fin 2 → ℤ), GeneratorsCongruent R i ε ∧ InfiniteOrderMod R i :=
  ⟨zRel, 1, fun _ => 1, zRel_congruent, zRel_infiniteOrder⟩

/-! ### Lemma 11 on concrete data, and a two-step iteration. -/

/-- `⟨x, y | y⁻¹x, x y⁻¹ x⟩`: `y` at position 1, `y⁻¹w` at index 0 with `w = x`. -/
def P2 : Relators 2 := fun i =>
  if i = 0 then (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
  else FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0

theorem P2_rel : P2 0 = rel 1 (FreeGroup.of (0 : Fin 1)) := by
  simp [P2, rel]

theorem P2_trivial : PresentsTrivialGroup P2 := by
  rw [presentsTrivialGroup_iff]
  apply eq_top_of_of_mem
  have h0 : P2 0 ∈ normalClosure (Set.range P2) := subset_normalClosure ⟨0, rfl⟩
  have h1 : P2 1 ∈ normalClosure (Set.range P2) := subset_normalClosure ⟨1, rfl⟩
  have hx : FreeGroup.of (0 : Fin 2) ∈ normalClosure (Set.range P2) := by
    have := inv_mem (mul_mem h0 (inv_mem h1))
    have e : ((P2 0) * (P2 1)⁻¹)⁻¹ = FreeGroup.of 0 := by simp [P2]
    rw [e] at this; exact this
  have hy : FreeGroup.of (1 : Fin 2) ∈ normalClosure (Set.range P2) := by
    have := inv_mem (mul_mem h0 (inv_mem hx))
    have e : ((P2 0) * (FreeGroup.of 0)⁻¹)⁻¹ = FreeGroup.of 1 := by simp [P2]
    rw [e] at this; exact this
  intro x
  fin_cases x
  · exact hx
  · exact hy

theorem P2_reduced : reduced P2 0 1 (FreeGroup.of (0 : Fin 1)) = standard 1 := by
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  have r0 : retract (1 : Fin 2) (FreeGroup.of 0) (FreeGroup.of (0 : Fin 2)) = FreeGroup.of 0 := by
    have h := retract_of_succAbove (1 : Fin 2) (FreeGroup.of 0) 0
    rwa [show (1 : Fin 2).succAbove 0 = 0 by decide] at h
  simp [reduced, standard, P2, r0]

theorem lemma11_witness : StableReachable ⟨2, P2⟩ ⟨1, standard 1⟩ := by
  have h := substitution_removal P2 0 1 (FreeGroup.of 0) P2_rel P2_trivial
  rw [P2_reduced] at h
  exact h

/-- Rank 3: `P2` lifted with a third generator `z` and the relator `z⁻¹x` at index 2. -/
def P3 : Relators 3 := fun i =>
  if i = 0 then (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
  else if i = 1 then FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
  else (FreeGroup.of 2)⁻¹ * FreeGroup.of 0

theorem P3_rel : P3 2 = rel 2 (FreeGroup.of (0 : Fin 2)) := by
  simp [P3, rel]

theorem P3_reduced : reduced P3 2 2 (FreeGroup.of (0 : Fin 2)) = P2 := by
  funext j
  have r0 : retract (2 : Fin 3) (FreeGroup.of 0) (FreeGroup.of (0 : Fin 3)) = FreeGroup.of 0 := by
    have h := retract_of_succAbove (2 : Fin 3) (FreeGroup.of 0) 0
    rwa [show (2 : Fin 3).succAbove 0 = 0 by decide] at h
  have r1 : retract (2 : Fin 3) (FreeGroup.of 0) (FreeGroup.of (1 : Fin 3)) = FreeGroup.of 1 := by
    have h := retract_of_succAbove (2 : Fin 3) (FreeGroup.of 0) 1
    rwa [show (2 : Fin 3).succAbove 1 = 1 by decide] at h
  fin_cases j
  · have e : (2 : Fin 3).succAbove 0 = 0 := by decide
    show retract 2 (FreeGroup.of 0) (P3 ((2 : Fin 3).succAbove 0)) = P2 0
    rw [e]
    show retract 2 (FreeGroup.of 0) ((FreeGroup.of 1)⁻¹ * FreeGroup.of 0) =
      (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
    simp [r0, r1]
  · have e : (2 : Fin 3).succAbove 1 = 1 := by decide
    show retract 2 (FreeGroup.of 0) (P3 ((2 : Fin 3).succAbove 1)) = P2 1
    rw [e]
    show retract 2 (FreeGroup.of 0) (FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0) =
      FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
    simp [r0, r1]

/-- The inductive class has a two-step member. -/
theorem iterated_two_steps : Iterated ⟨3, P3⟩ ⟨1, standard 1⟩ := by
  have s1 : Iterated ⟨3, P3⟩ ⟨2, P2⟩ := by
    have := Iterated.step (Iterated.refl ⟨3, P3⟩) 2 2 (FreeGroup.of 0) P3_rel
    rw [P3_reduced] at this; exact this
  have := Iterated.step s1 0 1 (FreeGroup.of 0) P2_rel
  rw [P2_reduced] at this; exact this

/-- A rank-3 presentation shown stably trivial through two removals. -/
theorem P3_stableTrivial : StableReachable ⟨3, P3⟩ ⟨3, standard 3⟩ := by
  have h2 : StableReachable ⟨2, P2⟩ ⟨2, standard 2⟩ :=
    (stableTrivial_iff P2 0 1 _ P2_rel P2_trivial).mpr (by rw [P2_reduced]; exact StableReachable.refl _)
  have h3 : PresentsTrivialGroup P3 := by
    rw [presentsTrivialGroup_iff]
    apply eq_top_of_of_mem
    have h0 : P3 0 ∈ normalClosure (Set.range P3) := subset_normalClosure ⟨0, rfl⟩
    have h1 : P3 1 ∈ normalClosure (Set.range P3) := subset_normalClosure ⟨1, rfl⟩
    have h2' : P3 2 ∈ normalClosure (Set.range P3) := subset_normalClosure ⟨2, rfl⟩
    have hx : FreeGroup.of (0 : Fin 3) ∈ normalClosure (Set.range P3) := by
      have := inv_mem (mul_mem h0 (inv_mem h1))
      have e : ((P3 0) * (P3 1)⁻¹)⁻¹ = FreeGroup.of 0 := by simp [P3]
      rw [e] at this; exact this
    have hy : FreeGroup.of (1 : Fin 3) ∈ normalClosure (Set.range P3) := by
      have := inv_mem (mul_mem h0 (inv_mem hx))
      have e : ((P3 0) * (FreeGroup.of 0)⁻¹)⁻¹ = FreeGroup.of 1 := by simp [P3]
      rw [e] at this; exact this
    have hz : FreeGroup.of (2 : Fin 3) ∈ normalClosure (Set.range P3) := by
      have := inv_mem (mul_mem h2' (inv_mem hx))
      have e : ((P3 2) * (FreeGroup.of 0)⁻¹)⁻¹ = FreeGroup.of 2 := by simp [P3]
      rw [e] at this; exact this
    intro x
    fin_cases x
    · exact hx
    · exact hy
    · exact hz
  exact (stableTrivial_iff P3 2 2 _ P3_rel h3).mpr (by rw [P3_reduced]; exact h2)

/-! ### Any-rank certificates: a rank-3 instance through the kernel. -/

theorem anyRank_kernel : checkEncodedAt [[1], [2], [3]] [17, 16, 15] = true := by decide +kernel

theorem anyRank_witness : ∃ P : RawPres, parsePres [[1], [2], [3]] = some P ∧
    StableReachable ⟨P.1, AC.Certificate.denote (toTuple P.2)⟩ ⟨P.1, standard P.1⟩ :=
  checkEncodedAt_sound anyRank_kernel

/-! ### A violation of the `rel` shape: the standard tuple is not of the form `y⁻¹w`. -/

theorem standard_not_rel : standard 2 0 ≠ rel 1 (FreeGroup.of (0 : Fin 1)) := by decide

end NonVacuous

#print axioms NonVacuous.chain2_reachable
#print axioms NonVacuous.root_witness
#print axioms NonVacuous.congr_generator_witness
#print axioms NonVacuous.conjecture19_hypotheses_satisfiable
#print axioms NonVacuous.lemma11_witness
#print axioms NonVacuous.iterated_two_steps
#print axioms NonVacuous.P3_stableTrivial
#print axioms NonVacuous.anyRank_witness
#print axioms NonVacuous.not_ascending_const
#print axioms NonVacuous.standard_not_rel
