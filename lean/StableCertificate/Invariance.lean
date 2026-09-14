import StableCertificate.Core
import StableCertificate.Official
import Mathlib.Tactic.Group

/-!
# The presented group is invariant along stable paths

`AC.lean` defines `PresentsTrivialGroup R` as the quotient of the free group by the
normal closure of the relators having one element, and states the conjectures for
presentations with that property. This module proves that the property is invariant
under every official move, ordinary or stable, so that it is a property of the
stable equivalence class. Two consequences: a presentation stably reachable from a
standard tuple presents the trivial group, and therefore every accepted certificate
also proves that its starting presentation presents the trivial group.
-/

namespace AC

open Subgroup

variable {n : ℕ}

theorem presentsTrivialGroup_iff (R : Relators n) :
    PresentsTrivialGroup R ↔ normalClosure (Set.range R) = ⊤ := by
  unfold PresentsTrivialGroup PresentedGroup
  exact QuotientGroup.subsingleton_iff

/-- A subgroup of a free group containing every generator is the whole group. -/
theorem eq_top_of_of_mem {α : Type*} (N : Subgroup (FreeGroup α))
    (h : ∀ x, FreeGroup.of x ∈ N) : N = ⊤ := by
  have hle : Subgroup.closure (Set.range (FreeGroup.of : α → FreeGroup α)) ≤ N := by
    rw [Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    exact h x
  rw [FreeGroup.closure_range_of] at hle
  exact top_le_iff.mp hle

/-- A homomorphism maps the normal closure of `s` into the normal closure of its image. -/
theorem map_mem_normalClosure_image {G H : Type*} [Group G] [Group H] (f : G →* H)
    {s : Set G} {x : G} (hx : x ∈ normalClosure s) : f x ∈ normalClosure (f '' s) := by
  have hle : normalClosure s ≤ (normalClosure (f '' s)).comap f :=
    normalClosure_le_normal fun y hy => Subgroup.mem_comap.mpr (subset_normalClosure ⟨y, hy, rfl⟩)
  exact Subgroup.mem_comap.mp (hle hx)

/-! ## Ordinary moves do not change the normal closure. -/

theorem normalClosure_update_eq (R : Relators n) (i : Fin n) (v : Word n)
    (hv : v ∈ normalClosure (Set.range R))
    (hR : R i ∈ normalClosure (Set.range (Function.update R i v))) :
    normalClosure (Set.range (Function.update R i v)) = normalClosure (Set.range R) := by
  apply le_antisymm
  · apply normalClosure_le_normal
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = i
    · subst hk; simpa using hv
    · rw [Function.update_of_ne hk]; exact subset_normalClosure ⟨k, rfl⟩
  · apply normalClosure_le_normal
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = i
    · subst hk; exact hR
    · have : R k = Function.update R i v k := (Function.update_of_ne hk _ _).symm
      rw [this]; exact subset_normalClosure ⟨k, rfl⟩

theorem Step.normalClosure_eq {R S : Relators n} (h : Step R S) :
    normalClosure (Set.range S) = normalClosure (Set.range R) := by
  cases h with
  | inv i =>
    apply normalClosure_update_eq
    · exact inv_mem (subset_normalClosure ⟨i, rfl⟩)
    · set S := Function.update R i (R i)⁻¹ with hS
      have : R i = (S i)⁻¹ := by simp [hS]
      rw [this]
      refine inv_mem ?_
      exact subset_normalClosure ⟨i, rfl⟩
  | mulRight i j hij =>
    apply normalClosure_update_eq
    · exact mul_mem (subset_normalClosure ⟨i, rfl⟩) (subset_normalClosure ⟨j, rfl⟩)
    · set S := Function.update R i (R i * R j) with hS
      have : R i = S i * (S j)⁻¹ := by simp [hS, hij.symm]
      rw [this]
      refine mul_mem ?_ (inv_mem ?_)
      · exact subset_normalClosure ⟨i, rfl⟩
      · exact subset_normalClosure ⟨j, rfl⟩
  | conj i w =>
    apply normalClosure_update_eq
    · refine Subgroup.normalClosure_normal.conj_mem _ ?_ w
      exact subset_normalClosure ⟨i, rfl⟩
    · set S := Function.update R i (w * R i * w⁻¹) with hS
      have : R i = w⁻¹ * S i * w⁻¹⁻¹ := by
        simp only [hS, Function.update_self]
        group
      rw [this]
      refine Subgroup.normalClosure_normal.conj_mem _ ?_ w⁻¹
      exact subset_normalClosure ⟨i, rfl⟩

theorem Step.presentsTrivialGroup_iff {R S : Relators n} (h : Step R S) :
    PresentsTrivialGroup S ↔ PresentsTrivialGroup R := by
  rw [AC.presentsTrivialGroup_iff, AC.presentsTrivialGroup_iff, h.normalClosure_eq]

theorem Reachable.presentsTrivialGroup_iff {R S : Relators n} (h : Reachable R S) :
    PresentsTrivialGroup S ↔ PresentsTrivialGroup R := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ step ih => exact step.presentsTrivialGroup_iff.trans ih

/-! ## Stabilization does not change the presented group. -/

/-- Kill the inserted generator `g` and send `g.succAbove j` back to `j`. -/
def unstab (g : Fin (n + 1)) : Word (n + 1) →* Word n :=
  FreeGroup.lift (Fin.insertNth g 1 fun j => FreeGroup.of j)

@[simp] theorem unstab_of_same (g : Fin (n + 1)) : unstab g (FreeGroup.of g) = 1 := by
  simp [unstab]

@[simp] theorem unstab_of_succAbove (g : Fin (n + 1)) (j : Fin n) :
    unstab g (FreeGroup.of (g.succAbove j)) = FreeGroup.of j := by
  simp [unstab]

@[simp] theorem unstab_map (g : Fin (n + 1)) (w : Word n) :
    unstab g (FreeGroup.map g.succAbove w) = w := by
  have : (unstab g).comp (FreeGroup.map g.succAbove) = MonoidHom.id (Word n) := by
    ext x
    simp
  exact DFunLike.congr_fun this w

theorem stabilize_presentsTrivialGroup_iff (R : Relators n) (g i : Fin (n + 1)) :
    PresentsTrivialGroup (stabilize R g i) ↔ PresentsTrivialGroup R := by
  rw [AC.presentsTrivialGroup_iff, AC.presentsTrivialGroup_iff]
  constructor
  · intro htop
    apply eq_top_of_of_mem
    intro j
    have hmem : FreeGroup.of (g.succAbove j) ∈ normalClosure (Set.range (stabilize R g i)) := by
      rw [htop]; exact Subgroup.mem_top _
    have h1 := map_mem_normalClosure_image (unstab g) hmem
    rw [unstab_of_succAbove] at h1
    refine normalClosure_le_normal ?_ h1
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    induction k using i.succAboveCases
    · simp
    · rename_i k
      simp only [stabilize_succAbove, unstab_map]
      exact subset_normalClosure ⟨k, rfl⟩
  · intro htop
    apply eq_top_of_of_mem
    intro x
    induction x using g.succAboveCases
    · have : FreeGroup.of g = stabilize R g i i := (stabilize_at R g i).symm
      rw [this]; exact subset_normalClosure ⟨i, rfl⟩
    · rename_i j
      have hj : FreeGroup.of j ∈ normalClosure (Set.range R) := by
        rw [htop]; exact Subgroup.mem_top _
      have h1 := map_mem_normalClosure_image (FreeGroup.map g.succAbove) hj
      rw [FreeGroup.map.of] at h1
      refine normalClosure_le_normal ?_ h1
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      have : FreeGroup.map g.succAbove (R k) = stabilize R g i (i.succAbove k) :=
        (stabilize_succAbove R g i k).symm
      rw [this]; exact subset_normalClosure ⟨_, rfl⟩

/-! ## Invariance along stable paths and its consequences. -/

theorem StableStep.presentsTrivialGroup_iff {P Q : Presentation} (h : StableStep P Q) :
    PresentsTrivialGroup Q.2 ↔ PresentsTrivialGroup P.2 := by
  cases h with
  | ac h => exact h.presentsTrivialGroup_iff
  | stabilize R g i => exact stabilize_presentsTrivialGroup_iff R g i
  | destabilize R g i => exact (stabilize_presentsTrivialGroup_iff R g i).symm

/-- Presenting the trivial group is a property of the stable equivalence class. -/
theorem StableReachable.presentsTrivialGroup_iff {P Q : Presentation} (h : StableReachable P Q) :
    PresentsTrivialGroup Q.2 ↔ PresentsTrivialGroup P.2 := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ step ih => exact step.presentsTrivialGroup_iff.trans ih

theorem standard_presentsTrivialGroup (n : ℕ) : PresentsTrivialGroup (standard n) := by
  rw [AC.presentsTrivialGroup_iff]
  exact eq_top_of_of_mem _ fun x => subset_normalClosure ⟨x, rfl⟩

/-- Anything stably reachable to a standard tuple presents the trivial group: the
hypothesis of the conjecture is automatic for the presentations its conclusion covers. -/
theorem presentsTrivialGroup_of_stableReachable_standard {R : Relators n}
    (h : StableReachable ⟨n, R⟩ ⟨n, standard n⟩) : PresentsTrivialGroup R :=
  h.presentsTrivialGroup_iff.mp (standard_presentsTrivialGroup n)

/-- Hence the stable conjecture can be stated without its hypothesis as a biconditional. -/
theorem stableConjecture_iff_forall_iff :
    StableConjecture ↔ ∀ (n : ℕ), 0 < n → ∀ (R : Relators n),
      PresentsTrivialGroup R ↔ StableReachable ⟨n, R⟩ ⟨n, standard n⟩ :=
  ⟨fun hc n hn R => ⟨hc n hn R, presentsTrivialGroup_of_stableReachable_standard⟩,
   fun hc n hn R hR => (hc n hn R).mp hR⟩

namespace Stable

open AC.Certificate

/-- An accepted certificate proves that its starting presentation presents the trivial group. -/
theorem check_presentsTrivialGroup {R : RawTuple 2} {ids : List ℕ} (h : check R ids = true) :
    PresentsTrivialGroup (denote R) :=
  presentsTrivialGroup_of_stableReachable_standard (check_sound h)

theorem checkEncoded_presentsTrivialGroup {words : List (List ℤ)} {ids : List ℤ}
    (h : checkEncoded words ids = true) :
    ∃ R, parseTuple words = some R ∧ PresentsTrivialGroup (denote R) := by
  obtain ⟨R, hr, hs⟩ := checkEncoded_sound h
  exact ⟨R, hr, presentsTrivialGroup_of_stableReachable_standard hs⟩

end Stable

end AC
