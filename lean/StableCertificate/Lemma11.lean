import StableCertificate.NormalClosure
import StableCertificate.Invariance
import Mathlib.Tactic.Group

/-!
# Substitution and removal (Lemma 11 of Shehper et al.)

If `⟨x₁,…,xₙ, y | r₁,…,rₙ, y⁻¹w⟩` presents the trivial group and `w` is a word in the
`x` alone, then it is stably AC-equivalent to `⟨x | r₁[w/y],…,rₙ[w/y]⟩`
(arXiv:2408.15332v2, Lemma 11). This module proves the statement against the
official relations with the generator `y` at any position `g` and the relator
`y⁻¹w` at any index `i`. Steps: substituting `w` for `y` is multiplication by
elements of the normal closure of `y⁻¹w` (`Reachable.replace_of_mem_normalClosure`);
triviality transfers to the substituted rank-`n` tuple through the retraction that
sends `y ↦ w`; hence `w` lies in the normal closure of the other relators, `y⁻¹w`
may be replaced by `y`, and one official destabilization removes the pair.
-/

namespace AC.Lemma11

open AC AC.Certificate Subgroup

variable {n : ℕ}

/-! ## S1: the retraction `y ↦ w'`, `x_j ↦ x_j`, and substitution. -/

/-- Substitute `w'` for the generator `g` and drop it. -/
def retract (g : Fin (n + 1)) (w' : Word n) : Word (n + 1) →* Word n :=
  FreeGroup.lift (Fin.insertNth g w' fun j => FreeGroup.of j)

@[simp] theorem retract_of_same (g : Fin (n + 1)) (w' : Word n) :
    retract g w' (FreeGroup.of g) = w' := by
  simp [retract]

@[simp] theorem retract_of_succAbove (g : Fin (n + 1)) (w' : Word n) (j : Fin n) :
    retract g w' (FreeGroup.of (g.succAbove j)) = FreeGroup.of j := by
  simp [retract]

@[simp] theorem retract_map (g : Fin (n + 1)) (w' : Word n) (v : Word n) :
    retract g w' (FreeGroup.map g.succAbove v) = v := by
  have : (retract g w').comp (FreeGroup.map g.succAbove) = MonoidHom.id (Word n) := by
    ext x
    simp
  exact DFunLike.congr_fun this v

/-- Substitute `w = map g.succAbove w'` for `y` inside a word of rank `n + 1`. -/
def subst (g : Fin (n + 1)) (w' : Word n) : Word (n + 1) →* Word (n + 1) :=
  (FreeGroup.map g.succAbove).comp (retract g w')

theorem subst_apply (g : Fin (n + 1)) (w' : Word n) (r : Word (n + 1)) :
    subst g w' r = FreeGroup.map g.succAbove (retract g w' r) := rfl

/-- The relator `y⁻¹ w`. -/
def rel (g : Fin (n + 1)) (w' : Word n) : Word (n + 1) :=
  (FreeGroup.of g)⁻¹ * FreeGroup.map g.succAbove w'

/-! ## S2: substitution is congruence modulo `y⁻¹w`. -/

theorem subst_congr (g : Fin (n + 1)) (w' : Word n) (r : Word (n + 1)) :
    r⁻¹ * subst g w' r ∈ normalClosure ({rel g w'} : Set (Word (n + 1))) := by
  set N := normalClosure ({rel g w'} : Set (Word (n + 1))) with hN
  let ψ : Word (n + 1) →* Word (n + 1) ⧸ N := QuotientGroup.mk' N
  have hgen : ∀ x, ψ (FreeGroup.of x) = (ψ.comp (subst g w')) (FreeGroup.of x) := by
    intro x
    induction x using g.succAboveCases
    · simp only [MonoidHom.comp_apply, subst_apply, retract_of_same, ψ, QuotientGroup.mk'_apply]
      exact QuotientGroup.eq.mpr (subset_normalClosure (Set.mem_singleton _))
    · rename_i j
      simp [MonoidHom.comp_apply, subst_apply, ψ]
  have h := FreeGroup.ext_hom ψ (ψ.comp (subst g w')) hgen
  have hr := DFunLike.congr_fun h r
  simp only [MonoidHom.comp_apply, ψ, QuotientGroup.mk'_apply] at hr
  exact QuotientGroup.eq.mp hr

/-! ## S3: substitution as ordinary AC moves, one relator at a time. -/

/-- Relators listed in `L`, other than `i`, substituted; the rest unchanged. -/
def substOn (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n) :
    List (Fin (n + 1)) → Relators (n + 1)
  | [] => R
  | j :: L =>
      if j = i then substOn R i g w' L
      else Function.update (substOn R i g w' L) j (subst g w' (R j))

theorem substOn_apply (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n)
    (L : List (Fin (n + 1))) (k : Fin (n + 1)) :
    substOn R i g w' L k = if k ≠ i ∧ k ∈ L then subst g w' (R k) else R k := by
  induction L with
  | nil => simp [substOn]
  | cons j L ih =>
    simp only [substOn]
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl, ih]
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    · rw [if_neg hj]
      by_cases hk : k = j
      · subst hk; simp [hj]
      · rw [Function.update_of_ne hk, ih]
        simp [hk]

theorem substOn_reachable (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n)
    (hRi : R i = rel g w') (L : List (Fin (n + 1))) :
    Reachable R (substOn R i g w' L) := by
  induction L with
  | nil => exact Reachable.refl _
  | cons j L ih =>
    simp only [substOn]
    by_cases hj : j = i
    · rw [if_pos hj]; exact ih
    · rw [if_neg hj]
      refine ih.trans (Reachable.replace_of_mem_normalClosure _ j ?_)
      rw [substOn_apply]
      by_cases hjL : j ∈ L
      · rw [if_pos ⟨hj, hjL⟩, inv_mul_cancel]
        exact one_mem _
      · rw [if_neg (fun h => hjL h.2)]
        refine normalClosure_mono ?_ (subst_congr g w' (R j))
        rw [Set.singleton_subset_iff]
        have : substOn R i g w' L i = rel g w' := by
          rw [substOn_apply, if_neg (fun h => h.1 rfl), hRi]
        rw [← this]
        exact mem_others _ (Ne.symm hj)

/-- All relators other than `i` substituted. -/
def substituted (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n) : Relators (n + 1) :=
  substOn R i g w' (List.finRange (n + 1))

theorem substituted_apply (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n)
    (k : Fin (n + 1)) :
    substituted R i g w' k = if k = i then R i else subst g w' (R k) := by
  rw [substituted, substOn_apply]
  by_cases hk : k = i
  · simp [hk]
  · simp [hk, List.mem_finRange]

theorem substituted_reachable (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n)
    (hRi : R i = rel g w') : Reachable R (substituted R i g w') :=
  substOn_reachable R i g w' hRi _

/-! ## S4: triviality transfers to the substituted rank-`n` tuple. -/

/-- The rank-`n` tuple `r_j[w/y]`, indexed by the positions other than `i`. -/
def reduced (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n) : Relators n :=
  fun j => retract g w' (R (i.succAbove j))

theorem retract_substituted_same (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n)
    (hRi : R i = rel g w') : retract g w' (substituted R i g w' i) = 1 := by
  rw [substituted_apply, if_pos rfl, hRi, rel]
  simp

theorem retract_substituted_succAbove (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n)
    (j : Fin n) : retract g w' (substituted R i g w' (i.succAbove j)) = reduced R i g w' j := by
  rw [substituted_apply, if_neg (Fin.succAbove_ne i j), subst_apply, retract_map]
  rfl

theorem reduced_normalClosure_eq_top (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n)
    (hRi : R i = rel g w') (htriv : PresentsTrivialGroup (substituted R i g w')) :
    normalClosure (Set.range (reduced R i g w')) = ⊤ := by
  rw [presentsTrivialGroup_iff] at htriv
  apply eq_top_of_of_mem
  intro j
  have hmem : FreeGroup.of (g.succAbove j) ∈ normalClosure (Set.range (substituted R i g w')) := by
    rw [htriv]; exact Subgroup.mem_top _
  have h1 := map_mem_normalClosure_image (retract g w') hmem
  rw [retract_of_succAbove] at h1
  refine normalClosure_le_normal ?_ h1
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  induction k using i.succAboveCases
  · rw [retract_substituted_same R i g w' hRi]; exact one_mem _
  · rename_i k
    rw [retract_substituted_succAbove]
    exact subset_normalClosure ⟨k, rfl⟩

/-! ## S5: `w` lies in the normal closure of the other relators; `y⁻¹w` becomes `y`. -/

theorem map_w_mem (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n)
    (hRi : R i = rel g w') (htriv : PresentsTrivialGroup (substituted R i g w')) :
    FreeGroup.map g.succAbove w' ∈ normalClosure (others (substituted R i g w') i) := by
  have hw : w' ∈ normalClosure (Set.range (reduced R i g w')) := by
    rw [reduced_normalClosure_eq_top R i g w' hRi htriv]; exact Subgroup.mem_top _
  have h1 := map_mem_normalClosure_image (FreeGroup.map g.succAbove) hw
  refine normalClosure_le_normal ?_ h1
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  refine subset_normalClosure ⟨i.succAbove k, Fin.succAbove_ne i k, ?_⟩
  rw [substituted_apply, if_neg (Fin.succAbove_ne i k), subst_apply]
  rfl

theorem substituted_to_generator (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n)
    (hRi : R i = rel g w') (htriv : PresentsTrivialGroup (substituted R i g w')) :
    Reachable (substituted R i g w') (Function.update (substituted R i g w') i (FreeGroup.of g)) := by
  have hmem := map_w_mem R i g w' hRi htriv
  have h1 : Reachable (substituted R i g w')
      (Function.update (substituted R i g w') i (FreeGroup.of g)⁻¹) := by
    apply Reachable.replace_of_mem_normalClosure
    rw [substituted_apply, if_pos rfl, hRi, rel]
    have : ((FreeGroup.of g)⁻¹ * FreeGroup.map g.succAbove w')⁻¹ * (FreeGroup.of g)⁻¹ =
        (FreeGroup.map g.succAbove w')⁻¹ := by group
    rw [this]
    exact inv_mem hmem
  have h2 := Reachable.single (Step.inv (Function.update (substituted R i g w') i (FreeGroup.of g)⁻¹) i)
  simp only [Function.update_self, inv_inv, Function.update_idem] at h2
  exact h1.trans h2

/-! ## S6: the result is a stabilization of the reduced tuple. -/

theorem update_eq_stabilize (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n) :
    Function.update (substituted R i g w') i (FreeGroup.of g) = stabilize (reduced R i g w') g i := by
  funext k
  induction k using i.succAboveCases
  · simp
  · rename_i j
    rw [Function.update_of_ne (Fin.succAbove_ne i j), stabilize_succAbove, substituted_apply,
      if_neg (Fin.succAbove_ne i j), subst_apply]
    rfl

/-- **Lemma 11.** With `y` at generator position `g` and `y⁻¹w` at relator index `i`,
a trivial-group presentation is stably reachable to the rank-`n` presentation with
`w` substituted for `y` and the pair removed. -/
theorem substitution_removal (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n)
    (hRi : R i = rel g w') (htriv : PresentsTrivialGroup R) :
    StableReachable ⟨n + 1, R⟩ ⟨n, reduced R i g w'⟩ := by
  have h1 := substituted_reachable R i g w' hRi
  have htriv' : PresentsTrivialGroup (substituted R i g w') :=
    h1.presentsTrivialGroup_iff.mpr htriv
  have h2 := substituted_to_generator R i g w' hRi htriv'
  have h3 : StableStep ⟨n + 1, Function.update (substituted R i g w') i (FreeGroup.of g)⟩
      ⟨n, reduced R i g w'⟩ := by
    rw [update_eq_stabilize]
    exact StableStep.destabilize _ g i
  exact ((h1.trans h2).stable).tail h3

/-! ## S7: corollaries. -/

theorem substitution_removal_symm (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n)
    (hRi : R i = rel g w') (htriv : PresentsTrivialGroup R) :
    StableReachable ⟨n, reduced R i g w'⟩ ⟨n + 1, R⟩ :=
  (substitution_removal R i g w' hRi htriv).symm

/-- Stable triviality transfers both ways across substitution and removal. -/
theorem stableTrivial_iff (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n)
    (hRi : R i = rel g w') (htriv : PresentsTrivialGroup R) :
    StableReachable ⟨n + 1, R⟩ ⟨n + 1, standard (n + 1)⟩ ↔
      StableReachable ⟨n, reduced R i g w'⟩ ⟨n, standard n⟩ := by
  have h := substitution_removal R i g w' hRi htriv
  constructor
  · intro hR
    exact ((h.symm.trans hR).trans (standard_to_empty (n + 1))).trans (empty_to_standard n)
  · intro hr
    exact ((h.trans hr).trans (standard_to_empty n)).trans (empty_to_standard (n + 1))

/-- The reduced tuple presents the trivial group. -/
theorem reduced_presentsTrivialGroup (R : Relators (n + 1)) (i g : Fin (n + 1)) (w' : Word n)
    (hRi : R i = rel g w') (htriv : PresentsTrivialGroup R) :
    PresentsTrivialGroup (reduced R i g w') :=
  (substitution_removal R i g w' hRi htriv).presentsTrivialGroup_iff.mpr htriv

end AC.Lemma11

namespace AC.Lemma11

open AC

/-! ## Iterated substitution and removal (the class of Remark 17). -/

/-- `Iterated P Q`: `Q` is obtained from `P` by finitely many substitution-and-removal
steps. A step carries only the syntactic hypothesis `R i = rel g w'`; the
trivial-group hypothesis of Lemma 11 is supplied along the way by invariance. -/
inductive Iterated : Presentation → Presentation → Prop
  | refl (P : Presentation) : Iterated P P
  | step {P : Presentation} {n : ℕ} {R : Relators (n + 1)} (h : Iterated P ⟨n + 1, R⟩)
      (i g : Fin (n + 1)) (w' : Word n) (hRi : R i = rel g w') :
      Iterated P ⟨n, reduced R i g w'⟩

/-- Every presentation obtained from a stably trivial one by iterated substitution
and removal is stably trivial. -/
theorem iterated_stableTrivial {P Q : Presentation} (h : Iterated P Q)
    (hP : StableReachable P ⟨P.1, standard P.1⟩) :
    StableReachable Q ⟨Q.1, standard Q.1⟩ := by
  induction h with
  | refl => exact hP
  | step h i g w' hRi ih =>
    have htriv : PresentsTrivialGroup _ := presentsTrivialGroup_of_stableReachable_standard ih
    exact (stableTrivial_iff _ i g w' hRi htriv).mp ih

theorem iterated_presentsTrivialGroup {P Q : Presentation} (h : Iterated P Q)
    (hP : StableReachable P ⟨P.1, standard P.1⟩) : PresentsTrivialGroup Q.2 :=
  presentsTrivialGroup_of_stableReachable_standard (iterated_stableTrivial h hP)

end AC.Lemma11
