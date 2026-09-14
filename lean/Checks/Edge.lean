import StableCertificate

/-! Boundary checks: ranks 0 and 1, and the frozen table's block edges. Every item is
a theorem; nothing here is a printed value. -/

open AC AC.Stable AC.Chain AC.Lemma11

/-- Rank 1: the chain with one generator is the standard tuple. -/
theorem chain_one (z : Fin 1 → Word 1) (s : Fin 1 → Bool) : chain z s = standard 1 := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  simp [chain, tree, upTo, standard]

/-- Rank 0: the empty tree is the (empty) standard tuple. -/
theorem tree_zero (p : Fin 0 → Fin 0) (z : Fin 0 → Word 0) (s : Fin 0 → Bool) :
    tree p z s = standard 0 := by
  funext i
  exact i.elim0

/-- Lemma 11 at `n = 0`: the rank-1 presentation `⟨y | y⁻¹⟩` reaches rank 0. -/
example : StableReachable ⟨1, fun _ => (FreeGroup.of (0 : Fin 1))⁻¹⟩ ⟨0, standard 0⟩ := by
  have htriv : PresentsTrivialGroup (fun _ : Fin 1 => (FreeGroup.of (0 : Fin 1))⁻¹) := by
    rw [presentsTrivialGroup_iff]
    apply eq_top_of_of_mem
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    subst hx
    have h := Subgroup.subset_normalClosure
      (s := Set.range fun _ : Fin 1 => (FreeGroup.of (0 : Fin 1))⁻¹) ⟨0, rfl⟩
    simpa using inv_mem h
  have h := substitution_removal (n := 0) (fun _ => (FreeGroup.of (0 : Fin 1))⁻¹) 0 0 1
    (by simp [rel]) htriv
  have hr : reduced (n := 0) (fun _ => (FreeGroup.of (0 : Fin 1))⁻¹) 0 0 1 = standard 0 :=
    funext fun j => j.elim0
  rw [hr] at h
  exact h

/-- The empty presentation is the rank-0 standard tuple and reaches itself. -/
example : StableReachable ⟨0, standard 0⟩ ⟨0, standard 0⟩ := empty_to_standard 0

/-- Table edges: id 257 is rejected at every rank; 256 exists. -/
theorem id257_rejected : (table[257]?).isNone = true := by decide +kernel
theorem id256_exists : (table[256]?).isSome = true := by decide +kernel

/-- Block boundaries at the ranks where they apply, from (x, y). -/
theorem edge_0 : (step ⟨2, [[(0, true)], [(1, true)]]⟩ 0).isOk = true := by decide +kernel
theorem edge_13 : (step ⟨2, [[(0, true)], [(1, true)]]⟩ 13).isOk = true := by decide +kernel
theorem edge_14 : (step ⟨2, [[(0, true)], [(1, true)]]⟩ 14).isOk = true := by decide +kernel
theorem edge_15 : (step ⟨2, [[(0, true)], [(1, true)]]⟩ 15).isOk = true := by decide +kernel
theorem edge_16 : (step ⟨2, [[(0, true)], [(1, true)]]⟩ 16).isOk = true := by decide +kernel
/-- 17 (destabilize r2) is out of rank at rank 2. -/
theorem edge_17_rejected : (step ⟨2, [[(0, true)], [(1, true)]]⟩ 17).isOk = false := by decide +kernel
/-- 22 (destabilize r7) needs rank 8; 23 (invert r2) needs rank 3. -/
theorem edge_22_rejected : (step ⟨2, [[(0, true)], [(1, true)]]⟩ 22).isOk = false := by decide +kernel
theorem edge_23_rejected : (step ⟨2, [[(0, true)], [(1, true)]]⟩ 23).isOk = false := by decide +kernel
theorem edge_23_rank3 :
    (step ⟨3, [[(0, true)], [(1, true)], [(2, true)]]⟩ 23).isOk = true := by decide +kernel
/-- 137 conjugates r0 by g3: out of rank at 2, fine at 3. -/
theorem edge_137_rejected : (step ⟨2, [[(0, true)], [(1, true)]]⟩ 137).isOk = false := by decide +kernel
theorem edge_137_rank3 :
    (step ⟨3, [[(0, true)], [(1, true)], [(2, true)]]⟩ 137).isOk = true := by decide +kernel
/-- 256 conjugates r7 by g8⁻¹: needs rank 8. -/
theorem edge_256_rejected : (step ⟨2, [[(0, true)], [(1, true)]]⟩ 256).isOk = false := by decide +kernel
theorem edge_256_rank8 :
    (step ⟨8, (List.finRange 8).map fun i => [(i, true)]⟩ 256).isOk = true := by decide +kernel
/-- Stabilize at rank 8 is rejected. -/
theorem edge_14_rank8_rejected :
    (step ⟨8, (List.finRange 8).map fun i => [(i, true)]⟩ 14).isOk = false := by decide +kernel
/-- Rank 0: every move is rejected. -/
theorem edge_rank0 : (step ⟨0, []⟩ 15).isOk = false ∧ (step ⟨0, []⟩ 0).isOk = false := by
  decide +kernel
/-- Rank 0 stabilizes to rank 1 (move 14 is applicable at rank 0). -/
theorem edge_rank0_stab : (step ⟨0, []⟩ 14).isOk = true := by decide +kernel
