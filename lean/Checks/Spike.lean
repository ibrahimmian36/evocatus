import StableCertificate

/-! Phase 1 spike: kernel-check the official rank-3 detour golden vector. -/

open AC.Stable

theorem detour_kernel :
    checkEncoded [[1], [2]] [14, 161, 162, 17, 16, 15] = true := by
  decide +kernel

theorem detour_solvable : EncodedStableSolvable [[1], [2]] :=
  checkEncoded_sound detour_kernel

/-- Negative control: a truncated path must be rejected by the executable checker. -/
theorem detour_truncated_rejected :
    checkEncoded [[1], [2]] [14, 161, 162, 17, 16] = false := by
  decide +kernel

#print axioms detour_solvable
#print axioms AC.Stable.checkEncoded_sound
