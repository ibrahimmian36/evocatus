import StableCertificate.Encode
import StableCertificate.Official

/-!
# Certificates from any starting rank

The Discovery Track starts every challenge at rank 2, and `checkEncoded` follows
that. Certificates for the families proved here start at any rank, so this module
adds a checker whose input is a word list of any length `k`, with the soundness
theorem `StableReachable ⟨k, R⟩ ⟨k, standard k⟩`. The parser `parsePres` is part of
the statement.
-/

namespace AC.Stable

/-- Replay from the parsed presentation of any rank to the empty presentation. -/
def checkEncodedAt (words : List (List ℤ)) (ids : List ℤ) : Bool :=
  match parsePres words, AC.Certificate.parseIds ids with
  | some P, some ms =>
      match replayFrom 0 P ms with
      | .ok Q => isEmpty Q
      | .error _ => false
  | _, _ => false

theorem checkEncodedAt_sound {words : List (List ℤ)} {ids : List ℤ}
    (h : checkEncodedAt words ids = true) :
    ∃ P : RawPres, parsePres words = some P ∧
      StableReachable ⟨P.1, AC.Certificate.denote (toTuple P.2)⟩ ⟨P.1, standard P.1⟩ := by
  unfold checkEncodedAt at h
  split at h
  · rename_i P ms hp hm
    refine ⟨P, hp, ?_⟩
    split at h
    · rename_i Q hr
      obtain ⟨k, T⟩ := Q
      cases k with
      | succ k => simp [isEmpty] at h
      | zero =>
        have hp := replayFrom_sound hr
        simp only [denoteP, denote_rank0] at hp
        exact hp.trans (empty_to_standard P.1)
    · cases h
  · cases h

end AC.Stable
