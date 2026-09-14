import StableCertificate.Core

/-!
# Integer encoding at every rank

Untrusted conveniences for the test harness: parse a rank-`k` tuple from the
official `±1..±k` integer encoding, and print a state back. The headline
theorem uses only the rank-2 parser inherited from the ordinary checker.
-/

namespace AC.Stable

open AC.Certificate

def parseLetterAt (k : ℕ) (a : ℤ) : Option (Letter k) :=
  if h : 1 ≤ a ∧ a ≤ k then some (⟨a.toNat - 1, by omega⟩, true)
  else if h' : -(k : ℤ) ≤ a ∧ a ≤ -1 then some (⟨(-a).toNat - 1, by omega⟩, false)
  else none

def parseWordAt (k : ℕ) (w : List ℤ) : Option (RawWord k) := w.mapM (parseLetterAt k)

/-- Parse `k` words into a rank-`k` tuple; the list length fixes the rank. -/
def parsePres (words : List (List ℤ)) : Option RawPres := do
  let k := words.length
  let ws ← words.mapM (parseWordAt k)
  pure ⟨k, ws⟩

def encodeLetter {k : ℕ} (c : Letter k) : ℤ :=
  if c.2 then (c.1.val : ℤ) + 1 else -((c.1.val : ℤ) + 1)

def encodePres (P : RawPres) : List (List ℤ) := P.2.map fun w => w.map encodeLetter

def Err.reason : Err → String
  | .badMoveId => "E_BAD_MOVE_ID"
  | .relatorOutOfRank => "relator_out_of_rank"
  | .generatorOutOfRank => "generator_out_of_rank"
  | .maxRankExceeded => "max_rank_exceeded"
  | .destabilizePrecondition => "destabilize_precondition"

/-- Re-serialize the frozen table row by row, for diffing against the specification. -/
def tableJsonLines : List String :=
  (List.range table.size).filterMap fun id => (table[id]?).map (Row.toCanonicalJson id)

end AC.Stable
