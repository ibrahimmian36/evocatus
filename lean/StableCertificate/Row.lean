/-!
# Rows of the frozen `sac-r8-v1` move table

One constructor per official category. Parameters are plain naturals and
integers exactly as in the specification file; rank checks happen at decode
time. The `inverse` column is carried only so the table can be re-serialized
and diffed against the specification.
-/

namespace AC.Stable

inductive Row
  | inversion (relator : Nat) (inverse : Option Nat)
  | multiplication (relator other : Nat) (invertOther : Bool) (inverse : Option Nat)
  | conjugation (relator : Nat) (conjugator : Int) (inverse : Option Nat)
  | stabilize (inverse : Option Nat)
  | destabilize (relator : Nat) (inverse : Option Nat)
  deriving DecidableEq, Repr

/-- Canonical JSON with sorted keys and no whitespace, matching RFC 8785 for these
values, so that `python3 -c 'json.dumps(row, sort_keys=True, separators=(",",":"))'`
agrees byte for byte. -/
def Row.toCanonicalJson (id : Nat) : Row → String
  | .inversion r inv =>
      s!"\{\"category\":\"inversion\",\"id\":{id},\"inverse\":{jsonOpt inv},\"relator\":{r}}"
  | .multiplication r o io inv =>
      s!"\{\"category\":\"multiplication\",\"id\":{id},\"inverse\":{jsonOpt inv},\"invert_other\":{io},\"other\":{o},\"relator\":{r}}"
  | .conjugation r c inv =>
      s!"\{\"category\":\"conjugation\",\"conjugator\":{c},\"id\":{id},\"inverse\":{jsonOpt inv},\"relator\":{r}}"
  | .stabilize inv =>
      s!"\{\"category\":\"stabilize\",\"id\":{id},\"inverse\":{jsonOpt inv}}"
  | .destabilize r inv =>
      s!"\{\"category\":\"destabilize\",\"id\":{id},\"inverse\":{jsonOpt inv},\"relator\":{r}}"
where
  jsonOpt : Option Nat → String
    | none => "null"
    | some n => toString n

end AC.Stable
