import Lean.Data.Json
import StableCertificate

/-!
# `stablecheck`: line-oriented front end for the differential tests

Reads JSON objects, one per line, from stdin and writes one JSON object per line.

* `{"kind":"step","state":[[..],..],"move":m}` →
  `{"ok":true,"state":[[..],..]}` or `{"ok":false,"reason":"…"}`
* `{"kind":"path","start":[[..],[..]],"moves":[..]}` →
  `{"ok":true,"final":[[..],..],"empty":bool}` or `{"ok":false,"reason":"…","move_index":i}`
* `{"kind":"table"}` → one canonical-JSON row per line, then `{"done":257}`
* `{"kind":"check","start":[[..],[..]],"moves":[..]}` → `{"accepted":bool}` using the
  rank-2 `checkEncoded` whose soundness theorem is `checkEncoded_sound`.

Everything here is untrusted glue; the trusted claim is the Lean theorem.
-/

open Lean AC.Stable AC.Certificate

def jsonIntsList (j : Json) : Except String (List ℤ) := do
  let arr ← j.getArr?
  arr.toList.mapM fun x => x.getInt?

def jsonWords (j : Json) : Except String (List (List ℤ)) := do
  let arr ← j.getArr?
  arr.toList.mapM jsonIntsList

def wordsToJson (ws : List (List ℤ)) : Json := toJson ws

def handleStep (o : Json) : Except String Json := do
  let words ← jsonWords (← o.getObjVal? "state")
  let m ← (← o.getObjVal? "move").getInt?
  let some P := parsePres words | throw "unparseable state"
  if m < 0 then
    return Json.mkObj [("ok", false), ("reason", "E_BAD_MOVE_ID")]
  match step P m.toNat with
  | .ok Q => return Json.mkObj [("ok", true), ("state", wordsToJson (encodePres Q))]
  | .error e => return Json.mkObj [("ok", false), ("reason", e.reason)]

def handlePath (o : Json) : Except String Json := do
  let words ← jsonWords (← o.getObjVal? "start")
  let moves ← jsonIntsList (← o.getObjVal? "moves")
  let some P := parsePres words | throw "unparseable start"
  match moves.findIdx? (· < 0) with
  | some i => return Json.mkObj [("ok", false), ("reason", "E_BAD_MOVE_ID"), ("move_index", i)]
  | none =>
    match replayFrom 0 P (moves.map Int.toNat) with
    | .ok Q =>
      return Json.mkObj [("ok", true), ("final", wordsToJson (encodePres Q)),
        ("empty", isEmpty Q)]
    | .error (i, e) =>
      return Json.mkObj [("ok", false), ("reason", e.reason), ("move_index", i)]

def handleCheck (o : Json) : Except String Json := do
  let words ← jsonWords (← o.getObjVal? "start")
  let moves ← jsonIntsList (← o.getObjVal? "moves")
  return Json.mkObj [("accepted", AC.Stable.checkEncoded words moves)]

/-- The ordinary rank-2 checker from the upstream package, for the `ac-r2-v1` vectors. -/
def handleCheckAC (o : Json) : Except String Json := do
  let words ← jsonWords (← o.getObjVal? "start")
  let moves ← jsonIntsList (← o.getObjVal? "moves")
  return Json.mkObj [("accepted", AC.Certificate.checkEncoded words moves)]

partial def loop (h : IO.FS.Stream) (out : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  let line := String.ofList (line.toList.reverse.dropWhile Char.isWhitespace).reverse
  if line.isEmpty then loop h out else
  let res : Except String Json := do
    let j ← Json.parse line
    let kind ← (← j.getObjVal? "kind").getStr?
    match kind with
    | "step" => handleStep j
    | "path" => handlePath j
    | "check" => handleCheck j
    | "check_ac" => handleCheckAC j
    | "table" => pure (Json.mkObj [("done", table.size)])
    | k => throw s!"unknown kind {k}"
  match res with
  | .ok j =>
    if (j.getObjVal? "done").toBool then
      for l in tableJsonLines do out.putStrLn l
    out.putStrLn j.compress
  | .error e => out.putStrLn (Json.mkObj [("error", e)]).compress
  out.flush
  loop h out

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
