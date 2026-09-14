import ACCertificate
import StableCertificate.Table

/-!
# Sound stable discovery certificates

An executable replay checker for the frozen `sac-r8-v1` move table, with a
soundness theorem against the unchanged official `AC.StableStep` relation.
Ordinary moves reuse `AC.Certificate.Move` at the current rank. Two new
executable operations, `stabApply` (move 14) and `destabApply` (moves 15–22),
are each proved to be one official `StableStep`.
-/

namespace AC.Stable

open AC.Certificate

/-- A raw presentation with its rank exposed: a list of `k` explicit words. Lists, not
functions, so that replay is plain data and no closure chain is ever rebuilt. -/
abbrev RawPres := (k : ℕ) × List (RawWord k)

/-- View a word list as a tuple; positions past the end read as the empty word. -/
def toTuple {k : ℕ} (ws : List (RawWord k)) : RawTuple k := fun i => ws.getD i.val []

theorem toTuple_ofFn {k : ℕ} (R : RawTuple k) : toTuple (List.ofFn R) = R := by
  funext i
  simp [toTuple, List.getD_eq_getElem?_getD]

/-- Interpretation in the official `Presentation` type. -/
def denoteP (P : RawPres) : Presentation := ⟨P.1, denote (toTuple P.2)⟩

/-! ## Stabilize (move 14): append generator `k+1` and the relator naming it. -/

def liftLetter {k : ℕ} (c : Letter k) : Letter (k + 1) := (c.1.castSucc, c.2)

def liftWord {k : ℕ} (w : RawWord k) : RawWord (k + 1) := w.map liftLetter

theorem liftWord_eq {k : ℕ} (w : RawWord k) :
    liftWord w = w.map fun c => (c.1.castSucc, c.2) := rfl

def stabApply {k : ℕ} (R : RawTuple k) : RawTuple (k + 1) :=
  Fin.snoc (fun j => liftWord (R j)) [(Fin.last k, true)]

theorem map_last_mk {k : ℕ} (w : RawWord k) :
    FreeGroup.map (Fin.last k).succAbove (FreeGroup.mk w) = FreeGroup.mk (liftWord w) := by
  rw [FreeGroup.map.mk]
  simp [liftWord_eq, Fin.succAbove_last_apply]

theorem denote_stabApply {k : ℕ} (R : RawTuple k) :
    denote (stabApply R) = stabilize (denote R) (Fin.last k) (Fin.last k) := by
  funext i
  simp only [stabilize]
  rw [Fin.insertNth_last']
  induction i using (Fin.last k).succAboveCases
  · simp [denote, stabApply, FreeGroup.of]
  · rename_i j
    simp [denote, stabApply, Fin.succAbove_last_apply, liftWord_eq, FreeGroup.map.mk]

theorem stab_sound {k : ℕ} (R : RawTuple k) :
    StableStep ⟨k, denote R⟩ ⟨k + 1, denote (stabApply R)⟩ := by
  rw [denote_stabApply]
  exact StableStep.stabilize (denote R) (Fin.last k) (Fin.last k)

/-! ## Destabilize (moves 15–22): delete an isolated positive singleton relator. -/

/-- Inverse of `g.succAbove` on a letter other than `g`; the letter `g` is dropped.
The proof terms match `Fin.succAbove_castPred_of_lt` and `Fin.succAbove_pred_of_lt`. -/
def unliftLetter {k : ℕ} (g : Fin (k + 1)) (c : Letter (k + 1)) : RawWord k :=
  if h : c.1 < g then
    [(c.1.castPred (Fin.ne_of_lt (Nat.lt_of_lt_of_le h g.le_last)), c.2)]
  else if h' : g < c.1 then
    [(c.1.pred (Fin.ne_of_gt (Fin.lt_of_le_of_lt g.zero_le h')), c.2)]
  else []

def unliftWord {k : ℕ} (g : Fin (k + 1)) (w : RawWord (k + 1)) : RawWord k :=
  w.flatMap (unliftLetter g)

/-- Whether the generator `g` occurs, with either sign, in a word. -/
def Mentions {k : ℕ} (g : Fin (k + 1)) (w : RawWord (k + 1)) : Prop := ∃ c ∈ w, c.1 = g

instance {k : ℕ} (g : Fin (k + 1)) (w : RawWord (k + 1)) : Decidable (Mentions g w) :=
  inferInstanceAs (Decidable (∃ c ∈ w, c.1 = g))

theorem unliftLetter_sound {k : ℕ} (g : Fin (k + 1)) (c : Letter (k + 1)) (h : c.1 ≠ g) :
    (unliftLetter g c).map (fun d => (g.succAbove d.1, d.2)) = [c] := by
  unfold unliftLetter
  rcases Fin.lt_or_lt_of_ne h with hlt | hgt
  · simp [hlt, Fin.succAbove_castPred_of_lt]
  · have hn : ¬ c.1 < g := not_lt.mpr hgt.le
    simp [hn, hgt, Fin.succAbove_pred_of_lt]

theorem unliftWord_sound {k : ℕ} (g : Fin (k + 1)) (w : RawWord (k + 1))
    (h : ¬ Mentions g w) :
    FreeGroup.map g.succAbove (FreeGroup.mk (unliftWord g w)) = FreeGroup.mk w := by
  rw [FreeGroup.map.mk]
  congr 1
  induction w with
  | nil => rfl
  | cons c w ih =>
    have hc : c.1 ≠ g := fun hc => h ⟨c, List.mem_cons_self .., hc⟩
    have hw : ¬ Mentions g w := fun ⟨d, hd, hdg⟩ => h ⟨d, List.mem_cons_of_mem _ hd, hdg⟩
    simp only [unliftWord, List.flatMap_cons, List.map_append, unliftLetter_sound g c hc]
    rw [← unliftWord, ih hw]
    rfl

/-- The precondition, and the deleted generator when it holds. -/
def destabPre {k : ℕ} (S : RawTuple (k + 1)) (i : Fin (k + 1)) : Option (Fin (k + 1)) :=
  match S i with
  | [(g, true)] =>
      if ∀ j : Fin k, ¬ Mentions g (S (i.succAbove j)) then some g else none
  | _ => none

def destabApply {k : ℕ} (S : RawTuple (k + 1)) (i : Fin (k + 1)) : Option (RawTuple k) :=
  (destabPre S i).map fun g => fun j => unliftWord g (S (i.succAbove j))

theorem destabPre_sound {k : ℕ} {S : RawTuple (k + 1)} {i g : Fin (k + 1)}
    (h : destabPre S i = some g) :
    S i = [(g, true)] ∧ ∀ j : Fin k, ¬ Mentions g (S (i.succAbove j)) := by
  unfold destabPre at h
  split at h
  · rename_i g' hSi
    split at h
    · rename_i hall
      cases h
      exact ⟨hSi, hall⟩
    · cases h
  · cases h

theorem destab_sound {k : ℕ} {S : RawTuple (k + 1)} {i : Fin (k + 1)} {R : RawTuple k}
    (h : destabApply S i = some R) :
    StableStep ⟨k + 1, denote S⟩ ⟨k, denote R⟩ := by
  unfold destabApply at h
  cases hp : destabPre S i with
  | none => simp [hp] at h
  | some g =>
    rw [hp] at h
    obtain ⟨hSi, hno⟩ := destabPre_sound hp
    have hR : R = fun j => unliftWord g (S (i.succAbove j)) := (Option.some.inj h).symm
    subst hR
    have key : stabilize (denote fun j => unliftWord g (S (i.succAbove j))) g i = denote S := by
      funext x
      induction x using i.succAboveCases
      · simp [denote, hSi, FreeGroup.of]
      · rename_i j
        simp [denote, unliftWord_sound g _ (hno j)]
    rw [← key]
    exact StableStep.destabilize _ g i

/-! ## Decoding the frozen table at the current rank. -/

/-- Rejection reasons, mirroring the official verifier's `E_BAD_MOVE_ID` and the four
`E_MOVE_NOT_APPLICABLE` reasons. -/
inductive Err
  | badMoveId
  | relatorOutOfRank
  | generatorOutOfRank
  | maxRankExceeded
  | destabilizePrecondition
  deriving DecidableEq, Repr

/-- The frozen rank cap of `sac-r8-v1`. Soundness does not depend on it. -/
def maxRank : ℕ := 8

/-- Apply an ordinary typed move to a word list. -/
def applyOrd {k : ℕ} (ws : List (RawWord k)) (m : Move k) : List (RawWord k) :=
  List.ofFn (m.apply (toTuple ws))

/-- Apply one table row at the current rank, in the official verifier's check order. -/
def stepRow (P : RawPres) : Row → Except Err RawPres
  | .stabilize _ =>
      if P.1 < maxRank then .ok ⟨P.1 + 1, List.ofFn (stabApply (toTuple P.2))⟩
      else .error .maxRankExceeded
  | .destabilize i _ =>
      match P with
      | ⟨0, _⟩ => .error .relatorOutOfRank
      | ⟨k + 1, S⟩ =>
          if h : i < k + 1 then
            match destabApply (toTuple S) ⟨i, h⟩ with
            | some R => .ok ⟨k, List.ofFn R⟩
            | none => .error .destabilizePrecondition
          else .error .relatorOutOfRank
  | .inversion i _ =>
      if h : i < P.1 then .ok ⟨P.1, applyOrd P.2 (Move.inv ⟨i, h⟩)⟩
      else .error .relatorOutOfRank
  | .multiplication i j io _ =>
      if hi : i < P.1 then
        if hj : j < P.1 then
          if hij : i ≠ j then
            let ne : (⟨i, hi⟩ : Fin P.1) ≠ ⟨j, hj⟩ := fun e => hij (Fin.mk.inj e)
            if io then .ok ⟨P.1, applyOrd P.2 (Move.mulInvRight ⟨i, hi⟩ ⟨j, hj⟩ ne)⟩
            else .ok ⟨P.1, applyOrd P.2 (Move.mulRight ⟨i, hi⟩ ⟨j, hj⟩ ne)⟩
          else .error .badMoveId
        else .error .relatorOutOfRank
      else .error .relatorOutOfRank
  | .conjugation i c _ =>
      if hi : i < P.1 then
        if hc : 1 ≤ c.natAbs ∧ c.natAbs ≤ P.1 then
          .ok ⟨P.1, applyOrd P.2 (Move.conj ⟨i, hi⟩ (⟨c.natAbs - 1, by omega⟩, decide (0 < c)))⟩
        else .error .generatorOutOfRank
      else .error .relatorOutOfRank

def step (P : RawPres) (id : ℕ) : Except Err RawPres :=
  match table[id]? with
  | none => .error .badMoveId
  | some row => stepRow P row

theorem ord_sound {k : ℕ} (ws : List (RawWord k)) (m : Move k) :
    StableReachable (denoteP ⟨k, ws⟩) (denoteP ⟨k, applyOrd ws m⟩) := by
  simp only [denoteP, applyOrd, toTuple_ofFn]
  exact (m.sound (toTuple ws)).reachable.stable

theorem stepRow_sound {P Q : RawPres} {r : Row} (h : stepRow P r = .ok Q) :
    StableReachable (denoteP P) (denoteP Q) := by
  obtain ⟨k, ws⟩ := P
  cases r with
  | stabilize _ =>
    simp only [stepRow] at h
    split at h
    · cases h
      simp only [denoteP, toTuple_ofFn]
      exact Relation.ReflTransGen.single (stab_sound (toTuple ws))
    · cases h
  | destabilize i _ =>
    cases k with
    | zero => simp [stepRow] at h
    | succ k =>
      simp only [stepRow] at h
      split at h
      · rename_i hi
        split at h
        · rename_i R' hR'
          cases h
          simp only [denoteP, toTuple_ofFn]
          exact Relation.ReflTransGen.single (destab_sound hR')
        · cases h
      · cases h
  | inversion i _ =>
    simp only [stepRow] at h
    split at h
    · cases h; exact ord_sound ws _
    · cases h
  | multiplication i j io _ =>
    simp only [stepRow] at h
    split at h
    · split at h
      · split at h
        · split at h
          · cases h; exact ord_sound ws _
          · cases h; exact ord_sound ws _
        · cases h
      · cases h
    · cases h
  | conjugation i c _ =>
    simp only [stepRow] at h
    split at h
    · split at h
      · cases h; exact ord_sound ws _
      · cases h
    · cases h

theorem step_sound {P Q : RawPres} {id : ℕ} (h : step P id = .ok Q) :
    StableReachable (denoteP P) (denoteP Q) := by
  unfold step at h
  split at h
  · cases h
  · exact stepRow_sound h

/-! ## Replay and the endpoint. -/

/-- Replay from move index `idx`; an error carries the 0-based index of the rejected move. -/
def replayFrom (idx : ℕ) (P : RawPres) : List ℕ → Except (ℕ × Err) RawPres
  | [] => .ok P
  | id :: ids =>
      match step P id with
      | .ok Q => replayFrom (idx + 1) Q ids
      | .error e => .error (idx, e)

theorem replayFrom_sound {P Q : RawPres} {idx : ℕ} {ids : List ℕ}
    (h : replayFrom idx P ids = .ok Q) : StableReachable (denoteP P) (denoteP Q) := by
  induction ids generalizing P idx with
  | nil =>
    have hPQ : P = Q := Except.ok.inj h
    subst hPQ
    exact Relation.ReflTransGen.refl
  | cons id ids ih =>
    rw [replayFrom] at h
    split at h
    · rename_i Q' hs
      exact (step_sound hs).trans (ih h)
    · cases h

/-- The official stable target is the empty presentation, rank zero. -/
def isEmpty : RawPres → Bool
  | ⟨0, _⟩ => true
  | _ => false

/-- Exact replay from rank 2 to the empty presentation. -/
def check (R : RawTuple 2) (ids : List ℕ) : Bool :=
  match replayFrom 0 ⟨2, List.ofFn R⟩ ids with
  | .ok P => isEmpty P
  | .error _ => false

theorem denote_rank0 (R : RawTuple 0) : denote R = standard 0 :=
  funext fun i => i.elim0

/-- The empty presentation reaches the official rank-2 endpoint by two stabilizations. -/
theorem empty_to_standard2 : StableReachable ⟨0, standard 0⟩ ⟨2, standard 2⟩ := by
  have h1 : StableStep ⟨0, standard 0⟩ ⟨1, standard 1⟩ := by
    simpa using StableStep.stabilize (standard 0) (Fin.last 0) (Fin.last 0)
  have h2 : StableStep ⟨1, standard 1⟩ ⟨2, standard 2⟩ := by
    simpa using StableStep.stabilize (standard 1) (Fin.last 1) (Fin.last 1)
  exact (Relation.ReflTransGen.single h1).tail h2

/-- An accepted stable certificate is a finite official stable path to `⟨2, standard 2⟩`. -/
theorem check_sound {R : RawTuple 2} {ids : List ℕ} (h : check R ids = true) :
    StableReachable ⟨2, denote R⟩ ⟨2, standard 2⟩ := by
  unfold check at h
  split at h
  · rename_i P hr
    obtain ⟨k, T⟩ := P
    cases k with
    | succ k => simp [isEmpty] at h
    | zero =>
      have hp := replayFrom_sound hr
      simp only [denoteP, toTuple_ofFn, denote_rank0] at hp
      exact hp.trans empty_to_standard2
  · cases h

/-! ## Encoded interface, reusing the ordinary checker's rank-2 parser. -/

def checkEncoded (words : List (List ℤ)) (ids : List ℤ) : Bool :=
  match parseTuple words, parseIds ids with
  | some R, some ms => check R ms
  | _, _ => false

/-- The parsed rank-2 tuple has a finite official stable path to the standard tuple. -/
def EncodedStableSolvable (words : List (List ℤ)) : Prop :=
  ∃ R, parseTuple words = some R ∧ StableReachable ⟨2, denote R⟩ ⟨2, standard 2⟩

theorem checkEncoded_sound {words : List (List ℤ)} {ids : List ℤ}
    (h : checkEncoded words ids = true) : EncodedStableSolvable words := by
  unfold checkEncoded at h
  split at h
  · rename_i R ms hr hm
    exact ⟨R, hr, check_sound h⟩
  · cases h

end AC.Stable
