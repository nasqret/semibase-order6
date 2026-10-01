import SemigroupBasis.CoRoots.S5_831Invariant

/-!
# Hull 23.1 phase-parity invariant and deterministic renderer

This module contains only basis-independent syntax.  It packages the complete
`S5_831` first-occurrence phase profile together with the parity of every
supported letter, and defines a canonical list from that package.

The renderer is the literal Lee--Zhang (23.3) shape.  Before the final
doubled phase, doubled markers use exponent two or three according to their
parity.  Undoubled even markers contribute one ordered debt copy.  The final
doubled marker uses exponent two when even; when odd it uses exponent one if
the prior debt already witnesses the doubled gap and exponent three
otherwise.  That debt is followed by the trailing undoubled markers.  The
later normalization proof can therefore target this renderer without
consulting the source word's raw history.
-/

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull23_1PhaseParityInvariant

open SemigroupBasis.CoRoots.S5_831

/-- Parities, in first-occurrence order, aligned with `phaseProfile`. -/
def phaseParityCoordinates (word : Word Nat) : List Nat :=
  (phaseLabels (phaseProfile word)).map
    (fun letter => word.toList.count letter % 2)

/-- The exact syntactic key used by the Hull 23.1 normalization. -/
structure PhaseParityKey where
  phases : List Phase
  parities : List Nat
deriving Repr, DecidableEq

/-- Package a word's phase profile and supported-letter parity vector. -/
def phaseParityKey (word : Word Nat) : PhaseParityKey where
  phases := phaseProfile word
  parities := phaseParityCoordinates word

@[simp]
theorem phaseParityKey_phases (word : Word Nat) :
    (phaseParityKey word).phases = phaseProfile word :=
  rfl

@[simp]
theorem phaseParityKey_parities (word : Word Nat) :
    (phaseParityKey word).parities = phaseParityCoordinates word :=
  rfl

theorem phaseParityCoordinates_length (word : Word Nat) :
    (phaseParityCoordinates word).length =
      (phaseProfile word).length := by
  simp [phaseParityCoordinates, phaseLabels]

/-- Equality of phase profiles and all count parities gives literal key
equality. -/
theorem phaseParityKey_eq_of_invariants
    {left right : Word Nat}
    (samePhases : phaseProfile left = phaseProfile right)
    (sameParity :
      forall letter,
        left.toList.count letter % 2 =
          right.toList.count letter % 2) :
    phaseParityKey left = phaseParityKey right := by
  have sameCoordinates :
      phaseParityCoordinates left =
        phaseParityCoordinates right := by
    unfold phaseParityCoordinates
    rw [samePhases]
    apply List.map_congr_left
    intro letter _
    exact sameParity letter
  change
    PhaseParityKey.mk (phaseProfile left)
        (phaseParityCoordinates left) =
      PhaseParityKey.mk (phaseProfile right)
        (phaseParityCoordinates right)
  rw [samePhases, sameCoordinates]

/-- One aligned phase/parity entry used by the executable renderer. -/
structure PhaseParityEntry where
  phase : Phase
  parity : Nat
deriving Repr, DecidableEq

/-- Zip phases with parity coordinates.  The odd fallback is unreachable for
keys constructed by `phaseParityKey`, whose two fields have equal length; it
makes the renderer total on arbitrary values of `PhaseParityKey`. -/
def phaseParityEntries :
    List Phase -> List Nat -> List PhaseParityEntry
  | [], _ => []
  | phase :: rest, [] =>
      { phase := phase, parity := 1 } ::
        phaseParityEntries rest []
  | phase :: rest, parity :: parities =>
      { phase := phase, parity := parity % 2 } ::
        phaseParityEntries rest parities

theorem phaseParityEntries_ne_nil_of_phases_ne_nil
    {phases : List Phase} (nonempty : phases ≠ [])
    (parities : List Nat) :
    phaseParityEntries phases parities ≠ [] := by
  cases phases with
  | nil =>
      exact (nonempty rfl).elim
  | cons phase rest =>
      cases parities <;> simp [phaseParityEntries]

/-- Whether the remaining entry stream contains a doubled phase. -/
def hasDoubledPhase : List PhaseParityEntry -> Bool
  | [] => false
  | entry :: rest =>
      entry.phase.doubled || hasDoubledPhase rest

/-- Render only the marker of each entry.  This is the trailing part after
the last doubled phase (and the whole renderer when no phase is doubled). -/
def renderPhaseMarkers : List PhaseParityEntry -> List Nat
  | [] => []
  | entry :: rest =>
      entry.phase.label :: renderPhaseMarkers rest

/-- A doubled phase before the last doubled phase: exponent two for even
parity and exponent three for odd parity. -/
def renderPriorDoubledPower
    (entry : PhaseParityEntry) : List Nat :=
  if entry.parity % 2 = 0 then
    [entry.phase.label, entry.phase.label]
  else
    [entry.phase.label, entry.phase.label, entry.phase.label]

/-- The last doubled phase.  An even marker has exponent two.  An odd marker
has exponent one when prior debt makes the gap nonempty, and exponent three
when it must witness the doubled gap itself. -/
def renderLastDoubledPower
    (debt : List Nat) (entry : PhaseParityEntry) : List Nat :=
  if entry.parity % 2 = 0 then
    [entry.phase.label, entry.phase.label]
  else if debt = [] then
    [entry.phase.label, entry.phase.label, entry.phase.label]
  else
    [entry.phase.label]

/-- An undoubled marker contributes one later debt copy exactly when its
target parity is even.  Appending preserves first-occurrence marker order. -/
def extendParityDebt
    (debt : List Nat) (entry : PhaseParityEntry) : List Nat :=
  if entry.parity % 2 = 0 then
    debt ++ [entry.phase.label]
  else
    debt

/-- Literal Lee--Zhang (23.3) rendering.  `debt` contains, in marker order,
the even undoubled markers preceding the last doubled phase. -/
def renderLeeZhang23_3Aux
    (debt : List Nat) :
    List PhaseParityEntry -> List Nat
  | [] => []
  | entry :: rest =>
      if entry.phase.doubled then
        if hasDoubledPhase rest then
          renderPriorDoubledPower entry ++
            renderLeeZhang23_3Aux debt rest
        else
          renderLastDoubledPower debt entry ++
            debt ++ renderPhaseMarkers rest
      else if hasDoubledPhase rest then
        entry.phase.label ::
          renderLeeZhang23_3Aux (extendParityDebt debt entry) rest
      else
        renderPhaseMarkers (entry :: rest)

def renderPhaseParityEntries
    (entries : List PhaseParityEntry) : List Nat :=
  renderLeeZhang23_3Aux [] entries

theorem renderLeeZhang23_3Aux_ne_nil_of_entries_ne_nil
    (debt : List Nat)
    {entries : List PhaseParityEntry} (nonempty : entries ≠ []) :
    renderLeeZhang23_3Aux debt entries ≠ [] := by
  cases entries with
  | nil =>
      exact (nonempty rfl).elim
  | cons entry rest =>
      cases doubled : entry.phase.doubled with
      | false =>
          cases more : hasDoubledPhase rest <;>
            simp [renderLeeZhang23_3Aux, doubled, more,
              renderPhaseMarkers]
      | true =>
          cases more : hasDoubledPhase rest with
          | false =>
              by_cases even : entry.parity % 2 = 0
              · simp [renderLeeZhang23_3Aux, doubled, more,
                  renderLastDoubledPower, even]
              · by_cases debtEmpty : debt = []
                · simp [renderLeeZhang23_3Aux, doubled, more,
                    renderLastDoubledPower, even, debtEmpty]
                · simp [renderLeeZhang23_3Aux, doubled, more,
                    renderLastDoubledPower, even, debtEmpty]
          | true =>
              by_cases even : entry.parity % 2 = 0 <;>
                simp [renderLeeZhang23_3Aux, doubled, more,
                  renderPriorDoubledPower, even]

theorem renderPhaseParityEntries_ne_nil_of_entries_ne_nil
    {entries : List PhaseParityEntry} (nonempty : entries ≠ []) :
    renderPhaseParityEntries entries ≠ [] :=
  renderLeeZhang23_3Aux_ne_nil_of_entries_ne_nil [] nonempty

/-- The canonical list selected by a phase-parity key. -/
def renderPhaseParityKeyList (key : PhaseParityKey) : List Nat :=
  renderPhaseParityEntries
    (phaseParityEntries key.phases key.parities)

/-- The canonical rendered list selected from a source word. -/
def canonicalPhaseParityList (word : Word Nat) : List Nat :=
  renderPhaseParityKeyList (phaseParityKey word)

theorem canonicalPhaseParityList_ne_nil (word : Word Nat) :
    canonicalPhaseParityList word ≠ [] := by
  apply renderPhaseParityEntries_ne_nil_of_entries_ne_nil
  apply phaseParityEntries_ne_nil_of_phases_ne_nil
  exact phaseProfile_ne_nil word

/-- Total conversion of a rendered list to a nonempty word.  The empty case
is irrelevant for keys coming from words because `phaseProfile` is nonempty. -/
def renderedWord : List Nat -> Word Nat
  | [] => Word.singleton 0
  | head :: tail => { head := head, tail := tail }

theorem toList_renderedWord_of_ne_nil
    {letters : List Nat} (nonempty : letters ≠ []) :
    (renderedWord letters).toList = letters := by
  cases letters with
  | nil =>
      exact (nonempty rfl).elim
  | cons head tail =>
      rfl

/-- The canonical word selected by a phase-parity key. -/
def renderPhaseParityKey (key : PhaseParityKey) : Word Nat :=
  renderedWord (renderPhaseParityKeyList key)

/-- The canonical word selected from a source word, only through its key. -/
def canonicalPhaseParityWord (word : Word Nat) : Word Nat :=
  renderPhaseParityKey (phaseParityKey word)

@[simp]
theorem toList_canonicalPhaseParityWord (word : Word Nat) :
    (canonicalPhaseParityWord word).toList =
      canonicalPhaseParityList word := by
  apply toList_renderedWord_of_ne_nil
  exact canonicalPhaseParityList_ne_nil word

/-- Equal keys render to literally equal canonical lists. -/
theorem renderPhaseParityKeyList_eq_of_key_eq
    {left right : PhaseParityKey}
    (same : left = right) :
    renderPhaseParityKeyList left =
      renderPhaseParityKeyList right := by
  cases same
  rfl

theorem canonicalPhaseParityList_eq_of_key_eq
    {left right : Word Nat}
    (same : phaseParityKey left = phaseParityKey right) :
    canonicalPhaseParityList left =
      canonicalPhaseParityList right :=
  renderPhaseParityKeyList_eq_of_key_eq same

/-- Equal keys render to literally equal canonical words. -/
theorem renderPhaseParityKey_eq_of_key_eq
    {left right : PhaseParityKey}
    (same : left = right) :
    renderPhaseParityKey left = renderPhaseParityKey right := by
  cases same
  rfl

/-- The interface consumed by the two-sided normalization proof. -/
theorem canonicalPhaseParityWord_eq_of_key_eq
    {left right : Word Nat}
    (same : phaseParityKey left = phaseParityKey right) :
    canonicalPhaseParityWord left =
      canonicalPhaseParityWord right :=
  renderPhaseParityKey_eq_of_key_eq same

/-- Phase equality and pointwise parity equality select one canonical word. -/
theorem canonicalPhaseParityWord_eq_of_invariants
    {left right : Word Nat}
    (samePhases : phaseProfile left = phaseProfile right)
    (sameParity :
      forall letter,
        left.toList.count letter % 2 =
          right.toList.count letter % 2) :
    canonicalPhaseParityWord left =
      canonicalPhaseParityWord right :=
  canonicalPhaseParityWord_eq_of_key_eq
    (phaseParityKey_eq_of_invariants samePhases sameParity)

end Order6Hull23_1PhaseParityInvariant
end CoRoots
end SemigroupBasis
