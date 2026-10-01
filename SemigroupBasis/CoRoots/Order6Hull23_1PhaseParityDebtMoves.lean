import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityMoves
import SemigroupBasis.CoRoots.S5_107ListDerives

/-!
# Hull 23.1 witnessed debt moves

This module packages the two operations used in the middle of the
Lee--Zhang Proposition 23.1 normalization.  Law (23.1e) permutes a later
block after witnesses for all its letters have appeared.  Law (23.1f)
moves one witnessed debt letter across an explicit terminal square while
adding two copies of the active marker.

The block induction below is proved directly from those two B15 moves.  It
does not import, or transport a derivation from, the Proposition 21.1
normalizer.  Its intermediate terminal debt records the literal order in
which repeated applications of (23.1f) produce marker/debt pairs; the final
theorem permits any exactly permuted terminal debt.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull23_1PhaseParityDebtMoves

open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityMoves

private abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Order6Subdirect.Hull23_1_S3_11_S5_831.publishedBasis

/-- List-level derivability by the literal fifteen-law Proposition 23.1
basis. -/
abbrev HullListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

/-! ## Witnessed permutations from (23.1e) -/

/-- Once both letters occur in `witnesses`, their adjacent later
occurrences can be swapped.  The proof locates the two witnesses in either
order and applies the corresponding orientation of (23.1e). -/
theorem hullListDerivesWitnessedAdjacentSwap
    (witnesses suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ witnesses)
    (rightSeen : right ∈ witnesses) :
    HullListDerives
      (witnesses ++ [left, right] ++ suffix)
      (witnesses ++ [right, left] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  · obtain ⟨leftBefore, leftAfter, witnessSplit⟩ :=
      List.mem_iff_append.mp leftSeen
    have rightInSplit :
        right ∈ leftBefore ∨ right ∈ leftAfter := by
      rw [witnessSplit] at rightSeen
      rcases List.mem_append.mp rightSeen with beforeMember | afterMember
      · exact Or.inl beforeMember
      · rcases List.mem_cons.mp afterMember with atLeft | inAfter
        · exact False.elim (equal atLeft.symm)
        · exact Or.inr inAfter
    rcases rightInSplit with rightBefore | rightAfter
    · obtain ⟨before, middle, beforeSplit⟩ :=
        List.mem_iff_append.mp rightBefore
      have displayed :=
        hullListDerivesExchange
          before suffix middle leftAfter right left
      simpa [witnessSplit, beforeSplit, List.append_assoc] using
        displayed.symm
    · obtain ⟨middle, after, afterSplit⟩ :=
        List.mem_iff_append.mp rightAfter
      simpa [witnessSplit, afterSplit, List.append_assoc] using
        hullListDerivesExchange
          leftBefore suffix middle after left right

/-- Any permutation of a later tail is derivable once every source letter
already has a witness in the fixed prefix. -/
theorem hullListDerivesWitnessedTailPermutation
    (witnesses suffix : List Nat)
    {source target : List Nat}
    (sourceSeen :
      forall letter, letter ∈ source -> letter ∈ witnesses)
    (permutation : source.Perm target) :
    HullListDerives
      (witnesses ++ source ++ suffix)
      (witnesses ++ target ++ suffix) := by
  induction permutation generalizing witnesses suffix with
  | nil =>
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | cons head permutation induction =>
      have tailDerivation :=
        induction
          (witnesses ++ [head]) suffix
          (fun letter member =>
            List.mem_append.mpr <|
              Or.inl <|
                sourceSeen letter (List.Mem.tail head member))
      simpa [List.append_assoc] using tailDerivation
  | swap first second rest =>
      have firstSeen : first ∈ witnesses :=
        sourceSeen first (by simp)
      have secondSeen : second ∈ witnesses :=
        sourceSeen second (by simp)
      simpa [List.append_assoc] using
        hullListDerivesWitnessedAdjacentSwap
          witnesses (rest ++ suffix)
          second first secondSeen firstSeen
  | trans firstPermutation _ firstInduction secondInduction =>
      have firstDerivation :=
        firstInduction witnesses suffix sourceSeen
      have secondDerivation :=
        secondInduction witnesses suffix (by
          intro letter member
          exact sourceSeen letter
            ((firstPermutation.mem_iff).mpr member))
      exact firstDerivation.trans secondDerivation

/-! ## Debt transport from (23.1f) -/

/-- Move one later occurrence of `debtLetter` across the displayed terminal
square.  Its earlier witness is allowed anywhere in `witnesses`.  This is
the form of (23.1f) used by the block induction. -/
theorem hullListDerivesBalanceAcrossTerminalSquare
    (witnesses middle suffix : List Nat)
    (marker debtLetter squareMarker : Nat)
    (debtSeen : debtLetter ∈ witnesses) :
    HullListDerives
      (witnesses ++ [marker, debtLetter] ++ middle ++
        [squareMarker, squareMarker] ++ suffix)
      (witnesses ++ [marker, marker] ++ middle ++
        [squareMarker, squareMarker, marker, debtLetter] ++ suffix) := by
  obtain ⟨before, after, witnessSplit⟩ :=
    List.mem_iff_append.mp debtSeen
  simpa [witnessSplit, List.append_assoc] using
    hullListDerivesBalance
      before suffix after middle marker debtLetter squareMarker

/-- Terminal marker/debt pairs in the literal order emitted by successive
applications of (23.1f).  For input `[y1, ..., yp]` this is
`[marker, yp, ..., marker, y1]`. -/
def terminalDebtPairs (marker : Nat) : List Nat -> List Nat
  | [] => []
  | debtLetter :: rest =>
      terminalDebtPairs marker rest ++ [marker, debtLetter]

/-- The terminal pairs contain only the active marker and letters of the
original debt block.  Conversely, each such letter occurs in the pair
list, except that an empty debt has no marker pair. -/
theorem mem_terminalDebtPairs_iff
    (letter marker : Nat) (debt : List Nat) :
    letter ∈ terminalDebtPairs marker debt ↔
      (debt ≠ [] ∧ letter = marker) ∨ letter ∈ debt := by
  induction debt with
  | nil =>
      simp [terminalDebtPairs]
  | cons head rest induction =>
      by_cases empty : rest = []
      · subst rest
        simp [terminalDebtPairs]
      · simp [terminalDebtPairs, induction, empty, or_assoc,
          or_left_comm, or_comm]

/-- The emitted pair list has exactly one marker and one original debt
letter per Balance step.  This is stronger than parity preservation: it is
an equality of every multiplicity, packaged as a permutation. -/
theorem terminalDebtPairs_perm_replicate_append
    (marker : Nat) (debt : List Nat) :
    (terminalDebtPairs marker debt).Perm
      (List.replicate debt.length marker ++ debt) := by
  rw [List.perm_iff_count]
  intro letter
  induction debt with
  | nil =>
      simp [terminalDebtPairs]
  | cons head rest induction =>
      simp only [terminalDebtPairs, List.length_cons,
        List.replicate_succ, List.count_append, List.count_cons,
        List.count_nil, induction]
      ac_rfl

/-- Raw Lee--Zhang debt sweep.  Every debt letter is witnessed in `stem`.
Each Balance step removes the next debt letter from before `middle`, adds
one marker to the active power, and records a marker/debt pair after the
terminal square.  Thus the left marker power grows from one to
`debt.length + 1`, accounting for exactly the two marker occurrences added
per step. -/
theorem hullListDerivesMoveWitnessedDebtBlockRaw
    (stem middle suffix debt : List Nat)
    (marker squareMarker : Nat)
    (debtSeen :
      forall letter, letter ∈ debt -> letter ∈ stem) :
    HullListDerives
      (stem ++ [marker] ++ debt ++ middle ++
        [squareMarker, squareMarker] ++ suffix)
      (stem ++ List.replicate (debt.length + 1) marker ++ middle ++
        [squareMarker, squareMarker] ++
        terminalDebtPairs marker debt ++ suffix) := by
  induction debt generalizing stem suffix with
  | nil =>
      simpa [terminalDebtPairs, List.replicate_succ,
        List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis)
          (stem ++ [marker] ++ middle ++
            [squareMarker, squareMarker] ++ suffix))
  | cons debtLetter rest induction =>
      have headSeen : debtLetter ∈ stem :=
        debtSeen debtLetter (by simp)
      have moveHead :
          HullListDerives
            (stem ++ [marker] ++ (debtLetter :: rest) ++ middle ++
              [squareMarker, squareMarker] ++ suffix)
            (stem ++ [marker, marker] ++ rest ++ middle ++
              [squareMarker, squareMarker, marker, debtLetter] ++
              suffix) := by
        simpa [List.append_assoc] using
          hullListDerivesBalanceAcrossTerminalSquare
            stem (rest ++ middle) suffix
            marker debtLetter squareMarker headSeen
      have restSeen :
          forall letter, letter ∈ rest ->
            letter ∈ stem ++ [marker] := by
        intro letter member
        exact List.mem_append.mpr <|
          Or.inl <| debtSeen letter (List.Mem.tail debtLetter member)
      have moveRest :=
        induction
          (stem := stem ++ [marker])
          (suffix := [marker, debtLetter] ++ suffix)
          restSeen
      have combined := moveHead.trans <| by
        simpa [List.append_assoc] using moveRest
      simpa [terminalDebtPairs, List.replicate_succ,
        List.append_assoc, Nat.add_assoc] using combined

/-- Move a nonempty witnessed debt block behind an explicit terminal
square, choosing any terminal order that is an exact permutation of the
marker/debt pairs produced by the Balance induction.  The permutation
hypothesis is the precise multiplicity (hence parity) accounting: no letter
is inserted or discarded in the terminal debt. -/
theorem hullListDerivesMoveWitnessedDebtBlock
    (stem middle suffix debt terminalDebt : List Nat)
    (marker squareMarker : Nat)
    (debtNonempty : debt ≠ [])
    (debtSeen :
      forall letter, letter ∈ debt -> letter ∈ stem)
    (terminalAccounting :
      (terminalDebtPairs marker debt).Perm terminalDebt) :
    HullListDerives
      (stem ++ [marker] ++ debt ++ middle ++
        [squareMarker, squareMarker] ++ suffix)
      (stem ++ List.replicate (debt.length + 1) marker ++ middle ++
        [squareMarker, squareMarker] ++ terminalDebt ++ suffix) := by
  have swept :=
    hullListDerivesMoveWitnessedDebtBlockRaw
      stem middle suffix debt marker squareMarker debtSeen
  let witnesses :=
    stem ++ List.replicate (debt.length + 1) marker ++ middle ++
      [squareMarker, squareMarker]
  have terminalSeen :
      forall letter,
        letter ∈ terminalDebtPairs marker debt ->
          letter ∈ witnesses := by
    intro letter member
    rw [mem_terminalDebtPairs_iff] at member
    rcases member with ⟨_, rfl⟩ | inDebt
    · simp [witnesses]
    · have inStem := debtSeen letter inDebt
      simp [witnesses, inStem]
  have permuted :=
    hullListDerivesWitnessedTailPermutation
      witnesses suffix terminalSeen terminalAccounting
  simpa [witnesses, List.append_assoc] using swept.trans permuted

/-- Canonical accounting specialization of the block move: the terminal
debt is the block marker repeated once per moved letter, followed by the
original debt block in its original order.  The total contribution is
therefore two copies of `marker` and one copy of the moved debt letter for
each Balance step. -/
theorem hullListDerivesMoveWitnessedDebtBlockCanonical
    (stem middle suffix debt : List Nat)
    (marker squareMarker : Nat)
    (debtNonempty : debt ≠ [])
    (debtSeen :
      forall letter, letter ∈ debt -> letter ∈ stem) :
    HullListDerives
      (stem ++ [marker] ++ debt ++ middle ++
        [squareMarker, squareMarker] ++ suffix)
      (stem ++ List.replicate (debt.length + 1) marker ++ middle ++
        [squareMarker, squareMarker] ++
        List.replicate debt.length marker ++ debt ++ suffix) := by
  simpa [List.append_assoc] using
    hullListDerivesMoveWitnessedDebtBlock
      stem middle suffix debt
      (List.replicate debt.length marker ++ debt)
      marker squareMarker debtNonempty debtSeen
      (terminalDebtPairs_perm_replicate_append marker debt)

end Order6Hull23_1PhaseParityDebtMoves
end CoRoots
end SemigroupBasis
