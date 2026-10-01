import SemigroupBasis.CoRoots.Order6SporadicSection27F9G1Canonical
import SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870

private abbrev F9Table : FiniteTable :=
  SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13559.table

private abbrev F9Separator : BetaSeparator F9Table.semigroup :=
  SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13559.betaSeparator

/-!
## First-occurrence bridge for the direct F9 target

The generated target exposes the paper's left-regular-band embedding through
the older first-occurrence implementation used by `S5_345`.  Gap blocks use
the accumulator implementation from `S5_870`; the following local bridge
keeps this uniqueness layer independent of the larger `S5_870Invariant`
module.
-/

private theorem firstOccurrenceSequenceAux_eq_filter
    (seen : List Nat) :
    ∀ letters : List Nat,
      firstOccurrenceSequenceAux seen letters =
        (SemigroupBasis.Examples.firstOccurrenceSequence letters).filter
          (fun letter => decide (letter ∉ seen))
  | [] => rfl
  | letter :: rest => by
      by_cases member : letter ∈ seen
      · rw [firstOccurrenceSequenceAux]
        simp only [member, if_pos,
          SemigroupBasis.Examples.firstOccurrenceSequence]
        rw [firstOccurrenceSequenceAux_eq_filter seen rest]
        rw [List.filter_cons]
        simp [member]
        apply List.filter_congr
        intro tested _
        by_cases equal : tested = letter
        · subst tested
          simp [member]
        · simp [equal]
      · rw [firstOccurrenceSequenceAux]
        simp only [member, if_neg,
          SemigroupBasis.Examples.firstOccurrenceSequence]
        rw [firstOccurrenceSequenceAux_eq_filter (letter :: seen) rest]
        rw [List.filter_cons]
        simp [member]
        apply List.filter_congr
        intro tested _
        exact Bool.and_comm _ _

private theorem firstOccurrenceSequenceList_eq_standard
    (letters : List Nat) :
    firstOccurrenceSequenceList letters =
      SemigroupBasis.Examples.firstOccurrenceSequence letters := by
  unfold firstOccurrenceSequenceList
  rw [firstOccurrenceSequenceAux_eq_filter]
  apply List.filter_eq_self.mpr
  intro letter _
  simp

/-- Every identity valid in the direct F9 table preserves the marker list
used by the Section 27 gap-block parser. -/
theorem f9_valid_firstOccurrenceSequenceList_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy F9Table.semigroup) :
    firstOccurrenceSequenceList identity.lhs.toList =
      firstOccurrenceSequenceList identity.rhs.toList := by
  have standard :=
    SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13559.valid_firstOccurrenceSequence_eq
      identity valid
  simpa only [firstOccurrenceSequenceList_eq_standard] using standard

/-!
## Exact F9 transition kernel used by Proposition 27.3

The shared `BetaSeparator` record contains every transition used after the
active state is reached.  The paper also uses `4 * 4 = 4` (one-based
notation) to scan a nonempty prefix whose letters all receive the ordinary
value.  This fact is target-specific and is certified directly from the
pinned F9 table here.
-/

/-- The one additional F9 transition needed before the generic separator
contract becomes applicable. -/
theorem f9_ordinary_ordinary :
    F9Table.semigroup.mul F9Separator.ordinary F9Separator.ordinary =
      F9Separator.ordinary := by
  decide

private theorem foldl_all_ordinary
    (valuation : Nat → Fin 6) :
    ∀ (letters : List Nat),
      (∀ letter, letter ∈ letters →
        valuation letter = F9Separator.ordinary) →
      letters.foldl
          (fun current letter =>
            F9Table.semigroup.mul current (valuation letter))
          F9Separator.ordinary =
        F9Separator.ordinary
  | [], _ => rfl
  | letter :: rest, allOrdinary => by
      have letterOrdinary :
          valuation letter = F9Separator.ordinary :=
        allOrdinary letter (List.Mem.head rest)
      have restOrdinary :
          ∀ tested, tested ∈ rest →
            valuation tested = F9Separator.ordinary := by
        intro tested member
        exact allOrdinary tested (List.Mem.tail letter member)
      simp only [List.foldl_cons, letterOrdinary,
        f9_ordinary_ordinary]
      exact foldl_all_ordinary valuation rest restOrdinary

private theorem foldl_all_bridge_from_active
    (valuation : Nat → Fin 6) :
    ∀ (letters : List Nat),
      (∀ letter, letter ∈ letters →
        valuation letter = F9Separator.bridge) →
      letters.foldl
          (fun current letter =>
            F9Table.semigroup.mul current (valuation letter))
          F9Separator.active =
        F9Separator.active
  | [], _ => rfl
  | letter :: rest, allBridge => by
      have letterBridge : valuation letter = F9Separator.bridge :=
        allBridge letter (List.Mem.head rest)
      have restBridge :
          ∀ tested, tested ∈ rest →
            valuation tested = F9Separator.bridge := by
        intro tested member
        exact allBridge tested (List.Mem.tail letter member)
      simp only [List.foldl_cons, letterBridge,
        F9Separator.active_bridge]
      exact foldl_all_bridge_from_active valuation rest restBridge

/-- The nonempty word `ordinaryPrefix ++ [pivot] ++ bridgeSuffix` used in
Cases 2 and 3 of the published proof. -/
private def paperPrefixWord
    (ordinaryPrefix : List Nat) (pivot : Nat)
    (bridgeSuffix : List Nat) : Word Nat :=
  match ordinaryPrefix with
  | [] => S5_107.listWordOfCons pivot bridgeSuffix
  | head :: tail =>
      S5_107.listWordOfCons head (tail ++ pivot :: bridgeSuffix)

private theorem paperPrefixWord_toList
    (ordinaryPrefix : List Nat) (pivot : Nat)
    (bridgeSuffix : List Nat) :
    (paperPrefixWord ordinaryPrefix pivot bridgeSuffix).toList =
      ordinaryPrefix ++ pivot :: bridgeSuffix := by
  cases ordinaryPrefix <;>
    simp [paperPrefixWord, S5_107.listWordOfCons, Word.toList]

/-- Scanning the paper's three valuation zones reaches the active state.
This is the common calculation behind all nonempty-prefix subcases. -/
theorem f9_eval_paperPrefixWord
    (valuation : Nat → Fin 6)
    (ordinaryPrefix : List Nat) (pivot : Nat)
    (bridgeSuffix : List Nat)
    (ordinaryValues :
      ∀ letter, letter ∈ ordinaryPrefix →
        valuation letter = F9Separator.ordinary)
    (pivotValue : valuation pivot = F9Separator.active)
    (bridgeValues :
      ∀ letter, letter ∈ bridgeSuffix →
        valuation letter = F9Separator.bridge) :
    F9Table.semigroup.eval valuation
        (paperPrefixWord ordinaryPrefix pivot bridgeSuffix) =
      F9Separator.active := by
  cases ordinaryPrefix with
  | nil =>
      change
        bridgeSuffix.foldl
            (fun current letter =>
              F9Table.semigroup.mul current (valuation letter))
            (valuation pivot) =
          F9Separator.active
      rw [pivotValue]
      exact foldl_all_bridge_from_active
        valuation bridgeSuffix bridgeValues
  | cons head tail =>
      have headOrdinary : valuation head = F9Separator.ordinary :=
        ordinaryValues head (List.Mem.head tail)
      have tailOrdinary :
          ∀ letter, letter ∈ tail →
            valuation letter = F9Separator.ordinary := by
        intro letter member
        exact ordinaryValues letter (List.Mem.tail head member)
      change
        (tail ++ pivot :: bridgeSuffix).foldl
            (fun current letter =>
              F9Table.semigroup.mul current (valuation letter))
            (valuation head) =
          F9Separator.active
      rw [headOrdinary, List.foldl_append,
        foldl_all_ordinary valuation tail tailOrdinary]
      simp only [List.foldl_cons, pivotValue,
        F9Separator.ordinary_active]
      exact foldl_all_bridge_from_active
        valuation bridgeSuffix bridgeValues

/-!
## Semantic separator certificates

The paper first appends a common fresh successor when the least differing
block is terminal.  The two structures below record the resulting literal
word decompositions.  They deliberately contain proof fields rather than any
unchecked oracle data.
-/

structure F9EmptySeparationCertificate
    (left right : Word Nat) where
  valuation : Nat → Fin 6
  freshLetter : Nat
  prefixWord : Word Nat
  leftTail : Word Nat
  rightTail : Word Nat
  killed : Nat
  leftExtended_eq :
    left ++ Word.singleton freshLetter =
      (prefixWord ++ Word.singleton killed) ++ leftTail
  rightExtended_eq :
    right ++ Word.singleton freshLetter = prefixWord ++ rightTail
  prefixActive :
    F9Table.semigroup.eval valuation prefixWord = F9Separator.active
  killedValue :
    valuation killed = F9Separator.active ∨
      valuation killed = F9Separator.ordinary
  leftFresh : valuation leftTail.head = F9Separator.fresh
  rightFresh : valuation rightTail.head = F9Separator.fresh

structure F9BridgeSeparationCertificate
    (left right : Word Nat) where
  valuation : Nat → Fin 6
  freshLetter : Nat
  prefixWord : Word Nat
  leftTail : Word Nat
  rightTail : Word Nat
  killed : Nat
  preserved : Nat
  leftExtended_eq :
    left ++ Word.singleton freshLetter =
      (prefixWord ++ Word.singleton killed) ++ leftTail
  rightExtended_eq :
    right ++ Word.singleton freshLetter =
      (prefixWord ++ Word.singleton preserved) ++ rightTail
  prefixActive :
    F9Table.semigroup.eval valuation prefixWord = F9Separator.active
  killedValue :
    valuation killed = F9Separator.active ∨
      valuation killed = F9Separator.ordinary
  preservedValue : valuation preserved = F9Separator.bridge
  leftFresh : valuation leftTail.head = F9Separator.fresh
  rightFresh : valuation rightTail.head = F9Separator.fresh

def F9SeparationCertificate (left right : Word Nat) : Prop :=
  Nonempty (F9EmptySeparationCertificate left right) ∨
    Nonempty (F9BridgeSeparationCertificate left right)

namespace F9EmptySeparationCertificate

theorem evaluations
    {left right : Word Nat}
    (certificate : F9EmptySeparationCertificate left right) :
    F9Table.semigroup.eval certificate.valuation
        (left ++ Word.singleton certificate.freshLetter) =
        F9Separator.hit ∧
      F9Table.semigroup.eval certificate.valuation
        (right ++ Word.singleton certificate.freshLetter) =
        F9Separator.miss := by
  rw [certificate.leftExtended_eq, certificate.rightExtended_eq]
  exact BetaSeparator.eval_kill_vs_empty F9Separator
    certificate.valuation certificate.prefixWord
    certificate.leftTail certificate.rightTail certificate.killed
    certificate.prefixActive certificate.killedValue
    certificate.leftFresh certificate.rightFresh

end F9EmptySeparationCertificate

namespace F9BridgeSeparationCertificate

theorem evaluations
    {left right : Word Nat}
    (certificate : F9BridgeSeparationCertificate left right) :
    F9Table.semigroup.eval certificate.valuation
        (left ++ Word.singleton certificate.freshLetter) =
        F9Separator.hit ∧
      F9Table.semigroup.eval certificate.valuation
        (right ++ Word.singleton certificate.freshLetter) =
        F9Separator.miss := by
  rw [certificate.leftExtended_eq, certificate.rightExtended_eq]
  exact BetaSeparator.eval_kill_vs_bridge F9Separator
    certificate.valuation certificate.prefixWord
    certificate.leftTail certificate.rightTail certificate.killed
    certificate.preserved certificate.prefixActive
    certificate.killedValue certificate.preservedValue
    certificate.leftFresh certificate.rightFresh

end F9BridgeSeparationCertificate

namespace F9SeparationCertificate

/-- Any exact paper-style separator certificate refutes validity in the
direct F9 target. -/
theorem not_satisfiedBy
    {left right : Word Nat}
    (certificate : F9SeparationCertificate left right) :
    ¬ (Identity.mk left right).SatisfiedBy F9Table.semigroup := by
  intro valid
  rcases certificate with ⟨emptyCertificate⟩ | ⟨bridgeCertificate⟩
  · rcases emptyCertificate with ⟨emptyCertificate⟩
    have values := emptyCertificate.evaluations
    have extendedEqual :
        F9Table.semigroup.eval emptyCertificate.valuation
            (left ++ Word.singleton emptyCertificate.freshLetter) =
          F9Table.semigroup.eval emptyCertificate.valuation
            (right ++ Word.singleton emptyCertificate.freshLetter) := by
      rw [Semigroup.eval_append, Semigroup.eval_append,
        valid emptyCertificate.valuation]
    exact F9Separator.hit_ne_miss <|
      values.1.symm.trans (extendedEqual.trans values.2)
  · rcases bridgeCertificate with ⟨bridgeCertificate⟩
    have values := bridgeCertificate.evaluations
    have extendedEqual :
        F9Table.semigroup.eval bridgeCertificate.valuation
            (left ++ Word.singleton bridgeCertificate.freshLetter) =
          F9Table.semigroup.eval bridgeCertificate.valuation
            (right ++ Word.singleton bridgeCertificate.freshLetter) := by
      rw [Semigroup.eval_append, Semigroup.eval_append,
        valid bridgeCertificate.valuation]
    exact F9Separator.hit_ne_miss <|
      values.1.symm.trans (extendedEqual.trans values.2)

end F9SeparationCertificate

/-!
## Canonical uniqueness boundary

`F9SeparatesDistinctBetaCanonicalBlocks` is the precise remaining structural
obligation from the paper: split at the least differing block and construct
one of the two certificates above.  Keeping it explicit prevents a bounded
oracle result or an unchecked choice from being mistaken for unrestricted
semantic uniqueness.
-/

def F9SeparatesDistinctBetaCanonicalBlocks : Prop :=
  ∀ {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
      {leftWord rightWord : Word Nat},
    BetaCanonicalBlocks leftBlocks →
    BetaCanonicalBlocks rightBlocks →
    renderGapBlocks leftBlocks = leftWord.toList →
    renderGapBlocks rightBlocks = rightWord.toList →
    gapBlockMarkers leftBlocks = gapBlockMarkers rightBlocks →
    leftBlocks ≠ rightBlocks →
      F9SeparationCertificate leftWord rightWord ∨
        F9SeparationCertificate rightWord leftWord

/-- Once the literal least-differing-block separator has been extracted,
validity in F9 forces two beta-canonical block lists to coincide. -/
theorem betaCanonicalBlocks_eq_of_f9_valid
    (separates : F9SeparatesDistinctBetaCanonicalBlocks)
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    {leftWord rightWord : Word Nat}
    (leftCanonical : BetaCanonicalBlocks leftBlocks)
    (rightCanonical : BetaCanonicalBlocks rightBlocks)
    (leftRendered : renderGapBlocks leftBlocks = leftWord.toList)
    (rightRendered : renderGapBlocks rightBlocks = rightWord.toList)
    (sameMarkers :
      gapBlockMarkers leftBlocks = gapBlockMarkers rightBlocks)
    (valid :
      (Identity.mk leftWord rightWord).SatisfiedBy F9Table.semigroup) :
    leftBlocks = rightBlocks := by
  apply Classical.byContradiction
  intro different
  rcases separates leftCanonical rightCanonical leftRendered rightRendered
      sameMarkers different with leftSeparates | rightSeparates
  · exact leftSeparates.not_satisfiedBy valid
  · apply rightSeparates.not_satisfiedBy
    intro valuation
    exact (valid valuation).symm

/-- Word-level semantic uniqueness for beta-canonical identities in the
direct F9 target.  This endpoint is independent of normalization existence. -/
theorem betaCanonicalWords_eq_of_f9_valid
    (separates : F9SeparatesDistinctBetaCanonicalBlocks)
    (identity : Identity Nat)
    (leftCanonical : BetaCanonicalList identity.lhs.toList)
    (rightCanonical : BetaCanonicalList identity.rhs.toList)
    (valid : identity.SatisfiedBy F9Table.semigroup) :
    identity.lhs = identity.rhs := by
  have sameFirsts := f9_valid_firstOccurrenceSequenceList_eq identity valid
  have sameMarkers :
      gapBlockMarkers (gapBlocksList identity.lhs.toList) =
        gapBlockMarkers (gapBlocksList identity.rhs.toList) := by
    simpa only [gapBlockMarkers_gapBlocksList] using sameFirsts
  have sameBlocks :=
    betaCanonicalBlocks_eq_of_f9_valid separates
      leftCanonical rightCanonical
      (render_gapBlocksList identity.lhs.toList)
      (render_gapBlocksList identity.rhs.toList)
      sameMarkers valid
  apply Word.toList_injective
  calc
    identity.lhs.toList =
        renderGapBlocks (gapBlocksList identity.lhs.toList) :=
      (render_gapBlocksList identity.lhs.toList).symm
    _ = renderGapBlocks (gapBlocksList identity.rhs.toList) :=
      congrArg renderGapBlocks sameBlocks
    _ = identity.rhs.toList :=
      render_gapBlocksList identity.rhs.toList

end SemigroupBasis.CoRoots.Order6SporadicSection27
