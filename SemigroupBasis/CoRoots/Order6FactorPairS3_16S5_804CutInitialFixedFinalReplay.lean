import SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitialEndpointCap
import SemigroupBasis.Examples.ConnectedComponentFourEnvelopeCombinatorics

/-!
# Pending-aware fixed-final replay for the d024 B10 root

The ordinary initial-envelope replay cannot be reused here: deleting the
crossing occurrence would require the false identity `xyxy = xyx`.  This
module instead carries at most one pending final letter.  A law-7 crossing
shift moves the old pending block and the consumed suffix prefix inside the
fixed head envelope, while the crossing itself becomes the new pending final.

Every algebraic leaf below is an explicit derivation from the literal B10
basis.  No predecessor-family derivation theorem is imported or retargeted.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial

open SemigroupBasis
open SemigroupBasis.Examples

private def concreteWord (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

private theorem basisMiddleDuplicationStep :
    Derives B10 middleDuplicationLaw.lhs middleDuplicationLaw.rhs :=
  Derives.fromBasis (e := middleDuplicationLaw) (by simp [B10])

private theorem basisCrossingContractionStep :
    Derives B10 crossingContractionLaw.lhs crossingContractionLaw.rhs :=
  Derives.fromBasis (e := crossingContractionLaw) (by simp [B10])

private theorem basisFinalCrossingShiftStep :
    Derives B10 finalCrossingShiftLaw.lhs finalCrossingShiftLaw.rhs :=
  Derives.fromBasis (e := finalCrossingShiftLaw) (by simp [B10])

private theorem basisNestedDeletionStep :
    Derives B10 nestedDeletionLaw.lhs nestedDeletionLaw.rhs :=
  Derives.fromBasis (e := nestedDeletionLaw) (by simp [B10])

private theorem basisFinalInsertionStep :
    Derives B10 finalInsertionLaw.lhs finalInsertionLaw.rhs :=
  Derives.fromBasis (e := finalInsertionLaw) (by simp [B10])

private theorem basisFinalDuplicationStep :
    Derives B10 finalDuplicationLaw.lhs finalDuplicationLaw.rhs :=
  Derives.fromBasis (e := finalDuplicationLaw) (by simp [B10])

/-- Put one substituted B10 step inside a concrete list context. -/
private theorem derivesConcreteContext
    {source target patternLeft patternRight : Word Nat}
    (patternDerivation : Derives B10 patternLeft patternRight)
    (first second third : Word Nat)
    (pre suffix : List Nat)
    (sourceShape :
      source.toList =
        pre ++
          (patternLeft.bind
            (instantiateThreeWords first second third)).toList ++
          suffix)
    (targetShape :
      target.toList =
        pre ++
          (patternRight.bind
            (instantiateThreeWords first second third)).toList ++
          suffix) :
    Derives B10 source target := by
  have contextual :
      B10ListDerives
        (pre ++
          (patternLeft.bind
            (instantiateThreeWords first second third)).toList ++
          suffix)
        (pre ++
          (patternRight.bind
            (instantiateThreeWords first second third)).toList ++
            suffix) :=
    (S5_107.ListDerives.ofWord
      (Derives.subst patternDerivation
        (instantiateThreeWords first second third))).context pre suffix
  rw [← sourceShape, ← targetShape] at contextual
  cases source with
  | mk sourceHead sourceTail =>
      cases target with
      | mk targetHead targetTail =>
          exact S5_107.ListDerives.toWord contextual

/-! ## Four nontrivial fixed-final crossing leaves -/

private theorem derivesCrossingShiftLeftMiddleEmpty :
    Derives B10
      (concreteWord 0 [1, 0, 2, 1])
      (concreteWord 0 [1, 2, 0, 1]) := by
  exact derivesConcreteContext basisFinalCrossingShiftStep
    (concreteWord 0 []) (concreteWord 1 []) (concreteWord 2 [])
    [] [] (by decide) (by decide)

private theorem derivesCrossingShiftLeftEmpty :
    Derives B10
      (concreteWord 0 [1, 2, 0, 3, 1])
      (concreteWord 0 [1, 2, 3, 0, 1]) := by
  have stepOne :
      Derives B10
        (concreteWord 0 [1, 2, 0, 3, 1])
        (concreteWord 0 [1, 0, 2, 0, 3, 1]) :=
    derivesConcreteContext basisCrossingContractionStep.symm
      (concreteWord 0 []) (concreteWord 1 []) (concreteWord 2 [])
      [] [3, 1] (by decide) (by decide)
  have stepTwo :
      Derives B10
        (concreteWord 0 [1, 0, 2, 0, 3, 1])
        (concreteWord 0 [1, 2, 0, 3, 0, 1]) :=
    derivesConcreteContext basisFinalCrossingShiftStep
      (concreteWord 0 []) (concreteWord 1 [])
      (concreteWord 2 [0, 3]) [] [] (by decide) (by decide)
  have stepThree :
      Derives B10
        (concreteWord 0 [1, 2, 0, 3, 0, 1])
        (concreteWord 0 [1, 2, 3, 0, 1]) :=
    derivesConcreteContext basisCrossingContractionStep
      (concreteWord 0 []) (concreteWord 1 [2]) (concreteWord 3 [])
      [] [1] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans stepThree

private theorem derivesCrossingShiftMiddleEmpty :
    Derives B10
      (concreteWord 0 [1, 2, 0, 3, 2])
      (concreteWord 0 [1, 2, 3, 0, 2]) := by
  have stepOne :
      Derives B10
        (concreteWord 0 [1, 2, 0, 3, 2])
        (concreteWord 0 [1, 2, 0, 3, 0, 2]) :=
    derivesConcreteContext basisFinalInsertionStep
      (concreteWord 2 []) (concreteWord 0 []) (concreteWord 3 [])
      [0, 1] [] (by decide) (by decide)
  have stepTwo :
      Derives B10
        (concreteWord 0 [1, 2, 0, 3, 0, 2])
        (concreteWord 0 [1, 2, 3, 0, 2]) :=
    derivesConcreteContext basisCrossingContractionStep
      (concreteWord 0 []) (concreteWord 1 [2]) (concreteWord 3 [])
      [] [2] (by decide) (by decide)
  exact stepOne.trans stepTwo

private theorem derivesCrossingShiftAllNonempty :
    Derives B10
      (concreteWord 0 [1, 2, 3, 0, 4, 2])
      (concreteWord 0 [1, 2, 3, 4, 0, 2]) := by
  have stepOne :
      Derives B10
        (concreteWord 0 [1, 2, 3, 0, 4, 2])
        (concreteWord 0 [1, 2, 0, 3, 0, 4, 2]) :=
    derivesConcreteContext basisCrossingContractionStep.symm
      (concreteWord 0 []) (concreteWord 1 [2]) (concreteWord 3 [])
      [] [4, 2] (by decide) (by decide)
  have stepTwo :
      Derives B10
        (concreteWord 0 [1, 2, 0, 3, 0, 4, 2])
        (concreteWord 0 [1, 2, 0, 3, 0, 4, 0, 2]) :=
    derivesConcreteContext basisFinalInsertionStep
      (concreteWord 2 []) (concreteWord 0 [])
      (concreteWord 3 [0, 4]) [0, 1] [] (by decide) (by decide)
  have stepThree :
      Derives B10
        (concreteWord 0 [1, 2, 0, 3, 0, 4, 0, 2])
        (concreteWord 0 [1, 2, 0, 3, 4, 0, 2]) :=
    derivesConcreteContext basisCrossingContractionStep
      (concreteWord 0 []) (concreteWord 1 [2, 0, 3])
      (concreteWord 4 []) [] [2] (by decide) (by decide)
  have stepFour :
      Derives B10
        (concreteWord 0 [1, 2, 0, 3, 4, 0, 2])
        (concreteWord 0 [1, 2, 3, 4, 0, 2]) :=
    derivesConcreteContext basisCrossingContractionStep
      (concreteWord 0 []) (concreteWord 1 [2])
      (concreteWord 3 [4]) [] [2] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans stepFour

/-! ## Eight fixed-envelope nested-deletion leaves -/

private theorem derivesNestedAllEmpty :
    Derives B10
      (concreteWord 0 [1, 1, 0])
      (concreteWord 0 [1, 0]) :=
  derivesConcreteContext basisMiddleDuplicationStep.symm
    (concreteWord 0 []) (concreteWord 1 []) (concreteWord 1 [])
    [] [] (by decide) (by decide)

private theorem derivesNestedLeftMiddleEmpty :
    Derives B10
      (concreteWord 0 [1, 1, 2, 0])
      (concreteWord 0 [1, 2, 0]) :=
  derivesConcreteContext basisNestedDeletionStep
    (concreteWord 0 []) (concreteWord 1 []) (concreteWord 2 [])
    [] [] (by decide) (by decide)

private theorem derivesNestedLeftRightEmpty :
    Derives B10
      (concreteWord 0 [1, 2, 1, 0])
      (concreteWord 0 [1, 2, 0]) :=
  derivesConcreteContext basisFinalInsertionStep.symm
    (concreteWord 0 []) (concreteWord 1 []) (concreteWord 2 [])
    [] [] (by decide) (by decide)

private theorem derivesNestedLeftEmpty :
    Derives B10
      (concreteWord 0 [1, 2, 1, 3, 0])
      (concreteWord 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives B10
        (concreteWord 0 [1, 2, 1, 3, 0])
        (concreteWord 0 [1, 2, 1, 0, 3, 0]) :=
    derivesConcreteContext basisCrossingContractionStep.symm
      (concreteWord 0 []) (concreteWord 1 [2, 1])
      (concreteWord 3 []) [] [] (by decide) (by decide)
  have stepTwo :
      Derives B10
        (concreteWord 0 [1, 2, 1, 0, 3, 0])
        (concreteWord 0 [1, 2, 0, 3, 0]) :=
    derivesConcreteContext basisFinalInsertionStep.symm
      (concreteWord 0 []) (concreteWord 1 []) (concreteWord 2 [])
      [] [3, 0] (by decide) (by decide)
  have stepThree :
      Derives B10
        (concreteWord 0 [1, 2, 0, 3, 0])
        (concreteWord 0 [1, 2, 3, 0]) :=
    derivesConcreteContext basisCrossingContractionStep
      (concreteWord 0 []) (concreteWord 1 [2]) (concreteWord 3 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans stepThree

private theorem derivesNestedMiddleRightEmpty :
    Derives B10
      (concreteWord 0 [1, 2, 2, 0])
      (concreteWord 0 [1, 2, 0]) :=
  derivesConcreteContext basisFinalDuplicationStep.symm
    (concreteWord 0 []) (concreteWord 1 []) (concreteWord 2 [])
    [] [] (by decide) (by decide)

private theorem derivesNestedMiddleEmpty :
    Derives B10
      (concreteWord 0 [1, 2, 2, 3, 0])
      (concreteWord 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives B10
        (concreteWord 0 [1, 2, 2, 3, 0])
        (concreteWord 0 [1, 0, 2, 2, 3, 0]) :=
    derivesConcreteContext basisCrossingContractionStep.symm
      (concreteWord 0 []) (concreteWord 1 [])
      (concreteWord 2 [2, 3]) [] [] (by decide) (by decide)
  have stepTwo :
      Derives B10
        (concreteWord 0 [1, 0, 2, 2, 3, 0])
        (concreteWord 0 [1, 0, 2, 3, 0]) :=
    derivesConcreteContext basisNestedDeletionStep
      (concreteWord 0 []) (concreteWord 2 []) (concreteWord 3 [])
      [0, 1] [] (by decide) (by decide)
  have stepThree :
      Derives B10
        (concreteWord 0 [1, 0, 2, 3, 0])
        (concreteWord 0 [1, 2, 3, 0]) :=
    derivesConcreteContext basisCrossingContractionStep
      (concreteWord 0 []) (concreteWord 1 [])
      (concreteWord 2 [3]) [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans stepThree

private theorem derivesNestedRightEmpty :
    Derives B10
      (concreteWord 0 [1, 2, 3, 2, 0])
      (concreteWord 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives B10
        (concreteWord 0 [1, 2, 3, 2, 0])
        (concreteWord 0 [1, 2, 3, 2, 1, 2, 3, 0]) :=
    derivesConcreteContext basisFinalInsertionStep
      (concreteWord 0 []) (concreteWord 1 [2, 3])
      (concreteWord 2 []) [] [] (by decide) (by decide)
  have stepTwo :
      Derives B10
        (concreteWord 0 [1, 2, 3, 2, 1, 2, 3, 0])
        (concreteWord 0 [1, 2, 3, 1, 2, 3, 0]) :=
    derivesConcreteContext basisCrossingContractionStep
      (concreteWord 2 []) (concreteWord 3 []) (concreteWord 1 [])
      [0, 1] [3, 0] (by decide) (by decide)
  have stepThree :
      Derives B10
        (concreteWord 0 [1, 2, 3, 1, 2, 3, 0])
        (concreteWord 0 [1, 2, 3, 0]) :=
    derivesConcreteContext basisMiddleDuplicationStep.symm
      (concreteWord 0 []) (concreteWord 1 [2, 3])
      (concreteWord 1 [2, 3]) [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans stepThree

private theorem derivesNestedAllNonempty :
    Derives B10
      (concreteWord 0 [1, 2, 3, 2, 4, 0])
      (concreteWord 0 [1, 2, 3, 4, 0]) := by
  have stepOne :
      Derives B10
        (concreteWord 0 [1, 2, 3, 2, 4, 0])
        (concreteWord 0 [1, 2, 3, 2, 4, 1, 2, 0]) :=
    derivesConcreteContext basisFinalInsertionStep
      (concreteWord 0 []) (concreteWord 1 [2])
      (concreteWord 3 [2, 4]) [] [] (by decide) (by decide)
  have stepTwo :
      Derives B10
        (concreteWord 0 [1, 2, 3, 2, 4, 1, 2, 0])
        (concreteWord 0 [1, 2, 3, 4, 1, 2, 0]) :=
    derivesConcreteContext basisCrossingContractionStep
      (concreteWord 2 []) (concreteWord 3 [])
      (concreteWord 4 [1]) [0, 1] [0] (by decide) (by decide)
  have stepThree :
      Derives B10
        (concreteWord 0 [1, 2, 3, 4, 1, 2, 0])
        (concreteWord 0 [1, 2, 3, 4, 0]) :=
    derivesConcreteContext basisFinalInsertionStep.symm
      (concreteWord 0 []) (concreteWord 1 [2])
      (concreteWord 3 [4]) [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans stepThree

private def substituteTwo (first second : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | n + 2 => Word.singleton (n + 2)

private def substituteThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

private def substituteFour
    (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | n + 4 => Word.singleton (n + 4)

private def substituteFive
    (first second third fourth fifth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | 4 => fifth
  | n + 5 => Word.singleton (n + 5)

/-- Move the suffix prefix before the fixed second endpoint while retaining
the crossing as a one-letter pending final.  An empty right filler is
literally reflexive; the other four branches are the concrete chains above. -/
theorem listDerivesCrossingShift
    (outer crossing : Nat) (left middle right : List Nat) :
    B10ListDerives
      ([outer] ++ left ++ [crossing] ++ middle ++
        [outer] ++ right ++ [crossing])
      ([outer] ++ left ++ [crossing] ++ middle ++
        right ++ [outer, crossing]) := by
  cases right with
  | nil =>
      simpa [List.append_assoc] using
        (S5_107.ListDerives.refl (basis := B10)
          ([outer] ++ left ++ [crossing] ++ middle ++ [outer, crossing]))
  | cons rightHead rightTail =>
      let rightWord := S5_107.listWordOfCons rightHead rightTail
      cases left with
      | nil =>
          cases middle with
          | nil =>
              have substituted :=
                Derives.subst derivesCrossingShiftLeftMiddleEmpty
                  (substituteThree
                    (Word.singleton outer)
                    (Word.singleton crossing) rightWord)
              simpa [concreteWord, rightWord, S5_107.listWordOfCons,
                substituteThree, Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
          | cons middleHead middleTail =>
              let middleWord :=
                S5_107.listWordOfCons middleHead middleTail
              have substituted :=
                Derives.subst derivesCrossingShiftLeftEmpty
                  (substituteFour
                    (Word.singleton outer)
                    (Word.singleton crossing) middleWord rightWord)
              simpa [concreteWord, middleWord, rightWord,
                S5_107.listWordOfCons, substituteFour,
                Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
      | cons leftHead leftTail =>
          let leftWord := S5_107.listWordOfCons leftHead leftTail
          cases middle with
          | nil =>
              have substituted :=
                Derives.subst derivesCrossingShiftMiddleEmpty
                  (substituteFour
                    (Word.singleton outer) leftWord
                    (Word.singleton crossing) rightWord)
              simpa [concreteWord, leftWord, rightWord,
                S5_107.listWordOfCons, substituteFour,
                Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
          | cons middleHead middleTail =>
              let middleWord :=
                S5_107.listWordOfCons middleHead middleTail
              have substituted :=
                Derives.subst derivesCrossingShiftAllNonempty
                  (substituteFive
                    (Word.singleton outer) leftWord
                    (Word.singleton crossing) middleWord rightWord)
              simpa [concreteWord, leftWord, middleWord, rightWord,
                S5_107.listWordOfCons, substituteFive,
                Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted


/-! ## Pending-aware envelope states and plans -/

/-- Render a fixed head, retained interior, second head, at most one pending
final letter, and the unprocessed suffix. -/
def fixedFinalEnvelopeRender
    (endpoint : Nat) (interior pending suffix : List Nat) : List Nat :=
  [endpoint] ++ interior ++ [endpoint] ++ pending ++ suffix

/-- The corrected fixed-final replay state.  Every pending letter already
occurs in the retained interior, so it may safely cross the next endpoint
without changing support or first-occurrence order. -/
structure FixedFinalEnvelopeState
    (endpoint : Nat) (interior pending suffix : List Nat) : Prop where
  linked :
    ConnectedComponentSuffixLinked
      ([endpoint] ++ interior ++ [endpoint] ++ pending) suffix
  endpointNotInterior : endpoint ∉ interior
  endpointNotPending : endpoint ∉ pending
  endpointNotSuffix : endpoint ∉ suffix
  pendingShape : pending = [] ∨ ∃ letter, pending = [letter]
  pendingSupport : ∀ letter ∈ pending, letter ∈ interior
  twoLimited :
    UniqueSeparatorTwoLimited
      (fixedFinalEnvelopeRender endpoint interior pending suffix)

private theorem fixedFinalAdvance_prefix_mem
    {endpoint crossing value : Nat}
    {interior pending before left : List Nat}
    (crossingInInterior : crossing ∈ interior)
    (member :
      value ∈
        ([endpoint] ++ interior ++ [endpoint] ++ pending) ++
          before ++ crossing :: left) :
    value ∈
      ([endpoint] ++ (interior ++ pending ++ before) ++
          [endpoint] ++ [crossing]) ++ left := by
  simpa [List.mem_append, crossingInInterior,
    or_assoc, or_left_comm, or_comm] using member

/-- One pending-aware advance only reorders the displayed letters. -/
private theorem fixedFinalAdvance_count
    (endpoint crossing tested : Nat)
    (interior pending before after : List Nat) :
    (fixedFinalEnvelopeRender endpoint
        (interior ++ pending ++ before) [crossing] after).count tested =
      (fixedFinalEnvelopeRender endpoint interior pending
        (before ++ crossing :: after)).count tested := by
  simp [fixedFinalEnvelopeRender, List.count_append, List.count_cons,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

namespace FixedFinalEnvelopeState

/-- A nonempty linked suffix contains a crossing already represented in the
interior.  It cannot be the endpoint, and a crossing found in the pending
slot is in the interior by `pendingSupport`. -/
theorem exists_crossing
    {endpoint : Nat} {interior pending suffix : List Nat}
    (state : FixedFinalEnvelopeState endpoint interior pending suffix)
    (suffixNonempty : suffix ≠ []) :
    ∃ crossing, crossing ∈ interior ∧ crossing ∈ suffix := by
  have intersect := state.linked [] suffix (by simp) suffixNonempty
  rcases intersect with ⟨crossing, prefixMember, suffixMember⟩
  have prefixMember' :
      crossing ∈ [endpoint] ++ interior ++ [endpoint] ++ pending := by
    simpa using prefixMember
  have alternatives :
      crossing = endpoint ∨
        crossing ∈ interior ∨ crossing ∈ pending := by
    simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using
      prefixMember'
  rcases alternatives with endpointEq | interiorOrPending
  · subst crossing
    exact False.elim (state.endpointNotSuffix suffixMember)
  · rcases interiorOrPending with interiorMember | pendingMember
    · exact ⟨crossing, interiorMember, suffixMember⟩
    · exact
        ⟨crossing, state.pendingSupport crossing pendingMember,
          suffixMember⟩

/-- One pending-aware crossing shift preserves every state invariant. -/
theorem advance
    {endpoint crossing : Nat}
    {interior pending suffix before after : List Nat}
    (state : FixedFinalEnvelopeState endpoint interior pending suffix)
    (crossingInInterior : crossing ∈ interior)
    (suffixShape : suffix = before ++ crossing :: after) :
    FixedFinalEnvelopeState endpoint
      (interior ++ pending ++ before) [crossing] after := by
  have crossingNeEndpoint : crossing ≠ endpoint := by
    intro equal
    subst crossing
    apply state.endpointNotSuffix
    rw [suffixShape]
    simp
  refine
    { linked := ?_
      endpointNotInterior := ?_
      endpointNotPending := ?_
      endpointNotSuffix := ?_
      pendingShape := Or.inr ⟨crossing, rfl⟩
      pendingSupport := ?_
      twoLimited := ?_ }
  · intro left right afterShape rightNonempty
    have oldSuffixShape :
        suffix = (before ++ crossing :: left) ++ right := by
      rw [suffixShape, afterShape]
      simp [List.append_assoc]
    have oldIntersect :=
      state.linked (before ++ crossing :: left) right
        oldSuffixShape rightNonempty
    rcases oldIntersect with ⟨value, oldPrefixMember, rightMember⟩
    exact
      ⟨value,
        fixedFinalAdvance_prefix_mem crossingInInterior
          (by simpa [List.append_assoc] using oldPrefixMember),
        rightMember⟩
  · intro endpointMember
    simp only [List.mem_append] at endpointMember
    rcases endpointMember with
      (interiorMember | pendingMember) | beforeMember
    · exact state.endpointNotInterior interiorMember
    · exact state.endpointNotPending pendingMember
    · apply state.endpointNotSuffix
      rw [suffixShape]
      exact List.mem_append_left _ beforeMember
  · intro endpointMember
    have endpointEqCrossing : endpoint = crossing := by
      simpa using endpointMember
    exact crossingNeEndpoint endpointEqCrossing.symm
  · intro endpointMember
    apply state.endpointNotSuffix
    rw [suffixShape]
    exact List.mem_append_right before <|
      List.Mem.tail crossing endpointMember
  · intro letter member
    have equal : letter = crossing := by simpa using member
    subst letter
    simp [crossingInInterior]
  · intro tested
    have bound := state.twoLimited tested
    rw [suffixShape] at bound
    rw [fixedFinalAdvance_count]
    exact bound

end FixedFinalEnvelopeState

/-- A finite plan that consumes the suffix while retaining its current final
crossing in a one-letter pending slot. -/
inductive FixedFinalEnvelopePlan
    (endpoint : Nat) :
    List Nat → List Nat → List Nat → List Nat → List Nat → Prop
  | done (interior pending : List Nat) :
      FixedFinalEnvelopePlan endpoint
        interior pending [] interior pending
  | advance
      {interior pending suffix before after
        finalInterior finalPending : List Nat}
      {crossing : Nat} :
      crossing ∈ interior →
      suffix = before ++ crossing :: after →
      FixedFinalEnvelopePlan endpoint
        (interior ++ pending ++ before) [crossing] after
        finalInterior finalPending →
      FixedFinalEnvelopePlan endpoint
        interior pending suffix finalInterior finalPending

namespace FixedFinalEnvelopePlan

/-- Replay a pending-aware plan with the explicit four-branch crossing
matrix. -/
theorem replay
    {endpoint : Nat}
    {interior pending suffix finalInterior finalPending : List Nat}
    (plan :
      FixedFinalEnvelopePlan endpoint interior pending suffix
        finalInterior finalPending) :
    B10ListDerives
      (fixedFinalEnvelopeRender endpoint interior pending suffix)
      (fixedFinalEnvelopeRender endpoint
        finalInterior finalPending []) := by
  induction plan with
  | done current currentPending =>
      exact S5_107.ListDerives.refl _
  | @advance interior pending suffix before after
      finalInterior finalPending crossing
      crossingInInterior suffixShape _ induction =>
      obtain ⟨left, middle, interiorShape⟩ :=
        List.append_of_mem crossingInInterior
      subst suffix
      have shifted :=
        (listDerivesCrossingShift endpoint crossing
          left middle (pending ++ before)).append after
      have first :
          B10ListDerives
            (fixedFinalEnvelopeRender endpoint interior pending
              (before ++ crossing :: after))
            (fixedFinalEnvelopeRender endpoint
              (interior ++ pending ++ before) [crossing] after) := by
        simpa [fixedFinalEnvelopeRender, interiorShape,
          List.append_assoc] using shifted
      exact first.trans induction

end FixedFinalEnvelopePlan

namespace FixedFinalEnvelopeState

/-- Every pending-aware state has a terminating plan.  The suffix strictly
shrinks past the selected crossing. -/
theorem exists_plan
    {endpoint : Nat} :
    ∀ (interior pending suffix : List Nat),
      FixedFinalEnvelopeState endpoint interior pending suffix →
        ∃ finalInterior finalPending,
          FixedFinalEnvelopePlan endpoint interior pending suffix
              finalInterior finalPending ∧
            FixedFinalEnvelopeState endpoint
              finalInterior finalPending [] := by
  intro interior pending suffix state
  by_cases suffixEmpty : suffix = []
  · subst suffix
    exact ⟨interior, pending, .done interior pending, state⟩
  · obtain ⟨crossing, crossingInInterior, crossingInSuffix⟩ :=
      state.exists_crossing suffixEmpty
    obtain ⟨before, after, suffixShape⟩ :=
      List.append_of_mem crossingInSuffix
    have nextState := state.advance crossingInInterior suffixShape
    obtain ⟨finalInterior, finalPending, remaining, finalState⟩ :=
      FixedFinalEnvelopeState.exists_plan
        (interior ++ pending ++ before) [crossing] after nextState
    exact
      ⟨finalInterior, finalPending,
        .advance crossingInInterior suffixShape remaining,
        finalState⟩
termination_by interior pending suffix _state => suffix.length
decreasing_by
  rw [suffixShape]
  simp
  omega

end FixedFinalEnvelopeState

/-- A connected two-limited list of length at least two starts with an empty
pending slot in the corrected replay state. -/
theorem exists_initialFixedFinalEnvelopeState
    {head : Nat} {tail : List Nat}
    (connected : ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length)
    (twoLimited : UniqueSeparatorTwoLimited (head :: tail)) :
    ∃ interior suffix,
      head :: tail =
        fixedFinalEnvelopeRender head interior [] suffix ∧
      FixedFinalEnvelopeState head interior [] suffix := by
  obtain ⟨interior, suffix, shape, linkedState⟩ :=
    connectedComponent_exists_initial_envelope
      connected lengthAtLeastTwo
  have endpointNotInterior : head ∉ interior := by
    intro endpointMember
    have positive : 1 ≤ interior.count head :=
      List.one_le_count_iff.mpr endpointMember
    have bound := twoLimited head
    rw [shape] at bound
    simp only [List.count_cons_self, List.count_append] at bound
    omega
  have endpointNotSuffix : head ∉ suffix := by
    intro endpointMember
    have positive : 1 ≤ suffix.count head :=
      List.one_le_count_iff.mpr endpointMember
    have bound := twoLimited head
    rw [shape] at bound
    simp only [List.count_cons_self, List.count_append] at bound
    omega
  have envelopeShape :
      head :: tail =
        fixedFinalEnvelopeRender head interior [] suffix := by
    simpa [fixedFinalEnvelopeRender, List.append_assoc] using shape
  refine ⟨interior, suffix, envelopeShape, ?_⟩
  · refine
      { linked := ?_
        endpointNotInterior := endpointNotInterior
        endpointNotPending := by simp
        endpointNotSuffix := endpointNotSuffix
        pendingShape := Or.inl rfl
        pendingSupport := by simp
        twoLimited := ?_ }
    · simpa [List.append_assoc] using linkedState.linked
    · rw [← envelopeShape]
      exact twoLimited

/-- Delete a repeated interior occurrence under a fixed outer endpoint.
All eight empty/nonempty filler combinations are explicit B10 chains. -/
theorem listDerivesNestedDeletion
    (outer repeated : Nat) (left middle right : List Nat) :
    B10ListDerives
      ([outer] ++ left ++ [repeated] ++ middle ++
        [repeated] ++ right ++ [outer])
      ([outer] ++ left ++ [repeated] ++ middle ++
        right ++ [outer]) := by
  cases left with
  | nil =>
      cases middle with
      | nil =>
          cases right with
          | nil =>
              have substituted :=
                Derives.subst derivesNestedAllEmpty
                  (substituteTwo
                    (Word.singleton outer)
                    (Word.singleton repeated))
              simpa [concreteWord, substituteTwo, Word.toList_bind,
                Word.singleton, List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted

          | cons rightHead rightTail =>
              let rightWord :=
                S5_107.listWordOfCons rightHead rightTail
              have substituted :=
                Derives.subst derivesNestedLeftMiddleEmpty
                  (substituteThree
                    (Word.singleton outer)
                    (Word.singleton repeated) rightWord)
              simpa [concreteWord, rightWord, S5_107.listWordOfCons,
                substituteThree, Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
      | cons middleHead middleTail =>
          let middleWord :=
            S5_107.listWordOfCons middleHead middleTail
          cases right with
          | nil =>
              have substituted :=
                Derives.subst derivesNestedLeftRightEmpty
                  (substituteThree
                    (Word.singleton outer)
                    (Word.singleton repeated) middleWord)
              simpa [concreteWord, middleWord, S5_107.listWordOfCons,
                substituteThree, Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
          | cons rightHead rightTail =>
              let rightWord :=
                S5_107.listWordOfCons rightHead rightTail
              have substituted :=
                Derives.subst derivesNestedLeftEmpty
                  (substituteFour
                    (Word.singleton outer)
                    (Word.singleton repeated) middleWord rightWord)
              simpa [concreteWord, middleWord, rightWord,
                S5_107.listWordOfCons, substituteFour,
                Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
  | cons leftHead leftTail =>
      let leftWord := S5_107.listWordOfCons leftHead leftTail
      cases middle with
      | nil =>
          cases right with
          | nil =>
              have substituted :=
                Derives.subst derivesNestedMiddleRightEmpty
                  (substituteThree
                    (Word.singleton outer) leftWord
                    (Word.singleton repeated))
              simpa [concreteWord, leftWord, S5_107.listWordOfCons,
                substituteThree, Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
          | cons rightHead rightTail =>
              let rightWord :=
                S5_107.listWordOfCons rightHead rightTail
              have substituted :=
                Derives.subst derivesNestedMiddleEmpty
                  (substituteFour
                    (Word.singleton outer) leftWord
                    (Word.singleton repeated) rightWord)
              simpa [concreteWord, leftWord, rightWord,
                S5_107.listWordOfCons, substituteFour,
                Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
      | cons middleHead middleTail =>
          let middleWord :=
            S5_107.listWordOfCons middleHead middleTail
          cases right with
          | nil =>
              have substituted :=
                Derives.subst derivesNestedRightEmpty
                  (substituteFour
                    (Word.singleton outer) leftWord
                    (Word.singleton repeated) middleWord)
              simpa [concreteWord, leftWord, middleWord,
                S5_107.listWordOfCons, substituteFour,
                Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
          | cons rightHead rightTail =>
              let rightWord :=
                S5_107.listWordOfCons rightHead rightTail
              have substituted :=
                Derives.subst derivesNestedAllNonempty
                  (substituteFive
                    (Word.singleton outer) leftWord
                    (Word.singleton repeated) middleWord rightWord)
              simpa [concreteWord, leftWord, middleWord, rightWord,
                S5_107.listWordOfCons, substituteFive,
                Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted

/-! ## Fixed-final interior deduplication -/

/-- Scan the envelope interior left to right.  When the current letter has
already been retained, the eight-branch nested-deletion matrix removes only
that later occurrence and leaves the pending final untouched. -/
private theorem exists_nodupFixedFinalInterior
    (endpoint : Nat) (pending : List Nat) :
    ∀ (retained remaining : List Nat),
      retained.Nodup →
      endpoint ∉ retained →
      endpoint ∉ remaining →
      ∃ finalInterior,
        B10ListDerives
            (fixedFinalEnvelopeRender endpoint
              (retained ++ remaining) pending [])
            (fixedFinalEnvelopeRender endpoint
              finalInterior pending []) ∧
          finalInterior.Nodup ∧
          endpoint ∉ finalInterior ∧
          (∀ tested,
            tested ∈ finalInterior ↔
              tested ∈ retained ∨ tested ∈ remaining)
  | retained, [], retainedNodup, endpointNotRetained, _ =>
      ⟨retained, by
        simpa using
          (S5_107.ListDerives.refl (basis := B10)
            (fixedFinalEnvelopeRender endpoint retained pending [])),
        retainedNodup, endpointNotRetained, by simp⟩
  | retained, current :: rest, retainedNodup,
      endpointNotRetained, endpointNotRemaining => by
      have currentNeEndpoint : current ≠ endpoint := by
        intro equal
        subst current
        exact endpointNotRemaining (List.Mem.head rest)
      have endpointNotRest : endpoint ∉ rest := by
        intro member
        exact endpointNotRemaining (List.Mem.tail current member)
      by_cases currentSeen : current ∈ retained
      · obtain ⟨left, middle, retainedShape⟩ :=
          List.append_of_mem currentSeen
        have deleteCurrent :
            B10ListDerives
              (fixedFinalEnvelopeRender endpoint
                (retained ++ current :: rest) pending [])
              (fixedFinalEnvelopeRender endpoint
                (retained ++ rest) pending []) := by
          have deleted :=
            (listDerivesNestedDeletion
              endpoint current left middle rest).append pending
          simpa [fixedFinalEnvelopeRender, retainedShape,
            List.append_assoc] using deleted
        obtain
          ⟨finalInterior, remainingDerivation,
            finalNodup, endpointAbsent, finalSupport⟩ :=
          exists_nodupFixedFinalInterior endpoint pending
            retained rest retainedNodup endpointNotRetained endpointNotRest
        refine
          ⟨finalInterior, deleteCurrent.trans remainingDerivation,
            finalNodup, endpointAbsent, ?_⟩
        intro tested
        rw [finalSupport tested]
        constructor
        · rintro (retainedMember | restMember)
          · exact Or.inl retainedMember
          · exact Or.inr (List.Mem.tail current restMember)
        · rintro (retainedMember | remainingMember)
          · exact Or.inl retainedMember
          · rcases List.mem_cons.mp remainingMember with equal | restMember
            · subst tested
              exact Or.inl currentSeen
            · exact Or.inr restMember
      · have nextNodup : (retained ++ [current]).Nodup := by
          apply List.nodup_append.mpr
          refine ⟨retainedNodup, by simp, ?_⟩
          intro left leftMember right rightMember equal
          have rightEq : right = current := by simpa using rightMember
          subst right
          subst left
          exact currentSeen leftMember
        have endpointNotNext : endpoint ∉ retained ++ [current] := by
          simp [endpointNotRetained, Ne.symm currentNeEndpoint]
        obtain
          ⟨finalInterior, remainingDerivation,
            finalNodup, endpointAbsent, finalSupport⟩ :=
          exists_nodupFixedFinalInterior endpoint pending
            (retained ++ [current]) rest nextNodup
            endpointNotNext endpointNotRest
        refine
          ⟨finalInterior, ?_, finalNodup, endpointAbsent, ?_⟩
        · simpa [fixedFinalEnvelopeRender,
            List.append_assoc] using remainingDerivation
        · intro tested
          simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using
            finalSupport tested
termination_by retained remaining _ _ _ => remaining.length

/-- Delete all repeated interior occurrences while preserving the pending
final slot and exact interior support. -/
theorem listDerivesNodupFixedFinalInterior
    (endpoint : Nat) (interior pending : List Nat)
    (endpointNotInterior : endpoint ∉ interior)
    (pendingSupport : ∀ letter ∈ pending, letter ∈ interior) :
    ∃ finalInterior,
      B10ListDerives
          (fixedFinalEnvelopeRender endpoint interior pending [])
          (fixedFinalEnvelopeRender endpoint finalInterior pending []) ∧
        finalInterior.Nodup ∧
        endpoint ∉ finalInterior ∧
        (∀ letter ∈ pending, letter ∈ finalInterior) ∧
        (∀ tested, tested ∈ finalInterior ↔ tested ∈ interior) := by
  obtain
    ⟨finalInterior, derivation, finalNodup,
      endpointAbsent, finalSupport⟩ :=
    exists_nodupFixedFinalInterior endpoint pending
      [] interior (by simp) (by simp) endpointNotInterior
  refine
    ⟨finalInterior, by
        simpa [fixedFinalEnvelopeRender] using derivation,
      finalNodup, endpointAbsent, ?_, ?_⟩
  · intro letter pendingMember
    exact (finalSupport letter).2 <|
      Or.inr (pendingSupport letter pendingMember)
  · intro tested
    simpa using finalSupport tested

/-! ## Pure terminal-envelope facts -/

private theorem firstOccurrenceSequence_append_singleton
    (selected : Nat) :
    ∀ letters : List Nat,
      firstOccurrenceSequence (letters ++ [selected]) =
        if selected ∈ letters then
          firstOccurrenceSequence letters
        else
          firstOccurrenceSequence letters ++ [selected]
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      have induction :=
        firstOccurrenceSequence_append_singleton selected rest
      by_cases equal : letter = selected
      · subst letter
        by_cases member : selected ∈ rest <;>
          simp [firstOccurrenceSequence, induction, member,
            List.filter_append]
      · have reverseEqual : selected ≠ letter := Ne.symm equal
        by_cases member : selected ∈ rest <;>
          simp [firstOccurrenceSequence, induction, equal, reverseEqual,
            member, List.filter_append]

/-- Appending only letters already represented on the left does not change
the first-occurrence sequence. -/
private theorem firstOccurrenceSequence_append_of_subset :
    ∀ (right left : List Nat),
      (∀ letter, letter ∈ right → letter ∈ left) →
      firstOccurrenceSequence (left ++ right) =
        firstOccurrenceSequence left
  | [], left, _ => by simp
  | letter :: rest, left, subset => by
      have letterMember : letter ∈ left :=
        subset letter (List.Mem.head rest)
      have restSubset :
          ∀ tested, tested ∈ rest → tested ∈ left ++ [letter] := by
        intro tested member
        exact List.mem_append_left [letter] <|
          subset tested (List.Mem.tail letter member)
      calc
        firstOccurrenceSequence (left ++ letter :: rest) =
            firstOccurrenceSequence ((left ++ [letter]) ++ rest) := by
          simp [List.append_assoc]
        _ = firstOccurrenceSequence (left ++ [letter]) :=
          firstOccurrenceSequence_append_of_subset rest
            (left ++ [letter]) restSubset
        _ = firstOccurrenceSequence left := by
          rw [firstOccurrenceSequence_append_singleton,
            if_pos letterMember]

private theorem firstOccurrenceSequence_fixedFinalEnvelope
    (endpoint : Nat) (interior pending : List Nat)
    (interiorNodup : interior.Nodup)
    (endpointNotInterior : endpoint ∉ interior)
    (pendingSupport : ∀ letter ∈ pending, letter ∈ interior) :
    firstOccurrenceSequence
        (fixedFinalEnvelopeRender endpoint interior pending []) =
      endpoint :: interior := by
  have headInteriorNodup : (endpoint :: interior).Nodup :=
    List.nodup_cons.mpr ⟨endpointNotInterior, interiorNodup⟩
  have appendedSubset :
      ∀ letter, letter ∈ endpoint :: pending →
        letter ∈ endpoint :: interior := by
    intro letter member
    rcases List.mem_cons.mp member with equal | pendingMember
    · subst letter
      simp
    · exact List.Mem.tail endpoint <|
        pendingSupport letter pendingMember
  calc
    firstOccurrenceSequence
        (fixedFinalEnvelopeRender endpoint interior pending []) =
        firstOccurrenceSequence
          ((endpoint :: interior) ++ (endpoint :: pending)) := by
      simp [fixedFinalEnvelopeRender, List.append_assoc]
    _ = firstOccurrenceSequence (endpoint :: interior) :=
      firstOccurrenceSequence_append_of_subset
        (endpoint :: pending) (endpoint :: interior) appendedSubset
    _ = endpoint :: interior :=
      firstOccurrenceSequence_eq_self_of_nodup headInteriorNodup

private theorem getLastD_append
    (left right : List Nat) (fallback : Nat) :
    (left ++ right).getLastD fallback =
      right.getLastD (left.getLastD fallback) := by
  induction left generalizing fallback with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.cons_append, List.getLastD_cons]
      exact induction head

private theorem componentFinal_append_singleton
    (letters : List Nat) (letter : Nat) :
    S5_804.componentFinal (letters ++ [letter]) = letter := by
  cases letters with
  | nil => rfl
  | cons head tail =>
      simp only [List.cons_append, S5_804.componentFinal]
      rw [getLastD_append]
      rfl

private theorem componentFinal_fixedFinalEnvelope_nil
    (endpoint : Nat) (interior : List Nat) :
    S5_804.componentFinal
        (fixedFinalEnvelopeRender endpoint interior [] []) = endpoint := by
  simpa [fixedFinalEnvelopeRender, List.append_assoc] using
    componentFinal_append_singleton
      (([endpoint] ++ interior)) endpoint

private theorem componentFinal_fixedFinalEnvelope_singleton
    (endpoint final : Nat) (interior : List Nat) :
    S5_804.componentFinal
        (fixedFinalEnvelopeRender endpoint interior [final] []) = final := by
  simpa [fixedFinalEnvelopeRender, List.append_assoc] using
    componentFinal_append_singleton
      ([endpoint] ++ interior ++ [endpoint]) final

/-! ## Recovering a whole-component signature from a B10 list derivation -/

private theorem connectedComponentDecomposeList_eq_singleton
    {letters : List Nat}
    (nonempty : letters ≠ [])
    (connected : ConnectedComponentSupportConnected letters) :
    connectedComponentDecomposeList letters = [letters] := by
  have decompositionNonempty :=
    connectedComponentDecomposeList_nonempty nonempty
  obtain ⟨first, rest, decompositionShape⟩ :=
    List.exists_cons_of_ne_nil decompositionNonempty
  cases rest with
  | nil =>
      have flattened := connectedComponentDecomposeList_flatten letters
      rw [decompositionShape] at flattened
      have firstEq : first = letters := by simpa using flattened
      simpa [firstEq] using decompositionShape
  | cons second remaining =>
      have firstNonempty : first ≠ [] :=
        connectedComponentDecomposeList_nonempty_components letters
          first (by rw [decompositionShape]; simp)
      have suffixNonempty : (second :: remaining).flatten ≠ [] := by
        have secondNonempty : second ≠ [] :=
          connectedComponentDecomposeList_nonempty_components letters
            second (by rw [decompositionShape]; simp)
        intro flattenedEmpty
        have appendedEmpty : second ++ remaining.flatten = [] := by
          simpa using flattenedEmpty
        exact secondNonempty
          (List.append_eq_nil_iff.mp appendedEmpty).1
      have pairwise :=
        connectedComponentDecomposeList_pairwiseDisjoint letters
      rw [decompositionShape] at pairwise
      have firstToSuffix := (List.pairwise_cons.mp pairwise).1
      have disjoint :
          ConnectedComponentSupportsDisjoint
            first (second :: remaining).flatten := by
        intro letter firstMember suffixMember
        rw [List.mem_flatten] at suffixMember
        rcases suffixMember with
          ⟨candidate, candidateMember, letterMember⟩
        exact
          (firstToSuffix candidate candidateMember
            letter firstMember) letterMember
      have flattened := connectedComponentDecomposeList_flatten letters
      rw [decompositionShape] at flattened
      have sourceShape :
          letters = first ++ (second :: remaining).flatten := by
        simpa using flattened.symm
      obtain ⟨letter, firstMember, suffixMember⟩ :=
        connected first (second :: remaining).flatten
          sourceShape firstNonempty suffixNonempty
      exact False.elim <|
        disjoint letter firstMember suffixMember

private theorem connectedCutComponentSignature_eq_of_listDerives
    {sourceHead targetHead : Nat}
    {sourceTail targetTail : List Nat}
    (sourceConnected :
      ConnectedComponentSupportConnected (sourceHead :: sourceTail))
    (derivation :
      B10ListDerives
        (sourceHead :: sourceTail) (targetHead :: targetTail)) :
    S5_804.connectedCutComponentSignatureOfList
        (sourceHead :: sourceTail) =
      S5_804.connectedCutComponentSignatureOfList
        (targetHead :: targetTail) := by
  have sourceDecomposition :=
    connectedComponentDecomposeList_eq_singleton
      (by simp) sourceConnected
  have sourceSignatures :
      S5_804.connectedCutSignaturesList (sourceHead :: sourceTail) =
        [S5_804.connectedCutComponentSignatureOfList
          (sourceHead :: sourceTail)] := by
    simp [S5_804.connectedCutSignaturesList, sourceDecomposition]
  have wordDerivation := S5_107.ListDerives.toWord derivation
  have signaturesEqual :
      S5_804.connectedCutSignaturesList (sourceHead :: sourceTail) =
        S5_804.connectedCutSignaturesList (targetHead :: targetTail) := by
    simpa [S5_107.listWordOfCons, Word.toList,
      S5_804.SameConnectedCutSignature,
      S5_804.connectedCutSignaturesWord] using
        (derives_sameCutInitialSignature wordDerivation).cuts
  have targetSignatures :
      S5_804.connectedCutSignaturesList (targetHead :: targetTail) =
        [S5_804.connectedCutComponentSignatureOfList
          (sourceHead :: sourceTail)] := by
    rw [← signaturesEqual, sourceSignatures]
  have targetDecompositionLength :
      (connectedComponentDecomposeList
        (targetHead :: targetTail)).length = 1 := by
    have lengths := congrArg List.length targetSignatures
    simpa [S5_804.connectedCutSignaturesList] using lengths
  obtain ⟨only, targetDecomposition⟩ :=
    List.length_eq_one_iff.mp targetDecompositionLength
  have flattened :=
    connectedComponentDecomposeList_flatten (targetHead :: targetTail)
  rw [targetDecomposition] at flattened
  have onlyEq : only = targetHead :: targetTail := by
    simpa using flattened
  have targetSignaturesSelf :
      S5_804.connectedCutSignaturesList (targetHead :: targetTail) =
        [S5_804.connectedCutComponentSignatureOfList
          (targetHead :: targetTail)] := by
    simp [S5_804.connectedCutSignaturesList,
      targetDecomposition, onlyEq]
  rw [targetSignaturesSelf] at targetSignatures
  simpa using targetSignatures.symm

/-- A deduplicated terminal pending envelope is already the deterministic
final-aware initial-order render of its own component signature. -/
private theorem renderCutInitialComponent_fixedFinalEnvelope
    (endpoint : Nat) (interior pending : List Nat)
    (interiorNodup : interior.Nodup)
    (endpointNotInterior : endpoint ∉ interior)
    (pendingShape : pending = [] ∨ ∃ final, pending = [final])
    (pendingSupport : ∀ letter ∈ pending, letter ∈ interior) :
    renderCutInitialComponent
        (firstOccurrenceSequence
          (fixedFinalEnvelopeRender endpoint interior pending []))
        (S5_804.connectedCutComponentSignatureOfList
          (fixedFinalEnvelopeRender endpoint interior pending [])) =
      fixedFinalEnvelopeRender endpoint interior pending [] := by
  let terminal :=
    fixedFinalEnvelopeRender endpoint interior pending []
  let signature :=
    S5_804.connectedCutComponentSignatureOfList terminal
  have initialSequence :
      firstOccurrenceSequence terminal = endpoint :: interior := by
    simpa [terminal] using
      firstOccurrenceSequence_fixedFinalEnvelope
        endpoint interior pending interiorNodup
          endpointNotInterior pendingSupport
  have baseSupport :
      signature.base.support =
        connectedComponentSortedSupport terminal := by
    simpa [signature, S5_804.connectedCutComponentSignatureOfList] using
      connectedComponentSignatureOfList_support terminal
  have orderEq :
      (firstOccurrenceSequence terminal).filter
          (fun letter => decide (letter ∈ signature.base.support)) =
        endpoint :: interior := by
    calc
      (firstOccurrenceSequence terminal).filter
          (fun letter => decide (letter ∈ signature.base.support)) =
          firstOccurrenceSequence terminal := by
        apply List.filter_eq_self.mpr
        intro letter sequenceMember
        rw [baseSupport]
        exact decide_eq_true <|
          (connectedComponentSortedSupport_mem_iff letter terminal).2 <|
            (mem_firstOccurrenceSequence_iff letter terminal).1
              sequenceMember
      _ = endpoint :: interior := initialSequence
  have supportNonempty :
      connectedComponentSortedSupport terminal ≠ [] :=
    connectedComponentSortedSupport_nonempty <| by
      simp [terminal, fixedFinalEnvelopeRender]
  cases supportShape : connectedComponentSortedSupport terminal with
  | nil =>
      exact False.elim (supportNonempty supportShape)
  | cons first remaining =>
      cases remaining with
      | nil =>
          have endpointInSupport : endpoint ∈ [first] := by
            rw [← supportShape,
              connectedComponentSortedSupport_mem_iff]
            simp [terminal, fixedFinalEnvelopeRender]
          have firstEq : first = endpoint := by
            have endpointEq : endpoint = first := by
              simpa using endpointInSupport
            exact endpointEq.symm
          subst first
          have interiorEmpty : interior = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro letter interiorMember
            have letterInSupport : letter ∈ [endpoint] := by
              rw [← supportShape,
                connectedComponentSortedSupport_mem_iff]
              simp [terminal, fixedFinalEnvelopeRender,
                interiorMember]
            have equal : letter = endpoint := by simpa using letterInSupport
            subst letter
            exact endpointNotInterior interiorMember
          subst interior
          rcases pendingShape with pendingEmpty | ⟨final, pendingSingleton⟩
          · subst pending
            have repeatedTrue : signature.base.repeatedUnary = true := by
              change
                (connectedComponentSignatureOfList terminal).repeatedUnary =
                  true
              unfold connectedComponentSignatureOfList
              rw [supportShape]
              simp [terminal, fixedFinalEnvelopeRender]
            change
              renderCutInitialComponent
                  (firstOccurrenceSequence terminal) signature = terminal
            unfold renderCutInitialComponent
            rw [orderEq, baseSupport, supportShape, repeatedTrue]
            simp [terminal, fixedFinalEnvelopeRender]
          · subst pending
            have finalInEmpty : final ∈ ([] : List Nat) :=
              pendingSupport final (by simp)
            simp at finalInEmpty
      | cons next rest =>
          change
            renderCutInitialComponent
                (firstOccurrenceSequence terminal) signature = terminal
          rcases pendingShape with pendingEmpty | ⟨final, pendingSingleton⟩
          · subst pending
            have finalEq : signature.final = endpoint := by
              simpa [signature, terminal] using
                componentFinal_fixedFinalEnvelope_nil endpoint interior
            unfold renderCutInitialComponent
            rw [orderEq, baseSupport, supportShape, finalEq]
            simp [terminal, fixedFinalEnvelopeRender, List.append_assoc]
          · subst pending
            have finalMember : final ∈ interior :=
              pendingSupport final (by simp)
            have finalNeEndpoint : final ≠ endpoint := by
              intro equal
              subst final
              exact endpointNotInterior finalMember
            have finalEq : signature.final = final := by
              simpa [signature, terminal] using
                componentFinal_fixedFinalEnvelope_singleton
                  endpoint final interior
            unfold renderCutInitialComponent
            rw [orderEq, baseSupport, supportShape, finalEq]
            simp [finalNeEndpoint, terminal, fixedFinalEnvelopeRender,
              List.append_assoc]

/-! ## Decisive connected-component normalizer -/

/-- Every nonempty support-connected two-limited component derives under
literal B10 to the final-aware renderer in its own first-occurrence order. -/
theorem listDerivesConnectedTwoLimitedCutInitial
    (component : List Nat)
    (nonempty : component ≠ [])
    (connected : ConnectedComponentSupportConnected component)
    (twoLimited : UniqueSeparatorTwoLimited component) :
    B10ListDerives component
      (renderCutInitialComponent
        (firstOccurrenceSequence component)
        (S5_804.connectedCutComponentSignatureOfList component)) := by
  cases component with
  | nil =>
      contradiction
  | cons head tail =>
      cases tail with
      | nil =>
          have supportShape :
              connectedComponentSortedSupport [head] = [head] := by
            simp [connectedComponentSortedSupport,
              connectedComponentDistinctSupport]
          simpa [renderCutInitialComponent,
            S5_804.connectedCutComponentSignatureOfList,
            connectedComponentSignatureOfList,
            S5_804.componentFinal, supportShape,
            firstOccurrenceSequence] using
              (S5_107.ListDerives.refl (basis := B10) [head])
      | cons next rest =>
          have lengthAtLeastTwo :
              2 ≤ (head :: next :: rest).length := by simp
          obtain ⟨initialInterior, suffix, sourceShape, initialState⟩ :=
            exists_initialFixedFinalEnvelopeState
              connected lengthAtLeastTwo twoLimited
          obtain
            ⟨finalInterior, finalPending, plan, finalState⟩ :=
            initialState.exists_plan
          have replay :
              B10ListDerives (head :: next :: rest)
                (fixedFinalEnvelopeRender
                  head finalInterior finalPending []) := by
            rw [sourceShape]
            exact plan.replay
          obtain
            ⟨nodupInterior, deduplication, interiorNodup,
              endpointAbsent, pendingSupport, interiorSupport⟩ :=
            listDerivesNodupFixedFinalInterior
              head finalInterior finalPending
                finalState.endpointNotInterior finalState.pendingSupport
          have combined :
              B10ListDerives (head :: next :: rest)
                (fixedFinalEnvelopeRender
                  head nodupInterior finalPending []) :=
            replay.trans deduplication
          have combinedCons :
              B10ListDerives (head :: next :: rest)
                (head :: (nodupInterior ++ head :: finalPending)) := by
            simpa [fixedFinalEnvelopeRender,
              List.append_assoc] using combined
          have signatureEq :
              S5_804.connectedCutComponentSignatureOfList
                  (head :: next :: rest) =
                S5_804.connectedCutComponentSignatureOfList
                  (fixedFinalEnvelopeRender
                    head nodupInterior finalPending []) := by
            simpa [fixedFinalEnvelopeRender,
              List.append_assoc] using
                connectedCutComponentSignature_eq_of_listDerives
                  connected combinedCons
          have wordDerivation := S5_107.ListDerives.toWord combinedCons
          have initialEq :
              firstOccurrenceSequence (head :: next :: rest) =
                firstOccurrenceSequence
                  (fixedFinalEnvelopeRender
                    head nodupInterior finalPending []) := by
            simpa [S5_107.listWordOfCons, Word.toList,
              fixedFinalEnvelopeRender, List.append_assoc] using
                (derives_sameCutInitialSignature wordDerivation).initials
          have targetSelf :
              renderCutInitialComponent
                  (firstOccurrenceSequence
                    (fixedFinalEnvelopeRender
                      head nodupInterior finalPending []))
                  (S5_804.connectedCutComponentSignatureOfList
                    (fixedFinalEnvelopeRender
                      head nodupInterior finalPending [])) =
                fixedFinalEnvelopeRender
                  head nodupInterior finalPending [] :=
            renderCutInitialComponent_fixedFinalEnvelope
              head nodupInterior finalPending interiorNodup
                endpointAbsent finalState.pendingShape pendingSupport
          have normalEq :
              renderCutInitialComponent
                  (firstOccurrenceSequence (head :: next :: rest))
                  (S5_804.connectedCutComponentSignatureOfList
                    (head :: next :: rest)) =
                fixedFinalEnvelopeRender
                  head nodupInterior finalPending [] := by
            rw [initialEq, signatureEq]
            exact targetSelf
          rw [normalEq]
          exact combined

end SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial
