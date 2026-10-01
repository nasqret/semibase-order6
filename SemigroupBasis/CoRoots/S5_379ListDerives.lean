import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_379

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_379

open SemigroupBasis

abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons :=
  S5_107.listWordOfCons

/-! ## Multiplicity-preserving crossing chains -/

/-- The nonempty-left-filler case
`x y z x y = x y y z x`. Every displayed variable has the same
multiplicity on both sides. -/
theorem derivesCrossingWithLeftFiller (x y z : Word Nat) :
    Derives basis
      (((((x ++ y) ++ z) ++ x) ++ y))
      (((((x ++ y) ++ y) ++ z) ++ x)) := by
  have first :=
    Derives.appendRight
      (derivesThirdOccurrenceDeletion x y z).symm y
  have second :=
    derivesCrossingEnvelopeRight x y (z ++ x)
  have third :=
    (derivesRightDuplication x (((y ++ y) ++ z))).symm
  simp only [Word.append_assoc] at first second third ⊢
  exact first.trans (second.trans third)

/-- The fully nonempty crossing case
`x y z x u y = x y y z u x`. -/
theorem derivesCrossingPreservingMultiplicity
    (x y z u : Word Nat) :
    Derives basis
      ((((((x ++ y) ++ z) ++ x) ++ u) ++ y))
      ((((((x ++ y) ++ y) ++ z) ++ u) ++ x)) := by
  have first :=
    Derives.appendRight
      (derivesThirdOccurrenceDeletion x y z).symm (u ++ y)
  have second :=
    derivesCrossingEnvelopeRight x y ((z ++ x) ++ u)
  have third :=
    derivesThirdOccurrenceDeletion x (((y ++ y) ++ z)) u
  simp only [Word.append_assoc] at first second third ⊢
  exact first.trans (second.trans third)

/-- Replay a crossing absorption for all four empty/nonempty filler cases.
The crossing letter is retained twice, unlike the concrete `S4_70`
normalizer. -/
theorem listDerivesCrossingPreservingMultiplicity
    (endpoint crossing : Nat) (middle before : List Nat) :
    ListDerives
      (endpoint :: crossing :: middle ++ endpoint :: before ++ [crossing])
      (endpoint :: crossing :: crossing :: middle ++ before ++ [endpoint]) := by
  cases middle with
  | nil =>
      cases before with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesCrossingFinal
                  (Word.singleton endpoint) (Word.singleton crossing)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesCrossingEnvelopeRight
                  (Word.singleton endpoint) (Word.singleton crossing)
                  (listWordOfCons beforeHead beforeTail)
  | cons middleHead middleTail =>
      cases before with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesCrossingWithLeftFiller
                  (Word.singleton endpoint) (Word.singleton crossing)
                  (listWordOfCons middleHead middleTail)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesCrossingPreservingMultiplicity
                  (Word.singleton endpoint) (Word.singleton crossing)
                  (listWordOfCons middleHead middleTail)
                  (listWordOfCons beforeHead beforeTail)

/-! ## Third-occurrence deletion -/

/-- Delete the middle of three displayed occurrences, including every
empty/nonempty combination of the two intervening gaps. -/
theorem listDerivesDeleteMiddleCore
    (letter : Nat) (left right : List Nat) :
    ListDerives
      ([letter] ++ left ++ [letter] ++ right ++ [letter])
      ([letter] ++ left ++ right ++ [letter]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                (derivesPowerExpansion (Word.singleton letter)).symm
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                (derivesLeftDuplication
                  (Word.singleton letter)
                  (listWordOfCons rightHead rightTail)).symm
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                (derivesRightDuplication
                  (Word.singleton letter)
                  (listWordOfCons leftHead leftTail)).symm
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesThirdOccurrenceDeletion
                  (Word.singleton letter)
                  (listWordOfCons leftHead leftTail)
                  (listWordOfCons rightHead rightTail)

/-- Delete the middle of three displayed occurrences in arbitrary list
context. The historical declaration name is retained for API stability. -/
theorem listDerivesDeleteThirdOccurrence
    (letter : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
        [letter] ++ after)
      (before ++ [letter] ++ firstGap ++ secondGap ++ [letter] ++
        after) := by
  simpa [List.append_assoc] using
    (listDerivesDeleteMiddleCore letter firstGap secondGap).context
      before after

/-- Absorb another endpoint occurrence from the suffix, leaving exactly the
two displayed envelope endpoints. -/
theorem listDerivesEndpointAbsorption
    (endpoint : Nat) (interior before after : List Nat) :
    ListDerives
      (endpoint :: interior ++ endpoint :: before ++ endpoint :: after)
      (endpoint :: (interior ++ before) ++ endpoint :: after) := by
  simpa [List.append_assoc] using
    (listDerivesDeleteMiddleCore endpoint interior before).append after

/-! ## Permuting an envelope interior -/

/-- Swap two nonempty blocks inside matching endpoints. -/
theorem listDerivesInteriorSwap
    (endpoint : Nat) (left right : List Nat)
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ []) :
    ListDerives
      (endpoint :: left ++ right ++ [endpoint])
      (endpoint :: right ++ left ++ [endpoint]) := by
  obtain ⟨leftHead, leftTail, rfl⟩ :=
    List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨rightHead, rightTail, rfl⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  exact S5_107.ListDerives.words <| by
    simpa [listWordOfCons, Word.singleton, Word.append,
      Word.append_assoc, List.append_assoc] using
        derivesClosedInteriorSwap
          (Word.singleton endpoint)
          (listWordOfCons leftHead leftTail)
          (listWordOfCons rightHead rightTail)

/-- Lift an interior derivation past one fixed interior letter. -/
theorem listDerivesInteriorCons
    (endpoint letter : Nat) (suffix : List Nat)
    {left right : List Nat}
    (derivation :
      ListDerives
        (endpoint :: left ++ endpoint :: suffix)
        (endpoint :: right ++ endpoint :: suffix)) :
    ListDerives
      (endpoint :: letter :: left ++ endpoint :: suffix)
      (endpoint :: letter :: right ++ endpoint :: suffix) := by
  have first :
      ListDerives
        (endpoint :: letter :: left ++ endpoint :: suffix)
        (endpoint :: letter :: endpoint :: left ++ endpoint :: suffix) := by
    simpa [List.append_assoc] using
      ((listDerivesDeleteMiddleCore endpoint [letter] left).symm).append suffix
  have second :
      ListDerives
        (endpoint :: letter :: endpoint :: left ++ endpoint :: suffix)
        (endpoint :: letter :: endpoint :: right ++ endpoint :: suffix) := by
    simpa [List.append_assoc] using derivation.prepend [endpoint, letter]
  have third :
      ListDerives
        (endpoint :: letter :: endpoint :: right ++ endpoint :: suffix)
        (endpoint :: letter :: right ++ endpoint :: suffix) := by
    simpa [List.append_assoc] using
      (listDerivesDeleteMiddleCore endpoint [letter] right).append suffix
  exact first.trans (second.trans third)

private theorem listDerivesSwapFirstInterior
    (endpoint first second : Nat) (rest suffix : List Nat) :
    ListDerives
      (endpoint :: first :: second :: rest ++ endpoint :: suffix)
      (endpoint :: second :: first :: rest ++ endpoint :: suffix) := by
  cases rest with
  | nil =>
      have core :=
        listDerivesInteriorSwap endpoint [first] [second] (by simp) (by simp)
      simpa [List.append_assoc] using core.append suffix
  | cons restHead restTail =>
      let restWord := listWordOfCons restHead restTail
      have firstStep :=
        (derivesThirdOccurrenceDeletion
          (Word.singleton endpoint)
          (Word.singleton first ++ Word.singleton second)
          restWord).symm
      have secondStep :=
        Derives.appendRight
          (derivesClosedInteriorSwap
            (Word.singleton endpoint)
            (Word.singleton first) (Word.singleton second))
          (restWord ++ Word.singleton endpoint)
      have thirdStep :=
        derivesThirdOccurrenceDeletion
          (Word.singleton endpoint)
          (Word.singleton second ++ Word.singleton first)
          restWord
      have core :
          ListDerives
            (endpoint :: first :: second :: restHead :: restTail ++ [endpoint])
            (endpoint :: second :: first :: restHead :: restTail ++ [endpoint]) :=
        S5_107.ListDerives.words <| by
          simp only [restWord, listWordOfCons, Word.singleton,
            Word.append, Word.append_assoc, List.append_assoc] at firstStep secondStep thirdStep ⊢
          exact firstStep.trans (secondStep.trans thirdStep)
      simpa [List.append_assoc] using (core.append suffix)

/-- Any permutation of the interior between matching endpoints is directly
derivable from the S5_379 laws. -/
theorem listDerivesInteriorPermutation
    (endpoint : Nat) (suffix : List Nat)
    {left right : List Nat} (permutation : left.Perm right) :
    ListDerives
      (endpoint :: left ++ endpoint :: suffix)
      (endpoint :: right ++ endpoint :: suffix) := by
  induction permutation with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons letter _ induction =>
      exact listDerivesInteriorCons endpoint letter suffix induction
  | swap first second rest =>
      exact listDerivesSwapFirstInterior endpoint second first rest suffix
  | trans _ _ first second =>
      exact first.trans second

/-- Every nonempty list derivation preserves each occurrence count after
capping at two. -/
theorem listDerives_cappedCount_eq
    {left right : List Nat} (derivation : ListDerives left right)
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (tested : Nat) :
    min (left.count tested) 2 = min (right.count tested) 2 := by
  cases derivation with
  | empty =>
      exact False.elim (leftNonempty rfl)
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      have same := derives_sameSignature wordDerivation
      have supportIff :
          0 < (leftHead :: leftTail).count tested ↔
            0 < (rightHead :: rightTail).count tested := by
        simpa [listWordOfCons, Word.toList, List.count_pos_iff,
          List.mem_cons] using same.support tested
      have simpleIff :
          (leftHead :: leftTail).count tested = 1 ↔
            (rightHead :: rightTail).count tested = 1 :=
        same.globallySimple tested
      omega

end SemigroupBasis.CoRoots.S5_379
