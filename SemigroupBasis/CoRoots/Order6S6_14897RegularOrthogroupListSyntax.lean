import SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupSyntax
import SemigroupBasis.CoRoots.S5_107ListDerives

namespace SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup

open SemigroupBasis

private abbrev ListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail

/-- Delete a displayed adjacent pair when the same letter occurs on both
sides. Empty gaps reduce to contraction of `x^3`; two nonempty gaps use the
regular-orthogroup law directly. -/
theorem listDerivesDeletePairBetweenGuards
    (letter : Nat)
    (left right : List Nat) :
    ListDerives
      ([letter] ++ left ++ [letter, letter] ++ right ++ [letter])
      ([letter] ++ left ++ right ++ [letter]) := by
  cases left with
  | nil =>
      have base :
          ListDerives [letter, letter, letter] [letter] :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesPowerContraction (Word.singleton letter))
      cases right with
      | nil =>
          simpa [List.append_assoc] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.context
              [letter] ([] : List Nat) base)
      | cons rightHead rightTail =>
          simpa [List.append_assoc] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.context
              ([] : List Nat)
              (rightHead :: rightTail ++ [letter]) base)
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          have base :
              ListDerives [letter, letter, letter] [letter] :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (derivesPowerContraction (Word.singleton letter))
          simpa [List.append_assoc] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.context
              ([letter] ++ leftHead :: leftTail)
              ([] : List Nat) base)
      | cons rightHead rightTail =>
          have core :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (derivesRegularContraction
                (Word.singleton letter)
                (wordOfCons leftHead leftTail)
                (wordOfCons rightHead rightTail))
          simpa [wordOfCons,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            List.append_assoc] using core

/-- Membership-facing adjacent-pair deletion. The leftContext and suffix provide
the two witnesses required by `listDerivesDeletePairBetweenGuards`. -/
theorem listDerivesDeleteAdjacentPairWithGuards
    (letter : Nat)
    (leftContext suffix : List Nat)
    (leftWitness : letter ∈ leftContext)
    (rightWitness : letter ∈ suffix) :
    ListDerives
      (leftContext ++ [letter, letter] ++ suffix)
      (leftContext ++ suffix) := by
  obtain ⟨leftBefore, leftAfter, leftSplit⟩ :=
    List.mem_iff_append.mp leftWitness
  obtain ⟨rightBefore, rightAfter, rightSplit⟩ :=
    List.mem_iff_append.mp rightWitness
  have core :=
    listDerivesDeletePairBetweenGuards
      letter leftAfter rightBefore
  have contextual :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.context
      leftBefore rightAfter core
  simpa [leftSplit, rightSplit, List.append_assoc] using contextual

end SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup
