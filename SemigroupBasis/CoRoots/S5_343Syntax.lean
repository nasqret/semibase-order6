import SemigroupBasis.CoRoots.S5_107Syntax
import SemigroupBasis.Examples.LeftRegularBandThree

namespace SemigroupBasis.CoRoots.S5_343Syntax

open SemigroupBasis
open SemigroupBasis.Examples

/-- The exact syntactic invariant of the `S5_343/S5_592` family. -/
structure SameEndpointSequenceSignature
    (left right : Word Nat) : Prop where
  firstOccurrences :
    firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList
  simpleInitial :
    left.toList.count left.head = 1 ↔
      right.toList.count right.head = 1
  simpleFinal :
    left.toList.count left.final = 1 ↔
      right.toList.count right.final = 1

namespace SameEndpointSequenceSignature

theorem refl (word : Word Nat) :
    SameEndpointSequenceSignature word word :=
  ⟨rfl, Iff.rfl, Iff.rfl⟩

theorem symm {left right : Word Nat}
    (same : SameEndpointSequenceSignature left right) :
    SameEndpointSequenceSignature right left :=
  ⟨same.firstOccurrences.symm, same.simpleInitial.symm,
    same.simpleFinal.symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameEndpointSequenceSignature left middle)
    (second : SameEndpointSequenceSignature middle right) :
    SameEndpointSequenceSignature left right :=
  ⟨first.firstOccurrences.trans second.firstOccurrences,
    first.simpleInitial.trans second.simpleInitial,
    first.simpleFinal.trans second.simpleFinal⟩

/-- Equal first-occurrence sequences have the same initial variable. -/
theorem head_eq {left right : Word Nat}
    (same : SameEndpointSequenceSignature left right) :
    left.head = right.head := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          have first := same.firstOccurrences
          simp only [Word.toList, firstOccurrenceSequence,
            List.cons.injEq] at first
          exact first.1

end SameEndpointSequenceSignature

/-- The four deterministic normal forms from the authoritative certificate. -/
def endpointCanonicalList (word : Word Nat) : List Nat :=
  let sequence := firstOccurrenceSequence word.toList
  if word.toList.count word.head = 1 then
    if word.toList.count word.final = 1 then
      sequence
    else
      sequence ++ [sequence.getLastD word.head]
  else
    if word.toList.count word.final = 1 then
      word.head :: sequence
    else
      sequence ++ [word.head]

theorem endpointCanonicalList_ne_nil (word : Word Nat) :
    endpointCanonicalList word ≠ [] := by
  cases word with
  | mk head tail =>
      unfold endpointCanonicalList
      split <;> split <;>
        simp [Word.toList, firstOccurrenceSequence]

private def wordOfListOr
    (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

/-- The nonempty word represented by `endpointCanonicalList`. -/
def endpointCanonicalWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head (endpointCanonicalList word)

@[simp]
theorem toList_endpointCanonicalWord (word : Word Nat) :
    (endpointCanonicalWord word).toList =
      endpointCanonicalList word := by
  unfold endpointCanonicalWord
  cases canonical : endpointCanonicalList word with
  | nil =>
      exact False.elim (endpointCanonicalList_ne_nil word canonical)
  | cons head tail =>
      rfl

namespace SameEndpointSequenceSignature

/-- The four-case canonical list depends only on the exact signature. -/
theorem endpointCanonicalList_eq {left right : Word Nat}
    (same : SameEndpointSequenceSignature left right) :
    endpointCanonicalList left = endpointCanonicalList right := by
  have heads := same.head_eq
  unfold endpointCanonicalList
  rw [same.firstOccurrences]
  by_cases leftInitial :
      left.toList.count left.head = 1
  · have rightInitial :
        right.toList.count right.head = 1 :=
      same.simpleInitial.mp leftInitial
    by_cases leftFinal :
        left.toList.count left.final = 1
    · have rightFinal :
      right.toList.count right.final = 1 :=
        same.simpleFinal.mp leftFinal
      rw [if_pos leftInitial, if_pos rightInitial,
        if_pos leftFinal, if_pos rightFinal]
    · have rightFinal :
          right.toList.count right.final ≠ 1 := by
        intro rightSimple
        exact leftFinal (same.simpleFinal.mpr rightSimple)
      rw [if_pos leftInitial, if_pos rightInitial,
        if_neg leftFinal, if_neg rightFinal, heads]
  · have rightInitial :
        right.toList.count right.head ≠ 1 := by
      intro rightSimple
      exact leftInitial (same.simpleInitial.mpr rightSimple)
    by_cases leftFinal :
        left.toList.count left.final = 1
    · have rightFinal :
          right.toList.count right.final = 1 :=
        same.simpleFinal.mp leftFinal
      rw [if_neg leftInitial, if_neg rightInitial,
        if_pos leftFinal, if_pos rightFinal, heads]
    · have rightFinal :
          right.toList.count right.final ≠ 1 := by
        intro rightSimple
        exact leftFinal (same.simpleFinal.mpr rightSimple)
      rw [if_neg leftInitial, if_neg rightInitial,
        if_neg leftFinal, if_neg rightFinal, heads]

/-- Equal signatures produce literally equal canonical words. -/
theorem endpointCanonicalWord_eq {left right : Word Nat}
    (same : SameEndpointSequenceSignature left right) :
    endpointCanonicalWord left = endpointCanonicalWord right := by
  apply Word.toList_injective
  simpa using same.endpointCanonicalList_eq

end SameEndpointSequenceSignature

end SemigroupBasis.CoRoots.S5_343Syntax
