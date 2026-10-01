import SemigroupBasis.CoRoots.S5_107
import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_107Syntax

namespace SemigroupBasis.CoRoots.S5_107

open SemigroupBasis

/-- Remove every later occurrence of one rendered square label while
retaining its first square. -/
private theorem listDerivesRemoveRepeatedSquare (anchor : Nat) :
    ∀ labels : List Nat,
      ListDerives basis
        (renderMultipleSquares (anchor :: labels))
        (renderMultipleSquares
          (anchor ::
            labels.filter
              (fun label => decide (label ≠ anchor))))
  | [] => ListDerives.refl _
  | label :: labels => by
      by_cases equal : label = anchor
      · subst label
        have contract :=
          (ListDerives.ofWord <|
            derivesFourToTwo
              (Word.singleton anchor)).append
              (renderMultipleSquares labels)
        have contractStep :
            ListDerives basis
              (renderMultipleSquares
                (anchor :: anchor :: labels))
              (renderMultipleSquares (anchor :: labels)) := by
          simpa [renderMultipleSquares, Word.toList,
            Word.singleton, Word.append, List.append_assoc] using
            contract
        simpa [renderMultipleSquares] using
          contractStep.trans
            (listDerivesRemoveRepeatedSquare anchor labels)
      · have commuteFront :
            ListDerives basis
              (renderMultipleSquares
                (anchor :: label :: labels))
              (renderMultipleSquares
                (label :: anchor :: labels)) := by
          simpa [renderMultipleSquares, List.append_assoc] using
            (ListDerives.ofWord <|
              derivesSquareBlockCommutation
                (Word.singleton anchor)
                (Word.singleton label)).append
                (renderMultipleSquares labels)
        have removeTail :
            ListDerives basis
              (renderMultipleSquares
                (label :: anchor :: labels))
              (renderMultipleSquares
                (label :: anchor ::
                  labels.filter
                    (fun next =>
                      decide (next ≠ anchor)))) := by
          simpa [renderMultipleSquares] using
            (listDerivesRemoveRepeatedSquare anchor labels).prepend
              [label, label]
        have commuteBack :
            ListDerives basis
              (renderMultipleSquares
                (label :: anchor ::
                  labels.filter
                    (fun next =>
                      decide (next ≠ anchor))))
              (renderMultipleSquares
                (anchor :: label ::
                  labels.filter
                    (fun next =>
                      decide (next ≠ anchor)))) := by
          simpa [renderMultipleSquares, List.append_assoc] using
            (ListDerives.ofWord <|
              derivesSquareBlockCommutation
                (Word.singleton label)
                (Word.singleton anchor)).append
                (renderMultipleSquares
                  (labels.filter
                    (fun next =>
                      decide (next ≠ anchor))))
        simpa [renderMultipleSquares, equal] using
          commuteFront.trans (removeTail.trans commuteBack)

/-- Rendering two copies of every input label derives the same rendering
after retaining only the first occurrence of each label. -/
theorem listDerivesMultipleSquareDedup :
    ∀ labels : List Nat,
      ListDerives basis
        (renderMultipleSquares labels)
        (renderMultipleSquares (distinctLetters labels))
  | [] => ListDerives.empty
  | label :: labels => by
      have dedupTail :
          ListDerives basis
            (renderMultipleSquares (label :: labels))
            (renderMultipleSquares
              (label :: distinctLetters labels)) := by
        simpa [renderMultipleSquares] using
          (listDerivesMultipleSquareDedup labels).prepend
            [label, label]
      exact
        dedupTail.trans
          (listDerivesRemoveRepeatedSquare
            label (distinctLetters labels))

end SemigroupBasis.CoRoots.S5_107
