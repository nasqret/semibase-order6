import SemigroupBasis.CoRoots.Order6SporadicSection17C5SimpleBlocks
import SemigroupBasis.CoRoots.Order6SporadicSection17C5CubicNormal

/-! Arbitrary permutation replay for alpha forms, including empty internal
gaps. Power tiles retain their exponents; no restricted square is collapsed.
These are raw13 derivations, not semantic-cancellation or completeness fields. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

inductive PowerTile where
  | square (marker : Nat)
  | cube (marker : Nat)
  deriving DecidableEq, Repr

def powerTileWord : PowerTile → List Nat
  | .square x => [x,x]
  | .cube x => [x,x,x]

def powerTileBody (tiles : List PowerTile) : List Nat := tiles.flatMap powerTileWord

theorem swapPowerTiles (left right : PowerTile) (gap : List Nat) :
    ListDerives (powerTileWord left ++ gap ++ powerTileWord right)
      (powerTileWord right ++ gap ++ powerTileWord left) := by
  cases left with
  | square x =>
      cases right with
      | square y => exact swapSquares x y gap
      | cube y => exact (swapCubeSquare y x gap).symm
  | cube x =>
      cases right with
      | square y => exact swapCubeSquare x y gap
      | cube y => exact swapCubes x y gap

theorem powerTileBody_perm {left right : List PowerTile} (permutation : left.Perm right) :
    ListDerives (powerTileBody left) (powerTileBody right) := by
  induction permutation with
  | nil => exact S5_107.ListDerives.refl _
  | cons tile permutation ih =>
      simpa [powerTileBody,List.append_assoc] using ih.prepend (powerTileWord tile)
  | swap a b rest =>
      simpa [powerTileBody,List.append_assoc] using
        (swapPowerTiles b a []).append (powerTileBody rest)
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

theorem swapSquareGapsList (h k t : Nat) (left right : List Nat) :
    ListDerives ([h,h] ++ left ++ [k,k] ++ right ++ [t,t])
      ([h,h] ++ right ++ [k,k] ++ left ++ [t,t]) := by
  cases left with
  | nil => simpa [List.append_assoc] using slideSquare h k t right
  | cons x xs =>
      cases right with
      | nil => simpa [List.append_assoc] using (slideSquare h k t (x :: xs)).symm
      | cons y ys =>
          simpa [S5_107.listWordOfCons,Word.toList,List.append_assoc] using
            swapSquareGaps h k t (S5_107.listWordOfCons x xs) (S5_107.listWordOfCons y ys)

def squareWeave : List Nat → List (List Nat) → List Nat
  | [], _ => []
  | x :: xs, [] => [x,x] ++ squareWeave xs []
  | x :: xs, gap :: gaps => [x,x] ++ gap ++ squareWeave xs gaps

def squareWeaveTail (markers : List Nat) : List (List Nat) → List Nat
  | [] => squareWeave markers []
  | gap :: gaps => gap ++ squareWeave markers gaps

theorem squareWeave_cons (x : Nat) (markers : List Nat) (gaps : List (List Nat)) :
    squareWeave (x :: markers) gaps = [x,x] ++ squareWeaveTail markers gaps := by
  cases gaps <;> rfl

theorem squareWeave_marker_perm {left right : List Nat} (permutation : left.Perm right) :
    ∀ gaps : List (List Nat), left.length = gaps.length →
      ListDerives (squareWeave left gaps) (squareWeave right gaps) := by
  induction permutation with
  | nil =>
      intro gaps length
      exact S5_107.ListDerives.refl _
  | @cons marker leftTail rightTail permutation ih =>
      intro gaps length
      cases gaps with
      | nil => simp at length
      | cons gap rest =>
          have tailLength : leftTail.length = rest.length := by
            simp only [List.length_cons] at length
            omega
          simpa only [squareWeave,List.append_assoc] using (ih rest tailLength).prepend ([marker,marker] ++ gap)
  | swap a b markers =>
      intro gaps length
      cases gaps with
      | nil => simp at length
      | cons gap rest =>
          cases rest with
          | nil => simp at length
          | cons next remaining =>
              simpa only [squareWeave,List.append_assoc] using
                (swapSquares b a gap).append (next ++ squareWeave markers remaining)
  | trans first second ihFirst ihSecond =>
      intro gaps length
      exact (ihFirst gaps length).trans (ihSecond gaps (first.length_eq.symm.trans length))

theorem squareWeave_gap_perm {left right : List (List Nat)} (permutation : left.Perm right)
    (terminal : List Nat) :
    ∀ markers : List Nat, markers.length = left.length + 1 →
      ListDerives (squareWeave markers (left ++ [terminal]))
        (squareWeave markers (right ++ [terminal])) := by
  induction permutation with
  | nil => intro markers _; exact S5_107.ListDerives.refl _
  | @cons gap leftTail rightTail permutation ih =>
      intro markers length
      cases markers with
      | nil => simp at length
      | cons marker rest =>
          have tailLength : rest.length = leftTail.length + 1 := by
            simp only [List.length_cons] at length
            omega
          simpa only [List.cons_append,squareWeave,List.append_assoc] using
            (ih rest tailLength).prepend ([marker,marker] ++ gap)
  | swap a b gaps =>
      intro markers length
      cases markers with
      | nil => simp at length
      | cons h first =>
          cases first with
          | nil => simp at length
          | cons k second =>
              cases second with
              | nil => simp at length
              | cons t rest =>
                  have localSwap := (swapSquareGapsList h k t b a).append
                    (squareWeaveTail rest (gaps ++ [terminal]))
                  simpa only [List.cons_append,squareWeave,squareWeave_cons,squareWeaveTail,List.append_assoc] using localSwap
  | trans first second ihFirst ihSecond =>
      intro markers length
      have nextLength := length.trans (congrArg (fun n : Nat => n + 1) first.length_eq)
      exact (ihFirst markers length).trans (ihSecond markers nextLength)

theorem alphaPermutation_replay {leftMarkers rightMarkers : List Nat}
    {leftGaps rightGaps : List (List Nat)}
    (markerPermutation : leftMarkers.Perm rightMarkers) (gapPermutation : leftGaps.Perm rightGaps)
    (length : leftMarkers.length = leftGaps.length + 1) (initial terminal : List Nat) :
    ListDerives (initial ++ squareWeave leftMarkers (leftGaps ++ [terminal]))
      (initial ++ squareWeave rightMarkers (rightGaps ++ [terminal])) := by
  have fullLength : leftMarkers.length = (leftGaps ++ [terminal]).length := by
    simpa using length
  have first := squareWeave_marker_perm markerPermutation (leftGaps ++ [terminal]) fullLength
  have nextLength := markerPermutation.length_eq.symm.trans length
  have second := squareWeave_gap_perm gapPermutation terminal rightMarkers nextLength
  exact (first.trans second).prepend initial

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.swapPowerTiles
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_perm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.swapSquareGapsList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.squareWeave_marker_perm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.squareWeave_gap_perm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.alphaPermutation_replay

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
