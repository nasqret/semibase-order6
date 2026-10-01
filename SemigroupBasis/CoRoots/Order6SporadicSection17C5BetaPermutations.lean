import SemigroupBasis.CoRoots.Order6SporadicSection17C5SquareMultiplicity

/-! Replay arbitrary beta internal-block permutations using the actual
nonempty common cube word. Initial and terminal gaps stay fixed. This module
does not assume that semantic equivalence has already supplied those gaps. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem swapRepeatedBlocksList (body first second : List Nat)
    (bodyNonempty : body ≠ []) (firstNonempty : first ≠ []) (secondNonempty : second ≠ []) :
    ListDerives (body ++ first ++ body ++ second ++ body)
      (body ++ second ++ body ++ first ++ body) := by
  cases body with
  | nil => exact False.elim (bodyNonempty rfl)
  | cons h t =>
      cases first with
      | nil => exact False.elim (firstNonempty rfl)
      | cons x xs =>
          cases second with
          | nil => exact False.elim (secondNonempty rfl)
          | cons y ys =>
              simpa only [S5_107.listWordOfCons,Word.toList] using
                swapRepeatedBlocks (S5_107.listWordOfCons h t)
                  (S5_107.listWordOfCons x xs) (S5_107.listWordOfCons y ys)

def uniformBodyTail (body : List Nat) : List (List Nat) → List Nat
  | [] => []
  | gap :: rest => gap ++ uniformBodyWord body rest

theorem uniformBodyWord_final (body : List Nat) (gaps : List (List Nat)) (terminal : List Nat) :
    uniformBodyWord body (gaps ++ [terminal]) = body ++ uniformBodyTail body (gaps ++ [terminal]) := by
  cases gaps <;> simp only [List.nil_append,List.cons_append,uniformBodyWord,uniformBodyTail,List.append_assoc]

theorem uniformBodyWord_gap_perm {left right : List (List Nat)} (permutation : left.Perm right)
    (body terminal : List Nat) (bodyNonempty : body ≠ [])
    (gapsNonempty : ∀ gap ∈ left, gap ≠ []) :
    ListDerives (uniformBodyWord body (left ++ [terminal]))
      (uniformBodyWord body (right ++ [terminal])) := by
  induction permutation with
  | nil => exact S5_107.ListDerives.refl _
  | @cons gap leftTail rightTail permutation ih =>
      have tailNonempty : ∀ other ∈ leftTail, other ≠ [] :=
        fun other member => gapsNonempty other (List.mem_cons_of_mem gap member)
      simpa only [List.cons_append,uniformBodyWord,List.append_assoc]
        using (ih tailNonempty).prepend (body ++ gap)
  | swap a b gaps =>
      have aNonempty : a ≠ [] := gapsNonempty a (by simp)
      have bNonempty : b ≠ [] := gapsNonempty b (by simp)
      have localSwap := (swapRepeatedBlocksList body b a bodyNonempty bNonempty aNonempty).append
        (uniformBodyTail body (gaps ++ [terminal]))
      have leftShape : uniformBodyWord body ((b :: a :: gaps) ++ [terminal]) =
          body ++ b ++ body ++ a ++ body ++ uniformBodyTail body (gaps ++ [terminal]) := by
        simp only [List.cons_append,uniformBodyWord]
        rw [uniformBodyWord_final]
        simp only [List.append_assoc]
      have rightShape : uniformBodyWord body ((a :: b :: gaps) ++ [terminal]) =
          body ++ a ++ body ++ b ++ body ++ uniformBodyTail body (gaps ++ [terminal]) := by
        simp only [List.cons_append,uniformBodyWord]
        rw [uniformBodyWord_final]
        simp only [List.append_assoc]
      rw [leftShape,rightShape]
      exact localSwap
  | trans first second ihFirst ihSecond =>
      have middleNonempty : ∀ gap ∈ _, gap ≠ [] :=
        fun gap member => gapsNonempty gap (first.mem_iff.mpr member)
      exact (ihFirst gapsNonempty).trans (ihSecond middleNonempty)

theorem uniformBodyWord_body_derives {left right : List Nat} (derivation : ListDerives left right)
    (gaps : List (List Nat)) :
    ListDerives (uniformBodyWord left gaps) (uniformBodyWord right gaps) := by
  induction gaps with
  | nil => exact S5_107.ListDerives.refl _
  | cons gap rest ih =>
      have first : ListDerives (left ++ gap ++ uniformBodyWord left rest)
          (right ++ gap ++ uniformBodyWord left rest) := by
        simpa only [List.append_assoc] using derivation.append (gap ++ uniformBodyWord left rest)
      have second := ih.prepend (right ++ gap)
      exact first.trans second

def betaPresentation (initial : List Nat) (squares cubes : List Nat)
    (internal : List (List Nat)) (terminal : List Nat) : List Nat :=
  initial ++ squareBody squares ++ uniformBodyWord (cubeBody cubes) (internal ++ [terminal])

theorem betaPermutation_replay {leftSquares rightSquares leftCubes rightCubes : List Nat}
    {leftGaps rightGaps : List (List Nat)}
    (squarePermutation : leftSquares.Perm rightSquares)
    (cubeContent : ∀ y, y ∈ leftCubes ↔ y ∈ rightCubes)
    (gapPermutation : leftGaps.Perm rightGaps)
    (cubeNonempty : leftCubes ≠ []) (gapsNonempty : ∀ gap ∈ leftGaps, gap ≠ [])
    (initial terminal : List Nat) :
    ListDerives (betaPresentation initial leftSquares leftCubes leftGaps terminal)
      (betaPresentation initial rightSquares rightCubes rightGaps terminal) := by
  have squares := (squareBody_perm squarePermutation).append
    (uniformBodyWord (cubeBody leftCubes) (leftGaps ++ [terminal]))
  have gaps := (uniformBodyWord_gap_perm gapPermutation (cubeBody leftCubes) terminal
    (cubeBody_nonempty leftCubes cubeNonempty) gapsNonempty).prepend (squareBody rightSquares)
  have cubes := (uniformBodyWord_body_derives (cubeBody_sameContent cubeContent)
    (rightGaps ++ [terminal])).prepend (squareBody rightSquares)
  simpa only [betaPresentation,List.append_assoc] using (squares.trans (gaps.trans cubes)).prepend initial

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.swapRepeatedBlocksList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.uniformBodyWord_final
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.uniformBodyWord_gap_perm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.uniformBodyWord_body_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.betaPermutation_replay

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
