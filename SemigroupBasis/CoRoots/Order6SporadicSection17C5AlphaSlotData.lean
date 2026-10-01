import SemigroupBasis.CoRoots.Order6SporadicSection17C5AlphaSlotRendering

/-! Extract the terminal slot and retain the multiplicity of empty internal
slots. Nonempty slots are exactly the already-characterized internal blocks;
their permutation plus the square count determines the full slot multiset. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

def bodyInternalSquareSlots : List BodyPiece → List (List Nat)
  | [] => []
  | [(tiles,_)] => List.replicate ((tileSquares tiles).length - 1) []
  | (tiles,gap) :: next :: rest =>
      List.replicate ((tileSquares tiles).length - 1) [] ++
        (gap :: bodyInternalSquareSlots (next :: rest))

theorem bodySquareSlots_split (pieces : List BodyPiece) (nonempty : pieces ≠ []) :
    bodySquareSlots pieces = bodyInternalSquareSlots pieces ++ [bodyTerminal pieces] := by
  induction pieces with
  | nil => exact False.elim (nonempty rfl)
  | cons piece rest ih =>
      rcases piece with ⟨tiles,gap⟩
      cases rest with
      | nil =>
          simp only [bodySquareSlots,bodyInternalSquareSlots,bodyTerminal,tileSquareSlots,List.append_nil]
      | cons next rest =>
          change tileSquareSlots tiles gap ++ bodySquareSlots (next :: rest) =
            (List.replicate ((tileSquares tiles).length - 1) [] ++
              (gap :: bodyInternalSquareSlots (next :: rest))) ++ [bodyTerminal (next :: rest)]
          rw [ih (by simp)]
          simp only [tileSquareSlots,List.append_assoc,List.cons_append,List.nil_append]

theorem bodyInternalSquareSlots_length (original : List Nat) (pieces : List BodyPiece)
    (good : BodyPiecesGood original pieces) (alpha : ¬ ∃ x, Unrestricted x original)
    (nonempty : pieces ≠ []) :
    (bodySquares pieces).length = (bodyInternalSquareSlots pieces).length + 1 := by
  have length := bodySquareSlots_length original pieces good alpha
  rw [bodySquareSlots_split pieces nonempty] at length
  simpa only [List.length_append,List.length_cons,List.length_nil] using length.symm

def nonemptyGaps (gaps : List (List Nat)) : List (List Nat) :=
  gaps.filter (fun gap => !gap.isEmpty)

theorem nonemptyGaps_append (left right : List (List Nat)) :
    nonemptyGaps (left ++ right) = nonemptyGaps left ++ nonemptyGaps right :=
  List.filter_append (p := fun gap : List Nat => !gap.isEmpty) left right

theorem nonemptyGaps_replicate_empty (n : Nat) :
    nonemptyGaps (List.replicate n []) = [] := by
  change (List.replicate n ([] : List Nat)).filter (fun gap => !gap.isEmpty) = []
  exact List.filter_replicate_of_neg (by decide)

theorem nonemptyGaps_cons_nonempty (gap : List Nat) (rest : List (List Nat)) (nonempty : gap ≠ []) :
    nonemptyGaps (gap :: rest) = gap :: nonemptyGaps rest := by
  cases gap with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs => rfl

theorem nonemptyGaps_bodyInternalSlots (original : List Nat) (pieces : List BodyPiece)
    (good : BodyPiecesGood original pieces) :
    nonemptyGaps (bodyInternalSquareSlots pieces) = bodyInternalGaps pieces := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
      rcases piece with ⟨tiles,gap⟩
      cases rest with
      | nil => exact nonemptyGaps_replicate_empty _
      | cons next rest =>
          change nonemptyGaps (List.replicate ((tileSquares tiles).length - 1) [] ++
            (gap :: bodyInternalSquareSlots (next :: rest))) = gap :: bodyInternalGaps (next :: rest)
          rw [nonemptyGaps_append,nonemptyGaps_replicate_empty,List.nil_append,
            nonemptyGaps_cons_nonempty gap _ (good.2.1 (by simp)),ih good.2.2]

def populatedAlphaInternal (original : List Nat) : List (List Nat) :=
  bodyInternalSquareSlots (populatedInputForm original).pieces

theorem populatedAlphaInternal_filter (original : List Nat) :
    nonemptyGaps (populatedAlphaInternal original) = populatedInternal original :=
  nonemptyGaps_bodyInternalSlots original (populatedInputForm original).pieces (populatedInputForm_good original).2

theorem populatedAlphaInternal_length (original : List Nat) (alpha : ¬ ∃ x, Unrestricted x original)
    (nonempty : (populatedInputForm original).pieces ≠ []) :
    (bodySquares (populatedInputForm original).pieces).length = (populatedAlphaInternal original).length + 1 :=
  bodyInternalSquareSlots_length original (populatedInputForm original).pieces
    (populatedInputForm_good original).2 alpha nonempty

theorem nonemptyGaps_count (gaps : List (List Nat)) (part : List Nat) (nonempty : part ≠ []) :
    (nonemptyGaps gaps).count part = gaps.count part := by
  have kept : (!part.isEmpty) = true := by
    cases part with
    | nil => exact False.elim (nonempty rfl)
    | cons x xs => rfl
  exact List.count_filter kept

theorem nonemptyGaps_length_add_empty_count (gaps : List (List Nat)) :
    (nonemptyGaps gaps).length + gaps.count [] = gaps.length := by
  induction gaps with
  | nil => rfl
  | cons gap rest ih =>
      cases gap with
      | nil =>
          change (nonemptyGaps rest).length + (([] : List Nat) :: rest).count [] =
            (([] : List Nat) :: rest).length
          simp only [List.count_cons_self,List.length_cons]
          omega
      | cons x xs =>
          have different : (x :: xs) ≠ ([] : List Nat) := by intro impossible; cases impossible
          change ((x :: xs) :: nonemptyGaps rest).length + ((x :: xs) :: rest).count [] =
            ((x :: xs) :: rest).length
          simp only [List.length_cons,List.count_cons_of_ne different]
          omega

theorem perm_of_nonemptyGaps {left right : List (List Nat)}
    (filtered : (nonemptyGaps left).Perm (nonemptyGaps right))
    (length : left.length = right.length) : left.Perm right := by
  apply List.perm_iff_count.mpr
  intro part
  by_cases empty : part = []
  · subst part
    have leftCount := nonemptyGaps_length_add_empty_count left
    have rightCount := nonemptyGaps_length_add_empty_count right
    have sameFilteredLength := filtered.length_eq
    omega
  · exact (nonemptyGaps_count left part empty).symm.trans
      (((List.perm_iff_count.mp filtered) part).trans (nonemptyGaps_count right part empty))

namespace Semantics

theorem SameEval.alphaInternal_perm {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (alpha : ¬ ∃ x, Unrestricted x left)
    (leftNonempty : (populatedInputForm left).pieces ≠ [])
    (rightNonempty : (populatedInputForm right).pieces ≠ []) :
    (populatedAlphaInternal left).Perm (populatedAlphaInternal right) := by
  have rightAlpha : ¬ ∃ x, Unrestricted x right := fun witness => alpha (same.beta_iff.mpr witness)
  have filtered : (nonemptyGaps (populatedAlphaInternal left)).Perm
      (nonemptyGaps (populatedAlphaInternal right)) := by
    simp only [populatedAlphaInternal_filter]
    exact same.populatedInternal_perm
  have leftLength := populatedAlphaInternal_length left alpha leftNonempty
  have rightLength := populatedAlphaInternal_length right rightAlpha rightNonempty
  have markersLength := same.collectedSquares_perm.length_eq
  apply perm_of_nonemptyGaps filtered
  omega

end Semantics

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodySquareSlots_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyInternalSquareSlots_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.nonemptyGaps_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.nonemptyGaps_replicate_empty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.nonemptyGaps_cons_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.nonemptyGaps_bodyInternalSlots
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedAlphaInternal_filter
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedAlphaInternal_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.nonemptyGaps_count
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.nonemptyGaps_length_add_empty_count
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.perm_of_nonemptyGaps
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.alphaInternal_perm

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
