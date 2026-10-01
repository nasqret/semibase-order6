import SemigroupBasis.CoRoots.Order6SporadicSection17C5AlphaSlotData

/-! Close alpha using the actual square slots, including the zero-power
case. Together with beta this is the unrestricted arbitrary-list converse
for either literal C5/C6 table, with no assumed comparison data. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem alphaBodySquares_nil_iff (original : List Nat) (pieces : List BodyPiece)
    (good : BodyPiecesGood original pieces) (alpha : ¬ ∃ x, Unrestricted x original) :
    bodySquares pieces = [] ↔ pieces = [] := by
  constructor
  · intro empty
    cases pieces with
    | nil => rfl
    | cons piece rest =>
        rcases piece with ⟨tiles,gap⟩
        have headNonempty := alphaTiles_squares_nonempty original tiles good.1.2.1 good.1.1 alpha
        have nonempty := listAppend_ne_nil_left (tileSquares tiles) (bodySquares rest) headNonempty
        exact False.elim (nonempty empty)
  · intro empty
    rw [empty]
    rfl

theorem alphaBodyForm_shape (original : List Nat) (alpha : ¬ ∃ x, Unrestricted x original)
    (nonempty : (populatedInputForm original).pieces ≠ []) :
    bodyFormWord (populatedInputForm original) =
      (populatedInputForm original).initial ++
        squareWeave (bodySquares (populatedInputForm original).pieces)
          (populatedAlphaInternal original ++ [populatedTerminal original]) := by
  have shape := bodySquareSlots_word original (populatedInputForm original).pieces
    (populatedInputForm_good original).2 alpha
  calc
    bodyFormWord (populatedInputForm original) =
        (populatedInputForm original).initial ++
          squareWeave (bodySquares (populatedInputForm original).pieces)
            (bodySquareSlots (populatedInputForm original).pieces) :=
      congrArg (List.append (populatedInputForm original).initial) shape
    _ = (populatedInputForm original).initial ++
        squareWeave (bodySquares (populatedInputForm original).pieces)
          (populatedAlphaInternal original ++ [populatedTerminal original]) := by
      rw [bodySquareSlots_split (populatedInputForm original).pieces nonempty]
      rfl

namespace Semantics

theorem SameEval.alphaPieces_empty_iff {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (alpha : ¬ ∃ x, Unrestricted x left) :
    (populatedInputForm left).pieces = [] ↔ (populatedInputForm right).pieces = [] := by
  have rightAlpha : ¬ ∃ x, Unrestricted x right := fun witness => alpha (same.beta_iff.mpr witness)
  have squaresEmpty : bodySquares (populatedInputForm left).pieces = [] ↔
      bodySquares (populatedInputForm right).pieces = [] := by
    constructor
    · intro empty
      have permutation := same.collectedSquares_perm
      rw [empty] at permutation
      exact permutation.nil_eq.symm
    · intro empty
      have permutation := same.collectedSquares_perm
      rw [empty] at permutation
      exact permutation.eq_nil
  exact (alphaBodySquares_nil_iff left (populatedInputForm left).pieces
    (populatedInputForm_good left).2 alpha).symm.trans
      (squaresEmpty.trans (alphaBodySquares_nil_iff right (populatedInputForm right).pieces
        (populatedInputForm_good right).2 rightAlpha))

theorem SameEval.alphaForms_derives {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (alpha : ¬ ∃ x, Unrestricted x left)
    (leftNonempty : (populatedInputForm left).pieces ≠ []) :
    ListDerives (bodyFormWord (populatedInputForm left)) (bodyFormWord (populatedInputForm right)) := by
  have rightAlpha : ¬ ∃ x, Unrestricted x right := fun witness => alpha (same.beta_iff.mpr witness)
  have rightNonempty : (populatedInputForm right).pieces ≠ [] :=
    fun empty => leftNonempty ((same.alphaPieces_empty_iff alpha).mpr empty)
  have replay := alphaPermutation_replay same.collectedSquares_perm
    (same.alphaInternal_perm alpha leftNonempty rightNonempty)
    (populatedAlphaInternal_length left alpha leftNonempty)
    (populatedInputForm left).initial (populatedTerminal left)
  have initialEqual := same.populatedInitial_eq
  have terminalEqual := same.populatedTerminal_eq leftNonempty rightNonempty
  rw [alphaBodyForm_shape left alpha leftNonempty,alphaBodyForm_shape right rightAlpha rightNonempty]
  rw [← initialEqual,← terminalEqual]
  exact replay

theorem SameEval.alpha_derives {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (alpha : ¬ ∃ x, Unrestricted x left) :
    ListDerives left right := by
  have leftReduction : ListDerives left (bodyFormWord (populatedInputForm left)) :=
    populatedInputForm_derives left
  have rightReduction : ListDerives right (bodyFormWord (populatedInputForm right)) :=
    populatedInputForm_derives right
  have comparison : ListDerives (bodyFormWord (populatedInputForm left))
      (bodyFormWord (populatedInputForm right)) := by
    by_cases empty : (populatedInputForm left).pieces = []
    · have rightEmpty := (same.alphaPieces_empty_iff alpha).mp empty
      have equal : bodyFormWord (populatedInputForm left) = bodyFormWord (populatedInputForm right) := by
        simp only [bodyFormWord,empty,rightEmpty,bodyPiecesWord,List.append_nil,same.populatedInitial_eq]
      rw [equal]
      exact S5_107.ListDerives.refl _
    · exact same.alphaForms_derives alpha empty
  exact leftReduction.trans (comparison.trans rightReduction.symm)

theorem SameEval.derives {which : Bool} {left right : List Nat} (same : SameEval which left right) :
    ListDerives left right := by
  classical
  by_cases beta : ∃ x, Unrestricted x left
  · exact same.beta_derives beta
  · exact same.alpha_derives beta

end Semantics

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.alphaBodySquares_nil_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.alphaBodyForm_shape
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.alphaPieces_empty_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.alphaForms_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.alpha_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.derives

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
