import SemigroupBasis.CoRoots.Order6SporadicSection17C5ScreenAlphabetWitnesses

/-! Nonempty actual power contexts separate internal simple blocks from
initial and terminal blocks. Every membership/count conversion is explicit. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem listAppend_ne_nil_left (left right : List Nat) (nonempty : left ≠ []) :
    left ++ right ≠ [] := by
  cases left with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs => intro impossible; cases impossible

theorem listAppend_ne_nil_right (left right : List Nat) (nonempty : right ≠ []) :
    left ++ right ≠ [] := by
  cases left with
  | nil => exact nonempty
  | cons x xs => intro impossible; cases impossible

theorem powerTileBody_nonempty (tiles : List PowerTile) (nonempty : tiles ≠ []) :
    powerTileBody tiles ≠ [] := by
  cases tiles with
  | nil => exact False.elim (nonempty rfl)
  | cons tile rest =>
      cases tile <;> intro impossible <;> cases impossible

theorem bodyPiecesWord_nonempty (original : List Nat) (pieces : List BodyPiece)
    (good : BodyPiecesGood original pieces) (nonempty : pieces ≠ []) :
    bodyPiecesWord pieces ≠ [] := by
  cases pieces with
  | nil => exact False.elim (nonempty rfl)
  | cons piece rest =>
      rcases piece with ⟨tiles,gap⟩
      change powerTileBody tiles ++ gap ++ bodyPiecesWord rest ≠ []
      exact listAppend_ne_nil_left _ _
        (listAppend_ne_nil_left _ _ (powerTileBody_nonempty tiles good.1.1))

theorem powerTileBody_member_not_simple (original : List Nat) (tiles : List PowerTile)
    (valid : ∀ tile ∈ tiles, CubicTokenValid original (.power tile))
    (x : Nat) (member : x ∈ powerTileBody tiles) : original.count x ≠ 1 := by
  intro one
  rcases (powerTileBody_mem tiles x).mp member with square | cube
  · have restricted : Restricted x original :=
      valid (.square x) ((tileSquares_mem tiles x).mp square)
    have two := restricted_count_two x original restricted
    omega
  · have unrestricted : Unrestricted x original :=
      valid (.cube x) ((tileCubes_mem tiles x).mp cube)
    exact unrestricted.2.1 one

theorem simpleBlock_not_initial_of_before (word before part after : List Nat)
    (shape : word = before ++ part ++ after) (beforeNonempty : before ≠ [])
    (simple : ∀ x ∈ part, word.count x = 1) : ¬ InitialSimpleBlock word part := by
  intro initial
  cases part with
  | nil => exact initial.1.1 rfl
  | cons x xs =>
      rcases initial.2 with ⟨otherAfter,otherShape⟩
      have one := simple x List.mem_cons_self
      have firstShape : word = before ++ x :: (xs ++ after) := by
        simpa only [List.cons_append,List.append_assoc] using shape
      have secondShape : word = [] ++ x :: (xs ++ otherAfter) := by
        simpa only [List.nil_append,List.cons_append] using otherShape
      have unique := first_split_unique x before (xs ++ after) [] (xs ++ otherAfter)
        (countOne_prefix_absent one firstShape) (countOne_prefix_absent one secondShape)
        (firstShape.symm.trans secondShape)
      exact beforeNonempty unique.1

theorem simpleBlock_not_terminal_of_after (word before part after : List Nat)
    (shape : word = before ++ part ++ after) (afterNonempty : after ≠ [])
    (simple : ∀ x ∈ part, word.count x = 1) : ¬ TerminalSimpleBlock word part := by
  intro terminal
  have reverseShape : word.reverse = after.reverse ++ part.reverse ++ before.reverse := by
    simpa only [List.reverse_append,List.append_assoc] using congrArg List.reverse shape
  have reverseNonempty : after.reverse ≠ [] := by
    intro empty
    apply afterNonempty
    simpa only [List.reverse_reverse,List.reverse_nil] using congrArg List.reverse empty
  have reverseSimple : ∀ x ∈ part.reverse, word.reverse.count x = 1 := by
    intro x member
    simpa only [List.count_reverse] using simple x (List.mem_reverse.mp member)
  exact simpleBlock_not_initial_of_before word.reverse after.reverse part.reverse before.reverse
    reverseShape reverseNonempty reverseSimple terminal.reverse_initial

theorem populatedInitial_block (original : List Nat)
    (nonempty : (populatedInputForm original).initial ≠ []) :
    InitialSimpleBlock original (populatedInputForm original).initial := by
  have derived := Semantics.derives_sameEval false (populatedInputForm_derives original)
  apply (derived.initialSimpleBlock (populatedInputForm original).initial).mpr
  apply initialSimpleBlock_of_context _ _ _ rfl nonempty
  · intro x member
    exact (derived.countOne x).mp ((populatedInputForm_good original).1 x member)
  · intro x tail shape one
    exact bodyPiecesWord_head_not_simple original (populatedInputForm original).pieces
      (populatedInputForm_good original).2 x tail shape ((derived.countOne x).mpr one)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.listAppend_ne_nil_left
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.listAppend_ne_nil_right
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyPiecesWord_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_member_not_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.simpleBlock_not_initial_of_before
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.simpleBlock_not_terminal_of_after
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedInitial_block

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
