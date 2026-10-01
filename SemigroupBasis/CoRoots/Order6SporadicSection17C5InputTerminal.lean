import SemigroupBasis.CoRoots.Order6SporadicSection17C5SimpleSuffixes

/-! Extract the terminal gap from the actual populated input. Its preceding
power body ends in a nonsimple letter, even after arbitrary earlier context.
Semantic suffix comparison therefore fixes the actual beta terminal word. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem powerTileWord_reverse (tile : PowerTile) : (powerTileWord tile).reverse = powerTileWord tile := by
  cases tile <;> rfl

theorem powerTileBody_reverse (tiles : List PowerTile) :
    (powerTileBody tiles).reverse = powerTileBody tiles.reverse := by
  induction tiles with
  | nil => rfl
  | cons tile rest ih =>
      simp only [powerTileBody_cons,List.reverse_append,List.reverse_cons,ih,powerTileWord_reverse,
        powerTileBody_append,powerTileBody_nil,List.append_nil]

theorem powerTileBody_head_not_simple (original : List Nat) (tiles : List PowerTile)
    (nonempty : tiles ≠ []) (valid : ∀ tile ∈ tiles, CubicTokenValid original (.power tile))
    (after : List Nat) (x : Nat) (tail : List Nat)
    (shape : powerTileBody tiles ++ after = x :: tail) : original.count x ≠ 1 := by
  cases tiles with
  | nil => exact False.elim (nonempty rfl)
  | cons tile rest =>
      cases tile with
      | square y =>
          have equal : y = x := (List.cons.inj shape).1
          subst x
          have restricted : Restricted y original := valid (.square y) List.mem_cons_self
          have two := restricted_count_two y original restricted
          omega
      | cube y =>
          have equal : y = x := (List.cons.inj shape).1
          subst x
          have unrestricted : Unrestricted y original := valid (.cube y) List.mem_cons_self
          exact unrestricted.2.1

theorem powerTileBody_tail_not_simple (original : List Nat) (tiles : List PowerTile)
    (nonempty : tiles ≠ []) (valid : ∀ tile ∈ tiles, CubicTokenValid original (.power tile))
    (before leading : List Nat) (x : Nat)
    (shape : before ++ powerTileBody tiles = leading ++ [x]) : original.count x ≠ 1 := by
  have reverseNonempty : tiles.reverse ≠ [] := by
    intro empty
    apply nonempty
    simpa only [List.reverse_reverse,List.reverse_nil] using congrArg List.reverse empty
  have reverseValid : ∀ tile ∈ tiles.reverse, CubicTokenValid original (.power tile) := by
    intro tile member
    exact valid tile (by simpa only [List.mem_reverse] using member)
  have reverseShape : powerTileBody tiles.reverse ++ before.reverse = x :: leading.reverse := by
    simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
      List.cons_append,powerTileBody_reverse] using congrArg List.reverse shape
  exact powerTileBody_head_not_simple original tiles.reverse reverseNonempty reverseValid
    before.reverse x leading.reverse reverseShape

def bodyTerminal : List BodyPiece → List Nat
  | [] => []
  | [(_,gap)] => gap
  | _ :: next :: rest => bodyTerminal (next :: rest)

def bodyBeforeTerminal : List BodyPiece → List Nat
  | [] => []
  | [(tiles,_)] => powerTileBody tiles
  | (tiles,gap) :: next :: rest => powerTileBody tiles ++ gap ++ bodyBeforeTerminal (next :: rest)

theorem bodyPiecesWord_terminal_split (pieces : List BodyPiece) :
    bodyPiecesWord pieces = bodyBeforeTerminal pieces ++ bodyTerminal pieces := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
      rcases piece with ⟨tiles,gap⟩
      cases rest with
      | nil => simp only [bodyPiecesWord,bodyBeforeTerminal,bodyTerminal,List.append_nil]
      | cons next rest =>
          change powerTileBody tiles ++ gap ++ bodyPiecesWord (next :: rest) =
            (powerTileBody tiles ++ gap ++ bodyBeforeTerminal (next :: rest)) ++ bodyTerminal (next :: rest)
          rw [ih]
          simp only [List.append_assoc]

theorem bodyTerminal_simple (original : List Nat) (pieces : List BodyPiece) :
    BodyPiecesGood original pieces → ∀ x ∈ bodyTerminal pieces, original.count x = 1 := by
  induction pieces with
  | nil => intro good x member; cases member
  | cons piece rest ih =>
      rcases piece with ⟨tiles,gap⟩
      intro good
      cases rest with
      | nil => exact good.1.2.2
      | cons next rest => exact ih good.2.2

theorem bodyBeforeTerminal_tail_not_simple (original : List Nat) (pieces : List BodyPiece) :
    BodyPiecesGood original pieces → pieces ≠ [] →
      ∀ (before leading : List Nat) (x : Nat),
        before ++ bodyBeforeTerminal pieces = leading ++ [x] → original.count x ≠ 1 := by
  induction pieces with
  | nil => intro good nonempty; exact False.elim (nonempty rfl)
  | cons piece rest ih =>
      rcases piece with ⟨tiles,gap⟩
      intro good nonempty before leading x shape
      cases rest with
      | nil => exact powerTileBody_tail_not_simple original tiles good.1.1 good.1.2.1 before leading x shape
      | cons next rest =>
          apply ih good.2.2 (by simp) (before ++ powerTileBody tiles ++ gap) leading x
          simpa only [bodyBeforeTerminal,List.append_assoc] using shape

def populatedTerminal (original : List Nat) : List Nat :=
  bodyTerminal (populatedInputForm original).pieces

theorem populatedInputForm_terminal_shape (original : List Nat) :
    bodyFormWord (populatedInputForm original) =
      ((populatedInputForm original).initial ++ bodyBeforeTerminal (populatedInputForm original).pieces) ++
        populatedTerminal original := by
  simp only [bodyFormWord,bodyPiecesWord_terminal_split,populatedTerminal,List.append_assoc]

theorem populatedTerminal_simple (original : List Nat) :
    ∀ x ∈ populatedTerminal original, original.count x = 1 :=
  bodyTerminal_simple original (populatedInputForm original).pieces (populatedInputForm_good original).2

namespace Semantics

theorem SameEval.populatedTerminal_eq {which : Bool} {left right : List Nat}
    (same : SameEval which left right)
    (leftNonempty : (populatedInputForm left).pieces ≠ [])
    (rightNonempty : (populatedInputForm right).pieces ≠ []) :
    populatedTerminal left = populatedTerminal right := by
  have leftDerived := derives_sameEval which (populatedInputForm_derives left)
  have rightDerived := derives_sameEval which (populatedInputForm_derives right)
  have forms : SameEval which (bodyFormWord (populatedInputForm left)) (bodyFormWord (populatedInputForm right)) :=
    fun value => (leftDerived value).symm.trans ((same value).trans (rightDerived value))
  apply forms.simpleSuffixes_eq (populatedInputForm_terminal_shape left) (populatedInputForm_terminal_shape right)
  · intro x member
    exact (leftDerived.countOne x).mp (populatedTerminal_simple left x member)
  · intro x member
    exact (rightDerived.countOne x).mp (populatedTerminal_simple right x member)
  · intro leading x shape one
    exact bodyBeforeTerminal_tail_not_simple left (populatedInputForm left).pieces (populatedInputForm_good left).2
      leftNonempty (populatedInputForm left).initial leading x shape ((leftDerived.countOne x).mpr one)
  · intro leading x shape one
    exact bodyBeforeTerminal_tail_not_simple right (populatedInputForm right).pieces (populatedInputForm_good right).2
      rightNonempty (populatedInputForm right).initial leading x shape ((rightDerived.countOne x).mpr one)

theorem SameEval.betaTerminal_eq {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (beta : ∃ x, Unrestricted x left) :
    populatedTerminal left = populatedTerminal right := by
  have rightBeta : ∃ x, Unrestricted x right := by
    rcases beta with ⟨x,unrestricted⟩
    exact ⟨x,(same.unrestricted x).mp unrestricted⟩
  exact same.populatedTerminal_eq (populatedInputForm_pieces_nonempty left beta)
    (populatedInputForm_pieces_nonempty right rightBeta)

end Semantics

theorem populatedTerminal_block (original : List Nat)
    (piecesNonempty : (populatedInputForm original).pieces ≠ [])
    (nonempty : populatedTerminal original ≠ []) :
    TerminalSimpleBlock original (populatedTerminal original) := by
  have derived := Semantics.derives_sameEval false (populatedInputForm_derives original)
  apply (derived.terminalSimpleBlock (populatedTerminal original)).mpr
  apply terminalSimpleBlock_of_context _ _ _ (populatedInputForm_terminal_shape original) nonempty
  · intro x member
    exact (derived.countOne x).mp (populatedTerminal_simple original x member)
  · intro leading x shape one
    exact bodyBeforeTerminal_tail_not_simple original (populatedInputForm original).pieces
      (populatedInputForm_good original).2 piecesNonempty (populatedInputForm original).initial leading x shape
      ((derived.countOne x).mpr one)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileWord_reverse
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_reverse
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_head_not_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_tail_not_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyPiecesWord_terminal_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyTerminal_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyBeforeTerminal_tail_not_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedInputForm_terminal_shape
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedTerminal_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.populatedTerminal_eq
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.betaTerminal_eq
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedTerminal_block

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
