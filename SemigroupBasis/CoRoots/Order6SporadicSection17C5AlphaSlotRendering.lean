import SemigroupBasis.CoRoots.Order6SporadicSection17C5BetaSemanticComparison

/-! In the alpha case every actual power tile is a square. Expand each
nonempty power body into one gap slot per square, retaining empty slots. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem alphaTiles_eq_squareMap (original : List Nat) (tiles : List PowerTile)
    (valid : ∀ tile ∈ tiles, CubicTokenValid original (.power tile))
    (alpha : ¬ ∃ x, Unrestricted x original) :
    tiles = (tileSquares tiles).map PowerTile.square := by
  induction tiles with
  | nil => rfl
  | cons tile rest ih =>
      have tailValid : ∀ other ∈ rest, CubicTokenValid original (.power other) :=
        fun other member => valid other (List.mem_cons_of_mem tile member)
      cases tile with
      | square x =>
          change PowerTile.square x :: rest = PowerTile.square x :: (tileSquares rest).map PowerTile.square
          exact congrArg (List.cons (PowerTile.square x)) (ih tailValid)
      | cube x => exact False.elim (alpha ⟨x,valid (.cube x) List.mem_cons_self⟩)

theorem alphaTiles_squares_nonempty (original : List Nat) (tiles : List PowerTile)
    (valid : ∀ tile ∈ tiles, CubicTokenValid original (.power tile))
    (nonempty : tiles ≠ []) (alpha : ¬ ∃ x, Unrestricted x original) :
    tileSquares tiles ≠ [] := by
  intro empty
  apply nonempty
  rw [alphaTiles_eq_squareMap original tiles valid alpha,empty]
  rfl

theorem alphaPowerBody_eq (original : List Nat) (tiles : List PowerTile)
    (valid : ∀ tile ∈ tiles, CubicTokenValid original (.power tile))
    (alpha : ¬ ∃ x, Unrestricted x original) :
    powerTileBody tiles = squareBody (tileSquares tiles) := by
  calc
    powerTileBody tiles = powerTileBody ((tileSquares tiles).map PowerTile.square) :=
      congrArg powerTileBody (alphaTiles_eq_squareMap original tiles valid alpha)
    _ = squareBody (tileSquares tiles) := powerTileBody_map_square (tileSquares tiles)

theorem squareWeave_append_exact (left right : List Nat) (gaps trailing : List (List Nat))
    (length : left.length = gaps.length) :
    squareWeave (left ++ right) (gaps ++ trailing) =
      squareWeave left gaps ++ squareWeave right trailing := by
  induction left generalizing gaps with
  | nil =>
      have empty : gaps = [] := List.length_eq_zero_iff.mp length.symm
      subst gaps
      rfl
  | cons x xs ih =>
      cases gaps with
      | nil => simp at length
      | cons gap rest =>
          have tailLength : xs.length = rest.length := by
            simp only [List.length_cons] at length
            omega
          simp only [List.cons_append,squareWeave]
          rw [ih rest tailLength]
          simp only [List.append_assoc]

theorem squareWeave_single_body (markers : List Nat) (gap : List Nat) (nonempty : markers ≠ []) :
    squareWeave markers (List.replicate (markers.length - 1) [] ++ [gap]) =
      squareBody markers ++ gap := by
  induction markers with
  | nil => exact False.elim (nonempty rfl)
  | cons x rest ih =>
      cases rest with
      | nil =>
          change [x,x] ++ gap ++ [] = [x,x] ++ gap
          exact List.append_nil _
      | cons y ys =>
          have shift : (x :: y :: ys).length - 1 = (y :: ys).length - 1 + 1 := by
            simp only [List.length_cons]
            omega
          rw [shift,List.replicate_succ,List.cons_append]
          change [x,x] ++ [] ++ squareWeave (y :: ys)
              (List.replicate ((y :: ys).length - 1) [] ++ [gap]) =
            ([x,x] ++ squareBody (y :: ys)) ++ gap
          rw [List.append_nil,ih (by simp)]
          simp only [List.append_assoc]

def tileSquareSlots (tiles : List PowerTile) (gap : List Nat) : List (List Nat) :=
  List.replicate ((tileSquares tiles).length - 1) [] ++ [gap]

def bodySquareSlots : List BodyPiece → List (List Nat)
  | [] => []
  | (tiles,gap) :: rest => tileSquareSlots tiles gap ++ bodySquareSlots rest

theorem tileSquareSlots_length (original : List Nat) (tiles : List PowerTile) (gap : List Nat)
    (valid : BodyPieceValid original (tiles,gap)) (alpha : ¬ ∃ x, Unrestricted x original) :
    (tileSquareSlots tiles gap).length = (tileSquares tiles).length := by
  have nonempty := alphaTiles_squares_nonempty original tiles valid.2.1 valid.1 alpha
  have positive : 0 < (tileSquares tiles).length := by
    have notZero : (tileSquares tiles).length ≠ 0 :=
      fun zero => nonempty (List.length_eq_zero_iff.mp zero)
    omega
  simp only [tileSquareSlots,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
  omega

theorem bodySquareSlots_length (original : List Nat) (pieces : List BodyPiece)
    (good : BodyPiecesGood original pieces) (alpha : ¬ ∃ x, Unrestricted x original) :
    (bodySquareSlots pieces).length = (bodySquares pieces).length := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
      rcases piece with ⟨tiles,gap⟩
      have head := tileSquareSlots_length original tiles gap good.1 alpha
      have tail := ih good.2.2
      simp only [bodySquareSlots,bodySquares,List.length_append]
      rw [head,tail]

theorem bodySquareSlots_word (original : List Nat) (pieces : List BodyPiece)
    (good : BodyPiecesGood original pieces) (alpha : ¬ ∃ x, Unrestricted x original) :
    bodyPiecesWord pieces = squareWeave (bodySquares pieces) (bodySquareSlots pieces) := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
      rcases piece with ⟨tiles,gap⟩
      have length := tileSquareSlots_length original tiles gap good.1 alpha
      have headShape : squareWeave (tileSquares tiles) (tileSquareSlots tiles gap) =
          powerTileBody tiles ++ gap := by
        change squareWeave (tileSquares tiles)
          (List.replicate ((tileSquares tiles).length - 1) [] ++ [gap]) = powerTileBody tiles ++ gap
        rw [alphaPowerBody_eq original tiles good.1.2.1 alpha]
        exact squareWeave_single_body (tileSquares tiles) gap
          (alphaTiles_squares_nonempty original tiles good.1.2.1 good.1.1 alpha)
      change powerTileBody tiles ++ gap ++ bodyPiecesWord rest =
        squareWeave (tileSquares tiles ++ bodySquares rest) (tileSquareSlots tiles gap ++ bodySquareSlots rest)
      rw [squareWeave_append_exact _ _ _ _ length.symm,headShape]
      exact congrArg (fun tail : List Nat => powerTileBody tiles ++ gap ++ tail) (ih good.2.2)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.alphaTiles_eq_squareMap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.alphaTiles_squares_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.alphaPowerBody_eq
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.squareWeave_append_exact
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.squareWeave_single_body
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.tileSquareSlots_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodySquareSlots_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodySquareSlots_word

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
