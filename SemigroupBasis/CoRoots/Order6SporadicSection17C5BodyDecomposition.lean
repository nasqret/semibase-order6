import SemigroupBasis.CoRoots.Order6SporadicSection17C5InputTiling

/-! Computable maximal grouping of the input tiling. Each power body is
nonempty; internal simple gaps are nonempty. The actual initial and final
simple gaps may be empty. All classifications remain relative to the input. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

abbrev BodyPiece := List PowerTile × List Nat

structure BodyForm where
  initial : List Nat
  pieces : List BodyPiece
  deriving DecidableEq, Repr

def bodyPiecesWord : List BodyPiece → List Nat
  | [] => []
  | (tiles,gap) :: rest => powerTileBody tiles ++ gap ++ bodyPiecesWord rest

def bodyFormWord (form : BodyForm) : List Nat :=
  form.initial ++ bodyPiecesWord form.pieces

def prependCubicToken (token : CubicToken) (form : BodyForm) : BodyForm :=
  match token, form.initial, form.pieces with
  | .simple x, initial, pieces => ⟨x :: initial,pieces⟩
  | .power tile, [], [] => ⟨[],[([tile],[])]⟩
  | .power tile, [], (tiles,gap) :: rest => ⟨[],(tile :: tiles,gap) :: rest⟩
  | .power tile, x :: xs, pieces => ⟨[],([tile],x :: xs) :: pieces⟩

def tokenBodyForm : List CubicToken → BodyForm
  | [] => ⟨[],[]⟩
  | token :: rest => prependCubicToken token (tokenBodyForm rest)

theorem prependCubicToken_word (token : CubicToken) (form : BodyForm) :
    bodyFormWord (prependCubicToken token form) = cubicTokenWord token ++ bodyFormWord form := by
  rcases form with ⟨initial,pieces⟩
  cases token with
  | simple x => rfl
  | power tile =>
      cases initial with
      | nil =>
          cases pieces with
          | nil => simp [prependCubicToken,bodyFormWord,bodyPiecesWord,powerTileBody,cubicTokenWord]
          | cons piece rest =>
              rcases piece with ⟨tiles,gap⟩
              simp [prependCubicToken,bodyFormWord,bodyPiecesWord,powerTileBody,cubicTokenWord,List.append_assoc]
      | cons x xs =>
          simp [prependCubicToken,bodyFormWord,bodyPiecesWord,powerTileBody,cubicTokenWord,List.append_assoc]

theorem tokenBodyForm_word (tokens : List CubicToken) :
    bodyFormWord (tokenBodyForm tokens) = cubicTokenRender tokens := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      rw [tokenBodyForm,prependCubicToken_word,ih,cubicTokenRender_cons]

def BodyPieceValid (original : List Nat) (piece : BodyPiece) : Prop :=
  piece.1 ≠ [] ∧
    (∀ tile ∈ piece.1, CubicTokenValid original (.power tile)) ∧
    (∀ x ∈ piece.2, original.count x = 1)

def BodyPiecesGood (original : List Nat) : List BodyPiece → Prop
  | [] => True
  | piece :: rest => BodyPieceValid original piece ∧
      (rest ≠ [] → piece.2 ≠ []) ∧ BodyPiecesGood original rest

def BodyFormGood (original : List Nat) (form : BodyForm) : Prop :=
  (∀ x ∈ form.initial, original.count x = 1) ∧ BodyPiecesGood original form.pieces

theorem bodyPieceValid_singleton (original : List Nat) (tile : PowerTile) (gap : List Nat)
    (valid : CubicTokenValid original (.power tile))
    (gapValid : ∀ x ∈ gap, original.count x = 1) :
    BodyPieceValid original ([tile],gap) := by
  refine ⟨by simp,?_,gapValid⟩
  intro other member
  have equal : other = tile := by simpa only [List.mem_singleton] using member
  subst other
  exact valid

theorem bodyPieceValid_prepend (original : List Nat) (tile : PowerTile)
    (tiles : List PowerTile) (gap : List Nat)
    (valid : CubicTokenValid original (.power tile))
    (previous : BodyPieceValid original (tiles,gap)) :
    BodyPieceValid original (tile :: tiles,gap) := by
  refine ⟨by simp,?_,previous.2.2⟩
  intro other member
  rcases List.mem_cons.mp member with rfl | found
  · exact valid
  · exact previous.2.1 other found

theorem prependCubicToken_good (original : List Nat) (token : CubicToken) (form : BodyForm)
    (valid : CubicTokenValid original token) (good : BodyFormGood original form) :
    BodyFormGood original (prependCubicToken token form) := by
  rcases form with ⟨initial,pieces⟩
  cases token with
  | simple x =>
      change (∀ y ∈ x :: initial, original.count y = 1) ∧ BodyPiecesGood original pieces
      refine ⟨?_,good.2⟩
      intro y member
      rcases List.mem_cons.mp member with rfl | found
      · exact valid
      · exact good.1 y found
  | power tile =>
      cases initial with
      | nil =>
          cases pieces with
          | nil =>
              change (∀ x ∈ ([] : List Nat), original.count x = 1) ∧
                BodyPiecesGood original [([tile],[])]
              refine ⟨by simp,bodyPieceValid_singleton original tile [] valid (by simp),?_,True.intro⟩
              intro impossible
              exact False.elim (impossible rfl)
          | cons piece rest =>
              rcases piece with ⟨tiles,gap⟩
              change (∀ x ∈ ([] : List Nat), original.count x = 1) ∧
                BodyPiecesGood original ((tile :: tiles,gap) :: rest)
              have previous : BodyPiecesGood original ((tiles,gap) :: rest) := good.2
              exact ⟨by simp,bodyPieceValid_prepend original tile tiles gap valid previous.1,
                previous.2.1,previous.2.2⟩
      | cons x xs =>
          change (∀ y ∈ ([] : List Nat), original.count y = 1) ∧
            BodyPiecesGood original (([tile],x :: xs) :: pieces)
          refine ⟨by simp,bodyPieceValid_singleton original tile (x :: xs) valid good.1,?_,good.2⟩
          intro _
          simp

theorem tokenBodyForm_good (original : List Nat) (tokens : List CubicToken)
    (valid : ∀ token ∈ tokens, CubicTokenValid original token) :
    BodyFormGood original (tokenBodyForm tokens) := by
  induction tokens with
  | nil => simp [tokenBodyForm,BodyFormGood,BodyPiecesGood]
  | cons token rest ih =>
      have tail : ∀ other ∈ rest, CubicTokenValid original other :=
        fun other member => valid other (List.mem_cons_of_mem token member)
      exact prependCubicToken_good original token (tokenBodyForm rest)
        (valid token List.mem_cons_self) (ih tail)

theorem BodyPiecesGood.pieceValid {original : List Nat} {pieces : List BodyPiece}
    (good : BodyPiecesGood original pieces) :
    ∀ piece ∈ pieces, BodyPieceValid original piece := by
  induction pieces with
  | nil => intro piece member; cases member
  | cons first rest ih =>
      intro piece member
      rcases List.mem_cons.mp member with rfl | found
      · exact good.1
      · exact ih good.2.2 piece found

theorem bodyPiecesWord_append (left right : List BodyPiece) :
    bodyPiecesWord (left ++ right) = bodyPiecesWord left ++ bodyPiecesWord right := by
  induction left with
  | nil => rfl
  | cons piece rest ih =>
      rcases piece with ⟨tiles,gap⟩
      simp only [List.cons_append,bodyPiecesWord,ih,List.append_assoc]

def inputBodyForm (original : List Nat) : BodyForm :=
  tokenBodyForm (inputTokens original original)

theorem inputBodyForm_word (original : List Nat) :
    bodyFormWord (inputBodyForm original) = cubicForm original := by
  rw [inputBodyForm,tokenBodyForm_word,inputTokens_render]

theorem inputBodyForm_good (original : List Nat) : BodyFormGood original (inputBodyForm original) :=
  tokenBodyForm_good original (inputTokens original original) (inputTokens_valid original)

theorem inputBodyForm_derives (original : List Nat) :
    ListDerives original (bodyFormWord (inputBodyForm original)) := by
  rw [inputBodyForm_word]
  exact cubicForm_derives original

theorem inputBodyForm_power_bodies_nonempty (original : List Nat) :
    ∀ piece ∈ (inputBodyForm original).pieces, piece.1 ≠ [] := by
  intro piece member
  exact ((inputBodyForm_good original).2.pieceValid piece member).1

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.prependCubicToken_word
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.tokenBodyForm_word
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyPieceValid_singleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyPieceValid_prepend
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.prependCubicToken_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.tokenBodyForm_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.BodyPiecesGood.pieceValid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyPiecesWord_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.inputBodyForm_word
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.inputBodyForm_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.inputBodyForm_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.inputBodyForm_power_bodies_nonempty

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
