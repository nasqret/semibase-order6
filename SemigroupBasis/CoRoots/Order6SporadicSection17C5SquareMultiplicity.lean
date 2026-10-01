import SemigroupBasis.CoRoots.Order6SporadicSection17C5BetaBodyNormalization

/-! The actual collected square list is exactly the restricted-letter set,
with multiplicity one proved from the semantic count-two invariant. No
deduplication of a square is used as an equational rewrite. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem powerTileBody_square_count_le (tiles : List PowerTile) (x : Nat) :
    2 * (tileSquares tiles).count x ≤ (powerTileBody tiles).count x := by
  induction tiles with
  | nil => simp [tileSquares,powerTileBody_nil]
  | cons tile rest ih =>
      cases tile with
      | square y =>
          by_cases equal : y = x
          · subst y
            simp only [tileSquares,powerTileBody_cons,powerTileWord,List.count_append,
              List.count_cons_self,List.count_nil]
            omega
          · simp only [tileSquares,powerTileBody_cons,powerTileWord,List.count_append,
              List.count_cons_of_ne equal,List.count_nil]
            omega
      | cube y =>
          simp only [tileSquares,powerTileBody_cons,powerTileWord,List.count_append]
          omega

theorem bodySquares_count_le (pieces : List BodyPiece) (x : Nat) :
    2 * (bodySquares pieces).count x ≤ (bodyPiecesWord pieces).count x := by
  induction pieces with
  | nil => simp [bodySquares,bodyPiecesWord]
  | cons piece rest ih =>
      rcases piece with ⟨tiles,gap⟩
      have head := powerTileBody_square_count_le tiles x
      simp only [bodySquares,bodyPiecesWord,List.count_append]
      omega

theorem bodyForm_square_count_le (form : BodyForm) (x : Nat) :
    2 * (bodySquares form.pieces).count x ≤ (bodyFormWord form).count x := by
  have body := bodySquares_count_le form.pieces x
  simp only [bodyFormWord,List.count_append]
  omega

theorem restricted_body_square_seed (original : List Nat) (x : Nat) (pieces : List BodyPiece)
    (good : BodyPiecesGood original pieces) (restricted : Restricted x original)
    (present : x ∈ bodyPiecesWord pieces) : x ∈ bodySquares pieces := by
  rcases (bodyPiecesWord_mem pieces x).mp present with ⟨piece,member,inBody | inGap⟩
  · have valid := good.pieceValid piece member
    rcases (powerTileBody_mem piece.1 x).mp inBody with square | cube
    · exact (bodySquares_mem pieces x).mpr ⟨piece,member,square⟩
    · have unrestricted : Unrestricted x original :=
        valid.2.1 (.cube x) ((tileCubes_mem piece.1 x).mp cube)
      exact False.elim (unrestricted.2.2 restricted)
  · have one := (good.pieceValid piece member).2.2 x inGap
    have two := restricted_count_two x original restricted
    omega

theorem populatedInputForm_square_iff (original : List Nat) (x : Nat) :
    x ∈ bodySquares (populatedInputForm original).pieces ↔ Restricted x original := by
  constructor
  · exact betaInputWord_squares_restricted original x
  · intro restricted
    have two := restricted_count_two x original restricted
    have member : x ∈ original := List.count_pos_iff.mp (by omega)
    have good := populatedInputForm_good original
    have same := Semantics.derives_sameEval false (populatedInputForm_derives original)
    have present := (same.mem x).mp member
    change x ∈ (populatedInputForm original).initial ++ bodyPiecesWord (populatedInputForm original).pieces at present
    rcases List.mem_append.mp present with initial | body
    · have one := good.1 x initial
      omega
    · exact restricted_body_square_seed original x (populatedInputForm original).pieces good.2 restricted body

theorem populatedInputForm_squares_nodup (original : List Nat) :
    (bodySquares (populatedInputForm original).pieces).Nodup := by
  apply List.nodup_iff_count.mpr
  intro x
  by_cases present : x ∈ bodySquares (populatedInputForm original).pieces
  · have restricted := (populatedInputForm_square_iff original x).mp present
    have same := Semantics.derives_sameEval false (populatedInputForm_derives original)
    have targetRestricted := same.restricted_forward x restricted
    have two := restricted_count_two x (bodyFormWord (populatedInputForm original)) targetRestricted
    have bound := bodyForm_square_count_le (populatedInputForm original) x
    omega
  · rw [List.count_eq_zero_of_not_mem present]
    omega

namespace Semantics

theorem SameEval.collectedSquares_perm {which : Bool} {left right : List Nat}
    (same : SameEval which left right) :
    (bodySquares (populatedInputForm left).pieces).Perm (bodySquares (populatedInputForm right).pieces) := by
  apply List.perm_iff_count.mpr
  intro x
  have membership : x ∈ bodySquares (populatedInputForm left).pieces ↔
      x ∈ bodySquares (populatedInputForm right).pieces :=
    (populatedInputForm_square_iff left x).trans
      ((same.restricted x).trans (populatedInputForm_square_iff right x).symm)
  simp only [(populatedInputForm_squares_nodup left).count,(populatedInputForm_squares_nodup right).count]
  by_cases present : x ∈ bodySquares (populatedInputForm left).pieces
  · rw [if_pos present,if_pos (membership.mp present)]
  · rw [if_neg present,if_neg (fun found => present (membership.mpr found))]

theorem SameEval.unrestrictedMarkers_perm {which : Bool} {left right : List Nat}
    (same : SameEval which left right) :
    (unrestrictedMarkers left).Perm (unrestrictedMarkers right) := by
  apply List.perm_iff_count.mpr
  intro x
  have membership : x ∈ unrestrictedMarkers left ↔ x ∈ unrestrictedMarkers right :=
    (unrestrictedMarkers_mem left x).trans
      ((same.unrestricted x).trans (unrestrictedMarkers_mem right x).symm)
  simp only [(unrestrictedMarkers_nodup left).count,(unrestrictedMarkers_nodup right).count]
  by_cases present : x ∈ unrestrictedMarkers left
  · rw [if_pos present,if_pos (membership.mp present)]
  · rw [if_neg present,if_neg (fun found => present (membership.mpr found))]

theorem SameEval.betaSquareWords_derives {which : Bool} {left right : List Nat}
    (same : SameEval which left right) :
    ListDerives (squareBody (bodySquares (populatedInputForm left).pieces))
      (squareBody (bodySquares (populatedInputForm right).pieces)) :=
  squareBody_perm same.collectedSquares_perm

theorem SameEval.betaCubeWords_derives {which : Bool} {left right : List Nat}
    (same : SameEval which left right) :
    ListDerives (cubeBody (unrestrictedMarkers left)) (cubeBody (unrestrictedMarkers right)) :=
  cubeBody_perm same.unrestrictedMarkers_perm

end Semantics

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_square_count_le
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodySquares_count_le
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyForm_square_count_le
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.restricted_body_square_seed
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedInputForm_square_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedInputForm_squares_nodup
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.collectedSquares_perm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.unrestrictedMarkers_perm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.betaSquareWords_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.betaCubeWords_derives

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
