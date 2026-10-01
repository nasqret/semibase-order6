import SemigroupBasis.CoRoots.Order6SporadicSection17C5BodySquareCollection

/-! Construct the beta presentation from the actual arbitrary input. All
restricted-square multiplicities occur in the initial power body and every
power body has the same nonempty unrestricted-cube word. Simple gaps are
unchanged; their comparison and the alpha case are separate obligations. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

def uniformBodyWord (body : List Nat) : List (List Nat) → List Nat
  | [] => []
  | gap :: rest => body ++ gap ++ uniformBodyWord body rest

theorem powerTileBody_markers_normalize (tiles : List PowerTile) (markers : List Nat)
    (same : ∀ y, y ∈ tileCubes tiles ↔ y ∈ markers) :
    ListDerives (powerTileBody tiles) (squareBody (tileSquares tiles) ++ cubeBody markers) :=
  (powerTileBody_split tiles).trans ((cubeBody_sameContent same).prepend (squareBody (tileSquares tiles)))

theorem powerTileBody_cube_normalize (tiles : List PowerTile) (markers : List Nat)
    (noSquares : tileSquares tiles = []) (same : ∀ y, y ∈ tileCubes tiles ↔ y ∈ markers) :
    ListDerives (powerTileBody tiles) (cubeBody markers) := by
  simpa only [noSquares,squareBody,List.nil_append] using powerTileBody_markers_normalize tiles markers same

theorem replaceBodySquares_piece_noSquares (x : Nat) (pieces : List BodyPiece) :
    ∀ piece ∈ replaceBodySquares x pieces, tileSquares piece.1 = [] := by
  induction pieces with
  | nil => intro piece member; cases member
  | cons first rest ih =>
      rcases first with ⟨tiles,gap⟩
      intro piece member
      rcases List.mem_cons.mp member with rfl | found
      · exact replaceSquares_noSquares x tiles
      · exact ih piece found

theorem bodyPiecesWord_cube_normalize (pieces : List BodyPiece) (markers : List Nat)
    (noSquares : ∀ piece ∈ pieces, tileSquares piece.1 = [])
    (same : ∀ piece ∈ pieces, ∀ y, y ∈ tileCubes piece.1 ↔ y ∈ markers) :
    ListDerives (bodyPiecesWord pieces) (uniformBodyWord (cubeBody markers) (pieces.map Prod.snd)) := by
  induction pieces with
  | nil => exact S5_107.ListDerives.refl _
  | cons first rest ih =>
      rcases first with ⟨tiles,gap⟩
      have head := powerTileBody_cube_normalize tiles markers
        (noSquares (tiles,gap) List.mem_cons_self) (same (tiles,gap) List.mem_cons_self)
      have tail := ih (fun piece member => noSquares piece (List.mem_cons_of_mem (tiles,gap) member))
        (fun piece member => same piece (List.mem_cons_of_mem (tiles,gap) member))
      have firstStep : ListDerives (powerTileBody tiles ++ gap ++ bodyPiecesWord rest)
          (cubeBody markers ++ gap ++ bodyPiecesWord rest) := by
        simpa only [List.append_assoc] using head.append (gap ++ bodyPiecesWord rest)
      have secondStep := tail.prepend (cubeBody markers ++ gap)
      simpa only [bodyPiecesWord,List.map_cons,uniformBodyWord,List.append_assoc]
        using firstStep.trans secondStep

theorem collectFormSquares_beta_normalize (x : Nat) (form : BodyForm) (markers : List Nat)
    (seed : x ∈ markers)
    (same : ∀ piece ∈ form.pieces, ∀ y, y ∈ tileCubes piece.1 ↔ y ∈ markers) :
    ListDerives (bodyFormWord (collectFormSquares x form))
      (form.initial ++ squareBody (bodySquares form.pieces) ++
        uniformBodyWord (cubeBody markers) (form.pieces.map Prod.snd)) := by
  rcases form with ⟨initial,pieces⟩
  cases pieces with
  | nil =>
      simpa only [collectFormSquares,bodyFormWord,bodyPiecesWord,bodySquares,squareBody,
        List.map_nil,uniformBodyWord,List.append_nil] using
        (S5_107.ListDerives.refl initial : ListDerives initial initial)
  | cons first rest =>
      rcases first with ⟨tiles,gap⟩
      have headSame : ∀ y, y ∈ tileCubes (tiles ++ (bodySquares rest).map PowerTile.square) ↔ y ∈ markers := by
        intro y
        simpa only [tileCubes_append,tileCubes_map_square,List.append_nil] using same (tiles,gap) List.mem_cons_self y
      have head := powerTileBody_markers_normalize
        (tiles ++ (bodySquares rest).map PowerTile.square) markers headSame
      rw [tileSquares_append,tileSquares_map_square] at head
      have tailSame := replaceBodySquares_cubes x rest (fun y => y ∈ markers) seed
        (fun piece member => same piece (List.mem_cons_of_mem (tiles,gap) member))
      have tail := bodyPiecesWord_cube_normalize (replaceBodySquares x rest) markers
        (replaceBodySquares_piece_noSquares x rest) tailSame
      rw [replaceBodySquares_gaps] at tail
      have firstStep : ListDerives
          (powerTileBody (tiles ++ (bodySquares rest).map PowerTile.square) ++
            gap ++ bodyPiecesWord (replaceBodySquares x rest))
          (squareBody (bodySquares ((tiles,gap) :: rest)) ++ cubeBody markers ++
            gap ++ bodyPiecesWord (replaceBodySquares x rest)) := by
        simpa only [bodySquares,List.append_assoc] using head.append (gap ++ bodyPiecesWord (replaceBodySquares x rest))
      have secondStep := tail.prepend (squareBody (bodySquares ((tiles,gap) :: rest)) ++ cubeBody markers ++ gap)
      simpa only [collectFormSquares,bodyFormWord,bodyPiecesWord,List.map_cons,uniformBodyWord,List.append_assoc]
        using (firstStep.trans secondStep).prepend initial

theorem bodyForm_beta_normalize (x : Nat) (form : BodyForm) (markers : List Nat)
    (seed : x ∈ markers)
    (same : ∀ piece ∈ form.pieces, ∀ y, y ∈ tileCubes piece.1 ↔ y ∈ markers) :
    ListDerives (bodyFormWord form)
      (form.initial ++ squareBody (bodySquares form.pieces) ++
        uniformBodyWord (cubeBody markers) (form.pieces.map Prod.snd)) :=
  (collectFormSquares_derives x form (fun piece member => (same piece member x).mpr seed)).trans
    (collectFormSquares_beta_normalize x form markers seed same)

def betaInputWord (original : List Nat) : List Nat :=
  let form := populatedInputForm original
  form.initial ++ squareBody (bodySquares form.pieces) ++
    uniformBodyWord (cubeBody (unrestrictedMarkers original)) (form.pieces.map Prod.snd)

theorem betaInputWord_derives (original : List Nat) (beta : ∃ x, Unrestricted x original) :
    ListDerives original (betaInputWord original) := by
  rcases beta with ⟨x,unrestricted⟩
  have same : ∀ piece ∈ (populatedInputForm original).pieces, ∀ y,
      y ∈ tileCubes piece.1 ↔ y ∈ unrestrictedMarkers original := by
    intro piece member y
    exact (populatedInputForm_cube_iff original piece member y).trans (unrestrictedMarkers_mem original y).symm
  exact (populatedInputForm_derives original).trans
    (bodyForm_beta_normalize x (populatedInputForm original) (unrestrictedMarkers original)
      ((unrestrictedMarkers_mem original x).mpr unrestricted) same)

theorem populatedInputForm_pieces_nonempty (original : List Nat) (beta : ∃ x, Unrestricted x original) :
    (populatedInputForm original).pieces ≠ [] := by
  rcases beta with ⟨x,unrestricted⟩
  intro empty
  have same := Semantics.derives_sameEval false (populatedInputForm_derives original)
  have present := (same.mem x).mp unrestricted.1
  have initial : x ∈ (populatedInputForm original).initial := by
    simpa only [bodyFormWord,empty,bodyPiecesWord,List.append_nil] using present
  exact unrestricted.2.1 ((populatedInputForm_good original).1 x initial)

theorem betaInputWord_common_cube_nonempty (original : List Nat) (beta : ∃ x, Unrestricted x original) :
    cubeBody (unrestrictedMarkers original) ≠ [] :=
  inputCommonCubeBody_nonempty original beta

theorem betaInputWord_initial_simple (original : List Nat) :
    ∀ x ∈ (populatedInputForm original).initial, original.count x = 1 :=
  (populatedInputForm_good original).1

theorem betaInputWord_gaps_simple (original : List Nat) :
    ∀ gap ∈ (populatedInputForm original).pieces.map Prod.snd,
      ∀ x ∈ gap, original.count x = 1 := by
  intro gap member
  rcases List.mem_map.mp member with ⟨piece,found,equal⟩
  subst gap
  exact ((populatedInputForm_good original).2.pieceValid piece found).2.2

theorem betaInputWord_squares_restricted (original : List Nat) :
    ∀ x ∈ bodySquares (populatedInputForm original).pieces, Restricted x original :=
  bodySquares_restricted original (populatedInputForm original).pieces (populatedInputForm_good original).2

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_markers_normalize
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_cube_normalize
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.replaceBodySquares_piece_noSquares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyPiecesWord_cube_normalize
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.collectFormSquares_beta_normalize
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyForm_beta_normalize
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.betaInputWord_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedInputForm_pieces_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.betaInputWord_common_cube_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.betaInputWord_initial_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.betaInputWord_gaps_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.betaInputWord_squares_restricted

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
