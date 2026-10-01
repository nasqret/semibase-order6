import SemigroupBasis.CoRoots.Order6SporadicSection17C5CubePopulation

/-! Discharge the population seed hypotheses from the ACTUAL arbitrary
input, and prove that every resulting body has exactly the global cube
support. No existential seed or completeness assumption is left to callers. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem powerTileBody_mem (tiles : List PowerTile) (x : Nat) :
    x ∈ powerTileBody tiles ↔ x ∈ tileSquares tiles ∨ x ∈ tileCubes tiles := by
  induction tiles with
  | nil => simp [powerTileBody,tileSquares,tileCubes]
  | cons tile rest ih =>
      cases tile with
      | square y =>
          change x ∈ [y,y] ++ powerTileBody rest ↔ x ∈ y :: tileSquares rest ∨ x ∈ tileCubes rest
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_self,ih,or_assoc]
      | cube y =>
          change x ∈ [y,y,y] ++ powerTileBody rest ↔ x ∈ tileSquares rest ∨ x ∈ y :: tileCubes rest
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,false_or,or_self,ih,or_assoc,or_left_comm,or_comm]

theorem bodyPiecesWord_mem (pieces : List BodyPiece) (x : Nat) :
    x ∈ bodyPiecesWord pieces ↔
      ∃ piece ∈ pieces, x ∈ powerTileBody piece.1 ∨ x ∈ piece.2 := by
  induction pieces with
  | nil => simp [bodyPiecesWord]
  | cons first rest ih =>
      rcases first with ⟨tiles,gap⟩
      constructor
      · intro member
        rcases List.mem_append.mp member with firstMember | restMember
        · exact ⟨(tiles,gap),List.mem_cons_self,List.mem_append.mp firstMember⟩
        · rcases ih.mp restMember with ⟨piece,found,present⟩
          exact ⟨piece,List.mem_cons_of_mem (tiles,gap) found,present⟩
      · rintro ⟨piece,member,present⟩
        rcases List.mem_cons.mp member with rfl | found
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr present))
        · exact List.mem_append.mpr (Or.inr (ih.mpr ⟨piece,found,present⟩))

theorem unrestricted_body_seed (original : List Nat) (x : Nat) (pieces : List BodyPiece)
    (good : BodyPiecesGood original pieces) (unrestricted : Unrestricted x original)
    (present : x ∈ bodyPiecesWord pieces) :
    ∃ piece ∈ pieces, x ∈ tileCubes piece.1 := by
  rcases (bodyPiecesWord_mem pieces x).mp present with ⟨piece,member,inBody | inGap⟩
  · have valid := good.pieceValid piece member
    rcases (powerTileBody_mem piece.1 x).mp inBody with square | cube
    · have restricted : Restricted x original :=
        valid.2.1 (.square x) ((tileSquares_mem piece.1 x).mp square)
      exact False.elim (unrestricted.2.2 restricted)
    · exact ⟨piece,member,cube⟩
  · have one : original.count x = 1 := (good.pieceValid piece member).2.2 x inGap
    exact False.elim (unrestricted.2.1 one)

theorem inputBodyForm_cube_seed (original : List Nat) (x : Nat)
    (unrestricted : Unrestricted x original) :
    ∃ piece ∈ (inputBodyForm original).pieces, x ∈ tileCubes piece.1 := by
  have good := inputBodyForm_good original
  have same := Semantics.derives_sameEval false (inputBodyForm_derives original)
  have present := (same.mem x).mp unrestricted.1
  change x ∈ (inputBodyForm original).initial ++ bodyPiecesWord (inputBodyForm original).pieces at present
  rcases List.mem_append.mp present with initial | body
  · exact False.elim (unrestricted.2.1 (good.1 x initial))
  · exact unrestricted_body_seed original x (inputBodyForm original).pieces good.2 unrestricted body

theorem populateCube_preserves_all (insert marker : Nat) (pieces : List BodyPiece)
    (all : ∀ piece ∈ pieces, marker ∈ tileCubes piece.1) :
    ∀ piece ∈ populateCube insert pieces, marker ∈ tileCubes piece.1 := by
  induction pieces with
  | nil => intro piece member; cases member
  | cons first rest ih =>
      rcases first with ⟨tiles,gap⟩
      intro piece member
      rcases List.mem_cons.mp member with rfl | found
      · change marker ∈ tileCubes (tiles ++ [.cube insert])
        rw [tileCubes_append]
        exact List.mem_append.mpr (Or.inl (all (tiles,gap) List.mem_cons_self))
      · have tail : ∀ other ∈ rest, marker ∈ tileCubes other.1 :=
          fun other member => all other (List.mem_cons_of_mem (tiles,gap) member)
        exact ih tail piece found

theorem populateCubes_preserves_all (markers : List Nat) (marker : Nat) (pieces : List BodyPiece)
    (all : ∀ piece ∈ pieces, marker ∈ tileCubes piece.1) :
    ∀ piece ∈ populateCubes markers pieces, marker ∈ tileCubes piece.1 := by
  induction markers generalizing pieces with
  | nil => exact all
  | cons insert rest ih =>
      exact ih (populateCube insert pieces) (populateCube_preserves_all insert marker pieces all)

theorem populateCubes_all (markers : List Nat) (pieces : List BodyPiece) :
    ∀ marker ∈ markers, ∀ piece ∈ populateCubes markers pieces, marker ∈ tileCubes piece.1 := by
  induction markers generalizing pieces with
  | nil => intro marker member; cases member
  | cons first rest ih =>
      intro marker member
      rcases List.mem_cons.mp member with equal | found
      · subst marker
        exact populateCubes_preserves_all rest first (populateCube first pieces) (populateCube_all first pieces)
      · exact ih (populateCube first pieces) marker found

def populatedInputForm (original : List Nat) : BodyForm :=
  let form := inputBodyForm original
  ⟨form.initial,populateCubes (unrestrictedMarkers original) form.pieces⟩

theorem populatedInputForm_good (original : List Nat) : BodyFormGood original (populatedInputForm original) := by
  have good := inputBodyForm_good original
  refine ⟨good.1,?_⟩
  exact populateCubes_good original (unrestrictedMarkers original) (inputBodyForm original).pieces
    (fun x member => (unrestrictedMarkers_mem original x).mp member) good.2

theorem populatedInputForm_derives (original : List Nat) :
    ListDerives original (bodyFormWord (populatedInputForm original)) := by
  have good := inputBodyForm_good original
  have population := populateCubes_sound original (unrestrictedMarkers original) (inputBodyForm original).pieces
    (fun x member => (unrestrictedMarkers_mem original x).mp member) good.2
    (fun x member => inputBodyForm_cube_seed original x ((unrestrictedMarkers_mem original x).mp member))
  exact (inputBodyForm_derives original).trans (population.prepend (inputBodyForm original).initial)

theorem populatedInputForm_cube_iff (original : List Nat) (piece : BodyPiece)
    (member : piece ∈ (populatedInputForm original).pieces) (x : Nat) :
    x ∈ tileCubes piece.1 ↔ Unrestricted x original := by
  constructor
  · intro present
    have valid := (populatedInputForm_good original).2.pieceValid piece member
    exact valid.2.1 (.cube x) ((tileCubes_mem piece.1 x).mp present)
  · intro unrestricted
    exact populateCubes_all (unrestrictedMarkers original) (inputBodyForm original).pieces x
      ((unrestrictedMarkers_mem original x).mpr unrestricted) piece member

theorem populatedInputForm_cubes_nonempty (original : List Nat)
    (beta : ∃ x, Unrestricted x original) (piece : BodyPiece)
    (member : piece ∈ (populatedInputForm original).pieces) : tileCubes piece.1 ≠ [] := by
  rcases beta with ⟨x,unrestricted⟩
  have present := (populatedInputForm_cube_iff original piece member x).mpr unrestricted
  intro empty
  rw [empty] at present
  cases present

theorem inputCommonCubeBody_nonempty (original : List Nat) (beta : ∃ x, Unrestricted x original) :
    cubeBody (unrestrictedMarkers original) ≠ [] := by
  apply cubeBody_nonempty
  rcases beta with ⟨x,unrestricted⟩
  have present := (unrestrictedMarkers_mem original x).mpr unrestricted
  intro empty
  rw [empty] at present
  cases present

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyPiecesWord_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.unrestricted_body_seed
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.inputBodyForm_cube_seed
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populateCube_preserves_all
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populateCubes_preserves_all
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populateCubes_all
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedInputForm_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedInputForm_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedInputForm_cube_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedInputForm_cubes_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.inputCommonCubeBody_nonempty

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
