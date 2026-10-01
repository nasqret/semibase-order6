import SemigroupBasis.CoRoots.Order6SporadicSection17C5CubePropagation

/-! Copy a seeded cube into every body, from an arbitrary seed position.
Then iterate over any finite list of globally unrestricted markers. Gaps,
all original tiles, and nonempty bodies are preserved throughout. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

def populateCube (x : Nat) : List BodyPiece → List BodyPiece
  | [] => []
  | (tiles,gap) :: rest => (tiles ++ [.cube x],gap) :: populateCube x rest

theorem cube_mem_adjoined (x : Nat) (tiles : List PowerTile) :
    x ∈ tileCubes (tiles ++ [.cube x]) := by
  rw [tileCubes_append]
  exact List.mem_append.mpr (Or.inr (by simp [tileCubes]))

theorem populateCube_piece_mem (x : Nat) (piece : BodyPiece) (pieces : List BodyPiece)
    (member : piece ∈ pieces) :
    (piece.1 ++ [.cube x],piece.2) ∈ populateCube x pieces := by
  induction pieces with
  | nil => cases member
  | cons first rest ih =>
      rcases first with ⟨tiles,gap⟩
      rcases List.mem_cons.mp member with rfl | found
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih found)

theorem populateCube_all (x : Nat) (pieces : List BodyPiece) :
    ∀ piece ∈ populateCube x pieces, x ∈ tileCubes piece.1 := by
  induction pieces with
  | nil => intro piece member; cases member
  | cons first rest ih =>
      rcases first with ⟨tiles,gap⟩
      intro piece member
      rcases List.mem_cons.mp member with rfl | found
      · exact cube_mem_adjoined x tiles
      · exact ih piece found

theorem populateCube_good (original : List Nat) (x : Nat) (pieces : List BodyPiece)
    (unrestricted : Unrestricted x original) (good : BodyPiecesGood original pieces) :
    BodyPiecesGood original (populateCube x pieces) := by
  induction pieces with
  | nil => exact True.intro
  | cons first rest ih =>
      rcases first with ⟨tiles,gap⟩
      change BodyPieceValid original (tiles ++ [.cube x],gap) ∧
        (populateCube x rest ≠ [] → gap ≠ []) ∧ BodyPiecesGood original (populateCube x rest)
      refine ⟨⟨by simp,?_,good.1.2.2⟩,?_,ih good.2.2⟩
      · intro tile member
        rcases List.mem_append.mp member with old | new
        · exact good.1.2.1 tile old
        · have equal : tile = .cube x := by simpa only [List.mem_singleton] using new
          subst tile
          exact unrestricted
      · intro nonempty
        apply good.2.1
        intro empty
        subst rest
        exact nonempty rfl

theorem populateCube_forward (original : List Nat) (x : Nat) :
    ∀ pieces : List BodyPiece, BodyPiecesGood original pieces →
    ∀ (left : List PowerTile) (gap : List Nat), x ∈ tileCubes left →
      (pieces ≠ [] → gap ≠ []) →
      ListDerives (powerTileBody left ++ gap ++ bodyPiecesWord pieces)
        (powerTileBody left ++ gap ++ bodyPiecesWord (populateCube x pieces)) := by
  intro pieces
  induction pieces with
  | nil =>
      intro good left gap present separated
      exact S5_107.ListDerives.refl _
  | cons first rest ih =>
      rcases first with ⟨tiles,nextGap⟩
      intro good left gap present separated
      have gapNonempty : gap ≠ [] := separated (by simp)
      have firstStep : ListDerives
          (powerTileBody left ++ gap ++ bodyPiecesWord ((tiles,nextGap) :: rest))
          (powerTileBody left ++ gap ++
            (powerTileBody (tiles ++ [.cube x]) ++ nextGap ++ bodyPiecesWord rest)) := by
        simpa only [bodyPiecesWord,List.append_assoc] using
          (propagateCubeRight x left tiles gap present gapNonempty good.1.1).append
            (nextGap ++ bodyPiecesWord rest)
      have continuation := ih good.2.2 (tiles ++ [.cube x]) nextGap
        (cube_mem_adjoined x tiles) good.2.1
      have secondStep : ListDerives
          (powerTileBody left ++ gap ++
            (powerTileBody (tiles ++ [.cube x]) ++ nextGap ++ bodyPiecesWord rest))
          (powerTileBody left ++ gap ++ bodyPiecesWord (populateCube x ((tiles,nextGap) :: rest))) := by
        simpa only [populateCube,bodyPiecesWord,List.append_assoc] using
          continuation.prepend (powerTileBody left ++ gap)
      exact firstStep.trans secondStep

theorem populateCube_sound (original : List Nat) (x : Nat) :
    ∀ pieces : List BodyPiece, BodyPiecesGood original pieces →
      (∃ piece ∈ pieces, x ∈ tileCubes piece.1) →
      ListDerives (bodyPiecesWord pieces) (bodyPiecesWord (populateCube x pieces)) := by
  intro pieces
  induction pieces with
  | nil =>
      rintro good ⟨piece,member,_⟩
      cases member
  | cons first rest ih =>
      rcases first with ⟨tiles,gap⟩
      intro good seed
      by_cases present : x ∈ tileCubes tiles
      · have firstStep : ListDerives (bodyPiecesWord ((tiles,gap) :: rest))
            (powerTileBody (tiles ++ [.cube x]) ++ gap ++ bodyPiecesWord rest) := by
          rw [powerTileBody_append]
          simpa only [bodyPiecesWord,List.append_assoc] using
            (powerTileBody_duplicate_right tiles x present).append (gap ++ bodyPiecesWord rest)
        have secondStep := populateCube_forward original x rest good.2.2
          (tiles ++ [.cube x]) gap (cube_mem_adjoined x tiles) good.2.1
        simpa only [populateCube,bodyPiecesWord] using firstStep.trans secondStep
      · have tailSeed : ∃ piece ∈ rest, x ∈ tileCubes piece.1 := by
          rcases seed with ⟨piece,member,found⟩
          rcases List.mem_cons.mp member with rfl | tailMember
          · exact False.elim (present found)
          · exact ⟨piece,tailMember,found⟩
        cases rest with
        | nil =>
            rcases tailSeed with ⟨piece,member,_⟩
            cases member
        | cons next remaining =>
            rcases next with ⟨right,nextGap⟩
            have tailDerivation := ih good.2.2 tailSeed
            have firstStep : ListDerives
                (bodyPiecesWord ((tiles,gap) :: (right,nextGap) :: remaining))
                (powerTileBody tiles ++ gap ++
                  (powerTileBody (right ++ [.cube x]) ++ nextGap ++ bodyPiecesWord (populateCube x remaining))) := by
              simpa only [bodyPiecesWord,populateCube,List.append_assoc] using
                tailDerivation.prepend (powerTileBody tiles ++ gap)
            have gapNonempty : gap ≠ [] := good.2.1 (by simp)
            have secondStep : ListDerives
                (powerTileBody tiles ++ gap ++
                  (powerTileBody (right ++ [.cube x]) ++ nextGap ++ bodyPiecesWord (populateCube x remaining)))
                (bodyPiecesWord (populateCube x ((tiles,gap) :: (right,nextGap) :: remaining))) := by
              simpa only [bodyPiecesWord,populateCube,List.append_assoc] using
                (propagateCubeLeft x tiles (right ++ [.cube x]) gap
                  (cube_mem_adjoined x right) gapNonempty good.1.1).append
                    (nextGap ++ bodyPiecesWord (populateCube x remaining))
            exact firstStep.trans secondStep

theorem populateCube_seed_preserved (x y : Nat) (pieces : List BodyPiece)
    (seed : ∃ piece ∈ pieces, y ∈ tileCubes piece.1) :
    ∃ piece ∈ populateCube x pieces, y ∈ tileCubes piece.1 := by
  rcases seed with ⟨⟨tiles,gap⟩,member,present⟩
  refine ⟨(tiles ++ [.cube x],gap),populateCube_piece_mem x (tiles,gap) pieces member,?_⟩
  change y ∈ tileCubes (tiles ++ [.cube x])
  rw [tileCubes_append]
  exact List.mem_append.mpr (Or.inl present)

def populateCubes : List Nat → List BodyPiece → List BodyPiece
  | [], pieces => pieces
  | x :: xs, pieces => populateCubes xs (populateCube x pieces)

theorem populateCubes_good (original : List Nat) (markers : List Nat) (pieces : List BodyPiece)
    (unrestricted : ∀ x ∈ markers, Unrestricted x original)
    (good : BodyPiecesGood original pieces) :
    BodyPiecesGood original (populateCubes markers pieces) := by
  induction markers generalizing pieces with
  | nil => exact good
  | cons x xs ih =>
      have tailUnrestricted : ∀ y ∈ xs, Unrestricted y original :=
        fun y member => unrestricted y (List.mem_cons_of_mem x member)
      exact ih (populateCube x pieces) tailUnrestricted
        (populateCube_good original x pieces (unrestricted x List.mem_cons_self) good)

theorem populateCubes_sound (original : List Nat) (markers : List Nat) (pieces : List BodyPiece)
    (unrestricted : ∀ x ∈ markers, Unrestricted x original)
    (good : BodyPiecesGood original pieces)
    (seeds : ∀ x ∈ markers, ∃ piece ∈ pieces, x ∈ tileCubes piece.1) :
    ListDerives (bodyPiecesWord pieces) (bodyPiecesWord (populateCubes markers pieces)) := by
  induction markers generalizing pieces with
  | nil => exact S5_107.ListDerives.refl _
  | cons x xs ih =>
      have headUnrestricted := unrestricted x List.mem_cons_self
      have tailUnrestricted : ∀ y ∈ xs, Unrestricted y original :=
        fun y member => unrestricted y (List.mem_cons_of_mem x member)
      have nextGood := populateCube_good original x pieces headUnrestricted good
      have laterSeeds : ∀ y ∈ xs, ∃ piece ∈ populateCube x pieces, y ∈ tileCubes piece.1 := by
        intro y member
        exact populateCube_seed_preserved x y pieces (seeds y (List.mem_cons_of_mem x member))
      have first := populateCube_sound original x pieces good (seeds x List.mem_cons_self)
      have second := ih (populateCube x pieces) tailUnrestricted nextGood laterSeeds
      exact first.trans second

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cube_mem_adjoined
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populateCube_piece_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populateCube_all
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populateCube_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populateCube_forward
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populateCube_sound
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populateCube_seed_preserved
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populateCubes_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populateCubes_sound

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
