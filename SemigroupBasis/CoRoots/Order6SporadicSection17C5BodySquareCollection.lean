import SemigroupBasis.CoRoots.Order6SporadicSection17C5SquareCollection

/-! Collect all restricted-square tiles into the first actual power body.
The initial word and every intervening/terminal gap remain literally fixed.
All later bodies retain their original cube support and remain nonempty. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

def bodySquares : List BodyPiece → List Nat
  | [] => []
  | (tiles,_) :: rest => tileSquares tiles ++ bodySquares rest

def replaceBodySquares (x : Nat) : List BodyPiece → List BodyPiece
  | [] => []
  | (tiles,gap) :: rest => (replaceSquares x tiles,gap) :: replaceBodySquares x rest

theorem replaceBodySquares_nil_iff (x : Nat) (pieces : List BodyPiece) :
    replaceBodySquares x pieces = [] ↔ pieces = [] := by
  cases pieces with
  | nil => simp [replaceBodySquares]
  | cons piece rest => cases piece; simp [replaceBodySquares]

theorem bodySquares_mem (pieces : List BodyPiece) (y : Nat) :
    y ∈ bodySquares pieces ↔ ∃ piece ∈ pieces, y ∈ tileSquares piece.1 := by
  induction pieces with
  | nil => simp [bodySquares]
  | cons piece rest ih =>
      rcases piece with ⟨tiles,gap⟩
      constructor
      · intro member
        rcases List.mem_append.mp member with first | tail
        · exact ⟨(tiles,gap),List.mem_cons_self,first⟩
        · rcases ih.mp tail with ⟨piece,found,present⟩
          exact ⟨piece,List.mem_cons_of_mem (tiles,gap) found,present⟩
      · rintro ⟨piece,member,present⟩
        rcases List.mem_cons.mp member with rfl | found
        · exact List.mem_append.mpr (Or.inl present)
        · exact List.mem_append.mpr (Or.inr (ih.mpr ⟨piece,found,present⟩))

theorem bodySquares_restricted (original : List Nat) (pieces : List BodyPiece)
    (good : BodyPiecesGood original pieces) (y : Nat) (member : y ∈ bodySquares pieces) :
    Restricted y original := by
  rcases (bodySquares_mem pieces y).mp member with ⟨piece,found,present⟩
  exact (good.pieceValid piece found).2.1 (.square y) ((tileSquares_mem piece.1 y).mp present)

theorem replaceBodySquares_good (original : List Nat) (x : Nat) (pieces : List BodyPiece)
    (unrestricted : Unrestricted x original) (good : BodyPiecesGood original pieces) :
    BodyPiecesGood original (replaceBodySquares x pieces) := by
  induction pieces with
  | nil => exact True.intro
  | cons piece rest ih =>
      rcases piece with ⟨tiles,gap⟩
      refine ⟨⟨replaceSquares_nonempty x tiles good.1.1,
        replaceSquares_valid original x tiles unrestricted good.1.2.1,good.1.2.2⟩,?_,ih good.2.2⟩
      intro nonempty
      apply good.2.1
      intro empty
      exact nonempty ((replaceBodySquares_nil_iff x rest).mpr empty)

theorem replaceBodySquares_noSquares (x : Nat) (pieces : List BodyPiece) :
    bodySquares (replaceBodySquares x pieces) = [] := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
      rcases piece with ⟨tiles,gap⟩
      simp only [replaceBodySquares,bodySquares,replaceSquares_noSquares,ih,List.nil_append]

theorem replaceBodySquares_gaps (x : Nat) (pieces : List BodyPiece) :
    (replaceBodySquares x pieces).map Prod.snd = pieces.map Prod.snd := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
      rcases piece with ⟨tiles,gap⟩
      simp only [replaceBodySquares,List.map_cons,ih]

theorem replaceBodySquares_cubes (x : Nat) (pieces : List BodyPiece) (support : Nat → Prop)
    (seed : support x)
    (cubes : ∀ piece ∈ pieces, ∀ y, y ∈ tileCubes piece.1 ↔ support y) :
    ∀ piece ∈ replaceBodySquares x pieces, ∀ y, y ∈ tileCubes piece.1 ↔ support y := by
  induction pieces with
  | nil => intro piece member; cases member
  | cons first rest ih =>
      rcases first with ⟨tiles,gap⟩
      intro piece member y
      rcases List.mem_cons.mp member with rfl | found
      · have first := cubes (tiles,gap) List.mem_cons_self
        exact (replaceSquares_cube_iff x tiles ((first x).mpr seed) y).trans (first y)
      · exact ih (fun other present => cubes other (List.mem_cons_of_mem (tiles,gap) present)) piece found y

theorem collectBodySquares (x : Nat) (left : List PowerTile) (gap : List Nat)
    (pieces : List BodyPiece) (present : x ∈ tileCubes left) :
    ListDerives (powerTileBody left ++ gap ++ bodyPiecesWord pieces)
      (powerTileBody (left ++ (bodySquares pieces).map PowerTile.square) ++
        gap ++ bodyPiecesWord (replaceBodySquares x pieces)) := by
  induction pieces generalizing left gap with
  | nil =>
      simpa only [bodySquares,List.map_nil,List.append_nil,replaceBodySquares,bodyPiecesWord]
        using (S5_107.ListDerives.refl (powerTileBody left ++ gap) :
          ListDerives (powerTileBody left ++ gap) (powerTileBody left ++ gap))
  | cons piece rest ih =>
      rcases piece with ⟨tiles,after⟩
      have first : ListDerives
          (powerTileBody left ++ gap ++ bodyPiecesWord ((tiles,after) :: rest))
          (powerTileBody (left ++ (tileSquares tiles).map PowerTile.square) ++
            (gap ++ powerTileBody (replaceSquares x tiles) ++ after) ++ bodyPiecesWord rest) := by
        simpa only [bodyPiecesWord,List.append_assoc] using
          (collectRightSquares x left tiles gap present).append (after ++ bodyPiecesWord rest)
      have retained : x ∈ tileCubes (left ++ (tileSquares tiles).map PowerTile.square) := by
        simpa only [tileCubes_append,tileCubes_map_square,List.append_nil] using present
      have second := ih (left ++ (tileSquares tiles).map PowerTile.square)
        (gap ++ powerTileBody (replaceSquares x tiles) ++ after) retained
      simpa only [bodySquares,List.map_append,replaceBodySquares,bodyPiecesWord,List.append_assoc]
        using first.trans second

def collectFormSquares (x : Nat) (form : BodyForm) : BodyForm :=
  match form.pieces with
  | [] => form
  | (left,gap) :: rest =>
      ⟨form.initial,(left ++ (bodySquares rest).map PowerTile.square,gap) :: replaceBodySquares x rest⟩

theorem collectFormSquares_initial (x : Nat) (form : BodyForm) :
    (collectFormSquares x form).initial = form.initial := by
  rcases form with ⟨initial,pieces⟩
  cases pieces with
  | nil => rfl
  | cons piece rest => cases piece; rfl

theorem collectFormSquares_gaps (x : Nat) (form : BodyForm) :
    (collectFormSquares x form).pieces.map Prod.snd = form.pieces.map Prod.snd := by
  rcases form with ⟨initial,pieces⟩
  cases pieces with
  | nil => rfl
  | cons piece rest =>
      rcases piece with ⟨tiles,gap⟩
      simp only [collectFormSquares,List.map_cons,replaceBodySquares_gaps]

theorem collectFormSquares_derives (x : Nat) (form : BodyForm)
    (seed : ∀ piece ∈ form.pieces, x ∈ tileCubes piece.1) :
    ListDerives (bodyFormWord form) (bodyFormWord (collectFormSquares x form)) := by
  rcases form with ⟨initial,pieces⟩
  cases pieces with
  | nil => exact S5_107.ListDerives.refl _
  | cons piece rest =>
      rcases piece with ⟨tiles,gap⟩
      exact (collectBodySquares x tiles gap rest (seed (tiles,gap) List.mem_cons_self)).prepend initial

theorem collectFormSquares_good (original : List Nat) (x : Nat) (form : BodyForm)
    (unrestricted : Unrestricted x original) (good : BodyFormGood original form) :
    BodyFormGood original (collectFormSquares x form) := by
  rcases form with ⟨initial,pieces⟩
  cases pieces with
  | nil => exact good
  | cons piece rest =>
      rcases piece with ⟨tiles,gap⟩
      refine ⟨good.1,⟨?_,?_,good.2.1.2.2⟩,?_,
        replaceBodySquares_good original x rest unrestricted good.2.2.2⟩
      · intro empty
        cases tiles with
        | nil => exact good.2.1.1 rfl
        | cons tile tail => cases empty
      · intro tile member
        rcases List.mem_append.mp member with old | moved
        · exact good.2.1.2.1 tile old
        · rcases List.mem_map.mp moved with ⟨y,found,equal⟩
          subst tile
          exact bodySquares_restricted original rest good.2.2.2 y found
      · intro nonempty
        apply good.2.2.1
        intro empty
        exact nonempty ((replaceBodySquares_nil_iff x rest).mpr empty)

theorem collectFormSquares_cubes (x : Nat) (form : BodyForm) (support : Nat → Prop)
    (seed : support x)
    (cubes : ∀ piece ∈ form.pieces, ∀ y, y ∈ tileCubes piece.1 ↔ support y) :
    ∀ piece ∈ (collectFormSquares x form).pieces, ∀ y, y ∈ tileCubes piece.1 ↔ support y := by
  rcases form with ⟨initial,pieces⟩
  cases pieces with
  | nil => exact cubes
  | cons first rest =>
      rcases first with ⟨tiles,gap⟩
      intro piece member y
      rcases List.mem_cons.mp member with rfl | found
      · simpa only [tileCubes_append,tileCubes_map_square,List.append_nil] using
          cubes (tiles,gap) List.mem_cons_self y
      · exact replaceBodySquares_cubes x rest support seed
          (fun other present => cubes other (List.mem_cons_of_mem (tiles,gap) present)) piece found y

theorem collectFormSquares_allSquares (x : Nat) (form : BodyForm) :
    bodySquares (collectFormSquares x form).pieces = bodySquares form.pieces := by
  rcases form with ⟨initial,pieces⟩
  cases pieces with
  | nil => rfl
  | cons piece rest =>
      rcases piece with ⟨tiles,gap⟩
      simp only [collectFormSquares,bodySquares,tileSquares_append,tileSquares_map_square,
        replaceBodySquares_noSquares,List.append_nil]

def collectedInputForm (original : List Nat) (x : Nat) : BodyForm :=
  collectFormSquares x (populatedInputForm original)

theorem collectedInputForm_derives (original : List Nat) (x : Nat) (unrestricted : Unrestricted x original) :
    ListDerives original (bodyFormWord (collectedInputForm original x)) :=
  (populatedInputForm_derives original).trans
    (collectFormSquares_derives x (populatedInputForm original)
      (fun piece member => (populatedInputForm_cube_iff original piece member x).mpr unrestricted))

theorem collectedInputForm_good (original : List Nat) (x : Nat) (unrestricted : Unrestricted x original) :
    BodyFormGood original (collectedInputForm original x) :=
  collectFormSquares_good original x (populatedInputForm original) unrestricted (populatedInputForm_good original)

theorem collectedInputForm_cube_iff (original : List Nat) (x : Nat) (unrestricted : Unrestricted x original) :
    ∀ piece ∈ (collectedInputForm original x).pieces, ∀ y, y ∈ tileCubes piece.1 ↔ Unrestricted y original :=
  collectFormSquares_cubes x (populatedInputForm original) (fun y => Unrestricted y original) unrestricted
    (populatedInputForm_cube_iff original)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.replaceBodySquares_nil_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodySquares_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodySquares_restricted
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.replaceBodySquares_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.replaceBodySquares_noSquares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.replaceBodySquares_gaps
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.replaceBodySquares_cubes
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.collectBodySquares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.collectFormSquares_initial
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.collectFormSquares_gaps
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.collectFormSquares_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.collectFormSquares_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.collectFormSquares_cubes
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.collectFormSquares_allSquares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.collectedInputForm_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.collectedInputForm_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.collectedInputForm_cube_iff

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
