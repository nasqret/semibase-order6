import SemigroupBasis.CoRoots.Order6SporadicSection17C5InputCubePopulation

/-! Move all squares from a remote power body into a body containing a cube.
The remote squares are replaced by copies of that existing cube. Square
multiplicities are retained exactly; the arbitrary intervening word is fixed. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem powerTileBody_nil : powerTileBody [] = [] := rfl

theorem powerTileBody_cons (tile : PowerTile) (rest : List PowerTile) :
    powerTileBody (tile :: rest) = powerTileWord tile ++ powerTileBody rest := rfl

def replaceSquares (x : Nat) : List PowerTile → List PowerTile
  | [] => []
  | .square _ :: rest => .cube x :: replaceSquares x rest
  | .cube y :: rest => .cube y :: replaceSquares x rest

theorem replaceSquares_length (x : Nat) (tiles : List PowerTile) :
    (replaceSquares x tiles).length = tiles.length := by
  induction tiles with
  | nil => rfl
  | cons tile rest ih => cases tile <;> simp only [replaceSquares,List.length_cons,ih]

theorem replaceSquares_nonempty (x : Nat) (tiles : List PowerTile) (nonempty : tiles ≠ []) :
    replaceSquares x tiles ≠ [] := by
  cases tiles with
  | nil => exact False.elim (nonempty rfl)
  | cons tile rest => cases tile <;> simp [replaceSquares]

theorem replaceSquares_noSquares (x : Nat) (tiles : List PowerTile) :
    tileSquares (replaceSquares x tiles) = [] := by
  induction tiles with
  | nil => rfl
  | cons tile rest ih => cases tile <;> simp only [replaceSquares,tileSquares,ih]

theorem replaceSquares_preserves_cube (x y : Nat) (tiles : List PowerTile)
    (present : y ∈ tileCubes tiles) : y ∈ tileCubes (replaceSquares x tiles) := by
  induction tiles with
  | nil => cases present
  | cons tile rest ih =>
      cases tile with
      | square z => exact List.mem_cons_of_mem x (ih present)
      | cube z =>
          rcases List.mem_cons.mp present with rfl | found
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem z (ih found)

theorem replaceSquares_cube_cases (x y : Nat) (tiles : List PowerTile)
    (present : y ∈ tileCubes (replaceSquares x tiles)) : y = x ∨ y ∈ tileCubes tiles := by
  induction tiles with
  | nil => cases present
  | cons tile rest ih =>
      cases tile with
      | square z =>
          rcases List.mem_cons.mp present with equal | found
          · exact Or.inl equal
          · exact ih found
      | cube z =>
          rcases List.mem_cons.mp present with equal | found
          · exact Or.inr (List.mem_cons.mpr (Or.inl equal))
          · rcases ih found with equal | old
            · exact Or.inl equal
            · exact Or.inr (List.mem_cons_of_mem z old)

theorem replaceSquares_cube_iff (x : Nat) (tiles : List PowerTile)
    (seed : x ∈ tileCubes tiles) (y : Nat) :
    y ∈ tileCubes (replaceSquares x tiles) ↔ y ∈ tileCubes tiles := by
  constructor
  · intro present
    rcases replaceSquares_cube_cases x y tiles present with rfl | old
    · exact seed
    · exact old
  · exact replaceSquares_preserves_cube x y tiles

theorem tileSquares_map_square (markers : List Nat) :
    tileSquares (markers.map PowerTile.square) = markers := by
  induction markers with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,tileSquares,ih]

theorem tileCubes_map_square (markers : List Nat) :
    tileCubes (markers.map PowerTile.square) = [] := by
  induction markers with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,tileCubes,ih]

theorem powerTileBody_map_square (markers : List Nat) :
    powerTileBody (markers.map PowerTile.square) = squareBody markers := by
  induction markers with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,powerTileBody_cons,powerTileWord,squareBody,ih]

theorem collectRightSquares (x : Nat) (left right : List PowerTile) (gap : List Nat)
    (present : x ∈ tileCubes left) :
    ListDerives (powerTileBody left ++ gap ++ powerTileBody right)
      (powerTileBody (left ++ (tileSquares right).map PowerTile.square) ++
        gap ++ powerTileBody (replaceSquares x right)) := by
  induction right generalizing left gap with
  | nil =>
      simpa only [tileSquares,List.map_nil,List.append_nil,replaceSquares,powerTileBody_nil]
        using (S5_107.ListDerives.refl (basis := basis) (powerTileBody left ++ gap))
  | cons tile rest ih =>
      cases tile with
      | square y =>
          have first : ListDerives
              (powerTileBody left ++ gap ++ powerTileBody (.square y :: rest))
              (powerTileBody left ++ [x,x,x] ++ gap ++ [y,y] ++ powerTileBody rest) := by
            simpa only [powerTileBody_cons,powerTileWord,List.append_assoc] using
              (powerTileBody_duplicate_right left x present).append (gap ++ [y,y] ++ powerTileBody rest)
          have second : ListDerives
              (powerTileBody left ++ [x,x,x] ++ gap ++ [y,y] ++ powerTileBody rest)
              (powerTileBody (left ++ [.square y]) ++ (gap ++ [x,x,x]) ++ powerTileBody rest) := by
            simpa only [powerTileBody_append,powerTileBody_cons,powerTileBody_nil,powerTileWord,
              List.append_nil,List.append_assoc] using
              ((swapCubeSquare x y gap).prepend (powerTileBody left)).append (powerTileBody rest)
          have retained : x ∈ tileCubes (left ++ [.square y]) := by
            simpa only [tileCubes_append,tileCubes,List.append_nil] using present
          have third := ih (left ++ [.square y]) (gap ++ [x,x,x]) retained
          simpa only [tileSquares,List.map_cons,replaceSquares,powerTileBody_cons,powerTileWord,
            List.append_assoc,List.cons_append,List.nil_append] using first.trans (second.trans third)
      | cube y =>
          simpa only [tileSquares,replaceSquares,powerTileBody_cons,powerTileWord,List.append_assoc]
            using ih left (gap ++ [y,y,y]) present

theorem replaceSquares_valid (original : List Nat) (x : Nat) (tiles : List PowerTile)
    (unrestricted : Unrestricted x original)
    (valid : ∀ tile ∈ tiles, CubicTokenValid original (.power tile)) :
    ∀ tile ∈ replaceSquares x tiles, CubicTokenValid original (.power tile) := by
  induction tiles with
  | nil => intro tile member; cases member
  | cons first rest ih =>
      have tail : ∀ tile ∈ rest, CubicTokenValid original (.power tile) :=
        fun tile member => valid tile (List.mem_cons_of_mem first member)
      cases first with
      | square y =>
          intro tile member
          rcases List.mem_cons.mp member with rfl | found
          · exact unrestricted
          · exact ih tail tile found
      | cube y =>
          intro tile member
          rcases List.mem_cons.mp member with rfl | found
          · exact valid (.cube y) List.mem_cons_self
          · exact ih tail tile found

theorem collectedSquares_valid (original : List Nat) (left right : List PowerTile)
    (leftValid : ∀ tile ∈ left, CubicTokenValid original (.power tile))
    (rightValid : ∀ tile ∈ right, CubicTokenValid original (.power tile)) :
    ∀ tile ∈ left ++ (tileSquares right).map PowerTile.square,
      CubicTokenValid original (.power tile) := by
  intro tile member
  rcases List.mem_append.mp member with old | moved
  · exact leftValid tile old
  · rcases List.mem_map.mp moved with ⟨y,found,equal⟩
    subst tile
    exact rightValid (.square y) ((tileSquares_mem right y).mp found)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_nil
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_cons
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.replaceSquares_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.replaceSquares_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.replaceSquares_noSquares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.replaceSquares_preserves_cube
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.replaceSquares_cube_cases
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.replaceSquares_cube_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.tileSquares_map_square
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.tileCubes_map_square
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_map_square
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.collectRightSquares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.replaceSquares_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.collectedSquares_valid

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
