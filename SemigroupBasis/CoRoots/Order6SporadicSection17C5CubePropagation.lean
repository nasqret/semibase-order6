import SemigroupBasis.CoRoots.Order6SporadicSection17C5BodyDecomposition

/-! Context-safe propagation of a cube between arbitrary nonempty power
bodies. A cube anchor is split as two letters plus explicit context, never
collapsed to a square. Both source bodies and intervening gaps are retained. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem tileSquares_append (left right : List PowerTile) :
    tileSquares (left ++ right) = tileSquares left ++ tileSquares right := by
  induction left with
  | nil => rfl
  | cons tile rest ih => cases tile <;> simp [tileSquares,ih]

theorem tileCubes_append (left right : List PowerTile) :
    tileCubes (left ++ right) = tileCubes left ++ tileCubes right := by
  induction left with
  | nil => rfl
  | cons tile rest ih => cases tile <;> simp [tileCubes,ih]

theorem tileSquares_mem (tiles : List PowerTile) (x : Nat) :
    x ∈ tileSquares tiles ↔ PowerTile.square x ∈ tiles := by
  induction tiles with
  | nil => simp [tileSquares]
  | cons tile rest ih => cases tile <;> simp [tileSquares,ih]

theorem tileCubes_mem (tiles : List PowerTile) (x : Nat) :
    x ∈ tileCubes tiles ↔ PowerTile.cube x ∈ tiles := by
  induction tiles with
  | nil => simp [tileCubes]
  | cons tile rest ih => cases tile <;> simp [tileCubes,ih]

theorem powerTileBody_append (left right : List PowerTile) :
    powerTileBody (left ++ right) = powerTileBody left ++ powerTileBody right :=
  List.flatMap_append

theorem powerTileBody_duplicate_left (tiles : List PowerTile) (x : Nat)
    (present : x ∈ tileCubes tiles) :
    ListDerives (powerTileBody tiles) ([x,x,x] ++ powerTileBody tiles) := by
  have squares : (tileSquares tiles).Perm (tileSquares (.cube x :: tiles)) := List.Perm.refl _
  have cubes : ∀ y, y ∈ tileCubes tiles ↔ y ∈ tileCubes (.cube x :: tiles) := by
    intro y
    change y ∈ tileCubes tiles ↔ y ∈ x :: tileCubes tiles
    constructor
    · exact List.mem_cons_of_mem x
    · intro member
      rcases List.mem_cons.mp member with rfl | found
      · exact present
      · exact found
  exact powerTileBody_compare squares cubes

theorem powerTileBody_duplicate_right (tiles : List PowerTile) (x : Nat)
    (present : x ∈ tileCubes tiles) :
    ListDerives (powerTileBody tiles) (powerTileBody tiles ++ [x,x,x]) := by
  have squares : (tileSquares tiles).Perm (tileSquares (tiles ++ [.cube x])) := by
    simpa only [tileSquares_append,tileSquares,List.append_nil] using (List.Perm.refl (tileSquares tiles))
  have cubes : ∀ y, y ∈ tileCubes tiles ↔ y ∈ tileCubes (tiles ++ [.cube x]) := by
    intro y
    simp only [tileCubes_append,tileCubes,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    constructor
    · exact Or.inl
    · rintro (found | rfl)
      · exact found
      · exact present
  have derivation := powerTileBody_compare squares cubes
  rw [powerTileBody_append] at derivation
  exact derivation

theorem cubeAcrossPowerBody (x : Nat) (tiles : List PowerTile) :
    ListDerives ([x,x,x] ++ powerTileBody tiles) (powerTileBody tiles ++ [x,x,x]) := by
  induction tiles with
  | nil => exact S5_107.ListDerives.refl _
  | cons tile rest ih =>
      have first : ListDerives
          ([x,x,x] ++ (powerTileWord tile ++ powerTileBody rest))
          (powerTileWord tile ++ ([x,x,x] ++ powerTileBody rest)) := by
        simpa only [powerTileWord,List.append_nil,List.append_assoc] using
          (swapPowerTiles (.cube x) tile []).append (powerTileBody rest)
      have second := ih.prepend (powerTileWord tile)
      simpa only [powerTileBody,List.flatMap_cons,List.append_assoc] using first.trans second

theorem spreadCube_to_nonempty_body (x : Nat) (gap : List Nat) (right : List PowerTile)
    (gapNonempty : gap ≠ []) (rightNonempty : right ≠ []) :
    ListDerives ([x,x,x] ++ gap ++ powerTileBody right)
      ([x,x,x] ++ gap ++ [x,x,x] ++ powerTileBody right) := by
  cases right with
  | nil => exact False.elim (rightNonempty rfl)
  | cons tile rest =>
      cases tile with
      | square h =>
          simpa only [powerTileBody,List.flatMap_cons,powerTileWord,List.append_assoc] using
            (spreadCubeRight x h gap gapNonempty).append (powerTileBody rest)
      | cube h =>
          simpa only [powerTileBody,List.flatMap_cons,powerTileWord,List.append_assoc] using
            (spreadCubeRight x h gap gapNonempty).append ([h] ++ powerTileBody rest)

theorem spreadCube_from_nonempty_body (x : Nat) (gap : List Nat) (left : List PowerTile)
    (gapNonempty : gap ≠ []) (leftNonempty : left ≠ []) :
    ListDerives (powerTileBody left ++ gap ++ [x,x,x])
      (powerTileBody left ++ [x,x,x] ++ gap ++ [x,x,x]) := by
  induction left with
  | nil => exact False.elim (leftNonempty rfl)
  | cons tile rest ih =>
      cases rest with
      | nil =>
          cases tile with
          | square h =>
              simpa only [powerTileBody,List.flatMap_cons,List.flatMap_nil,powerTileWord,List.append_nil,List.append_assoc] using
                spreadCubeLeft h x gap gapNonempty
          | cube h =>
              simpa only [powerTileBody,List.flatMap_cons,List.flatMap_nil,powerTileWord,List.append_nil,List.append_assoc] using
                (spreadCubeLeft h x gap gapNonempty).prepend [h]
      | cons next rest =>
          have tail := ih (by simp)
          simpa only [powerTileBody,List.flatMap_cons,List.append_assoc] using tail.prepend (powerTileWord tile)

theorem propagateCubeRight (x : Nat) (left right : List PowerTile) (gap : List Nat)
    (present : x ∈ tileCubes left) (gapNonempty : gap ≠ []) (rightNonempty : right ≠ []) :
    ListDerives (powerTileBody left ++ gap ++ powerTileBody right)
      (powerTileBody left ++ gap ++ powerTileBody (right ++ [.cube x])) := by
  have duplicate := powerTileBody_duplicate_right left x present
  have first : ListDerives (powerTileBody left ++ gap ++ powerTileBody right)
      (powerTileBody left ++ [x,x,x] ++ gap ++ powerTileBody right) := by
    simpa only [List.append_assoc] using duplicate.append (gap ++ powerTileBody right)
  have second : ListDerives
      (powerTileBody left ++ [x,x,x] ++ gap ++ powerTileBody right)
      (powerTileBody left ++ [x,x,x] ++ gap ++ [x,x,x] ++ powerTileBody right) := by
    simpa only [List.append_assoc] using
      (spreadCube_to_nonempty_body x gap right gapNonempty rightNonempty).prepend (powerTileBody left)
  have third : ListDerives
      (powerTileBody left ++ [x,x,x] ++ gap ++ [x,x,x] ++ powerTileBody right)
      (powerTileBody left ++ gap ++ [x,x,x] ++ powerTileBody right) := by
    simpa only [List.append_assoc] using duplicate.symm.append (gap ++ [x,x,x] ++ powerTileBody right)
  have fourth : ListDerives
      (powerTileBody left ++ gap ++ [x,x,x] ++ powerTileBody right)
      (powerTileBody left ++ gap ++ (powerTileBody right ++ [x,x,x])) := by
    simpa only [List.append_assoc] using (cubeAcrossPowerBody x right).prepend (powerTileBody left ++ gap)
  have derivation := first.trans (second.trans (third.trans fourth))
  rw [powerTileBody_append]
  exact derivation

theorem propagateCubeLeft (x : Nat) (left right : List PowerTile) (gap : List Nat)
    (present : x ∈ tileCubes right) (gapNonempty : gap ≠ []) (leftNonempty : left ≠ []) :
    ListDerives (powerTileBody left ++ gap ++ powerTileBody right)
      (powerTileBody (left ++ [.cube x]) ++ gap ++ powerTileBody right) := by
  have duplicate := powerTileBody_duplicate_left right x present
  have first : ListDerives (powerTileBody left ++ gap ++ powerTileBody right)
      (powerTileBody left ++ gap ++ [x,x,x] ++ powerTileBody right) := by
    simpa only [List.append_assoc] using duplicate.prepend (powerTileBody left ++ gap)
  have second : ListDerives
      (powerTileBody left ++ gap ++ [x,x,x] ++ powerTileBody right)
      (powerTileBody left ++ [x,x,x] ++ gap ++ [x,x,x] ++ powerTileBody right) := by
    simpa only [List.append_assoc] using
      (spreadCube_from_nonempty_body x gap left gapNonempty leftNonempty).append (powerTileBody right)
  have third : ListDerives
      (powerTileBody left ++ [x,x,x] ++ gap ++ [x,x,x] ++ powerTileBody right)
      (powerTileBody left ++ [x,x,x] ++ gap ++ powerTileBody right) := by
    simpa only [List.append_assoc] using duplicate.symm.prepend (powerTileBody left ++ [x,x,x] ++ gap)
  have derivation := first.trans (second.trans third)
  rw [powerTileBody_append]
  exact derivation

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.tileSquares_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.tileCubes_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.tileSquares_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.tileCubes_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_duplicate_left
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_duplicate_right
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubeAcrossPowerBody
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.spreadCube_to_nonempty_body
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.spreadCube_from_nonempty_body
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.propagateCubeRight
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.propagateCubeLeft

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
