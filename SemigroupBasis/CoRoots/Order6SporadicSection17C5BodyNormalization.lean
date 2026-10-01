import SemigroupBasis.CoRoots.Order6SporadicSection17C5BlockPermutations

/-! Unrestricted nonsimple-body normalization. Cubes form a commutative
idempotent subcalculus; square multiplicities are retained, never deduplicated.
This is the within-body stage of beta normalization, not its propagation step. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

def squareBody : List Nat → List Nat
  | [] => []
  | x :: xs => [x,x] ++ squareBody xs

def cubeBody : List Nat → List Nat
  | [] => []
  | x :: xs => [x,x,x] ++ cubeBody xs

theorem squareBody_perm {left right : List Nat} (permutation : left.Perm right) :
    ListDerives (squareBody left) (squareBody right) := by
  induction permutation with
  | nil => exact S5_107.ListDerives.refl _
  | cons x permutation ih => exact ih.prepend [x,x]
  | swap x y rest =>
      simpa only [squareBody,List.append_nil,List.append_assoc] using
        (swapSquares y x []).append (squareBody rest)
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

theorem cubeBody_perm {left right : List Nat} (permutation : left.Perm right) :
    ListDerives (cubeBody left) (cubeBody right) := by
  induction permutation with
  | nil => exact S5_107.ListDerives.refl _
  | cons x permutation ih => exact ih.prepend [x,x,x]
  | swap x y rest =>
      simpa only [cubeBody,List.append_nil,List.append_assoc] using
        (swapCubes y x []).append (cubeBody rest)
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

theorem cubeBody_absorb (x : Nat) (markers : List Nat) :
    x ∈ markers → ListDerives ([x,x,x] ++ cubeBody markers) (cubeBody markers) := by
  induction markers with
  | nil => intro impossible; cases impossible
  | cons y ys ih =>
      intro member
      by_cases equal : x = y
      · subst y
        simpa only [cubeBody,List.append_assoc] using (cubeIdempotent x).append (cubeBody ys)
      · have tailMember : x ∈ ys := by
          rcases List.mem_cons.mp member with same | found
          · exact False.elim (equal same)
          · exact found
        have first : ListDerives ([x,x,x] ++ ([y,y,y] ++ cubeBody ys))
            ([y,y,y] ++ ([x,x,x] ++ cubeBody ys)) := by
          simpa only [List.append_nil,List.append_assoc] using (swapCubes x y []).append (cubeBody ys)
        exact first.trans ((ih tailMember).prepend [y,y,y])

theorem cubeBody_unique (markers : List Nat) :
    ListDerives (cubeBody markers) (cubeBody (uniqueMarkers markers)) := by
  induction markers with
  | nil => exact S5_107.ListDerives.refl _
  | cons x xs ih =>
      by_cases present : x ∈ xs
      · simpa only [cubeBody,uniqueMarkers,if_pos present] using (cubeBody_absorb x xs present).trans ih
      · simpa only [cubeBody,uniqueMarkers,if_neg present] using ih.prepend [x,x,x]

theorem uniqueMarkers_perm_of_mem {left right : List Nat}
    (same : ∀ marker, marker ∈ left ↔ marker ∈ right) :
    (uniqueMarkers left).Perm (uniqueMarkers right) := by
  apply List.perm_iff_count.mpr
  intro marker
  simp only [(uniqueMarkers_nodup left).count,(uniqueMarkers_nodup right).count,
    uniqueMarkers_mem,same marker]

theorem cubeBody_sameContent {left right : List Nat}
    (same : ∀ marker, marker ∈ left ↔ marker ∈ right) :
    ListDerives (cubeBody left) (cubeBody right) :=
  (cubeBody_unique left).trans
    ((cubeBody_perm (uniqueMarkers_perm_of_mem same)).trans (cubeBody_unique right).symm)

theorem cubeBody_nonempty (markers : List Nat) (nonempty : markers ≠ []) : cubeBody markers ≠ [] := by
  cases markers with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs => simp [cubeBody]

def tileSquares : List PowerTile → List Nat
  | [] => []
  | .square x :: rest => x :: tileSquares rest
  | .cube _ :: rest => tileSquares rest

def tileCubes : List PowerTile → List Nat
  | [] => []
  | .square _ :: rest => tileCubes rest
  | .cube x :: rest => x :: tileCubes rest

theorem cube_across_squares (x : Nat) (squares : List Nat) :
    ListDerives ([x,x,x] ++ squareBody squares) (squareBody squares ++ [x,x,x]) := by
  induction squares with
  | nil => exact S5_107.ListDerives.refl _
  | cons y ys ih =>
      have first : ListDerives ([x,x,x] ++ ([y,y] ++ squareBody ys))
          ([y,y] ++ ([x,x,x] ++ squareBody ys)) := by
        simpa only [List.append_nil,List.append_assoc] using (swapCubeSquare x y []).append (squareBody ys)
      have second := ih.prepend [y,y]
      simpa only [squareBody,List.append_assoc] using first.trans second

theorem powerTileBody_split (tiles : List PowerTile) :
    ListDerives (powerTileBody tiles) (squareBody (tileSquares tiles) ++ cubeBody (tileCubes tiles)) := by
  induction tiles with
  | nil => exact S5_107.ListDerives.refl _
  | cons tile rest ih =>
      cases tile with
      | square x =>
          simpa only [powerTileBody,List.flatMap_cons,powerTileWord,tileSquares,tileCubes,squareBody,List.append_assoc]
            using ih.prepend [x,x]
      | cube x =>
          have first : ListDerives (powerTileBody (.cube x :: rest))
              ([x,x,x] ++ (squareBody (tileSquares rest) ++ cubeBody (tileCubes rest))) := by
            simpa only [powerTileBody,List.flatMap_cons,powerTileWord] using ih.prepend [x,x,x]
          have second : ListDerives
              ([x,x,x] ++ (squareBody (tileSquares rest) ++ cubeBody (tileCubes rest)))
              (squareBody (tileSquares rest) ++ ([x,x,x] ++ cubeBody (tileCubes rest))) := by
            simpa only [List.append_assoc] using
              (cube_across_squares x (tileSquares rest)).append (cubeBody (tileCubes rest))
          simpa only [tileSquares,tileCubes,cubeBody] using first.trans second

theorem powerTileBody_normalize (tiles : List PowerTile) :
    ListDerives (powerTileBody tiles)
      (squareBody (tileSquares tiles) ++ cubeBody (uniqueMarkers (tileCubes tiles))) :=
  (powerTileBody_split tiles).trans ((cubeBody_unique (tileCubes tiles)).prepend (squareBody (tileSquares tiles)))

theorem powerTileBody_compare {left right : List PowerTile}
    (squares : (tileSquares left).Perm (tileSquares right))
    (cubes : ∀ marker, marker ∈ tileCubes left ↔ marker ∈ tileCubes right) :
    ListDerives (powerTileBody left) (powerTileBody right) := by
  have first := (squareBody_perm squares).append (cubeBody (tileCubes left))
  have second := (cubeBody_sameContent cubes).prepend (squareBody (tileSquares right))
  exact (powerTileBody_split left).trans (first.trans (second.trans (powerTileBody_split right).symm))

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.squareBody_perm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubeBody_perm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubeBody_absorb
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubeBody_unique
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.uniqueMarkers_perm_of_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubeBody_sameContent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubeBody_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cube_across_squares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_normalize
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.powerTileBody_compare

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
