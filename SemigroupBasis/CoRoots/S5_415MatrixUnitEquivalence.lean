import SemigroupBasis.CoRoots.S5_415
import SemigroupBasis.MatrixUnitIdentityTheory

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-- A two-sided equivalence packaged with explicit forward and inverse maps. -/
structure Equiv (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ value, invFun (toFun value) = value
  right_inv : ∀ value, toFun (invFun value) = value

/-- Send the zero catalogue element to the zero matrix unit and decode every
nonzero catalogue element by its two matrix-unit coordinates. -/
def catalogueToMatrixUnit (value : Fin 5) : MatrixUnit (Fin 2) :=
  if value = 0 then MatrixUnit.zero
  else MatrixUnit.ofIndices (firstCoordinate value) (finalCoordinate value)

/-- Encode zero and the four matrix units in the catalogue's zero-based
labelling. -/
def matrixUnitToCatalogue : MatrixUnit (Fin 2) -> Fin 5
  | none => 0
  | some (first, final) => coordinateValue first final

@[simp]
theorem catalogueToMatrixUnit_zero :
    catalogueToMatrixUnit 0 = (MatrixUnit.zero : MatrixUnit (Fin 2)) := by
  rfl

@[simp]
theorem catalogueToMatrixUnit_coordinateValue (first final : Fin 2) :
    catalogueToMatrixUnit (coordinateValue first final) =
      MatrixUnit.ofIndices first final := by
  simp [catalogueToMatrixUnit, coordinateValue_ne_zero]

@[simp]
theorem matrixUnitToCatalogue_zero :
    matrixUnitToCatalogue (MatrixUnit.zero : MatrixUnit (Fin 2)) = 0 := by
  rfl

@[simp]
theorem matrixUnitToCatalogue_ofIndices (first final : Fin 2) :
    matrixUnitToCatalogue (MatrixUnit.ofIndices first final) =
      coordinateValue first final := by
  rfl

@[simp]
theorem matrixUnitToCatalogue_catalogueToMatrixUnit (value : Fin 5) :
    matrixUnitToCatalogue (catalogueToMatrixUnit value) = value := by
  by_cases zero : value = 0
  · subst value
    rfl
  · simp [catalogueToMatrixUnit, zero, coordinateValue_eq value zero]

@[simp]
theorem catalogueToMatrixUnit_matrixUnitToCatalogue
    (value : MatrixUnit (Fin 2)) :
    catalogueToMatrixUnit (matrixUnitToCatalogue value) = value := by
  rcases value with _ | ⟨first, final⟩
  · rfl
  · exact catalogueToMatrixUnit_coordinateValue first final

/-- The explicit bijection between the catalogue carrier and zero together
with the four `2 x 2` matrix units. -/
def matrixUnitEquivalence : Equiv (Fin 5) (MatrixUnit (Fin 2)) where
  toFun := catalogueToMatrixUnit
  invFun := matrixUnitToCatalogue
  left_inv := matrixUnitToCatalogue_catalogueToMatrixUnit
  right_inv := catalogueToMatrixUnit_matrixUnitToCatalogue

theorem catalogueToMatrixUnit_map_mul (left right : Fin 5) :
    catalogueToMatrixUnit
        (Generated.Catalogue.S5_415.table.semigroup.mul left right) =
      (MatrixUnit.semigroup (I := Fin 2)).mul
        (catalogueToMatrixUnit left) (catalogueToMatrixUnit right) := by
  decide +revert

theorem matrixUnitToCatalogue_map_mul
    (left right : MatrixUnit (Fin 2)) :
    matrixUnitToCatalogue
        ((MatrixUnit.semigroup (I := Fin 2)).mul left right) =
      Generated.Catalogue.S5_415.table.semigroup.mul
        (matrixUnitToCatalogue left) (matrixUnitToCatalogue right) := by
  have mapped := congrArg matrixUnitToCatalogue
    (catalogueToMatrixUnit_map_mul
      (matrixUnitToCatalogue left) (matrixUnitToCatalogue right))
  simpa using mapped.symm

/-- The catalogue presentation embedded into the matrix-unit presentation. -/
def catalogueToMatrixUnitEmbedding :
    Embedding Generated.Catalogue.S5_415.table.semigroup
      (MatrixUnit.semigroup (I := Fin 2)) where
  toFun := catalogueToMatrixUnit
  map_mul := catalogueToMatrixUnit_map_mul
  injective := by
    intro left right equality
    have inverseEquality := congrArg matrixUnitToCatalogue equality
    simpa using inverseEquality

/-- The inverse embedding from matrix units to catalogue labels. -/
def matrixUnitToCatalogueEmbedding :
    Embedding (MatrixUnit.semigroup (I := Fin 2))
      Generated.Catalogue.S5_415.table.semigroup where
  toFun := matrixUnitToCatalogue
  map_mul := matrixUnitToCatalogue_map_mul
  injective := by
    intro left right equality
    have inverseEquality := congrArg catalogueToMatrixUnit equality
    simpa using inverseEquality

/-- The two concrete semigroup presentations satisfy exactly the same
identities over any variable type. -/
theorem sameIdentityTheoryOver_matrixUnit (α : Type u) :
    SameIdentityTheoryOver
      Generated.Catalogue.S5_415.table.semigroup
      (MatrixUnit.semigroup (I := Fin 2)) α := by
  intro identity
  constructor
  · exact matrixUnitToCatalogueEmbedding.pullback_identity identity
  · exact catalogueToMatrixUnitEmbedding.pullback_identity identity

/-- The catalogue presentation and the standard five-element matrix-unit
semigroup have exactly the same plain (`Nat`-variable) identities. -/
theorem sameIdentityTheory_matrixUnit :
    SameIdentityTheory
      Generated.Catalogue.S5_415.table.semigroup
      (MatrixUnit.semigroup (I := Fin 2)) :=
  sameIdentityTheoryOver_matrixUnit Nat

/-- Every identity of the catalogue `B_2` table holds in matrix units over an
arbitrary decidable index type. -/
theorem matrixUnit_satisfiedBy_of_catalogue [DecidableEq I]
    (identity : Identity α)
    (valid :
      identity.SatisfiedBy Generated.Catalogue.S5_415.table.semigroup) :
    identity.SatisfiedBy (MatrixUnit.semigroup (I := I)) :=
  MatrixUnit.satisfiedBy_of_finTwo identity
    ((sameIdentityTheoryOver_matrixUnit α identity).mp valid)

end SemigroupBasis.CoRoots.S5_415
