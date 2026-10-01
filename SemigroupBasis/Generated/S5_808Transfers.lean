import SemigroupBasis.CoRoots.S5_808
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.S5_808Transfers

open SemigroupBasis

namespace S5_844

abbrev sourceTable : FiniteTable :=
  Generated.Catalogue.S5_808.table

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_844.table

theorem table_eq_canonical_catalogue :
    table = Generated.Catalogue.S5_844.table := rfl

/-- The first recorded one-based homomorphism `[1,2,3,3,4]`. -/
def firstHom :
    Hom sourceTable.semigroup table.semigroup where
  toFun := fun value =>
    if value = (0 : Fin 5) then (0 : Fin 5)
    else if value = (1 : Fin 5) then (1 : Fin 5)
    else if value = (2 : Fin 5) then (2 : Fin 5)
    else if value = (3 : Fin 5) then (2 : Fin 5)
    else (3 : Fin 5)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide

/-- The second recorded one-based homomorphism `[1,1,4,5,4]`. -/
def secondHom :
    Hom sourceTable.semigroup table.semigroup where
  toFun := fun value =>
    if value = (0 : Fin 5) then (0 : Fin 5)
    else if value = (1 : Fin 5) then (0 : Fin 5)
    else if value = (2 : Fin 5) then (3 : Fin 5)
    else if value = (3 : Fin 5) then (4 : Fin 5)
    else (3 : Fin 5)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide

def separatingHomomorphismsOneBased : List (List Nat) :=
  [[(firstHom.toFun (0 : Fin 5)).val + 1,
      (firstHom.toFun (1 : Fin 5)).val + 1,
      (firstHom.toFun (2 : Fin 5)).val + 1,
      (firstHom.toFun (3 : Fin 5)).val + 1,
      (firstHom.toFun (4 : Fin 5)).val + 1],
    [(secondHom.toFun (0 : Fin 5)).val + 1,
      (secondHom.toFun (1 : Fin 5)).val + 1,
      (secondHom.toFun (2 : Fin 5)).val + 1,
      (secondHom.toFun (3 : Fin 5)).val + 1,
      (secondHom.toFun (4 : Fin 5)).val + 1]]

theorem separatingHomomorphismsOneBased_certificate :
    separatingHomomorphismsOneBased =
      [[1, 2, 3, 3, 4], [1, 1, 4, 5, 4]] := by
  decide

def diagonalSignaturesOneBased : List (Nat × Nat) :=
  [((firstHom.toFun (0 : Fin 5)).val + 1,
      (secondHom.toFun (0 : Fin 5)).val + 1),
    ((firstHom.toFun (1 : Fin 5)).val + 1,
      (secondHom.toFun (1 : Fin 5)).val + 1),
    ((firstHom.toFun (2 : Fin 5)).val + 1,
      (secondHom.toFun (2 : Fin 5)).val + 1),
    ((firstHom.toFun (3 : Fin 5)).val + 1,
      (secondHom.toFun (3 : Fin 5)).val + 1),
    ((firstHom.toFun (4 : Fin 5)).val + 1,
      (secondHom.toFun (4 : Fin 5)).val + 1)]

theorem diagonalSignaturesOneBased_certificate :
    diagonalSignaturesOneBased =
      [(1, 1), (2, 1), (3, 4), (3, 5), (4, 4)] := by
  decide

theorem separatingPair_injective :
    Function.Injective fun value =>
      (firstHom.toFun value, secondHom.toFun value) := by
  intro left right
  revert left right
  decide

/-- The diagonal of the two recorded homomorphisms embeds `S5_808`
into the direct square of `S5_844`. -/
def sourceEmbedding :
    Embedding sourceTable.semigroup
      (table.semigroup.pi (Fin 2)) where
  toFun := fun value coordinate =>
    if coordinate = 0 then
      firstHom.toFun value
    else
      secondHom.toFun value
  map_mul := by
    intro left right
    funext coordinate
    exact by decide +revert
  injective := by
    intro left right equal
    have first := congrFun equal (0 : Fin 2)
    have second := congrFun equal (1 : Fin 2)
    clear equal
    exact by decide +revert

theorem targetModels :
    Models table.semigroup
      SemigroupBasis.CoRoots.S5_808.basis :=
  SemigroupBasis.CoRoots.S5_808.models_of_finite_checks
    table (by decide)

/-- The recorded direct-power identity sandwich transfers the complete
`S5_808` basis to `S5_844`. -/
theorem representative_basis :
    BasisFor table.semigroup
      SemigroupBasis.CoRoots.S5_808.basis :=
  SemigroupBasis.CoRoots.S5_808.representative_basis.inheritAlongPowerEmbedding
    sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_808.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_808.oppositeBasis] using
    representative_basis.oppositeReversed

end S5_844

structure FamilyBasisEndpoints : Prop where
  s5_808Representative :
    BasisFor Generated.Catalogue.S5_808.table.semigroup
      SemigroupBasis.CoRoots.S5_808.basis
  s5_808Opposite :
    BasisFor Generated.Catalogue.S5_808.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_808.oppositeBasis
  s5_844Representative :
    BasisFor Generated.Catalogue.S5_844.table.semigroup
      SemigroupBasis.CoRoots.S5_808.basis
  s5_844Opposite :
    BasisFor Generated.Catalogue.S5_844.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_808.oppositeBasis

theorem allEndpoints : FamilyBasisEndpoints :=
  ⟨SemigroupBasis.CoRoots.S5_808.representative_basis,
    SemigroupBasis.CoRoots.S5_808.opposite_basis,
    S5_844.representative_basis,
    S5_844.opposite_basis⟩

end SemigroupBasis.Generated.S5_808Transfers
