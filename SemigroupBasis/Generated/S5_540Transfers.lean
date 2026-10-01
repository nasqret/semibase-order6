import SemigroupBasis.CoRoots.S5_540
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.S5_540Transfers.S5_540

open SemigroupBasis
open SemigroupBasis.Examples

abbrev sourceTable : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_1159.table

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_540.table

abbrev sourceSemigroup : Semigroup (Fin 5) :=
  SemigroupBasis.Generated.Catalogue.S5_1159.table.semigroup

abbrev targetSemigroup : Semigroup (Fin 5) :=
  SemigroupBasis.Generated.Catalogue.S5_540.table.semigroup

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_540.table := rfl

/-- The recorded one-based homomorphism `[1,4,5,5,4]`. -/
def firstHom :
    Hom sourceSemigroup targetSemigroup where
  toFun := fun a =>
    if a = 0 then 0
    else if a = 1 then 3
    else if a = 2 then 4
    else if a = 3 then 4
    else 3
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide

/-- The recorded one-based homomorphism `[1,1,1,2,3]`. -/
def secondHom :
    Hom sourceSemigroup targetSemigroup where
  toFun := fun a =>
    if a = 0 then 0
    else if a = 1 then 0
    else if a = 2 then 0
    else if a = 3 then 1
    else 2
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide

theorem separatingPair_injective :
    Function.Injective fun a =>
      (firstHom.toFun a, secondHom.toFun a) := by
  intro a b
  revert a b
  decide

def separatingHomomorphismsOneBased : List (List Nat) :=
  [[(firstHom.toFun 0).val + 1,
      (firstHom.toFun 1).val + 1,
      (firstHom.toFun 2).val + 1,
      (firstHom.toFun 3).val + 1,
      (firstHom.toFun 4).val + 1],
    [(secondHom.toFun 0).val + 1,
      (secondHom.toFun 1).val + 1,
      (secondHom.toFun 2).val + 1,
      (secondHom.toFun 3).val + 1,
      (secondHom.toFun 4).val + 1]]

theorem separatingHomomorphismsOneBased_certificate :
    separatingHomomorphismsOneBased =
      [[1, 4, 5, 5, 4], [1, 1, 1, 2, 3]] := by
  decide

def diagonalSignaturesOneBased : List (Nat × Nat) :=
  [((firstHom.toFun 0).val + 1, (secondHom.toFun 0).val + 1),
    ((firstHom.toFun 1).val + 1, (secondHom.toFun 1).val + 1),
    ((firstHom.toFun 2).val + 1, (secondHom.toFun 2).val + 1),
    ((firstHom.toFun 3).val + 1, (secondHom.toFun 3).val + 1),
    ((firstHom.toFun 4).val + 1, (secondHom.toFun 4).val + 1)]

theorem diagonalSignaturesOneBased_certificate :
    diagonalSignaturesOneBased =
      [(1, 1), (4, 1), (5, 1), (5, 2), (4, 3)] := by
  decide

/-- The diagonal of the two recorded homomorphisms embeds `S5_1159` into
the direct square of `S5_540`. -/
def sourceEmbedding :
    Embedding sourceSemigroup
      (targetSemigroup.pi (Fin 2)) where
  toFun := fun a i =>
    if i = 0 then firstHom.toFun a else secondHom.toFun a
  map_mul := by
    intro a b
    funext i
    exact by decide +revert
  injective := by
    intro a b equal
    have first := congrFun equal (0 : Fin 2)
    have second := congrFun equal (1 : Fin 2)
    clear equal
    exact by decide +revert

theorem targetModels :
    Models targetSemigroup
      SemigroupBasis.CoRoots.S5_540.basis := by
  intro identity member
  simp only [SemigroupBasis.CoRoots.S5_540.basis,
    cyclicThreeThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [← cyclicThreeThreeFiniteCommutativityLaw_map]
    exact table.checkIdentityNat_sound
      cyclicThreeThreeFiniteCommutativityLaw (by decide)
  · rw [← cyclicThreeThreeFiniteLongCancellationLaw_map]
    exact table.checkIdentityNat_sound
      cyclicThreeThreeFiniteLongCancellationLaw (by decide)

theorem representative_basis :
    BasisFor targetSemigroup
      SemigroupBasis.CoRoots.S5_540.basis :=
  SemigroupBasis.BasisFor.inheritAlongPowerEmbedding
    SemigroupBasis.CoRoots.S5_540.S5_1159.representative_basis
    sourceEmbedding targetModels

theorem self_dual :
    targetSemigroup.opposite = targetSemigroup := by
  unfold targetSemigroup SemigroupBasis.Generated.Catalogue.S5_540.table
    SemigroupBasis.Generated.Catalogue.S5_540.mul
    FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  apply Fin.ext
  decide +revert

theorem opposite_basis :
    BasisFor targetSemigroup.opposite
      SemigroupBasis.CoRoots.S5_540.basis := by
  rw [self_dual]
  exact representative_basis

end SemigroupBasis.Generated.S5_540Transfers.S5_540
