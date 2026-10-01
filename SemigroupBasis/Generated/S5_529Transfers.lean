import SemigroupBasis.CoRoots.S5_529
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.S5_529Transfers.S5_532

open SemigroupBasis
open SemigroupBasis.Examples

abbrev sourceTable : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_529.table

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_532.table

abbrev sourceSemigroup : Semigroup (Fin 5) :=
  SemigroupBasis.Generated.Catalogue.S5_529.table.semigroup

abbrev targetSemigroup : Semigroup (Fin 5) :=
  SemigroupBasis.Generated.Catalogue.S5_532.table.semigroup

/-- The recorded one-based homomorphism `[1,2,3,1,4]`. -/
def firstHom :
    Hom sourceSemigroup targetSemigroup where
  toFun := fun a =>
    if a = 0 then 0
    else if a = 1 then 1
    else if a = 2 then 2
    else if a = 3 then 0
    else 3
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide

/-- The recorded one-based homomorphism `[4,4,4,5,4]`. -/
def secondHom :
    Hom sourceSemigroup targetSemigroup where
  toFun := fun a =>
    if a = 0 then 3
    else if a = 1 then 3
    else if a = 2 then 3
    else if a = 3 then 4
    else 3
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
      [[1, 2, 3, 1, 4], [4, 4, 4, 5, 4]] := by
  decide

def diagonalSignaturesOneBased : List (Nat × Nat) :=
  [((firstHom.toFun 0).val + 1, (secondHom.toFun 0).val + 1),
    ((firstHom.toFun 1).val + 1, (secondHom.toFun 1).val + 1),
    ((firstHom.toFun 2).val + 1, (secondHom.toFun 2).val + 1),
    ((firstHom.toFun 3).val + 1, (secondHom.toFun 3).val + 1),
    ((firstHom.toFun 4).val + 1, (secondHom.toFun 4).val + 1)]

theorem diagonalSignaturesOneBased_certificate :
    diagonalSignaturesOneBased =
      [(1, 4), (2, 4), (3, 4), (1, 5), (4, 4)] := by
  decide

/-- The diagonal of the two recorded homomorphisms embeds `S5_529` into
the direct square of `S5_532`. -/
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
      SemigroupBasis.CoRoots.S5_529.basis := by
  intro identity member
  simp only [SemigroupBasis.CoRoots.S5_529.basis,
    headSortedCappedThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [← SemigroupBasis.CoRoots.S5_529.finitePowerLaw_map]
    exact table.checkIdentityNat_sound
      SemigroupBasis.CoRoots.S5_529.finitePowerLaw (by decide)
  · rw [← SemigroupBasis.CoRoots.S5_529.finiteGatherLaw_map]
    exact table.checkIdentityNat_sound
      SemigroupBasis.CoRoots.S5_529.finiteGatherLaw (by decide)
  · rw [← SemigroupBasis.CoRoots.S5_529.finiteSuffixSwapLaw_map]
    exact table.checkIdentityNat_sound
      SemigroupBasis.CoRoots.S5_529.finiteSuffixSwapLaw (by decide)

theorem representative_basis :
    BasisFor targetSemigroup
      SemigroupBasis.CoRoots.S5_529.basis :=
  SemigroupBasis.CoRoots.S5_529.representative_basis.inheritAlongPowerEmbedding
    sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor targetSemigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_529.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S5_529Transfers.S5_532
