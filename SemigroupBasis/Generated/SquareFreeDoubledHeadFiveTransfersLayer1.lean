import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S5_830
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.SquareFreeDoubledHeadFiveTransfers

open SemigroupBasis

-- BEGIN S5_833
namespace S5_833

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S5_830.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_833.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else (4 : Fin 5) else if a = 0 then (2 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else (0 : Fin 5)
  map_mul := by
    intro a b
    funext i
    exact by decide +revert
  injective := by
    intro a b h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    clear h
    exact by decide +revert

def finiteSquareLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteReturnLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def finiteDoubledPrefixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [0, 2, 1]⟩⟩

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_833.table.semigroup
      SemigroupBasis.CoRoots.S5_830.basis := by
  intro e he
  simp only [
    SemigroupBasis.CoRoots.S5_830.basis,
    List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · change (finiteSquareLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_833.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_833.table.checkIdentityNat_sound
      finiteSquareLaw (by decide)
  · change (finiteReturnLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_833.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_833.table.checkIdentityNat_sound
      finiteReturnLaw (by decide)
  · change (finiteDoubledPrefixSwapLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_833.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_833.table.checkIdentityNat_sound
      finiteDoubledPrefixSwapLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_833.table.semigroup
      SemigroupBasis.CoRoots.S5_830.basis :=
  SemigroupBasis.Generated.S5_830.representative_basis.inheritAlongPowerEmbedding
    powerEmbedding targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_833.table.semigroup.opposite
      (reversedBasis
        SemigroupBasis.CoRoots.S5_830.basis) :=
  representative_basis.oppositeReversed

end S5_833
-- END S5_833

-- BEGIN S5_872
namespace S5_872

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S5_830.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_872.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else (3 : Fin 5) else if a = 0 then (3 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (3 : Fin 5) else if a = 3 then (4 : Fin 5) else (0 : Fin 5)
  map_mul := by
    intro a b
    funext i
    exact by decide +revert
  injective := by
    intro a b h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    clear h
    exact by decide +revert

def finiteSquareLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteReturnLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def finiteDoubledPrefixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [0, 2, 1]⟩⟩

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_872.table.semigroup
      SemigroupBasis.CoRoots.S5_830.basis := by
  intro e he
  simp only [
    SemigroupBasis.CoRoots.S5_830.basis,
    List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · change (finiteSquareLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_872.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_872.table.checkIdentityNat_sound
      finiteSquareLaw (by decide)
  · change (finiteReturnLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_872.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_872.table.checkIdentityNat_sound
      finiteReturnLaw (by decide)
  · change (finiteDoubledPrefixSwapLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_872.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_872.table.checkIdentityNat_sound
      finiteDoubledPrefixSwapLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_872.table.semigroup
      SemigroupBasis.CoRoots.S5_830.basis :=
  SemigroupBasis.Generated.S5_830.representative_basis.inheritAlongPowerEmbedding
    powerEmbedding targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_872.table.semigroup.opposite
      (reversedBasis
        SemigroupBasis.CoRoots.S5_830.basis) :=
  representative_basis.oppositeReversed

end S5_872
-- END S5_872

-- BEGIN S5_904
namespace S5_904

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S5_830.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_904.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else (3 : Fin 5) else if a = 0 then (4 : Fin 5) else if a = 1 then (4 : Fin 5) else if a = 2 then (4 : Fin 5) else if a = 3 then (0 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    funext i
    exact by decide +revert
  injective := by
    intro a b h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    clear h
    exact by decide +revert

def finiteSquareLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteReturnLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def finiteDoubledPrefixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [0, 2, 1]⟩⟩

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_904.table.semigroup
      SemigroupBasis.CoRoots.S5_830.basis := by
  intro e he
  simp only [
    SemigroupBasis.CoRoots.S5_830.basis,
    List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · change (finiteSquareLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_904.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_904.table.checkIdentityNat_sound
      finiteSquareLaw (by decide)
  · change (finiteReturnLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_904.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_904.table.checkIdentityNat_sound
      finiteReturnLaw (by decide)
  · change (finiteDoubledPrefixSwapLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_904.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_904.table.checkIdentityNat_sound
      finiteDoubledPrefixSwapLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_904.table.semigroup
      SemigroupBasis.CoRoots.S5_830.basis :=
  SemigroupBasis.Generated.S5_830.representative_basis.inheritAlongPowerEmbedding
    powerEmbedding targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_904.table.semigroup.opposite
      (reversedBasis
        SemigroupBasis.CoRoots.S5_830.basis) :=
  representative_basis.oppositeReversed

end S5_904
-- END S5_904

end SemigroupBasis.Generated.SquareFreeDoubledHeadFiveTransfers
