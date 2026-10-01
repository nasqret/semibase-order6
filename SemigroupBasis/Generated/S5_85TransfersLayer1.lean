import SemigroupBasis.CoRoots.S5_85Family
import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.S5_85Transfers

open SemigroupBasis

-- BEGIN S5_98
namespace S5_98

def divisorSubMul
    (a b : Fin 7) : Fin 7 :=
  if a = 0 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (0 : Fin 7) else (0 : Fin 7) else if a = 1 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (0 : Fin 7) else (0 : Fin 7) else if a = 2 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (0 : Fin 7) else (1 : Fin 7) else if a = 3 then if b = 0 then (3 : Fin 7) else if b = 1 then (3 : Fin 7) else if b = 2 then (3 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (3 : Fin 7) else if b = 5 then (3 : Fin 7) else (3 : Fin 7) else if a = 4 then if b = 0 then (4 : Fin 7) else if b = 1 then (4 : Fin 7) else if b = 2 then (4 : Fin 7) else if b = 3 then (4 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (4 : Fin 7) else (4 : Fin 7) else if a = 5 then if b = 0 then (4 : Fin 7) else if b = 1 then (4 : Fin 7) else if b = 2 then (4 : Fin 7) else if b = 3 then (4 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (4 : Fin 7) else (4 : Fin 7) else if b = 0 then (4 : Fin 7) else if b = 1 then (4 : Fin 7) else if b = 2 then (5 : Fin 7) else if b = 3 then (4 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (4 : Fin 7) else (4 : Fin 7)

def divisorSubTable : FiniteTable where
  order := 7
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_98.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 7) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (4 : Fin 5) else if a = 5 then (4 : Fin 5) else (4 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (4 : Fin 5) else if a = 4 then (0 : Fin 5) else if a = 5 then (1 : Fin 5) else (3 : Fin 5)
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

def divisorQuotient :
    SplitSurjection divisorSubTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_85.table.semigroup where
  toFun := fun a : Fin 7 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (4 : Fin 5) else if a = 4 then (0 : Fin 5) else if a = 5 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 7) else if b = 1 then (5 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (6 : Fin 7) else (3 : Fin 7)
  right_inverse := by
    intro b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteSquareSuffixLaw : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 1]⟩⟩

def finiteSquareMiddleLaw : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 0]⟩⟩

def finiteFirstSquareLaw : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_98.table.semigroup
      SemigroupBasis.CoRoots.S5_85.basis := by
  intro e he
  simp only [
    SemigroupBasis.CoRoots.S5_85.basis,
    List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · change (finitePowerLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_98.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_98.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · change (finiteSquareSuffixLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_98.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_98.table.checkIdentityNat_sound
      finiteSquareSuffixLaw (by decide)
  · change (finiteSquareMiddleLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_98.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_98.table.checkIdentityNat_sound
      finiteSquareMiddleLaw (by decide)
  · change (finiteFirstSquareLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_98.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_98.table.checkIdentityNat_sound
      finiteFirstSquareLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_98.table.semigroup
      SemigroupBasis.CoRoots.S5_85.basis :=
  SemigroupBasis.CoRoots.S5_85Family.S5_85.basis_complete.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_98.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_85.basis) :=
  representative_basis.oppositeReversed

end S5_98
-- END S5_98

-- BEGIN S5_241
namespace S5_241

def divisorSubMul
    (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def divisorSubTable : FiniteTable where
  order := 6
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_241.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 6) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (0 : Fin 5) else (3 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (4 : Fin 5) else (0 : Fin 5)
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

def divisorQuotient :
    SplitSurjection divisorSubTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_85.table.semigroup where
  toFun := fun a : Fin 6 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (2 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteSquareSuffixLaw : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 1]⟩⟩

def finiteSquareMiddleLaw : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 0]⟩⟩

def finiteFirstSquareLaw : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_241.table.semigroup
      SemigroupBasis.CoRoots.S5_85.basis := by
  intro e he
  simp only [
    SemigroupBasis.CoRoots.S5_85.basis,
    List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · change (finitePowerLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_241.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_241.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · change (finiteSquareSuffixLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_241.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_241.table.checkIdentityNat_sound
      finiteSquareSuffixLaw (by decide)
  · change (finiteSquareMiddleLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_241.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_241.table.checkIdentityNat_sound
      finiteSquareMiddleLaw (by decide)
  · change (finiteFirstSquareLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_241.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_241.table.checkIdentityNat_sound
      finiteFirstSquareLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_241.table.semigroup
      SemigroupBasis.CoRoots.S5_85.basis :=
  SemigroupBasis.CoRoots.S5_85Family.S5_85.basis_complete.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_241.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_85.basis) :=
  representative_basis.oppositeReversed

end S5_241
-- END S5_241

end SemigroupBasis.Generated.S5_85Transfers
