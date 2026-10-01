import SemigroupBasis.CoRoots.S5_443Family
import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.S5_443Transfers

open SemigroupBasis

-- BEGIN S5_443
namespace S5_443

def divisorSubMul
    (a b : Fin 7) : Fin 7 :=
  if a = 0 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (4 : Fin 7) else (4 : Fin 7) else if a = 1 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (1 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (4 : Fin 7) else (4 : Fin 7) else if a = 2 then if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (2 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7) else if a = 3 then if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7) else if a = 4 then if b = 0 then (4 : Fin 7) else if b = 1 then (4 : Fin 7) else if b = 2 then (4 : Fin 7) else if b = 3 then (4 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (0 : Fin 7) else (0 : Fin 7) else if a = 5 then if b = 0 then (4 : Fin 7) else if b = 1 then (4 : Fin 7) else if b = 2 then (4 : Fin 7) else if b = 3 then (5 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (0 : Fin 7) else (0 : Fin 7) else if b = 0 then (4 : Fin 7) else if b = 1 then (5 : Fin 7) else if b = 2 then (6 : Fin 7) else if b = 3 then (6 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (1 : Fin 7) else (2 : Fin 7)

def divisorSubTable : FiniteTable where
  order := 7
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_443.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 7) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (2 : Fin 5) else if a = 5 then (2 : Fin 5) else (2 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else if a = 3 then (4 : Fin 5) else if a = 4 then (0 : Fin 5) else if a = 5 then (1 : Fin 5) else (3 : Fin 5)
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
      SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup where
  toFun := fun a : Fin 7 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (4 : Fin 5) else if a = 4 then (0 : Fin 5) else if a = 5 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (6 : Fin 7) else (3 : Fin 7)
  right_inverse := by
    intro b
    exact by decide +revert

def finitePeriodTwoLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteSquareCommutationLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_443.table.semigroup
      SemigroupBasis.CoRoots.S5_443Family.basis := by
  intro e he
  simp only [
    SemigroupBasis.CoRoots.S5_443Family.basis,
    List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · change (finitePeriodTwoLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_443.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_443.table.checkIdentityNat_sound
      finitePeriodTwoLaw (by decide)
  · change (finiteGatherLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_443.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_443.table.checkIdentityNat_sound
      finiteGatherLaw (by decide)
  · change (finiteSquareCommutationLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_443.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_443.table.checkIdentityNat_sound
      finiteSquareCommutationLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_443.table.semigroup
      SemigroupBasis.CoRoots.S5_443Family.basis :=
  SemigroupBasis.CoRoots.S5_443Family.S5_614.basis_complete.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_443.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_443Family.basis) :=
  representative_basis.oppositeReversed

end S5_443
-- END S5_443

-- BEGIN S5_465
namespace S5_465

def divisorSubMul
    (a b : Fin 9) : Fin 9 :=
  if a = 0 then if b = 0 then (0 : Fin 9) else if b = 1 then (1 : Fin 9) else if b = 2 then (1 : Fin 9) else if b = 3 then (0 : Fin 9) else if b = 4 then (0 : Fin 9) else if b = 5 then (5 : Fin 9) else if b = 6 then (6 : Fin 9) else if b = 7 then (6 : Fin 9) else (5 : Fin 9) else if a = 1 then if b = 0 then (1 : Fin 9) else if b = 1 then (0 : Fin 9) else if b = 2 then (0 : Fin 9) else if b = 3 then (1 : Fin 9) else if b = 4 then (1 : Fin 9) else if b = 5 then (6 : Fin 9) else if b = 6 then (5 : Fin 9) else if b = 7 then (5 : Fin 9) else (6 : Fin 9) else if a = 2 then if b = 0 then (1 : Fin 9) else if b = 1 then (0 : Fin 9) else if b = 2 then (0 : Fin 9) else if b = 3 then (1 : Fin 9) else if b = 4 then (2 : Fin 9) else if b = 5 then (6 : Fin 9) else if b = 6 then (5 : Fin 9) else if b = 7 then (5 : Fin 9) else (6 : Fin 9) else if a = 3 then if b = 0 then (0 : Fin 9) else if b = 1 then (1 : Fin 9) else if b = 2 then (2 : Fin 9) else if b = 3 then (3 : Fin 9) else if b = 4 then (3 : Fin 9) else if b = 5 then (5 : Fin 9) else if b = 6 then (6 : Fin 9) else if b = 7 then (7 : Fin 9) else (8 : Fin 9) else if a = 4 then if b = 0 then (0 : Fin 9) else if b = 1 then (1 : Fin 9) else if b = 2 then (2 : Fin 9) else if b = 3 then (3 : Fin 9) else if b = 4 then (4 : Fin 9) else if b = 5 then (5 : Fin 9) else if b = 6 then (6 : Fin 9) else if b = 7 then (7 : Fin 9) else (8 : Fin 9) else if a = 5 then if b = 0 then (5 : Fin 9) else if b = 1 then (6 : Fin 9) else if b = 2 then (6 : Fin 9) else if b = 3 then (5 : Fin 9) else if b = 4 then (5 : Fin 9) else if b = 5 then (0 : Fin 9) else if b = 6 then (1 : Fin 9) else if b = 7 then (1 : Fin 9) else (0 : Fin 9) else if a = 6 then if b = 0 then (6 : Fin 9) else if b = 1 then (5 : Fin 9) else if b = 2 then (5 : Fin 9) else if b = 3 then (6 : Fin 9) else if b = 4 then (6 : Fin 9) else if b = 5 then (1 : Fin 9) else if b = 6 then (0 : Fin 9) else if b = 7 then (0 : Fin 9) else (1 : Fin 9) else if a = 7 then if b = 0 then (6 : Fin 9) else if b = 1 then (5 : Fin 9) else if b = 2 then (5 : Fin 9) else if b = 3 then (6 : Fin 9) else if b = 4 then (7 : Fin 9) else if b = 5 then (1 : Fin 9) else if b = 6 then (0 : Fin 9) else if b = 7 then (0 : Fin 9) else (1 : Fin 9) else if b = 0 then (5 : Fin 9) else if b = 1 then (6 : Fin 9) else if b = 2 then (7 : Fin 9) else if b = 3 then (8 : Fin 9) else if b = 4 then (8 : Fin 9) else if b = 5 then (0 : Fin 9) else if b = 6 then (1 : Fin 9) else if b = 7 then (2 : Fin 9) else (3 : Fin 9)

def divisorSubTable : FiniteTable where
  order := 9
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_465.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 9) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (0 : Fin 5) else if a = 5 then (1 : Fin 5) else if a = 6 then (1 : Fin 5) else if a = 7 then (1 : Fin 5) else (1 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (4 : Fin 5) else if a = 5 then (0 : Fin 5) else if a = 6 then (1 : Fin 5) else if a = 7 then (2 : Fin 5) else (3 : Fin 5)
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
      SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup where
  toFun := fun a : Fin 9 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (4 : Fin 5) else if a = 5 then (0 : Fin 5) else if a = 6 then (0 : Fin 5) else if a = 7 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 9) else if b = 1 then (2 : Fin 9) else if b = 2 then (3 : Fin 9) else if b = 3 then (8 : Fin 9) else (4 : Fin 9)
  right_inverse := by
    intro b
    exact by decide +revert

def finitePeriodTwoLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteSquareCommutationLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_465.table.semigroup
      SemigroupBasis.CoRoots.S5_443Family.basis := by
  intro e he
  simp only [
    SemigroupBasis.CoRoots.S5_443Family.basis,
    List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · change (finitePeriodTwoLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_465.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_465.table.checkIdentityNat_sound
      finitePeriodTwoLaw (by decide)
  · change (finiteGatherLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_465.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_465.table.checkIdentityNat_sound
      finiteGatherLaw (by decide)
  · change (finiteSquareCommutationLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_465.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_465.table.checkIdentityNat_sound
      finiteSquareCommutationLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_465.table.semigroup
      SemigroupBasis.CoRoots.S5_443Family.basis :=
  SemigroupBasis.CoRoots.S5_443Family.S5_614.basis_complete.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_465.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_443Family.basis) :=
  representative_basis.oppositeReversed

end S5_465
-- END S5_465

-- BEGIN S5_635
namespace S5_635

def divisorSubMul
    (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (1 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (4 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (3 : Fin 5) else if b = 3 then (3 : Fin 5) else (4 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (4 : Fin 5) else if b = 3 then (4 : Fin 5) else (3 : Fin 5)

def divisorSubTable : FiniteTable where
  order := 5
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_635.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (2 : Fin 5) else (3 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (4 : Fin 5) else (4 : Fin 5)
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
      SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (4 : Fin 5) else if a = 3 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (3 : Fin 5) else if b = 3 then (4 : Fin 5) else (2 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finitePeriodTwoLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteSquareCommutationLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_635.table.semigroup
      SemigroupBasis.CoRoots.S5_443Family.basis := by
  intro e he
  simp only [
    SemigroupBasis.CoRoots.S5_443Family.basis,
    List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · change (finitePeriodTwoLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_635.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_635.table.checkIdentityNat_sound
      finitePeriodTwoLaw (by decide)
  · change (finiteGatherLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_635.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_635.table.checkIdentityNat_sound
      finiteGatherLaw (by decide)
  · change (finiteSquareCommutationLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_635.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_635.table.checkIdentityNat_sound
      finiteSquareCommutationLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_635.table.semigroup
      SemigroupBasis.CoRoots.S5_443Family.basis :=
  SemigroupBasis.CoRoots.S5_443Family.S5_614.basis_complete.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_635.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_443Family.basis) :=
  representative_basis.oppositeReversed

end S5_635
-- END S5_635

end SemigroupBasis.Generated.S5_443Transfers
