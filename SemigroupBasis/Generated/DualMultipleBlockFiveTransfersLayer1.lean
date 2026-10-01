import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S5_121
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.DualMultipleBlockFiveTransfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S5_123
namespace S5_123

def divisorSubMul
    (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def divisorSubTable : FiniteTable where
  order := 6
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_123.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 6) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (1 : Fin 5) else (4 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (0 : Fin 5) else (4 : Fin 5)
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
      SemigroupBasis.Generated.S5_121.table.semigroup where
  toFun := fun a : Fin 6 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finitePrefixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def finiteSquareRotationLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val =
      dualMultipleBlockFiveStoredPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val =
      dualMultipleBlockFiveStoredGatherLaw := rfl

theorem finitePrefixSwapLaw_map :
    finitePrefixSwapLaw.map Fin.val =
      dualMultipleBlockFiveStoredPrefixSwapLaw := rfl

theorem finiteSquareRotationLaw_map :
    finiteSquareRotationLaw.map Fin.val =
      dualMultipleBlockFiveStoredSquareRotationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_123.table.semigroup dualMultipleBlockFiveStoredBasis := by
  intro e he
  simp only [dualMultipleBlockFiveStoredBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_123.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_123.table.checkIdentityNat_sound
      finiteGatherLaw (by decide)
  · rw [← finitePrefixSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_123.table.checkIdentityNat_sound
      finitePrefixSwapLaw (by decide)
  · rw [← finiteSquareRotationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_123.table.checkIdentityNat_sound
      finiteSquareRotationLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_123.table.semigroup
      dualMultipleBlockFiveStoredBasis :=
  SemigroupBasis.Generated.S5_121.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_123.table.semigroup.opposite
      (reversedBasis dualMultipleBlockFiveStoredBasis) :=
  representative_basis.oppositeReversed

end S5_123
-- END S5_123

-- BEGIN S5_132
namespace S5_132

def divisorSubMul
    (a b : Fin 7) : Fin 7 :=
  if a = 0 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (2 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7) else if a = 1 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (2 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7) else if a = 2 then if b = 0 then (2 : Fin 7) else if b = 1 then (2 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (2 : Fin 7) else if b = 5 then (6 : Fin 7) else (5 : Fin 7) else if a = 3 then if b = 0 then (2 : Fin 7) else if b = 1 then (2 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (3 : Fin 7) else if b = 5 then (6 : Fin 7) else (5 : Fin 7) else if a = 4 then if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7) else if a = 5 then if b = 0 then (5 : Fin 7) else if b = 1 then (5 : Fin 7) else if b = 2 then (6 : Fin 7) else if b = 3 then (6 : Fin 7) else if b = 4 then (5 : Fin 7) else if b = 5 then (0 : Fin 7) else (2 : Fin 7) else if b = 0 then (6 : Fin 7) else if b = 1 then (6 : Fin 7) else if b = 2 then (5 : Fin 7) else if b = 3 then (5 : Fin 7) else if b = 4 then (6 : Fin 7) else if b = 5 then (2 : Fin 7) else (0 : Fin 7)

def divisorSubTable : FiniteTable where
  order := 7
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_132.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 7) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (0 : Fin 5) else if a = 5 then (2 : Fin 5) else (2 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (4 : Fin 5) else if a = 5 then (0 : Fin 5) else (2 : Fin 5)
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
      SemigroupBasis.Generated.S5_121.table.semigroup where
  toFun := fun a : Fin 7 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (4 : Fin 5) else if a = 5 then (3 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (3 : Fin 7) else if b = 3 then (5 : Fin 7) else (4 : Fin 7)
  right_inverse := by
    intro b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finitePrefixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def finiteSquareRotationLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val =
      dualMultipleBlockFiveStoredPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val =
      dualMultipleBlockFiveStoredGatherLaw := rfl

theorem finitePrefixSwapLaw_map :
    finitePrefixSwapLaw.map Fin.val =
      dualMultipleBlockFiveStoredPrefixSwapLaw := rfl

theorem finiteSquareRotationLaw_map :
    finiteSquareRotationLaw.map Fin.val =
      dualMultipleBlockFiveStoredSquareRotationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_132.table.semigroup dualMultipleBlockFiveStoredBasis := by
  intro e he
  simp only [dualMultipleBlockFiveStoredBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_132.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_132.table.checkIdentityNat_sound
      finiteGatherLaw (by decide)
  · rw [← finitePrefixSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_132.table.checkIdentityNat_sound
      finitePrefixSwapLaw (by decide)
  · rw [← finiteSquareRotationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_132.table.checkIdentityNat_sound
      finiteSquareRotationLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_132.table.semigroup
      dualMultipleBlockFiveStoredBasis :=
  SemigroupBasis.Generated.S5_121.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_132.table.semigroup.opposite
      (reversedBasis dualMultipleBlockFiveStoredBasis) :=
  representative_basis.oppositeReversed

end S5_132
-- END S5_132

-- BEGIN S5_134
namespace S5_134

def divisorSubMul
    (a b : Fin 7) : Fin 7 :=
  if a = 0 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (2 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7) else if a = 1 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (2 : Fin 7) else if b = 4 then (1 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7) else if a = 2 then if b = 0 then (2 : Fin 7) else if b = 1 then (2 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (2 : Fin 7) else if b = 5 then (6 : Fin 7) else (5 : Fin 7) else if a = 3 then if b = 0 then (2 : Fin 7) else if b = 1 then (2 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (2 : Fin 7) else if b = 5 then (6 : Fin 7) else (5 : Fin 7) else if a = 4 then if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7) else if a = 5 then if b = 0 then (5 : Fin 7) else if b = 1 then (5 : Fin 7) else if b = 2 then (6 : Fin 7) else if b = 3 then (6 : Fin 7) else if b = 4 then (5 : Fin 7) else if b = 5 then (0 : Fin 7) else (2 : Fin 7) else if b = 0 then (6 : Fin 7) else if b = 1 then (6 : Fin 7) else if b = 2 then (5 : Fin 7) else if b = 3 then (5 : Fin 7) else if b = 4 then (6 : Fin 7) else if b = 5 then (2 : Fin 7) else (0 : Fin 7)

def divisorSubTable : FiniteTable where
  order := 7
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_134.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 7) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (0 : Fin 5) else if a = 5 then (2 : Fin 5) else (2 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (4 : Fin 5) else if a = 5 then (0 : Fin 5) else (2 : Fin 5)
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
      SemigroupBasis.Generated.S5_121.table.semigroup where
  toFun := fun a : Fin 7 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (1 : Fin 5) else if a = 4 then (4 : Fin 5) else if a = 5 then (3 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 7) else if b = 1 then (3 : Fin 7) else if b = 2 then (1 : Fin 7) else if b = 3 then (5 : Fin 7) else (4 : Fin 7)
  right_inverse := by
    intro b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finitePrefixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def finiteSquareRotationLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val =
      dualMultipleBlockFiveStoredPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val =
      dualMultipleBlockFiveStoredGatherLaw := rfl

theorem finitePrefixSwapLaw_map :
    finitePrefixSwapLaw.map Fin.val =
      dualMultipleBlockFiveStoredPrefixSwapLaw := rfl

theorem finiteSquareRotationLaw_map :
    finiteSquareRotationLaw.map Fin.val =
      dualMultipleBlockFiveStoredSquareRotationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_134.table.semigroup dualMultipleBlockFiveStoredBasis := by
  intro e he
  simp only [dualMultipleBlockFiveStoredBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_134.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_134.table.checkIdentityNat_sound
      finiteGatherLaw (by decide)
  · rw [← finitePrefixSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_134.table.checkIdentityNat_sound
      finitePrefixSwapLaw (by decide)
  · rw [← finiteSquareRotationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_134.table.checkIdentityNat_sound
      finiteSquareRotationLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_134.table.semigroup
      dualMultipleBlockFiveStoredBasis :=
  SemigroupBasis.Generated.S5_121.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_134.table.semigroup.opposite
      (reversedBasis dualMultipleBlockFiveStoredBasis) :=
  representative_basis.oppositeReversed

end S5_134
-- END S5_134

-- BEGIN S5_143
namespace S5_143

def divisorSubMul
    (a b : Fin 7) : Fin 7 :=
  if a = 0 then if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (1 : Fin 7) else if b = 3 then (1 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7) else if a = 1 then if b = 0 then (1 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (1 : Fin 7) else if b = 5 then (6 : Fin 7) else (5 : Fin 7) else if a = 2 then if b = 0 then (1 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (1 : Fin 7) else if b = 5 then (6 : Fin 7) else (5 : Fin 7) else if a = 3 then if b = 0 then (1 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (3 : Fin 7) else if b = 5 then (6 : Fin 7) else (5 : Fin 7) else if a = 4 then if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7) else if a = 5 then if b = 0 then (5 : Fin 7) else if b = 1 then (6 : Fin 7) else if b = 2 then (6 : Fin 7) else if b = 3 then (6 : Fin 7) else if b = 4 then (5 : Fin 7) else if b = 5 then (0 : Fin 7) else (1 : Fin 7) else if b = 0 then (6 : Fin 7) else if b = 1 then (5 : Fin 7) else if b = 2 then (5 : Fin 7) else if b = 3 then (5 : Fin 7) else if b = 4 then (6 : Fin 7) else if b = 5 then (1 : Fin 7) else (0 : Fin 7)

def divisorSubTable : FiniteTable where
  order := 7
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_143.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 7) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (0 : Fin 5) else if a = 5 then (1 : Fin 5) else (1 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (4 : Fin 5) else if a = 5 then (0 : Fin 5) else (1 : Fin 5)
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
      SemigroupBasis.Generated.S5_121.table.semigroup where
  toFun := fun a : Fin 7 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (4 : Fin 5) else if a = 5 then (3 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 7) else if b = 1 then (2 : Fin 7) else if b = 2 then (3 : Fin 7) else if b = 3 then (5 : Fin 7) else (4 : Fin 7)
  right_inverse := by
    intro b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finitePrefixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def finiteSquareRotationLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val =
      dualMultipleBlockFiveStoredPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val =
      dualMultipleBlockFiveStoredGatherLaw := rfl

theorem finitePrefixSwapLaw_map :
    finitePrefixSwapLaw.map Fin.val =
      dualMultipleBlockFiveStoredPrefixSwapLaw := rfl

theorem finiteSquareRotationLaw_map :
    finiteSquareRotationLaw.map Fin.val =
      dualMultipleBlockFiveStoredSquareRotationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_143.table.semigroup dualMultipleBlockFiveStoredBasis := by
  intro e he
  simp only [dualMultipleBlockFiveStoredBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_143.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_143.table.checkIdentityNat_sound
      finiteGatherLaw (by decide)
  · rw [← finitePrefixSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_143.table.checkIdentityNat_sound
      finitePrefixSwapLaw (by decide)
  · rw [← finiteSquareRotationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_143.table.checkIdentityNat_sound
      finiteSquareRotationLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_143.table.semigroup
      dualMultipleBlockFiveStoredBasis :=
  SemigroupBasis.Generated.S5_121.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_143.table.semigroup.opposite
      (reversedBasis dualMultipleBlockFiveStoredBasis) :=
  representative_basis.oppositeReversed

end S5_143
-- END S5_143

-- BEGIN S5_145
namespace S5_145

def divisorSubMul
    (a b : Fin 10) : Fin 10 :=
  if a = 0 then if b = 0 then (0 : Fin 10) else if b = 1 then (1 : Fin 10) else if b = 2 then (1 : Fin 10) else if b = 3 then (1 : Fin 10) else if b = 4 then (4 : Fin 10) else if b = 5 then (5 : Fin 10) else if b = 6 then (0 : Fin 10) else if b = 7 then (1 : Fin 10) else if b = 8 then (1 : Fin 10) else (0 : Fin 10) else if a = 1 then if b = 0 then (1 : Fin 10) else if b = 1 then (0 : Fin 10) else if b = 2 then (0 : Fin 10) else if b = 3 then (0 : Fin 10) else if b = 4 then (5 : Fin 10) else if b = 5 then (4 : Fin 10) else if b = 6 then (1 : Fin 10) else if b = 7 then (0 : Fin 10) else if b = 8 then (0 : Fin 10) else (1 : Fin 10) else if a = 2 then if b = 0 then (1 : Fin 10) else if b = 1 then (0 : Fin 10) else if b = 2 then (0 : Fin 10) else if b = 3 then (0 : Fin 10) else if b = 4 then (5 : Fin 10) else if b = 5 then (4 : Fin 10) else if b = 6 then (1 : Fin 10) else if b = 7 then (0 : Fin 10) else if b = 8 then (0 : Fin 10) else (2 : Fin 10) else if a = 3 then if b = 0 then (1 : Fin 10) else if b = 1 then (0 : Fin 10) else if b = 2 then (0 : Fin 10) else if b = 3 then (0 : Fin 10) else if b = 4 then (5 : Fin 10) else if b = 5 then (4 : Fin 10) else if b = 6 then (1 : Fin 10) else if b = 7 then (0 : Fin 10) else if b = 8 then (0 : Fin 10) else (2 : Fin 10) else if a = 4 then if b = 0 then (4 : Fin 10) else if b = 1 then (5 : Fin 10) else if b = 2 then (5 : Fin 10) else if b = 3 then (5 : Fin 10) else if b = 4 then (0 : Fin 10) else if b = 5 then (1 : Fin 10) else if b = 6 then (4 : Fin 10) else if b = 7 then (5 : Fin 10) else if b = 8 then (5 : Fin 10) else (4 : Fin 10) else if a = 5 then if b = 0 then (5 : Fin 10) else if b = 1 then (4 : Fin 10) else if b = 2 then (4 : Fin 10) else if b = 3 then (4 : Fin 10) else if b = 4 then (1 : Fin 10) else if b = 5 then (0 : Fin 10) else if b = 6 then (5 : Fin 10) else if b = 7 then (4 : Fin 10) else if b = 8 then (4 : Fin 10) else (5 : Fin 10) else if a = 6 then if b = 0 then (0 : Fin 10) else if b = 1 then (1 : Fin 10) else if b = 2 then (1 : Fin 10) else if b = 3 then (1 : Fin 10) else if b = 4 then (4 : Fin 10) else if b = 5 then (5 : Fin 10) else if b = 6 then (6 : Fin 10) else if b = 7 then (7 : Fin 10) else if b = 8 then (7 : Fin 10) else (6 : Fin 10) else if a = 7 then if b = 0 then (1 : Fin 10) else if b = 1 then (0 : Fin 10) else if b = 2 then (0 : Fin 10) else if b = 3 then (0 : Fin 10) else if b = 4 then (5 : Fin 10) else if b = 5 then (4 : Fin 10) else if b = 6 then (7 : Fin 10) else if b = 7 then (6 : Fin 10) else if b = 8 then (6 : Fin 10) else (7 : Fin 10) else if a = 8 then if b = 0 then (1 : Fin 10) else if b = 1 then (0 : Fin 10) else if b = 2 then (0 : Fin 10) else if b = 3 then (0 : Fin 10) else if b = 4 then (5 : Fin 10) else if b = 5 then (4 : Fin 10) else if b = 6 then (7 : Fin 10) else if b = 7 then (6 : Fin 10) else if b = 8 then (6 : Fin 10) else (8 : Fin 10) else if b = 0 then (0 : Fin 10) else if b = 1 then (1 : Fin 10) else if b = 2 then (2 : Fin 10) else if b = 3 then (3 : Fin 10) else if b = 4 then (4 : Fin 10) else if b = 5 then (5 : Fin 10) else if b = 6 then (6 : Fin 10) else if b = 7 then (7 : Fin 10) else if b = 8 then (8 : Fin 10) else (9 : Fin 10)

def divisorSubTable : FiniteTable where
  order := 10
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_145.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 10) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (1 : Fin 5) else if a = 5 then (1 : Fin 5) else if a = 6 then (4 : Fin 5) else if a = 7 then (4 : Fin 5) else if a = 8 then (4 : Fin 5) else (4 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (0 : Fin 5) else if a = 5 then (1 : Fin 5) else if a = 6 then (0 : Fin 5) else if a = 7 then (1 : Fin 5) else if a = 8 then (2 : Fin 5) else (4 : Fin 5)
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
      SemigroupBasis.Generated.S5_121.table.semigroup where
  toFun := fun a : Fin 10 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (1 : Fin 5) else if a = 4 then (3 : Fin 5) else if a = 5 then (3 : Fin 5) else if a = 6 then (0 : Fin 5) else if a = 7 then (0 : Fin 5) else if a = 8 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 10) else if b = 1 then (3 : Fin 10) else if b = 2 then (8 : Fin 10) else if b = 3 then (4 : Fin 10) else (9 : Fin 10)
  right_inverse := by
    intro b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finitePrefixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def finiteSquareRotationLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val =
      dualMultipleBlockFiveStoredPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val =
      dualMultipleBlockFiveStoredGatherLaw := rfl

theorem finitePrefixSwapLaw_map :
    finitePrefixSwapLaw.map Fin.val =
      dualMultipleBlockFiveStoredPrefixSwapLaw := rfl

theorem finiteSquareRotationLaw_map :
    finiteSquareRotationLaw.map Fin.val =
      dualMultipleBlockFiveStoredSquareRotationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_145.table.semigroup dualMultipleBlockFiveStoredBasis := by
  intro e he
  simp only [dualMultipleBlockFiveStoredBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_145.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_145.table.checkIdentityNat_sound
      finiteGatherLaw (by decide)
  · rw [← finitePrefixSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_145.table.checkIdentityNat_sound
      finitePrefixSwapLaw (by decide)
  · rw [← finiteSquareRotationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_145.table.checkIdentityNat_sound
      finiteSquareRotationLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_145.table.semigroup
      dualMultipleBlockFiveStoredBasis :=
  SemigroupBasis.Generated.S5_121.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_145.table.semigroup.opposite
      (reversedBasis dualMultipleBlockFiveStoredBasis) :=
  representative_basis.oppositeReversed

end S5_145
-- END S5_145

-- BEGIN S5_247
namespace S5_247

def divisorSubMul
    (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (1 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (1 : Fin 5) else if b = 3 then (1 : Fin 5) else (1 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (3 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (4 : Fin 5)

def divisorSubTable : FiniteTable where
  order := 5
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_247.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else (3 : Fin 5) else if a = 0 then (3 : Fin 5) else if a = 1 then (4 : Fin 5) else if a = 2 then (3 : Fin 5) else if a = 3 then (3 : Fin 5) else (3 : Fin 5)
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
      SemigroupBasis.Generated.S5_121.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else if b = 3 then (1 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finitePrefixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def finiteSquareRotationLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val =
      dualMultipleBlockFiveStoredPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val =
      dualMultipleBlockFiveStoredGatherLaw := rfl

theorem finitePrefixSwapLaw_map :
    finitePrefixSwapLaw.map Fin.val =
      dualMultipleBlockFiveStoredPrefixSwapLaw := rfl

theorem finiteSquareRotationLaw_map :
    finiteSquareRotationLaw.map Fin.val =
      dualMultipleBlockFiveStoredSquareRotationLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_247.table.semigroup dualMultipleBlockFiveStoredBasis := by
  intro e he
  simp only [dualMultipleBlockFiveStoredBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_247.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_247.table.checkIdentityNat_sound
      finiteGatherLaw (by decide)
  · rw [← finitePrefixSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_247.table.checkIdentityNat_sound
      finitePrefixSwapLaw (by decide)
  · rw [← finiteSquareRotationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_247.table.checkIdentityNat_sound
      finiteSquareRotationLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_247.table.semigroup
      dualMultipleBlockFiveStoredBasis :=
  SemigroupBasis.Generated.S5_121.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_247.table.semigroup.opposite
      (reversedBasis dualMultipleBlockFiveStoredBasis) :=
  representative_basis.oppositeReversed

end S5_247
-- END S5_247

end SemigroupBasis.Generated.DualMultipleBlockFiveTransfers
