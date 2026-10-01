import SemigroupBasis.Generated.DualMultipleBlockFiveTransfersLayer1

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.DualMultipleBlockFiveTransfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S5_251
namespace S5_251

def divisorSubMul
    (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (1 : Fin 5) else if b = 3 then (1 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (1 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (1 : Fin 5) else if a = 2 then if b = 0 then (1 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (2 : Fin 5) else if a = 3 then if b = 0 then (1 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (2 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (4 : Fin 5)

def divisorSubTable : FiniteTable where
  order := 5
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_251.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else (3 : Fin 5) else if a = 0 then (3 : Fin 5) else if a = 1 then (4 : Fin 5) else if a = 2 then (4 : Fin 5) else if a = 3 then (4 : Fin 5) else (3 : Fin 5)
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
      SemigroupBasis.Generated.Catalogue.S5_145.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (4 : Fin 5)
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
    Models SemigroupBasis.Generated.Catalogue.S5_251.table.semigroup dualMultipleBlockFiveStoredBasis := by
  intro e he
  simp only [dualMultipleBlockFiveStoredBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_251.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_251.table.checkIdentityNat_sound
      finiteGatherLaw (by decide)
  · rw [← finitePrefixSwapLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_251.table.checkIdentityNat_sound
      finitePrefixSwapLaw (by decide)
  · rw [← finiteSquareRotationLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_251.table.checkIdentityNat_sound
      finiteSquareRotationLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_251.table.semigroup
      dualMultipleBlockFiveStoredBasis :=
  SemigroupBasis.Generated.DualMultipleBlockFiveTransfers.S5_145.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_251.table.semigroup.opposite
      (reversedBasis dualMultipleBlockFiveStoredBasis) :=
  representative_basis.oppositeReversed

end S5_251
-- END S5_251

end SemigroupBasis.Generated.DualMultipleBlockFiveTransfers
