import SemigroupBasis.Generated.ParityInitialTransfersLayer1

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.ParityInitialTransfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S5_669
namespace S5_669

def divisorSubMul
    (a b : Fin 7) : Fin 7 :=
  if a = 0 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (2 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (2 : Fin 7) else (0 : Fin 7) else if a = 1 then if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (2 : Fin 7) else (1 : Fin 7) else if a = 2 then if b = 0 then (2 : Fin 7) else if b = 1 then (2 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (2 : Fin 7) else if b = 5 then (0 : Fin 7) else (2 : Fin 7) else if a = 3 then if b = 0 then (2 : Fin 7) else if b = 1 then (3 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (1 : Fin 7) else if b = 4 then (2 : Fin 7) else if b = 5 then (0 : Fin 7) else (3 : Fin 7) else if a = 4 then if b = 0 then (4 : Fin 7) else if b = 1 then (4 : Fin 7) else if b = 2 then (5 : Fin 7) else if b = 3 then (5 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (5 : Fin 7) else (4 : Fin 7) else if a = 5 then if b = 0 then (5 : Fin 7) else if b = 1 then (5 : Fin 7) else if b = 2 then (4 : Fin 7) else if b = 3 then (4 : Fin 7) else if b = 4 then (5 : Fin 7) else if b = 5 then (4 : Fin 7) else (5 : Fin 7) else if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7)

def divisorSubTable : FiniteTable where
  order := 7
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_669.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 7) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (1 : Fin 5) else if a = 4 then (2 : Fin 5) else if a = 5 then (3 : Fin 5) else (4 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (4 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (4 : Fin 5) else if a = 4 then (0 : Fin 5) else if a = 5 then (0 : Fin 5) else (4 : Fin 5)
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
      SemigroupBasis.Generated.Catalogue.S5_972.table.semigroup where
  toFun := fun a : Fin 7 =>
    if a = 0 then (3 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (3 : Fin 5) else if a = 3 then (1 : Fin 5) else if a = 4 then (4 : Fin 5) else if a = 5 then (4 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (1 : Fin 7) else if b = 1 then (3 : Fin 7) else if b = 2 then (6 : Fin 7) else if b = 3 then (0 : Fin 7) else (4 : Fin 7)
  right_inverse := by
    intro b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = parityInitialPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = parityInitialGatherLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_669.table.semigroup parityInitialBasis := by
  intro e he
  simp only [parityInitialBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_669.table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_669.table.checkIdentityNat_sound finiteGatherLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_669.table.semigroup
      parityInitialBasis :=
  SemigroupBasis.Generated.ParityInitialTransfers.S5_972.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_669.table.semigroup.opposite
      (reversedBasis parityInitialBasis) :=
  representative_basis.oppositeReversed

end S5_669
-- END S5_669

-- BEGIN S5_964
namespace S5_964

def divisorSubMul
    (a b : Fin 7) : Fin 7 :=
  if a = 0 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (3 : Fin 7) else if b = 5 then (3 : Fin 7) else (0 : Fin 7) else if a = 1 then if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (5 : Fin 7) else (0 : Fin 7) else if a = 2 then if b = 0 then (2 : Fin 7) else if b = 1 then (2 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (5 : Fin 7) else if b = 4 then (5 : Fin 7) else if b = 5 then (5 : Fin 7) else (2 : Fin 7) else if a = 3 then if b = 0 then (3 : Fin 7) else if b = 1 then (3 : Fin 7) else if b = 2 then (3 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (0 : Fin 7) else (3 : Fin 7) else if a = 4 then if b = 0 then (3 : Fin 7) else if b = 1 then (4 : Fin 7) else if b = 2 then (5 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (1 : Fin 7) else if b = 5 then (2 : Fin 7) else (3 : Fin 7) else if a = 5 then if b = 0 then (5 : Fin 7) else if b = 1 then (5 : Fin 7) else if b = 2 then (5 : Fin 7) else if b = 3 then (2 : Fin 7) else if b = 4 then (2 : Fin 7) else if b = 5 then (2 : Fin 7) else (5 : Fin 7) else if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (3 : Fin 7) else if b = 5 then (3 : Fin 7) else (6 : Fin 7)

def divisorSubTable : FiniteTable where
  order := 7
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_964.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 7) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (1 : Fin 5) else if a = 4 then (1 : Fin 5) else if a = 5 then (1 : Fin 5) else (2 : Fin 5) else if a = 0 then (2 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (4 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else if a = 5 then (4 : Fin 5) else (2 : Fin 5)
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
      SemigroupBasis.Generated.Catalogue.S5_984.table.semigroup where
  toFun := fun a : Fin 7 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (4 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (1 : Fin 5) else if a = 5 then (4 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (1 : Fin 7) else if b = 1 then (4 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (6 : Fin 7) else (2 : Fin 7)
  right_inverse := by
    intro b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = parityInitialPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = parityInitialGatherLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_964.table.semigroup parityInitialBasis := by
  intro e he
  simp only [parityInitialBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_964.table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_964.table.checkIdentityNat_sound finiteGatherLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_964.table.semigroup
      parityInitialBasis :=
  SemigroupBasis.Generated.ParityInitialTransfers.S5_984.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_964.table.semigroup.opposite
      (reversedBasis parityInitialBasis) :=
  representative_basis.oppositeReversed

end S5_964
-- END S5_964

end SemigroupBasis.Generated.ParityInitialTransfers
