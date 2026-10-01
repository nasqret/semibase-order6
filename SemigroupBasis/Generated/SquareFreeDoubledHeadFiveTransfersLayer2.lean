import SemigroupBasis.Generated.SquareFreeDoubledHeadFiveTransfersLayer1

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.SquareFreeDoubledHeadFiveTransfers

open SemigroupBasis

-- BEGIN S5_943
namespace S5_943

def divisorSubMul
    (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def divisorSubTable : FiniteTable where
  order := 6
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_943.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 6) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (4 : Fin 5) else (4 : Fin 5) else if a = 0 then (2 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (0 : Fin 5) else (2 : Fin 5)
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
      SemigroupBasis.Generated.Catalogue.S5_872.table.semigroup where
  toFun := fun a : Fin 6 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (4 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (5 : Fin 6) else (4 : Fin 6)
  right_inverse := by
    intro b
    exact by decide +revert

def finiteSquareLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteReturnLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def finiteDoubledPrefixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [0, 2, 1]⟩⟩

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_943.table.semigroup
      SemigroupBasis.CoRoots.S5_830.basis := by
  intro e he
  simp only [
    SemigroupBasis.CoRoots.S5_830.basis,
    List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · change (finiteSquareLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_943.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_943.table.checkIdentityNat_sound
      finiteSquareLaw (by decide)
  · change (finiteReturnLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_943.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_943.table.checkIdentityNat_sound
      finiteReturnLaw (by decide)
  · change (finiteDoubledPrefixSwapLaw.map Fin.val).SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_943.table.semigroup
    exact SemigroupBasis.Generated.Catalogue.S5_943.table.checkIdentityNat_sound
      finiteDoubledPrefixSwapLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_943.table.semigroup
      SemigroupBasis.CoRoots.S5_830.basis :=
  SemigroupBasis.Generated.SquareFreeDoubledHeadFiveTransfers.S5_872.representative_basis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_943.table.semigroup.opposite
      (reversedBasis
        SemigroupBasis.CoRoots.S5_830.basis) :=
  representative_basis.oppositeReversed

end S5_943
-- END S5_943

end SemigroupBasis.Generated.SquareFreeDoubledHeadFiveTransfers
